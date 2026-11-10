import PASoundness.PAtoCompactMemberCutReadyTarget
import PASoundness.PAtoCompactFreeVacuity
import PASoundness.PAtoCompactTermGraphBinderRange

/-! Eliminate supplied target-cut and target-suffix witnesses from the
fixed-witness addition construction. Their existence remains an explicit K
antecedent: no outer isomorphism, filter, or suffix graph is constructed here. -/
namespace PASoundness.PAtoCompactMemberCutSelectedTarget
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactTermGraphBinderRange
open PASoundness.PAtoCompactFreeNames
open PASoundness.PAtoCompactMemberCutQuotientChains PASoundness.PAtoCompactMemberCutReadyTarget
set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def oldCut : Formula := PASoundness.PAtoCompactOrdinalAddition.equivAt 30 33
def oldSuffix : Formula := PASoundness.PAtoCompactOrdinalAddition.equivAt 31 34
/-- Actual operand domains and actual old witness isomorphisms. -/
def base : Formula := namedBoth (domainAt 100 30) (namedBoth (domainAt 100 31)
  (namedBoth oldCut oldSuffix))
/-- The chosen target cut/suffix are respectively 41 and 38, with supplied
old-to-new isomorphisms and the literal target suffix predicate. -/
def chosenBody : Formula := namedBoth (equivAt 100 33 41) (namedBoth (equivAt 100 34 38)
  (namedBoth (.member 8 41) PAtoCompactMemberCutRawTargetIntro.targetSuffix))
def chosen : Formula := .ex 41 (.ex 38 chosenBody)
def target : Formula := addAt 100 30 31 8

private theorem base_free_fresh (n : Nat) (h30 : n ≠ 30) (h31 : n ≠ 31)
    (h33 : n ≠ 33) (h34 : n ≠ 34) : n ∉ base.free := by
  intro h
  simp only [base,namedBoth,Formula.free,Finset.union_empty,Finset.empty_union,Finset.mem_union] at h
  rcases h with h | h | h | h
  · have hh := domainAt_free 100 30 h
    simp only [Finset.mem_singleton] at hh
    exact h30 hh
  · have hh := domainAt_free 100 31 h
    simp only [Finset.mem_singleton] at hh
    exact h31 hh
  · have hh : n = 30 ∨ n = 33 := by
      have hf : oldCut.free = {30,33} := by decide
      rw [hf] at h
      simpa using h
    rcases hh with hh | hh
    · exact h30 hh
    · exact h33 hh
  · have hh : n = 31 ∨ n = 34 := by
      have hf : oldSuffix.free = {31,34} := by decide
      rw [hf] at h
      simpa using h
    rcases hh with hh | hh
    · exact h31 hh
    · exact h34 hh

private theorem target_free_fresh (n : Nat) (h30 : n ≠ 30) (h31 : n ≠ 31)
    (h8 : n ≠ 8) : n ∉ target.free := by
  intro h
  have hh := addAt_free 100 30 31 8 h
  simp only [Finset.mem_insert,Finset.mem_singleton] at hh
  rcases hh with hh | hh | hh
  · exact h30 hh
  · exact h31 hh
  · exact h8 hh

/-- The actual old witnesses plus an explicitly supplied single target
cut/suffix pair yield target addition. All four named objects may coincide. -/
def target_from_selected : KDerivation
    (imp base.encode (imp chosen.encode target.encode)) := by
  let Γ := [base.encode]
  have hb : Context Γ base.encode := .head _ _
  have hlocal : Context (chosenBody.encode :: Γ) target.encode := by
    let Δ := chosenBody.encode :: Γ
    have hch : Context Δ chosenBody.encode := .head _ _
    have hb' : Context Δ base.encode := .under hb _
    have hd30 : Context Δ (domainAt 100 30).encode := Context.conjunctionLeft hb'
    have ht := Context.conjunctionRight hb'
    have hd31 : Context Δ (domainAt 100 31).encode := Context.conjunctionLeft ht
    have ht := Context.conjunctionRight ht
    have hc : Context Δ oldCut.encode := Context.conjunctionLeft ht
    have hs : Context Δ oldSuffix.encode := Context.conjunctionRight ht
    have hcut : Context Δ (equivAt 100 33 41).encode := Context.conjunctionLeft hch
    have ht := Context.conjunctionRight hch
    have hsuf : Context Δ (equivAt 100 34 38).encode := Context.conjunctionLeft ht
    have ht := Context.conjunctionRight ht
    have hm : Context Δ (member 8 41) := Context.conjunctionLeft ht
    have hf : Context Δ PAtoCompactMemberCutRawTargetIntro.targetSuffix.encode := Context.conjunctionRight ht
    have hg : Context Δ PAtoCompactMemberCutQuotientChains.guard.encode := by
      have h := Context.conjunctionIntro hd30 (Context.conjunctionIntro hd31
        (Context.conjunctionIntro hc (Context.conjunctionIntro hs (Context.conjunctionIntro hcut hsuf))))
      simpa only [PAtoCompactMemberCutQuotientChains.guard,oldCut,oldSuffix,namedBoth,Formula.not,Formula.encode,both,neg] using h
    have hr : Context Δ ready.encode := by
      have h := Context.conjunctionIntro hg (Context.conjunctionIntro hm hf)
      simpa only [ready,namedBoth,Formula.not,Formula.encode,both,neg] using h
    exact .mp hr (.closed addition_of_ready)
  have hv38 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 38 h)) := by
    intro h hh
    have he : h = base.encode := by simpa [Γ] using hh
    subst h
    exact free_vacuity 38 base (base_free_fresh 38 (by decide) (by decide) (by decide) (by decide))
  have hall38 := Context.generalize 38 hv38 (Context.deduction hlocal)
  have hinner : Context ((.ex 38 chosenBody : Formula).encode :: Γ) target.encode := by
    have he : Context ((.ex 38 chosenBody : Formula).encode :: Γ) (existsCode 38 chosenBody.encode) := .head _ _
    exact Context.existsElim (free_vacuity 38 target (target_free_fresh 38 (by decide) (by decide) (by decide)))
      (.under hall38 _) he
  have hv41 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 41 h)) := by
    intro h hh
    have he : h = base.encode := by simpa [Γ] using hh
    subst h
    exact free_vacuity 41 base (base_free_fresh 41 (by decide) (by decide) (by decide) (by decide))
  have hall41 := Context.generalize 41 hv41 (Context.deduction hinner)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Δ := [chosen.encode,base.encode]
  have hchosen : Context Δ (existsCode 41 (existsCode 38 chosenBody.encode)) := by
    simpa only [Δ,chosen,Formula.encode] using (Context.head [base.encode] chosen.encode)
  exact Context.existsElim (free_vacuity 41 target (target_free_fresh 41 (by decide) (by decide) (by decide)))
    (.under hall41 _) hchosen

theorem target_from_selected_certificate : theoremCode (certificate target_from_selected) =
    imp base.encode (imp chosen.encode target.encode) := certificate_correct target_from_selected
end PASoundness.PAtoCompactMemberCutSelectedTarget

#print axioms PASoundness.PAtoCompactMemberCutSelectedTarget.target_from_selected
#print axioms PASoundness.PAtoCompactMemberCutSelectedTarget.target_from_selected_certificate
