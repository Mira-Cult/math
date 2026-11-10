import PASoundness.PAtoCompactMultiplicationOldForwardSpecialize

/-! Conditional finite K transfer of old-coordinate output uniqueness.
The two graph-recovery/old-output-membership implications are explicit K
proof inputs under a retained hypothesis. This does not establish either
input, a new product graph, or multiplication totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationOldForwardUniqueConditional
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactMultiplicationOldForwardSpecialize
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Old-graph uniqueness for the output already named 5. -/
def oldUnique : Formula := .all 9 (.imp
  (namedBoth (.member 32 9) (tripleAt 10 9)) (.equal 9 5))

/-- New-graph uniqueness for the same output, guarded by new result 45. -/
def newUnique : Formula := .all 9 (.imp
  (namedBoth (.member 45 9) (tripleAt 64 9)) (.equal 9 5))

private def oldPoint : Formula := .imp
  (namedBoth (.member 32 9) (tripleAt 10 9)) (.equal 9 5)
private def newPoint : Formula := .imp
  (namedBoth (.member 45 70) (tripleAt 64 70)) (.equal 70 5)

/-- Under retained hypothesis H, old uniqueness transfers if every new query
at competitor 70 is an old query and every such old query has an output in
old result 32. H's K vacuity at 70 is explicit. The final universal uses
capture-safe alpha conversion from fresh name 70 to binder 9. -/
def unique_transfer (H : Formula)
    (hH : KDerivation (imp H.encode (allCode 70 H.encode)))
    (hrec : KDerivation (imp H.encode
      (imp (tripleAt 64 70).encode (tripleAt 10 70).encode)))
    (hout : KDerivation (imp H.encode
      (imp (tripleAt 10 70).encode (member 32 70)))) :
    KDerivation (imp H.encode (imp oldUnique.encode newUnique.encode)) := by
  have hi := universalInstance 9 70 oldPoint (by decide) (by decide) (by decide)
  have hs : replace 9 70 oldPoint = .imp
      (namedBoth (.member 32 70) (tripleAt 10 70)) (.equal 70 5) := by decide
  rw [hs] at hi
  have hi' : KDerivation (imp oldUnique.encode
      (imp (both (member 32 70) (tripleAt 10 70).encode) (equal 70 5))) := by
    simpa [oldUnique,oldPoint,namedBoth,Formula.not,Formula.encode,both,neg] using hi
  let Γ := [oldUnique.encode,H.encode]
  have hU : Context Γ oldUnique.encode := .head _ _
  have hH' : Context Γ H.encode := .hypothesis (by simp [Γ])
  have hp : Context Γ newPoint.encode := by
    apply Context.deduction
    let Δ := [(namedBoth (.member 45 70) (tripleAt 64 70)).encode,oldUnique.encode,H.encode]
    have hc : Context Δ (both (member 45 70) (tripleAt 64 70).encode) := by
      have hh : Context Δ (namedBoth (.member 45 70) (tripleAt 64 70)).encode := .head _ _
      simpa [namedBoth,Formula.not,Formula.encode,both,neg] using hh
    have hn : Context Δ (tripleAt 64 70).encode := Context.conjunctionRight hc
    have hr : Context Δ (tripleAt 10 70).encode := .mp hn (.mp (.under hH' _) (.closed hrec))
    have hm : Context Δ (member 32 70) := .mp hr (.mp (.under hH' _) (.closed hout))
    have hu : Context Δ (imp (both (member 32 70) (tripleAt 10 70).encode) (equal 70 5)) :=
      .mp (.under hU _) (.closed hi')
    exact .mp (Context.conjunctionIntro hm hr) hu
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 70 h)) := by
    intro h hh
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hh
    by_cases he : h = oldUnique.encode
    · subst h; exact oldUnique.vacuity 70 (by decide)
    · have he' : h = H.encode := hh.resolve_left he
      subst h; exact hH
  have hall : Context Γ (allCode 70 newPoint.encode) := Context.generalize 70 hv hp
  have hα := (universalAlpha 70 9 newPoint (by decide) (by decide) (by decide)).1
  have hα' : KDerivation (imp (allCode 70 newPoint.encode) newUnique.encode) := by
    have hr : replace 70 9 newPoint = .imp
      (namedBoth (.member 45 9) (tripleAt 64 9)) (.equal 9 5) := by decide
    rw [hr] at hα
    simpa [newUnique,Formula.encode] using hα
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  exact .mp hall (.closed hα')

theorem unique_transfer_certificate (H : Formula)
    (hH : KDerivation (imp H.encode (allCode 70 H.encode)))
    (hrec : KDerivation (imp H.encode (imp (tripleAt 64 70).encode (tripleAt 10 70).encode)))
    (hout : KDerivation (imp H.encode (imp (tripleAt 10 70).encode (member 32 70)))) :
    theoremCode (certificate (unique_transfer H hH hrec hout)) =
      imp H.encode (imp oldUnique.encode newUnique.encode) := certificate_correct _
end PASoundness.PAtoCompactMultiplicationOldForwardUniqueConditional
#print axioms PASoundness.PAtoCompactMultiplicationOldForwardUniqueConditional.unique_transfer
#print axioms PASoundness.PAtoCompactMultiplicationOldForwardUniqueConditional.unique_transfer_certificate
