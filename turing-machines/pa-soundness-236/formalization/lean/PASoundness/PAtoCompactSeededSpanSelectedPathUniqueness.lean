import PASoundness.PAtoCompactSeededSpanPointUniquenessSeed
import PASoundness.CompactNamed

/-! The two same-path uniqueness directions for explicitly selected common
source witnesses 42 and 43. Four local input-bijection uniqueness tests,
domain memberships and the four original graph edges remain explicit K
antecedents. This does not yet construct these tests or eliminate paths. -/
namespace PASoundness.PAtoCompactSeededSpanSelectedPathUniqueness

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactSeededSpanPointUniqueness

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def selectedGuard : Nat := both (member 1 42) (both (member 1 43)
  (both (member 0 2) (both (member 0 26) (both (member 8 3) (both (member 8 27)
    (both (graphFormula 6 42 2).encode (both (graphFormula 6 43 26).encode
      (both (graphFormula 7 42 3).encode (graphFormula 7 43 27).encode))))))))

def firstInverse : Nat := imp (member 0 2) (imp (member 1 42) (imp (member 1 43)
  (imp (graphFormula 6 42 2).encode (imp (graphFormula 6 43 2).encode (equal 42 43)))))
def secondForward : Nat := imp (member 1 42) (imp (member 8 3) (imp (member 8 27)
  (imp (graphFormula 7 42 3).encode (imp (graphFormula 7 42 27).encode (equal 3 27)))))
def secondInverse : Nat := imp (member 8 3) (imp (member 1 42) (imp (member 1 43)
  (imp (graphFormula 7 42 3).encode (imp (graphFormula 7 43 3).encode (equal 42 43)))))
def firstForward : Nat := imp (member 1 42) (imp (member 0 2) (imp (member 0 26)
  (imp (graphFormula 6 42 2).encode (imp (graphFormula 6 42 26).encode (equal 2 26)))))

/-- The same pair of selected witnesses controls both output directions. -/
def selected_path_uniqueness : KDerivation (imp selectedGuard (imp firstInverse
    (imp secondForward (imp secondInverse (imp firstForward pointUniqueness))))) := by
  have hs := (equalityReplace 26 2 (graphFormula 6 43 26) (by decide) (by decide)).1
  have hs' : replace 26 2 (graphFormula 6 43 26) = graphFormula 6 43 2 := by decide
  rw [hs'] at hs
  have ht := (equalityReplace 27 3 (graphFormula 7 43 27) (by decide) (by decide)).1
  have ht' : replace 27 3 (graphFormula 7 43 27) = graphFormula 7 43 3 := by decide
  rw [ht'] at ht
  have h7 := (equalityReplace 43 42 (graphFormula 7 43 27) (by decide) (by decide)).1
  have h7' : replace 43 42 (graphFormula 7 43 27) = graphFormula 7 42 27 := by decide
  rw [h7'] at h7
  have h6 := (equalityReplace 43 42 (graphFormula 6 43 26) (by decide) (by decide)).1
  have h6' : replace 43 42 (graphFormula 6 43 26) = graphFormula 6 42 26 := by decide
  rw [h6'] at h6
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [firstForward,secondInverse,secondForward,firstInverse,selectedGuard]
  have hff : Context Γ firstForward := .head _ _
  have hsi : Context Γ secondInverse := .hypothesis (by simp [Γ])
  have hsf : Context Γ secondForward := .hypothesis (by simp [Γ])
  have hfi : Context Γ firstInverse := .hypothesis (by simp [Γ])
  have hg : Context Γ selectedGuard := .hypothesis (by simp [Γ])
  have h42 : Context Γ (member 1 42) := Context.conjunctionLeft hg
  have hr := Context.conjunctionRight hg
  have h43 : Context Γ (member 1 43) := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have h02 : Context Γ (member 0 2) := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have h026 : Context Γ (member 0 26) := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have h83 : Context Γ (member 8 3) := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have h827 : Context Γ (member 8 27) := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have he61 : Context Γ (graphFormula 6 42 2).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have he62 : Context Γ (graphFormula 6 43 26).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have he71 : Context Γ (graphFormula 7 42 3).encode := Context.conjunctionLeft hr
  have he72 : Context Γ (graphFormula 7 43 27).encode := Context.conjunctionRight hr
  have hforward : Context Γ (imp (equal 2 26) (equal 3 27)) := by
    apply Context.deduction
    let Δ := equal 2 26 :: Γ
    have he : Context Δ (equal 2 26) := .head _ _
    have hedge : Context Δ (graphFormula 6 43 2).encode :=
      .mp (.under he62 _) (.mp (Context.eqSymm he) (.closed hs))
    have hw : Context Δ (equal 42 43) := .mp hedge (.mp (.under he61 _)
      (.mp (.under h43 _) (.mp (.under h42 _) (.mp (.under h02 _) (.under hfi _)))))
    have hedge' : Context Δ (graphFormula 7 42 27).encode :=
      .mp (.under he72 _) (.mp (Context.eqSymm hw) (.closed h7))
    exact .mp hedge' (.mp (.under he71 _) (.mp (.under h827 _)
      (.mp (.under h83 _) (.mp (.under h42 _) (.under hsf _)))))
  have hreverse : Context Γ (imp (equal 3 27) (equal 2 26)) := by
    apply Context.deduction
    let Δ := equal 3 27 :: Γ
    have he : Context Δ (equal 3 27) := .head _ _
    have hedge : Context Δ (graphFormula 7 43 3).encode :=
      .mp (.under he72 _) (.mp (Context.eqSymm he) (.closed ht))
    have hw : Context Δ (equal 42 43) := .mp hedge (.mp (.under he71 _)
      (.mp (.under h43 _) (.mp (.under h42 _) (.mp (.under h83 _) (.under hsi _)))))
    have hedge' : Context Δ (graphFormula 6 42 26).encode :=
      .mp (.under he62 _) (.mp (Context.eqSymm hw) (.closed h6))
    exact .mp hedge' (.mp (.under he61 _) (.mp (.under h026 _)
      (.mp (.under h02 _) (.mp (.under h42 _) (.under hff _)))))
  exact Context.conjunctionIntro hforward hreverse

end PASoundness.PAtoCompactSeededSpanSelectedPathUniqueness

#print axioms PASoundness.PAtoCompactSeededSpanSelectedPathUniqueness.selectedGuard
#print axioms PASoundness.PAtoCompactSeededSpanSelectedPathUniqueness.firstInverse
#print axioms PASoundness.PAtoCompactSeededSpanSelectedPathUniqueness.secondForward
#print axioms PASoundness.PAtoCompactSeededSpanSelectedPathUniqueness.secondInverse
#print axioms PASoundness.PAtoCompactSeededSpanSelectedPathUniqueness.firstForward
#print axioms PASoundness.PAtoCompactSeededSpanSelectedPathUniqueness.selected_path_uniqueness
