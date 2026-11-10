import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.CompactNamed

/-! Pointwise uniqueness of the target of two supplied composition paths.

Both functionality instances and all domain/edge guards are explicit K
antecedents. This constructs neither a composition graph nor its functionality
families, and does not assert transitivity of the quotient relation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactConditionalTransitivityUniqueness
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The local functionality instance for the first graph, explicitly guarded
by membership of its source and both candidate images. -/
def firstUnique : Nat := imp (member 0 2) (imp (member 1 10) (imp (member 1 11)
  (imp (graphFormula 6 2 10).encode (imp (graphFormula 6 2 11).encode (equal 10 11)))))

/-- The local functionality instance for the second graph at source 10,
explicitly guarded by the intermediate and both target memberships. -/
def secondUnique : Nat := imp (member 1 10) (imp (member 8 3) (imp (member 8 5)
  (imp (graphFormula 7 10 3).encode (imp (graphFormula 7 10 5).encode (equal 3 5)))))

/-- One path carries its intermediate and target domain guards as well as both
graph edges. The intermediate witness and target are literal names. -/
def firstPath : Nat := both (member 1 10) (both (member 8 3)
  (both (graphFormula 6 2 10).encode (graphFormula 7 10 3).encode))

def secondPath : Nat := both (member 1 11) (both (member 8 5)
  (both (graphFormula 6 2 11).encode (graphFormula 7 11 5).encode))

/-- The two paths have the same target, conditional on the two displayed
guarded functionality instances. -/
def path_target_unique : KDerivation
    (imp firstUnique (imp secondUnique (imp (member 0 2)
      (imp firstPath (imp secondPath (equal 3 5)))))) := by
  have hsrc := (equalityReplace 11 10 (graphFormula 7 11 5) (by decide) (by decide)).1
  have hrename : replace 11 10 (graphFormula 7 11 5) = graphFormula 7 10 5 := by decide
  rw [hrename] at hsrc
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [secondPath, firstPath, member 0 2, secondUnique, firstUnique]
  have hp : Context Γ firstPath := .hypothesis (by simp [Γ])
  have hq : Context Γ secondPath := Context.head _ _
  have ha : Context Γ (member 0 2) := .hypothesis (by simp [Γ])
  have hf : Context Γ firstUnique := .hypothesis (by simp [Γ])
  have hg : Context Γ secondUnique := .hypothesis (by simp [Γ])
  have hb : Context Γ (member 1 10) := Context.conjunctionLeft hp
  have hb' : Context Γ (member 1 11) := Context.conjunctionLeft hq
  have hc : Context Γ (member 8 3) := Context.conjunctionLeft (Context.conjunctionRight hp)
  have hc' : Context Γ (member 8 5) := Context.conjunctionLeft (Context.conjunctionRight hq)
  have hf₁ : Context Γ (graphFormula 6 2 10).encode :=
    Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hp))
  have hf₂ : Context Γ (graphFormula 6 2 11).encode :=
    Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hq))
  have hg₁ : Context Γ (graphFormula 7 10 3).encode :=
    Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hp))
  have hg₂ : Context Γ (graphFormula 7 11 5).encode :=
    Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hq))
  have he : Context Γ (equal 10 11) :=
    .mp hf₂ (.mp hf₁ (.mp hb' (.mp hb (.mp ha hf))))
  have hg₂' : Context Γ (graphFormula 7 10 5).encode :=
    .mp hg₂ (.mp (Context.eqSymm he) (.closed hsrc))
  exact .mp hg₂' (.mp hg₁ (.mp hc' (.mp hc (.mp hb hg))))

theorem path_target_unique_certificate : theoremCode (certificate path_target_unique) =
    imp firstUnique (imp secondUnique (imp (member 0 2)
      (imp firstPath (imp secondPath (equal 3 5))))) :=
  certificate_correct path_target_unique

/-- Local preimage uniqueness for the second graph at the target 3. -/
def secondInverseUnique : Nat := imp (member 8 3) (imp (member 1 10) (imp (member 1 11)
  (imp (graphFormula 7 10 3).encode (imp (graphFormula 7 11 3).encode (equal 10 11)))))

/-- Local preimage uniqueness for the first graph at intermediate 10. -/
def firstInverseUnique : Nat := imp (member 1 10) (imp (member 0 2) (imp (member 0 4)
  (imp (graphFormula 6 2 10).encode (imp (graphFormula 6 4 10).encode (equal 2 4)))))

def firstPreimagePath : Nat := both (member 0 2) (both (member 1 10)
  (both (graphFormula 6 2 10).encode (graphFormula 7 10 3).encode))

def secondPreimagePath : Nat := both (member 0 4) (both (member 1 11)
  (both (graphFormula 6 4 11).encode (graphFormula 7 11 3).encode))

/-- Dually, paths with a shared target have the same source under the two
explicitly guarded preimage-uniqueness instances. -/
def path_source_unique : KDerivation
    (imp secondInverseUnique (imp firstInverseUnique (imp (member 8 3)
      (imp firstPreimagePath (imp secondPreimagePath (equal 2 4)))))) := by
  have himg := (equalityReplace 11 10 (graphFormula 6 4 11) (by decide) (by decide)).1
  have hrename : replace 11 10 (graphFormula 6 4 11) = graphFormula 6 4 10 := by decide
  rw [hrename] at himg
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [secondPreimagePath, firstPreimagePath, member 8 3,
    firstInverseUnique, secondInverseUnique]
  have hp : Context Γ firstPreimagePath := .hypothesis (by simp [Γ])
  have hq : Context Γ secondPreimagePath := Context.head _ _
  have hc : Context Γ (member 8 3) := .hypothesis (by simp [Γ])
  have hf : Context Γ firstInverseUnique := .hypothesis (by simp [Γ])
  have hg : Context Γ secondInverseUnique := .hypothesis (by simp [Γ])
  have ha : Context Γ (member 0 2) := Context.conjunctionLeft hp
  have ha' : Context Γ (member 0 4) := Context.conjunctionLeft hq
  have hb : Context Γ (member 1 10) := Context.conjunctionLeft (Context.conjunctionRight hp)
  have hb' : Context Γ (member 1 11) := Context.conjunctionLeft (Context.conjunctionRight hq)
  have hf₁ : Context Γ (graphFormula 6 2 10).encode :=
    Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hp))
  have hf₂ : Context Γ (graphFormula 6 4 11).encode :=
    Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hq))
  have hg₁ : Context Γ (graphFormula 7 10 3).encode :=
    Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hp))
  have hg₂ : Context Γ (graphFormula 7 11 3).encode :=
    Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hq))
  have he : Context Γ (equal 10 11) :=
    .mp hg₂ (.mp hg₁ (.mp hb' (.mp hb (.mp hc hg))))
  have hf₂' : Context Γ (graphFormula 6 4 10).encode :=
    .mp hf₂ (.mp (Context.eqSymm he) (.closed himg))
  exact .mp hf₂' (.mp hf₁ (.mp ha' (.mp ha (.mp hb hf))))

theorem path_source_unique_certificate : theoremCode (certificate path_source_unique) =
    imp secondInverseUnique (imp firstInverseUnique (imp (member 8 3)
      (imp firstPreimagePath (imp secondPreimagePath (equal 2 4))))) :=
  certificate_correct path_source_unique

end PASoundness.PAtoCompactConditionalTransitivityUniqueness

#print axioms PASoundness.PAtoCompactConditionalTransitivityUniqueness.path_target_unique
#print axioms PASoundness.PAtoCompactConditionalTransitivityUniqueness.path_target_unique_certificate
#print axioms PASoundness.PAtoCompactConditionalTransitivityUniqueness.path_source_unique
#print axioms PASoundness.PAtoCompactConditionalTransitivityUniqueness.path_source_unique_certificate
