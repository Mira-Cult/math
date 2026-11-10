import PASoundness.PAtoCompactMultiplicationCleanMapUnique41

/-! Capture-safe specialization of clean map uniqueness to multiplication's
point labels. K equality aliases are introduced and eliminated without
assuming extensionality or distinct represented objects. This supplies only a
pointwise uniqueness implication, not graph existence or multiplication. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationCleanMapUniqueActual
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactMultiplicationSuffixCleanEdges
open PASoundness.PAtoCompactMultiplicationCleanMapUnique41
attribute [local irreducible] imp Cantor.pair Cantor.triangle

private def eliminate_alias (x y E : Nat)
    (hv : KDerivation (imp E (allCode x E)))
    (h : KDerivation (imp (equal x y) E)) : KDerivation E := by
  apply Context.closeEmpty
  apply Context.existsElim hv
  · exact .closed (.generalize x h)
  · exact .closed (existsEqual x y)

private def goal : Formula := .imp suffixClean (.imp mapBijection40
  (.imp (.member 31 3) (.imp (graphFormula 6 3 5)
    (.imp (graphFormula 6 3 9) (.equal 9 5)))))
private def with41 : Formula := .imp (.equal 41 3) goal
private def with42 : Formula := .imp (.equal 42 5) with41

private def point : KDerivation (imp (equal 43 9) with42.encode) := by
  let H := Formula.member 31 3
  let F := graphFormula 6 3 5
  let F41 := graphFormula 6 41 5
  let G := graphFormula 6 3 9
  let G41 := graphFormula 6 41 9
  have htH := (equalityReplace 3 41 H (by decide) (by decide)).1
  have hH : replace 3 41 H = .member 31 41 := by decide
  rw [hH] at htH
  have htF := (equalityReplace 3 41 F (by decide) (by decide)).1
  have hF : replace 3 41 F = F41 := by decide
  rw [hF] at htF
  have htF2 := (equalityReplace 5 42 F41 (by decide) (by decide)).1
  have hF2 : replace 5 42 F41 = graphFormula 6 41 42 := by decide
  rw [hF2] at htF2
  have htG := (equalityReplace 3 41 G (by decide) (by decide)).1
  have hG : replace 3 41 G = G41 := by decide
  rw [hG] at htG
  have htG2 := (equalityReplace 9 43 G41 (by decide) (by decide)).1
  have hG2 : replace 9 43 G41 = graphFormula 6 41 43 := by decide
  rw [hG2] at htG2
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [G.encode,F.encode,member 31 3,mapBijection40.encode,suffixClean.encode,
    equal 41 3,equal 42 5,equal 43 9]
  have hg : Context Γ G.encode := .head _ _
  have hf : Context Γ F.encode := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 31 3) := .hypothesis (by simp [Γ])
  have hb : Context Γ mapBijection40.encode := .hypothesis (by simp [Γ])
  have hc : Context Γ suffixClean.encode := .hypothesis (by simp [Γ])
  have he1 : Context Γ (equal 41 3) := .hypothesis (by simp [Γ])
  have he2 : Context Γ (equal 42 5) := .hypothesis (by simp [Γ])
  have he3 : Context Γ (equal 43 9) := .hypothesis (by simp [Γ])
  have hm' : Context Γ (member 31 41) := .mp hm (.mp (Context.eqSymm he1) (.closed htH))
  have hf' : Context Γ (graphFormula 6 41 42).encode :=
    .mp (.mp hf (.mp (Context.eqSymm he1) (.closed htF)))
      (.mp (Context.eqSymm he2) (.closed htF2))
  have hg' : Context Γ (graphFormula 6 41 43).encode :=
    .mp (.mp hg (.mp (Context.eqSymm he1) (.closed htG)))
      (.mp (Context.eqSymm he3) (.closed htG2))
  have he : Context Γ (equal 42 43) :=
    .mp hg' (.mp hf' (.mp hm' (.mp hb (.mp hc (.closed clean_unique)))))
  exact Context.eqSymm (Context.eqTrans (Context.eqSymm he2) (Context.eqTrans he he3))

/-- A clean source-31, target-40 bijection has at most one output for source
3. The queried graph edges need not be represented by the same pair object. -/
def clean_unique_actual : KDerivation (imp suffixClean.encode (imp mapBijection40.encode
    (imp (member 31 3) (imp (graphFormula 6 3 5).encode
      (imp (graphFormula 6 3 9).encode (equal 9 5)))))) := by
  have hv43 : KDerivation (imp with42.encode (allCode 43 with42.encode)) := with42.vacuity 43 (by decide)
  have h1 : KDerivation with42.encode := eliminate_alias 43 9 with42.encode hv43 point
  have hv42 : KDerivation (imp with41.encode (allCode 42 with41.encode)) := with41.vacuity 42 (by decide)
  have h2 : KDerivation with41.encode := eliminate_alias 42 5 with41.encode hv42 h1
  have hv41 : KDerivation (imp goal.encode (allCode 41 goal.encode)) := goal.vacuity 41 (by decide)
  have h3 : KDerivation goal.encode := eliminate_alias 41 3 goal.encode hv41 h2
  simpa [goal, Formula.encode] using h3

theorem clean_unique_actual_certificate : theoremCode (certificate clean_unique_actual) =
    imp suffixClean.encode (imp mapBijection40.encode (imp (member 31 3)
      (imp (graphFormula 6 3 5).encode (imp (graphFormula 6 3 9).encode (equal 9 5))))) :=
  certificate_correct clean_unique_actual
end PASoundness.PAtoCompactMultiplicationCleanMapUniqueActual
#print axioms PASoundness.PAtoCompactMultiplicationCleanMapUniqueActual.clean_unique_actual
#print axioms PASoundness.PAtoCompactMultiplicationCleanMapUniqueActual.clean_unique_actual_certificate
