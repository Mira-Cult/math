import PASoundness.PAtoCompactAdditionSuccessorGraphClean

/-! Pointwise uniqueness at the unequal top coordinates of an addition graph
extension. The displayed split formulas are explicit object-level K premises;
this module does not construct a graph or establish a bijection. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionUnequalTopUnique
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactAdditionSuccessorGraphClean
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- A new edge at the appended source is either old or has the appended
coordinates. This is a premise, not an asserted graph decomposition. -/
def sourceSplit (v : Nat) : Nat :=
  imp (graphFormula 9 31 v).encode
    (either (graphFormula 6 31 v).encode (both (equal 31 31) (equal v 32)))

/-- A new edge at the appended target is either old or has the appended
coordinates. -/
def targetSplit (u : Nat) : Nat :=
  imp (graphFormula 9 u 32).encode
    (either (graphFormula 6 u 32).encode (both (equal u 31) (equal 32 32)))

/-- The appended source has at most the appended target. Only a clean old
graph and the pointwise new-edge split are used. -/
def source_top_unique (v : Nat)
    (hf : [19,25,26,31,v,20,21,22,23,24].Nodup) :
    KDerivation (imp oldClean.encode (imp (sourceSplit v)
      (imp (graphFormula 9 31 v).encode (equal v 32)))) := by
  let C := oldClean.encode
  let S := sourceSplit v
  let G := (graphFormula 9 31 v).encode
  let O := (graphFormula 6 31 v).encode
  let P := both (equal 31 31) (equal v 32)
  let Γ := [G,S,C]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  have hc : Context Γ C := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hg : Context Γ G := .head _ _
  have cases : Context Γ (either O P) := .mp hg hs
  apply Context.disjunctionElim cases
  · have ho : Context (O :: Γ) O := .head _ _
    have hfalse : Context (O :: Γ) 1 :=
      .mp ho (.mp (Context.under hc O) (.closed (source_top_excluded v hf)))
    exact Context.explode (equal v 32) hfalse
  · exact Context.conjunctionRight (Context.head Γ P)

/-- The appended target has at most the appended source. The suffix filter
implies the whole old result is outside the old suffix; no transitivity of
the suffix is assumed. -/
def target_top_unique (u : Nat)
    (hf : [19,25,26,u,32,20,21,22,23,24].Nodup) :
    KDerivation (imp suffix (imp oldClean.encode (imp (targetSplit u)
      (imp (graphFormula 9 u 32).encode (equal u 31))))) := by
  let F := suffix
  let C := oldClean.encode
  let S := targetSplit u
  let G := (graphFormula 9 u 32).encode
  let O := (graphFormula 6 u 32).encode
  let P := both (equal u 31) (equal 32 32)
  let Γ := [G,S,C,F]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  have hf' : Context Γ F := .hypothesis (by simp [Γ])
  have hc : Context Γ C := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hg : Context Γ G := .head _ _
  have cases : Context Γ (either O P) := .mp hg hs
  apply Context.disjunctionElim cases
  · have ho : Context (O :: Γ) O := .head _ _
    have hfalse : Context (O :: Γ) 1 :=
      .mp ho (.mp (Context.under hc O)
        (.mp (Context.under hf' O) (.closed (target_top_excluded u hf))))
    exact Context.explode (equal u 31) hfalse
  · exact Context.conjunctionLeft (Context.head Γ P)

theorem source_top_unique_certificate (v : Nat)
    (hf : [19,25,26,31,v,20,21,22,23,24].Nodup) :
    theoremCode (certificate (source_top_unique v hf)) =
      imp oldClean.encode (imp (sourceSplit v)
        (imp (graphFormula 9 31 v).encode (equal v 32))) :=
  certificate_correct (source_top_unique v hf)

theorem target_top_unique_certificate (u : Nat)
    (hf : [19,25,26,u,32,20,21,22,23,24].Nodup) :
    theoremCode (certificate (target_top_unique u hf)) =
      imp suffix (imp oldClean.encode (imp (targetSplit u)
        (imp (graphFormula 9 u 32).encode (equal u 31)))) :=
  certificate_correct (target_top_unique u hf)
end PASoundness.PAtoCompactAdditionUnequalTopUnique

#print axioms PASoundness.PAtoCompactAdditionUnequalTopUnique.source_top_unique
#print axioms PASoundness.PAtoCompactAdditionUnequalTopUnique.target_top_unique
#print axioms PASoundness.PAtoCompactAdditionUnequalTopUnique.source_top_unique_certificate
#print axioms PASoundness.PAtoCompactAdditionUnequalTopUnique.target_top_unique_certificate
