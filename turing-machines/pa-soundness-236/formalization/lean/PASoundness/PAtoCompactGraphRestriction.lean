import PASoundness.PAtoCompactFilteredSubset
import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.PAtoCompactZeroSuccessor

/-! Restriction of a supplied graph to displayed endpoint sets, using literal
selector-8 K proof data. This constructs a subset of an existing graph; it
provides no cartesian product, identity graph, composition or quotient. The
standard-HF reading below is separate from the K construction. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactGraphRestriction
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactMatrix
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactOrderIsomorphism

/-- A pair witness at t has a first endpoint in x and a second endpoint in y.
Names 25 and 26 are endpoint witnesses; pairFormula binds 20, 21, 22. -/
def edgePredicate (t x y : Nat) : CompactNamed.Formula :=
  .ex 25 (namedBoth (.member x 25)
    (.ex 26 (namedBoth (.member y 26) (pairFormula t 25 26))))

/-- The automatically fresh selector witness code for this exact predicate. -/
def restrictionName (g t x y : Nat) : Nat :=
  filterPredicate g t (edgePredicate t x y).encode

/-- Selector 8 gives an actual represented subset of the supplied g having
exactly the qualifying edges under the explicit predicate. The formulas are
literal K formulas; freshness of g and t is sufficient for this syntax-level
construction. The intended relational reading has further freshness below. -/
def graph_restriction_exists (g t x y : Nat) (hgt : g ≠ t) :
    KDerivation (existsCode (restrictionName g t x y)
      (filterGraph g (restrictionName g t x y) t (edgePredicate t x y).encode)) := by
  exact filtered_subset_exists g t (edgePredicate t x y).encode hgt

theorem graph_restriction_certificate (g t x y : Nat) (hgt : g ≠ t) :
    theoremCode (certificate (graph_restriction_exists g t x y hgt)) =
      existsCode (restrictionName g t x y)
        (filterGraph g (restrictionName g t x y) t (edgePredicate t x y).encode) :=
  certificate_correct (graph_restriction_exists g t x y hgt)

/-- The named endpoint predicate has its intended two existential witnesses
in standard HF semantics. The fixed input labels avoid the five bound labels;
they may denote identical objects. -/
theorem edge_predicate_standard (t x y : Nat) (ρ : Environment)
    (fresh : [t,x,y,20,21,22,25,26].Nodup) :
    (edgePredicate t x y).Realize ρ ↔
      ∃ u v, bit (ρ x) u = true ∧ bit (ρ y) v = true ∧
        (pairFormula t 25 26).Realize (update (update ρ 25 u) 26 v) := by
  have hx25 : x ≠ 25 := by intro h; subst x; simp at fresh
  have hy25 : y ≠ 25 := by intro h; subst y; simp at fresh
  have hy26 : y ≠ 26 := by intro h; subst y; simp at fresh
  simp [edgePredicate, namedBoth, CompactNamed.Formula.Realize,
    CompactMatrix.update, hx25, hy25, hy26]

/-- Exact finite-filter reading in standard HF semantics. Each retained edge
is in the supplied graph and satisfies the displayed named endpoint predicate.
No existence of g or interpretation of pairFormula is used here. -/
theorem restriction_standard (g t x y : Nat) (ρ : Environment) (hgt : g ≠ t) :
    (decode (existsCode (restrictionName g t x y)
      (filterGraph g (restrictionName g t x y) t (edgePredicate t x y).encode))).Realize ρ ↔
    ∃ w, ∀ v, bit w v = true ↔
      (bit (ρ g) v = true ∧ (edgePredicate t x y).Realize (update ρ t v)) := by
  simpa only [restrictionName, CompactNamed.Formula.encode_realize] using
    filtered_subset_standard g t (edgePredicate t x y).encode ρ hgt

/-- The standard-HF reading exposes the retained source edge and its two
endpoint witnesses. This says nothing about edges absent from the source g. -/
theorem restriction_endpoints_standard (g t x y : Nat) (ρ : Environment)
    (fresh : [g,t,x,y,20,21,22,25,26].Nodup) :
    (decode (existsCode (restrictionName g t x y)
      (filterGraph g (restrictionName g t x y) t (edgePredicate t x y).encode))).Realize ρ ↔
    ∃ w, ∀ v, bit w v = true ↔
      (bit (ρ g) v = true ∧ ∃ u z, bit (ρ x) u = true ∧ bit (ρ y) z = true ∧
        (pairFormula t 25 26).Realize (update (update (update ρ t v) 25 u) 26 z)) := by
  have hgt : g ≠ t := by intro h; subst g; simp at fresh
  have hxt : x ≠ t := by intro h; subst x; simp at fresh
  have hyt : y ≠ t := by intro h; subst y; simp at fresh
  have hf : [t,x,y,20,21,22,25,26].Nodup := fresh.tail
  rw [restriction_standard g t x y ρ hgt]
  apply exists_congr
  intro w
  apply forall_congr'
  intro v
  apply iff_congr Iff.rfl
  apply and_congr Iff.rfl
  simpa only [CompactSemantics.update_other ρ t x v hxt,
    CompactSemantics.update_other ρ t y v hyt] using edge_predicate_standard t x y (update ρ t v) hf

end PASoundness.PAtoCompactGraphRestriction

#print axioms PASoundness.PAtoCompactGraphRestriction.graph_restriction_exists
#print axioms PASoundness.PAtoCompactGraphRestriction.graph_restriction_certificate
#print axioms PASoundness.PAtoCompactGraphRestriction.edge_predicate_standard
#print axioms PASoundness.PAtoCompactGraphRestriction.restriction_standard
#print axioms PASoundness.PAtoCompactGraphRestriction.restriction_endpoints_standard
