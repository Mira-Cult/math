import PASoundness.PAtoCompactOrderIsoZero
import PASoundness.PAtoCompactPointAdjoin

/-! Empty-prefix base for a candidate fixed-coordinate row extension. The
invariant uses existential edge coverage and a no-garbage condition, rather
than requiring every potentially nonunique pair representative to occur.
This is a finite K base proof, not row collection or multiplication totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactFixedFirstCoverageBase
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactOrderIsoZero PASoundness.PAtoCompactEmptyExtrema
open PASoundness.PAtoCompactAdjunction PASoundness.PAtoCompactPointAdjoin
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- A possible row entry is `((a,b),c)` with `b` in the prefix and source,
`F(b,c)` and the displayed pair witnesses. Names: prefix 0, `F` 6, old graph
10, fixed first coordinate 30, source 31, entry 9, and witnesses 3,4,5. -/
def rowWitness : Formula := .ex 3 (.ex 4 (.ex 5
  (namedBoth (.member 0 3) (namedBoth (.member 31 3)
    (namedBoth (graphFormula 6 3 4)
      (namedBoth (pairFormula 5 30 3) (pairFormula 9 5 4)))))))

/-- Each point in the prefix/source intersection has some supplied F edge,
pair witness and represented row edge. -/
def coverage (h : Nat) : Formula := .all 3
  (.imp (namedBoth (.member 0 3) (.member 31 3)) (.ex 4 (.ex 5
    (namedBoth (graphFormula 6 3 4)
      (namedBoth (pairFormula 5 30 3) (graphFormula h 5 4))))))

/-- Each entry in the extended graph was already in graph 10 or arises from
an explicitly represented row point. -/
def noGarbage (h : Nat) : Formula := .all 9
  (.imp (.member h 9) (namedEither (.member 10 9) rowWitness))

def rowInvariant (h : Nat) : Formula := namedBoth (coverage h) (noGarbage h)

/-- At an empty prefix the arbitrary old graph 10 satisfies both clauses. -/
def zero_row_invariant : KDerivation (imp (zeroCode 0 12) (rowInvariant 10).encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [zeroCode 0 12]
  have hz : Context Γ (zeroCode 0 12) := .head _ _
  let C : Formula := .ex 4 (.ex 5 (namedBoth (graphFormula 6 3 4)
    (namedBoth (pairFormula 5 30 3) (graphFormula 10 5 4))))
  have hpoint : Context Γ (imp (both (member 0 3) (member 31 3)) C.encode) := by
    apply Context.deduction
    let Δ := [both (member 0 3) (member 31 3), zeroCode 0 12]
    have ha : Context Δ (both (member 0 3) (member 31 3)) := .head _ _
    have hz' : Context Δ (zeroCode 0 12) := .under hz _
    have hn : Context Δ (neg (member 0 3)) :=
      .mp hz' (.closed (PAtoCompactZeroSuccessor.zero_excludes 0 12 3 (by decide) (by decide)))
    exact Context.explode C.encode (.mp (Context.conjunctionLeft ha) hn)
  have hv : ∀ q, q ∈ Γ → KDerivation (imp q (allCode 3 q)) := by
    intro q hq
    have hq' : q = zeroCode 0 12 := by simpa [Γ] using hq
    subst q
    exact zero_vacuity 0 12 3 (by decide) (by decide)
  have hc : Context Γ (coverage 10).encode := by
    have hall := Context.generalize 3 hv hpoint
    simpa [coverage,C,namedBoth,Formula.not,Formula.encode,both,neg] using hall
  have hgpoint : KDerivation (imp (member 10 9) (either (member 10 9) rowWitness.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    exact Context.disjunctionLeft (.head _ _)
  have hg : Context Γ (noGarbage 10).encode := by
    have hall := KDerivation.generalize 9 hgpoint
    have hc : Context Γ (allCode 9 (imp (member 10 9) (either (member 10 9) rowWitness.encode))) :=
      .closed hall
    simpa [noGarbage,namedEither,Formula.not,Formula.encode,neg,either] using hc
  have hpair := Context.conjunctionIntro hc hg
  simpa [rowInvariant,namedBoth,Formula.not,Formula.encode,both,neg] using hpair

/-- K supplies a graph satisfying the row invariant when the prefix is zero:
the existential graph witness is the old graph 10. -/
def zero_row_exists : KDerivation
    (imp (zeroCode 0 12) (existsCode 7 (rowInvariant 7).encode)) := by
  have hi := exists_variable_intro 7 10 (rowInvariant 7) (by decide) (by decide) (by decide)
  have hr : CompactNamed.replace 7 10 (rowInvariant 7) = rowInvariant 10 := by decide
  rw [hr] at hi
  exact compose zero_row_invariant hi

theorem zero_row_exists_certificate : theoremCode (certificate zero_row_exists) =
    imp (zeroCode 0 12) (existsCode 7 (rowInvariant 7).encode) :=
  certificate_correct zero_row_exists
end PASoundness.PAtoCompactFixedFirstCoverageBase
#print axioms PASoundness.PAtoCompactFixedFirstCoverageBase.zero_row_invariant
#print axioms PASoundness.PAtoCompactFixedFirstCoverageBase.zero_row_exists
#print axioms PASoundness.PAtoCompactFixedFirstCoverageBase.zero_row_exists_certificate
