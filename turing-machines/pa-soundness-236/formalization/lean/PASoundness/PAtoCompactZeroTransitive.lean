import PASoundness.PAtoCompactZeroExistence
import PASoundness.PAtoCompactTransitiveClosure

/-! Constructive K transitivity of a zero-graph witness and a combined
existence theorem. Compact code 1 is literally `member 0 0`; graph names and
the standard-HF interpretation are stated separately. No uniqueness,
induction, or full arithmetic-domain interpretation is claimed. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactZeroTransitive
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactZeroExistence
open PASoundness.PAtoCompactTransitiveSuccessor

/-- The exact zero formula is vacuous at any syntactically fresh name. The
compact `.bottom` node used here encodes literal code 1. -/
def zero_graph_vacuity (z t v : Nat) (hvz : v ≠ z) (hvt : v ≠ t) :
    KDerivation (imp (zeroCode z t) (allCode v (zeroCode z t))) := by
  let f : CompactNamed.Formula := .all t (.imp (.member z t) .bottom)
  have hv : v ∉ f.names := by
    simp [f, CompactNamed.Formula.names, hvz, hvt]
  have h := f.vacuity v hv
  simpa [f, zeroCode, CompactNamed.Formula.encode, CompactProof.neg] using h

/-- A zero graph implies transitivity by a literal finite K derivation. The
selector's quantified test label t is distinct from z and p; the output
transitivity labels p and q are distinct and avoid both names so the assumptions
generalize and the displayed formula retains two independent quantifiers. -/
def zero_graph_implies_transitive (z t p q : Nat)
    (htz : t ≠ z) (htp : t ≠ p)
    (hpz : p ≠ z) (hqz : q ≠ z) (hqt : q ≠ t) (_hpq : p ≠ q) :
    KDerivation (imp (zeroCode z t) (transitiveCode z p q)) := by
  let Γ := [zeroCode z t]
  have hz : Context Γ (zeroCode z t) := Context.head [] _
  have hno : Context Γ (neg (member z p)) :=
    .mp hz (.closed (zero_excludes z t p htp htz))
  have hpoint : Context Γ (imp (member z p) (imp (member p q) (member z q))) := by
    apply Context.deduction
    apply Context.deduction
    have hm : Context (member p q :: member z p :: Γ) (member z p) := .hypothesis (by simp)
    have hn : Context (member p q :: member z p :: Γ) (neg (member z p)) :=
      Context.under (Context.under hno (member z p)) (member p q)
    exact Context.explode (member z q) (.mp hm hn)
  have hvq : ∀ h, h ∈ Γ → KDerivation (imp h (allCode q h)) := by
    intro h hh
    have he : h = zeroCode z t := by simpa [Γ] using hh
    subst h
    exact zero_graph_vacuity z t q hqz hqt
  have hvp : ∀ h, h ∈ Γ → KDerivation (imp h (allCode p h)) := by
    intro h hh
    have he : h = zeroCode z t := by simpa [Γ] using hh
    subst h
    exact zero_graph_vacuity z t p hpz (Ne.symm htp)
  have htrans : Context Γ (transitiveCode z p q) :=
    Context.generalize p hvp (Context.generalize q hvq hpoint)
  apply Context.closeEmpty
  apply Context.deduction
  exact htrans

/-- A zero-graph witness is also a witness for the displayed conjunction of
the zero graph and transitivity. -/
def zero_graph_add_transitivity (z t p q : Nat)
    (htz : t ≠ z) (htp : t ≠ p)
    (hpz : p ≠ z) (hqz : q ≠ z) (hqt : q ≠ t) (hpq : p ≠ q) :
    KDerivation (imp (zeroCode z t) (both (zeroCode z t) (transitiveCode z p q))) := by
  apply Context.closeEmpty
  apply Context.deduction
  have hz := Context.head [] (zeroCode z t)
  exact Context.conjunctionIntro hz (.mp hz (.closed
    (zero_graph_implies_transitive z t p q htz htp hpz hqz hqt hpq)))

/-- Explicit transitive-domain zero witness: selector 8 gives the zero graph
at witness label 1 and test label 2, while 3 and 4 are distinct fresh
transitivity test labels. This statement asserts existence only. -/
def transitive_zero_exists :
    KDerivation (existsCode 1 (both (zeroCode 1 2) (transitiveCode 1 3 4))) := by
  exact .mp zero_graph_exists_closed (existsCongr 1
    (zero_graph_add_transitivity 1 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)))

theorem transitive_zero_certificate :
    theoremCode (certificate transitive_zero_exists) =
      existsCode 1 (both (zeroCode 1 2) (transitiveCode 1 3 4)) :=
  certificate_correct transitive_zero_exists

/-- In standard HF semantics, a zero-graph witness is a finite ordinal zero
and hence transitive. This semantic confirmation is not used to construct the
K proof. -/
theorem standard_zero_is_transitive (z t p q : Nat) (ρ : CompactMatrix.Environment)
    (hzt : z ≠ t) (hzp : z ≠ p) (hzq : z ≠ q) (hpq : p ≠ q)
    (hz : (CompactMatrix.decode (zeroCode z t)).Realize ρ) :
    (CompactMatrix.decode (transitiveCode z p q)).Realize ρ := by
  have hzero := (zeroCode_realize z t ρ hzt).mp hz
  apply ordinal_transitive_true z p q 0 ρ hzp hzq hpq
  simpa [HFCoding.ordinal, HFCoding.empty] using hzero

end PASoundness.PAtoCompactZeroTransitive
