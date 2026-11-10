import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.PAtoCompactEmptyExtrema
import PASoundness.CompactQuantifiers

/-! Two objects satisfying explicit zero graphs satisfy the proposed
order-isomorphism relation by vacuity. This is a finite K proof, not an
assertion of reflexivity, congruence, or graph collection for nonempty inputs.
Code 1 remains the literal compact bottom formula. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactOrderIsoZero
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactEmptyExtrema
open PASoundness.PAtoCompactOrderIsomorphism
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def leftConsequent : Nat := match bijectionFormula with
  | .imp (.imp (.all _ (.imp _ b)) _) _ => b.encode
  | _ => 0

def rightConsequent : Nat := match bijectionFormula with
  | .imp (.imp _ (.imp (.all _ (.imp _ b)) .bottom)) .bottom => b.encode
  | _ => 0

def orderTail : Nat := match orderFormula with
  | .all _ (.all _ (.all _ (.all _ (.imp
      (.imp (.imp _ (.imp tail .bottom)) .bottom) _)))) => tail.encode
  | _ => 0

def orderConsequent : Nat := match orderFormula with
  | .all _ (.all _ (.all _ (.all _ (.imp _ rhs)))) => rhs.encode
  | _ => 0

/-- The zero graph yields a guarded implication with an arbitrary conclusion. -/
def zero_guard (x z v R : Nat) (hvz : z ≠ v) (hzx : z ≠ x) :
    KDerivation (imp (zeroCode x z) (imp (member x v) R)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member x v, zeroCode x z]
  have hv : Context Γ (member x v) := Context.head _ _
  have hz : Context Γ (zeroCode x z) := .hypothesis (by simp [Γ])
  have hn : Context Γ (neg (member x v)) := .mp hz (.closed (zero_excludes x z v hvz hzx))
  exact Context.explode R (.mp hv hn)

/-- A guarded implication generalizes over an explicitly fresh index. -/
def zero_guard_all (x z v R : Nat) (hvx : v ≠ x) (hvz : v ≠ z) (hzx : z ≠ x) :
    KDerivation (imp (zeroCode x z) (allCode v (imp (member x v) R))) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [zeroCode x z]
  have hz : Context Γ (zeroCode x z) := Context.head [] _
  have hi : Context Γ (imp (member x v) R) :=
    .mp hz (.closed (zero_guard x z v R (Ne.symm hvz) hzx))
  have hf : ∀ h, h ∈ Γ → KDerivation (imp h (allCode v h)) := by
    intro h hh
    have he : h = zeroCode x z := by simpa [Γ] using hh
    subst h
    exact zero_vacuity x z v hvx hvz
  exact Context.generalize v hf hi

/-- Under the first zero graph, the candidate order clause holds for an
arbitrary graph variable; the alleged first input member is impossible. -/
def zero_order : KDerivation (imp (zeroCode 0 7) orderFormula.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Z := zeroCode 0 7
  let Γ := [Z]
  have hz : Context Γ Z := Context.head [] Z
  have hlocal : Context Γ
      (imp (both (member 0 2) orderTail) orderConsequent) := by
    apply Context.deduction
    let Δ := [both (member 0 2) orderTail,Z]
    have ha : Context Δ (both (member 0 2) orderTail) := Context.head _ _
    have hm : Context Δ (member 0 2) := Context.conjunctionLeft ha
    have hz' : Context Δ Z := .hypothesis (by simp [Δ])
    have hn : Context Δ (neg (member 0 2)) := .mp hz' (.closed (zero_excludes 0 7 2 (by decide) (by decide)))
    exact Context.explode orderConsequent (.mp hm hn)
  have v5 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 5 h)) := by
    intro h hh
    have he : h = Z := by simpa [Γ] using hh
    subst h
    exact zero_vacuity 0 7 5 (by decide) (by decide)
  have v3 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 3 h)) := by
    intro h hh
    have he : h = Z := by simpa [Γ] using hh
    subst h
    exact zero_vacuity 0 7 3 (by decide) (by decide)
  have v4 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 4 h)) := by
    intro h hh
    have he : h = Z := by simpa [Γ] using hh
    subst h
    exact zero_vacuity 0 7 4 (by decide) (by decide)
  have v2 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 2 h)) := by
    intro h hh
    have he : h = Z := by simpa [Γ] using hh
    subst h
    exact zero_vacuity 0 7 2 (by decide) (by decide)
  have hh := Context.generalize 2 v2 (Context.generalize 4 v4
    (Context.generalize 3 v3 (Context.generalize 5 v5 hlocal)))
  exact hh

/-- Any two inputs with zero graphs satisfy the literal quotient proposal. -/
def two_zeros_equivalent : KDerivation
    (imp (zeroCode 0 7) (imp (zeroCode 1 7) equivalentFormula.encode)) := by
  let Z0 := zeroCode 0 7
  let Z1 := zeroCode 1 7
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [Z1,Z0]
  have hz0 : Context Γ Z0 := .hypothesis (by simp [Γ])
  have hz1 : Context Γ Z1 := Context.head _ _
  have hl : Context Γ (allCode 2 (imp (member 0 2) leftConsequent)) :=
    .mp hz0 (.closed (zero_guard_all 0 7 2 leftConsequent (by decide) (by decide) (by decide)))
  have hr : Context Γ (allCode 3 (imp (member 1 3) rightConsequent)) :=
    .mp hz1 (.closed (zero_guard_all 1 7 3 rightConsequent (by decide) (by decide) (by decide)))
  have hb : Context Γ bijectionFormula.encode := Context.conjunctionIntro hl hr
  have ho : Context Γ orderFormula.encode := .mp hz0 (.closed zero_order)
  have hbo := Context.conjunctionIntro hb ho
  have hi := CompactNamed.existsIntroduce 6
    ((bijectionFormula.imp orderFormula.not).not) (by decide)
  exact .mp hbo (.closed hi)

theorem two_zeros_equivalent_certificate :
    theoremCode (certificate two_zeros_equivalent) =
      imp (zeroCode 0 7) (imp (zeroCode 1 7) equivalentFormula.encode) :=
  certificate_correct two_zeros_equivalent

end PASoundness.PAtoCompactOrderIsoZero

#print axioms PASoundness.PAtoCompactOrderIsoZero.two_zeros_equivalent
#print axioms PASoundness.PAtoCompactOrderIsoZero.two_zeros_equivalent_certificate
