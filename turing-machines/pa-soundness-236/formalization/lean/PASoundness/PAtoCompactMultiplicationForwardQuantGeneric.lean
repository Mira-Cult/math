import PASoundness.PAtoCompactMultiplicationCandidate
import PASoundness.PAtoCompactTransitiveClosure

/-! Conditional finite-K assembly of the literal extended product forward
clause. The old-major and top-major point proofs, successor projection, and
common-context vacuity are all explicit proof-data inputs. This does not
construct them, a product graph, multiplication totality, or a PA bridge. -/
namespace PASoundness.PAtoCompactMultiplicationForwardQuantGeneric
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactSuccessorInjective
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The queried source pair and target point in graph 64. -/
def triple64 (c : Nat) : Formula := replace 6 64 (tripleFormula 3 4 c)
/-- The exact forward existential witness and uniqueness clause. -/
def witness : Formula := .ex 5 (namedBoth (.member 45 5)
  (namedBoth (triple64 5) (.all 9 (.imp
    (namedBoth (.member 45 9) (triple64 9)) (.equal 9 5)))))
def point : Formula := .all 4 (.imp (.member 31 4) witness)
def newForward : Formula := replace 6 64 (replace 2 45 (replace 1 31 (replace 0 38 forwardFormula)))

theorem forward_shape : newForward = .all 3 (.imp (.member 38 3) point) := by decide

/-- With the named successor and each of the two point branches supplied
inside P, this builds the quantified forward clause. The supplied vacuity
proofs keep P fixed during generalization. -/
def forward_from_cases (P : Nat)
    (hS : KDerivation (imp P (successorCode 30 38 39)))
    (hOld : KDerivation (imp P (imp (member 30 3) (imp (member 31 4) witness.encode))))
    (hTop : KDerivation (imp P (imp (equal 3 30) (imp (member 31 4) witness.encode))))
    (hP3 : KDerivation (imp P (allCode 3 P)))
    (hP4 : KDerivation (imp P (allCode 4 P))) :
    KDerivation (imp P newForward.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [P]
  have hp : Context Γ P := .head _ _
  have hforall : Context Γ (allCode 3 (imp (member 38 3) (allCode 4
      (imp (member 31 4) witness.encode)))) := by
    apply Context.generalize 3
    · intro q hq
      have hq' : q = P := by simpa [Γ] using hq
      subst q
      exact hP3
    · apply Context.deduction
      let Δ := [member 38 3,P]
      have hsource : Context Δ (member 38 3) := .head _ _
      have hp' : Context Δ P := .under hp _
      have hs : Context Δ (successorCode 30 38 39) := .mp hp' (.closed hS)
      have hsplit : Context Δ (either (equal 3 30) (member 30 3)) :=
        .mp hsource (.mp hs (.closed (successor_inspect 30 38 39 3 (by decide) (by decide) (by decide))))
      apply Context.generalize 4
      · intro q hq
        change q ∈ Δ at hq
        by_cases hq1 : q = member 38 3
        · subst q
          exact membershipVacuity 38 3 4 (by decide) (by decide)
        · have hq2 : q = P := by simpa [Δ,hq1] using hq
          subst q
          exact hP4
      · apply Context.deduction
        let Θ := [member 31 4,member 38 3,P]
        have hminor : Context Θ (member 31 4) := .head _ _
        have hp'' : Context Θ P := .hypothesis (by simp [Θ])
        apply Context.disjunctionElim (.under hsplit _)
        · let Ξ := equal 3 30 :: Θ
          have he : Context Ξ (equal 3 30) := .head _ _
          exact .mp (.under hminor _) (.mp he (.mp (.under hp'' _) (.closed hTop)))
        · let Ξ := member 30 3 :: Θ
          have hm : Context Ξ (member 30 3) := .head _ _
          exact .mp (.under hminor _) (.mp hm (.mp (.under hp'' _) (.closed hOld)))
  rw [forward_shape]
  simpa [point,Formula.encode] using hforall

theorem forward_from_cases_certificate (P : Nat)
    (hS : KDerivation (imp P (successorCode 30 38 39)))
    (hOld : KDerivation (imp P (imp (member 30 3) (imp (member 31 4) witness.encode))))
    (hTop : KDerivation (imp P (imp (equal 3 30) (imp (member 31 4) witness.encode))))
    (hP3 : KDerivation (imp P (allCode 3 P)))
    (hP4 : KDerivation (imp P (allCode 4 P))) :
    theoremCode (certificate (forward_from_cases P hS hOld hTop hP3 hP4)) =
      imp P newForward.encode := certificate_correct _
end PASoundness.PAtoCompactMultiplicationForwardQuantGeneric
#print axioms PASoundness.PAtoCompactMultiplicationForwardQuantGeneric.forward_shape
#print axioms PASoundness.PAtoCompactMultiplicationForwardQuantGeneric.forward_from_cases
#print axioms PASoundness.PAtoCompactMultiplicationForwardQuantGeneric.forward_from_cases_certificate
