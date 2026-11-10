import PASoundness.PAtoCompactPAAddSuccUniformBase
import PASoundness.PAtoCompactRawSuccBridge

/-! Freshen the raw successor test binder in a fixed-name allocated addition
successor derivation. No arbitrary operand renaming or PA axiom is claimed. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPAAddSuccFreshTest
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactRawSuccBridge
open PASoundness.PAtoCompactPAAddSuccUniformBase
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Move the bound raw-successor test to the fixed name 39. Equality of the
old and new test names is permitted; both are fresh for the two operands. -/
def successor_test_to_39 (x y w : Nat) (hxw : x ≠ w) (hyw : y ≠ w)
    (hx39 : x ≠ 39) (hy39 : y ≠ 39) :
    KDerivation (imp (successorCode x y w) (successorCode x y 39)) := by
  by_cases hw : w = 39
  · subst w
    exact PASoundness.CompactHilbertBasis.identity _
  · have h := raw_successor_alpha x y w 39 hw hxw hyw hx39 hy39
    simpa [namedSuccessor, namedSuccessorBody, namedBoth, namedEither, successorCode,
      Formula.encode, CompactProof.both, CompactProof.neg, CompactDerivations.either] using h

/-- For a fresh test name w, the fixed operand addition step holds with both
raw successor tests using w. Names of represented values are not required to
be semantically distinct. -/
noncomputable def fixed_fresh_test_step (b w : Nat) (hb : 46 ≤ b)
    (h31 : 31 ≠ w) (h32 : 32 ≠ w) (h38 : 38 ≠ w) (h45 : 45 ≠ w) :
    KDerivation (imp (domainAt b 31).encode (imp (domainAt b 32).encode
      (imp (successorCode 31 38 w) (imp (successorCode 32 45 w)
        (imp (addAt b 30 31 32).encode (addAt b 30 38 45).encode))))) := by
  have hs := successor_test_to_39 31 38 w h31 h38 (by decide) (by decide)
  have ht := successor_test_to_39 32 45 w h32 h45 (by decide) (by decide)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(addAt b 30 31 32).encode, successorCode 32 45 w,
    successorCode 31 38 w, (domainAt b 32).encode, (domainAt b 31).encode]
  have hA : Context Γ (addAt b 30 31 32).encode := .head _ _
  have hT : Context Γ (successorCode 32 45 w) := .hypothesis (by simp [Γ])
  have hS : Context Γ (successorCode 31 38 w) := .hypothesis (by simp [Γ])
  have hE : Context Γ (domainAt b 32).encode := .hypothesis (by simp [Γ])
  have hD : Context Γ (domainAt b 31).encode := .hypothesis (by simp [Γ])
  have hS' : Context Γ (successorCode 31 38 39) := .mp hS (.closed hs)
  have hT' : Context Γ (successorCode 32 45 39) := .mp hT (.closed ht)
  exact .mp hA (.mp hT' (.mp hS' (.mp hE (.mp hD (.closed (uniform_base_step b hb))))))

theorem fixed_fresh_test_step_certificate (b w : Nat) (hb : 46 ≤ b)
    (h31 : 31 ≠ w) (h32 : 32 ≠ w) (h38 : 38 ≠ w) (h45 : 45 ≠ w) :
    theoremCode (certificate (fixed_fresh_test_step b w hb h31 h32 h38 h45)) =
      imp (domainAt b 31).encode (imp (domainAt b 32).encode
        (imp (successorCode 31 38 w) (imp (successorCode 32 45 w)
          (imp (addAt b 30 31 32).encode (addAt b 30 38 45).encode)))) := certificate_correct _
end PASoundness.PAtoCompactPAAddSuccFreshTest
#print axioms PASoundness.PAtoCompactPAAddSuccFreshTest.successor_test_to_39
#print axioms PASoundness.PAtoCompactPAAddSuccFreshTest.fixed_fresh_test_step
#print axioms PASoundness.PAtoCompactPAAddSuccFreshTest.fixed_fresh_test_step_certificate
