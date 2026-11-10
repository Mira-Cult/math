import PASoundness.PAtoCompactLiteralCutBaseAlpha
import PASoundness.PAtoCompactGuardBaseTransport
import PASoundness.PAtoCompactMultiplicationCandidate
import PASoundness.PAtoCompactAdjunction

/-! Finite K reallocation of a supplied canonical multiplication graph-step
proof.  Candidate and literal-cut private binders move from base 100 to 300;
all operand names remain 30,31,32,38,45.  The original graph-step proof is
an explicit input. This does not construct multiplication or prove totality. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationCanonicalBaseStep
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactMultiplicationCandidate
open PASoundness.PAtoCompactGuardBaseTransport PASoundness.PAtoCompactLiteralCutBaseSyntax
open PASoundness.PAtoCompactLiteralCutBaseAlpha PASoundness.PAtoCompactAdjunction
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Old raw product at the displayed canonical parameter names. -/
def rawOld : Formula := replace 2 32 (replace 1 31 (replace 0 30 productFormula))
/-- New raw product after incrementing the first factor. -/
def rawNew : Formula := replace 2 45 (replace 1 31 (replace 0 38 productFormula))

/-- Curried canonical extension obligation with allocator-indexed guards.
The old/new product relations and successor retain their literal names. -/
def canonical (b : Nat) : Formula :=
  .imp (domainAt b 30) (.imp (domainAt b 31) (.imp (domainAt b 32)
    (.imp (namedSuccessor 30 38 39) (.imp (domainAt b 38) (.imp rawOld
      (.imp (domainAt b 45) (.imp (literalCutAt b 32 31 45) rawNew)))))))

def canonical100 : Formula := canonical 100
def canonical300 : Formula := canonical 300

/-- Reallocate all five candidate guards and the anchored cut, then apply the
supplied finite K proof.  No proof of the graph-extension obligation is
asserted by this transformer. -/
noncomputable def canonical_step_rebase
    (h : KDerivation canonical100.encode) : KDerivation canonical300.encode := by
  let D (b x : Nat) := (domainAt b x).encode
  let C (b : Nat) := (literalCutAt b 32 31 45).encode
  let S := (namedSuccessor 30 38 39).encode
  let O := rawOld.encode
  let N := rawNew.encode
  change KDerivation (imp (D 300 30) (imp (D 300 31) (imp (D 300 32)
    (imp S (imp (D 300 38) (imp O (imp (D 300 45) (imp (C 300) N))))))))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [C 300,D 300 45,O,D 300 38,S,D 300 32,D 300 31,D 300 30]
  have h30 : Context Γ (D 300 30) := .hypothesis (by simp [Γ])
  have h31 : Context Γ (D 300 31) := .hypothesis (by simp [Γ])
  have h32 : Context Γ (D 300 32) := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have h38 : Context Γ (D 300 38) := .hypothesis (by simp [Γ])
  have ho : Context Γ O := .hypothesis (by simp [Γ])
  have h45 : Context Γ (D 300 45) := .hypothesis (by simp [Γ])
  have hc : Context Γ (C 300) := .head _ _
  have c30 : Context Γ (D 100 30) := .mp h30 (.closed (domainAt_transport 300 100 30 (by decide) (by decide)))
  have c31 : Context Γ (D 100 31) := .mp h31 (.closed (domainAt_transport 300 100 31 (by decide) (by decide)))
  have c32 : Context Γ (D 100 32) := .mp h32 (.closed (domainAt_transport 300 100 32 (by decide) (by decide)))
  have c38 : Context Γ (D 100 38) := .mp h38 (.closed (domainAt_transport 300 100 38 (by decide) (by decide)))
  have c45 : Context Γ (D 100 45) := .mp h45 (.closed (domainAt_transport 300 100 45 (by decide) (by decide)))
  have cc : Context Γ (C 100) := .mp hc (.closed (base_alpha 300 100 32 31 45
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).forward)
  have hi : Context Γ (imp (D 100 30) (imp (D 100 31) (imp (D 100 32)
      (imp S (imp (D 100 38) (imp O (imp (D 100 45) (imp (C 100) N)))))))) := by
    change KDerivation (imp (D 100 30) (imp (D 100 31) (imp (D 100 32)
      (imp S (imp (D 100 38) (imp O (imp (D 100 45) (imp (C 100) N)))))))) at h
    exact .closed h
  exact .mp cc (.mp c45 (.mp ho (.mp c38 (.mp hs (.mp c32 (.mp c31 (.mp c30 hi)))))))

theorem canonical_step_rebase_certificate (h : KDerivation canonical100.encode) :
    theoremCode (certificate (canonical_step_rebase h)) = canonical300.encode := certificate_correct _
end PASoundness.PAtoCompactMultiplicationCanonicalBaseStep
#print axioms PASoundness.PAtoCompactMultiplicationCanonicalBaseStep.canonical_step_rebase
#print axioms PASoundness.PAtoCompactMultiplicationCanonicalBaseStep.canonical_step_rebase_certificate
