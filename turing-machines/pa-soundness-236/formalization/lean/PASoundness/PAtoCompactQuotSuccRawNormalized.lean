import PASoundness.PAtoCompactQuotSuccInjectiveRaw
import PASoundness.PAtoCompactQuotSuccCandidateAlign

/-! Compose raw successor cancellation with the actual binder-alignment proofs
for both quotient-successor witness domains. The displayed raw graphs,
predecessor domain, equivalences and guarded endpoint remain explicit. No
quotient-successor existential is eliminated here. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactQuotSuccRawNormalized
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactQuotientSuccessor
open PASoundness.PAtoCompactEquivalentAliasInstantiation PASoundness.PAtoCompactEquivalentAliasGuardLift
open PASoundness.PAtoCompactQuotSuccInjectiveRaw PASoundness.PAtoCompactQuotSuccCandidateAlign
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The exact literal domains for raw successor witnesses 0 and 1 provide the
symmetry/transitivity candidate forms needed by raw cancellation. -/
def raw_normalized : KDerivation
    (imp (successorCode 2 0 9) (imp (successorCode 5 1 10)
      (imp (domainFormula 5).encode (imp (domainFormula 0).encode
        (imp (domainFormula 1).encode (imp edge07.encode (imp edge78.encode
          (imp edge18.encode (guarded originalAliases).encode)))))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let S := successorCode 2 0 9
  let T := successorCode 5 1 10
  let D5 := (domainFormula 5).encode
  let D0 := (domainFormula 0).encode
  let D1 := (domainFormula 1).encode
  let Γ := [edge18.encode,edge78.encode,edge07.encode,D1,D0,D5,T,S]
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have ht : Context Γ T := .hypothesis (by simp [Γ])
  have hd5 : Context Γ D5 := .hypothesis (by simp [Γ])
  have hd0 : Context Γ D0 := .hypothesis (by simp [Γ])
  have hd1 : Context Γ D1 := .hypothesis (by simp [Γ])
  have h07 : Context Γ edge07.encode := .hypothesis (by simp [Γ])
  have h78 : Context Γ edge78.encode := .hypothesis (by simp [Γ])
  have h18 : Context Γ edge18.encode := Context.head _ _
  have hc0 : Context Γ candidate0 := .mp hd0 (.closed (domain_to_symmetry 0 (by decide)))
  have hc1 : Context Γ candidate1 := .mp hd1 (.closed (domain_to_symmetry 1 (by decide)))
  exact .mp h18 (.mp h78 (.mp h07 (.mp hc1 (.mp hc0 (.mp hd5
    (.mp ht (.mp hs (.closed raw_cancellation))))))))

theorem raw_normalized_certificate : theoremCode (certificate raw_normalized) =
    imp (successorCode 2 0 9) (imp (successorCode 5 1 10)
      (imp (domainFormula 5).encode (imp (domainFormula 0).encode
        (imp (domainFormula 1).encode (imp edge07.encode (imp edge78.encode
          (imp edge18.encode (guarded originalAliases).encode))))))) :=
  certificate_correct raw_normalized

end PASoundness.PAtoCompactQuotSuccRawNormalized

#print axioms PASoundness.PAtoCompactQuotSuccRawNormalized.raw_normalized
#print axioms PASoundness.PAtoCompactQuotSuccRawNormalized.raw_normalized_certificate
