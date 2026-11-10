import PASoundness.PAtoCompactMultiplicationCanonicalBaseStep
import PASoundness.PAtoCompactMultiplicationAllocatedStepTransport
import PASoundness.PAtoCompactMultiplicationAnchoredLocal
import PASoundness.PAtoCompactRawSuccessorBinderBridge

/-! Capture-safe K proof-data transport from the canonical *conditional* raw
multiplication successor obligation to the exact induction-interface graph
extension obligation.  The canonical K derivation is an explicit input; this
does not supply that derivation, collect a product graph, or prove totality. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationExtensionTargetRebase
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactLiteralCutBaseSyntax
open PASoundness.PAtoCompactMultiplicationCanonicalBaseStep
open PASoundness.PAtoCompactMultiplicationAllocatedStepTransport
open PASoundness.PAtoCompactMultiplicationAnchoredLocal
open PASoundness.PAtoCompactRawSuccessorBinderBridge
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def relabeled30 : Formula := replace 30 204 canonical300
private def relabeled31 : Formula := replace 31 30 relabeled30
private def relabeled38 : Formula := replace 38 205 relabeled31
private def actualRawStep : Formula :=
  .imp (domainAt 300 204) (.imp (domainAt 300 30) (.imp (domainAt 300 32)
    (.imp (namedSuccessor 204 205 39) (.imp (domainAt 300 205) (.imp oldRaw
      (.imp (domainAt 300 45) (.imp (literalCutAt 300 32 30 45) newRaw)))))))

private theorem relabeled_shape : relabeled38 = actualRawStep := by decide

/-- Specialize after moving the private allocator block to 300. The sequence
30→204 before 31→30 prevents overwriting the first input. -/
noncomputable def raw_step_at_induction_names (h : KDerivation canonical300.encode) :
    KDerivation actualRawStep.encode := by
  have i30 := universalInstance 30 204 canonical300 (by decide) (by decide) (by decide)
  have d30 : KDerivation relabeled30.encode := .mp (.generalize 30 h) i30
  have i31 := universalInstance 31 30 relabeled30 (by decide) (by decide) (by decide)
  have d31 : KDerivation relabeled31.encode := .mp (.generalize 31 d30) i31
  have i38 := universalInstance 38 205 relabeled31 (by decide) (by decide) (by decide)
  have d38 : KDerivation relabeled38.encode := .mp (.generalize 38 d31) i38
  rwa [relabeled_shape] at d38

/-- The explicitly supplied raw extension proof, after guard rebasing and
safe name specialization, yields the exact allocated graph-extension proof
needed by the multiplication induction. No graph-extension proof is assumed
implicitly: `h` is a finite K derivation of the canonical raw obligation. -/
noncomputable def extension_from_canonical (h : KDerivation canonical100.encode) :
    KDerivation graphExtensionCode := by
  have hbase : KDerivation canonical300.encode := canonical_step_rebase h
  have hraw : KDerivation actualRawStep.encode := raw_step_at_induction_names hbase
  let D := (domainAt 300 204).encode
  let G := (domainAt 300 30).encode
  let O := (domainAt 300 32).encode
  let S := successorCode 204 205 208
  let T := (domainAt 300 205).encode
  let M := (mulAt 300 204 30 32).encode
  let Z := (domainAt 300 45).encode
  let C := (literalCutAt 300 32 30 45).encode
  let Γ := [C,Z,M,T,S,O,G,D]
  change KDerivation (imp D (imp G (imp O (imp S (imp T (imp M (imp Z (imp C
    (mulAt 300 205 30 45).encode))))))))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  have hd : Context Γ D := .hypothesis (by simp [Γ])
  have hg : Context Γ G := .hypothesis (by simp [Γ])
  have ho : Context Γ O := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have ht : Context Γ T := .hypothesis (by simp [Γ])
  have hm : Context Γ M := .hypothesis (by simp [Γ])
  have hz : Context Γ Z := .hypothesis (by simp [Γ])
  have hc : Context Γ C := .head _ _
  have hs' : Context Γ (successorCode 204 205 39) :=
    .mp hs (.closed (raw_successor_rename 204 205 208 39 (by decide) (by decide) (by decide) (by decide)))
  have hm' : Context Γ oldRaw.encode := .mp hm (.closed old_allocated_to_raw)
  have hr : Context Γ (imp D (imp G (imp O (imp (successorCode 204 205 39)
      (imp T (imp oldRaw.encode (imp Z (imp C newRaw.encode)))))))) := by
    simpa [actualRawStep, Formula.encode, namedSuccessor, namedSuccessorBody,
      namedBoth, namedEither, CompactProof.both, CompactProof.neg,
      CompactDerivations.either, successorCode] using
      (Context.closed (Γ := Γ) hraw)
  have hn : Context Γ newRaw.encode :=
    .mp hc (.mp hz (.mp hm' (.mp ht (.mp hs' (.mp ho (.mp hg (.mp hd hr)))))))
  exact .mp hn (.closed new_raw_to_allocated)

theorem extension_from_canonical_certificate (h : KDerivation canonical100.encode) :
    theoremCode (certificate (extension_from_canonical h)) = graphExtensionCode :=
  certificate_correct _
end PASoundness.PAtoCompactMultiplicationExtensionTargetRebase
#print axioms PASoundness.PAtoCompactMultiplicationExtensionTargetRebase.raw_step_at_induction_names
#print axioms PASoundness.PAtoCompactMultiplicationExtensionTargetRebase.extension_from_canonical
#print axioms PASoundness.PAtoCompactMultiplicationExtensionTargetRebase.extension_from_canonical_certificate
