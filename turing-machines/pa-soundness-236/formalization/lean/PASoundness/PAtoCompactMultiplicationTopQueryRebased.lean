import PASoundness.PAtoCompactMultiplicationTopQueryConditional
import PASoundness.PAtoCompactFreeVacuity

/-! Capture-safe top-row query specialization under the fixed old-clean and
row-no-garbage context. Generalization is performed inside that context, so
internal names 3,4,5 occurring bound in its assumptions do not capture the
queried coordinates. The old-major endpoint proof remains explicit here. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationTopQueryRebased
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactFixedFirstCoverageBase
open PASoundness.PAtoCompactMultiplicationOldTripleIntro PASoundness.PAtoCompactMultiplicationTripleEdgeAlpha
open PASoundness.PAtoCompactMultiplicationTopQueryConditional PASoundness.PAtoCompactFreeVacuity
attribute [local irreducible] imp Cantor.pair Cantor.triangle

private def clean : Formula := PASoundness.PAtoCompactProductOldSuffixExclusion.oldClean
private def garbage : Formula := noGarbage 64
private def ctx : List Nat := [garbage.encode,clean.encode]
private def result (u v : Nat) : Formula := namedBoth (.member 31 u) (graphFormula 6 u v)
private def body0 : Formula := .imp (.equal 3 30) (.imp queriedTriple (result 4 5))
private def body1 : Formula := .imp (replace 3 30 queriedTriple) (result 4 5)
private def body2 : Formula := replace 4 3 body1

private def ctx_vacuity (v : Nat) (hv : v ∈ [3,4,5]) :
    ∀ h, h ∈ ctx → KDerivation (imp h (allCode v h)) := by
  have hgv : v ∉ garbage.free := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl | rfl | rfl <;> decide
  have hcv : v ∉ clean.free := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl | rfl | rfl <;> decide
  intro h hh
  simp only [ctx,List.mem_cons,List.not_mem_nil,or_false] at hh
  by_cases he : h = garbage.encode
  · subst h
    exact free_vacuity v garbage hgv
  · have hc : h = clean.encode := by simpa [he] using hh
    subst h
    exact free_vacuity v clean hcv

/-- Under clean old graph and explicit no-garbage, an extended triple at the
new major coordinate implies its queried second coordinate is in source31 and
its output is an edge of the same graph6. The finite K major-endpoint proof for
the old clean graph is an explicit input. -/
def top_query_rebased
    (hOld : KDerivation (imp clean.encode (imp oldTriple.encode (member 30 3)))) :
    KDerivation (imp clean.encode (imp garbage.encode
      (imp (replace 6 64 (tripleFormula 30 3 70)).encode
        (both (member 31 3) (graphFormula 6 3 70).encode)))) := by
  have h0 : Context ctx body0.encode := by
    have hn : Context ctx garbage.encode := .head _ _
    have hc : Context ctx clean.encode := .hypothesis (by simp [ctx])
    have h := Context.mp hn (Context.mp hc (.closed (top_query_of_old_endpoint hOld)))
    simpa [body0,result,namedBoth,Formula.not,Formula.encode,both,neg,clean,garbage] using h
  have hgen3 := Context.generalize 3 (ctx_vacuity 3 (by decide)) h0
  have hi3 := universalInstance 3 30 body0 (by decide) (by decide) (by decide)
  have h1 : Context ctx (replace 3 30 body0).encode := .mp hgen3 (.closed hi3)
  have hs1 : replace 3 30 body0 = .imp (.equal 30 30) body1 := by decide
  rw [hs1] at h1
  have hb1 : Context ctx body1.encode := .mp (.closed (equalityReflexive 30)) h1
  have hgen4 := Context.generalize 4 (ctx_vacuity 4 (by decide)) hb1
  have hi4 := universalInstance 4 3 body1 (by decide) (by decide) (by decide)
  have hb2 : Context ctx body2.encode := .mp hgen4 (.closed hi4)
  have hgen5 := Context.generalize 5 (ctx_vacuity 5 (by decide)) hb2
  have hi5 := universalInstance 5 70 body2 (by decide) (by decide) (by decide)
  have hb3 : Context ctx (replace 5 70 body2).encode := .mp hgen5 (.closed hi5)
  have hs3 : replace 5 70 body2 = .imp (replace 6 64 (tripleFormula 30 3 70)) (result 3 70) := by decide
  rw [hs3] at hb3
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  simpa [ctx,clean,garbage,result,namedBoth,Formula.not,Formula.encode,both,neg] using hb3

theorem top_query_rebased_certificate
    (hOld : KDerivation (imp clean.encode (imp oldTriple.encode (member 30 3)))) :
    theoremCode (certificate (top_query_rebased hOld)) =
      imp clean.encode (imp garbage.encode
        (imp (replace 6 64 (tripleFormula 30 3 70)).encode
          (both (member 31 3) (graphFormula 6 3 70).encode))) :=
  certificate_correct (top_query_rebased hOld)
private def finalBody : Formula := .imp garbage
  (.imp (replace 6 64 (tripleFormula 30 3 70)) (result 3 70))

/-- The same query implication under the full-prefix no-garbage condition
obtained by replacing the row prefix 0 with source31. -/
def top_query_full_prefix
    (hOld : KDerivation (imp clean.encode (imp oldTriple.encode (member 30 3)))) :
    KDerivation (imp clean.encode (imp (replace 0 31 garbage).encode
      (imp (replace 6 64 (tripleFormula 30 3 70)).encode
        (both (member 31 3) (graphFormula 6 3 70).encode)))) := by
  let Γ := [clean.encode]
  have hc : Context Γ clean.encode := .head _ _
  have hp : Context Γ finalBody.encode := by
    have h := Context.mp hc (.closed (top_query_rebased hOld))
    simpa [finalBody,result,namedBoth,Formula.not,Formula.encode,both,neg] using h
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 0 h)) := by
    intro h hh
    have he : h = clean.encode := by simpa [Γ] using hh
    subst h
    exact free_vacuity 0 clean (by decide)
  have hall := Context.generalize 0 hv hp
  have hi := universalInstance 0 31 finalBody (by decide) (by decide) (by decide)
  have hresult : Context Γ (replace 0 31 finalBody).encode := .mp hall (.closed hi)
  have hs : replace 0 31 finalBody = .imp (replace 0 31 garbage)
      (.imp (replace 6 64 (tripleFormula 30 3 70)) (result 3 70)) := by decide
  rw [hs] at hresult
  apply Context.closeEmpty
  apply Context.deduction
  simpa [Γ,result,namedBoth,Formula.not,Formula.encode,both,neg] using hresult

theorem top_query_full_prefix_certificate
    (hOld : KDerivation (imp clean.encode (imp oldTriple.encode (member 30 3)))) :
    theoremCode (certificate (top_query_full_prefix hOld)) =
      imp clean.encode (imp (replace 0 31 garbage).encode
        (imp (replace 6 64 (tripleFormula 30 3 70)).encode
          (both (member 31 3) (graphFormula 6 3 70).encode))) :=
  certificate_correct (top_query_full_prefix hOld)

end PASoundness.PAtoCompactMultiplicationTopQueryRebased
#print axioms PASoundness.PAtoCompactMultiplicationTopQueryRebased.top_query_rebased
#print axioms PASoundness.PAtoCompactMultiplicationTopQueryRebased.top_query_rebased_certificate

#print axioms PASoundness.PAtoCompactMultiplicationTopQueryRebased.top_query_full_prefix
#print axioms PASoundness.PAtoCompactMultiplicationTopQueryRebased.top_query_full_prefix_certificate
