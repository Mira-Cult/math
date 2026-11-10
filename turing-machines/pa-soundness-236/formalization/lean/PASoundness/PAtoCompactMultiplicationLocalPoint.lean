import PASoundness.PAtoCompactMultiplicationRestrictedInductionInstance
import PASoundness.PAtoCompactMultiplicationPredecessorDomainAlign
import PASoundness.PAtoCompactMultiplicationStepOutputAlpha
import PASoundness.PAtoCompactFreeVacuity
import PASoundness.PAtoCompactUniformStep

/-! Conditional K multiplication induction point. A local successor law
which constructs a candidate output is an explicit finite K proof input.
No multiplication graph extension or totality is claimed. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationLocalPoint
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactUniformStep
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactMultiplicationRestrictedInductionInstance
open PASoundness.PAtoCompactMultiplicationPredecessorDomainAlign
open PASoundness.PAtoCompactMultiplicationStepOutputAlpha
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Old product-output matrix for first-factor predecessor 204. -/
def oldOutput : Formula := andF (domainAt 300 32) (mulAt 300 204 30 32)
/-- New output matrix, with the induction variable advanced to 205. -/
def newOutput : Formula := andF (domainAt 300 32) (mulAt 300 205 30 32)
/-- The generated existential target uses the original output binder 32. -/
def result : Formula := .ex 32 newOutput
/-- Local new-output existential uses fresh witness label 45. -/
def newOutput45 : Formula := andF (domainAt 300 45) (mulAt 300 205 30 45)

private theorem previous_shape : replace 31 204 predicate =
    .imp (domainAt 300 30) (.ex 32 oldOutput) := by decide
private theorem next_shape : replace 31 205 predicate =
    .imp (domainAt 300 30) result := by decide

/-- Given a K local successor witness constructor, an old candidate product
witness can be eliminated to obtain the new candidate product witness. -/
def witness_bind
    (hstep : KDerivation (imp (domainAt 300 204).encode
      (imp (domainAt 300 30).encode (imp (domainAt 300 32).encode
        (imp (successorCode 204 205 208) (imp (mulAt 300 204 30 32).encode
          (existsCode 45 newOutput45.encode))))))) :
    KDerivation (imp (domainAt 300 204).encode (imp (domainAt 300 30).encode
      (imp (successorCode 204 205 208) (imp (existsCode 32 oldOutput.encode) result.encode)))) := by
  let D := (domainAt 300 204).encode
  let G := (domainAt 300 30).encode
  let S := successorCode 204 205 208
  let O := oldOutput.encode
  let R := result.encode
  have hpoint : KDerivation (imp D (imp G (imp S (imp O R)))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let Γ := [O,S,G,D]
    have ho : Context Γ O := .head _ _
    have hs : Context Γ S := .hypothesis (by simp [Γ])
    have hg : Context Γ G := .hypothesis (by simp [Γ])
    have hd : Context Γ D := .hypothesis (by simp [Γ])
    have hc : Context Γ (both (domainAt 300 32).encode (mulAt 300 204 30 32).encode) := by
      simpa [O,oldOutput,andF,Formula.encode,Formula.not,both,neg] using ho
    have hm := Context.conjunctionRight hc
    have hw := Context.conjunctionLeft hc
    have he : Context Γ (existsCode 45 newOutput45.encode) :=
      .mp hm (.mp hs (.mp hw (.mp hg (.mp hd (.closed hstep)))))
    exact .mp he (.closed output_alpha)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [existsCode 32 O,S,G,D]
  have he : Context Γ (existsCode 32 O) := .head _ _
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hg : Context Γ G := .hypothesis (by simp [Γ])
  have hd : Context Γ D := .hypothesis (by simp [Γ])
  have hc : Context Γ (imp O R) := .mp hs (.mp hg (.mp hd (.closed hpoint)))
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 32 h)) := by
    intro h hh
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hh
    by_cases he : h = existsCode 32 O
    · subst h; exact free_vacuity 32 (.ex 32 oldOutput) (by decide)
    by_cases hs : h = S
    · subst h; exact (namedSuccessor 204 205 208).vacuity 32 (by decide)
    by_cases hg : h = G
    · subst h; exact (domainAt 300 30).vacuity 32 (by decide)
    have hd : h = D := by simpa [he,hs,hg] using hh
    subst h
    exact (domainAt 300 204).vacuity 32 (by decide)
  have hall := Context.generalize 32 hv hc
  exact Context.existsElim (free_vacuity 32 result (by decide)) hall he

/-- The exact candidate-restricted point premise follows from the displayed
local successor witness constructor. Both candidates and the predecessor
core remain visible as literal K antecedents. -/
def guarded_point
    (hstep : KDerivation (imp (domainAt 300 204).encode
      (imp (domainAt 300 30).encode (imp (domainAt 300 32).encode
        (imp (successorCode 204 205 208) (imp (mulAt 300 204 30 32).encode
          (existsCode 45 newOutput45.encode))))))) :
    KDerivation (imp (candidateCode 204 230 209 210 232 31 203 231 206)
      (imp (candidateCode 205 234 209 210 237 31 240 231 206)
        (imp (predecessorCore 201 204 205 208 209 210)
          (imp (replace 31 204 predicate).encode (replace 31 205 predicate).encode)))) := by
  rw [previous_shape,next_shape]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let C := candidateCode 204 230 209 210 232 31 203 231 206
  let T := candidateCode 205 234 209 210 237 31 240 231 206
  let P := predecessorCore 201 204 205 208 209 210
  let G := (domainAt 300 30).encode
  let B := imp G (existsCode 32 oldOutput.encode)
  let Γ := [G,B,P,T,C]
  have hg : Context Γ G := .head _ _
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  have hp : Context Γ P := .hypothesis (by simp [Γ])
  have hc : Context Γ C := .hypothesis (by simp [Γ])
  have hd : Context Γ (domainAt 300 204).encode := .mp hc (.closed predecessor_guard_align)
  have hs : Context Γ (successorCode 204 205 208) :=
    Context.conjunctionLeft (Context.conjunctionRight hp)
  have ho : Context Γ (existsCode 32 oldOutput.encode) := .mp hg hb
  exact .mp ho (.mp hs (.mp hg (.mp hd (.closed (witness_bind hstep)))))

theorem guarded_point_certificate
    (hstep : KDerivation (imp (domainAt 300 204).encode
      (imp (domainAt 300 30).encode (imp (domainAt 300 32).encode
        (imp (successorCode 204 205 208) (imp (mulAt 300 204 30 32).encode
          (existsCode 45 newOutput45.encode))))))) :
    theoremCode (certificate (guarded_point hstep)) =
      imp (candidateCode 204 230 209 210 232 31 203 231 206)
        (imp (candidateCode 205 234 209 210 237 31 240 231 206)
          (imp (predecessorCore 201 204 205 208 209 210)
            (imp (replace 31 204 predicate).encode (replace 31 205 predicate).encode))) :=
  certificate_correct (guarded_point hstep)
end PASoundness.PAtoCompactMultiplicationLocalPoint
#print axioms PASoundness.PAtoCompactMultiplicationLocalPoint.witness_bind
#print axioms PASoundness.PAtoCompactMultiplicationLocalPoint.guarded_point
#print axioms PASoundness.PAtoCompactMultiplicationLocalPoint.guarded_point_certificate
