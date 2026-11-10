import PASoundness.PAtoCompactSuccessorInjective

/-! The pointwise successor-prefix case split for partial composition. The
old/new case derivations and path are supplied hypotheses; no graph exists by
this result alone. Literal compact bottom remains code 1. -/
namespace PASoundness.PAtoCompactCompositionForwardCases
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactSuccessorInjective
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Any member of successor prefix 13 is either old-prefix endpoint 10 or an
old member of prefix 10. Given explicit implications for both cases, transfer
an arbitrary supplied path code to an arbitrary target code. -/
def forward_cases (path target : Nat) : KDerivation
    (imp (successorCode 10 13 15)
      (imp (imp (member 10 2) (imp path target))
        (imp (imp (equal 2 10) (imp path target))
          (imp (member 13 2) (imp path target))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let S := successorCode 10 13 15
  let O := imp (member 10 2) (imp path target)
  let N := imp (equal 2 10) (imp path target)
  let Γ := [path,member 13 2,N,O,S]
  have hp : Context Γ path := Context.head _ _
  have hm : Context Γ (member 13 2) := .hypothesis (by simp [Γ])
  have hn : Context Γ N := .hypothesis (by simp [Γ])
  have ho : Context Γ O := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hsplit : Context Γ (either (equal 2 10) (member 10 2)) :=
    .mp hm (.mp hs (.closed (successor_inspect 10 13 15 2 (by decide) (by decide) (by decide))))
  apply Context.disjunctionElim hsplit
  · have he : Context (equal 2 10 :: Γ) (equal 2 10) := Context.head _ _
    exact .mp (Context.under hp _) (.mp he (Context.under hn _))
  · have he : Context (member 10 2 :: Γ) (member 10 2) := Context.head _ _
    exact .mp (Context.under hp _) (.mp he (Context.under ho _))

theorem forward_cases_certificate (path target : Nat) :
    theoremCode (certificate (forward_cases path target)) =
      imp (successorCode 10 13 15)
        (imp (imp (member 10 2) (imp path target))
          (imp (imp (equal 2 10) (imp path target))
            (imp (member 13 2) (imp path target)))) :=
  certificate_correct (forward_cases path target)

end PASoundness.PAtoCompactCompositionForwardCases

#print axioms PASoundness.PAtoCompactCompositionForwardCases.forward_cases
#print axioms PASoundness.PAtoCompactCompositionForwardCases.forward_cases_certificate
