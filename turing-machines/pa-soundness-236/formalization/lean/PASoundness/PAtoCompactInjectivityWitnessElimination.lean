import PASoundness.CompactDerivations

/-! Generic finite K elimination of two separately supplied existential
witnesses, retaining a common antecedent and explicit vacuity proofs. No graph
existence, successor cancellation, or PA-axiom translation is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactInjectivityWitnessElimination
open PASoundness.CompactProof PASoundness.CompactDerivations
attribute [local irreducible] PASoundness.CompactProof.imp PASoundness.Cantor.pair PASoundness.Cantor.triangle

/-- Eliminate the first and second witnesses under a shared premise. Every
vacuity and local implication is supplied as finite K proof data. No name
inequalities or assumptions about the values of witnesses are imposed here. -/
def eliminate_two_witnesses (a c M T U E F : Nat)
    (hA : KDerivation (imp M (existsCode a T)))
    (hC : KDerivation (imp M (existsCode c U)))
    (hE : KDerivation (imp M E))
    (hlocal : KDerivation (imp T (imp U (imp E F))))
    (hMa : KDerivation (imp M (allCode a M)))
    (hMc : KDerivation (imp M (allCode c M)))
    (hTc : KDerivation (imp T (allCode c T)))
    (hFa : KDerivation (imp F (allCode a F)))
    (hFc : KDerivation (imp F (allCode c F))) : KDerivation (imp M F) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [M]
  have hm : Context Γ M := Context.head [] M
  have hexA : Context Γ (existsCode a T) := .mp hm (.closed hA)
  have hallA : Context Γ (allCode a (imp T F)) := by
    apply Context.generalize a
    · intro h hh
      have he : h = M := by simpa [Γ] using hh
      subst h
      exact hMa
    · apply Context.deduction
      let Δ := [T,M]
      have ht : Context Δ T := Context.head [M] T
      have hm' : Context Δ M := .hypothesis (by simp [Δ])
      have hexC : Context Δ (existsCode c U) := .mp hm' (.closed hC)
      have hallC : Context Δ (allCode c (imp U F)) := by
        apply Context.generalize c
        · intro h hh
          have he : h = T ∨ h = M := by simpa [Δ] using hh
          by_cases heq : h = T
          · subst h
            exact hTc
          · have hmEq : h = M := he.resolve_left heq
            subst h
            exact hMc
        · apply Context.deduction
          let Θ := [U,T,M]
          have hu : Context Θ U := Context.head [T,M] U
          have ht' : Context Θ T := .hypothesis (by simp [Θ])
          have hm'' : Context Θ M := .hypothesis (by simp [Θ])
          have he : Context Θ E := .mp hm'' (.closed hE)
          exact .mp he (.mp hu (.mp ht' (.closed hlocal)))
      exact Context.existsElim hFc hallC hexC
  exact Context.existsElim hFa hallA hexA

theorem eliminate_two_witnesses_certificate (a c M T U E F : Nat)
    (hA : KDerivation (imp M (existsCode a T)))
    (hC : KDerivation (imp M (existsCode c U)))
    (hE : KDerivation (imp M E))
    (hlocal : KDerivation (imp T (imp U (imp E F))))
    (hMa : KDerivation (imp M (allCode a M)))
    (hMc : KDerivation (imp M (allCode c M)))
    (hTc : KDerivation (imp T (allCode c T)))
    (hFa : KDerivation (imp F (allCode a F)))
    (hFc : KDerivation (imp F (allCode c F))) :
    theoremCode (certificate (eliminate_two_witnesses a c M T U E F
      hA hC hE hlocal hMa hMc hTc hFa hFc)) = imp M F := certificate_correct _

end PASoundness.PAtoCompactInjectivityWitnessElimination

#print axioms PASoundness.PAtoCompactInjectivityWitnessElimination.eliminate_two_witnesses
#print axioms PASoundness.PAtoCompactInjectivityWitnessElimination.eliminate_two_witnesses_certificate
