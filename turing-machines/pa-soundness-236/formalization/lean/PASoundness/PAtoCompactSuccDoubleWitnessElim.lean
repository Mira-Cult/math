import PASoundness.CompactNamed

/-! Generic finite K elimination of two existential witnesses. Each required
vacuity premise is explicit K proof data; this does not assume any semantic
truth or quotient property. -/
namespace PASoundness.PAtoCompactSuccDoubleWitnessElim
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed

/-- Given a proof from both witness bodies, eliminate the two existential
witnesses. Vacuity of the ambient hypotheses and goal is explicit. -/
def double_exists (w z E B C O : Nat)
    (vwE : KDerivation (imp E (allCode w E)))
    (vwH : KDerivation (imp (existsCode z C) (allCode w (existsCode z C))))
    (vwO : KDerivation (imp O (allCode w O)))
    (vwW : KDerivation (imp (existsCode w B) (allCode w (existsCode w B))))
    (vzE : KDerivation (imp E (allCode z E)))
    (vzH : KDerivation (imp (existsCode z C) (allCode z (existsCode z C))))
    (vzB : KDerivation (imp B (allCode z B)))
    (vzO : KDerivation (imp O (allCode z O)))
    (vzW : KDerivation (imp (existsCode w B) (allCode z (existsCode w B))))
    (step : KDerivation (imp E (imp B (imp C O)))) :
    KDerivation (imp E (imp (existsCode w B) (imp (existsCode z C) O))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let H := existsCode z C
  let Γ := [H, existsCode w B, E]
  have he : Context Γ E := .hypothesis (by simp [Γ])
  have hw : Context Γ (existsCode w B) := .hypothesis (by simp [Γ])
  have hz : Context Γ H := .head _ _
  apply Context.existsElim vwO _ hw
  apply Context.generalize w
  · intro a ha
    by_cases hh : a = H
    · subst a; exact vwH
    · by_cases hh' : a = existsCode w B
      · subst a
        exact vwW
      · have h : a = E := by simpa [Γ, hh, hh'] using ha
        subst a; exact vwE
  · apply Context.deduction
    let Δ := [B,H,existsCode w B,E]
    have hE : Context Δ E := .hypothesis (by simp [Δ])
    have hB : Context Δ B := .hypothesis (by simp [Δ])
    have hH : Context Δ H := .hypothesis (by simp [Δ])
    apply Context.existsElim vzO _ hH
    apply Context.generalize z
    · intro a ha
      by_cases hB' : a = B
      · subst a; exact vzB
      · by_cases hH' : a = H
        · subst a; exact vzH
        · by_cases hW' : a = existsCode w B
          · subst a
            exact vzW
          · have h : a = E := by simpa [Δ, hB', hH', hW'] using ha
            subst a; exact vzE
    · apply Context.deduction
      let Θ := [C,B,H,existsCode w B,E]
      have hC : Context Θ C := .hypothesis (by simp [Θ])
      have hB : Context Θ B := .hypothesis (by simp [Θ])
      have hE : Context Θ E := .hypothesis (by simp [Θ])
      exact .mp hC (.mp hB (.mp hE (.closed step)))

end PASoundness.PAtoCompactSuccDoubleWitnessElim

#print axioms PASoundness.PAtoCompactSuccDoubleWitnessElim.double_exists
