import PASoundness.PAtoCompactMultiplicationRowOldEntry
import PASoundness.PAtoCompactMultiplicationRowNewEntry
import PASoundness.PAtoCompactFreeVacuity
import PASoundness.PAtoCompactPointAdjoin

/-! Quantified no-garbage preservation for one represented multiplication-row
extension. The prefix inclusion, old no-garbage invariant, graph adjunction,
new-index memberships, map edge and both chosen pair witnesses are explicit K
antecedents. No pair-representative uniqueness, row graph existence, or
multiplication totality is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationRowNoGarbageStep
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactMultiplicationRowPrefixTransport
open PASoundness.PAtoCompactMultiplicationRowOldEntry PASoundness.PAtoCompactMultiplicationRowNewEntry
attribute [local irreducible] imp Cantor.pair Cantor.triangle

def extension : Formula := namedAdjoin 7 13 11 14

def newNoGarbage : Formula := .all 9 (.imp (.member 11 9) (entry 1))

private def adjoin_instance : KDerivation (imp extension.encode
    (imp (member 11 9) (either (equal 9 13) (member 7 9)))) := by
  let f : Formula := namedBoth
    (.imp (.member 11 14) (namedEither (.equal 14 13) (.member 7 14)))
    (.imp (namedEither (.equal 14 13) (.member 7 14)) (.member 11 14))
  have h := universalInstance 14 9 f (by decide) (by decide) (by decide)
  have hi : KDerivation (imp extension.encode
      (both (imp (member 11 9) (either (equal 9 13) (member 7 9)))
        (imp (either (equal 9 13) (member 7 9)) (member 11 9)))) := by
    simpa [f,extension,namedAdjoin,namedBoth,namedEither,Formula.not,Formula.encode,
      replace,rename,both,neg,either] using h
  apply Context.closeEmpty
  apply Context.deduction
  exact Context.conjunctionLeft (.mp (.head _ _) (.closed hi))

/-- Every member of new graph 11 is either an original graph entry or has a
row witness for prefix 1, given the displayed old invariant and exact chosen
new-row witnesses. The old and new edge cases preserve their own witnesses. -/
def no_garbage_step : KDerivation (imp prefixInclusion
    (imp oldNoGarbage.encode (imp extension.encode
      (imp (member 1 0) (imp (member 31 0) (imp (graphFormula 6 0 4).encode
        (imp (pairFormula 12 30 0).encode (imp (pairFormula 13 12 4).encode
          newNoGarbage.encode)))))))) := by
  let I : Formula := .all 3 (.imp (.member 0 3) (.member 1 3))
  let N := oldNoGarbage
  let A := extension
  let K : Formula := .member 1 0
  let Y : Formula := .member 31 0
  let F := graphFormula 6 0 4
  let Q := pairFormula 12 30 0
  let P := pairFormula 13 12 4
  let Γ := [P.encode,Q.encode,F.encode,Y.encode,K.encode,A.encode,N.encode,I.encode]
  have hv : ∀ q, q ∈ Γ → KDerivation (imp q (allCode 9 q)) := by
    intro q hq
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hq
    by_cases hP : q = P.encode
    · subst q; exact P.vacuity 9 (by decide)
    ·
      by_cases hQ : q = Q.encode
      · subst q; exact Q.vacuity 9 (by decide)
      ·
        by_cases hF : q = F.encode
        · subst q; exact F.vacuity 9 (by decide)
        ·
          by_cases hY : q = Y.encode
          · subst q; exact Y.vacuity 9 (by decide)
          ·
            by_cases hK : q = K.encode
            · subst q; exact K.vacuity 9 (by decide)
            ·
              by_cases hA : q = A.encode
              · subst q; exact A.vacuity 9 (by decide)
              ·
                by_cases hN : q = N.encode
                · subst q; exact free_vacuity 9 N (by decide)
                ·
                  have hI : q = I.encode := by simpa [hP,hQ,hF,hY,hK,hA,hN] using hq
                  subst q; exact I.vacuity 9 (by decide)
  have hp : Context Γ (imp (member 11 9) (entry 1).encode) := by
    apply Context.deduction
    let Δ := member 11 9 :: Γ
    have hm : Context Δ (member 11 9) := .head _ _
    have ha : Context Δ A.encode := .hypothesis (by simp [Δ,Γ])
    have hc : Context Δ (either (equal 9 13) (member 7 9)) :=
      .mp hm (.mp ha (.closed adjoin_instance))
    change Context Δ (either (member 10 9) (rowWitness 1).encode)
    apply Context.disjunctionElim hc
    · let Θ := equal 9 13 :: Δ
      have he : Context Θ (equal 9 13) := .head _ _
      have hp : Context Θ P.encode := .hypothesis (by simp [Θ,Δ,Γ])
      have hq : Context Θ Q.encode := .hypothesis (by simp [Θ,Δ,Γ])
      have hf : Context Θ F.encode := .hypothesis (by simp [Θ,Δ,Γ])
      have hy : Context Θ (member 31 0) := .hypothesis (by simp [Θ,Δ,Γ,Y,Formula.encode])
      have hk : Context Θ (member 1 0) := .hypothesis (by simp [Θ,Δ,Γ,K,Formula.encode])
      have hw : Context Θ (rowWitness 1).encode :=
        .mp he (.mp hp (.mp hq (.mp hf (.mp hy (.mp hk (.closed new_entry_is_row_witness))))))
      exact Context.disjunctionRight hw
    · let Θ := member 7 9 :: Δ
      have hmold : Context Θ (member 7 9) := .head _ _
      have hn : Context Θ oldNoGarbage.encode := .hypothesis (by simp [Θ,Δ,Γ,N])
      have hI : Context Θ I.encode := .hypothesis (by simp [Θ,Δ,Γ])
      have hi : Context Θ prefixInclusion := by
        change Context Θ I.encode
        exact hI
      have he : Context Θ (entry 1).encode :=
        .mp hmold (.mp hn (.mp hi (.closed old_entry_preserved)))
      exact he
  have hall := Context.generalize 9 hv hp
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  exact hall

theorem no_garbage_step_certificate : theoremCode (certificate no_garbage_step) =
    imp prefixInclusion (imp oldNoGarbage.encode (imp extension.encode
      (imp (member 1 0) (imp (member 31 0) (imp (graphFormula 6 0 4).encode
        (imp (pairFormula 12 30 0).encode (imp (pairFormula 13 12 4).encode
          newNoGarbage.encode))))))) := certificate_correct no_garbage_step
end PASoundness.PAtoCompactMultiplicationRowNoGarbageStep
#print axioms PASoundness.PAtoCompactMultiplicationRowNoGarbageStep.no_garbage_step
#print axioms PASoundness.PAtoCompactMultiplicationRowNoGarbageStep.no_garbage_step_certificate
