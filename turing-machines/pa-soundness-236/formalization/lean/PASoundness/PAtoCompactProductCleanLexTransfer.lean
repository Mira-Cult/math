import PASoundness.PAtoCompactMultiplicationCandidate
import PASoundness.PAtoCompactProductCleanFilter
import PASoundness.PAtoCompactFreeVacuity
import PASoundness.CompactQuantifiers

/-! Transfer of the literal product lexicographic clause from graph 6 to
filtered graph 54, conditional on explicit K reverse-triple implications at
both point tuples. This file does not prove those implications, graph
existence, multiplication totality, or PA proof transport. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductCleanLexTransfer
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactProductCleanFilter
open PASoundness.PAtoCompactFreeVacuity
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Literal encoded product triple at the indicated graph label. -/
def tripleAt (g a b c : Nat) : Formula := replace 6 g (tripleFormula a b c)

def antecedent (g : Nat) : Formula := namedBoth (.member 0 3)
  (namedBoth (.member 1 4) (namedBoth (.member 2 5)
    (namedBoth (.member 0 7) (namedBoth (.member 1 8) (namedBoth (.member 2 9)
      (namedBoth (tripleAt g 3 4 5) (tripleAt g 7 8 9)))))))

def comparison : Formula := namedBoth
  (.imp (.member 9 5) (namedEither (.member 7 3) (namedBoth (.equal 3 7) (.member 8 4))))
  (.imp (namedEither (.member 7 3) (namedBoth (.equal 3 7) (.member 8 4))) (.member 9 5))

def point (g : Nat) : Formula := .imp (antecedent g) comparison

def filteredLex : Formula := replace 6 54 lexFormula

theorem original_shape : lexFormula = .all 3 (.all 4 (.all 5 (.all 7 (.all 8 (.all 9 (point 6)))))) := by decide

theorem filtered_shape : filteredLex = .all 3 (.all 4 (.all 5 (.all 7 (.all 8 (.all 9 (point 54)))))) := by decide

private def old_point : KDerivation (imp lexFormula.encode (point 6).encode) := by
  have h3 := allSpecialize 3 (.all 4 (.all 5 (.all 7 (.all 8 (.all 9 (point 6)))))) (by decide)
  have h4 := allSpecialize 4 (.all 5 (.all 7 (.all 8 (.all 9 (point 6))))) (by decide)
  have h5 := allSpecialize 5 (.all 7 (.all 8 (.all 9 (point 6)))) (by decide)
  have h7 := allSpecialize 7 (.all 8 (.all 9 (point 6))) (by decide)
  have h8 := allSpecialize 8 (.all 9 (point 6)) (by decide)
  have h9 := allSpecialize 9 (point 6) (by decide)
  rw [original_shape]
  exact compose h3 (compose h4 (compose h5 (compose h7 (compose h8 h9))))

/-- Both retained context hypotheses admit generalization over all six
point labels; this uses free-variable rather than all-name freshness. -/
def context_vacuity (x : Nat) (hx : x ∈ [3,4,5,7,8,9]) :
    ∀ h, h ∈ [lexFormula.encode, filterCode 54] → KDerivation (imp h (allCode x h)) := by
  intro h hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  by_cases he : h = lexFormula.encode
  · subst h
    apply free_vacuity x lexFormula
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · have he' : h = filterCode 54 := hh.resolve_left he
    subst h
    let F : Formula := .all 55 (PAtoCompactFilterInstantiation.namedFilterBody 6 54 55
      (cleanPredicate 55))
    have hf : F.encode = filterCode 54 := by rfl
    rw [← hf]
    apply free_vacuity x F
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- A pair of actual K reverse-triple proofs suffices to transfer the entire
six-quantifier lex clause. The proof inputs remain explicit; no claim is made
here that they have been constructed. -/
def transfer_of_reverse
    (h35 : KDerivation (imp (filterCode 54) (imp (tripleAt 54 3 4 5).encode (tripleAt 6 3 4 5).encode)))
    (h79 : KDerivation (imp (filterCode 54) (imp (tripleAt 54 7 8 9).encode (tripleAt 6 7 8 9).encode))) :
    KDerivation (imp (filterCode 54) (imp lexFormula.encode filteredLex.encode)) := by
  let F := filterCode 54
  let O := lexFormula.encode
  let Γ := [O,F]
  have hf : Context Γ F := .hypothesis (by simp [Γ])
  have ho : Context Γ O := .head _ _
  have hpold : Context Γ (point 6).encode := .mp ho (.closed old_point)
  have hpnew : Context Γ (point 54).encode := by
    apply Context.deduction
    let Δ := (antecedent 54).encode :: Γ
    have ha : Context Δ (antecedent 54).encode := .head _ _
    have ha' : Context Δ (both (member 0 3) (both (member 1 4) (both (member 2 5)
        (both (member 0 7) (both (member 1 8) (both (member 2 9)
          (both (tripleAt 54 3 4 5).encode (tripleAt 54 7 8 9).encode))))))) := by
      simpa [antecedent, namedBoth, Formula.encode, CompactProof.both, CompactProof.neg] using ha
    have h1 := Context.conjunctionLeft ha'
    have r1 := Context.conjunctionRight ha'
    have h2 := Context.conjunctionLeft r1
    have r2 := Context.conjunctionRight r1
    have h3 := Context.conjunctionLeft r2
    have r3 := Context.conjunctionRight r2
    have h4 := Context.conjunctionLeft r3
    have r4 := Context.conjunctionRight r3
    have h5 := Context.conjunctionLeft r4
    have r5 := Context.conjunctionRight r4
    have h6 := Context.conjunctionLeft r5
    have ht := Context.conjunctionRight r5
    have ht1 : Context Δ (tripleAt 6 3 4 5).encode :=
      .mp (Context.conjunctionLeft ht) (.mp (.under hf _) (.closed h35))
    have ht2 : Context Δ (tripleAt 6 7 8 9).encode :=
      .mp (Context.conjunctionRight ht) (.mp (.under hf _) (.closed h79))
    have haold : Context Δ (antecedent 6).encode := by
      simpa [antecedent, namedBoth, Formula.encode, CompactProof.both, CompactProof.neg] using
        (Context.conjunctionIntro h1 (Context.conjunctionIntro h2 (Context.conjunctionIntro h3
          (Context.conjunctionIntro h4 (Context.conjunctionIntro h5 (Context.conjunctionIntro h6
            (Context.conjunctionIntro ht1 ht2)))))))
    exact .mp haold (.under hpold _)
  have h9 := Context.generalize 9 (context_vacuity 9 (by decide)) hpnew
  have h8 := Context.generalize 8 (context_vacuity 8 (by decide)) h9
  have h7 := Context.generalize 7 (context_vacuity 7 (by decide)) h8
  have h5 := Context.generalize 5 (context_vacuity 5 (by decide)) h7
  have h4 := Context.generalize 4 (context_vacuity 4 (by decide)) h5
  have h3 := Context.generalize 3 (context_vacuity 3 (by decide)) h4
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  rw [filtered_shape]
  exact h3

theorem transfer_of_reverse_certificate
    (h35 : KDerivation (imp (filterCode 54) (imp (tripleAt 54 3 4 5).encode (tripleAt 6 3 4 5).encode)))
    (h79 : KDerivation (imp (filterCode 54) (imp (tripleAt 54 7 8 9).encode (tripleAt 6 7 8 9).encode))) :
    theoremCode (certificate (transfer_of_reverse h35 h79)) =
      imp (filterCode 54) (imp lexFormula.encode filteredLex.encode) :=
  certificate_correct (transfer_of_reverse h35 h79)
end PASoundness.PAtoCompactProductCleanLexTransfer
#print axioms PASoundness.PAtoCompactProductCleanLexTransfer.transfer_of_reverse
#print axioms PASoundness.PAtoCompactProductCleanLexTransfer.transfer_of_reverse_certificate
