import PASoundness.PAtoCompactFixedFirstTopConstructedEleven
import PASoundness.PAtoCompactFixedFirstPreservedBase
import PASoundness.PAtoCompactFreeVacuity

/-! Eliminate the constructed nested pair and graph witnesses from a supplied
inside-index invariant step. The step remains explicit proof data; no row
collection or multiplication totality is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactFixedFirstInsideWitnessElim
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactFixedFirstPreservedBase PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactFixedFirstTopCoverageEleven
open PASoundness.PAtoCompactFixedFirstTopConstructedEleven
attribute [local irreducible] imp Cantor.pair Cantor.triangle

private def S : Formula := namedSuccessor 0 1 2
private def Y : Formula := .member 31 0
private def O : Formula := rowInvariantPreserved 7
private def F : Formula := graphFormula 6 0 4
private def P : Formula := pairFormula 12 30 0
private def Q : Formula := pairFormula 13 12 4
private def A : Formula := namedAdjoin 7 13 11 14
private def N : Formula := replace 0 1 (rowInvariantPreserved 11)
private def E : Formula := .ex 11 N
private def B : Formula := namedBoth A topCoverage11
private def C : Formula := namedBoth Q (.ex 11 B)
private def D : Formula := namedBoth P (.ex 13 C)

/-- Construct and eliminate the nested pair and graph witnesses, provided a
finite K inside-invariant derivation. All object-level hypotheses and the
remaining proof-data input are displayed; no uniqueness of pair objects is
used. -/
def from_step
    (step : KDerivation (imp (successorCode 0 1 2) (imp (member 31 0)
      (imp (rowInvariantPreserved 7).encode (imp (adjoinCode 7 13 11 14)
        (imp (graphFormula 6 0 4).encode (imp (pairFormula 12 30 0).encode
          (imp (pairFormula 13 12 4).encode (imp topCoverage11.encode
            (replace 0 1 (rowInvariantPreserved 11)).encode))))))))) :
    KDerivation (imp (successorCode 0 1 2) (imp (member 31 0)
      (imp (rowInvariantPreserved 7).encode (imp (graphFormula 6 0 4).encode
        (existsCode 11 (replace 0 1 (rowInvariantPreserved 11)).encode))))) := by
  have hv12 : KDerivation (imp E.encode (allCode 12 E.encode)) := E.vacuity 12 (by decide)
  have hv13 : KDerivation (imp E.encode (allCode 13 E.encode)) := E.vacuity 13 (by decide)
  have hv11 : KDerivation (imp E.encode (allCode 11 E.encode)) :=
    free_vacuity 11 E (by decide)
  have hintro := existsIntroduce 11 N (by decide)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [F.encode,O.encode,Y.encode,S.encode]
  have hf : Context Γ F.encode := .head _ _
  have hex12 : Context Γ (existsCode 12 D.encode) := by
    have h := Context.mp hf (.closed top_coverage_constructed)
    change Context Γ (existsCode 12 (both P.encode (existsCode 13
      (both Q.encode (existsCode 11 (both (adjoinCode 7 13 11 14) topCoverage11.encode)))))) at h
    change Context Γ (existsCode 12 (both P.encode (existsCode 13
      (both Q.encode (existsCode 11 (both (adjoinCode 7 13 11 14) topCoverage11.encode))))))
    exact h
  change Context Γ E.encode
  apply Context.existsElim hv12 _ hex12
  apply Context.generalize 12
  · intro q hq
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hq
    by_cases hF : q = F.encode
    · subst q; exact F.vacuity 12 (by decide)
    · by_cases hO : q = O.encode
      · subst q; exact O.vacuity 12 (by decide)
      · by_cases hY : q = Y.encode
        · subst q; exact Y.vacuity 12 (by decide)
        · have hS : q = S.encode := by simpa [hF,hO,hY] using hq
          subst q; exact S.vacuity 12 (by decide)
  apply Context.deduction
  let Δ := D.encode :: Γ
  have hd : Context Δ D.encode := .head _ _
  have hp : Context Δ P.encode := Context.conjunctionLeft hd
  have hex13 : Context Δ (existsCode 13 C.encode) := Context.conjunctionRight hd
  apply Context.existsElim hv13 _ hex13
  apply Context.generalize 13
  · intro q hq
    simp only [Δ,Γ,List.mem_cons,List.not_mem_nil,or_false] at hq
    by_cases hD : q = D.encode
    · subst q; exact free_vacuity 13 D (by decide)
    · by_cases hF : q = F.encode
      · subst q; exact F.vacuity 13 (by decide)
      · by_cases hO : q = O.encode
        · subst q; exact O.vacuity 13 (by decide)
        · by_cases hY : q = Y.encode
          · subst q; exact Y.vacuity 13 (by decide)
          · have hS : q = S.encode := by simpa [hD,hF,hO,hY] using hq
            subst q; exact S.vacuity 13 (by decide)
  apply Context.deduction
  let Θ := C.encode :: Δ
  have hc : Context Θ C.encode := .head _ _
  have hq : Context Θ Q.encode := Context.conjunctionLeft hc
  have hex11 : Context Θ (existsCode 11 B.encode) := Context.conjunctionRight hc
  apply Context.existsElim hv11 _ hex11
  apply Context.generalize 11
  · intro q hq
    simp only [Θ,Δ,Γ,List.mem_cons,List.not_mem_nil,or_false] at hq
    by_cases hC : q = C.encode
    · subst q; exact free_vacuity 11 C (by decide)
    · by_cases hD : q = D.encode
      · subst q; exact free_vacuity 11 D (by decide)
      · by_cases hF : q = F.encode
        · subst q; exact F.vacuity 11 (by decide)
        · by_cases hO : q = O.encode
          · subst q; exact O.vacuity 11 (by decide)
          · by_cases hY : q = Y.encode
            · subst q; exact Y.vacuity 11 (by decide)
            · have hS : q = S.encode := by simpa [hC,hD,hF,hO,hY] using hq
              subst q; exact S.vacuity 11 (by decide)
  apply Context.deduction
  let Ξ := B.encode :: Θ
  have hb : Context Ξ B.encode := .head _ _
  have ha : Context Ξ A.encode := Context.conjunctionLeft hb
  have ht : Context Ξ topCoverage11.encode := Context.conjunctionRight hb
  have hq' : Context Ξ Q.encode := .under hq _
  have hp' : Context Ξ P.encode := .under (.under hp _) _
  have hf' : Context Ξ F.encode := .hypothesis (by simp [Ξ,Θ,Δ,Γ])
  have ho : Context Ξ O.encode := .hypothesis (by simp [Ξ,Θ,Δ,Γ])
  have hy : Context Ξ Y.encode := .hypothesis (by simp [Ξ,Θ,Δ,Γ])
  have hs : Context Ξ S.encode := .hypothesis (by simp [Ξ,Θ,Δ,Γ])
  have hn : Context Ξ N.encode := by
    have hn' := Context.mp ht (Context.mp hq' (Context.mp hp' (Context.mp hf'
      (Context.mp ha (Context.mp ho (Context.mp hy (Context.mp hs (.closed step))))))))
    simpa [S,Y,O,F,P,Q,A,N,namedSuccessor,namedSuccessorBody,namedAdjoin,namedBoth,namedEither,
      Formula.not,Formula.encode,successorCode,adjoinCode,both,neg,either] using hn'
  exact .mp hn (.closed hintro)

end PASoundness.PAtoCompactFixedFirstInsideWitnessElim
#print axioms PASoundness.PAtoCompactFixedFirstInsideWitnessElim.from_step
