import PASoundness.PAtoCompactFixedFirstSuccessorGraphAlpha
import PASoundness.PAtoCompactFixedFirstInsideMapClosed
import PASoundness.PAtoCompactFreeVacuity

/-! Eliminate the old graph existential in the actual inside-index step,
while retaining the map bijection as an object-level K assumption. The new
graph witness is capture-safely rebound to the original graph label. No row
collection or multiplication totality is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactFixedFirstGuardedOldExists
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactFixedFirstPreservedBase
open PASoundness.PAtoCompactFixedFirstSuccessorGraphAlpha
open PASoundness.PAtoCompactFixedFirstInsideMapClosed PASoundness.PAtoCompactMultiplicationRowMapEdge
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The actual inside step, lifted over an existentially supplied old graph.
The displayed map bijection and inside-membership assumptions remain literal
K antecedents; no proof-data input or representative uniqueness is used. -/
def inside_from_old_exists : KDerivation (imp mapBijection.encode
    (imp (successorCode 0 1 2) (imp (member 31 0)
      (imp (existsCode 7 (rowInvariantPreserved 7).encode)
        (existsCode 7 (replace 0 1 (rowInvariantPreserved 7)).encode))))) := by
  let M := mapBijection
  let S : Formula := namedSuccessor 0 1 2
  let Y : Formula := .member 31 0
  let O := rowInvariantPreserved 7
  let H : Formula := .ex 7 O
  let E : Formula := .ex 7 (replace 0 1 (rowInvariantPreserved 7))
  have hvE : KDerivation (imp E.encode (allCode 7 E.encode)) := free_vacuity 7 E (by decide)
  have hvH : KDerivation (imp H.encode (allCode 7 H.encode)) := free_vacuity 7 H (by decide)
  have hvS : KDerivation (imp S.encode (allCode 7 S.encode)) := S.vacuity 7 (by decide)
  have hvY : KDerivation (imp Y.encode (allCode 7 Y.encode)) := Y.vacuity 7 (by decide)
  have hvM : KDerivation (imp M.encode (allCode 7 M.encode)) := M.vacuity 7 (by decide)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [H.encode,Y.encode,S.encode,M.encode]
  have hex : Context Γ (existsCode 7 O.encode) := .head _ _
  have hlocal : Context (O.encode :: Γ) E.encode := by
    let Δ := O.encode :: Γ
    have ho : Context Δ O.encode := .head _ _
    have hy : Context Δ (member 31 0) := by
      have h : Context Δ Y.encode := .hypothesis (by simp [Δ,Γ])
      exact h
    have hs : Context Δ (successorCode 0 1 2) := by
      have h : Context Δ S.encode := .hypothesis (by simp [Δ,Γ])
      simpa [S,namedSuccessor,namedSuccessorBody,namedBoth,namedEither,Formula.encode,
        Formula.not,successorCode,both,neg,either] using h
    have hm : Context Δ mapBijection.encode := .hypothesis (by simp [Δ,Γ,M])
    have hn : Context Δ (existsCode 11 (replace 0 1 (rowInvariantPreserved 11)).encode) := by
      have h := Context.mp ho (Context.mp hy (Context.mp hs (Context.mp hm (.closed inside_from_bijection))))
      exact h
    exact .mp hn (.closed alpha_graph_witness)
  have hall : Context Γ (allCode 7 (imp O.encode E.encode)) := by
    apply Context.generalize 7
    · intro q hq
      simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hq
      by_cases hh : q = H.encode
      · subst q; exact hvH
      · by_cases hy : q = Y.encode
        · subst q; exact hvY
        · by_cases hs : q = S.encode
          · subst q; exact hvS
          · have hm : q = M.encode := by simpa [hh,hy,hs] using hq
            subst q; exact hvM
    exact Context.deduction hlocal
  have hout : Context Γ E.encode := Context.existsElim hvE hall hex
  simpa [Γ,H,Y,S,E,O,M,namedSuccessor,namedSuccessorBody,namedBoth,namedEither,
    Formula.encode,Formula.not,successorCode,both,neg,either] using hout

theorem inside_from_old_exists_certificate : theoremCode (certificate inside_from_old_exists) =
    imp mapBijection.encode (imp (successorCode 0 1 2) (imp (member 31 0)
      (imp (existsCode 7 (rowInvariantPreserved 7).encode)
        (existsCode 7 (replace 0 1 (rowInvariantPreserved 7)).encode)))) :=
  certificate_correct inside_from_old_exists
end PASoundness.PAtoCompactFixedFirstGuardedOldExists
#print axioms PASoundness.PAtoCompactFixedFirstGuardedOldExists.inside_from_old_exists
#print axioms PASoundness.PAtoCompactFixedFirstGuardedOldExists.inside_from_old_exists_certificate
