import PASoundness.PAtoCompactTermSubstBinaryStep
import PASoundness.PAtoCompactAllElimTermEquality

/-! Functionality of binary term graphs from explicit finite-K child and
operation functionality proofs. Four witness-elimination vacuity obligations
are retained explicitly. No arithmetic functionality or totality is assumed. -/
namespace PASoundness.PAtoCompactBinaryGraphFunctionalConditional

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermSubstBinaryStep
open PASoundness.PAtoCompactAllElimTermEquality

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] PASoundness.CompactProof.imp Cantor.pair Cantor.triangle

/-- Pairwise operation functionality lifts through two independently
allocated pairs of term witnesses. All graph/guard vacuity hypotheses are
actual K derivations: callers must prove the freshness facts needed for them. -/
def binary_functionality {α : Type} (v : α → Nat)
    (t u : Peano.language.Term α) (add : Bool) (b c p q e f : Nat)
    (g : Formula)
    (left : KDerivation (imp g.encode
      (imp (termGraph v t b (b+64)).encode
        (imp (termGraph v t c (c+64)).encode (equivAt e b c).encode))))
    (right : KDerivation (imp g.encode
      (imp (termGraph v u (b+1) (b+64+termCost t)).encode
        (imp (termGraph v u (c+1) (c+64+termCost t)).encode
          (equivAt e (b+1) (c+1)).encode))))
    (operation : KDerivation (imp g.encode
      (imp (equivAt e b c).encode (imp (equivAt e (b+1) (c+1)).encode
        (imp (binaryRel add b p).encode (imp (binaryRel add c q).encode
          (equivAt f p q).encode))))))
    (vH₀ : KDerivation (imp (andF g (andF
      (termGraph v (binaryTerm add t u) p b)
      (termGraph v (binaryTerm add t u) q c))).encode
      (allCode b (andF g (andF (termGraph v (binaryTerm add t u) p b)
        (termGraph v (binaryTerm add t u) q c))).encode)))
    (vH₁ : KDerivation (imp (andF g (andF
      (termGraph v (binaryTerm add t u) p b)
      (termGraph v (binaryTerm add t u) q c))).encode
      (allCode (b+1) (andF g (andF (termGraph v (binaryTerm add t u) p b)
        (termGraph v (binaryTerm add t u) q c))).encode)))
    (vHM₀ : KDerivation (imp (andF (andF g (andF
      (termGraph v (binaryTerm add t u) p b)
      (termGraph v (binaryTerm add t u) q c))) (matrix v add t u b p)).encode
      (allCode c (andF (andF g (andF (termGraph v (binaryTerm add t u) p b)
        (termGraph v (binaryTerm add t u) q c))) (matrix v add t u b p)).encode)))
    (vHM₁ : KDerivation (imp (andF (andF g (andF
      (termGraph v (binaryTerm add t u) p b)
      (termGraph v (binaryTerm add t u) q c))) (matrix v add t u b p)).encode
      (allCode (c+1) (andF (andF g (andF (termGraph v (binaryTerm add t u) p b)
        (termGraph v (binaryTerm add t u) q c))) (matrix v add t u b p)).encode)))
    (vE₀ : KDerivation (imp (equivAt f p q).encode (allCode b (equivAt f p q).encode)))
    (vE₁ : KDerivation (imp (equivAt f p q).encode (allCode (b+1) (equivAt f p q).encode)))
    (vE₂ : KDerivation (imp (equivAt f p q).encode (allCode c (equivAt f p q).encode)))
    (vE₃ : KDerivation (imp (equivAt f p q).encode (allCode (c+1) (equivAt f p q).encode))) :
    KDerivation (imp g.encode
      (imp (termGraph v (binaryTerm add t u) p b).encode
        (imp (termGraph v (binaryTerm add t u) q c).encode (equivAt f p q).encode))) := by
  let A := termGraph v (binaryTerm add t u) p b
  let B := termGraph v (binaryTerm add t u) q c
  let M := matrix v add t u b p
  let N := matrix v add t u c q
  let H := andF g (andF A B)
  let HM := andF H M
  let E := (equivAt f p q).encode
  have point : KDerivation (imp HM.encode (imp N.encode E)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [N.encode, HM.encode]
    have hN : Context Γ N.encode := .head _ _
    have hHM : Context Γ HM.encode := .hypothesis (by simp [Γ])
    have hHM' : Context Γ (both H.encode M.encode) := by
      simpa [HM, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hHM
    have hH := Context.conjunctionLeft hHM'
    have hM := Context.conjunctionRight hHM'
    have hH' : Context Γ (both g.encode (andF A B).encode) := by
      simpa [H, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hH
    have hg := Context.conjunctionLeft hH'
    have hM' : Context Γ (both (termGraph v t b (b+64)).encode
        (both (termGraph v u (b+1) (b+64+termCost t)).encode (binaryRel add b p).encode)) := by
      simpa [M, matrix, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hM
    have hN' : Context Γ (both (termGraph v t c (c+64)).encode
        (both (termGraph v u (c+1) (c+64+termCost t)).encode (binaryRel add c q).encode)) := by
      simpa [N, matrix, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hN
    have he1 := Context.mp (Context.conjunctionLeft hN')
      (Context.mp (Context.conjunctionLeft hM') (Context.mp hg (.closed left)))
    have he2 := Context.mp (Context.conjunctionLeft (Context.conjunctionRight hN'))
      (Context.mp (Context.conjunctionLeft (Context.conjunctionRight hM')) (Context.mp hg (.closed right)))
    exact .mp (Context.conjunctionRight (Context.conjunctionRight hN'))
      (.mp (Context.conjunctionRight (Context.conjunctionRight hM'))
        (.mp he2 (.mp he1 (.mp hg (.closed operation)))))
  have elimN := two_exists_left_guarded c (c+1) HM.encode N.encode E vHM₀ vHM₁ vE₂ vE₃ point
  have pointM : KDerivation (imp H.encode (imp M.encode E)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [M.encode, H.encode]
    have hM : Context Γ M.encode := .head _ _
    have hH : Context Γ H.encode := .hypothesis (by simp [Γ])
    have hH' : Context Γ (both g.encode (andF A B).encode) := by
      simpa [H, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hH
    have hAB : Context Γ (both A.encode B.encode) := by
      simpa [andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using Context.conjunctionRight hH'
    have hB := Context.conjunctionRight hAB
    have hBN : Context Γ (existsCode c (existsCode (c+1) N.encode)) := by
      have hb : Context Γ (both (domainAt c q).encode (existsCode c (existsCode (c+1) N.encode))) := by
        cases add <;> simpa [B, binaryTerm, termGraph, N, matrix, binaryRel, andF,
          CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg, existsCode] using hB
      exact Context.conjunctionRight hb
    have hHM : Context Γ HM.encode := by
      have hh := Context.conjunctionIntro hH hM
      simpa [HM, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hh
    exact .mp hBN (.mp hHM (.closed elimN))
  have elimM := two_exists_left_guarded b (b+1) H.encode M.encode E vH₀ vH₁ vE₀ vE₁ pointM
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [B.encode, A.encode, g.encode]
  have hB : Context Γ B.encode := .head _ _
  have hA : Context Γ A.encode := .hypothesis (by simp [Γ])
  have hg : Context Γ g.encode := .hypothesis (by simp [Γ])
  have hAM : Context Γ (existsCode b (existsCode (b+1) M.encode)) := by
    have ha : Context Γ (both (domainAt b p).encode (existsCode b (existsCode (b+1) M.encode))) := by
      cases add <;> simpa [A, binaryTerm, termGraph, M, matrix, binaryRel, andF,
        CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg, existsCode] using hA
    exact Context.conjunctionRight ha
  have hH : Context Γ H.encode := by
    have hh := Context.conjunctionIntro hg (Context.conjunctionIntro hA hB)
    simpa [H, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hh
  exact .mp hAM (.mp hH (.closed elimM))

#print axioms binary_functionality
end PASoundness.PAtoCompactBinaryGraphFunctionalConditional
