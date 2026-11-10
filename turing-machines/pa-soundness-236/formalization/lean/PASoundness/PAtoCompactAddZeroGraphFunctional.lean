import PASoundness.PAtoCompactTermZeroGuarded
import PASoundness.PAtoCompactSuccessorGraphFunctionalityConditional
import PASoundness.PAtoCompactDynamicSymmetry
import PASoundness.PAtoCompactDynamicTransitivityFinal

/-! Conditional K assembly for right-zero graph functionality, retaining the
child functionality, quotient-chain and witness-projection proofs explicitly. -/
namespace PASoundness.PAtoCompactAddZeroGraphFunctional
open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermZeroGuarded
open PASoundness.PAtoCompactDynamicSymmetry PASoundness.PAtoCompactDynamicTransitivityFinal
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] PASoundness.CompactProof.imp Cantor.pair Cantor.triangle

/-- The quotient-chain used to compare two output values. Both candidate
conditions are explicit; the four labels may alias. -/
def quotient_chain (e a c p q : Nat)
    (ha : a < e+2) (hc : c < e+2) (hp : p < e+2) (hq : q < e+2) :
    KDerivation (imp (domainAt e a).encode (imp (domainAt e p).encode
      (imp (equivAt e a p).encode (imp (equivAt e a c).encode
        (imp (equivAt e c q).encode (equivAt e p q).encode))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(equivAt e c q).encode, (equivAt e a c).encode,
    (equivAt e a p).encode, (domainAt e p).encode, (domainAt e a).encode]
  have hDa : Context Γ (domainAt e a).encode := .hypothesis (by simp [Γ])
  have hDp : Context Γ (domainAt e p).encode := .hypothesis (by simp [Γ])
  have hAP : Context Γ (equivAt e a p).encode := .hypothesis (by simp [Γ])
  have hAC : Context Γ (equivAt e a c).encode := .hypothesis (by simp [Γ])
  have hCQ : Context Γ (equivAt e c q).encode := .head _ _
  have hPA := Context.mp hAP (Context.mp hDa (.closed (dynamic_symmetry e a p ha hp)))
  have hPC := Context.mp hAC (Context.mp hPA
    (Context.mp hDp (.closed (dynamic_transitivity e p a c hp ha hc))))
  exact Context.mp hCQ (Context.mp hPC
    (Context.mp hDp (.closed (dynamic_transitivity e p c q hp hc hq))))

def add_zero_functionality_of_projections {α : Type} (v : α → Nat) (t : Peano.language.Term α)
    (b c p q e f : Nat) (g : Formula)
    (child : KDerivation (imp g.encode
      (imp (termGraph v t b (b+64)).encode
        (imp (termGraph v t c (c+64)).encode (equivAt e b c).encode))))
    (next : KDerivation (imp g.encode
      (imp (equivAt e b c).encode (imp (equivAt b b p).encode
        (imp (equivAt c c q).encode (equivAt f p q).encode)))))
    (project1 : KDerivation (imp (termGraph v (binaryTerm true t (.func .zero Fin.elim0)) p b).encode
      (existsCode b (andF (termGraph v t b (b+64)) (equivAt b b p)).encode)))
    (project2 : KDerivation (imp (termGraph v (binaryTerm true t (.func .zero Fin.elim0)) q c).encode
      (existsCode c (andF (termGraph v t c (c+64)) (equivAt c c q)).encode)))
    (vgb : KDerivation (imp g.encode (allCode b g.encode)))
    (vgc : KDerivation (imp g.encode (allCode c g.encode)))
    (vg1b : KDerivation (imp (termGraph v (binaryTerm true t (.func .zero Fin.elim0)) p b).encode
      (allCode b (termGraph v (binaryTerm true t (.func .zero Fin.elim0)) p b).encode)))
    (vg2b : KDerivation (imp (termGraph v (binaryTerm true t (.func .zero Fin.elim0)) q c).encode
      (allCode b (termGraph v (binaryTerm true t (.func .zero Fin.elim0)) q c).encode)))
    (vg1c : KDerivation (imp (termGraph v (binaryTerm true t (.func .zero Fin.elim0)) p b).encode
      (allCode c (termGraph v (binaryTerm true t (.func .zero Fin.elim0)) p b).encode)))
    (vg2c : KDerivation (imp (termGraph v (binaryTerm true t (.func .zero Fin.elim0)) q c).encode
      (allCode c (termGraph v (binaryTerm true t (.func .zero Fin.elim0)) q c).encode)))
    (vbody1c : KDerivation (imp (andF (termGraph v t b (b+64)) (equivAt b b p)).encode
      (allCode c (andF (termGraph v t b (b+64)) (equivAt b b p)).encode)))
    (veb : KDerivation (imp (equivAt f p q).encode (allCode b (equivAt f p q).encode)))
    (vec : KDerivation (imp (equivAt f p q).encode (allCode c (equivAt f p q).encode))) :
    KDerivation (imp g.encode
      (imp (termGraph v (binaryTerm true t (.func .zero Fin.elim0)) p b).encode
        (imp (termGraph v (binaryTerm true t (.func .zero Fin.elim0)) q c).encode (equivAt f p q).encode))) := by
  let A := (termGraph v (binaryTerm true t (.func .zero Fin.elim0)) p b).encode
  let B := (termGraph v (binaryTerm true t (.func .zero Fin.elim0)) q c).encode
  let C := (andF (termGraph v t b (b+64)) (equivAt b b p)).encode
  let D := (andF (termGraph v t c (c+64)) (equivAt c c q)).encode
  let E := (equivAt f p q).encode
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [B,A,g.encode]
  have hA : Context Γ A := .hypothesis (by simp [Γ])
  have hB : Context Γ B := .head _ _
  have hExA : Context Γ (existsCode b C) := .mp hA (.closed project1)
  apply Context.existsElim veb _ hExA
  apply Context.generalize b
  · intro n hn
    change n ∈ [B,A,g.encode] at hn
    by_cases h : n = B
    · subst n; exact vg2b
    · by_cases h' : n = A
      · subst n; exact vg1b
      · have h'' : n = g.encode := by simpa [h, h'] using hn
        subst n; exact vgb
  apply Context.deduction
  let Δ := [C,B,A,g.encode]
  have hC : Context Δ C := .head _ _
  have hB' : Context Δ B := .hypothesis (by simp [Δ])
  have hExB : Context Δ (existsCode c D) := .mp hB' (.closed project2)
  apply Context.existsElim vec _ hExB
  apply Context.generalize c
  · intro n hn
    change n ∈ [C,B,A,g.encode] at hn
    by_cases h : n = C
    · subst n; exact vbody1c
    · by_cases h' : n = B
      · subst n; exact vg2c
      · by_cases h'' : n = A
        · subst n; exact vg1c
        · have hlast : n = g.encode := by simpa [h, h', h''] using hn
          subst n; exact vgc
  apply Context.deduction
  let Θ := [D,C,B,A,g.encode]
  have hD : Context Θ D := .head _ _
  have hC' : Context Θ C := .hypothesis (by simp [Θ])
  have hg : Context Θ g.encode := .hypothesis (by simp [Θ])
  have hc1 : Context Θ (termGraph v t b (b+64)).encode := Context.conjunctionLeft hC'
  have hs1 : Context Θ (equivAt b b p).encode := Context.conjunctionRight hC'
  have hc2 : Context Θ (termGraph v t c (c+64)).encode := Context.conjunctionLeft hD
  have hs2 : Context Θ (equivAt c c q).encode := Context.conjunctionRight hD
  have he : Context Θ (equivAt e b c).encode := .mp hc2 (.mp hc1 (.mp hg (.closed child)))
  exact .mp hs2 (.mp hs1 (.mp he (.mp hg (.closed next))))

end PASoundness.PAtoCompactAddZeroGraphFunctional
#print axioms PASoundness.PAtoCompactAddZeroGraphFunctional.quotient_chain
#print axioms PASoundness.PAtoCompactAddZeroGraphFunctional.add_zero_functionality_of_projections
