import PASoundness.PAtoCompactSuccVariableFunctionalityClosed
import PASoundness.PAtoCompactUnaryGraphFunctional
import PASoundness.PAtoCompactUnaryTermTransport

/-! Finite-K functionality of all unary-fragment PA term graphs. Source
variables are supplied with explicit guard-to-candidate K proof data. -/
namespace PASoundness.PAtoCompactUnaryGraphFunctionalityFull

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFreeNames
open PASoundness.PAtoCompactGuardBaseTransport PASoundness.PAtoCompactAllTermTransport
open PASoundness.PAtoCompactVariableGraphLaws PASoundness.PAtoCompactUnaryGraphFunctional
open PASoundness.PAtoCompactUnaryTermTransport
open PASoundness.PAtoCompactSuccessorGraphFunctionalityConditional
open PASoundness.PAtoCompactSuccBaseMultiAlpha PASoundness.PAtoCompactEquivMultiAlpha
open PASoundness.PAtoCompactSuccCongruenceWitnessLift

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- For a unary term, any two graph outputs are quotient-equivalent under a
source guard which supplies a candidate for each used variable. Variable,
output and represented object names may coincide. -/
noncomputable def unary_functional {α : Type} [DecidableEq α] (v : α → Nat)
    (g : Formula) {t : Peano.language.Term α} (ht : UnaryTerm t) :
    ∀ b p q, (∀ a ∈ t.varFinset, v a < b) → (∀ x ∈ g.free, x < b) →
      (∀ a ∈ t.varFinset, KDerivation (imp g.encode (domainAt b (v a)).encode)) →
      p < b → q < b →
      KDerivation (imp g.encode (imp (termGraph v t p b).encode
        (imp (termGraph v t q b).encode (equivAt b p q).encode))) := by
  induction ht with
  | var a =>
      intro b p q hv hg hd hp hq
      have ha : v a < b := hv a (by simp [Term.varFinset])
      have hguard := hd a (by simp [Term.varFinset])
      have hf := variable_functional v a b p q (by omega) (by omega) (by omega)
      apply Context.closeEmpty
      apply Context.deduction
      apply Context.deduction
      apply Context.deduction
      let A := (termGraph v (.var a) p b).encode
      let B := (termGraph v (.var a) q b).encode
      let Γ := [B,A,g.encode]
      have hg' : Context Γ g.encode := .hypothesis (by simp [Γ])
      have hA : Context Γ A := .hypothesis (by simp [Γ])
      have hB : Context Γ B := .head _ _
      exact .mp hB (.mp hA (.mp (.mp hg' (.closed hguard)) (.closed hf)))
  | zero =>
      intro b p q hv hg hd hp hq
      have hf := zero_graph_functional v b p q (by omega) (by omega)
      apply Context.closeEmpty
      apply Context.deduction
      apply Context.deduction
      apply Context.deduction
      let A := (termGraph v (.func .zero Fin.elim0) p b).encode
      let B := (termGraph v (.func .zero Fin.elim0) q b).encode
      let Γ := [B,A,g.encode]
      have hA : Context Γ A := .hypothesis (by simp [Γ])
      have hB : Context Γ B := .head _ _
      exact .mp hB (.mp hA (.closed hf))
  | @succ u hu ih =>
      intro b p q hv hg hd hp hq
      let c := b+1
      let d := c+64
      have hvars : (.func .succ ![u] : Peano.language.Term α).varFinset = u.varFinset := by simp [Term.varFinset]
      have hvar : ∀ a ∈ u.varFinset, v a < b := by
        intro a ha
        exact hv a (hvars ▸ ha)
      have hvarD : ∀ a ∈ u.varFinset, v a < d := by
        intro a ha
        have hh := hvar a ha
        dsimp [d,c]
        omega
      have hguardD : ∀ x ∈ g.free, x < d := by
        intro x hx
        have hh := hg x hx
        dsimp [d,c]
        omega
      have hdomD : ∀ a ∈ u.varFinset, KDerivation (imp g.encode (domainAt d (v a)).encode) := by
        intro a ha
        have hh := hd a (hvars ▸ ha)
        have htr := domainAt_transport b d (v a) (by have := hvar a ha; omega)
          (by have := hvar a ha; dsimp [d,c]; omega)
        exact compose hh htr
      have hfirst := (termGraph_base_transport v u (b+64) d b (by omega)
        (by dsimp [d,c]; omega) (by intro a ha; have := hvar a ha; omega) hvarD).1
      have hfun := ih d b c hvarD hguardD hdomD (by dsimp [d,c]; omega) (by dsimp [d]; omega)
      have hchild : KDerivation (imp g.encode (imp (termGraph v u b (b+64)).encode
          (imp (termGraph v u c (c+64)).encode (equivAt d b c).encode))) := by
        apply Context.closeEmpty
        apply Context.deduction
        apply Context.deduction
        apply Context.deduction
        let A := (termGraph v u b (b+64)).encode
        let B := (termGraph v u c d).encode
        let Γ := [B,A,g.encode]
        have hg' : Context Γ g.encode := .hypothesis (by simp [Γ])
        have hA : Context Γ A := .hypothesis (by simp [Γ])
        have hB : Context Γ B := .head _ _
        exact .mp hB (.mp (.mp hA (.closed hfirst)) (.mp hg' (.closed hfun)))
      have hs1 := (succAt_base_alpha b d b p (by omega) (by omega)
        (by dsimp [d,c]; omega) (by dsimp [d,c]; omega)).forward
      have hs2 := (succAt_base_alpha c d c q (by omega) (by dsimp [c]; omega)
        (by dsimp [d]; omega) (by dsimp [d,c]; omega)).forward
      have ho := (equivAt_base_alpha d b p q (by dsimp [d,c]; omega)
        (by dsimp [d,c]; omega) (by omega) (by omega)).forward
      have hc := successor_congruence d b c p q (by dsimp [d,c]; omega)
        (by dsimp [d]; omega) (by dsimp [d,c]; omega) (by dsimp [d,c]; omega)
      have hnext : KDerivation (imp g.encode (imp (equivAt d b c).encode
          (imp (succAt b b p).encode (imp (succAt c c q).encode (equivAt b p q).encode)))) := by
        apply Context.closeEmpty
        apply Context.deduction
        apply Context.deduction
        apply Context.deduction
        apply Context.deduction
        let E := (equivAt d b c).encode
        let S := (succAt b b p).encode
        let T := (succAt c c q).encode
        let Γ := [T,S,E,g.encode]
        have he : Context Γ E := .hypothesis (by simp [Γ])
        have hs : Context Γ S := .hypothesis (by simp [Γ])
        have ht' : Context Γ T := .head _ _
        exact .mp (.mp (.mp ht' (.closed hs2)) (.mp (.mp hs (.closed hs1))
          (.mp he (.closed hc)))) (.closed ho)
      have hgb : b ∉ g.free := by intro hh; have := hg b hh; omega
      have hgc : c ∉ g.free := by intro hh; have := hg c hh; dsimp [c] at *; omega
      exact successor_functionality_same_base v u b c p q d b g (by dsimp [c]; omega)
        hp hq hvar hgb hgc hchild hnext

end PASoundness.PAtoCompactUnaryGraphFunctionalityFull

#print axioms PASoundness.PAtoCompactUnaryGraphFunctionalityFull.unary_functional
