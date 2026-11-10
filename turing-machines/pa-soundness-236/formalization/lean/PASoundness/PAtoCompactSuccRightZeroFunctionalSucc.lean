import PASoundness.PAtoCompactUnaryGraphFunctionalityFull

/-! The successor step for guarded term-graph functionality. The child
functionality family is finite K proof data and remains an explicit input. -/
namespace PASoundness.PAtoCompactSuccRightZeroFunctionalSucc

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFreeNames
open PASoundness.PAtoCompactGuardBaseTransport PASoundness.PAtoCompactAllTermTransport
open PASoundness.PAtoCompactSuccessorGraphFunctionalityConditional
open PASoundness.PAtoCompactSuccBaseMultiAlpha PASoundness.PAtoCompactEquivMultiAlpha
open PASoundness.PAtoCompactSuccCongruenceWitnessLift

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Lift a child-functionality family through successor. The output and
variable names are strictly below the allocator, and the guard supplies the
candidate condition for every variable occurring in the child. -/
noncomputable def successor_functional {α : Type} [DecidableEq α]
    (v : α → Nat) (g : Formula) (u : Peano.language.Term α)
    (child : ∀ b p q, (∀ a ∈ u.varFinset, v a < b) →
      (∀ x ∈ g.free, x < b) →
      (∀ a ∈ u.varFinset, KDerivation (imp g.encode (domainAt b (v a)).encode)) →
      p < b → q < b → KDerivation (imp g.encode
        (imp (termGraph v u p b).encode
          (imp (termGraph v u q b).encode (equivAt b p q).encode))))
    (b p q : Nat) (hv : ∀ a ∈ u.varFinset, v a < b)
    (hg : ∀ x ∈ g.free, x < b)
    (hd : ∀ a ∈ u.varFinset, KDerivation (imp g.encode (domainAt b (v a)).encode))
    (hp : p < b) (hq : q < b) :
    KDerivation (imp g.encode (imp (termGraph v (.func .succ ![u]) p b).encode
      (imp (termGraph v (.func .succ ![u]) q b).encode (equivAt b p q).encode))) := by
  let c := b+1
  let d := c+64
  have hvarD : ∀ a ∈ u.varFinset, v a < d := by
    intro a ha
    have hh := hv a ha
    dsimp [d,c]
    omega
  have hguardD : ∀ x ∈ g.free, x < d := by
    intro x hx
    have hh := hg x hx
    dsimp [d,c]
    omega
  have hdomD : ∀ a ∈ u.varFinset, KDerivation (imp g.encode (domainAt d (v a)).encode) := by
    intro a ha
    have hh := hd a ha
    have htr := domainAt_transport b d (v a) (by have := hv a ha; omega)
      (by have := hv a ha; dsimp [d,c]; omega)
    exact compose hh htr
  have hfirst := (termGraph_base_transport v u (b+64) d b (by omega)
    (by dsimp [d,c]; omega) (by intro a ha; have := hv a ha; omega) hvarD).1
  have hfun := child d b c hvarD hguardD hdomD (by dsimp [d,c]; omega) (by dsimp [d]; omega)
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
    hp hq hv hgb hgc hchild hnext

end PASoundness.PAtoCompactSuccRightZeroFunctionalSucc

#print axioms PASoundness.PAtoCompactSuccRightZeroFunctionalSucc.successor_functional
