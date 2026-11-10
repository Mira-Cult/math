import PASoundness.PAtoCompactAddZeroGraphFunctional
import PASoundness.PAtoCompactEquivMultiAlpha
import PASoundness.PAtoCompactSuccTermTotality
import PASoundness.PAtoCompactGuardBaseTransport

/-! Pointwise quotient chaining from the two graphs' actual candidate guards.
No graph functionality or existence is assumed or inferred here. -/
namespace PASoundness.PAtoCompactAddZeroQuotientChain
open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermZeroGuarded
open PASoundness.PAtoCompactAddZeroGraphFunctional PASoundness.PAtoCompactEquivMultiAlpha
open PASoundness.PAtoCompactSuccTermTotality PASoundness.PAtoCompactGuardBaseTransport
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] PASoundness.CompactProof.imp Cantor.pair Cantor.triangle

/-- The child and whole graphs provide the two candidate assumptions needed
to compose the three quotient equivalences at a common allocator. -/
def pointwise {α : Type} (v : α → Nat) (t : Peano.language.Term α)
    (b c p q : Nat) (hbc : b < c) (hp : p < b) (hq : q < b) :
    KDerivation (imp (termGraph v t b (b+64)).encode
      (imp (termGraph v (binaryTerm true t (.func .zero Fin.elim0)) p b).encode
      (imp (equivAt (c+1) b c).encode
      (imp (equivAt b b p).encode
      (imp (equivAt c c q).encode (equivAt b p q).encode))))) := by
  let e := c+1
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(equivAt c c q).encode, (equivAt b b p).encode,
    (equivAt e b c).encode,
    (termGraph v (binaryTerm true t (.func .zero Fin.elim0)) p b).encode,
    (termGraph v t b (b+64)).encode]
  have hCQ : Context Γ (equivAt c c q).encode := .head _ _
  have hBP : Context Γ (equivAt b b p).encode := .hypothesis (by simp [Γ])
  have hBC : Context Γ (equivAt e b c).encode := .hypothesis (by simp [Γ])
  have hA : Context Γ (termGraph v (binaryTerm true t (.func .zero Fin.elim0)) p b).encode := .hypothesis (by simp [Γ])
  have hC : Context Γ (termGraph v t b (b+64)).encode := .hypothesis (by simp [Γ])
  have hDb0 := Context.mp hC (.closed (termGraph_domain v t b (b+64)))
  have hDb : Context Γ (domainAt e b).encode := Context.mp hDb0
    (.closed (domainAt_transport (b+64) e b (by omega) (by dsimp [e]; omega)))
  have hDp0 := Context.mp hA (.closed (termGraph_domain v (binaryTerm true t (.func .zero Fin.elim0)) p b))
  have hDp : Context Γ (domainAt e p).encode := Context.mp hDp0
    (.closed (domainAt_transport b e p (by omega) (by dsimp [e]; omega)))
  have hBP' : Context Γ (equivAt e b p).encode := Context.mp hBP
    (.closed (equivAt_base_alpha b e b p (by omega) (by omega) (by dsimp [e]; omega) (by dsimp [e]; omega)).forward)
  have hCQ' : Context Γ (equivAt e c q).encode := Context.mp hCQ
    (.closed (equivAt_base_alpha c e c q (by omega) (by omega) (by dsimp [e]; omega) (by dsimp [e]; omega)).forward)
  have chain := quotient_chain e b c p q (by dsimp [e]; omega) (by dsimp [e]; omega)
    (by dsimp [e]; omega) (by dsimp [e]; omega)
  have hPQ' : Context Γ (equivAt e p q).encode :=
    .mp hCQ' (.mp hBC (.mp hBP' (.mp hDp (.mp hDb (.closed chain)))))
  exact .mp hPQ' (.closed (equivAt_base_alpha b e p q (by omega) (by omega)
    (by dsimp [e]; omega) (by dsimp [e]; omega)).backward)

end PASoundness.PAtoCompactAddZeroQuotientChain
#print axioms PASoundness.PAtoCompactAddZeroQuotientChain.pointwise
