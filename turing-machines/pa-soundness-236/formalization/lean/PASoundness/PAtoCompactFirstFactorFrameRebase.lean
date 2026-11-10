import PASoundness.PAtoCompactFirstFactorRenameSyntax
import PASoundness.PAtoCompactLiteralCutBaseAlpha
import PASoundness.PAtoCompactAddBaseMultiAlpha
import PASoundness.PAtoCompactMulBaseMultiAlpha
import PASoundness.PAtoCompactGuardBaseTransport

/-! Generic allocator transport for a supplied first-factor successor frame.
The input labels may coincide; the same existential output is retained through
all four output relations. No input proof or arithmetic axiom is constructed. -/
namespace PASoundness.PAtoCompactFirstFactorFrameRebase

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardBaseTransport
open PASoundness.PAtoCompactFirstFactorOutputAlpha PASoundness.PAtoCompactFirstFactorRenameSyntax
open PASoundness.PAtoCompactLiteralCutBaseSyntax PASoundness.PAtoCompactAddBaseMultiAlpha
open PASoundness.PAtoCompactMulBaseMultiAlpha

set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Reallocate every component of the retained body for the same output r. -/
def body_rebase (a b p y s r : Nat)
    (hpa : p < a+2) (hya : y < a+2) (hsa : s < a+2) (hra : r < a+2)
    (hpb : p < b+2) (hyb : y < b+2) (hsb : s < b+2) (hrb : r < b+2) :
    KDerivation (imp (body a p y s r).encode (body b p y s r).encode) := by
  have hd := domainAt_transport a b r (by omega) (by omega)
  have hc := (PASoundness.PAtoCompactLiteralCutBaseAlpha.base_alpha a b p y r
    hpa hya hra hpb hyb hrb).forward
  have ha := (addAt_base_alpha a b p y r hpa hya hra hpb hyb hrb).forward
  have hm := (mulAt_base_alpha a b s y r hsa hya hra hsb hyb hrb).forward
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [(body a p y s r).encode]
  have h : Context Γ (body a p y s r).encode := .head _ _
  have h' : Context Γ (both (domainAt a r).encode
      (both (literalCutAt a p y r).encode
        (both (addAt a p y r).encode (mulAt a s y r).encode))) := by
    simpa [body, andF, Formula.not, Formula.encode, both, neg] using h
  have hD := Context.mp (Context.conjunctionLeft h') (.closed hd)
  have h1 := Context.conjunctionRight h'
  have hC := Context.mp (Context.conjunctionLeft h1) (.closed hc)
  have h2 := Context.conjunctionRight h1
  have hA := Context.mp (Context.conjunctionLeft h2) (.closed ha)
  have hM := Context.mp (Context.conjunctionRight h2) (.closed hm)
  have hres := Context.conjunctionIntro hD
    (Context.conjunctionIntro hC (Context.conjunctionIntro hA hM))
  simpa [Γ, body, andF, Formula.not, Formula.encode, both, neg] using hres

/-- A supplied frame proof at allocator a yields one at b. All four input
labels may alias, and the raw successor test name w stays unchanged. -/
def frame_rebase (a b r w x y p s : Nat)
    (hxa : x < a+2) (hya : y < a+2) (hpa : p < a+2) (hsa : s < a+2) (hra : r < a+2)
    (hxb : x < b+2) (hyb : y < b+2) (hpb : p < b+2) (hsb : s < b+2) (hrb : r < b+2)
    (d : KDerivation (assignedFrame a r w x y p s).encode) :
    KDerivation (assignedFrame b r w x y p s).encode := by
  have hx := domainAt_transport b a x (by omega) (by omega)
  have hy := domainAt_transport b a y (by omega) (by omega)
  have hp := domainAt_transport b a p (by omega) (by omega)
  have hm := (mulAt_base_alpha b a x y p hxb hyb hpb hxa hya hpa).forward
  have hw := existsCongr r (body_rebase a b p y s r hpa hya hsa hra hpb hyb hsb hrb)
  change KDerivation (imp (domainAt b x).encode (imp (domainAt b y).encode
    (imp (domainAt b p).encode (imp (PASoundness.PAtoCompactAdjunction.namedSuccessor x s w).encode
      (imp (mulAt b x y p).encode (existsCode r (body b p y s r).encode))))))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let S := (PASoundness.PAtoCompactAdjunction.namedSuccessor x s w).encode
  let Γ := [(mulAt b x y p).encode,S,(domainAt b p).encode,
    (domainAt b y).encode,(domainAt b x).encode]
  have hM : Context Γ (mulAt b x y p).encode := .head _ _
  have hS : Context Γ S := .hypothesis (by simp [Γ])
  have hP : Context Γ (domainAt b p).encode := .hypothesis (by simp [Γ])
  have hY : Context Γ (domainAt b y).encode := .hypothesis (by simp [Γ])
  have hX : Context Γ (domainAt b x).encode := .hypothesis (by simp [Γ])
  have hsource : Context Γ (existsCode r (body a p y s r).encode) := by
    have hh : Context Γ (imp (domainAt a x).encode (imp (domainAt a y).encode
        (imp (domainAt a p).encode (imp S (imp (mulAt a x y p).encode
          (existsCode r (body a p y s r).encode)))))) := by
      simpa [assignedFrame, Formula.encode, S] using (Context.closed (Γ := Γ) d)
    exact .mp (.mp hM (.closed hm)) (.mp hS (.mp (.mp hP (.closed hp))
      (.mp (.mp hY (.closed hy)) (.mp (.mp hX (.closed hx)) hh))))
  exact .mp hsource (.closed hw)

theorem frame_rebase_certificate (a b r w x y p s : Nat)
    (hxa : x < a+2) (hya : y < a+2) (hpa : p < a+2) (hsa : s < a+2) (hra : r < a+2)
    (hxb : x < b+2) (hyb : y < b+2) (hpb : p < b+2) (hsb : s < b+2) (hrb : r < b+2)
    (d : KDerivation (assignedFrame a r w x y p s).encode) :
    theoremCode (certificate (frame_rebase a b r w x y p s hxa hya hpa hsa hra
      hxb hyb hpb hsb hrb d)) = (assignedFrame b r w x y p s).encode := certificate_correct _

end PASoundness.PAtoCompactFirstFactorFrameRebase

#print axioms PASoundness.PAtoCompactFirstFactorFrameRebase.body_rebase
#print axioms PASoundness.PAtoCompactFirstFactorFrameRebase.frame_rebase
#print axioms PASoundness.PAtoCompactFirstFactorFrameRebase.frame_rebase_certificate
