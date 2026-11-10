import PASoundness.PAtoCompactFirstFactorSuccessorAddShared
import PASoundness.PAtoCompactLiteralCutBaseAlpha
import PASoundness.PAtoCompactAddBaseMultiAlpha
import PASoundness.PAtoCompactMulBaseMultiAlpha
import PASoundness.PAtoCompactGuardBaseTransport

/-! Allocator-block transport for the fixed-name first-factor successor
shared-output proof. The output witness and all its relation conjuncts remain
shared. This does not rename operands or establish the PA axiom. -/
namespace PASoundness.PAtoCompactFirstFactorSuccessorSharedRebase

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactAdjunction PASoundness.PAtoCompactGuardBaseTransport
open PASoundness.PAtoCompactLiteralCutBaseSyntax PASoundness.PAtoCompactAddBaseMultiAlpha
open PASoundness.PAtoCompactMulBaseMultiAlpha PASoundness.PAtoCompactFirstFactorSuccessorAddShared

set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def resultBody (b : Nat) : Formula := andF (domainAt b 45)
  (andF (literalCutAt b 32 30 45)
    (andF (addAt b 32 30 45) (mulAt b 205 30 45)))

/-- Transport all four conjuncts for one fixed output. -/
def result_body (b : Nat) (hb : 205 < b) :
    KDerivation (imp (resultBody 300).encode (resultBody b).encode) := by
  have hd := domainAt_transport 300 b 45 (by omega) (by omega)
  have hc := (PASoundness.PAtoCompactLiteralCutBaseAlpha.base_alpha 300 b 32 30 45
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).forward
  have ha := (addAt_base_alpha 300 b 32 30 45
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).forward
  have hm := (mulAt_base_alpha 300 b 205 30 45
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).forward
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [(resultBody 300).encode]
  have h : Context Γ (resultBody 300).encode := .head _ _
  have h' : Context Γ (both (domainAt 300 45).encode
      (both (literalCutAt 300 32 30 45).encode
        (both (addAt 300 32 30 45).encode (mulAt 300 205 30 45).encode))) := by
    simpa [resultBody, andF, Formula.not, Formula.encode, both, neg] using h
  have hD := Context.mp (Context.conjunctionLeft h') (.closed hd)
  have h1 := Context.conjunctionRight h'
  have hC := Context.mp (Context.conjunctionLeft h1) (.closed hc)
  have h2 := Context.conjunctionRight h1
  have hA := Context.mp (Context.conjunctionLeft h2) (.closed ha)
  have hM := Context.mp (Context.conjunctionRight h2) (.closed hm)
  have hres := Context.conjunctionIntro hD
    (Context.conjunctionIntro hC (Context.conjunctionIntro hA hM))
  simpa [Γ, resultBody, andF, Formula.not, Formula.encode, both, neg] using hres

/-- Rebase the fixed-name shared witness to any allocator above all operand
names. The five source premises remain antecedents and the raw successor test
binder is unchanged. -/
noncomputable def rebase (b : Nat) (hb : 205 < b) : KDerivation
    (imp (domainAt b 204).encode
      (imp (domainAt b 30).encode (imp (domainAt b 32).encode
        (imp (successorCode 204 205 208) (imp (mulAt b 204 30 32).encode
          (existsCode 45 (resultBody b).encode)))))) := by
  have hd := domainAt_transport b 300 204 (by omega) (by omega)
  have hg := domainAt_transport b 300 30 (by omega) (by omega)
  have ho := domainAt_transport b 300 32 (by omega) (by omega)
  have hm := (mulAt_base_alpha b 300 204 30 32
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).forward
  have hw := existsCongr 45 (result_body b hb)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(mulAt b 204 30 32).encode, successorCode 204 205 208,
    (domainAt b 32).encode, (domainAt b 30).encode, (domainAt b 204).encode]
  have hM : Context Γ (mulAt b 204 30 32).encode := .head _ _
  have hS : Context Γ (successorCode 204 205 208) := .hypothesis (by simp [Γ])
  have hO : Context Γ (domainAt b 32).encode := .hypothesis (by simp [Γ])
  have hG : Context Γ (domainAt b 30).encode := .hypothesis (by simp [Γ])
  have hD : Context Γ (domainAt b 204).encode := .hypothesis (by simp [Γ])
  have hsource : Context Γ (existsCode 45 (resultBody 300).encode) := by
    have h := Context.mp (.mp hM (.closed hm))
      (.mp hS (.mp (.mp hO (.closed ho)) (.mp (.mp hG (.closed hg))
        (.mp (.mp hD (.closed hd)) (.closed shared_successor_add_output)))))
    simpa [resultBody] using h
  exact .mp hsource (.closed hw)

theorem rebase_certificate (b : Nat) (hb : 205 < b) :
    theoremCode (certificate (rebase b hb)) =
      imp (domainAt b 204).encode
        (imp (domainAt b 30).encode (imp (domainAt b 32).encode
          (imp (successorCode 204 205 208) (imp (mulAt b 204 30 32).encode
            (existsCode 45 (resultBody b).encode))))) := certificate_correct _

end PASoundness.PAtoCompactFirstFactorSuccessorSharedRebase

#print axioms PASoundness.PAtoCompactFirstFactorSuccessorSharedRebase.resultBody
#print axioms PASoundness.PAtoCompactFirstFactorSuccessorSharedRebase.result_body
#print axioms PASoundness.PAtoCompactFirstFactorSuccessorSharedRebase.rebase
#print axioms PASoundness.PAtoCompactFirstFactorSuccessorSharedRebase.rebase_certificate
