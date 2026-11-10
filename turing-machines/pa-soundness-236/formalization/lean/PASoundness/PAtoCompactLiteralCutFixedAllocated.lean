import PASoundness.PAtoCompactLiteralCutFixedRename
import PASoundness.PAtoCompactLiteralCutOriginalAllocated
import PASoundness.PAtoCompactAlphaCongruence
import PASoundness.PAtoCompactGuardBaseTransport

/-! Fixed-input, arbitrary-base candidate output for the literal-cut addition
relation. Input 30 remains the actual cut; no arithmetic soundness theorem or
additional proof-data input is used. This does not establish multiplication
or the PA bridge. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactLiteralCutFixedAllocated
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardBaseTransport
open PASoundness.PAtoCompactLiteralCutAdditionDefinition PASoundness.PAtoCompactLiteralCutBaseSyntax
open PASoundness.PAtoCompactLiteralCutFixedRename PASoundness.PAtoCompactLiteralCutOriginalAllocated
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def conj_first {a b : Formula} (c : Formula) (h : KDerivation (imp a.encode b.encode)) :
    KDerivation (imp (andF a c).encode (andF b c).encode) := by
  change KDerivation (imp (neg (imp a.encode (neg c.encode))) (neg (imp b.encode (neg c.encode))))
  exact contrapose (implicationCongr h (PASoundness.CompactHilbertBasis.identity (neg c.encode)))

/-- Given two candidate inputs, K constructs an output candidate whose cut
is literally the first input, under the displayed allocator bound. -/
def fixed_allocated (b : Nat) (hb : 38 ≤ b) : KDerivation
    (imp (domainAt b 30).encode (imp (domainAt b 31).encode
      (existsCode 32 (andF (domainAt b 32) (literalCutAt b 30 31 32)).encode))) := by
  have h30 := domainAt_transport b 100 30 (by omega) (by decide)
  have h31 := domainAt_transport b 100 31 (by omega) (by decide)
  have h32 := domainAt_transport 100 b 32 (by decide) (by omega)
  have ha := original_allocated_alpha b hb
  have hbody : KDerivation (imp (andF (domainAt 100 32) literalCut).encode
      (andF (domainAt b 32) (literalCutAt b 30 31 32)).encode) := by
    have first := conj_first literalCut h32
    have second := (PASoundness.PAtoCompactAlphaCongruence.andF_congr
      (ProofEquiv.refl (domainAt b 32)) ha).forward
    exact compose first second
  have hex := existsCongr 32 hbody
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(domainAt b 31).encode, (domainAt b 30).encode]
  have hx : Context Γ (domainAt b 30).encode := .hypothesis (by simp [Γ])
  have hy : Context Γ (domainAt b 31).encode := .head _ _
  have hfixed := Context.mp (Context.mp (.mp hy (.closed h31))
    (Context.mp (.mp hx (.closed h30)) (.closed fixed_renamed))) (.closed hex)
  exact hfixed

theorem fixed_allocated_certificate (b : Nat) (hb : 38 ≤ b) :
    theoremCode (certificate (fixed_allocated b hb)) =
      imp (domainAt b 30).encode (imp (domainAt b 31).encode
        (existsCode 32 (andF (domainAt b 32) (literalCutAt b 30 31 32)).encode)) :=
  certificate_correct _
end PASoundness.PAtoCompactLiteralCutFixedAllocated
#print axioms PASoundness.PAtoCompactLiteralCutFixedAllocated.fixed_allocated
#print axioms PASoundness.PAtoCompactLiteralCutFixedAllocated.fixed_allocated_certificate
