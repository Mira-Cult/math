import PASoundness.PAtoCompactLiteralCutFixedAllocated
import PASoundness.PAtoCompactLiteralCutTwoInputRename
import PASoundness.PAtoCompactLiteralCutOutputAlpha
import PASoundness.PAtoCompactLiteralCutBaseTransport

/-! Candidate-guarded addition output with a literal first-input cut, at
arbitrary allocated names. The input names may coincide; the output binder is
fresh for both. The construction produces finite K proof data, without
multiplication totality, soundness, or the PA bridge. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactLiteralCutArbitraryTotality
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactLiteralCutBaseSyntax
open PASoundness.PAtoCompactLiteralCutFixedAllocated PASoundness.PAtoCompactLiteralCutTwoInputRename
open PASoundness.PAtoCompactLiteralCutBaseTransport
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Both candidate inputs have a candidate output whose addition cut is
literally the first input. Input labels may coincide; output-label freshness
and the allocation bounds are explicit. -/
def literal_cut_total (b x y out : Nat)
    (hx : x < b+2) (hy : y < b+2) (ho : out < b+2)
    (hxo : x ≠ out) (hyo : y ≠ out) :
    KDerivation (imp (domainAt b x).encode (imp (domainAt b y).encode
      (existsCode out (andF (domainAt b out) (literalCutAt b x y out)).encode))) := by
  let q := max 32 (max x (max y out)) + 1
  let high := max b q + 40
  have hq : 32 < q := by dsimp [q]; omega
  have hqx : q ≠ x := by dsimp [q]; omega
  have hqy : q ≠ y := by dsimp [q]; omega
  have hqo : q ≠ out := by dsimp [q]; omega
  have hqh : q < high := by dsimp [high]; omega
  have hhigh : 38 ≤ high := by dsimp [high]; omega
  have hxh : x < high+2 := by dsimp [high, q]; omega
  have hyh : y < high+2 := by dsimp [high, q]; omega
  have hoh : out < high+2 := by dsimp [high, q]; omega
  have halpha := PASoundness.PAtoCompactLiteralCutOutputAlpha.output_alpha
    high 30 31 32 q (by omega) (by omega) (by decide) (by decide) (by omega) (by omega) (by omega)
  have hfixed : KDerivation (source high q).encode := by
    have h0 := fixed_allocated high hhigh
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [(domainAt high 31).encode, (domainAt high 30).encode]
    have hy' : Context Γ (domainAt high 31).encode := .head _ _
    have hx' : Context Γ (domainAt high 30).encode := .hypothesis (by simp [Γ])
    have hw := Context.mp hy' (Context.mp hx' (.closed h0))
    have hz := Context.mp hw (.closed halpha)
    simpa [source, PASoundness.PAtoCompactLiteralCutOutputAlpha.body, Formula.encode] using hz
  have hsource := rename_inputs high q x y hhigh hq (by omega) hxh hyh
    (Ne.symm hqx) (Ne.symm hqy) hfixed
  have hout := PASoundness.PAtoCompactLiteralCutOutputAlpha.output_alpha
    high x y q out hqh hoh hqx hqy hqo (Ne.symm hxo) (Ne.symm hyo)
  have hmid : KDerivation (imp (domainAt high x).encode (imp (domainAt high y).encode
      (existsCode out (andF (domainAt high out) (literalCutAt high x y out)).encode))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [(domainAt high y).encode, (domainAt high x).encode]
    have hy' : Context Γ (domainAt high y).encode := .head _ _
    have hx' : Context Γ (domainAt high x).encode := .hypothesis (by simp [Γ])
    have hw := Context.mp hy' (Context.mp hx' (.closed hsource))
    exact .mp hw (.closed hout)
  exact rebase high b x y out hxh hyh hoh hx hy ho hmid

theorem literal_cut_total_certificate (b x y out : Nat)
    (hx : x < b+2) (hy : y < b+2) (ho : out < b+2)
    (hxo : x ≠ out) (hyo : y ≠ out) :
    theoremCode (certificate (literal_cut_total b x y out hx hy ho hxo hyo)) =
      imp (domainAt b x).encode (imp (domainAt b y).encode
        (existsCode out (andF (domainAt b out) (literalCutAt b x y out)).encode)) :=
  certificate_correct _
end PASoundness.PAtoCompactLiteralCutArbitraryTotality
#print axioms PASoundness.PAtoCompactLiteralCutArbitraryTotality.literal_cut_total
#print axioms PASoundness.PAtoCompactLiteralCutArbitraryTotality.literal_cut_total_certificate
