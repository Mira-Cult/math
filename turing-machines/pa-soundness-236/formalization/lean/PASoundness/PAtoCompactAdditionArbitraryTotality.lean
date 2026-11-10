import PASoundness.PAtoCompactAdditionFixedBaseAllocated
import PASoundness.PAtoCompactAdditionTwoDomainRename
import PASoundness.PAtoCompactAdditionGeneralBaseTransport
import PASoundness.PAtoCompactAdditionZeroTotality

/-! Candidate-guarded addition output existence at arbitrary allocated names.
The proof constructs finite K proof data by relocating the independently
constructed fixed-name theorem through a fresh intermediate output and base.
Input labels may alias; the output binder must be distinct from both. This does
not prove graph functionality, multiplication totality, or the PA bridge. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionArbitraryTotality
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactAdditionFixedBaseAllocated
open PASoundness.PAtoCompactAdditionTwoDomainRename
open PASoundness.PAtoCompactAdditionGeneralBaseTransport
open PASoundness.PAtoCompactAdditionZeroTotality.M236ArbitraryOutputAlpha
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- K constructs an output candidate and its addition graph for any two
candidate inputs with labels within the allocator's range. The input labels
may coincide; the output label is required fresh for both inputs. -/
def addition_total (b x y out : Nat)
    (hx : x < b+2) (hy : y < b+2) (ho : out < b+2)
    (hxo : x ≠ out) (hyo : y ≠ out) :
    KDerivation (imp (domainAt b x).encode (imp (domainAt b y).encode
      (existsCode out (andF (domainAt b out) (addAt b x y out)).encode))) := by
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
  have halpha := (PASoundness.PAtoCompactAdditionOutputAlpha.output_alpha
    high high q (by omega) hq (by omega) (by omega)).1
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
    simpa [source, PASoundness.PAtoCompactAdditionOutputAlpha.body, Formula.encode] using hz
  have hsource := rename_inputs high q x y hhigh hq (by omega) hxh hyh
    (Ne.symm hqx) (Ne.symm hqy) hfixed
  have hout := output_alpha high x y q out hqh hoh hqx hqy hqo
    (Ne.symm hxo) (Ne.symm hyo)
  have hmid : KDerivation (imp (domainAt high x).encode (imp (domainAt high y).encode
      (existsCode out (andF (domainAt high out) (addAt high x y out)).encode))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [(domainAt high y).encode, (domainAt high x).encode]
    have hy' : Context Γ (domainAt high y).encode := .head _ _
    have hx' : Context Γ (domainAt high x).encode := .hypothesis (by simp [Γ])
    have hw := Context.mp hy' (Context.mp hx' (.closed hsource))
    exact .mp hw (.closed hout)
  exact rebase high b x y out hxh hyh hoh hx hy ho hmid

theorem addition_total_certificate (b x y out : Nat)
    (hx : x < b+2) (hy : y < b+2) (ho : out < b+2)
    (hxo : x ≠ out) (hyo : y ≠ out) :
    theoremCode (certificate (addition_total b x y out hx hy ho hxo hyo)) =
      imp (domainAt b x).encode (imp (domainAt b y).encode
        (existsCode out (andF (domainAt b out) (addAt b x y out)).encode)) :=
  certificate_correct _
end PASoundness.PAtoCompactAdditionArbitraryTotality
#print axioms PASoundness.PAtoCompactAdditionArbitraryTotality.addition_total
#print axioms PASoundness.PAtoCompactAdditionArbitraryTotality.addition_total_certificate
