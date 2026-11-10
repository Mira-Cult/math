import PASoundness.PAtoCompactMultiplicationTotalityFixedRename
import PASoundness.PAtoCompactMultiplicationTwoDomainRename
import PASoundness.PAtoCompactMultiplicationGeneralBaseTransport
import PASoundness.PAtoCompactMultiplicationOutputAlpha

/-! Conditional multiplication output existence at arbitrary allocated names.
The proof relocates an explicitly supplied fixed-name K proof through a fresh
intermediate output and base; it does not itself establish the input proof.
Input labels may alias; the output binder must be distinct from both. This does
not prove graph functionality, multiplication totality, or the PA bridge. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationArbitraryFromFixed
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactMultiplicationTotalityFixedRename
open PASoundness.PAtoCompactMultiplicationTwoDomainRename
open PASoundness.PAtoCompactMultiplicationGeneralBaseTransport
open PASoundness.PAtoCompactMultiplicationOutputAlpha
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- K constructs an output candidate and its multiplication graph for any two
candidate inputs with labels within the allocator's range. The input labels
may coincide; the output label is required fresh for both inputs. -/
def arbitrary_from_fixed
    (fixed : KDerivation (imp (domainAt 300 200).encode (imp (domainAt 300 30).encode
      (existsCode 32 (andF (domainAt 300 32) (mulAt 300 200 30 32)).encode))))
    (b x y out : Nat)
    (hx : x < b+2) (hy : y < b+2) (ho : out < b+2)
    (hxo : x ≠ out) (hyo : y ≠ out) :
    KDerivation (imp (domainAt b x).encode (imp (domainAt b y).encode
      (existsCode out (andF (domainAt b out) (mulAt b x y out)).encode))) := by
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
  have halpha := output_alpha high 30 31 32 q (by omega) (by omega)
    (by decide) (by decide) (by omega) (by omega) (by omega)
  have hfixed : KDerivation (source high q).encode := by
    have h0 := rebase 300 high 30 31 32 (by decide) (by decide) (by decide)
      (by omega) (by omega) (by omega) (fixed_renamed fixed)
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [(domainAt high 31).encode, (domainAt high 30).encode]
    have hy' : Context Γ (domainAt high 31).encode := .head _ _
    have hx' : Context Γ (domainAt high 30).encode := .hypothesis (by simp [Γ])
    have hw := Context.mp hy' (Context.mp hx' (.closed h0))
    have hz := Context.mp hw (.closed halpha)
    simpa [source, PASoundness.PAtoCompactMultiplicationOutputAlpha.body, Formula.encode] using hz
  have hsource := rename_inputs high q x y hhigh hq (by omega) hxh hyh
    (Ne.symm hqx) (Ne.symm hqy) hfixed
  have hout := output_alpha high x y q out hqh hoh hqx hqy hqo
    (Ne.symm hxo) (Ne.symm hyo)
  have hmid : KDerivation (imp (domainAt high x).encode (imp (domainAt high y).encode
      (existsCode out (andF (domainAt high out) (mulAt high x y out)).encode))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [(domainAt high y).encode, (domainAt high x).encode]
    have hy' : Context Γ (domainAt high y).encode := .head _ _
    have hx' : Context Γ (domainAt high x).encode := .hypothesis (by simp [Γ])
    have hw := Context.mp hy' (Context.mp hx' (.closed hsource))
    exact .mp hw (.closed hout)
  exact rebase high b x y out hxh hyh hoh hx hy ho hmid

theorem arbitrary_from_fixed_certificate
    (fixed : KDerivation (imp (domainAt 300 200).encode (imp (domainAt 300 30).encode
      (existsCode 32 (andF (domainAt 300 32) (mulAt 300 200 30 32)).encode))))
    (b x y out : Nat)
    (hx : x < b+2) (hy : y < b+2) (ho : out < b+2)
    (hxo : x ≠ out) (hyo : y ≠ out) :
    theoremCode (certificate (arbitrary_from_fixed fixed b x y out hx hy ho hxo hyo)) =
      imp (domainAt b x).encode (imp (domainAt b y).encode
        (existsCode out (andF (domainAt b out) (mulAt b x y out)).encode)) :=
  certificate_correct _
end PASoundness.PAtoCompactMultiplicationArbitraryFromFixed
#print axioms PASoundness.PAtoCompactMultiplicationArbitraryFromFixed.arbitrary_from_fixed
#print axioms PASoundness.PAtoCompactMultiplicationArbitraryFromFixed.arbitrary_from_fixed_certificate
