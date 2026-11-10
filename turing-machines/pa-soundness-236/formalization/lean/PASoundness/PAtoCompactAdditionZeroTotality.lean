import PASoundness.PAtoCompactAddTermBody
import PASoundness.PAtoCompactVacuousUniversal
import PASoundness.PAtoCompactAdditionZeroOperand
import PASoundness.PAtoCompactAdditionFinalBaseTransport

set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionZeroTotality
namespace M236ArbitraryOutputAlpha
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFreeNames
open PASoundness.PAtoCompactTermGraphBinderRange PASoundness.PAtoCompactAddTermBody
open PASoundness.PAtoCompactVacuousUniversal

def body (b x y q : Nat) : Formula := andF (domainAt b q) (addAt b x y q)

theorem source_not_binder (b x y q : Nat) (hq : q < b) :
    q ∉ (body b x y q).binders := by
  intro h
  simp only [body, andF_binders, Finset.mem_union] at h
  rcases h with h | h
  · have hh := domainAt_private b q q h; omega
  · have hh := addAt_private b x y q q h; omega

theorem target_not_names (b x y q out : Nat) (ho : out < b+2)
    (hxo : out ≠ x) (hyo : out ≠ y) (hqo : out ≠ q) :
    out ∉ (body b x y q).names := by
  intro h
  rw [Formula.names_eq_free_union_binders] at h
  rcases Finset.mem_union.mp h with h | h
  · simp only [body, andF_free, Finset.mem_union] at h
    rcases h with h | h
    · have hh := domainAt_free b q h
      simp only [Finset.mem_singleton] at hh
      exact hqo hh
    · have hh := addAt_free b x y q h
      simp only [Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hh with hh | hh | hh
      · exact hxo hh
      · exact hyo hh
      · exact hqo hh
  · simp only [body, andF_binders, Finset.mem_union] at h
    rcases h with h | h
    · have hh := domainAt_private b q out h; omega
    · have hh := addAt_private b x y q out h; omega

theorem replace_body (b x y q out : Nat) (hq : q < b) (hqx : q ≠ x) (hqy : q ≠ y) :
    replace q out (body b x y q) = body b x y out := by
  rw [body, body]
  simp only [andF, Formula.not, replace]
  rw [replace_domainAt b q out hq, replace_addAt b x y q q out (by omega)]
  simp [rename, Ne.symm hqx, Ne.symm hqy]

def output_alpha (b x y q out : Nat) (hq : q < b) (ho : out < b+2)
    (hqx : q ≠ x) (hqy : q ≠ y) (hqo : q ≠ out)
    (hox : out ≠ x) (hoy : out ≠ y) :
    KDerivation (imp (existsCode q (body b x y q).encode)
      (existsCode out (body b x y out).encode)) := by
  have h := existentialAlpha q out (body b x y q) hqo
    (source_not_binder b x y q hq)
    (target_not_names b x y q out ho hox hoy (Ne.symm hqo))
  rw [replace_body b x y q out hq hqx hqy] at h
  exact h.1
end M236ArbitraryOutputAlpha

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation

/-- K constructs the right-zero addition output under allocator name bounds.
Input labels may coincide; the output binder must be distinct from both. -/
def right_zero_total (b x y out : Nat)
    (hx : x < b+2) (hy : y < b+2) (ho : out < b+2)
    (hxo : x ≠ out) (hyo : y ≠ out) :
    KDerivation (imp (domainAt b x).encode (imp (zeroAt b y).encode
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
  have hsource := PAtoCompactAdditionZeroOperand.M236AddOperandInstantiation.instantiated
    high q x y hhigh hq (by omega) hxh hyh (Ne.symm hqx) (Ne.symm hqy)
  have halpha := M236ArbitraryOutputAlpha.output_alpha high x y q out hqh hoh
    hqx hqy hqo (Ne.symm hxo) (Ne.symm hyo)
  have hmid : KDerivation (imp (domainAt high x).encode (imp (zeroAt high y).encode
      (existsCode out (andF (domainAt high out) (addAt high x y out)).encode))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [(zeroAt high y).encode, (domainAt high x).encode]
    have hzy : Context Γ (zeroAt high y).encode := .head _ _
    have hdx : Context Γ (domainAt high x).encode := .hypothesis (by simp [Γ])
    have hres := Context.mp hzy (Context.mp hdx (Context.closed hsource))
    exact .mp hres (.closed halpha)
  exact PAtoCompactAdditionFinalBaseTransport.rebase high b x y out
    hxh hyh hoh hx hy ho hmid

theorem right_zero_total_certificate (b x y out : Nat)
    (hx : x < b+2) (hy : y < b+2) (ho : out < b+2)
    (hxo : x ≠ out) (hyo : y ≠ out) :
    theoremCode (certificate (right_zero_total b x y out hx hy ho hxo hyo)) =
      imp (domainAt b x).encode (imp (zeroAt b y).encode
        (existsCode out (andF (domainAt b out) (addAt b x y out)).encode)) := certificate_correct _

end PASoundness.PAtoCompactAdditionZeroTotality
#print axioms PASoundness.PAtoCompactAdditionZeroTotality.right_zero_total
#print axioms PASoundness.PAtoCompactAdditionZeroTotality.right_zero_total_certificate
