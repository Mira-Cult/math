import PASoundness.PAtoCompactVacuousUniversalFresh

/-! A K-level universal congruence step with automatically chosen common
binder and guard allocation. Alignment of the renamed children remains an
explicit input. -/
namespace PASoundness.PAtoCompactGuardedUniversalAlign

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.CompactHilbertBasis PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactGuardBaseTransport PASoundness.PAtoCompactTermGraphBinderRange
open PASoundness.PAtoCompactVacuousUniversal PASoundness.PAtoCompactVacuousUniversalFresh

def guardedBody (p base : Nat) (a : Formula) : Formula := .imp (domainAt base p) a

def commonName (p q : Nat) (a b : Formula) : Nat :=
  max p (max q ((a.names ∪ b.names).sup id)) + 1

/-- Rebase a universal's domain guard without changing its bound name. -/
def rebase_guard (p base : Nat) (a : Formula) (hp : p < base + 32) :
    KDerivation (imp (Formula.all p (guardedBody p (p+1) a)).encode
      (Formula.all p (guardedBody p base a)).encode) ×
    KDerivation (imp (Formula.all p (guardedBody p base a)).encode
      (Formula.all p (guardedBody p (p+1) a)).encode) := by
  have h1 := domainAt_transport (p+1) base p (by omega) hp
  have h2 := domainAt_transport base (p+1) p hp (by omega)
  exact ⟨allCongr p (implicationCongr h2 (identity a.encode)),
    allCongr p (implicationCongr h1 (identity a.encode))⟩

/-- Under explicit freshness, move the bound label after rebasing the guard. -/
def high_alpha (p z base : Nat) (a : Formula) (hp : p < base)
    (hpa : p ∉ a.binders) (hne : p ≠ z) (hz : z ∉ a.names) (hzb : z < base + 2) :
    ProofEquiv (.all p (guardedBody p base a))
      (.all z (.imp (domainAt base z) (replace p z a))) := by
  have hpb : p ∉ (guardedBody p base a).binders := by
    simp only [guardedBody, Formula.binders, Finset.mem_union, not_or]
    constructor
    · intro h
      have ht := domainAt_private base p p h
      omega
    · exact hpa
  have hzn : z ∉ (guardedBody p base a).names := by
    simp only [guardedBody, Formula.names, Finset.mem_union, not_or]
    exact ⟨low_name_not_domain_names base p z hzb (Ne.symm hne), hz⟩
  have h := ProofEquiv.alphaAll p z (guardedBody p base a) hne hpb hzn
  simpa only [guardedBody, replace, replace_domainAt base p z hp] using h

/-- A supplied common name can be chosen fresh for additional intermediate
formulas as well. The caller supplies only syntactic freshness/bounds and the
two finite K child implications. -/
def guarded_universals_of_child (p q z base : Nat) (a b : Formula)
    (hpa : p ∉ a.binders) (hqb : q ∉ b.binders)
    (hp : p < base) (hq : q < base) (hz : z < base + 2)
    (hpz : p ≠ z) (hqz : q ≠ z) (hza : z ∉ a.names) (hzb : z ∉ b.names)
    (hf : KDerivation (imp (replace p z a).encode (replace q z b).encode))
    (hr : KDerivation (imp (replace q z b).encode (replace p z a).encode)) :
    KDerivation (imp (Formula.all p (guardedBody p (p+1) a)).encode
      (Formula.all q (guardedBody q (q+1) b)).encode) ×
    KDerivation (imp (Formula.all q (guardedBody q (q+1) b)).encode
      (Formula.all p (guardedBody p (p+1) a)).encode) := by
  have ra := rebase_guard p base a (by omega)
  have rb := rebase_guard q base b (by omega)
  have aa := high_alpha p z base a hp hpa hpz hza hz
  have ba := high_alpha q z base b hq hqb hqz hzb hz
  have hf' := allCongr z (implicationCongr (identity (domainAt base z).encode) hf)
  have hr' := allCongr z (implicationCongr (identity (domainAt base z).encode) hr)
  exact ⟨compose ra.1 (compose aa.forward (compose hf' (compose ba.backward rb.2))),
    compose rb.1 (compose ba.forward (compose hr' (compose aa.backward ra.2)))⟩

/-- Choose one genuinely fresh binder for both guarded universals. The two
input implications must prove the children aligned after their respective
bound names have been replaced by this common label. -/
def guarded_universals_of_common_child (p q : Nat) (a b : Formula)
    (hpa : p ∉ a.binders) (hqb : q ∉ b.binders)
    (hf : let z := commonName p q a b
      KDerivation (imp (replace p z a).encode (replace q z b).encode))
    (hr : let z := commonName p q a b
      KDerivation (imp (replace q z b).encode (replace p z a).encode)) :
    KDerivation (imp (Formula.all p (guardedBody p (p+1) a)).encode
      (Formula.all q (guardedBody q (q+1) b)).encode) ×
    KDerivation (imp (Formula.all q (guardedBody q (q+1) b)).encode
      (Formula.all p (guardedBody p (p+1) a)).encode) := by
  let z := commonName p q a b
  let base := z + 1
  have hp : p < z := by dsimp [z, commonName]; omega
  have hq : q < z := by dsimp [z, commonName]; omega
  have hza : z ∉ a.names := by
    intro h
    have hl : z ≤ (a.names ∪ b.names).sup id :=
      Finset.le_sup (f := id) (Finset.mem_union_left _ h)
    dsimp [z, commonName] at hl
    omega
  have hzb : z ∉ b.names := by
    intro h
    have hl : z ≤ (a.names ∪ b.names).sup id :=
      Finset.le_sup (f := id) (Finset.mem_union_right _ h)
    dsimp [z, commonName] at hl
    omega
  exact guarded_universals_of_child p q z base a b hpa hqb
    (by dsimp [base]; omega) (by dsimp [base]; omega) (by dsimp [base]; omega)
    (by omega) (by omega) hza hzb hf hr

end PASoundness.PAtoCompactGuardedUniversalAlign

#print axioms PASoundness.PAtoCompactGuardedUniversalAlign.rebase_guard
#print axioms PASoundness.PAtoCompactGuardedUniversalAlign.high_alpha
#print axioms PASoundness.PAtoCompactGuardedUniversalAlign.guarded_universals_of_child
#print axioms PASoundness.PAtoCompactGuardedUniversalAlign.guarded_universals_of_common_child
