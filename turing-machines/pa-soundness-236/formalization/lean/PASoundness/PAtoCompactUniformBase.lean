import PASoundness.PAtoCompactUniformStep

/-! Capture-safe quantified zero-base premise for the local K case proof.
The premise, classification, leastness and domain are not proved here. Code 1
is literally `member 0 0`, not primitive falsity in arbitrary raw models. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactUniformBase
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactLeastCounterexample
open PASoundness.PAtoCompactUniformStep

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The explicitly supplied base schema: every displayed zero witness m
satisfies the capture-safe named instance f(m). -/
def uniformBaseCode (t m z : Nat) (f : CompactNamed.Formula) : Nat :=
  allCode m (imp (zeroCode m z) (CompactNamed.replace t m f).encode)

def namedUniformBaseBody (t m z : Nat) (f : CompactNamed.Formula) : CompactNamed.Formula :=
  .imp (.all z (.imp (.member m z) .bottom)) (CompactNamed.replace t m f)

/-- K derives the needed local zero-base instance from the supplied universal
schema. The m name is fresh for the original predicate and distinct from both
the substitution name and zero graph's internal test binder. -/
def uniform_base_instance (t m z : Nat) (f : CompactNamed.Formula)
    (_htm : t ≠ m) (hzm : z ≠ m) (hmf : m ∉ f.names) (_htf : t ∉ f.binders) :
    KDerivation (imp (uniformBaseCode t m z f)
      (imp (zeroCode m z) (CompactNamed.replace t m f).encode)) := by
  let body := namedUniformBaseBody t m z f
  have hmb : m ∉ f.binders := fun h => hmf (f.binders_subset_names h)
  have hbody : m ∉ body.binders := by
    simp [body, namedUniformBaseBody, CompactNamed.Formula.binders,
      CompactNamed.replace_binders, Ne.symm hzm, hmb]
  have h := CompactNamed.allSpecialize m body hbody
  simpa [body, namedUniformBaseBody, uniformBaseCode, zeroCode,
    CompactNamed.Formula.encode, CompactProof.neg] using h

/-- Under explicit quantified base and step hypotheses, the supplied
zero-or-predecessor classification and exposed least-filter witness lead to
literal code 1. The quantified hypotheses and classification remain premises;
this is not a global induction theorem. -/
def uniform_base_step_cases (x t y m r z w p q : Nat) (f : CompactNamed.Formula)
    (hxt : x ≠ t) (hty : t ≠ y) (htm : t ≠ m) (hzm : z ≠ m)
    (htf : t ∉ f.binders) (hmf : m ∉ f.names) (hyf : y ∉ f.names)
    (hyx : y ≠ x) (hym : y ≠ m) (hyz : y ≠ z)
    (hyc : y ≠ filterPredicate x t (neg f.encode))
    (hrc : r ≠ filterPredicate x t (neg f.encode)) (hrm : r ≠ m) (hry : r ≠ y)
    (hwy : w ≠ y) (hwm : w ≠ m)
    (hpm : p ≠ m) (hpy : p ≠ y) (hpq : p ≠ q) (hqm : q ≠ m) (hqy : q ≠ y) :
    let c := filterPredicate x t (neg f.encode)
    KDerivation (imp (filterGraph x c t (neg f.encode)) (imp (leastMemberCode c m r)
      (imp (uniformStepCode x t y m w p q f) (imp (zeroOrPredecessorCore x y m z w p q)
        (imp (uniformBaseCode t m z f) 1))))) := by
  dsimp only
  let c := filterPredicate x t (neg f.encode)
  let fm := (CompactNamed.replace t m f).encode
  let G := filterGraph x c t (neg f.encode)
  let L := leastMemberCode c m r
  let U := uniformStepCode x t y m w p q f
  let C := zeroOrPredecessorCore x y m z w p q
  let B := uniformBaseCode t m z f
  let Γ := [B,C,U,L,G]
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  have hc : Context Γ C := .hypothesis (by simp [Γ])
  have hu : Context Γ U := .hypothesis (by simp [Γ])
  have hl : Context Γ L := .hypothesis (by simp [Γ])
  have hg : Context Γ G := .hypothesis (by simp [Γ])
  have hmfb : m ∉ f.binders := fun h => hmf (f.binders_subset_names h)
  have hbase : Context Γ (imp (zeroCode m z) fm) :=
    .mp hb (.closed (uniform_base_instance t m z f htm hzm hmf htf))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  exact .mp hbase (.mp hc (.mp hu (.mp hl (.mp hg
    (.closed (uniform_step_cases x t y m r z w p q f hxt hty htm hzm htf hmfb hyf
      hyx hym hyz hyc hrc hrm hry hwy hwm hpm hpy hpq hqm hqy))))))

theorem uniform_base_step_cases_certificate (x t y m r z w p q : Nat) (f : CompactNamed.Formula)
    (hxt : x ≠ t) (hty : t ≠ y) (htm : t ≠ m) (hzm : z ≠ m)
    (htf : t ∉ f.binders) (hmf : m ∉ f.names) (hyf : y ∉ f.names)
    (hyx : y ≠ x) (hym : y ≠ m) (hyz : y ≠ z)
    (hyc : y ≠ filterPredicate x t (neg f.encode))
    (hrc : r ≠ filterPredicate x t (neg f.encode)) (hrm : r ≠ m) (hry : r ≠ y)
    (hwy : w ≠ y) (hwm : w ≠ m)
    (hpm : p ≠ m) (hpy : p ≠ y) (hpq : p ≠ q) (hqm : q ≠ m) (hqy : q ≠ y) :
    let c := filterPredicate x t (neg f.encode)
    theoremCode (certificate (uniform_base_step_cases x t y m r z w p q f hxt hty htm hzm htf hmf hyf
      hyx hym hyz hyc hrc hrm hry hwy hwm hpm hpy hpq hqm hqy)) =
      imp (filterGraph x c t (neg f.encode)) (imp (leastMemberCode c m r)
        (imp (uniformStepCode x t y m w p q f) (imp (zeroOrPredecessorCore x y m z w p q)
          (imp (uniformBaseCode t m z f) 1)))) :=
  certificate_correct (uniform_base_step_cases x t y m r z w p q f hxt hty htm hzm htf hmf hyf
    hyx hym hyz hyc hrc hrm hry hwy hwm hpm hpy hpq hqm hqy)

/-- In standard HF semantics the quantified base schema means f holds at
zero. The proof uses capture-safe substitution and the exact zero-graph
semantics separately from the K proof construction. -/
theorem uniform_base_standard (t m z : Nat) (f : CompactNamed.Formula)
    (htm : t ≠ m) (hzm : z ≠ m) (hmf : m ∉ f.names) (htf : t ∉ f.binders)
    (ρ : CompactMatrix.Environment) :
    (CompactMatrix.decode (uniformBaseCode t m z f)).Realize ρ ↔
      ∀ v, v = 0 → f.Realize (CompactMatrix.update ρ t v) := by
  have hmb : m ∉ f.binders := fun h => hmf (f.binders_subset_names h)
  rw [uniformBaseCode, CompactSemantics.realize_all]
  apply forall_congr'
  intro v
  rw [CompactSemantics.realize_imp,
    zeroCode_realize m z (CompactMatrix.update ρ m v) (Ne.symm hzm),
    CompactNamed.Formula.encode_realize,
    CompactNamed.replace_realize t m f htf hmb (CompactMatrix.update ρ m v)]
  simp only [CompactSemantics.update_same]
  have h : f.Realize (CompactMatrix.update (CompactMatrix.update ρ m v) t v) ↔
      f.Realize (CompactMatrix.update ρ t v) := by
    rw [CompactSemantics.update_commute ρ m t v v (Ne.symm htm)]
    exact CompactNamed.Formula.realize_update_fresh f _ m v hmf
  exact imp_congr Iff.rfl h

end PASoundness.PAtoCompactUniformBase
