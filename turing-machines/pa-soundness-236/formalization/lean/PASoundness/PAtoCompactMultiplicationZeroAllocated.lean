import PASoundness.PAtoCompactZeroTermTotality
import PASoundness.PAtoCompactTermGraphBinderRange
import PASoundness.PAtoCompactFreeVacuity
import PASoundness.PAtoCompactMultiplicationZeroAllocatedMatrix

/-! Finite K zero-factor multiplication existence for the allocated template.
The construction combines a pointwise proof with an independently constructed
zero candidate; it does not establish arbitrary multiplication totality. -/
namespace PASoundness.PAtoCompactMultiplicationZeroAllocated

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermGraphBinderRange
open PASoundness.PAtoCompactZeroTermTotality PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactFreeNames

/-- Construct one candidate zero output from an explicit pointwise proof of
the allocated product relation. The output label is distinct from the input
labels as syntax; their assigned objects may coincide. -/
def zero_product_exists_of_pointwise (base x y out : Nat)
    (_hx : x < base) (_hy : y < base) (hout : out < base)
    (hox : out ≠ x) (_hoy : out ≠ y)
    (pointwise : KDerivation (imp (zeroAt base x).encode
      (imp (zeroAt base out).encode (mulAt base x y out).encode))) :
    KDerivation (imp (zeroAt base x).encode
      (existsCode out (andF (domainAt base out) (mulAt base x y out)).encode)) := by
  let Z := zeroAt base x
  let W := andF (domainAt base out) (zeroAt base out)
  let R := andF (domainAt base out) (mulAt base x y out)
  let E := Formula.ex out R
  have hfree : out ∉ Z.free := by
    intro h
    have hh := zeroAt_free base x h
    exact hox (Finset.mem_singleton.mp hh)
  have hzv := free_vacuity out Z hfree
  have hev : KDerivation (imp E.encode (allCode out E.encode)) :=
    free_vacuity out E (by simp [E, Formula.free])
  have hrb : out ∉ R.binders := by
    intro h
    have hd : out ∉ (domainAt base out).binders := by
      intro hbad
      have hh := domainAt_private base out out hbad
      omega
    have hm : out ∉ (mulAt base x y out).binders := by
      intro hbad
      have hh := mulAt_private base x y out out hbad
      omega
    simp [R, andF, CompactNamed.Formula.not, Formula.binders, hd, hm] at h
  have hintro := existsIntroduce out R hrb
  have hstep : KDerivation (imp Z.encode (imp W.encode E.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [W.encode, Z.encode]
    have hz : Context Γ Z.encode := .hypothesis (by simp [Γ])
    have hw : Context Γ (both (domainAt base out).encode (zeroAt base out).encode) := by
      have hh : Context Γ W.encode := .hypothesis (by simp [Γ])
      simpa [W, andF, Formula.encode, CompactNamed.Formula.not, both, neg] using hh
    have hd := Context.conjunctionLeft hw
    have ho := Context.conjunctionRight hw
    have hm : Context Γ (mulAt base x y out).encode := .mp ho (.mp hz (.closed pointwise))
    have hr : Context Γ R.encode := by
      have hh := Context.conjunctionIntro hd hm
      simpa [R, andF, Formula.encode, CompactNamed.Formula.not, both, neg] using hh
    exact .mp hr (.closed hintro)
  have hzero : KDerivation (existsCode out W.encode) := by
    simpa only [W, termGraph] using
      (zero_term_total (fun n : Nat => n) base out (by omega))
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [Z.encode]
  have hz : Context Γ Z.encode := Context.head [] _
  have hbody : Context Γ (imp W.encode E.encode) := .mp hz (.closed hstep)
  have hall : Context Γ (allCode out (imp W.encode E.encode)) :=
    Context.generalize out (by
      intro h hh
      have he : h = Z.encode := by simpa [Γ] using hh
      subst h
      exact hzv) hbody
  have he : Context Γ E.encode := Context.existsElim hev hall (.closed hzero)
  simpa only [E, Formula.encode] using he

theorem zero_product_exists_of_pointwise_certificate (base x y out : Nat)
    (hx : x < base) (hy : y < base) (hout : out < base)
    (hox : out ≠ x) (hoy : out ≠ y)
    (pointwise : KDerivation (imp (zeroAt base x).encode
      (imp (zeroAt base out).encode (mulAt base x y out).encode))) :
    theoremCode (certificate (zero_product_exists_of_pointwise base x y out hx hy hout hox hoy pointwise)) =
      imp (zeroAt base x).encode
        (existsCode out (andF (domainAt base out) (mulAt base x y out)).encode) := certificate_correct _

/-- A zero left factor has a candidate product output in the actual allocated
template. The second factor is arbitrary; the output label is fresh for both
input labels, while the represented objects may coincide. -/
def zero_product_exists (base x y out : Nat)
    (hx : x < base) (hy : y < base) (hout : out < base)
    (hox : out ≠ x) (hoy : out ≠ y) :
    KDerivation (imp (zeroAt base x).encode
      (existsCode out (andF (domainAt base out) (mulAt base x y out)).encode)) :=
  zero_product_exists_of_pointwise base x y out hx hy hout hox hoy
    (PAtoCompactMultiplicationZeroAllocatedMatrix.zero_product base x y out hx hy hout)

theorem zero_product_exists_certificate (base x y out : Nat)
    (hx : x < base) (hy : y < base) (hout : out < base)
    (hox : out ≠ x) (hoy : out ≠ y) :
    theoremCode (certificate (zero_product_exists base x y out hx hy hout hox hoy)) =
      imp (zeroAt base x).encode
        (existsCode out (andF (domainAt base out) (mulAt base x y out)).encode) := certificate_correct _

end PASoundness.PAtoCompactMultiplicationZeroAllocated

#print axioms PASoundness.PAtoCompactMultiplicationZeroAllocated.zero_product_exists_of_pointwise
#print axioms PASoundness.PAtoCompactMultiplicationZeroAllocated.zero_product_exists_of_pointwise_certificate
#print axioms PASoundness.PAtoCompactMultiplicationZeroAllocated.zero_product_exists
#print axioms PASoundness.PAtoCompactMultiplicationZeroAllocated.zero_product_exists_certificate
