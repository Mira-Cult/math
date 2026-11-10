import PASoundness.PAtoCompactZeroTermTotality
import PASoundness.PAtoCompactTermGraphBinderRange
import PASoundness.PAtoCompactFreeVacuity
import PASoundness.PAtoCompactMultiplicationRightZeroMatrix

/-! Finite K right-zero multiplication proof retaining the zero output. -/
namespace PASoundness.PAtoCompactMultiplicationRightZeroOutput

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermGraphBinderRange
open PASoundness.PAtoCompactZeroTermTotality PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactFreeNames

/-- A pointwise K proof can be packaged with a zero witness, retaining that
witness's zero graph in the existential conclusion. Names are syntactic. -/
def right_zero_output_of_pointwise (base x y out : Nat)
    (_hx : x < base) (_hy : y < base) (hout : out < base)
    (_hox : out ≠ x) (hoy : out ≠ y)
    (pointwise : KDerivation (imp (zeroAt base y).encode
      (imp (zeroAt base out).encode (mulAt base x y out).encode))) :
    KDerivation (imp (zeroAt base y).encode
      (existsCode out (andF (domainAt base out)
        (andF (zeroAt base out) (mulAt base x y out))).encode)) := by
  let Z := zeroAt base y
  let W := andF (domainAt base out) (zeroAt base out)
  let R := andF (domainAt base out) (andF (zeroAt base out) (mulAt base x y out))
  let E := Formula.ex out R
  have hfree : out ∉ Z.free := by
    intro h
    have hh := zeroAt_free base y h
    exact hoy (Finset.mem_singleton.mp hh)
  have hzv := free_vacuity out Z hfree
  have hev : KDerivation (imp E.encode (allCode out E.encode)) :=
    free_vacuity out E (by simp [E, Formula.free])
  have hrb : out ∉ R.binders := by
    intro h
    have hd : out ∉ (domainAt base out).binders := by
      intro hbad
      have hh := domainAt_private base out out hbad
      omega
    have hz : out ∉ (zeroAt base out).binders := by
      intro hbad
      have hh := zeroAt_private base out out hbad
      omega
    have hm : out ∉ (mulAt base x y out).binders := by
      intro hbad
      have hh := mulAt_private base x y out out hbad
      omega
    simp [R, andF, CompactNamed.Formula.not, Formula.binders, hd, hz, hm] at h
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
      have hh := Context.conjunctionIntro hd (Context.conjunctionIntro ho hm)
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

/-- The output can be chosen to satisfy both zero and multiplication graphs
when the second factor is zero. Input labels may coincide. -/
def right_zero_output (base x y out : Nat)
    (hx : x < base) (hy : y < base) (hout : out < base)
    (hox : out ≠ x) (hoy : out ≠ y) :
    KDerivation (imp (zeroAt base y).encode
      (existsCode out (andF (domainAt base out)
        (andF (zeroAt base out) (mulAt base x y out))).encode)) :=
  right_zero_output_of_pointwise base x y out hx hy hout hox hoy
    (PAtoCompactMultiplicationRightZeroMatrix.zero_product base x y out hx hy hout)

theorem right_zero_output_certificate (base x y out : Nat)
    (hx : x < base) (hy : y < base) (hout : out < base)
    (hox : out ≠ x) (hoy : out ≠ y) :
    theoremCode (certificate (right_zero_output base x y out hx hy hout hox hoy)) =
      imp (zeroAt base y).encode
        (existsCode out (andF (domainAt base out)
          (andF (zeroAt base out) (mulAt base x y out))).encode) :=
  certificate_correct _

end PASoundness.PAtoCompactMultiplicationRightZeroOutput

#print axioms PASoundness.PAtoCompactMultiplicationRightZeroOutput.right_zero_output_of_pointwise
#print axioms PASoundness.PAtoCompactMultiplicationRightZeroOutput.right_zero_output
#print axioms PASoundness.PAtoCompactMultiplicationRightZeroOutput.right_zero_output_certificate
