import PASoundness.PAtoCompactOrdinalShiftGraph
import PASoundness.PAtoCompactOrdinalEquivalence

/-! A candidate first-order quotient-addition relation and its standard-HF
meaning. The relation is intended to be restricted to candidate-domain inputs.
This file does not prove K existence, functionality, congruence, arithmetic
axioms, induction or PA proof transport. Its classical negation reading is
only standard-HF; compact code 1 is literal self-membership in raw K models. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactOrdinalAddition
open PASoundness.CompactNamed PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactOrdinalEquivalence PASoundness.PAtoCompactOrdinalInterval
open PASoundness.PAtoCompactOrdinalShiftGraph PASoundness.HFCoding
open PASoundness.CompactMatrix (Environment bit update decode)

private def andF (a b : Formula) : Formula := (a.imp b.not).not
private def orF (a b : Formula) : Formula := a.not.imp b
private def iffF (a b : Formula) : Formula := andF (a.imp b) (b.imp a)

/-- The same concrete candidate equivalence with its free inputs renamed to
the indicated labels. Intended readings require these labels to be fresh for
its internal binders. -/
def equivAt (x y : Nat) : Formula :=
  replace 1 y (replace 0 x equivalentFormula)

/-- Name 34 is the portion of name 32 outside the cut at name 33; name 35 is
the element-test binder. -/
def suffixFormula : Formula := .all 35
  (iffF (.member 34 35) (andF (.member 32 35) (Formula.member 33 35).not))

/-- Inputs 30,31,32 are respectively the two summands and result. A cut 33
is either the result itself or one of its members; it is isomorphic to the
first input, while its relative complement 34 is isomorphic to the second. -/
def additionFormula : Formula := .ex 33 (.ex 34
  (andF (orF (.equal 33 32) (.member 32 33))
    (andF (equivAt 30 33) (andF suffixFormula (equivAt 31 34)))))

/-- This is the free-name set of the named IR. Encoding its bottom as literal
self-membership is a separate raw-K consideration. -/
theorem addition_named_free : additionFormula.free = {30,31,32} := by decide

private theorem and_meaning (a b : Formula) (ρ : Environment) :
    (andF a b).Realize ρ ↔ a.Realize ρ ∧ b.Realize ρ := by
  simp [andF, Formula.not, Formula.Realize]

private theorem or_meaning (a b : Formula) (ρ : Environment) :
    (orF a b).Realize ρ ↔ a.Realize ρ ∨ b.Realize ρ := by
  classical
  simp [orF, Formula.not, Formula.Realize]
  tauto

/-- The suffix formula has its literal set-difference meaning in standard HF. -/
theorem suffix_meaning (ρ : Environment) : suffixFormula.Realize ρ ↔
    ∀ z, bit (ρ 34) z = true ↔ bit (ρ 32) z = true ∧ bit (ρ 33) z = false := by
  classical
  simp [suffixFormula, iffF, andF, Formula.not, Formula.Realize, update]
  constructor
  · intro h z
    exact ⟨(h z).1, fun hz => (h z).2 hz.1 hz.2⟩
  · intro h z
    exact ⟨(h z).mp, fun hz hz' => (h z).mpr ⟨hz,hz'⟩⟩

/-- Semantic meaning of the two free-input replacements used below. -/
theorem equivAt_meaning (x y : Nat) (ρ : Environment)
    (hx : x ∉ equivalentFormula.binders) (hy : y ∉ equivalentFormula.binders)
    (hxy : x ≠ 1) : (equivAt x y).Realize ρ ↔
      equivalentFormula.Realize (update (update ρ 1 (ρ y)) 0 (ρ x)) := by
  unfold equivAt
  rw [replace_realize 1 y _ (by simpa [replace_binders] using (show 1 ∉ equivalentFormula.binders by decide))
      (by simpa [replace_binders] using hy)]
  rw [replace_realize 0 x equivalentFormula (by decide) hx]
  simp [update, hxy]

private theorem equivAt_ordinal (x y : Nat) (ρ : Environment) (n m : Nat)
    (hx : x ∉ equivalentFormula.binders) (hy : y ∉ equivalentFormula.binders)
    (hxy : x ≠ 1) (h0 : ρ x = (ordinal n).code) (h1 : ρ y = (ordinal m).code) :
    (equivAt x y).Realize ρ ↔ n=m := by
  rw [equivAt_meaning x y ρ hx hy hxy]
  have h := standard_ordinal_iff (update (update ρ 1 (ρ y)) 0 (ρ x)) n m
    (by simp [update,h0]) (by simp [update,h1])
  rw [Formula.encode_realize] at h
  exact h

private theorem equivAt_interval (x y : Nat) (ρ : Environment) (l n m : Nat)
    (hx : x ∉ equivalentFormula.binders) (hy : y ∉ equivalentFormula.binders)
    (hxy : x ≠ 1) (h0 : ρ x = (ordinal n).code)
    (h1 : ρ y = (ordinalInterval l (l+m)).code) :
    (equivAt x y).Realize ρ ↔ n=m := by
  rw [equivAt_meaning x y ρ hx hy hxy]
  exact standard_interval_equivalent_iff (update (update ρ 1 (ρ y)) 0 (ρ x)) l n m
    (by simp [update,h0]) (by simp [update,h1])

private theorem suffix_code (ρ : Environment) (l k : Nat)
    (h32 : ρ 32 = (ordinal k).code) (h33 : ρ 33 = (ordinal l).code) :
    suffixFormula.Realize ρ ↔ ρ 34 = (ordinalInterval l k).code := by
  rw [suffix_meaning]
  constructor
  · intro h
    have he : (⟨ρ 34⟩ : Object) = ordinalInterval l k := by
      apply HFCoding.ext
      intro z
      have hz := h z.code
      change bit (ρ 34) z.code = true ↔
        bit (ρ 32) z.code = true ∧ bit (ρ 33) z.code = false at hz
      rw [mem_interval_iff_difference]
      change (bit (ρ 34) z.code = true) ↔
        (bit (ordinal k).code z.code = true ∧ ¬ bit (ordinal l).code z.code = true)
      rw [h32,h33] at hz
      cases hbit : bit (ordinal l).code z.code <;> simp_all
    exact congrArg Object.code he
  · intro h z
    have hi := mem_interval_iff_difference (⟨z⟩ : Object) l k
    change (bit (ordinalInterval l k).code z = true) ↔
      (bit (ordinal k).code z = true ∧ ¬ bit (ordinal l).code z = true) at hi
    rw [h,h32,h33]
    cases hbit : bit (ordinal l).code z <;> simp_all

/-- On finite ordinal codes the literal addition proposal holds exactly for
arithmetic addition. The proof supplies the actual HF interval and shift
graph as witnesses; it does not construct them in K. -/
theorem standard_ordinal_addition_iff (ρ : Environment) (i j k : Nat)
    (h30 : ρ 30 = (ordinal i).code) (h31 : ρ 31 = (ordinal j).code)
    (h32 : ρ 32 = (ordinal k).code) :
    (decode additionFormula.encode).Realize ρ ↔ k=i+j := by
  rw [Formula.encode_realize]
  change (∃ u, ∃ v, (andF (orF (.equal 33 32) (.member 32 33))
    (andF (equivAt 30 33) (andF suffixFormula (equivAt 31 34)))).Realize
      (update (update ρ 33 u) 34 v)) ↔ _
  simp only [and_meaning, or_meaning]
  constructor
  · rintro ⟨u,v,hcut,heq,hsuf,htail⟩
    let η := update (update ρ 33 u) 34 v
    have hη30 : η 30 = (ordinal i).code := by simp [η,update,h30]
    have hη31 : η 31 = (ordinal j).code := by simp [η,update,h31]
    have hη32 : η 32 = (ordinal k).code := by simp [η,update,h32]
    have hη33 : η 33 = u := by simp [η,update]
    have hη34 : η 34 = v := by simp [η]
    have hcut' : u=(ordinal k).code ∨ bit (ordinal k).code u = true := by
      simpa [Formula.Realize,η,update,h32] using hcut
    obtain ⟨l,hl,hucode⟩ : ∃ l, l≤k ∧ u=(ordinal l).code := by
      rcases hcut' with he | hm
      · exact ⟨k,le_rfl,he⟩
      · have hm' : (⟨u⟩ : Object) ∈ ordinal k := hm
        obtain ⟨l,hl,he⟩ := (mem_ordinal _ _).mp hm'
        exact ⟨l,by omega,congrArg Object.code he⟩
    have hl : i=l := (equivAt_ordinal 30 33 η i l (by decide) (by decide)
      (by decide) hη30 (by simpa [hucode] using hη33)).mp heq
    have hv : v=(ordinalInterval l k).code := by
      have hh := (suffix_code η l k hη32 (by simpa [hucode] using hη33)).mp hsuf
      simpa [hη34] using hh
    have hsum : l+(k-l)=k := by omega
    have hj : j=k-l := (equivAt_interval 31 34 η l j (k-l)
      (by decide) (by decide) (by decide) hη31
      (by simpa [hsum,hv] using hη34)).mp htail
    omega
  · intro h
    let u := (ordinal i).code
    let v := (ordinalInterval i (i+j)).code
    let η := update (update ρ 33 u) 34 v
    have hη30 : η 30=(ordinal i).code := by simp [η,update,h30]
    have hη31 : η 31=(ordinal j).code := by simp [η,update,h31]
    have hη32 : η 32=(ordinal (i+j)).code := by simp [η,update,h32,h]
    have hη33 : η 33=(ordinal i).code := by simp [η,update,u]
    have hη34 : η 34=(ordinalInterval i (i+j)).code := by simp [η,v]
    refine ⟨u,v,?_,?_,?_,?_⟩
    · by_cases hj : j=0
      · left; simp [Formula.Realize,update,u,h32,h,hj]
      · right
        change bit (η 32) (η 33) = true
        rw [hη32,hη33]
        exact ordinal_member (by omega)
    · exact (equivAt_ordinal 30 33 η i i (by decide) (by decide)
        (by decide) hη30 hη33).mpr rfl
    · exact (suffix_code η i (i+j) hη32 hη33).mpr hη34
    · exact (equivAt_interval 31 34 η i j j (by decide) (by decide)
        (by decide) hη31 hη34).mpr rfl

end PASoundness.PAtoCompactOrdinalAddition

#print axioms PASoundness.PAtoCompactOrdinalAddition.suffix_meaning
#print axioms PASoundness.PAtoCompactOrdinalAddition.equivAt_meaning
#print axioms PASoundness.PAtoCompactOrdinalAddition.addition_named_free
#print axioms PASoundness.PAtoCompactOrdinalAddition.standard_ordinal_addition_iff
