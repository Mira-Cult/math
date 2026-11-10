import PASoundness.CompactFreshen
import PASoundness.PAtoCompactFreeVacuity

/-! Freshen the body before moving an enclosing universal binder. This gives
finite K proofs of the two alpha directions but does not identify the result
with a separately generated PA scope translation. -/
namespace PASoundness.PAtoCompactGeneralizationFreshAlpha

open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactFreeVacuity

theorem replace_self (x : Nat) (f : Formula) : replace x x f = f := by
  induction f with
  | truth | bottom => rfl
  | member a b | equal a b =>
      by_cases ha : a = x <;> by_cases hb : b = x <;> simp [replace, rename, ha, hb]
  | imp a b ia ib => simp [replace, ia, ib]
  | all z a ih | ex z a ih =>
      by_cases hz : z = x <;> simp [replace, hz, ih]

/-- Freshening a body above `x` and a fresh target `y` makes moving an
enclosing universal binder capture-safe. The result retains the freshly
allocated body and is not an equivalence of open formulas at different free
input names. -/
def universal_fresh_alpha (f : Formula) (start x y : Nat)
    (hn : ∀ v ∈ f.names, v < start)
    (hx : x < start) (hy : y < start) (hxy : x ≠ y) (hyfresh : y ∉ f.free) :
    ProofEquiv (.all x f) (.all y (replace x y (freshen f start hn).formula)) := by
  let fresh := freshen f start hn
  have hxbind : x ∉ fresh.formula.binders := by
    intro h
    have hg := fresh.binders_ge x h
    omega
  have hynames : y ∉ fresh.formula.names := by
    intro h
    rw [Formula.names_eq_free_union_binders] at h
    rcases Finset.mem_union.mp h with hf | hb
    · exact hyfresh (freshen_free_subset f start hn hf)
    · have hg := fresh.binders_ge y hb
      omega
  exact (ProofEquiv.universal x fresh.equivalent).trans
    (ProofEquiv.alphaAll x y fresh.formula hxy hxbind hynames)

/-- The same-binder case needs no freshness condition on that name. -/
def universal_fresh_same (f : Formula) (start x : Nat)
    (hn : ∀ v ∈ f.names, v < start) :
    ProofEquiv (.all x f) (.all x (replace x x (freshen f start hn).formula)) := by
  simpa only [replace_self] using ProofEquiv.universal x (freshen f start hn).equivalent

theorem universal_fresh_alpha_forward_certificate (f : Formula) (start x y : Nat)
    (hn : ∀ v ∈ f.names, v < start)
    (hx : x < start) (hy : y < start) (hxy : x ≠ y) (hyfresh : y ∉ f.free) :
    theoremCode (certificate (universal_fresh_alpha f start x y hn hx hy hxy hyfresh).forward) =
      imp (Formula.all x f).encode (Formula.all y (replace x y (freshen f start hn).formula)).encode :=
  certificate_correct _

theorem universal_fresh_alpha_backward_certificate (f : Formula) (start x y : Nat)
    (hn : ∀ v ∈ f.names, v < start)
    (hx : x < start) (hy : y < start) (hxy : x ≠ y) (hyfresh : y ∉ f.free) :
    theoremCode (certificate (universal_fresh_alpha f start x y hn hx hy hxy hyfresh).backward) =
      imp (Formula.all y (replace x y (freshen f start hn).formula)).encode (Formula.all x f).encode :=
  certificate_correct _

end PASoundness.PAtoCompactGeneralizationFreshAlpha

#print axioms PASoundness.PAtoCompactGeneralizationFreshAlpha.universal_fresh_alpha
#print axioms PASoundness.PAtoCompactGeneralizationFreshAlpha.replace_self
#print axioms PASoundness.PAtoCompactGeneralizationFreshAlpha.universal_fresh_same
#print axioms PASoundness.PAtoCompactGeneralizationFreshAlpha.universal_fresh_alpha_forward_certificate
#print axioms PASoundness.PAtoCompactGeneralizationFreshAlpha.universal_fresh_alpha_backward_certificate
