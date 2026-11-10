import PASoundness.PAtoCompactTermTranslation
import PASoundness.CompactNamedSemantics
import PASoundness.PAtoCompactMultiplicationSound
import PASoundness.PAtoCompactTermSuccessorIdentity

/-! Standard-HF semantics for uniform named-IR renaming under an injective
name map. The `.bottom` constructor stays fixed; its literal encoding is code
1, and the existing `encode_realize` theorem supplies its HF interpretation.
There is no substitution or derivation claim for arbitrary K models. -/
namespace PASoundness.PAtoCompactTermRenamingSemantics

open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.CompactMatrix (Environment update)

/-- Updating an injectively renamed bound variable commutes with pulling the
assignment back. Equal *values* are permitted; only names are injective. -/
theorem update_comp (f : Nat → Nat) (inj : Function.Injective f)
    (ρ : Environment) (x v : Nat) :
    (update ρ (f x) v) ∘ f = update (ρ ∘ f) x v := by
  funext y
  by_cases h : y = x
  · subst y
    simp [update]
  · have hf : f y ≠ f x := fun he => h (inj he)
    simp [update, h, hf]

/-- Full explicit-name renaming preserves named semantics when the name map is
injective. It handles all quantifiers structurally and does not assume that
assigned objects are distinct. -/
theorem mapNames_realize (f : Nat → Nat) (inj : Function.Injective f)
    (a : Formula) (ρ : Environment) :
    (mapNames f a).Realize ρ ↔ a.Realize (ρ ∘ f) := by
  induction a generalizing ρ with
  | truth | bottom => rfl
  | member a b | equal a b => rfl
  | imp a b ia ib =>
    change ((mapNames f a).Realize ρ → (mapNames f b).Realize ρ) ↔
      (a.Realize (ρ ∘ f) → b.Realize (ρ ∘ f))
    exact imp_congr (ia ρ) (ib ρ)
  | all x a ih =>
    change (∀ v, (mapNames f a).Realize (update ρ (f x) v)) ↔
      ∀ v, a.Realize (update (ρ ∘ f) x v)
    apply forall_congr'
    intro v
    rw [ih, update_comp f inj ρ x v]
  | ex x a ih =>
    change (∃ v, (mapNames f a).Realize (update ρ (f x) v)) ↔
      ∃ v, a.Realize (update (ρ ∘ f) x v)
    apply exists_congr
    intro v
    rw [ih, update_comp f inj ρ x v]

/-- The numeric encoded formula has the same standard-HF truth value. This
uses `encode_realize`, in particular its established handling of code 1. -/
theorem mapNames_encode_realize (f : Nat → Nat) (inj : Function.Injective f)
    (a : Formula) (ρ : Environment) :
    (PASoundness.CompactMatrix.decode (mapNames f a).encode).Realize ρ ↔
      a.Realize (ρ ∘ f) := by
  rw [Formula.encode_realize]
  exact mapNames_realize f inj a ρ

/-- The concrete one-input map is injective when its operand label precedes
the private binder block. -/
theorem oneMap_injective (base p x : Nat) (hx : x < base + 2) :
    Function.Injective (oneMap base p x) := by
  intro i j hij
  simp only [oneMap] at hij
  split_ifs at hij <;> omega

/-- Syntactic operand labels for two separate placeholders must be distinct;
their denoted objects may still be equal. -/
theorem twoMap_injective (base p q x y : Nat) (_hpq : p ≠ q) (hxy : x ≠ y)
    (hx : x < base + 2) (hy : y < base + 2) :
    Function.Injective (twoMap base p q x y) := by
  intro i j hij
  simp only [twoMap] at hij
  split_ifs at hij <;> omega

/-- Analogous allocation criterion for three placeholders. -/
theorem threeMap_injective (base p q r x y z : Nat)
    (_hpq : p ≠ q) (_hpr : p ≠ r) (_hqr : q ≠ r)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : x < base + 2) (hy : y < base + 2) (hz : z < base + 2) :
    Function.Injective (threeMap base p q r x y z) := by
  intro i j hij
  simp only [threeMap] at hij
  split_ifs at hij <;> omega

/-- Exact standard-HF semantics of the concretely renamed candidate template. -/
theorem domainAt_realize (base x : Nat) (hx : x < base + 2) (ρ : Environment) :
    (domainAt base x).Realize ρ ↔ (domainTemplate 0).Realize (ρ ∘ oneMap base 0 x) :=
  mapNames_realize _ (oneMap_injective base 0 x hx) _ ρ

/-- Bottom normalization also preserves standard-HF truth. The proof uses
the exact encoding equality and the established literal-code truth theorem. -/
theorem normalizeBottom_realize (a : Formula) (ρ : Environment) :
    (normalizeBottom a).Realize ρ ↔ a.Realize ρ := by
  rw [← Formula.encode_realize, normalizeBottom_encode, Formula.encode_realize]

/-- The generated isomorphism instance has its established ordinal meaning,
provided the source and output names are distinct and below the local block. -/
theorem equivAt_ordinal (base x y n m : Nat) (hxy : x ≠ y)
    (hx : x < base + 2) (hy : y < base + 2) (ρ : Environment)
    (h0 : ρ x = (PASoundness.HFCoding.ordinal n).code)
    (h1 : ρ y = (PASoundness.HFCoding.ordinal m).code) :
    (equivAt base x y).Realize ρ ↔ n = m := by
  unfold equivAt
  rw [mapNames_realize _ (twoMap_injective base 0 1 x y (by decide) hxy hx hy),
    normalizeBottom_realize, ← Formula.encode_realize]
  apply PASoundness.PAtoCompactOrdinalEquivalence.standard_ordinal_iff
  · simpa [Function.comp_def, twoMap] using h0
  · simpa [Function.comp_def, twoMap] using h1

/-- The generated addition instance has exactly the arithmetic ordinal
meaning. This does not construct the corresponding K graph. -/
theorem addAt_ordinal (base x y z i j k : Nat)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : x < base + 2) (hy : y < base + 2) (hz : z < base + 2)
    (ρ : Environment)
    (h0 : ρ x = (PASoundness.HFCoding.ordinal i).code)
    (h1 : ρ y = (PASoundness.HFCoding.ordinal j).code)
    (h2 : ρ z = (PASoundness.HFCoding.ordinal k).code) :
    (addAt base x y z).Realize ρ ↔ k = i + j := by
  unfold addAt
  rw [mapNames_realize _ (threeMap_injective base 30 31 32 x y z
    (by decide) (by decide) (by decide) hxy hxz hyz hx hy hz),
    normalizeBottom_realize, ← Formula.encode_realize]
  apply PASoundness.PAtoCompactOrdinalAddition.standard_ordinal_addition_iff
  · simpa [Function.comp_def, threeMap] using h0
  · simpa [Function.comp_def, threeMap] using h1
  · simpa [Function.comp_def, threeMap] using h2

/-- The generated product instance has exactly the arithmetic ordinal
meaning, under the same syntactic-name conditions. -/
theorem mulAt_ordinal (base x y z i j k : Nat)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : x < base + 2) (hy : y < base + 2) (hz : z < base + 2)
    (ρ : Environment)
    (h0 : ρ x = (PASoundness.HFCoding.ordinal i).code)
    (h1 : ρ y = (PASoundness.HFCoding.ordinal j).code)
    (h2 : ρ z = (PASoundness.HFCoding.ordinal k).code) :
    (mulAt base x y z).Realize ρ ↔ k = i * j := by
  unfold mulAt
  rw [mapNames_realize _ (threeMap_injective base 0 1 2 x y z
    (by decide) (by decide) (by decide) hxy hxz hyz hx hy hz),
    normalizeBottom_realize, ← Formula.encode_realize]
  apply PASoundness.PAtoCompactMultiplicationSound.encoded_ordinal_product_iff
  · simpa [Function.comp_def, threeMap] using h0
  · simpa [Function.comp_def, threeMap] using h1
  · simpa [Function.comp_def, threeMap] using h2

/-- The generated zero instance recognizes the empty ordinal. -/
theorem zeroAt_iff (base x : Nat) (hx : x < base + 2) (ρ : Environment) :
    (zeroAt base x).Realize ρ ↔ ρ x = (PASoundness.HFCoding.ordinal 0).code := by
  unfold zeroAt
  rw [mapNames_realize _ (oneMap_injective base 0 x hx),
    ← Formula.encode_realize, zeroTemplate_encode]
  simpa [Function.comp_def, oneMap] using
    PASoundness.PAtoCompactZeroSuccessor.ordinal_zero_relation 0 1 (ρ ∘ oneMap base 0 x) (by decide)

/-- The generated quotient-successor relation has the calibrated arithmetic
meaning on ordinal inputs; this is a standard-HF statement. -/
theorem succAt_ordinal (base x y n m : Nat) (hxy : x ≠ y)
    (hx : x < base + 2) (hy : y < base + 2) (ρ : Environment)
    (h0 : ρ x = (PASoundness.HFCoding.ordinal n).code)
    (h1 : ρ y = (PASoundness.HFCoding.ordinal m).code) :
    (succAt base x y).Realize ρ ↔ m = n + 1 := by
  unfold succAt
  rw [mapNames_realize _ (twoMap_injective base 0 1 x y (by decide) hxy hx hy),
    ← Formula.encode_realize,
    PASoundness.PAtoCompactTermSuccessorIdentity.successorTemplate_encode]
  apply PASoundness.PAtoCompactQuotientSuccessor.standard_ordinal_successor_iff
  · simpa [Function.comp_def, twoMap] using h0
  · simpa [Function.comp_def, twoMap] using h1

/-- The generated candidate-domain guard contains every standard ordinal,
with its label separated from all allocated binder names. -/
theorem domainAt_ordinal (base x n : Nat) (hx : x < base + 2)
    (ρ : Environment) (h0 : ρ x = (PASoundness.HFCoding.ordinal n).code) :
    (domainAt base x).Realize ρ := by
  have hc : (domainAt base x).encode =
      PASoundness.PAtoCompactCandidateExact.candidateCode x
        (base+32) (base+33) (base+34) (base+35)
        (base+36) (base+37) (base+38) (base+39) := by rfl
  have hn : [x,base+32,base+33,base+34,base+35,base+36,base+37,base+38,base+39].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or, List.nodup_nil,
      not_false_eq_true, and_true]
    repeat' apply And.intro
    all_goals omega
  rw [← Formula.encode_realize, hc]
  exact (PASoundness.PAtoCompactCandidateStandard.candidate_standard_iff x
    (base+32) (base+33) (base+34) (base+35) (base+36) (base+37) (base+38) (base+39)
    ρ hn).mpr ⟨n,h0⟩

end PASoundness.PAtoCompactTermRenamingSemantics

#print axioms PASoundness.PAtoCompactTermRenamingSemantics.mapNames_encode_realize

#print axioms PASoundness.PAtoCompactTermRenamingSemantics.addAt_ordinal
#print axioms PASoundness.PAtoCompactTermRenamingSemantics.mulAt_ordinal

#print axioms PASoundness.PAtoCompactTermRenamingSemantics.succAt_ordinal
#print axioms PASoundness.PAtoCompactTermRenamingSemantics.domainAt_ordinal
