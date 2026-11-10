import PASoundness.HFCoding
import Mathlib.Data.Fintype.Prod

/-! A standard-HF cardinality consequence of a supplied ternary relation.
This is a semantic result, not a K proof of product or graph existence, a
quotient interpretation, or an arithmetic proof translation. -/
namespace PASoundness.PAtoCompactProductCardinality
open PASoundness.CompactMatrix PASoundness.HFCoding

/-- A relation that gives every ordered pair of members of ordinal `m` and
ordinal `n` a unique member of ordinal `k`, and every member of ordinal `k`
a unique such ordered pair, forces `k = m*n`. The relation is arbitrary:
neither its representation by a K graph nor preservation of any order is
assumed or established. -/
theorem ordinal_product_bijection_cardinality (m n k : Nat)
    (R : Nat → Nat → Nat → Prop)
    (forward : ∀ a, bit (ordinal m).code a = true →
      ∀ b, bit (ordinal n).code b = true →
      ∃ c, bit (ordinal k).code c = true ∧ R a b c ∧
        ∀ c', bit (ordinal k).code c' = true → R a b c' → c' = c)
    (reverse : ∀ c, bit (ordinal k).code c = true →
      ∃ a, bit (ordinal m).code a = true ∧
      ∃ b, bit (ordinal n).code b = true ∧ R a b c ∧
        ∀ a', bit (ordinal m).code a' = true →
        ∀ b', bit (ordinal n).code b' = true → R a' b' c → a' = a ∧ b' = b) :
    k = m * n := by
  classical
  have forwardFin : ∀ ij : Fin m × Fin n, ∃ c : Fin k,
      R (ordinal ij.1.val).code (ordinal ij.2.val).code (ordinal c.val).code := by
    intro ij
    have hi : bit (ordinal m).code (ordinal ij.1.val).code = true := ordinal_member ij.1.isLt
    have hj : bit (ordinal n).code (ordinal ij.2.val).code = true := ordinal_member ij.2.isLt
    obtain ⟨c, hc, hr, _⟩ := forward _ hi _ hj
    have hc' : (⟨c⟩ : Object) ∈ ordinal k := hc
    obtain ⟨l, hl, hcl⟩ := (mem_ordinal _ _).mp hc'
    have hcode : c = (ordinal l).code := congrArg Object.code hcl
    exact ⟨⟨l, hl⟩, by simpa [hcode] using hr⟩
  choose f hf using forwardFin
  have hinj : Function.Injective f := by
    intro ij uv h
    have hc : bit (ordinal k).code (ordinal (f ij).val).code = true := ordinal_member (f ij).isLt
    obtain ⟨a, ha, b, hb, hr, uniq⟩ := reverse _ hc
    have hi : bit (ordinal m).code (ordinal ij.1.val).code = true := ordinal_member ij.1.isLt
    have hj : bit (ordinal n).code (ordinal ij.2.val).code = true := ordinal_member ij.2.isLt
    have hu : bit (ordinal m).code (ordinal uv.1.val).code = true := ordinal_member uv.1.isLt
    have hv : bit (ordinal n).code (ordinal uv.2.val).code = true := ordinal_member uv.2.isLt
    have h₁ := uniq _ hi _ hj (hf ij)
    have hrel : R (ordinal uv.1.val).code (ordinal uv.2.val).code
        (ordinal (f ij).val).code := by simpa [h] using hf uv
    have h₂ := uniq _ hu _ hv hrel
    apply Prod.ext
    · exact Fin.ext (ordinal_code_strictMono.injective (h₁.1.trans h₂.1.symm))
    · exact Fin.ext (ordinal_code_strictMono.injective (h₁.2.trans h₂.2.symm))
  have hsurj : Function.Surjective f := by
    intro c
    have hc : bit (ordinal k).code (ordinal c.val).code = true := ordinal_member c.isLt
    obtain ⟨a, ha, b, hb, hr, _⟩ := reverse _ hc
    have ha' : (⟨a⟩ : Object) ∈ ordinal m := ha
    have hb' : (⟨b⟩ : Object) ∈ ordinal n := hb
    obtain ⟨i, hi, hai⟩ := (mem_ordinal _ _).mp ha'
    obtain ⟨j, hj, hbj⟩ := (mem_ordinal _ _).mp hb'
    have hacode : a = (ordinal i).code := congrArg Object.code hai
    have hbcode : b = (ordinal j).code := congrArg Object.code hbj
    let ij : Fin m × Fin n := (⟨i, hi⟩, ⟨j, hj⟩)
    have hrel : R (ordinal i).code (ordinal j).code (ordinal c.val).code := by
      simpa [hacode, hbcode] using hr
    have hi' : bit (ordinal m).code (ordinal i).code = true := ordinal_member hi
    have hj' : bit (ordinal n).code (ordinal j).code = true := ordinal_member hj
    obtain ⟨d, hd, hdr, uniq⟩ := forward _ hi' _ hj'
    have hcEq := uniq _ hc hrel
    have hfi : bit (ordinal k).code (ordinal (f ij).val).code = true := ordinal_member (f ij).isLt
    have hfEq := uniq _ hfi (hf ij)
    exact ⟨ij, Fin.ext (ordinal_code_strictMono.injective (hfEq.trans hcEq.symm))⟩
  have hc := Fintype.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  simpa using hc.symm

end PASoundness.PAtoCompactProductCardinality

#print axioms PASoundness.PAtoCompactProductCardinality.ordinal_product_bijection_cardinality
