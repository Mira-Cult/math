import PASoundness.HFCoding

/-! Standard-HF ordinal rigidity for an explicit binary relation on codes.
This is a semantic finite-cardinality fact, not a K proof of graph existence,
a quotient interpretation, or a proof translation. -/
namespace PASoundness.PAtoCompactOrdinalBijection
open PASoundness.CompactMatrix PASoundness.HFCoding

/-- Any relation that gives each member of ordinal n a unique member of
ordinal m, and conversely, forces n=m. Here the relation may be arbitrary;
no order-preservation hypothesis is needed. -/
theorem ordinal_bijection_cardinality (n m : Nat) (R : Nat → Nat → Prop)
    (forward : ∀ a, bit (ordinal n).code a = true →
      ∃ b, bit (ordinal m).code b = true ∧ R a b ∧
        ∀ b', bit (ordinal m).code b' = true → R a b' → b' = b)
    (reverse : ∀ b, bit (ordinal m).code b = true →
      ∃ a, bit (ordinal n).code a = true ∧ R a b ∧
        ∀ a', bit (ordinal n).code a' = true → R a' b → a' = a) :
    n = m := by
  classical
  have forwardFin : ∀ i : Fin n, ∃ j : Fin m, R (ordinal i.val).code (ordinal j.val).code := by
    intro i
    have hi : bit (ordinal n).code (ordinal i.val).code = true := ordinal_member i.isLt
    obtain ⟨b,hb,hr,_⟩ := forward _ hi
    have hb' : (⟨b⟩ : Object) ∈ ordinal m := hb
    obtain ⟨j,hj,hbj⟩ := (mem_ordinal _ _).mp hb'
    have hbcode : b = (ordinal j).code := congrArg Object.code hbj
    refine ⟨⟨j,hj⟩, ?_⟩
    simpa [hbcode] using hr
  choose f hf using forwardFin
  have hinj : Function.Injective f := by
    intro i j h
    have hj : bit (ordinal m).code (ordinal (f i).val).code = true := ordinal_member (f i).isLt
    obtain ⟨a,ha,har,uniq⟩ := reverse _ hj
    have hi' : bit (ordinal n).code (ordinal i.val).code = true := ordinal_member i.isLt
    have hj' : bit (ordinal n).code (ordinal j.val).code = true := ordinal_member j.isLt
    have hiEq := uniq _ hi' (hf i)
    have hjR : R (ordinal j.val).code (ordinal (f i).val).code := by simpa [h] using hf j
    have hjEq := uniq _ hj' hjR
    have hcode : (ordinal i.val).code = (ordinal j.val).code := hiEq.trans hjEq.symm
    exact Fin.ext (ordinal_code_strictMono.injective hcode)
  have hsurj : Function.Surjective f := by
    intro j
    have hj : bit (ordinal m).code (ordinal j.val).code = true := ordinal_member j.isLt
    obtain ⟨a,ha,har,uniq⟩ := reverse _ hj
    have ha' : (⟨a⟩ : Object) ∈ ordinal n := ha
    obtain ⟨i,hi,hai⟩ := (mem_ordinal _ _).mp ha'
    have hacode : a = (ordinal i).code := congrArg Object.code hai
    let ii : Fin n := ⟨i,hi⟩
    have hiR : R (ordinal i).code (ordinal j.val).code := by simpa [hacode] using har
    have hii : bit (ordinal n).code (ordinal i).code = true := ordinal_member hi
    obtain ⟨b,hb,hbr,hu⟩ := forward _ hii
    have hjEq := hu _ hj hiR
    have hfi : bit (ordinal m).code (ordinal (f ii).val).code = true := ordinal_member (f ii).isLt
    have hfiEq := hu _ hfi (hf ii)
    have hcode : (ordinal (f ii).val).code = (ordinal j.val).code := hfiEq.trans hjEq.symm
    exact ⟨ii, Fin.ext (ordinal_code_strictMono.injective hcode)⟩
  have hc := Fintype.card_congr (Equiv.ofBijective f ⟨hinj,hsurj⟩)
  simpa using hc

end PASoundness.PAtoCompactOrdinalBijection

#print axioms PASoundness.PAtoCompactOrdinalBijection.ordinal_bijection_cardinality
