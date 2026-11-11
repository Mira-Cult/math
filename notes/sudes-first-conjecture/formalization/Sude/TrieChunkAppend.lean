import Sude.FiniteDistinctChunks

/-! Extend already verified checkpoints without re-assuming earlier stages. -/
namespace Sude

theorem VerifiedTrieChunks.append {depth : ℕ} {t u v : DistinctTrie}
    {first second : List (List ℕ)}
    (hfirst : VerifiedTrieChunks depth t first u)
    (hsecond : VerifiedTrieChunks depth u second v) :
    VerifiedTrieChunks depth t (first ++ second) v := by
  induction hfirst with
  | nil => simpa using hsecond
  | @cons t u w xs rest hstep htail ih =>
    simpa only [List.cons_append] using VerifiedTrieChunks.cons hstep (ih hsecond)

/-- A no-duplicate concatenation of two explicit finite enumerations proves
both within-family injectivity and cross-family separation. -/
theorem sumFamily_injective_of_nodup {m n : ℕ} {α β : Type*}
    (ea : Fin m ≃ α) (eb : Fin n ≃ β) (f : α → ℕ) (g : β → ℕ)
    (h : (List.ofFn (f ∘ ea) ++ List.ofFn (g ∘ eb)).Nodup) :
    Function.Injective (Sum.elim f g) := by
  obtain ⟨ha, hb, hcross⟩ := List.nodup_append.mp h
  rw [List.ofFn_eq_map] at ha hb
  have hia := (List.nodup_map_iff_inj_on (List.nodup_finRange m)).mp ha
  have hib := (List.nodup_map_iff_inj_on (List.nodup_finRange n)).mp hb
  have hfa : Function.Injective f := by
    apply (ea.injective_comp f).mp
    intro x y heq
    exact hia x (List.mem_finRange x) y (List.mem_finRange y) heq
  have hfb : Function.Injective g := by
    apply (eb.injective_comp g).mp
    intro x y heq
    exact hib x (List.mem_finRange x) y (List.mem_finRange y) heq
  intro x y heq
  cases x with
  | inl x =>
    cases y with
    | inl y => exact congrArg Sum.inl (hfa heq)
    | inr y =>
      exfalso
      apply hcross (f x) ?_ (g y) ?_ heq
      · exact List.mem_ofFn.mpr ⟨ea.symm x, by simp⟩
      · exact List.mem_ofFn.mpr ⟨eb.symm y, by simp⟩
  | inr x =>
    cases y with
    | inl y =>
      exfalso
      apply hcross (f y) ?_ (g x) ?_ heq.symm
      · exact List.mem_ofFn.mpr ⟨ea.symm y, by simp⟩
      · exact List.mem_ofFn.mpr ⟨eb.symm x, by simp⟩
    | inr y => exact congrArg Sum.inr (hfb heq)

end Sude
