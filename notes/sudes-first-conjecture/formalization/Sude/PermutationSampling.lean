import Sude.PermutationCuts
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Finset.Powerset

/-! The exact without-replacement law for the image of a fixed set. -/
namespace Sude
noncomputable section

/-- Permutations mapping a fixed finite set to one specified image. -/
def permutationImageFiber {n : ℕ} (S T : Finset (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun p => S.image p = T)

/-- Fibers over sets of the same cardinality are equinumerous. The bijection
composes with a permutation carrying one image set to the other. -/
theorem permutationImageFiber_card_eq {n : ℕ} (S T U : Finset (Fin n))
    (h : T.card = U.card) :
    (permutationImageFiber S T).card = (permutationImageFiber S U).card := by
  classical
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq T U h
  have hforward : T.image σ = U := by simpa [Finset.map_eq_image] using hσ
  have hback : U.image σ.symm = T := by
    rw [← hforward, Finset.image_image]
    simp
  refine Finset.card_bij' (fun p _ => p.trans σ) (fun p _ => p.trans σ.symm) ?_ ?_ ?_ ?_
  · intro p hp
    have hp' : S.image p = T := (Finset.mem_filter.mp hp).2
    simp only [permutationImageFiber, Finset.mem_filter, Finset.mem_univ, true_and]
    change S.image (σ ∘ p) = U
    rw [← Finset.image_image, hp', hforward]
  · intro p hp
    have hp' : S.image p = U := (Finset.mem_filter.mp hp).2
    simp only [permutationImageFiber, Finset.mem_filter, Finset.mem_univ, true_and]
    change S.image (σ.symm ∘ p) = T
    rw [← Finset.image_image, hp', hback]
  · intro p hp
    ext x
    simp
  · intro p hp
    ext x
    simp

/-- The event that the image of `S` lies in a specified family of sets. -/
def permutationImageEvent {n : ℕ} (S : Finset (Fin n))
    (targets : Finset (Finset (Fin n))) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun p => S.image p ∈ targets)

/-- A uniformly sampled permutation sends `S` to each same-sized subset
with the same probability. The integer identity avoids division and also
covers the empty and full set. -/
theorem permutation_image_uniform {n : ℕ} (S : Finset (Fin n))
    (targets : Finset (Finset (Fin n)))
    (htargets : ∀ T ∈ targets, T.card = S.card) :
    Nat.choose n S.card * (permutationImageEvent S targets).card =
      n.factorial * targets.card := by
  classical
  let all : Finset (Finset (Fin n)) := (Finset.univ : Finset (Fin n)).powersetCard S.card
  let f : Equiv.Perm (Fin n) → Finset (Fin n) := fun p => S.image p
  let c := (permutationImageFiber S S).card
  have hfiber (T : Finset (Fin n)) (hT : T.card = S.card) :
      (permutationImageFiber S T).card = c := by
    exact permutationImageFiber_card_eq S T S hT
  have hall : (Finset.univ : Finset (Equiv.Perm (Fin n))).card = all.card * c := by
    have hmap : ∀ p ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))), f p ∈ all := by
      intro p hp
      simp [all, f, Finset.card_image_of_injective _ p.injective]
    rw [Finset.card_eq_sum_card_fiberwise hmap]
    calc
      _ = ∑ T ∈ all, c := by
        apply Finset.sum_congr rfl
        intro T hT
        have ht : T.card = S.card := (Finset.mem_powersetCard.mp hT).2
        exact hfiber T ht
      _ = all.card * c := by simp
  have hevent : (permutationImageEvent S targets).card = targets.card * c := by
    have hmap : ∀ p ∈ permutationImageEvent S targets, f p ∈ targets := by
      intro p hp
      exact (Finset.mem_filter.mp hp).2
    rw [Finset.card_eq_sum_card_fiberwise hmap]
    calc
      _ = ∑ T ∈ targets, c := by
        apply Finset.sum_congr rfl
        intro T hT
        have hset : (permutationImageEvent S targets).filter (fun p => f p = T) =
            permutationImageFiber S T := by
          ext p
          simp only [permutationImageEvent, permutationImageFiber, f, Finset.mem_filter,
            Finset.mem_univ, true_and]
          constructor
          · exact And.right
          · intro heq
            exact ⟨heq ▸ hT, heq⟩
        rw [hset]
        exact hfiber T (htargets T hT)
      _ = targets.card * c := by simp
  have hallcard : all.card = Nat.choose n S.card := by
    simp [all, Finset.card_powersetCard]
  have htotal : (Finset.univ : Finset (Equiv.Perm (Fin n))).card = n.factorial := by
    simp [Fintype.card_perm]
  rw [hallcard, htotal] at hall
  rw [hevent, hall]
  ring

/-- Candidate image sets with exactly `j` elements outside the original set. -/
def hypergeometricTargets {n : ℕ} (S : Finset (Fin n)) (j : ℕ) : Finset (Finset (Fin n)) :=
  ((S.powersetCard (S.card - j)).product (Sᶜ.powersetCard j)).image
    (fun z => z.1 ∪ z.2)

/-- The inside and outside parts determine the union uniquely. -/
theorem hypergeometricTargets_card {n : ℕ} (S : Finset (Fin n)) (j : ℕ) (hj : j ≤ S.card) :
    (hypergeometricTargets S j).card = Nat.choose S.card j * Nat.choose (n - S.card) j := by
  classical
  unfold hypergeometricTargets
  rw [Finset.card_image_of_injOn]
  · change ((S.powersetCard (S.card - j)) ×ˢ (Sᶜ.powersetCard j)).card = _
    rw [Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard,
      Finset.card_compl, Fintype.card_fin, Nat.choose_symm hj]
  · intro x hx y hy heq
    obtain ⟨hxa, hxb⟩ := Finset.mem_product.mp hx
    obtain ⟨hya, hyb⟩ := Finset.mem_product.mp hy
    have hxa' := (Finset.mem_powersetCard.mp hxa).1
    have hxb' := (Finset.mem_powersetCard.mp hxb).1
    have hya' := (Finset.mem_powersetCard.mp hya).1
    have hyb' := (Finset.mem_powersetCard.mp hyb).1
    change x.1 ∪ x.2 = y.1 ∪ y.2 at heq
    apply Prod.ext
    · have ha : (x.1 ∪ x.2) ∩ S = x.1 := by
        ext z
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨h | h, hz⟩
          · exact h
          · exact False.elim ((Finset.mem_compl.mp (hxb' h)) hz)
        · intro hz
          exact ⟨Or.inl hz, hxa' hz⟩
      have hb : (y.1 ∪ y.2) ∩ S = y.1 := by
        ext z
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨h | h, hz⟩
          · exact h
          · exact False.elim ((Finset.mem_compl.mp (hyb' h)) hz)
        · intro hz
          exact ⟨Or.inl hz, hya' hz⟩
      rw [← ha, ← hb, heq]
    · have ha : (x.1 ∪ x.2) \ S = x.2 := by
        ext z
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨h | h, hz⟩
          · exact False.elim (hz (hxa' h))
          · exact h
        · intro hz
          exact ⟨Or.inr hz, Finset.mem_compl.mp (hxb' hz)⟩
      have hb : (y.1 ∪ y.2) \ S = y.2 := by
        ext z
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨h | h, hz⟩
          · exact False.elim (hz (hya' h))
          · exact h
        · intro hz
          exact ⟨Or.inr hz, Finset.mem_compl.mp (hyb' hz)⟩
      rw [← ha, ← hb, heq]

/-- The two-part representation describes exactly the image sets with the
specified number of elements outside `S`. -/
theorem mem_hypergeometricTargets_iff {n : ℕ} (S T : Finset (Fin n)) (j : ℕ)
    (hj : j ≤ S.card) :
    T ∈ hypergeometricTargets S j ↔ T.card = S.card ∧ (T \ S).card = j := by
  classical
  unfold hypergeometricTargets
  change T ∈ (((S.powersetCard (S.card - j)) ×ˢ (Sᶜ.powersetCard j)).image
    (fun z => z.1 ∪ z.2)) ↔ _
  simp only [Finset.mem_image, Finset.mem_product, Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨A, B⟩, ⟨⟨hAS, hAc⟩, ⟨hBS, hBc⟩⟩, rfl⟩
    have hd : Disjoint A B := by
      apply Finset.disjoint_left.mpr
      intro x hxA hxB
      exact (Finset.mem_compl.mp (hBS hxB)) (hAS hxA)
    have hs : (A ∪ B) \ S = B := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨h | h, hn⟩
        · exact False.elim (hn (hAS h))
        · exact h
      · intro hb
        exact ⟨Or.inr hb, Finset.mem_compl.mp (hBS hb)⟩
    constructor
    · rw [Finset.card_union_of_disjoint hd, hAc, hBc]
      omega
    · rw [hs, hBc]
  · rintro ⟨hcard, hdiff⟩
    refine ⟨(T ∩ S, T \ S), ⟨⟨Finset.inter_subset_right, ?_⟩, ⟨?_, hdiff⟩⟩, ?_⟩
    · change (T ∩ S).card = S.card - j
      have hpart := Finset.card_sdiff_add_card_inter T S
      omega
    · intro x hx
      exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hx).2
    · rw [Finset.union_comm, Finset.sdiff_union_inter]

/-- Exact hypergeometric counting law for outgoing edges of a uniform
permutation. The identity contains no independence approximation. -/
theorem permutation_outgoing_hypergeometric {n : ℕ} (S : Finset (Fin n))
    (j : ℕ) (hj : j ≤ S.card) :
    Nat.choose n S.card *
        ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
          (fun p => (permutationOutgoing p S).card = j)).card =
      n.factorial * (Nat.choose S.card j * Nat.choose (n - S.card) j) := by
  classical
  have htarget : ∀ T ∈ hypergeometricTargets S j, T.card = S.card := by
    intro T hT
    exact ((mem_hypergeometricTargets_iff S T j hj).mp hT).1
  have hevent : permutationImageEvent S (hypergeometricTargets S j) =
      (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
        (fun p => (permutationOutgoing p S).card = j) := by
    ext p
    simp only [permutationImageEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [mem_hypergeometricTargets_iff S (S.image p) j hj]
    have hc : (S.image p).card = S.card := Finset.card_image_of_injective S p.injective
    have ho : (S.image p \ S).card = (permutationOutgoing p S).card := by
      rw [← permutationOutgoing_image, Finset.card_image_of_injective _ p.injective]
    simp [hc, ho]
  have h := permutation_image_uniform S (hypergeometricTargets S j) htarget
  rw [hevent, hypergeometricTargets_card S j hj] at h
  exact h

end
end Sude
