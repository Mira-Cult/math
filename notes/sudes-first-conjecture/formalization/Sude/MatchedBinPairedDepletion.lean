import Sude.BMORPhysicalMatchedPreserved

/-!
# Paired-Bin Depletion for Matched-Bin Double-Block Selection

Each `DoublePair` satisfying `DoublePair.MatchedValid low high` draws one `(low i, high i)`
pair and one `(low j, high j)` pair from pairwise-disjoint `(low, high)` bins. Consequently,
for every bin `m : Fin N`, a selected block removes the **exact same number** of elements from
`low m` and `high m` (`0`, `1`, or `2`), and the sum across `m` of `(low m ∩ b.footprint).card`
is at most `2`.

Iterating across `k` blocks therefore reduces `∑ m, min (low m).card (high m).card` by at most
`other.card + 2 * k` rather than `other.card + 4 * k`.
-/

namespace Sude

noncomputable section

open scoped BigOperators

set_option autoImplicit false

/-- In pairwise-disjoint `(low, high)` bins, any `MatchedValid` double-pair block hits
`low m` and `high m` in equal cardinalities for every `m`, with total `low`-hits at most `2`. -/
theorem matched_valid_block_equal_bin_hits {N : ℕ}
    (low high : Fin N → Finset ℕ) (b : DoublePair)
    (hdis : (Set.univ : Set (Fin N × Bool)).PairwiseDisjoint
      (fun z => if z.2 then high z.1 else low z.1))
    (hmatched : b.MatchedValid low high) :
    (∀ m : Fin N, (low m ∩ b.footprint).card = (high m ∩ b.footprint).card) ∧
      (∑ m : Fin N, (low m ∩ b.footprint).card) ≤ 2 := by
  classical
  rcases hmatched with ⟨hval, ⟨i, hli, hhi⟩, ⟨j, hlj, hhj⟩⟩
  have hlowne : b.low₁ ≠ b.low₂ := hval.2.2.2.2.1
  have hhighne : b.high₁ ≠ b.high₂ := hval.2.2.2.2.2.1
  have hdis_lh : ∀ m p : Fin N, Disjoint (low m) (high p) := by
    intro m p
    exact hdis (Set.mem_univ (m, false)) (Set.mem_univ (p, true)) (by simp)
  have hdis_ll : ∀ m p : Fin N, m ≠ p → Disjoint (low m) (low p) := by
    intro m p hne
    exact hdis (Set.mem_univ (m, false)) (Set.mem_univ (p, false)) (by simpa using hne)
  have hdis_hh : ∀ m p : Fin N, m ≠ p → Disjoint (high m) (high p) := by
    intro m p hne
    exact hdis (Set.mem_univ (m, true)) (Set.mem_univ (p, true)) (by simpa using hne)
  have hlow_eq : ∀ m : Fin N,
      low m ∩ b.footprint =
        (if m = i then {b.low₁} else ∅) ∪ (if m = j then {b.low₂} else ∅) := by
    intro m
    ext x
    simp only [DoublePair.footprint, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_union]
    constructor
    · rintro ⟨hxm, rfl | rfl | rfl | rfl⟩
      · have hmi : m = i := by
          by_contra hne
          exact Finset.disjoint_left.mp (hdis_ll m i hne) hxm hli
        left; simp [hmi]
      · have hmj : m = j := by
          by_contra hne
          exact Finset.disjoint_left.mp (hdis_ll m j hne) hxm hlj
        right; simp [hmj]
      · exact False.elim (Finset.disjoint_left.mp (hdis_lh m i) hxm hhi)
      · exact False.elim (Finset.disjoint_left.mp (hdis_lh m j) hxm hhj)
    · rintro (hx | hx)
      · split_ifs at hx with hmi
        · subst hmi
          have hx' : x = b.low₁ := Finset.mem_singleton.mp hx
          subst hx'
          exact ⟨hli, Or.inl rfl⟩
        · simp at hx
      · split_ifs at hx with hmj
        · subst hmj
          have hx' : x = b.low₂ := Finset.mem_singleton.mp hx
          subst hx'
          exact ⟨hlj, Or.inr (Or.inl rfl)⟩
        · simp at hx
  have hhigh_eq : ∀ m : Fin N,
      high m ∩ b.footprint =
        (if m = i then {b.high₁} else ∅) ∪ (if m = j then {b.high₂} else ∅) := by
    intro m
    ext x
    simp only [DoublePair.footprint, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_union]
    constructor
    · rintro ⟨hxm, rfl | rfl | rfl | rfl⟩
      · exact False.elim (Finset.disjoint_left.mp (hdis_lh i m) hli hxm)
      · exact False.elim (Finset.disjoint_left.mp (hdis_lh j m) hlj hxm)
      · have hmi : m = i := by
          by_contra hne
          exact Finset.disjoint_left.mp (hdis_hh m i hne) hxm hhi
        left; simp [hmi]
      · have hmj : m = j := by
          by_contra hne
          exact Finset.disjoint_left.mp (hdis_hh m j hne) hxm hhj
        right; simp [hmj]
    · rintro (hx | hx)
      · split_ifs at hx with hmi
        · subst hmi
          have hx' : x = b.high₁ := Finset.mem_singleton.mp hx
          subst hx'
          exact ⟨hhi, Or.inr (Or.inr (Or.inl rfl))⟩
        · simp at hx
      · split_ifs at hx with hmj
        · subst hmj
          have hx' : x = b.high₂ := Finset.mem_singleton.mp hx
          subst hx'
          exact ⟨hhj, Or.inr (Or.inr (Or.inr rfl))⟩
        · simp at hx
  refine ⟨?_, ?_⟩
  · intro m
    rw [hlow_eq m, hhigh_eq m]
    split_ifs with hmi hmj hmj
    · simp [Finset.card_pair hlowne, Finset.card_pair hhighne]
    · simp
    · simp
    · simp
  · have hsub_low : ∀ m : Fin N, low m ∩ b.footprint ⊆ ({b.low₁, b.low₂} : Finset ℕ) := by
      intro m x hx
      rw [hlow_eq m] at hx
      rcases Finset.mem_union.mp hx with hx1 | hx2
      · split_ifs at hx1 with hmi
        · exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hx1))
        · simp at hx1
      · split_ifs at hx2 with hmj
        · exact Finset.mem_insert.mpr (Or.inr hx2)
        · simp at hx2
    have hdis_inter :
        (↑(Finset.univ : Finset (Fin N)) : Set (Fin N)).PairwiseDisjoint
          (fun m => low m ∩ b.footprint) := by
      intro m _ p _ hne
      exact (hdis_ll m p hne).mono Finset.inter_subset_left Finset.inter_subset_left
    have hbiSub :
        (Finset.univ : Finset (Fin N)).biUnion (fun m => low m ∩ b.footprint) ⊆
          ({b.low₁, b.low₂} : Finset ℕ) := by
      intro x hx
      obtain ⟨m, _, hxm⟩ := Finset.mem_biUnion.mp hx
      exact hsub_low m hxm
    calc
      (∑ m : Fin N, (low m ∩ b.footprint).card)
          = ((Finset.univ : Finset (Fin N)).biUnion (fun m => low m ∩ b.footprint)).card := by
            rw [Finset.card_biUnion hdis_inter]
      _ ≤ ({b.low₁, b.low₂} : Finset ℕ).card := Finset.card_le_card hbiSub
      _ ≤ 2 := Finset.card_le_two

/-- Depletion accounting when `paired` hits `low m` and `high m` equally in every bin `m`
and `other` is paid once globally across all disjoint bins. -/
theorem matched_bin_stock_after_paired_and_other {N W : ℕ}
    (low high : Fin N → Finset ℕ) (other paired : Finset ℕ)
    (hdis : (Set.univ : Set (Fin N × Bool)).PairwiseDisjoint
      (fun k => if k.2 then high k.1 else low k.1))
    (hlow : ∀ i, W ≤ (low i).card) (hhigh : ∀ i, W ≤ (high i).card)
    (hpaired : ∀ i, (low i ∩ paired).card = (high i ∩ paired).card) :
    N * W ≤
      (∑ i, min ((low i \ (other ∪ paired)).card) ((high i \ (other ∪ paired)).card)) +
        (∑ i, (low i ∩ paired).card) + other.card := by
  classical
  let stock : Fin N × Bool → Finset ℕ := fun k => if k.2 then high k.1 else low k.1
  have hinterdis : (↑(Finset.univ : Finset (Fin N × Bool)) : Set (Fin N × Bool)).PairwiseDisjoint
      (fun k => stock k ∩ other) := by
    intro x _ y _ hxy
    apply Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left
    exact hdis (by simp) (by simp) hxy
  let deleted := (Finset.univ : Finset (Fin N × Bool)).biUnion (fun k => stock k ∩ other)
  have hdsub : deleted ⊆ other := by
    intro x hx
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_inter.mp hk).2
  have hdel : (∑ i, ((low i ∩ other).card + (high i ∩ other).card)) ≤ other.card := by
    have h := Finset.card_le_card hdsub
    have hcard : deleted.card = ∑ k : Fin N × Bool, (stock k ∩ other).card := by
      simp [deleted, Finset.card_biUnion hinterdis]
    rw [hcard, Fintype.sum_prod_type] at h
    simpa [stock, Fintype.sum_bool, add_comm] using h
  have hper : ∀ i, W ≤
      min ((low i \ (other ∪ paired)).card) ((high i \ (other ∪ paired)).card) +
        (low i ∩ paired).card + ((low i ∩ other).card + (high i ∩ other).card) := by
    intro i
    have hl := Finset.card_sdiff_add_card_inter (low i) (other ∪ paired)
    have hh := Finset.card_sdiff_add_card_inter (high i) (other ∪ paired)
    have hlu : (low i ∩ (other ∪ paired)).card ≤ (low i ∩ other).card + (low i ∩ paired).card := by
      rw [Finset.inter_union_distrib_left]
      exact Finset.card_union_le _ _
    have hhu : (high i ∩ (other ∪ paired)).card ≤ (high i ∩ other).card + (high i ∩ paired).card := by
      rw [Finset.inter_union_distrib_left]
      exact Finset.card_union_le _ _
    have hp := hpaired i
    have hli := hlow i
    have hhi := hhigh i
    omega
  calc
    N * W = ∑ _i : Fin N, W := by simp
    _ ≤ ∑ i : Fin N,
          (min ((low i \ (other ∪ paired)).card) ((high i \ (other ∪ paired)).card) +
            (low i ∩ paired).card + ((low i ∩ other).card + (high i ∩ other).card)) :=
        Finset.sum_le_sum (fun i _ => hper i)
    _ = (∑ i, min ((low i \ (other ∪ paired)).card) ((high i \ (other ∪ paired)).card)) +
          (∑ i, (low i ∩ paired).card) +
          ∑ i, ((low i ∩ other).card + (high i ∩ other).card) := by
        simp only [Finset.sum_add_distrib, add_assoc]
    _ ≤ (∑ i, min ((low i \ (other ∪ paired)).card) ((high i \ (other ∪ paired)).card)) +
          (∑ i, (low i ∩ paired).card) + other.card := by
        omega

/-- Repeated-gap step under paired-plus-other depletion. -/
theorem matched_bins_repeated_after_paired_and_other {N W B X : ℕ}
    (low high : Fin N → Finset ℕ) (other paired differences : Finset ℕ)
    (hdis : (Set.univ : Set (Fin N × Bool)).PairwiseDisjoint
      (fun k => if k.2 then high k.1 else low k.1))
    (hlow : ∀ i, W ≤ (low i).card) (hhigh : ∀ i, W ≤ (high i).card)
    (horder : ∀ i j a, a ∈ low i → ∀ b, b ∈ high j → a < b)
    (hdiff : ∀ i a, a ∈ low i → ∀ b, b ∈ high i → b - a ∈ differences)
    (hspan : differences.card ≤ X)
    (hpaired : ∀ i, (low i ∩ paired).card = (high i ∩ paired).card)
    (hbudget : other.card + (∑ i, (low i ∩ paired).card) ≤ B)
    (hgate : (N : ℝ) * X < ((N * W - B : ℕ) : ℝ) ^ 2) :
    ∃ b : DoublePair,
      b.MatchedValid low high ∧ Disjoint b.footprint (other ∪ paired) := by
  classical
  have hstock := matched_bin_stock_after_paired_and_other low high other paired hdis hlow hhigh hpaired
  have hnat : N * W - B ≤
      ∑ i, min ((low i \ (other ∪ paired)).card) ((high i \ (other ∪ paired)).card) := by
    omega
  have hsubR : ((N * W - B : ℕ) : ℝ) ≤
      ((∑ i, min ((low i \ (other ∪ paired)).card) ((high i \ (other ∪ paired)).card) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hnon : 0 ≤ ((N * W - B : ℕ) : ℝ) := by positivity
  have hsquare : ((N * W - B : ℕ) : ℝ) ^ 2 ≤
      ((∑ i, min ((low i \ (other ∪ paired)).card) ((high i \ (other ∪ paired)).card) : ℕ) : ℝ) ^ 2 := by
    nlinarith
  have hspanR : (differences.card : ℝ) ≤ X := by exact_mod_cast hspan
  have hN : 0 ≤ (N : ℝ) := by positivity
  have hgate' : (N : ℝ) * differences.card <
      ((∑ i, min ((low i \ (other ∪ paired)).card) ((high i \ (other ∪ paired)).card) : ℕ) : ℝ) ^ 2 :=
    (mul_le_mul_of_nonneg_left hspanR hN).trans_lt (hgate.trans_le hsquare)
  obtain ⟨block, ⟨i, hli, hhi⟩, ⟨j, hlj, hhj⟩,
    hlowne, hhighne, ho₁, ho₂, _, _, hgap⟩ :=
    matched_bins_repeated_difference
      (fun m => low m \ (other ∪ paired))
      (fun m => high m \ (other ∪ paired))
      differences
      (by
        intro m p hne
        apply Disjoint.mono Finset.sdiff_subset Finset.sdiff_subset
        exact hdis (Set.mem_univ (m, false)) (Set.mem_univ (p, false)) (by simpa using hne))
      (fun m p a ha b hb => horder m p a (Finset.mem_sdiff.mp ha).1 b (Finset.mem_sdiff.mp hb).1)
      (fun m a ha b hb => hdiff m a (Finset.mem_sdiff.mp ha).1 b (Finset.mem_sdiff.mp hb).1)
      hgate'
  have hli' := Finset.mem_sdiff.mp hli
  have hhi' := Finset.mem_sdiff.mp hhi
  have hlj' := Finset.mem_sdiff.mp hlj
  have hhj' := Finset.mem_sdiff.mp hhj
  have hv : block.valid (Finset.univ.biUnion low) (Finset.univ.biUnion high) := by
    refine ⟨?_, ?_, ?_, ?_, hlowne, hhighne, ho₁, ho₂, hgap⟩
    · exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hli'.1⟩
    · exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hlj'.1⟩
    · exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hhi'.1⟩
    · exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hhj'.1⟩
  have havoid : Disjoint block.footprint (other ∪ paired) := by
    apply Finset.disjoint_left.mpr
    intro x hx hxr
    simp only [DoublePair.footprint, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hli'.2 hxr
    · exact hlj'.2 hxr
    · exact hhi'.2 hxr
    · exact hhj'.2 hxr
  exact ⟨block, ⟨hv, ⟨i, hli'.1, hhi'.1⟩, ⟨j, hlj'.1, hhj'.1⟩⟩, havoid⟩

/-- Select `k` mutually disjoint `MatchedValid` blocks paying only `2 * k` (not `4 * k`)
in the matched-bin depletion budget `B`. -/
theorem select_matched_bin_double_pairs_paired_budget {N W B X k : ℕ}
    (low high : Fin N → Finset ℕ) (removed differences : Finset ℕ)
    (hdis : (Set.univ : Set (Fin N × Bool)).PairwiseDisjoint
      (fun z => if z.2 then high z.1 else low z.1))
    (hlow : ∀ i, W ≤ (low i).card) (hhigh : ∀ i, W ≤ (high i).card)
    (horder : ∀ i j a, a ∈ low i → ∀ b, b ∈ high j → a < b)
    (hdiff : ∀ i a, a ∈ low i → ∀ b, b ∈ high i → b - a ∈ differences)
    (hspan : differences.card ≤ X)
    (hgate : (N : ℝ) * X < ((N * W - B : ℕ) : ℝ) ^ 2)
    (hbudget : removed.card + 2 * k ≤ B) :
    ∃ blocks : List DoublePair, blocks.length = k ∧
      (∀ b ∈ blocks, b.MatchedValid low high) ∧
      blocks.Pairwise (fun b c => Disjoint b.footprint c.footprint) ∧
      (∀ b ∈ blocks, Disjoint b.footprint removed) := by
  classical
  suffices haux :
      ∀ (m : ℕ) (paired : Finset ℕ),
        (∀ i, (low i ∩ paired).card = (high i ∩ paired).card) →
        removed.card + (∑ i, (low i ∩ paired).card) + 2 * m ≤ B →
        ∃ blocks : List DoublePair, blocks.length = m ∧
          (∀ b ∈ blocks, b.MatchedValid low high) ∧
          blocks.Pairwise (fun b c => Disjoint b.footprint c.footprint) ∧
          (∀ b ∈ blocks, Disjoint b.footprint (removed ∪ paired)) by
    obtain ⟨blocks, hlen, hvalid, hpair, havoid⟩ := haux k ∅ (by simp) (by simpa using hbudget)
    refine ⟨blocks, hlen, hvalid, hpair, ?_⟩
    intro b hb
    simpa using havoid b hb
  intro m
  induction m with
  | zero =>
    intro paired _ _
    exact ⟨[], rfl, by simp, by simp, by simp⟩
  | succ m ih =>
    intro paired hpaired hbud
    obtain ⟨b, hbValid, hbDisj⟩ :=
      matched_bins_repeated_after_paired_and_other low high removed paired differences
        hdis hlow hhigh horder hdiff hspan hpaired (by omega) hgate
    have hbHits := matched_valid_block_equal_bin_hits low high b hdis hbValid
    have hdis_bp : Disjoint paired b.footprint :=
      (Disjoint.mono_right (Finset.subset_union_right : paired ⊆ removed ∪ paired) hbDisj).symm
    let nextPaired := paired ∪ b.footprint
    have hnext_eq : ∀ i, (low i ∩ nextPaired).card = (high i ∩ nextPaired).card := by
      intro i
      have hdl : Disjoint (low i ∩ paired) (low i ∩ b.footprint) :=
        hdis_bp.mono Finset.inter_subset_right Finset.inter_subset_right
      have hdh : Disjoint (high i ∩ paired) (high i ∩ b.footprint) :=
        hdis_bp.mono Finset.inter_subset_right Finset.inter_subset_right
      calc
        (low i ∩ nextPaired).card
            = ((low i ∩ paired) ∪ (low i ∩ b.footprint)).card := by
                rw [Finset.inter_union_distrib_left]
        _ = (low i ∩ paired).card + (low i ∩ b.footprint).card :=
              Finset.card_union_of_disjoint hdl
        _ = (high i ∩ paired).card + (high i ∩ b.footprint).card := by
              rw [hpaired i, hbHits.1 i]
        _ = ((high i ∩ paired) ∪ (high i ∩ b.footprint)).card :=
              (Finset.card_union_of_disjoint hdh).symm
        _ = (high i ∩ nextPaired).card := by
              rw [← Finset.inter_union_distrib_left]
    have hnext_sum :
        (∑ i, (low i ∩ nextPaired).card) ≤ (∑ i, (low i ∩ paired).card) + 2 := by
      have hpoint : ∀ i,
          (low i ∩ nextPaired).card = (low i ∩ paired).card + (low i ∩ b.footprint).card := by
        intro i
        have hdl : Disjoint (low i ∩ paired) (low i ∩ b.footprint) :=
          hdis_bp.mono Finset.inter_subset_right Finset.inter_subset_right
        rw [show low i ∩ nextPaired = (low i ∩ paired) ∪ (low i ∩ b.footprint) by
          exact Finset.inter_union_distrib_left _ _ _, Finset.card_union_of_disjoint hdl]
      calc
        (∑ i, (low i ∩ nextPaired).card)
            = (∑ i, (low i ∩ paired).card) + ∑ i, (low i ∩ b.footprint).card := by
                simp only [hpoint, Finset.sum_add_distrib]
        _ ≤ (∑ i, (low i ∩ paired).card) + 2 := Nat.add_le_add_left hbHits.2 _
    obtain ⟨tail, hlen, hvalid, hpair, havoid⟩ := ih nextPaired hnext_eq (by omega)
    refine ⟨b :: tail, by simp [hlen], ?_, ?_, ?_⟩
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hbValid
      · exact hvalid c hc
    · apply List.pairwise_cons.mpr
      refine ⟨?_, hpair⟩
      intro c hc
      have hsub : b.footprint ⊆ removed ∪ nextPaired :=
        Finset.subset_union_right.trans (by intro x hx; exact Finset.mem_union_right _ hx)
      exact (Disjoint.mono_right
        (show b.footprint ⊆ removed ∪ nextPaired from fun x hx =>
          Finset.mem_union_right _ (Finset.mem_union_right _ hx))
        (havoid c hc)).symm
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hbDisj
      · exact Disjoint.mono_right
          (show removed ∪ paired ⊆ removed ∪ nextPaired from fun x hx => by
            rcases Finset.mem_union.mp hx with hr | hp
            · exact Finset.mem_union_left _ hr
            · exact Finset.mem_union_right _ (Finset.mem_union_left _ hp))
          (havoid c hc)

/-- Select and physically install `k` matched-bin blocks while paying `removed.card + 2 * k ≤ B`. -/
theorem bmor_select_and_install_matched_blocks_paired_budget {n N W B k : ℕ}
    (h : BMORFiniteTheta) (upper : RSIndexUpper) (b c : Fin N × Bool → ℝ)
    (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18)
    (hb : ∀ z, 1 ≤ b z) (hbc : ∀ z, b z ≤ c z)
    (hcX : ∀ z, c z ≤ (poolMaximum n : ℝ))
    (hsep : ∀ z t, z ≠ t → c z ≤ b t ∨ c t ≤ b z)
    (hcross : ∀ i j, c (i, false) ≤ b (j, true))
    (hW : ∀ z, (W : ℝ) ≤
      ((c z - b z) - (518 / 125 : ℝ) * (Real.sqrt (b z) + Real.sqrt (c z))) /
        Real.log (poolMaximum n : ℝ))
    (removed : Finset ℕ)
    (hgate : (N : ℝ) * (poolMaximum n : ℝ) < ((N * W - B : ℕ) : ℝ) ^ 2)
    (hbudget : removed.card + 2 * k ≤ B)
    (a : Cell n ≃ Fin (n * n)) (cells : Fin k × Fin 4 → Cell n)
    (reserved : Finset (Cell n)) (hcells : Function.Injective cells)
    (hnew : ∀ x, cells x ∉ reserved)
    (hreserved : ∀ cell ∈ reserved,
      entry a cell ∈ removed ∨
        entry a cell ∉ Finset.univ.biUnion (bmorLowBins b c) ∪
          Finset.univ.biUnion (bmorHighBins b c)) :
    let low := bmorLowBins b c
    let high := bmorHighBins b c
    ∃ (blocks : List DoublePair) (hlen : blocks.length = k) (a' : Cell n ≃ Fin (n * n)),
      (∀ block ∈ blocks, block.MatchedValid low high) ∧
      blocks.Pairwise (fun x y => Disjoint x.footprint y.footprint) ∧
      (∀ block ∈ blocks, Disjoint block.footprint removed) ∧
      (∀ x : Fin blocks.length × Fin 4,
        entry a' (cells (Fin.cast hlen x.1, x.2)) = doublePairSequenceEndpoint blocks x) ∧
      (∀ cell ∈ reserved, entry a' cell = entry a cell) := by
  classical
  dsimp only
  obtain ⟨hdis, hlow, hhigh, horder, hdiff, hpoolL, hpoolH⟩ :=
    bmor_two_matched_bin_inputs h upper n W b c hn hnmax hb hbc hcX hsep hcross hW
  obtain ⟨blocks, hlen, hmatched, hpair, havoid⟩ :=
    select_matched_bin_double_pairs_paired_budget
      (bmorLowBins b c) (bmorHighBins b c) removed (Finset.range (poolMaximum n))
      hdis hlow hhigh horder hdiff (by simp) hgate hbudget
  have hvalid : ∀ bl ∈ blocks,
      bl.valid (Finset.univ.biUnion (bmorLowBins b c)) (Finset.univ.biUnion (bmorHighBins b c)) :=
    fun bl hbl => (hmatched bl hbl).1
  have horder' : ∀ p ∈ Finset.univ.biUnion (bmorLowBins b c),
      ∀ q ∈ Finset.univ.biUnion (bmorHighBins b c), p < q := by
    intro p hp q hq
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hq
    exact horder i j p hi q hj
  have hpoolL' : ∀ p ∈ Finset.univ.biUnion (bmorLowBins b c), p ∈ pool n := by
    intro p hp
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
    exact hpoolL i p hi
  have hpoolH' : ∀ p ∈ Finset.univ.biUnion (bmorHighBins b c), p ∈ pool n := by
    intro p hp
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
    exact hpoolH i p hi
  let cells' : Fin blocks.length × Fin 4 → Cell n := fun x => cells (Fin.cast hlen x.1, x.2)
  have hcells' : Function.Injective cells' := by
    rintro ⟨i, u⟩ ⟨j, v⟩ he
    have he' : (Fin.cast hlen i, u) = (Fin.cast hlen j, v) := hcells he
    have hi : i = j := Fin.ext (congrArg (fun z : Fin k × Fin 4 => z.1.val) he')
    have hv : u = v := congrArg Prod.snd he'
    cases hi
    cases hv
    rfl
  have hnew' : ∀ x, cells' x ∉ reserved := fun x => hnew (Fin.cast hlen x.1, x.2)
  have havoidentries : ∀ bl ∈ blocks, ∀ v ∈ bl.footprint, ∀ cell ∈ reserved, v ≠ entry a cell := by
    intro bl hbl v hv cell hcell heq
    rcases hreserved cell hcell with hmem | hout
    · exact Finset.disjoint_left.mp (havoid bl hbl) hv (heq ▸ hmem)
    · apply hout
      rw [← heq]
      rcases hmatched bl hbl with ⟨_, ⟨i, hli, hhi⟩, ⟨j, hlj, hhj⟩⟩
      simp only [DoublePair.footprint, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hli⟩)
      · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hlj⟩)
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hhi⟩)
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hhj⟩)
  obtain ⟨a', hplace, hfixed⟩ := install_double_pair_sequence blocks _ _ horder' hvalid hpair
    hpoolL' hpoolH' a cells' reserved hcells' hnew' havoidentries
  exact ⟨blocks, hlen, a', hmatched, hpair, havoid, hplace, hfixed⟩

end

end Sude
