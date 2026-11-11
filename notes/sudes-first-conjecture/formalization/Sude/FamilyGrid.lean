import Sude.CenteredGrid
import Sude.NetworkSwitches

/-! Simultaneous centered subset choices on distinct physical reservoirs.
The edge flows are inputs here; their integral existence remains open. -/
namespace Sude
noncomputable section

/-- Choosing a subset of each pairwise-disjoint block and taking their union
recovers exactly that subset when intersected with the original block. -/
theorem biUnion_inter_block {E K : Type*} [Fintype E] [DecidableEq E] [DecidableEq K]
    (block choose : E → Finset K) (hsub : ∀ e, choose e ⊆ block e)
    (hdisj : ∀ e f, e ≠ f → Disjoint (block e) (block f)) (e : E) :
    ((Finset.univ.biUnion choose) ∩ block e) = choose e := by
  ext k
  simp only [Finset.mem_inter, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨f, hf⟩, he⟩
    by_cases hfe : f = e
    · simpa [hfe] using hf
    · exact False.elim (Finset.disjoint_left.mp (hdisj f e hfe) (hsub f hf) he)
  · intro hk
    exact ⟨⟨e, hk⟩, hsub e hk⟩

/-- Select all reservoir reference subsets once, then simultaneously realize
any family of even signed transfers within the individual centered radii.
The blocks correspond to disjoint physical pairs, not shared abstract stock. -/
theorem simultaneous_centered_subsets {E K : Type*} [Fintype E] [DecidableEq E] [DecidableEq K]
    (block : E → Finset K) (gap : K → ℕ) (R : E → ℕ)
    (hdisj : ∀ e f, e ≠ f → Disjoint (block e) (block f))
    (hgrid : ∀ e, CompleteEvenGrid (block e) gap (R e)) :
    ∃ S₀ : Finset K,
      S₀ ⊆ Finset.univ.biUnion block ∧
      (∀ e, ((∑ k ∈ S₀ ∩ block e, gap k : ℕ) : ℤ) = evenGridCenter (R e)) ∧
      (∀ t : E → ℤ, (∀ e, (2 : ℤ) ∣ t e) →
        (∀ e, -(evenGridCenter (R e) : ℤ) ≤ t e) →
        (∀ e, t e ≤ evenGridCenter (R e)) →
        ∃ S : Finset K, S ⊆ Finset.univ.biUnion block ∧
          ∀ e, ((∑ k ∈ S ∩ block e, gap k : ℕ) : ℤ) -
            ((∑ k ∈ S₀ ∩ block e, gap k : ℕ) : ℤ) = t e) := by
  classical
  have href : ∀ e, ∃ T : Finset K, T ⊆ block e ∧
      ((∑ k ∈ T, gap k : ℕ) : ℤ) - evenGridCenter (R e) = 0 := by
    intro e
    exact centered_even_grid (block e) gap (R e) (hgrid e) 0 (by norm_num) (by omega) (by omega)
  choose T₀ hT₀ hsum₀ using href
  let S₀ := Finset.univ.biUnion T₀
  have hS₀ : S₀ ⊆ Finset.univ.biUnion block := by
    intro k hk
    obtain ⟨e, _, he⟩ := Finset.mem_biUnion.mp hk
    exact Finset.mem_biUnion.mpr ⟨e, Finset.mem_univ _, hT₀ e he⟩
  have hreference : ∀ e, ((∑ k ∈ S₀ ∩ block e, gap k : ℕ) : ℤ) = evenGridCenter (R e) := by
    intro e
    rw [biUnion_inter_block block T₀ hT₀ hdisj e]
    have hh := hsum₀ e
    omega
  refine ⟨S₀, hS₀, hreference, ?_⟩
  intro t heven hlow hhigh
  have hex : ∀ e, ∃ T : Finset K, T ⊆ block e ∧
      ((∑ k ∈ T, gap k : ℕ) : ℤ) - evenGridCenter (R e) = t e := by
    intro e
    exact centered_even_grid (block e) gap (R e) (hgrid e) (t e) (heven e) (hlow e) (hhigh e)
  choose T hT hsum using hex
  let S := Finset.univ.biUnion T
  have hS : S ⊆ Finset.univ.biUnion block := by
    intro k hk
    obtain ⟨e, _, he⟩ := Finset.mem_biUnion.mp hk
    exact Finset.mem_biUnion.mpr ⟨e, Finset.mem_univ _, hT e he⟩
  refine ⟨S, hS, ?_⟩
  intro e
  rw [biUnion_inter_block block T hT hdisj e, hreference e]
  exact hsum e

/-- A sum over selected pair labels splits exactly over disjoint reservoirs. -/
theorem sum_by_disjoint_blocks {E K : Type*} [Fintype E] [DecidableEq E] [DecidableEq K]
    (block : E → Finset K) (hdisj : ∀ e f, e ≠ f → Disjoint (block e) (block f))
    (S : Finset K) (hS : S ⊆ Finset.univ.biUnion block) (f : K → ℤ) :
    (∑ k ∈ S, f k) = ∑ e : E, ∑ k ∈ S ∩ block e, f k := by
  classical
  have hunion : Finset.univ.biUnion (fun e => S ∩ block e) = S := by
    ext k
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_inter]
    constructor
    · rintro ⟨e, hk, _⟩
      exact hk
    · intro hk
      obtain ⟨e, _, he⟩ := Finset.mem_biUnion.mp (hS hk)
      exact ⟨e, hk, he⟩
  have hpair : Set.PairwiseDisjoint (↑(Finset.univ : Finset E)) (fun e => S ∩ block e) := by
    intro e he f hf hne
    exact (hdisj e f hne).mono Finset.inter_subset_right Finset.inter_subset_right
  calc
    (∑ k ∈ S, f k) = ∑ k ∈ Finset.univ.biUnion (fun e => S ∩ block e), f k := by rw [hunion]
    _ = ∑ e : E, ∑ k ∈ S ∩ block e, f k := Finset.sum_biUnion hpair

/-- An oriented signed transfer at one reservoir's two endpoint rows. -/
def edgeTransfer {E : Type*} {n : ℕ} (source target : E → Fin n)
    (t : E → ℤ) (e : E) (r : Fin n) : ℤ :=
  (if source e = r then t e else 0) - (if target e = r then t e else 0)

/-- Gather physical pair contributions by their reservoir, retaining both
endpoint signs and every selected gap. -/
theorem rowNetwork_sum_by_reservoir {n : ℕ} {E K : Type*}
    [Fintype E] [DecidableEq E] [DecidableEq K]
    {a : Cell n ≃ Fin (n * n)} (v : RowNetworkPairs K a)
    (block : E → Finset K) (source target : E → Fin n)
    (hdisj : ∀ e f, e ≠ f → Disjoint (block e) (block f))
    (hend : ∀ e k, k ∈ block e → v.low k = source e ∧ v.high k = target e)
    (S : Finset K) (hS : S ⊆ Finset.univ.biUnion block) (r : Fin n) :
    (∑ k ∈ S, rowNetworkDelta v k r) =
      ∑ e : E, ((if source e = r then ∑ k ∈ S ∩ block e, (v.gap k : ℤ) else 0) -
        (if target e = r then ∑ k ∈ S ∩ block e, (v.gap k : ℤ) else 0)) := by
  rw [sum_by_disjoint_blocks block hdisj S hS (fun k => rowNetworkDelta v k r)]
  apply Finset.sum_congr rfl
  intro e he
  calc
    (∑ k ∈ S ∩ block e, rowNetworkDelta v k r) =
        ∑ k ∈ S ∩ block e, ((if source e = r then (v.gap k : ℤ) else 0) -
          (if target e = r then (v.gap k : ℤ) else 0)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hh := hend e k (Finset.mem_inter.mp hk).2
      simp [rowNetworkDelta, hh.1, hh.2]
    _ = _ := by simp [Finset.sum_sub_distrib, Finset.sum_ite_irrel]

/-- Reservoir-sum differences are exactly the directed edge-transfer sum. -/
theorem rowNetwork_subset_difference {n : ℕ} {E K : Type*}
    [Fintype E] [DecidableEq E] [DecidableEq K]
    {a : Cell n ≃ Fin (n * n)} (v : RowNetworkPairs K a)
    (block : E → Finset K) (source target : E → Fin n)
    (hdisj : ∀ e f, e ≠ f → Disjoint (block e) (block f))
    (hend : ∀ e k, k ∈ block e → v.low k = source e ∧ v.high k = target e)
    (S S₀ : Finset K) (hS : S ⊆ Finset.univ.biUnion block)
    (hS₀ : S₀ ⊆ Finset.univ.biUnion block) (t : E → ℤ)
    (hsum : ∀ e, (∑ k ∈ S ∩ block e, (v.gap k : ℤ)) -
      (∑ k ∈ S₀ ∩ block e, (v.gap k : ℤ)) = t e) (r : Fin n) :
    (∑ k ∈ S, rowNetworkDelta v k r) - (∑ k ∈ S₀, rowNetworkDelta v k r) =
      ∑ e : E, edgeTransfer source target t e r := by
  let effect : Finset K → E → ℤ := fun T e =>
    (if source e = r then ∑ k ∈ T ∩ block e, (v.gap k : ℤ) else 0) -
      (if target e = r then ∑ k ∈ T ∩ block e, (v.gap k : ℤ) else 0)
  have hnew : (∑ k ∈ S, rowNetworkDelta v k r) = ∑ e : E, effect S e :=
    rowNetwork_sum_by_reservoir v block source target hdisj hend S hS r
  have hbase : (∑ k ∈ S₀, rowNetworkDelta v k r) = ∑ e : E, effect S₀ e :=
    rowNetwork_sum_by_reservoir v block source target hdisj hend S₀ hS₀ r
  rw [hnew, hbase, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e he
  have hh := hsum e
  dsimp [effect, edgeTransfer]
  split_ifs <;> omega

/-- Explicit data and proved hypotheses for disjoint physical reservoirs. -/
structure CenteredNetwork {n : ℕ} (E K : Type*) [Fintype E] [DecidableEq E]
    [DecidableEq K] {a : Cell n ≃ Fin (n * n)} (v : RowNetworkPairs K a) where
  block : E → Finset K
  radius : E → ℕ
  source : E → Fin n
  target : E → Fin n
  disjoint : ∀ e f, e ≠ f → Disjoint (block e) (block f)
  grid : ∀ e, CompleteEvenGrid (block e) v.gap (radius e)
  endpoints : ∀ e k, k ∈ block e → v.low k = source e ∧ v.high k = target e

/-- A single physical reference placement realizes every simultaneous family
of bounded even edge transfers through actual disjoint row-pair swaps. The
per-edge flow values are supplied; this theorem does not prove their existence. -/
theorem rowNetwork_centered_transfers {n : ℕ} {E K : Type*}
    [Fintype E] [DecidableEq E] [DecidableEq K]
    (a : Cell n ≃ Fin (n * n)) (v : RowNetworkPairs K a)
    (reserved : Finset (Cell n)) (block : E → Finset K) (R : E → ℕ)
    (source target : E → Fin n)
    (hdisj : ∀ e f, e ≠ f → Disjoint (block e) (block f))
    (hgrid : ∀ e, CompleteEvenGrid (block e) v.gap (R e))
    (hend : ∀ e k, k ∈ block e → v.low k = source e ∧ v.high k = target e)
    (hprotect : ∀ c ∈ reserved, ∀ k ∈ Finset.univ.biUnion block,
      c ≠ (v.low k, v.column k) ∧ c ≠ (v.high k, v.column k)) :
    ∃ (S₀ : Finset K) (b₀ : Cell n ≃ Fin (n * n)),
      S₀ ⊆ Finset.univ.biUnion block ∧ RowNetworkOutcome v S₀ b₀ ∧
      (∀ e, ((∑ k ∈ S₀ ∩ block e, v.gap k : ℕ) : ℤ) = evenGridCenter (R e)) ∧
      (∀ t : E → ℤ, (∀ e, (2 : ℤ) ∣ t e) →
        (∀ e, -(evenGridCenter (R e) : ℤ) ≤ t e) →
        (∀ e, t e ≤ evenGridCenter (R e)) →
        ∃ (S : Finset K) (b : Cell n ≃ Fin (n * n)),
          S ⊆ Finset.univ.biUnion block ∧ RowNetworkOutcome v S b ∧
          (∀ r, (rowSum b r : ℤ) - (rowSum b₀ r : ℤ) = ∑ e : E, edgeTransfer source target t e r) ∧
          (∀ c, columnSum b c = columnSum b₀ c) ∧
          mainSum b = mainSum b₀ ∧ antiSum b = antiSum b₀ ∧
          (∀ c ∈ reserved, entry b c = entry b₀ c) ∧
          Set.range (entry b) = pool n ∧ Function.Injective (entry b)) := by
  obtain ⟨S₀, hS₀, hcenters, hchoose⟩ :=
    simultaneous_centered_subsets block v.gap R hdisj hgrid
  obtain ⟨b₀, hb₀⟩ := rowNetwork_toggle_subset a v S₀
  refine ⟨S₀, b₀, hS₀, hb₀, hcenters, ?_⟩
  intro t heven hlow hhigh
  obtain ⟨S, hS, hsum⟩ := hchoose t heven hlow hhigh
  obtain ⟨b, hb⟩ := rowNetwork_toggle_subset a v S
  have hsumZ : ∀ e, (∑ k ∈ S ∩ block e, (v.gap k : ℤ)) -
      (∑ k ∈ S₀ ∩ block e, (v.gap k : ℤ)) = t e := by
    intro e
    exact_mod_cast hsum e
  refine ⟨S, b, hS, hb, ?_, ?_, ?_, ?_, ?_, entry_range _, entry_injective _⟩
  · intro r
    let effect : Finset K → E → ℤ := fun T e =>
      (if source e = r then ∑ k ∈ T ∩ block e, (v.gap k : ℤ) else 0) -
        (if target e = r then ∑ k ∈ T ∩ block e, (v.gap k : ℤ) else 0)
    have hbase : (rowSum b₀ r : ℤ) - (rowSum a r : ℤ) = ∑ e : E, effect S₀ e := by
      exact (hb₀.rows r).trans (rowNetwork_sum_by_reservoir v block source target hdisj hend S₀ hS₀ r)
    have hnew : (rowSum b r : ℤ) - (rowSum a r : ℤ) = ∑ e : E, effect S e := by
      exact (hb.rows r).trans (rowNetwork_sum_by_reservoir v block source target hdisj hend S hS r)
    calc
      (rowSum b r : ℤ) - (rowSum b₀ r : ℤ) = (∑ e : E, effect S e) - ∑ e : E, effect S₀ e := by omega
      _ = ∑ e : E, (effect S e - effect S₀ e) :=
        (Finset.sum_sub_distrib (fun e => effect S e) (fun e => effect S₀ e)).symm
      _ = ∑ e : E, edgeTransfer source target t e r := by
        apply Finset.sum_congr rfl
        intro e he
        have hh := hsumZ e
        dsimp [effect, edgeTransfer]
        split_ifs <;> omega
  · intro c
    exact (hb.columns c).trans (hb₀.columns c).symm
  · exact hb.main.trans hb₀.main.symm
  · exact hb.anti.trans hb₀.anti.symm
  · intro c hc
    have h₀ : entry b₀ c = entry a c := by
      apply hb₀.outside_fixed c
      intro k hk
      exact hprotect c hc k (hS₀ hk)
    have h₁ : entry b c = entry a c := by
      apply hb.outside_fixed c
      intro k hk
      exact hprotect c hc k (hS hk)
    exact h₁.trans h₀.symm

/-- Choose one joint physical reference for both installed networks. Every
subsequently supplied family of bounded even edge flows is realized by actual
disjoint swaps, with all row and column effects, both diagonals, the original
reservation, and the exact pool accounted for. The theorem does not assert
that a flow satisfying chosen line demands exists. The same reference also
retains its selected-swap line identities and its signed center invoices;
no bound on those invoices is asserted. -/
theorem twoNetworks_centered_transfers_with_invoice {n : ℕ} {Er Ec : Type*}
    [Fintype Er] [DecidableEq Er] [Fintype Ec] [DecidableEq Ec]
    (a : Cell n ≃ Fin (n * n)) (reserved : Finset (Cell n))
    (rows cols : List (LayerPacking.Layer n))
    (hr : LayerPacking.PackedLayers reserved rows)
    (hc : LayerPacking.PackedLayers
      (LayerPacking.transposeCells (reserved ∪ LayerPacking.layersSupport rows)) cols)
    (rowGap : Fin rows.length → Fin n → ℕ)
    (colGap : Fin cols.length → Fin n → ℕ)
    (hrowGap : ∀ i e, entry a ((rows.get i).1 e, (rows.get i).2 e) =
      entry a (e, (rows.get i).2 e) + rowGap i e)
    (hcolGap : ∀ i e, entry a ((cols.get i).2 e, (cols.get i).1 e) =
      entry a ((cols.get i).2 e, e) + colGap i e)
    (BR : CenteredNetwork Er (Fin rows.length × Fin n) (hr.rowPairs a rowGap hrowGap))
    (BC : CenteredNetwork Ec (Fin cols.length × Fin n) (hc.columnPairs a colGap hcolGap)) :
    ∃ (Sr₀ : Finset (Fin rows.length × Fin n)) (Sc₀ : Finset (Fin cols.length × Fin n))
      (b₀ : Cell n ≃ Fin (n * n)),
      Sr₀ ⊆ Finset.univ.biUnion BR.block ∧ Sc₀ ⊆ Finset.univ.biUnion BC.block ∧
      (∀ e, ((∑ k ∈ Sr₀ ∩ BR.block e, rowGap k.1 k.2 : ℕ) : ℤ) = evenGridCenter (BR.radius e)) ∧
      (∀ e, ((∑ k ∈ Sc₀ ∩ BC.block e, colGap k.1 k.2 : ℕ) : ℤ) = evenGridCenter (BC.radius e)) ∧
      (∀ r, (rowSum b₀ r : ℤ) - (rowSum a r : ℤ) = ∑ k ∈ Sr₀, layerTransfer rows rowGap k r) ∧
      (∀ c, (columnSum b₀ c : ℤ) - (columnSum a c : ℤ) = ∑ k ∈ Sc₀, layerTransfer cols colGap k c) ∧
      (∀ r, (rowSum b₀ r : ℤ) - (rowSum a r : ℤ) =
        ∑ e : Er, edgeTransfer BR.source BR.target (fun e => evenGridCenter (BR.radius e)) e r) ∧
      (∀ c, (columnSum b₀ c : ℤ) - (columnSum a c : ℤ) =
        ∑ e : Ec, edgeTransfer BC.source BC.target (fun e => evenGridCenter (BC.radius e)) e c) ∧
      mainSum b₀ = mainSum a ∧ antiSum b₀ = antiSum a ∧
      (∀ c ∈ reserved, entry b₀ c = entry a c) ∧
      (∀ tr : Er → ℤ, (∀ e, (2 : ℤ) ∣ tr e) →
        (∀ e, -(evenGridCenter (BR.radius e) : ℤ) ≤ tr e) →
        (∀ e, tr e ≤ evenGridCenter (BR.radius e)) →
        ∀ tc : Ec → ℤ, (∀ e, (2 : ℤ) ∣ tc e) →
        (∀ e, -(evenGridCenter (BC.radius e) : ℤ) ≤ tc e) →
        (∀ e, tc e ≤ evenGridCenter (BC.radius e)) →
        ∃ b : Cell n ≃ Fin (n * n),
          (∀ r, (rowSum b r : ℤ) - (rowSum b₀ r : ℤ) = ∑ e : Er, edgeTransfer BR.source BR.target tr e r) ∧
          (∀ c, (columnSum b c : ℤ) - (columnSum b₀ c : ℤ) = ∑ e : Ec, edgeTransfer BC.source BC.target tc e c) ∧
          mainSum b = mainSum b₀ ∧ antiSum b = antiSum b₀ ∧
          (∀ c ∈ reserved, entry b c = entry b₀ c) ∧
          Set.range (entry b) = pool n ∧ Function.Injective (entry b)) := by
  let vr := hr.rowPairs a rowGap hrowGap
  let vc := hc.columnPairs a colGap hcolGap
  obtain ⟨Sr₀, hr₀, hrcenters, hrchoose⟩ :=
    simultaneous_centered_subsets BR.block vr.gap BR.radius BR.disjoint BR.grid
  obtain ⟨Sc₀, hc₀, hccenters, hcchoose⟩ :=
    simultaneous_centered_subsets BC.block vc.gap BC.radius BC.disjoint BC.grid
  obtain ⟨b₀, hbaseRows, hbaseCols, hbaseMain, hbaseAnti, hbaseFixed, _, _⟩ :=
    toggle_two_installed_networks a reserved rows cols hr hc rowGap colGap hrowGap hcolGap Sr₀ Sc₀
  have hrinvoice (r : Fin n) : (rowSum b₀ r : ℤ) - (rowSum a r : ℤ) =
      ∑ e : Er, edgeTransfer BR.source BR.target (fun e => evenGridCenter (BR.radius e)) e r := by
    rw [hbaseRows r]
    have hsum := rowNetwork_sum_by_reservoir vr BR.block BR.source BR.target
      BR.disjoint BR.endpoints Sr₀ hr₀ r
    change (∑ k ∈ Sr₀, layerTransfer rows rowGap k r) = _ at hsum
    rw [hsum]
    apply Finset.sum_congr rfl
    intro e he
    have hcenter : (∑ k ∈ Sr₀ ∩ BR.block e, (vr.gap k : ℤ)) = evenGridCenter (BR.radius e) := by
      exact_mod_cast hrcenters e
    simp only [hcenter, edgeTransfer]
  have hcinvoice (c : Fin n) : (columnSum b₀ c : ℤ) - (columnSum a c : ℤ) =
      ∑ e : Ec, edgeTransfer BC.source BC.target (fun e => evenGridCenter (BC.radius e)) e c := by
    rw [hbaseCols c]
    have hsum := rowNetwork_sum_by_reservoir vc BC.block BC.source BC.target
      BC.disjoint BC.endpoints Sc₀ hc₀ c
    change (∑ k ∈ Sc₀, layerTransfer cols colGap k c) = _ at hsum
    rw [hsum]
    apply Finset.sum_congr rfl
    intro e he
    have hcenter : (∑ k ∈ Sc₀ ∩ BC.block e, (vc.gap k : ℤ)) = evenGridCenter (BC.radius e) := by
      exact_mod_cast hccenters e
    simp only [hcenter, edgeTransfer]
  refine ⟨Sr₀, Sc₀, b₀, hr₀, hc₀, hrcenters, hccenters, hbaseRows, hbaseCols,
    hrinvoice, hcinvoice, hbaseMain, hbaseAnti, hbaseFixed, ?_⟩
  intro tr hre hrl hrh tc hce hcl hch
  obtain ⟨Sr, hrs, hrsums⟩ := hrchoose tr hre hrl hrh
  obtain ⟨Sc, hcs, hcsums⟩ := hcchoose tc hce hcl hch
  obtain ⟨b, hrows, hcols, hm, ha, hfixed, hpool, hinj⟩ :=
    toggle_two_installed_networks a reserved rows cols hr hc rowGap colGap hrowGap hcolGap Sr Sc
  have hrsumsZ : ∀ e, (∑ k ∈ Sr ∩ BR.block e, (vr.gap k : ℤ)) -
      (∑ k ∈ Sr₀ ∩ BR.block e, (vr.gap k : ℤ)) = tr e := by
    intro e
    exact_mod_cast hrsums e
  have hcsumsZ : ∀ e, (∑ k ∈ Sc ∩ BC.block e, (vc.gap k : ℤ)) -
      (∑ k ∈ Sc₀ ∩ BC.block e, (vc.gap k : ℤ)) = tc e := by
    intro e
    exact_mod_cast hcsums e
  refine ⟨b, ?_, ?_, hm.trans hbaseMain.symm, ha.trans hbaseAnti.symm, ?_, hpool, hinj⟩
  · intro r
    have hdiff := rowNetwork_subset_difference vr BR.block BR.source BR.target
      BR.disjoint BR.endpoints Sr Sr₀ hrs hr₀ tr hrsumsZ r
    have hnew := hrows r
    have hbase := hbaseRows r
    change (∑ k ∈ Sr, layerTransfer rows rowGap k r) -
      (∑ k ∈ Sr₀, layerTransfer rows rowGap k r) = _ at hdiff
    omega
  · intro c
    have hdiff := rowNetwork_subset_difference vc BC.block BC.source BC.target
      BC.disjoint BC.endpoints Sc Sc₀ hcs hc₀ tc hcsumsZ c
    have hnew := hcols c
    have hbase := hbaseCols c
    change (∑ k ∈ Sc, layerTransfer cols colGap k c) -
      (∑ k ∈ Sc₀, layerTransfer cols colGap k c) = _ at hdiff
    omega
  · intro c hc'
    exact (hfixed c hc').trans (hbaseFixed c hc').symm

/-- The original interface, obtained by forgetting the centering invoice. -/
theorem twoNetworks_centered_transfers {n : ℕ} {Er Ec : Type*}
    [Fintype Er] [DecidableEq Er] [Fintype Ec] [DecidableEq Ec]
    (a : Cell n ≃ Fin (n * n)) (reserved : Finset (Cell n))
    (rows cols : List (LayerPacking.Layer n))
    (hr : LayerPacking.PackedLayers reserved rows)
    (hc : LayerPacking.PackedLayers
      (LayerPacking.transposeCells (reserved ∪ LayerPacking.layersSupport rows)) cols)
    (rowGap : Fin rows.length → Fin n → ℕ)
    (colGap : Fin cols.length → Fin n → ℕ)
    (hrowGap : ∀ i e, entry a ((rows.get i).1 e, (rows.get i).2 e) =
      entry a (e, (rows.get i).2 e) + rowGap i e)
    (hcolGap : ∀ i e, entry a ((cols.get i).2 e, (cols.get i).1 e) =
      entry a ((cols.get i).2 e, e) + colGap i e)
    (BR : CenteredNetwork Er (Fin rows.length × Fin n) (hr.rowPairs a rowGap hrowGap))
    (BC : CenteredNetwork Ec (Fin cols.length × Fin n) (hc.columnPairs a colGap hcolGap)) :
    ∃ (Sr₀ : Finset (Fin rows.length × Fin n)) (Sc₀ : Finset (Fin cols.length × Fin n))
      (b₀ : Cell n ≃ Fin (n * n)),
      Sr₀ ⊆ Finset.univ.biUnion BR.block ∧ Sc₀ ⊆ Finset.univ.biUnion BC.block ∧
      (∀ e, ((∑ k ∈ Sr₀ ∩ BR.block e, rowGap k.1 k.2 : ℕ) : ℤ) = evenGridCenter (BR.radius e)) ∧
      (∀ e, ((∑ k ∈ Sc₀ ∩ BC.block e, colGap k.1 k.2 : ℕ) : ℤ) = evenGridCenter (BC.radius e)) ∧
      mainSum b₀ = mainSum a ∧ antiSum b₀ = antiSum a ∧
      (∀ c ∈ reserved, entry b₀ c = entry a c) ∧
      (∀ tr : Er → ℤ, (∀ e, (2 : ℤ) ∣ tr e) →
        (∀ e, -(evenGridCenter (BR.radius e) : ℤ) ≤ tr e) →
        (∀ e, tr e ≤ evenGridCenter (BR.radius e)) →
        ∀ tc : Ec → ℤ, (∀ e, (2 : ℤ) ∣ tc e) →
        (∀ e, -(evenGridCenter (BC.radius e) : ℤ) ≤ tc e) →
        (∀ e, tc e ≤ evenGridCenter (BC.radius e)) →
        ∃ b : Cell n ≃ Fin (n * n),
          (∀ r, (rowSum b r : ℤ) - (rowSum b₀ r : ℤ) = ∑ e : Er, edgeTransfer BR.source BR.target tr e r) ∧
          (∀ c, (columnSum b c : ℤ) - (columnSum b₀ c : ℤ) = ∑ e : Ec, edgeTransfer BC.source BC.target tc e c) ∧
          mainSum b = mainSum b₀ ∧ antiSum b = antiSum b₀ ∧
          (∀ c ∈ reserved, entry b c = entry b₀ c) ∧
          Set.range (entry b) = pool n ∧ Function.Injective (entry b)) := by
  obtain ⟨Sr₀, Sc₀, b₀, hr₀, hc₀, hrcenters, hccenters, _, _, _, _,
    hmain, hanti, hfixed, hrealize⟩ :=
    twoNetworks_centered_transfers_with_invoice a reserved rows cols hr hc rowGap colGap
      hrowGap hcolGap BR BC
  exact ⟨Sr₀, Sc₀, b₀, hr₀, hc₀, hrcenters, hccenters, hmain, hanti, hfixed, hrealize⟩

end
end Sude
