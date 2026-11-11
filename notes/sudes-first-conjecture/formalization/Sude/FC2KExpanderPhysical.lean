import Sude.PrefixInstalledNetwork
import Sude.PermutationExceptions
import Sude.PhysicalCutRouting

/-! Install a proved FC2K expander on both actual prefix pair networks. -/
namespace Sude
noncomputable section

theorem prefixNetworkInput_cast {P d r n Q m q : ℕ}
    (hfit : (4 * d) * 2 + 2 * (r * n) ≤ Q) (h₁ : m = q) (h₂ : q = P * r)
    (network : Fin 2) (x : Fin m × (Fin n × Bool)) :
    prefixNetworkInput hfit h₂ network (Fin.cast h₁ x.1, x.2) =
      prefixNetworkInput hfit (h₁.trans h₂) network x := by
  simp [prefixNetworkInput]

/-- The graph permutations are constructed, not assumed. The input population
must still supply distinct prescribed-pool entries for every prefix stage;
the packing, rectangle and reservation hypotheses are also explicit. -/
theorem fc2k_install_expanding_prefix {P d n Q L B : ℕ}
    (hn : 2001 ≤ n)
    (hfit : (4 * d) * 2 + 2 * (3 * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (values : (Fin P × Fin Q) × Bool → pool n) (hinj : Function.Injective values)
    (hgap : ∀ j i, (values ((j, i), true)).val =
      (values ((j, i), false)).val + 2 ^ (j.val + 1))
    (initial : Finset ℕ) (havoid : ∀ x, (values x).val ∉ initial)
    (base : Finset (Cell n)) (hrload : ∀ i, (LayerPacking.rowUsed base i).card ≤ B)
    (hcload : ∀ i, (LayerPacking.colUsed base i).card ≤ B)
    (hcapacity : 4 * ((B + 2) + 2 * (P * 3) + 2 * (P * 3)) + 8 < n)
    (a : Cell n ≃ Fin (n * n)) (hbase : ∀ c ∈ base, entry a c ∈ initial)
    (hfree : ∀ x : Fin (P * (4 * d)) × Fin 4,
      packedRectangleCorner hs choice (Fin.castLE hrect x.1, x.2) ∉ base) :
    ∃ (p : Fin 3 → Equiv.Perm (Fin n))
      (rows cols : List (LayerPacking.Layer n))
      (hrows : rows.length = P * 3) (hcols : cols.length = P * 3)
      (b : Cell n ≃ Fin (n * n)),
      (∀ i v, p i v ≠ v) ∧
      (∀ S : Finset (Fin n), 199 * min S.card (n - S.card) ≤
        200 * (cutEdges (fun e : Fin 3 × Fin n => e.2)
          (fun e => p e.1 e.2) S).card) ∧
      rows.map Prod.fst = bridgeRepeatedPermutations P p ∧
      cols.map Prod.fst = bridgeRepeatedPermutations P p ∧
      LayerPacking.PackedLayers (base ∪ allocatedBridgeRectangleSupport hrect hs choice) rows ∧
      LayerPacking.PackedLayers (LayerPacking.transposeCells
        ((base ∪ allocatedBridgeRectangleSupport hrect hs choice) ∪
          LayerPacking.layersSupport rows)) cols ∧
      Disjoint (LayerPacking.layersSupport rows)
        (LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∧
      (∀ x : Fin (P * (4 * d)) × Fin 4,
        entry b (packedRectangleCorner hs choice (Fin.castLE hrect x.1, x.2)) =
          (values (prefixRectangleInput hdiag x)).val) ∧
      (∀ x, entry b (LayerPacking.sequenceCell rows x) =
        (values (prefixNetworkInput hfit hrows 0 x)).val) ∧
      (∀ x, entry b (LayerPacking.sequenceCell cols x).swap =
        (values (prefixNetworkInput hfit hcols 1 x)).val) ∧
      (∀ i e, entry b ((rows.get i).1 e, (rows.get i).2 e) =
        entry b (e, (rows.get i).2 e) + prefixNetworkGap hrows i e) ∧
      (∀ i e, entry b ((cols.get i).2 e, (cols.get i).1 e) =
        entry b ((cols.get i).2 e, e) + prefixNetworkGap hcols i e) ∧
      (∀ c ∈ base, entry b c = entry a c) := by
  obtain ⟨p, hderange, hexp⟩ := fc2k_permutation_expander_exists hn
  let perms := bridgeRepeatedPermutations P p
  have hlen : perms.length = P * 3 := bridgeRepeatedPermutations_length p
  have hder : ∀ π ∈ perms, ∀ i, π i ≠ i :=
    bridgeRepeatedPermutations_derange p hderange
  have hcap : 4 * ((B + 2) + 2 * perms.length + 2 * perms.length) + 8 < n := by
    simpa only [hlen] using hcapacity
  obtain ⟨rows, cols, hr, hc, b, hrmap, hcmap, hrpack, hcpack, hdisjoint,
    hrectplaced, hrplaced, hcplaced, hrgap, hcgap, hfixed⟩ :=
    install_prefix_diagonal_and_ordinary hfit hdiag hrect hs choice values hinj hgap
      initial havoid perms perms hlen hlen hder hder base hrload hcload hcap a hbase hfree
  refine ⟨p, rows, cols, hr.trans hlen, hc.trans hlen, b, hderange, hexp,
    hrmap, hcmap, hrpack, hcpack, hdisjoint, hrectplaced, ?_, ?_, ?_, ?_, hfixed⟩
  · intro x
    simpa only [prefixNetworkInput_cast] using hrplaced x
  · intro x
    simpa only [prefixNetworkInput_cast] using hcplaced x
  · intro i e
    simpa only [prefixNetworkGap_cast] using hrgap i e
  · intro i e
    simpa only [prefixNetworkGap_cast] using hcgap i e

/-- An installed expanding prefix gives actual integral routing in the square.
The two prefix networks use disjoint physical cells; both diagonals and the
reservation are fixed. The supply and packing used to obtain this installation
are separate hypotheses of `fc2k_install_expanding_prefix`. -/
theorem fc2k_route_installed_prefix {P n : ℕ}
    (a : Cell n ≃ Fin (n * n)) (reserved : Finset (Cell n))
    (p : Fin 3 → Equiv.Perm (Fin n))
    (hexp : ∀ S : Finset (Fin n), 199 * min S.card (n - S.card) ≤
      200 * (cutEdges (fun e : Fin 3 × Fin n => e.2)
        (fun e => p e.1 e.2) S).card)
    (rows cols : List (LayerPacking.Layer n))
    (hrlen : rows.length = P * 3) (hclen : cols.length = P * 3)
    (hrperms : rows.map Prod.fst = bridgeRepeatedPermutations P p)
    (hcperms : cols.map Prod.fst = bridgeRepeatedPermutations P p)
    (hr : LayerPacking.PackedLayers reserved rows)
    (hc : LayerPacking.PackedLayers
      (LayerPacking.transposeCells (reserved ∪ LayerPacking.layersSupport rows)) cols)
    (hrowGap : ∀ i e, entry a ((rows.get i).1 e, (rows.get i).2 e) =
      entry a (e, (rows.get i).2 e) + prefixNetworkGap hrlen i e)
    (hcolGap : ∀ i e, entry a ((cols.get i).2 e, (cols.get i).1 e) =
      entry a ((cols.get i).2 e, e) + prefixNetworkGap hclen i e)
    (N B : ℕ) (hradius : 2 * N ≤ 2 ^ (P + 1) - 2)
    (hN : 2000 ≤ N) (hB : 400000 * B < 199 * 999 * N) :
    ∃ b₀ : Cell n ≃ Fin (n * n),
      mainSum b₀ = mainSum a ∧ antiSum b₀ = antiSum a ∧
      (∀ c ∈ reserved, entry b₀ c = entry a c) ∧
      ∀ dr dc : Fin n → ℤ,
      (∑ r, dr r = 0) → (∑ c, dc c = 0) →
      (∀ r, |dr r| ≤ (B : ℤ)) → (∀ c, |dc c| ≤ (B : ℤ)) →
      ∃ b : Cell n ≃ Fin (n * n),
        (∀ r, (rowSum b r : ℤ) - (rowSum b₀ r : ℤ) = 2 * dr r) ∧
        (∀ c, (columnSum b c : ℤ) - (columnSum b₀ c : ℤ) = 2 * dc c) ∧
        mainSum b = mainSum b₀ ∧ antiSum b = antiSum b₀ ∧
        (∀ c ∈ reserved, entry b c = entry b₀ c) ∧
        Set.range (entry b) = pool n ∧ Function.Injective (entry b) := by
  let BR := installedPrefixCenteredNetwork rows hrlen p hrperms reserved hr a hrowGap
  have hcolGap' : ∀ i e,
      entry (LayerPacking.transposePlacement a) ((cols.get i).1 e, (cols.get i).2 e) =
      entry (LayerPacking.transposePlacement a) (e, (cols.get i).2 e) +
        prefixNetworkGap hclen i e := by
    intro i e
    simpa using hcolGap i e
  let BC : CenteredNetwork (Fin 3 × Fin n) (Fin cols.length × Fin n)
      (hc.columnPairs a (prefixNetworkGap hclen) hcolGap) :=
    installedPrefixCenteredNetwork cols hclen p hcperms
      (LayerPacking.transposeCells (reserved ∪ LayerPacking.layersSupport rows)) hc
      (LayerPacking.transposePlacement a) hcolGap'
  exact twoNetworks_realize_fc2k_demands a reserved rows cols hr hc
    (prefixNetworkGap hrlen) (prefixNetworkGap hclen) hrowGap hcolGap BR BC N B
    (fun _ => hradius) (fun _ => hradius) hN hB hexp hexp

end
end Sude
