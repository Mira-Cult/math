import Sude

#print axioms Sude.oddPrime_injective
#print axioms Sude.entry_injective
#print axioms Sude.entry_range
#print axioms Sude.hasSquare_iff_values
#print axioms Sude.square_one
#print axioms Sude.compose_finite_and_open_tail
#print axioms Sude.odd_tail_interval_cover
#print axioms Sude.odd_power_boundary
#print axioms Sude.source_routes_iff_interval_routes
#print axioms Sude.odd_tail_source_cover
#print axioms Sude.primeOneBased_succ
#print axioms Sude.poolMaximum_mem
#print axioms Sude.pool_le_poolMaximum
#print axioms Sude.poolMaximum_lower
#print axioms Sude.poolMaximum_upper
#print axioms Sude.poolMaximum_upper_sharp
#print axioms Sude.tail_prime_index_domains
#print axioms Sude.primeOneBased_one
#print axioms Sude.primeOneBased_two
#print axioms Sude.poolMaximum_prime
#print axioms Sude.poolMaximum_log_lower
#print axioms Sude.poolMaximum_log_lower_v
#print axioms Sude.poolMaximum_below_two_pow_41
#print axioms Sude.pool_entry_below_ten_pow_13
#print axioms Sude.poolMaximum_below_two_pow_44
#print axioms Sude.mem_apPrefix_iff
#print axioms Sude.thetaAP_eq_sum_apPrefix
#print axioms Sude.bmorLimit_two_mod_four
#print axioms Sude.bmorLimit_ge_ten_pow_13
#print axioms Sude.bmor_theta_pointwise
#print axioms Sude.bmor_theta_bounded
#print axioms Sude.thetaAP_two_eq_four_classes
#print axioms Sude.bmor_theta_two_via_four
#print axioms Sude.prime_mem_pool_of_le_max
#print axioms Sude.mem_apInterval_iff
#print axioms Sude.thetaAP_sub_eq_interval_sum
#print axioms Sude.thetaAP_interval_le_count_log
#print axioms Sude.interval_count_from_theta_bounds
#print axioms Sude.even_reduced_class_excludes_two
#print axioms Sude.even_apInterval_subset_pool
#print axioms Sude.bmor_interval_count
#print axioms Sude.bmor_interval_count_two
#print axioms Sude.bmor_even_pool_interval_supply
#print axioms Sude.bmor_two_pool_interval_supply
#print axioms Sude.availableInterval_card_lower
#print axioms Sude.availableInterval_even_subset_pool
#print axioms Sude.bmor_even_available_pool_supply
#print axioms Sude.bmor_two_available_pool_supply

-- Boundary controls for the exact half-open interval and q=2 residue.
example : 3 ∉ Sude.apInterval 3 11 2 1 := by
  rw [Sude.mem_apInterval_iff 3 11 2 1 (by norm_num) (by norm_num) 3]
  norm_num

example : 11 ∈ Sude.apInterval 3 11 2 1 := by
  rw [Sude.mem_apInterval_iff 3 11 2 1 (by norm_num) (by norm_num) 11]
  norm_num [Nat.prime_eleven]

example : 2 ∉ Sude.apInterval 1 11 2 1 := by
  rw [Sude.mem_apInterval_iff 1 11 2 1 (by norm_num) (by norm_num) 2]
  norm_num

-- BMOR cutoff controls, including the exceptional q ≡ 2 (mod 4) rule.
example : Sude.bmorLimit 2 = 10 ^ 12 := by decide
example : Sude.bmorLimit 4 = 4 * 10 ^ 13 := by decide
example : Sude.bmorLimit 100 = 10 ^ 13 := by decide
example : Sude.bmorLimit 101 = 10 ^ 12 := by decide
example : Sude.bmorLimit 102 = 10 ^ 13 := by decide
example : Sude.bmorLimit 10002 = 10 ^ 12 := by decide
example : Sude.bmorLimit 100000 = 10 ^ 11 := by decide

-- The types retain the published assumptions; the axiom report alone does not show them.
#check Sude.bmor_even_available_pool_supply
#check Sude.bmor_two_available_pool_supply

#print axioms Sude.sum_swap_effect
#print axioms Sude.rectangleTrade_line_effect
#print axioms Sude.placementLineSum_row
#print axioms Sude.placementLineSum_column
#print axioms Sude.placementLineSum_main
#print axioms Sude.placementLineSum_anti
#print axioms Sude.rectangleTrade_rows
#print axioms Sude.rectangleTrade_columns
#print axioms Sude.rectangleTrade_main
#print axioms Sude.rectangleTrade_anti
#print axioms Sude.rectangleTrade_outside
#print axioms Sude.rectangleTrade_pool_preserved
#print axioms Sude.rectangleTrade_gap_positive
#print axioms Sude.undoRectangleTrade_rectangleTrade
#print axioms Sude.undoRectangleTrade_main
#print axioms Sude.undoRectangleTrade_anti
#print axioms Sude.centerCell_on_both_diagonals
#print axioms Sude.rectangleTrade_center_unchanged
#print axioms Sude.rectangleTrade_center_unchanged_of_main
#print axioms Sude.verticalSwap_row_effect
#print axioms Sude.verticalSwap_columns
#print axioms Sude.horizontalSwap_column_effect
#print axioms Sude.horizontalSwap_rows
#print axioms Sude.swapPlacement_diagonals_unchanged
#print axioms Sude.centerSwap_changes_both_diagonals
#print axioms Sude.rectangleTrade_other_cells_unchanged
#print axioms Sude.rectangleTrade_other_gaps_unchanged
#print axioms Sude.rectangleTrade_commute_disjoint
#print axioms Sude.rectangleTrade_main_then_anti
#print axioms Sude.rectangleTrade_main_then_anti_center

-- The single cell of order one belongs to both labelled diagonals.
example : ((0 : Fin 1), (0 : Fin 1)) ∈ Sude.mainCells 1 ∧
    ((0 : Fin 1), (0 : Fin 1)) ∈ Sude.antiCells 1 := by decide

-- An order-five main-diagonal rectangle has precisely the intended geometry.
example : ((0 : Fin 5), (0 : Fin 5)) ∈ Sude.mainCells 5 ∧
    ((0 : Fin 5), (0 : Fin 5)) ∉ Sude.antiCells 5 ∧
    ((0 : Fin 5), (2 : Fin 5)) ∉ Sude.mainCells 5 ∧
    ((0 : Fin 5), (2 : Fin 5)) ∉ Sude.antiCells 5 ∧
    ((1 : Fin 5), (0 : Fin 5)) ∉ Sude.mainCells 5 ∧
    ((1 : Fin 5), (0 : Fin 5)) ∉ Sude.antiCells 5 ∧
    ((1 : Fin 5), (2 : Fin 5)) ∉ Sude.mainCells 5 ∧
    ((1 : Fin 5), (2 : Fin 5)) ∉ Sude.antiCells 5 := by decide

#check Sude.rectangleTrade_main_then_anti

#print axioms Sude.RectanglePacking.next_ne_self
#print axioms Sude.RectanglePacking.nextTwo_ne_self
#print axioms Sude.RectanglePacking.nextTwo_ne_next
#print axioms Sude.RectanglePacking.rowSlot_injective
#print axioms Sude.RectanglePacking.columnSlot_injective
#print axioms Sude.RectanglePacking.designated_corner_geometry
#print axioms Sude.RectanglePacking.firstRow_secondColumn_off_diagonals
#print axioms Sude.RectanglePacking.secondRow_firstColumn_off_diagonals
#print axioms Sude.RectanglePacking.secondRow_secondColumn_off_diagonals
#print axioms Sude.RectanglePacking.rectangle_avoids_center
#print axioms Sude.RectanglePacking.rectangle_cells_disjoint
#print axioms Sude.RectanglePacking.rectangle_four_cells
#print axioms Sude.RectanglePacking.rp1_exact_packing
#print axioms Sude.RectanglePacking.packed_main_then_anti
#print axioms Sude.RectanglePacking.packed_main_then_anti_center

-- The sharp order n=2J+1 at J=3 supports arbitrary diagonal choices.
example (choice : Fin 3 → Bool) :
    Function.Injective (Sude.RectanglePacking.rowSlot (J := 3) (n := 7) (by decide)) ∧
    Function.Injective (Sude.RectanglePacking.columnSlot (J := 3) (n := 7) (by decide) choice) := by
  exact ⟨Sude.RectanglePacking.rowSlot_injective (by decide),
    Sude.RectanglePacking.columnSlot_injective (by decide) choice⟩

-- The size and cycle hypotheses are necessary for this construction.
example : ¬ (2 * 3 + 1 ≤ 6) := by decide
example : Sude.RectanglePacking.nextTwo 2 (0 : Fin 2) = 0 := by decide

#check Sude.RectanglePacking.rp1_exact_packing
#check Sude.RectanglePacking.packed_main_then_anti

#print axioms Sude.place_distinct_pool_entries
#print axioms Sude.place_distinct_pool_entries_preserving
#print axioms Sude.RectanglePacking.cornerSlot_injective
#print axioms Sude.RectanglePacking.place_packed_entries
#print axioms Sude.RectanglePacking.packed_trade_preserves_reserved
#print axioms Sude.RectanglePacking.place_packed_pairs_preserving
#print axioms Sude.RectanglePacking.place_and_trade_packed_pairs

#check Sude.RectanglePacking.place_and_trade_packed_pairs

#print axioms Sude.RectanglePacking.cornerSlot_card
#print axioms Sude.RectanglePacking.cornerSlot_range_iff

#print axioms Sude.binary_subset_sum
#print axioms Sude.binary_even_grid
#print axioms Sude.completeEvenGrid_insert
#print axioms Sude.verticalSwap_other_column
#print axioms Sude.verticalPairs_toggle_subset
#print axioms Sude.vertical_grid_correction
#print axioms Sude.vertical_binary_correction

-- Grid endpoints; these examples do not certify the finite prime supplies.
example : ∃ S : Finset ℕ, S ⊆ Finset.range 3 ∧
    (∑ j ∈ S, 2 ^ (j + 1)) = 14 := by
  exact Sude.binary_even_grid 3 14 (by decide) (by decide)

example : ∃ S : Finset ℕ, S ⊆ Finset.range 0 ∧
    (∑ j ∈ S, 2 ^ (j + 1)) = 0 := by
  exact Sude.binary_even_grid 0 0 (by decide) (by decide)

#check Sude.vertical_grid_correction
#check Sude.vertical_binary_correction


#print axioms Sude.three_term_multiple_three
#print axioms Sude.no_prime_triple_of_mod_three
#print axioms Sude.prime_pair_endpoints_disjoint
#print axioms Sude.two_pow_mod_three_ne_zero
#print axioms Sude.binary_prime_family_disjoint
#print axioms Sude.pairFootprint_card
#print axioms Sude.availablePairs_card_lower
#print axioms Sude.select_available_pairs
#print axioms Sude.pairEndpoint_injective
#print axioms Sude.place_pair_family_preserving

-- The lower bound and gap restrictions are material, not cosmetic.
example : ¬ Disjoint ({3, 5} : Finset ℕ) {5, 7} := by decide
example : ¬ Disjoint ({5, 11} : Finset ℕ) {11, 17} := by decide
example : Disjoint ({5, 7} : Finset ℕ) {11, 13} := by
  exact Sude.binary_prime_pair_endpoints_disjoint (j := 1) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
example : (Sude.pairFootprint {5, 11} 2).card = 4 := by decide

#check Sude.select_available_pairs
#check Sude.place_pair_family_preserving

#print axioms Sude.prime_count_succ_eq_oddPrefix_add_one
#print axioms Sude.prime_mem_pool_of_oddPrefix_card_le
#print axioms Sude.select_binary_pool_pairs

-- Tiny kernel-checked indexing controls; not the five FPF numerical certificates.
example : (Sude.oddPrimePrefix 13).card = 5 := by decide
example : 13 ∈ Sude.pool 3 := by
  exact Sude.prime_mem_pool_of_oddPrefix_card_le (B := 13) (by decide)
    (by decide) (by decide) (by decide) (by decide)

#check Sude.select_binary_pool_pairs

#print axioms Sude.Lucas.powMod_correct
#print axioms Sude.Lucas.prime_divisor_in_factor_bases
#print axioms Sude.Lucas.nodeValid_prime
#print axioms Sude.Lucas.checkNodes_sound
#print axioms Sude.Lucas.checkCertificate_sound
#print axioms Sude.Lucas.firstTargetNodes_accepted
#print axioms Sude.Lucas.firstTargets_prime
#print axioms Sude.Lucas.firstTarget_integer_controls

-- Failed or incomplete Lucas certificates must not pass.
example : Sude.Lucas.checkCertificate [⟨2, 1, []⟩, ⟨9, 2, [(2, 3)]⟩] = false := by
  decide +kernel
example : Sude.Lucas.checkCertificate [⟨3, 2, [(2, 1)]⟩] = false := by
  decide +kernel
example : Sude.Lucas.checkCertificate [⟨2, 1, []⟩, ⟨7, 3, [(2, 1)]⟩] = false := by
  decide +kernel

#print axioms Sude.Lucas.absDiff_cast
#print axioms Sude.Lucas.absDiff_cast_real
#print axioms Sude.Lucas.integer_radius_implies_real
#print axioms Sude.Lucas.targetRowValid_real_radius
#print axioms Sude.Lucas.Generated.R0000.rows_valid
#print axioms Sude.Lucas.Generated.R0003.rows_valid
#print axioms Sude.Lucas.Generated.firstHundred_orders
#print axioms Sude.Lucas.Generated.firstHundred_cover

-- Both endpoints of the exact odd-order coverage interval are included.
example : ∃ row ∈ Sude.Lucas.Generated.firstHundredRows, row.order = 2001 ∧
    Sude.Lucas.TargetRowValid row :=
  Sude.Lucas.Generated.firstHundred_cover 2001 (by decide) (by decide) (by decide)
example : ∃ row ∈ Sude.Lucas.Generated.firstHundredRows, row.order = 2199 ∧
    Sude.Lucas.TargetRowValid row :=
  Sude.Lucas.Generated.firstHundred_cover 2199 (by decide) (by decide) (by decide)
example : ¬ (2201 ≤ 2199) := by decide

#print axioms Sude.Lucas.Generated.R0009.rows_valid
#print axioms Sude.Lucas.Generated.first250_orders
#print axioms Sude.Lucas.Generated.first250_cover

example : ∃ row ∈ Sude.Lucas.Generated.first250Rows, row.order = 2499 ∧
    Sude.Lucas.TargetRowValid row :=
  Sude.Lucas.Generated.first250_cover 2499 (by decide) (by decide) (by decide)

#print axioms Sude.Lucas.targetList_length
#print axioms Sude.Lucas.targetList_sum
#print axioms Sude.Lucas.targetList_prime
#print axioms Sude.Lucas.placement_total
#print axioms Sude.Lucas.targetAt_prime
#print axioms Sude.Lucas.targetAt_odd
#print axioms Sude.Lucas.targetAt_radius
#print axioms Sude.Lucas.targetAt_sum
#print axioms Sude.Lucas.sum_rowSums
#print axioms Sude.Lucas.sum_columnSums
#print axioms Sude.Lucas.targetAt_axis_compatibility
#print axioms Sude.Lucas.pool_target_system

-- Line targets retain multiplicity, including when all target values agree.
example : Sude.Lucas.targetList ⟨3, 1, 1, 5, 7, 11⟩ = [5, 7, 11] := by decide
example : Sude.Lucas.targetList ⟨4, 1, 1, 5, 5, 5⟩ = [5, 5, 5, 5] := by decide
#check Sude.Lucas.pool_target_system

#print axioms Sude.Lucas.Generated.R0016.rows_valid
#print axioms Sude.Lucas.Generated.first425_orders
#print axioms Sude.Lucas.Generated.first425_cover
example : ∃ row ∈ Sude.Lucas.Generated.first425Rows, row.order = 2849 ∧
    Sude.Lucas.TargetRowValid row :=
  Sude.Lucas.Generated.first425_cover 2849 (by decide) (by decide) (by decide)

#print axioms Sude.LayerPacking.dense_allowed_matching
#print axioms Sude.LayerPacking.blockedColumns_card
#print axioms Sude.LayerPacking.blockedEdges_card
#print axioms Sude.LayerPacking.blockedColumns_transpose
#print axioms Sude.LayerPacking.physical_layer_matching
#print axioms Sude.LayerPacking.layerCell_injective
#print axioms Sude.LayerPacking.layer_row_eq
#print axioms Sude.LayerPacking.layer_column_eq
#print axioms Sude.LayerPacking.layer_balanced
#print axioms Sude.LayerPacking.layerCells_card
#print axioms Sude.LayerPacking.physical_balanced_layer
#print axioms Sude.LayerPacking.place_physical_balanced_layer
#print axioms Sude.LayerPacking.layer_load_update
#print axioms Sude.LayerPacking.physical_two_layers

-- Identity edges reuse their two cells, hence the derangement hypothesis matters.
example : Sude.LayerPacking.layerCell (Equiv.refl (Fin 1)) (Equiv.refl (Fin 1)) (0, false) =
    Sude.LayerPacking.layerCell (Equiv.refl (Fin 1)) (Equiv.refl (Fin 1)) (0, true) := rfl
example : ¬ (4 * 0 + 8 < 8) := by decide
#check Sude.LayerPacking.place_physical_balanced_layer
#check Sude.LayerPacking.physical_two_layers

#print axioms Sude.LayerPacking.pack_finite_layers
#print axioms Sude.LayerPacking.PackedLayers.reserved_disjoint
#print axioms Sude.LayerPacking.PackedLayers.pairwise_disjoint
#print axioms Sude.LayerPacking.PackedLayers.row_balance
#print axioms Sude.LayerPacking.PackedLayers.column_balance
#print axioms Sude.LayerPacking.PackedLayers.sequenceCell_injective
#print axioms Sude.LayerPacking.PackedLayers.install_gap_values
#print axioms Sude.LayerPacking.pack_and_install_finite_layers
#print axioms Sude.LayerPacking.antiSum_transpose
#print axioms Sude.LayerPacking.PackedLayers.transposed_support_safe
#print axioms Sude.LayerPacking.pack_and_install_column_layers
#print axioms Sude.LayerPacking.PackedLayers.union_load
#print axioms Sude.LayerPacking.pack_and_install_two_networks
#print axioms Sude.LayerPacking.pb9_capacity_for_two_networks

-- Empty sequences keep the existing reservation and have zero support.
example (reserved : Finset (Sude.Cell 1)) : Sude.LayerPacking.PackedLayers reserved [] :=
  Sude.LayerPacking.PackedLayers.nil reserved
example : (Sude.LayerPacking.layersSupport ([] : List (Sude.LayerPacking.Layer 1))).card = 0 := by decide
-- The single cell is simultaneously on both labelled diagonals after transpose.
example (a : Sude.Cell 1 ≃ Fin (1 * 1)) :
    Sude.antiSum (Sude.LayerPacking.transposePlacement a) = Sude.antiSum a :=
  Sude.LayerPacking.antiSum_transpose a
#check Sude.LayerPacking.pack_and_install_two_networks
#check Sude.LayerPacking.pb9_capacity_for_two_networks

#print axioms Sude.rowNetwork_toggle_subset
#print axioms Sude.columnNetwork_toggle_subset
#print axioms Sude.LayerPacking.PackedLayers.rowPairs
#print axioms Sude.LayerPacking.PackedLayers.columnPairs
#print axioms Sude.layerTransfer_sum_zero
#print axioms Sude.selectedTransfers_sum_zero
#print axioms Sude.selectedTransfers_even
#print axioms Sude.toggle_two_installed_networks
#print axioms Sude.repair_two_networks_of_selected_transfers
#print axioms Sude.square_of_selected_network_transfers
#print axioms Sude.binary_gap_total
#print axioms Sude.evenGridCenter_midpoint_error
#print axioms Sude.centered_even_grid
#print axioms Sude.vertical_centered_reference

-- Negative signed correction at the lower endpoint of a complete grid.
example : ∃ T : Finset ℕ, T ⊆ Finset.range 3 ∧
    ((∑ k ∈ T, 2 ^ (k + 1) : ℕ) : ℤ) - Sude.evenGridCenter 14 = -6 := by
  have hgrid : Sude.CompleteEvenGrid (Finset.range 3) (fun k => 2 ^ (k + 1)) 14 := by
    intro t ht heven
    exact Sude.binary_even_grid 3 t heven (by simpa using ht)
  exact Sude.centered_even_grid _ _ 14 hgrid (-6) (by norm_num)
    (by norm_num [Sude.evenGridCenter]) (by norm_num [Sude.evenGridCenter])
#check Sude.toggle_two_installed_networks
#check Sude.square_of_selected_network_transfers
#check Sude.vertical_centered_reference

#print axioms Sude.biUnion_inter_block
#print axioms Sude.simultaneous_centered_subsets
#print axioms Sude.sum_by_disjoint_blocks
#print axioms Sude.rowNetwork_subset_difference
#print axioms Sude.rowNetwork_centered_transfers
#print axioms Sude.twoNetworks_centered_transfers
#print axioms Sude.evenGridCenter_pays_capacity
#print axioms Sude.scaled_flow_within_center
#print axioms Sude.fc2k_floor_capacity_gate
#print axioms Sude.twoNetworks_realize_bounded_integer_flows
#print axioms Sude.twoNetworks_square_from_integral_flows

-- Both signs and the capacity endpoint are represented; an over-capacity
-- demand is not justified by the stated sufficient bound.
example : 2 * (9 / 2) ≤ Sude.evenGridCenter 18 := by decide
example : ¬ (2 * (10 / 2) ≤ Sude.evenGridCenter 18) := by decide
example : 200 * 994 < 199 * (2000 / 2) :=
  Sude.fc2k_floor_capacity_gate 2000 994 (by decide) (by decide)
#check Sude.twoNetworks_centered_transfers
#check Sude.twoNetworks_realize_bounded_integer_flows
#check Sude.twoNetworks_square_from_integral_flows


#print axioms Sude.zero_total_cut_demand
#print axioms Sude.edgeTransfer_cut_bound
#print axioms Sude.bounded_flow_cut_inequality
#print axioms Sude.edge_divergence_sum_zero
#print axioms Sude.bounded_flow_necessary_conditions
#print axioms Sude.scaled_cut_capacity
#print axioms Sude.fc2k_cut_inequalities

-- Two parallel edges cross the cut and a loop does not.
example : (Sude.cutEdges (fun _ : Fin 2 => (0 : Fin 2))
    (fun _ : Fin 2 => (1 : Fin 2)) {0}).card = 2 := by decide
example : (Sude.cutEdges (fun _ : Fin 1 => (0 : Fin 2))
    (fun _ : Fin 1 => (0 : Fin 2)) {0}).card = 0 := by decide
example : ¬ (400000 * 999 < 199 * 999 * 2000) := by decide
#check Sude.fc2k_cut_inequalities
#check Sude.bounded_flow_necessary_conditions


#print axioms Sude.closed_cut_edge_transfer
#print axioms Sude.closed_cut_residual_nonpos
#print axioms Sude.residual_reachable_closed
#print axioms Sude.residual_positive_reaches_negative
#print axioms Sude.apply_unit_adjustment
#print axioms Sude.unit_transfer_decreases_mass
#print axioms Sude.residual_arc_unit_adjustment
#print axioms Sude.routing_by_unit_augmentations
#print axioms Sude.routing_of_residual_path_adjustments

-- At capacity an edge has no residual arc in its forward direction,
-- while its reverse direction remains available.
example : ¬ Sude.residualArc (fun _ : Fin 1 => (0 : Fin 2))
    (fun _ : Fin 1 => (1 : Fin 2)) (fun _ => (3 : ℤ)) 3 0 1 := by
  intro ⟨e, h⟩
  fin_cases e
  norm_num at h
example : Sude.residualArc (fun _ : Fin 1 => (0 : Fin 2))
    (fun _ : Fin 1 => (1 : Fin 2)) (fun _ => (3 : ℤ)) 3 1 0 := by
  exact ⟨0, Or.inr ⟨rfl, rfl, by decide⟩⟩
example : Sude.residualMass (fun x : Fin 2 => if x = 0 then 1 else -1) = 2 := by decide
#check Sude.residual_positive_reaches_negative
#check Sude.routing_of_residual_path_adjustments


#print axioms Sude.simpleDirectedPath_of_reachable
#print axioms Sude.simple_residual_path_adjustment
#print axioms Sude.residual_path_adjustment
#print axioms Sude.integer_flow_of_cut_inequalities
#print axioms Sude.fc2k_integral_flow
#print axioms Sude.twoNetworks_realize_cut_demands
#print axioms Sude.twoNetworks_realize_fc2k_demands

-- One unit crosses a single edge; the theorem itself constructs the flow.
example : ∃ f : Fin 1 → ℤ, (∀ e, |f e| ≤ 1) ∧
    ∀ v : Fin 2, (∑ e : Fin 1, Sude.edgeTransfer (fun _ => 0) (fun _ => 1) f e v) =
      (if v = 0 then 1 else -1) := by
  apply Sude.integer_flow_of_cut_inequalities (fun _ : Fin 1 => (0 : Fin 2))
    (fun _ : Fin 1 => (1 : Fin 2)) (fun v => if v = 0 then 1 else -1) 1
  · decide
  · decide
#check Sude.integer_flow_of_cut_inequalities
#check Sude.twoNetworks_realize_fc2k_demands

#print axioms Sude.extend_even_gap_chain
#print axioms Sude.extend_even_gap_chain_actual_total
#print axioms Sude.binary_prefix_actual_grid
#print axioms Sude.oriented_pairs_midpoint_identity
#print axioms Sude.oriented_pairs_midpoint_error
#print axioms Sude.complete_grid_has_true_midpoint_reference
#print axioms Sude.oddPrime_odd
#print axioms Sude.rowSum_odd
#print axioms Sude.columnSum_odd
#print axioms Sude.halfLineDemand_system
#print axioms Sude.fc2k_square_of_ftt_targets

-- Signed half-demands include negative corrections; the midpoint bound
-- includes the lower midpoint for a pair with gap two.
example : Sude.halfLineDemand 7 11 = -2 := by decide
example : 0 ≤ 2 * (∑ k ∈ ({0} : Finset ℕ),
    (if k ∈ (∅ : Finset ℕ) then (3 : ℤ) else 5)) -
    (∑ _k ∈ ({0} : Finset ℕ), ((3 : ℤ) + 5)) ∧
    2 * (∑ k ∈ ({0} : Finset ℕ),
    (if k ∈ (∅ : Finset ℕ) then (3 : ℤ) else 5)) -
    (∑ _k ∈ ({0} : Finset ℕ), ((3 : ℤ) + 5)) ≤ 2 := by
  exact Sude.oriented_pairs_midpoint_error {0} ∅ (fun _ => 3) (fun _ => 5)
    (fun _ => 2) (by decide) (by decide) (by decide) (by decide)
#check Sude.fc2k_square_of_ftt_targets

#print axioms Sude.pool_eq_prefix
#print axioms Sude.poolTotal_eq_prefix_sum
#print axioms Sude.poolMaximum_eq_of_oddPrefix_count
#print axioms Sude.pool_identities_of_oddPrefix_certificate
#print axioms Sude.canonicalPrimeBase_complete
#print axioms Sude.passesPrimeBase_iff_prime
#print axioms Sude.checkedOddSegment_additive
#print axioms Sude.checkedOddSegment_spec
#print axioms Sude.checked_prefix_pool_identities
#print axioms Sude.Lucas.Generated.first_ftt_max_prime
#print axioms Sude.first_ftt_pool_identities_of_verified_prefix

-- A small end-to-end acceptance test of the same exact prefix interface.
-- This does not establish any tail order's prefix count or sum.
example : Sude.poolMaximum 2 = 11 ∧ Sude.Lucas.poolTotal 2 = 26 := by
  apply Sude.checked_prefix_pool_identities (Sude.canonicalPrimeBase 4) 4 2 11 26
  · exact Sude.canonicalPrimeBase_complete 4
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
#check Sude.first_ftt_pool_identities_of_verified_prefix

#print axioms Sude.checkFactorRow_spec
#print axioms Sude.factorSurvivors_spec
#print axioms Sude.factorSurvivors_nodup
#print axioms Sude.factor_certificate_segment
#print axioms Sude.factor_certificate_count_sum
#print axioms Sude.GeneratedPrefix.firstTailPrimeSegment_count_sum

-- Composite witnesses must be proper, and an alleged prime must be certified.
example : Sude.checkFactorRow [] 9 3 = true := by decide +kernel
example : Sude.checkFactorRow [] 9 1 = false := by decide +kernel
example : Sude.checkFactorRow [] 9 9 = false := by decide +kernel
example : Sude.checkFactorRow [] 9 0 = false := by decide +kernel
#check Sude.GeneratedPrefix.firstTailPrimeSegment_count_sum

#print axioms Sude.oddCeiling_spec
#print axioms Sude.firstOddMark_source_formula
#print axioms Sude.firstOddMark_progression
#print axioms Sude.firstMarkIndex_value
#print axioms Sude.markingCount_spec
#print axioms Sude.markingIndices_spec
#print axioms Sude.unmarkedIndices_spec
#print axioms Sude.markedSieveValues_spec
#print axioms Sude.markedSieve_prefix
#print axioms Sude.markedSieve_pool_identities
#print axioms Sude.firstTailMarked_count_sum

-- p itself is never marked; exact starts, a nonempty source interval, and
-- a first mark past the interval all exercise boundary conditions.
example : Sude.firstOddMark 3 3 = 9 := by decide +kernel
example : Sude.firstOddMark 7 67939501 = 67939501 := by decide +kernel
example : Sude.markingCount 3 67939501 54 = 18 := by decide +kernel
example : Sude.markingCount 8243 67939501 54 = 0 := by decide +kernel
example : (Sude.markedSieveValues (Sude.canonicalPrimeBase 4) 3 5).card = 4 := by decide +kernel
example : (∑ p ∈ Sude.markedSieveValues (Sude.canonicalPrimeBase 4) 3 5, p) = 26 := by decide +kernel
#check Sude.markedSieve_pool_identities

#print axioms Sude.markingSegmentSummary_spec
#print axioms Sude.markingSegmentScan_append
#print axioms Sude.uniformSegmentWidths_sum
#print axioms Sude.oddPrimeSegment_additive
#print axioms Sude.markingSegmentScan_spec
#print axioms Sude.markingSegmentScan_prefix
#print axioms Sude.markingSegmentScan_pool_identities
#print axioms Sude.uniformScan_pool_identities
#print axioms Sude.first512PrimeSegment_count_sum
#print axioms Sude.latePrefixPrimeSegment_count_sum

-- Empty and remainder segments preserve their exact total width.
example : (Sude.uniformSegmentWidths 0 16).sum = 0 := Sude.uniformSegmentWidths_sum 0 16
example : (Sude.uniformSegmentWidths 19 16).sum = 19 := Sude.uniformSegmentWidths_sum 19 16
#check Sude.uniformScan_pool_identities

#print axioms Sude.encodeMarkBits_spec
#print axioms Sude.canonicalPrimeBaseList_complete
#print axioms Sude.markingIndexList_spec
#print axioms Sude.segmentMarkBits_spec
#print axioms Sude.bitsetUnmarked_eq
#print axioms Sude.bitsetSegmentSummary_spec
#print axioms Sude.bitsetSegmentScan_eq
#print axioms Sude.bitsetSegmentScan_append
#print axioms Sude.bitsetScan_pool_identities
#print axioms Sude.bitsetFirst4096_prime_count_sum

-- Duplicate marks do not toggle a bit off; an unlisted index stays clear.
example : (Sude.encodeMarkBits [1, 1, 4]).testBit 1 = true := by decide +kernel
example : (Sude.encodeMarkBits [1, 1, 4]).testBit 2 = false := by decide +kernel
#check Sude.bitsetFirst4096_prime_count_sum
#print axioms Sude.bitsetScan_count_sum
#print axioms Sude.combineOddPrimeSegments
#print axioms Sude.bitsetNext4096_prime_count_sum
#print axioms Sude.bitsetFirst8192_prime_count_sum
#check Sude.bitsetFirst8192_prime_count_sum

#print axioms Sude.streamBitSummary_spec
#print axioms Sude.streamBitSummary_eq
#print axioms Sude.streamingSegmentSummary_eq
#print axioms Sude.streamingSegmentScan_eq
#print axioms Sude.streamingScan_pool_identities
#print axioms Sude.streamingFirst16384_prime_count_sum

-- A zero-width segment is empty; bits 1 and 3 exclude exactly 5 and 9.
example : Sude.streamBitSummary 10 3 0 = (0, 0) := by decide +kernel
example : Sude.streamBitSummary 10 3 4 = (2, 10) := by decide +kernel
#check Sude.streamingFirst16384_prime_count_sum

#print axioms Sude.relevantMarkingBase_bits_eq
#print axioms Sude.prunedSegmentSummary_eq
#print axioms Sude.prunedSegmentScan_eq
#print axioms Sude.prunedFirst8192_prime_count_sum
#print axioms Sude.prunedNext8192_prime_count_sum
#print axioms Sude.prunedFirst32768_prime_count_sum

-- The square of 5 is excluded at the upper endpoint but included one
-- candidate later; duplicate base entries remain harmless.
example : Sude.relevantMarkingBase [3, 5, 5, 7] 3 11 = [3] := by decide +kernel
example : Sude.relevantMarkingBase [3, 5, 5, 7] 3 12 = [3, 5, 5] := by decide +kernel
#check Sude.prunedFirst32768_prime_count_sum

#print axioms Sude.repeated_difference_double_pair
#print axioms Sude.repeated_difference_after_deletions
#print axioms Sude.even_span_card_le
#print axioms Sude.even_real_span_int_bounds
#print axioms Sude.even_real_span_card_le
#print axioms Sude.real_square_gate_implies_floor_gate
#print axioms Sude.repeated_even_difference_of_span
#print axioms Sude.select_disjoint_double_pairs
#print axioms Sude.select_pool_double_pairs_after_deletions
#print axioms Sude.select_pool_double_pairs_fc2k
#print axioms Sude.doublePairSequenceEndpoint_injective
#print axioms Sude.install_double_pair_sequence
#print axioms Sude.installed_double_pair_gaps

-- The lower endpoint may be odd; parity still gives H+1 possible gaps.
example : ({2, 4} : Finset ℕ).card ≤ 3 := by
  apply Sude.even_span_card_le _ 1 2
  · intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl <;> omega
  · intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl <;> omega

#check Sude.select_pool_double_pairs_after_deletions
#check Sude.install_double_pair_sequence

-- Exercise sequential selection on ordered stocks after budgeting one block.
example : ∃ blocks : List Sude.DoublePair, blocks.length = 1 ∧
    (∀ b ∈ blocks, b.valid (Finset.range 6) (Finset.Ico 10 16)) ∧
    blocks.Pairwise (fun b c => Disjoint b.footprint c.footprint) := by
  apply Sude.select_disjoint_double_pairs (Finset.range 6) (Finset.Ico 10 16)
    (Finset.Icc 5 15) 4 11 1
  · intro a ha b hb
    simp only [Finset.mem_range] at ha
    simp only [Finset.mem_Ico] at hb
    omega
  · intro a ha b hb
    simp only [Finset.mem_range] at ha
    simp only [Finset.mem_Ico] at hb
    simp only [Finset.mem_Icc]
    omega
  · decide
  · decide
  · decide
  · decide

#print axioms Sude.bridgeSpan_source
#print axioms Sude.bridgeGapLower_source
#print axioms Sude.bridge_window_geometry
#print axioms Sude.bridge_cross_gap
#print axioms Sude.pool_ordered_difference_even
#print axioms Sude.bridge_select_pool_blocks
#print axioms Sude.bridge_extends_grid_from_lower_bound
#print axioms Sude.bmor_bridge_interval_stock
#print axioms Sude.bmor_bridge_stocks
#print axioms Sude.bmor_bridge_select_pool_blocks
#print axioms Sude.bridgeIteration_terminates
#print axioms Sude.bridgeIteration_preserves_grids
#print axioms Sude.bridgeIteration_completes_grid

-- A rational bridge checks the half-open endpoints and exact increment.
example : Sude.bridgeLowStart 100 30 = 35 ∧
    Sude.bridgeLowEnd 100 30 = 359 / 10 ∧
    Sude.bridgeHighStart 100 30 = 641 / 10 ∧
    Sude.bridgeHighEnd 100 30 = 65 ∧
    Sude.bridgeGapLower 100 30 = 141 / 5 := by
  norm_num [Sude.bridgeLowStart, Sude.bridgeLowEnd, Sude.bridgeHighStart,
    Sude.bridgeHighEnd, Sude.bridgeGapLower, Sude.bridgeWidth, Sude.bridgeSpan]

#check Sude.bmor_bridge_select_pool_blocks
#check Sude.bridgeIteration_completes_grid

#print axioms Sude.stagedReservation_inter_card_le
#print axioms Sude.bridge_lower_upper_disjoint
#print axioms Sude.doubleBatchLow_card_le
#print axioms Sude.doubleBatchHigh_card_le
#print axioms Sude.doubleBatch_avoids_reservation
#print axioms Sude.bmor_bridge_stage_from_overlap_budget
#print axioms Sude.select_bridge_stage_sequence
#print axioms Sude.bridgeStageSequence_disjoint
#print axioms Sude.prime_overlap_card_le_geometric
#print axioms Sude.bridgeStageBudget_of_geometric
#print axioms Sude.select_bridge_until_covered
#print axioms Sude.selectedBridgeGap_bounds
#print axioms Sude.selectedBridgeBatches_grow_grid
#print axioms Sude.select_bridge_and_grow_grids

#check Sude.select_bridge_and_grow_grids

-- Touching endpoints of half-open windows do not count as overlap.
example : Sude.geometricallyOverlappingWindows ({0, 1, 2} : Finset ℕ)
    (fun i => (i : ℝ)) (fun i => (i : ℝ) + 1) 1 2 = {1} := by
  classical
  ext i
  simp only [Sude.geometricallyOverlappingWindows, Finset.mem_filter,
    Finset.mem_insert, Finset.mem_singleton]
  norm_num <;> omega

#print axioms Sude.bridgeStageBlock_same_stage_disjoint
#print axioms Sude.bridgeStageBlock_different_stage_disjoint
#print axioms Sude.bridgeStageEndpoint_injective
#print axioms Sude.bridgeStageEndpoint_pool_avoids
#print axioms Sude.bridgeStageBlock_gap
#print axioms Sude.install_bridge_stage_blocks
#print axioms Sude.bridge_stage_cells_of_capacity
#print axioms Sude.install_bridge_stage_blocks_of_capacity
#print axioms Sude.select_grow_install_bridge_stages

-- Four slots fit exactly in a two-by-two square with no reservations.
example : ∃ cells : (Fin 1 × Fin 1) × Fin 4 → Sude.Cell 2,
    Function.Injective cells ∧ ∀ x, cells x ∉ (∅ : Finset (Sude.Cell 2)) := by
  apply Sude.bridge_stage_cells_of_capacity 1 1
  decide

#check Sude.select_grow_install_bridge_stages

#print axioms Sude.packedRectangleCorner_injective
#print axioms Sude.install_selected_bridge_rectangles
#print axioms Sude.unselected_bridge_endpoints_remain_available
#print axioms Sude.selected_bridge_main_then_anti
#print axioms Sude.packedTradeSequence_fixes_outside
#print axioms Sude.packedTradeSequence_effect
#print axioms Sude.selected_bridge_trade_sequence
#print axioms Sude.selected_bridge_orientation_difference
#print axioms Sude.install_and_trade_selected_bridge_rectangles

#check Sude.install_and_trade_selected_bridge_rectangles
#check Sude.selected_bridge_orientation_difference

#print axioms Sude.bridgeDiagonalBlockSelect_injective
#print axioms Sude.bridgeDiagonalRectangle_injective
#print axioms Sude.bridgeDiagonalChoice_at
#print axioms Sude.bridgeDiagonalChoice_outside
#print axioms Sude.bridgeDiagonal_index_counts
#print axioms Sude.fc2k_diagonal_blocks_fit
#print axioms Sude.install_allocated_bridge_diagonal_blocks

#check Sude.install_allocated_bridge_diagonal_blocks

#print axioms Sude.bridgeOrdinaryBlockIndex_injective
#print axioms Sude.bridgeOrdinarySlot_injective
#print axioms Sude.bridgeOrdinarySlot_ne_diagonal
#print axioms Sude.bridgeOrdinaryEndpoint_injective
#print axioms Sude.bridgeOrdinaryEndpoint_ne_diagonal
#print axioms Sude.bridgeOrdinary_pair_gap
#print axioms Sude.fc2k_bridge_ordinary_blocks_fit
#print axioms Sude.bridgeNetworkValue_injective
#print axioms Sude.bridgeNetworkValues_separate
#print axioms Sude.bridgeNetworkValue_gap
#print axioms Sude.pack_and_install_bridge_ordinary_networks
#print axioms Sude.packedRectangleSupport_row_load
#print axioms Sude.packedRectangleSupport_column_load
#print axioms Sude.packedRectangle_joint_reservation_load
#print axioms Sude.allocatedBridge_free_of_other_rectangles
#print axioms Sude.allocatedBridge_joint_reservation_load
#print axioms Sude.fc2k_bridge_pb9_matching_capacity
#print axioms Sude.install_bridge_diagonal_and_ordinary_networks
#print axioms Sude.allocatedBridgeTrades_preserve_networks
#print axioms Sude.allocatedBridgeOrientations_preserve_networks

-- The first lower-tail order has exactly enough blocks for this allocation.
example : 4 * 6 + 3 * 2001 = (6 * (2001 + 8)) / 2 := by decide +kernel

#check Sude.install_bridge_diagonal_and_ordinary_networks
#check Sude.allocatedBridgeTrades_preserve_networks
#check Sude.allocatedBridgeOrientations_preserve_networks

#print axioms Sude.completeEvenGrid_finite_relabel
#print axioms Sude.bridgeStageLayerIndex_injective
#print axioms Sude.bridgeNetworkGap_stage
#print axioms Sude.bridgeNetworkGap_cast
#print axioms Sude.bridgeRepeatedPermutations_derange
#print axioms Sude.bridgeStageLayer_endpoints
#print axioms Sude.bridgePhysicalLabel_injective
#print axioms Sude.bridgePhysicalLabel_support
#print axioms Sude.selectedBridgeBatches_physical_grid
#print axioms Sude.selectedBridgeBatches_packed_grid
#print axioms Sude.bridgePackedPair_endpoints

example : Sude.bridgeStageLayerIndex (J := 2) (r := 3) (m := 6) rfl
    (1 : Fin 2) (2 : Fin 3) = (5 : Fin 6) := by decide +kernel

#check Sude.selectedBridgeBatches_packed_grid
#check Sude.bridgePackedPair_endpoints

#print axioms Sude.RowNetworkPairs.rebase
#print axioms Sude.RowNetworkPairs.join
#print axioms Sude.rowNetworkPairs_disjoint_of_reservation
#print axioms Sude.joinReservedPackedPairs
#print axioms Sude.joinedBridgeGrid_disjoint
#print axioms Sude.selectedBridgeBatches_joined_grid
#print axioms Sude.joinedBridgeGrid_endpoints
#print axioms Sude.joinedBridgeCenteredNetwork
#print axioms Sude.joinedBridgeCentered_radius_covers

#check Sude.joinedBridgeCenteredNetwork

#print axioms Sude.prefixPairBlock_grid
#print axioms Sude.prefixPairBlock_disjoint
#print axioms Sude.prefixPairBlock_endpoints
#print axioms Sude.prefixRadius_even

#check Sude.prefixPairBlock_grid

#print axioms Sude.prefixDiagonalPairIndex_injective
#print axioms Sude.prefixOrdinaryPairIndex_injective
#print axioms Sude.prefixOrdinary_ne_diagonal
#print axioms Sude.fc2k_prefix_pair_allocation
#print axioms Sude.prefixRectangleInput_injective
#print axioms Sude.prefixOrdinaryInput_ne_rectangle
#print axioms Sude.install_prefix_diagonal_rectangles
#print axioms Sude.prefixNetworkInput_injective
#print axioms Sude.prefixNetworkInputs_separate
#print axioms Sude.prefixNetwork_pair_gap
#print axioms Sude.install_prefix_ordinary_networks
#print axioms Sude.install_prefix_diagonal_and_ordinary
#print axioms Sude.prefixPhysicalStageSlot_injective
#print axioms Sude.prefixNetworkGap_stage
#print axioms Sude.prefixNetworkGap_cast
#print axioms Sude.installedPrefixCenteredNetwork

example : (4 * 6) * 2 + 2 * (3 * 2001) = 6 * (2001 + 8) := by decide +kernel

#check Sude.install_prefix_diagonal_and_ordinary
#check Sude.installedPrefixCenteredNetwork

#print axioms Sude.prefixAllInput_injective
#print axioms Sude.prefixAllInput_bijective
#print axioms Sude.prefixNetworkInput_stage
#print axioms Sude.installed_prefix_covers_population
#print axioms Sude.installed_prefix_population_exact
#print axioms Sude.prefixPopulation_card

#check Sude.installed_prefix_population_exact

#print axioms Sude.half_lt_log_fifteen_eighths
#print axioms Sude.finitePrefix_log_index_gt_fifteen
#print axioms Sude.finitePrefix_L_below_poolMaximum
#print axioms Sude.finitePrefix_C27_below_poolMaximum
#print axioms Sude.finitePrefix_T_below_poolMaximum
#print axioms Sude.finitePrefix_L_prime_in_pool
#print axioms Sude.finitePrefix_C27_prime_in_pool
#print axioms Sude.finitePrefix_T_prime_in_pool
#print axioms Sude.GeneratedPrefix.firstFamilyNodes_checked
#print axioms Sude.GeneratedPrefix.firstFamilyEndpoint_injective
#print axioms Sude.GeneratedPrefix.firstFamilyEndpoint_prime
#print axioms Sude.GeneratedPrefix.firstFamilyEndpoint_in_pool
#print axioms Sude.GeneratedPrefix.firstFamilyPoolValues_injective
#print axioms Sude.GeneratedPrefix.firstFamilyPoolValues_gap

#check Sude.GeneratedPrefix.firstFamilyEndpoint_in_pool
#check Sude.GeneratedPrefix.firstFamilyPoolValues_gap

#print axioms Sude.count_log_le_thetaAP_interval
#print axioms Sude.bmor_prime_interval_upper
#print axioms Sude.prime_count_split
#print axioms Sude.log_scaled_rational_lower
#print axioms Sude.prime_count_150000000_upper
#print axioms Sude.prime_count_450000000_upper
#print axioms Sude.finitePrefix_M_below_poolMaximum
#print axioms Sude.finitePrefix_H_below_poolMaximum
#print axioms Sude.fpf_profile_cover
#print axioms Sude.fpf_profile_prime_in_pool

#check Sude.fpf_profile_prime_in_pool

#print axioms Sude.DistinctTrie.contains_insert_self
#print axioms Sude.DistinctTrie.contains_insert_mono
#print axioms Sude.distinctTrieAux_sound
#print axioms Sude.finiteDistinctCheck_sound
#print axioms Sude.finiteDistinctCheck_equiv_sound
#print axioms Sude.GeneratedPrefix.L8.endpoint_injective
#print axioms Sude.GeneratedPrefix.L8.endpoint_prime
#print axioms Sude.GeneratedPrefix.L8.endpoint_in_pool
#print axioms Sude.GeneratedPrefix.L8.poolValues_injective
#print axioms Sude.GeneratedPrefix.L8.poolValues_gap

-- A bounded trie may reject distinct values with the same low bits.
example : Sude.finiteDistinctCheck 2 (![0, 4] : Fin 2 → ℕ) = false := by decide +kernel
example : Sude.finiteDistinctCheck 2 (![0, 1, 2] : Fin 3 → ℕ) = true := by decide +kernel
example : Sude.finiteDistinctCheck 2 (![0, 1, 0] : Fin 3 → ℕ) = false := by decide +kernel

#check Sude.GeneratedPrefix.L8.poolValues_gap

#print axioms Sude.DistinctTrie.advance_append
#print axioms Sude.DistinctTrie.advance_implies_check
#print axioms Sude.DistinctTrie.advance_of_check
#print axioms Sude.VerifiedTrieChunks.advance_flatten
#print axioms Sude.VerifiedTrieChunks.nodup
#print axioms Sude.GeneratedPrefix.L32Distinct.checkpoints
#print axioms Sude.GeneratedPrefix.L32Distinct.endpoints_nodup
#print axioms Sude.GeneratedPrefix.L32Distinct.endpoint_injective

-- A repeated value in a later chunk is rejected against the prior state.
example : Sude.distinctTrieAux 4 [3, 1] (Sude.DistinctTrie.insertAll 4 .empty [1, 2]) = false := by
  decide +kernel
example : Sude.distinctTrieAux 4 [3, 4] (Sude.DistinctTrie.insertAll 4 .empty [1, 2]) = true := by
  decide +kernel

#check Sude.GeneratedPrefix.L32Distinct.endpoint_injective

#print axioms Sude.GeneratedPrefix.L32Primes.endpoint_prime
#print axioms Sude.GeneratedPrefix.L32Primes.endpoint_bounds
#print axioms Sude.GeneratedPrefix.L32Primes.endpoint_in_pool
#print axioms Sude.GeneratedPrefix.L32Primes.poolValues_injective
#print axioms Sude.GeneratedPrefix.L32Primes.poolValues_gap

#check Sude.GeneratedPrefix.L32Primes.poolValues_gap

#print axioms Sude.VerifiedTrieChunks.append
#print axioms Sude.sumFamily_injective_of_nodup
#print axioms Sude.GeneratedPrefix.L64Extra.both_enumerations_nodup
#print axioms Sude.GeneratedPrefix.L64Extra.extra_prime
#print axioms Sude.GeneratedPrefix.L64.endpoint_injective
#print axioms Sude.GeneratedPrefix.L64.endpoint_prime
#print axioms Sude.GeneratedPrefix.L64.endpoint_in_pool
#print axioms Sude.GeneratedPrefix.L64.poolValues_injective
#print axioms Sude.GeneratedPrefix.L64.poolValues_gap

#check Sude.GeneratedPrefix.L64.poolValues_gap

#print axioms Sude.prefixTruncationIndex_injective
#print axioms Sude.truncatePrefixValues_injective
#print axioms Sude.truncatePrefixValues_gap
#print axioms Sude.truncatePrefixValues_suffix_free
#print axioms Sude.finitePrefix_order_size
#print axioms Sude.truncatePrefixValues_card

#check Sude.truncatePrefixValues_suffix_free

#print axioms Sude.prefixStageBlock_of_certificate
#print axioms Sude.PrefixStageBlock.append
#print axioms Sude.PrefixStageBlock.L_pool_matching
#print axioms Sude.GeneratedPrefix.LStage0.valid
#print axioms Sude.GeneratedPrefix.LStage0.pool_matching

#check Sude.GeneratedPrefix.LStage0.pool_matching

-- The diagonal split is exact at the 2d boundary.
example : Sude.bridgeDiagonalChoice (J := 1) (d := 1) (L := 4) (by decide) (fun _ => false)
    (Sude.bridgeDiagonalRectangle (J := 1) (d := 1) (L := 4) (by decide)
      (finProdFinEquiv ((0 : Fin 1), (1 : Fin 4)))) = true := by
  rw [Sude.bridgeDiagonalChoice_at]
  decide

example : Sude.bridgeDiagonalChoice (J := 1) (d := 1) (L := 4) (by decide) (fun _ => true)
    (Sude.bridgeDiagonalRectangle (J := 1) (d := 1) (L := 4) (by decide)
      (finProdFinEquiv ((0 : Fin 1), (2 : Fin 4)))) = false := by
  rw [Sude.bridgeDiagonalChoice_at]
  decide

#print axioms Sude.fc2k_large_cut_gate
#check Sude.fc2k_large_cut_gate
#print axioms Sude.fc2k_small_cut_gate
#print axioms Sude.fc2k_entropy_half_gate
#print axioms Sude.fc2k_entropy_small_gate
#check Sude.fc2k_small_cut_gate
#check Sude.fc2k_entropy_half_gate
#check Sude.fc2k_entropy_small_gate

#print axioms Sude.fc2k_curvature_pos
#print axioms Sude.fc2k_entropy_hasDerivAt
#print axioms Sude.fc2k_entropySlope_hasDerivAt
#print axioms Sude.fc2k_entropy_convex
#print axioms Sude.fc2k_entropy_interval_gate
#check Sude.fc2k_entropy_interval_gate

#print axioms Sude.factorial_le_three_numDerangements
#print axioms Sude.card_triples_le_27_derangements
#print axioms Sude.exists_derangement_triple_avoiding_two
#check Sude.exists_derangement_triple_avoiding_two

#print axioms Sude.permutationOutgoing_card_eq_incoming
#print axioms Sude.permutationFamily_cut_card
#print axioms Sude.permutationCutFailure_small_side
#print axioms Sude.mem_permutationSmallCutBad_iff
#print axioms Sude.mem_permutationLargeCutBad_iff
#print axioms Sude.exists_permutation_expander_of_bad_card
#check Sude.exists_permutation_expander_of_bad_card

#print axioms Sude.permutationImageFiber_card_eq
#print axioms Sude.permutation_image_uniform
#print axioms Sude.hypergeometricTargets_card
#print axioms Sude.mem_hypergeometricTargets_iff
#print axioms Sude.permutation_outgoing_hypergeometric
#check Sude.permutation_outgoing_hypergeometric

#print axioms Sude.permutationCountTuple_hypergeometric
#print axioms Sude.permutationFamily_cut_card_sum
#print axioms Sude.permutationCutFailure_iff_tuple
#print axioms Sude.permutationFixedCutBad_card_partition
#print axioms Sude.permutationFixedCutBad_hypergeometric
#check Sude.permutationFixedCutBad_hypergeometric

#print axioms Sude.permutationFixedCutBad_card_eq
#print axioms Sude.permutation_cut_union_bounds
#print axioms Sude.permutation_sum_cuts_by_size
#print axioms Sude.permutationFixedCutCount_scaled
#print axioms Sude.permutation_cut_union_bounds_by_size
#print axioms Sude.exists_permutation_expander_of_cut_sums
#check Sude.exists_permutation_expander_of_cut_sums

#print axioms Sude.binomial_term_le_one
#print axioms Sude.binomial_choose_le_exp_entropy_all
#print axioms Sude.binomial_lower_tail_weighted
#print axioms Sude.binomial_lower_tail_le_exp_entropy
#print axioms Sude.fc2k_exception_binomial_bound
#check Sude.fc2k_exception_binomial_bound

#print axioms Sude.binomialModeTerm_step
#print axioms Sude.binomialModeTerm_le_mode
#print axioms Sude.binomialModeTerm_mode_lower
#print axioms Sude.binomial_exp_entropy_le_succ_mul_choose_all
#check Sude.binomial_exp_entropy_le_succ_mul_choose_all

#print axioms Sude.entropy_sum_three_le
#print axioms Sude.fc2k_entropy_tuple_bound
#print axioms Sude.fc2k_tuple_choose_entropy_bound
#print axioms Sude.fc2k_cutWeight_entropy_bound
#print axioms Sude.fc2k_fixedCut_large_entropy_bound
#print axioms Sude.fc2k_large_cut_integer_budget
#check Sude.fc2k_large_cut_integer_budget

#print axioms Sude.permutationContainment_exact
#print axioms Sude.descFactorial_ratio_power
#print axioms Sude.choose_ratio_power
#print axioms Sude.permutationContainment_power_bound
#print axioms Sude.permutationFamilyContainment_power_bound
#check Sude.permutationFamilyContainment_power_bound

#print axioms Sude.permutationFixedCutBad_subset_exception_union
#print axioms Sude.permutationKeptInputs_card_sum
#print axioms Sude.permutationExceptionPatterns_card
#print axioms Sude.permutationException_containment_bound
#print axioms Sude.permutationFixedCutBad_exception_entropy_bound
#print axioms Sude.fc2k_small_cut_summand_bound
#print axioms Sude.fc2k_small_cut_integer_budget
#print axioms Sude.fc2k_permutation_expander_exists
#check Sude.fc2k_permutation_expander_exists

#print axioms Sude.fc2k_install_expanding_prefix
#print axioms Sude.fc2k_route_installed_prefix
#check Sude.fc2k_install_expanding_prefix
#check Sude.fc2k_route_installed_prefix

#print axioms Sude.stagePairPoolValues_injective
#print axioms Sude.CertifiedPrefixFamily.ofLStages
#print axioms Sude.CertifiedPrefixFamily.values_injective
#print axioms Sude.GeneratedPrefix.LStage0.retainedPoolValues_injective
#print axioms Sude.GeneratedPrefix.LStage0.retainedPoolValues_card
#print axioms Sude.GeneratedPrefix.LStage0.allocatorValues_injective
#print axioms Sude.GeneratedPrefix.LStage0.install_certified_stage
#check Sude.GeneratedPrefix.LStage0.install_certified_stage

#print axioms Sude.PrefixStageBlock.footprints_disjoint
#print axioms Sude.GeneratedPrefix.LStage1.valid
#print axioms Sude.GeneratedPrefix.LStage1.pool_matching
#print axioms Sude.GeneratedPrefix.firstStage_disjoint_secondStageCheckpoint
#check Sude.GeneratedPrefix.firstStage_disjoint_secondStageCheckpoint

#print axioms Sude.GeneratedPrefix.firstStage_disjoint_second
#print axioms Sude.GeneratedPrefix.firstTwoStageFamily
#print axioms Sude.GeneratedPrefix.firstTwoStageValues_injective
#print axioms Sude.GeneratedPrefix.firstTwoStageValues_gap
#check Sude.GeneratedPrefix.firstTwoStageValues_injective

#print axioms Sude.fullPrefixValues_injective
#print axioms Sude.fullPrefix_example_gates
#print axioms Sude.fullPrefix_realizes_demands
#check Sude.fullPrefix_realizes_demands

#print axioms Sude.finite_path_near_crossing
#print axioms Sude.central_window_select_from_counts
#print axioms Sude.central_unused_stock_select
#print axioms Sude.central_unused_entries_select
#print axioms Sude.central_stock_after_deletion
#print axioms Sude.central_entries_actual_mean_update
#check Sude.central_unused_entries_select
#check Sude.central_entries_actual_mean_update
#print axioms Sude.central_batch_select_and_update
#check Sude.central_batch_select_and_update
#print axioms Sude.central_source_reserve
#print axioms Sude.central_three_batches
#print axioms Sude.central_source_diagonal_batches
#check Sude.central_source_diagonal_batches
#print axioms Sude.central_three_error_identity
#print axioms Sude.central_three_error_bound
#print axioms Sude.central_actual_three_batch_error
#print axioms Sude.central_source_batches_with_total_error
#check Sude.central_source_batches_with_total_error
#print axioms Sude.central_diagonal_error_identities
#print axioms Sude.central_diagonal_source_ratio
#print axioms Sude.central_diagonal_source_denominators
#print axioms Sude.central_actual_diagonal_errors
#print axioms Sude.central_source_batches_with_diagonal_errors
#check Sude.central_source_batches_with_diagonal_errors
#print axioms Sude.place_three_finite_populations
#print axioms Sude.central_select_and_place
#print axioms Sude.central_place_actual_diagonals
#print axioms Sude.main_anti_intersection
#print axioms Sude.central_free_diagonal_geometry
#print axioms Sude.central_place_odd_diagonals
#check Sude.central_place_odd_diagonals
#print axioms Sude.actualUnusedPool_card
#print axioms Sude.actualUnusedPool_after_placement
#print axioms Sude.unreservedDiagonalCells_partition
#print axioms Sude.central_place_odd_diagonals_exact_pool
#check Sude.central_place_odd_diagonals_exact_pool
#print axioms Sude.regular_factor_perfect_matching
#print axioms Sude.regular_factor_remove_matching
#print axioms Sude.regular_factor_matching_decomposition
#print axioms Sude.regular_factor_disjoint_matchings
#print axioms Sude.regularMatchingSlotEquiv
#check Sude.regular_factor_disjoint_matchings
#check Sude.regularMatchingSlotEquiv
#print axioms Sude.consecutive_sorted_blocks_balanced
#print axioms Sude.place_sorted_regular_factor
#print axioms Sude.sortedFactorReal_sum
#print axioms Sude.sortedFactor_blocks_balanced
#print axioms Sude.sorted_factor_row_bound
#print axioms Sude.sorted_factor_column_bound
#print axioms Sude.regularFactor_row_sum
#print axioms Sude.regularFactor_column_sum
#print axioms Sude.sorted_regular_factor_completion
#check Sude.sorted_regular_factor_completion
#print axioms Sude.dense_factor_cut_bound
#print axioms Sude.cell_cut_column_degree_bound
#print axioms Sude.cell_cut_omitted_row_bound
#print axioms Sude.cellCutCount_transpose
#print axioms Sude.dense_factor_all_cuts
#print axioms Sude.dense_factor_source_cuts
#check Sude.dense_factor_source_cuts
#print axioms Sude.place_central_exceptions_and_complete_factor
#print axioms Sude.central_exception_mean_shift
#print axioms Sude.central_exception_line_error
#check Sude.place_central_exceptions_and_complete_factor
#check Sude.central_exception_mean_shift
#print axioms Sude.GeneratedPrefix.LStage1.checkedLows_valid
#print axioms Sude.GeneratedPrefix.LStage1.checkedLows_length
#print axioms Sude.GeneratedPrefix.actualFirstTwoStageValues_injective
#print axioms Sude.GeneratedPrefix.actualFirstTwoStageValues_gap
#print axioms Sude.central_exception_cells_error
#print axioms Sude.exception_budget_of_row_degrees
#print axioms Sude.central_stock_regular_factor_completion
#check Sude.central_stock_regular_factor_completion
#print axioms Sude.directed_closed_cut_edge_transfer
#print axioms Sude.directed_positive_reaches_negative
#print axioms Sude.directed_residual_path_adjustment
#print axioms Sude.directed_routing_by_unit_augmentations
#print axioms Sude.directed_unit_flow_of_cut_inequalities
#check Sude.directed_unit_flow_of_cut_inequalities
#print axioms Sude.cellCutCount_eq_filter_card
#print axioms Sude.factor_directed_cut_card
#print axioms Sude.factor_demand_cut
#print axioms Sude.factor_directed_cuts
#print axioms Sude.factor_flow_of_cuts
#print axioms Sude.factorFlowCells_regular
#print axioms Sude.regular_factor_of_cut_inequalities
#print axioms Sude.dense_residual_regular_factor
#print axioms Sude.factor_exception_degrees
#print axioms Sude.dense_central_stock_completion
#check Sude.dense_central_stock_completion
#print axioms Sude.actual_unused_pool_strict_width
#print axioms Sude.balanced_factor_parameters
#print axioms Sude.balanced_residual_degrees
#print axioms Sude.balanced_residual_central_completion
#check Sude.balanced_residual_central_completion
#print axioms Sude.bmor_central_stock_full_reservation
#print axioms Sude.bmor_balanced_residual_completion
#check Sude.bmor_balanced_residual_completion
#print axioms Sude.central_window_avoids_outer_bands
#print axioms Sude.interval_deletions_le_accounted
#print axioms Sude.available_central_interval_le_stock
#print axioms Sude.bmor_central_stock_charged_deletions
#print axioms Sude.bmor_central_stock_excluding_outer_bands
#print axioms Sude.central_source_bound_le_charged
#print axioms Sude.bmor_central_stock_source_bound
#print axioms Sude.bmor_balanced_charged_completion
#check Sude.bmor_balanced_charged_completion
#print axioms Sude.prescribedPoolValues_mean
#print axioms Sude.actualUnusedPool_eq_full_sdiff
#print axioms Sude.actual_unused_mean_from_reserved_error
#print axioms Sude.reserved_pairs_total_error
#print axioms Sude.actual_unused_mean_from_reserved_pairs_source
#check Sude.actual_unused_mean_from_reserved_pairs_source
#print axioms Sude.row_unreserved_diagonal_card_le_two
#print axioms Sude.column_unreserved_diagonal_card_le_two
#print axioms Sude.central_diagonals_from_reserved_pairs
#print axioms Sude.diagonal_preassignment_line_transfer
#print axioms Sude.diagonal_preassignment_rows_columns_transfer
#print axioms Sude.central_diagonal_rows_columns_transfer
#check Sude.central_diagonals_from_reserved_pairs
#check Sude.central_diagonal_rows_columns_transfer
#print axioms Sude.post_diagonal_balanced_occupancy
#print axioms Sude.packed_layers_exact_occupancy
#print axioms Sude.packed_layers_post_diagonal_occupancy
#check Sude.packed_layers_post_diagonal_occupancy
#print axioms Sude.postDiagonal_contains_both
#print axioms Sude.bounded_central_construction_from_pairs
#check Sude.PostDiagonalAnalyticInputs
#check Sude.bounded_central_construction_from_pairs
#print axioms Sude.post_diagonal_analytic_inputs_of_bands
#print axioms Sude.diagonal_mean_shift_uniform
#print axioms Sude.post_diagonal_mean_from_pair_budget
#print axioms Sude.post_diagonal_inputs_from_pair_budget
#check Sude.post_diagonal_inputs_from_pair_budget
#print axioms Sude.available_interval_le_unused_window
#print axioms Sude.bmor_unused_window_count
#print axioms Sude.bmor_two_diagonal_window_supplies
#print axioms Sude.window_deletions_le_reserved_card
#check Sude.bmor_two_diagonal_window_supplies
#print axioms Sude.mv_short_interval_subset_bound
#print axioms Sude.mv_depleted_neighbour_bound
#print axioms Sude.mv_neighbour_radius_identity
#check Sude.MVBrunTitchmarsh
#check Sude.mv_depleted_neighbour_bound
#print axioms Sude.fixed_gap_parity_disjoint
#print axioms Sude.fixed_gap_half_matching
#print axioms Sude.common_gap_matching_from_pairs
#print axioms Sude.mv_short_pair_count
#print axioms Sude.mv_common_gap_from_pair_population
#check Sude.mv_common_gap_from_pair_population
#print axioms Sude.sameClassPairs_card
#print axioms Sude.sameClassPairs_cauchy
#print axioms Sude.sameClassPairs_lower_bound
#print axioms Sude.mv_short_pair_count_multiclass
#print axioms Sude.mv_multiclass_common_gap_from_pair_population
#print axioms Sude.mv_common_gap_from_fiber_partition
#print axioms Sude.same_spatial_bin_gap
#print axioms Sude.progression_bin_key_card
#print axioms Sude.progression_bin_key_pair
#print axioms Sude.mv_common_gap_from_interval_classes
#check Sude.mv_common_gap_from_interval_classes
#print axioms Sude.fixed_gap_select_and_deplete
#print axioms Sude.mv_interval_stage_select_and_deplete
#check Sude.mv_interval_stage_select_and_deplete
#print axioms Sude.bt_source_bin_coefficient
#print axioms Sude.bt_source_pair_surplus
#print axioms Sude.bt_source_pair_gate
#print axioms Sude.bt_source_gate_from_bins
#print axioms Sude.bt_bin_count_le_source
#print axioms Sude.bt_source_implies_exact_bin_gate
#print axioms Sude.mv_interval_stage_from_source_budget
#check Sude.mv_interval_stage_from_source_budget
#print axioms Sude.BTStageTrace.footprints_subset
#print axioms Sude.BTStageTrace.stage_properties
#print axioms Sude.BTStageTrace.pairwise_disjoint
#print axioms Sude.BTStageTrace.final_subset_and_card
#print axioms Sude.mv_iterate_interval_stages
#check Sude.BTStageNumericData
#check Sude.mv_iterate_interval_stages
#print axioms Sude.BTStageTrace.lowAt_mem
#print axioms Sude.BTStageTrace.endpoint_mem_initial
#print axioms Sude.BTStageTrace.poolValues_gap
#print axioms Sude.BTStageTrace.stageAt_disjoint
#print axioms Sude.BTStageTrace.poolValues_injective
#check Sude.BTStageTrace.poolValues_injective
#print axioms Sude.install_variable_prefix_diagonal_rectangles
#print axioms Sude.BTStageTrace.install_diagonal_rectangles
#print axioms Sude.variable_prefixNetwork_pair_gap
#print axioms Sude.install_variable_prefix_ordinary_networks
#print axioms Sude.install_variable_prefix_diagonal_and_ordinary
#print axioms Sude.BTStageTrace.install_diagonal_and_ordinary
#check Sude.BTStageTrace.install_diagonal_and_ordinary

#print axioms Sude.completeStepGrid_insert
#print axioms Sude.extend_step_gap_chain
#print axioms Sude.BTStageTrace.nodup
#print axioms Sude.BTStageTrace.step_gap_chain
#print axioms Sude.BTStageTrace.seeded_step_grid
#print axioms Sude.BTStageTrace.physical_step_chain
#print axioms Sude.BTStageTrace.physical_seeded_step_grid
#check Sude.BTStageTrace.physical_seeded_step_grid

#print axioms Sude.GeneratedPrefix.LStage2.checkedLows_valid
#print axioms Sude.GeneratedPrefix.firstStage_disjoint_third
#print axioms Sude.GeneratedPrefix.secondStage_disjoint_third
#print axioms Sude.GeneratedPrefix.actualFirstThreeStageFamily
#print axioms Sude.GeneratedPrefix.actualFirstThreeStageValues_injective
#print axioms Sude.GeneratedPrefix.actualFirstThreeStageValues_gap
#check Sude.GeneratedPrefix.actualFirstThreeStageValues_gap

#print axioms Sude.variablePrefixNetworkGap_slot
#print axioms Sude.BTStageTrace.installed_network_step_grid
#print axioms Sude.installed_variable_grid_endpoints
#print axioms Sude.BTStageTrace.extend_installed_network_grid
#check Sude.BTStageTrace.installed_network_step_grid
#check Sude.BTStageTrace.extend_installed_network_grid

#print axioms Sude.BTGrowingTrace.final_accounting
#print axioms Sude.BTGrowingTrace.extend_step_grid
#print axioms Sude.mv_iterate_growing_interval_stages
#print axioms Sude.BTGrowingTrace.poolValues_injective
#print axioms Sude.BTGrowingTrace.install_diagonal_and_ordinary
#print axioms Sude.BTGrowingTrace.extend_installed_network_grid
#print axioms Sude.bt_shifted_width_identity
#print axioms Sude.bt_shifted_width_lower
#print axioms Sude.bt_shifted_radius_growth
#print axioms Sude.bt_phase_entry
#print axioms Sude.bt_stage_overshoot
#print axioms Sude.bt_log_growth_lower
#print axioms Sude.bt_log_phase_growth
#print axioms Sude.bt_log_phase_growth_uniform
#print axioms Sude.bt_linear_stock_sum
#print axioms Sude.bt_linear_phase_bound
#print axioms Sude.bt_phase_target_of_log_budget
#print axioms Sude.bt_linear_phase_reaches_target
#print axioms Sude.BTGrowingTrace.prefix_gap_bound
#print axioms Sude.BTGrowingTrace.split_at_stage
#print axioms Sude.BTGrowingTrace.prefix_stock_accounting
#print axioms Sude.BTGrowingTrace.prefix_shifted_growth
#print axioms Sude.BTWidthTrace.prefix
#print axioms Sude.mv_iterate_growing_interval_stages_with_widths
#print axioms Sude.BTGrowingTrace.linear_width_prefix_growth
#print axioms Sude.BTGrowingTrace.linear_width_steps
#print axioms Sude.BTGrowingTrace.linear_width_reaches_target
#print axioms Sude.mv_growing_linear_phase_reaches_target
#check Sude.mv_growing_linear_phase_reaches_target

#print axioms Sude.ap_short_fiber_bound
#print axioms Sude.ap_short_pair_count
#print axioms Sude.ap_common_gap_from_interval_classes
#print axioms Sude.ap_source_implies_exact_bin_gate
#print axioms Sude.ap_interval_stage_from_source_budget
#print axioms Sude.ap_iterate_growing_interval_stages_with_widths
#print axioms Sude.ap_growing_linear_phase_reaches_target
#print axioms Sude.BTGrowingTrace.append_accounting
#check Sude.ap_growing_linear_phase_reaches_target
#print axioms Sude.BTGrowingTrace.phase_entry_persists
#print axioms Sude.BTGrowingTrace.phase_entry_at_stage
#print axioms Sude.bt_linear_stock_floor
#print axioms Sude.bt_uniform_numeric_data_from_scalar
#print axioms Sude.ap_uniform_numeric_data_from_scalar
#print axioms Sude.mv_growing_linear_phase_from_scalar
#print axioms Sude.ap_growing_linear_phase_from_scalar
#check Sude.mv_growing_linear_phase_from_scalar
#check Sude.ap_growing_linear_phase_from_scalar
#print axioms Sude.mv_continue_after_paid_entry
#check Sude.mv_continue_after_paid_entry
#print axioms Sude.ap_then_bt_from_scalar
#check Sude.ap_then_bt_from_scalar
#print axioms Sude.ap_then_bt_or_finish_from_scalar
#check Sude.ap_then_bt_or_finish_from_scalar
#print axioms Sude.ap_then_bt_with_minimum_budget
#check Sude.ap_then_bt_with_minimum_budget
#print axioms Sude.GeneratedPrefix.LStage3.checkedLows_valid
#print axioms Sude.GeneratedPrefix.stage0_disjoint_stage3
#print axioms Sude.GeneratedPrefix.stage1_disjoint_stage3
#print axioms Sude.GeneratedPrefix.stage2_disjoint_stage3
#print axioms Sude.GeneratedPrefix.actualFirstFourStageFamily
#print axioms Sude.GeneratedPrefix.actualFirstFourStageValues_injective
#print axioms Sude.GeneratedPrefix.actualFirstFourStageValues_gap
#print axioms Sude.narrow_candidate_batch
#print axioms Sude.narrow_matching_and_deplete
#print axioms Sude.ap_narrow_interval_stage
#print axioms Sude.mv_narrow_interval_stage
#print axioms Sude.ap_iterate_narrow_growing_stages
#print axioms Sude.mv_iterate_narrow_growing_stages
#print axioms Sude.ap_narrow_uniform_numeric_data_from_scalar
#print axioms Sude.bt_narrow_uniform_numeric_data_from_scalar
#print axioms Sude.ap_then_bt_narrow_with_minimum_budget
#check Sude.ap_then_bt_narrow_with_minimum_budget
#print axioms Sude.BTGrowingTrace.poolValues_midpoints
#print axioms Sude.BTGrowingTrace.network_midpoints
#print axioms Sude.BTGrowingTrace.placed_network_midpoints
#print axioms Sude.bounded_positive_pool_midpoint_span
#print axioms Sude.prescribed_pool_midpoint_span
#print axioms Sude.prefixRectangleInput_pair
#print axioms Sude.BTGrowingTrace.placed_rectangle_midpoints
#print axioms Sude.BTGrowingTrace.placed_rectangle_pair_gap
#print axioms Sude.BTGrowingTrace.packed_networks_midpoints
#print axioms Sude.poolFinset_card
#print axioms Sude.pool_prime_and_residue
#print axioms Sude.screened_pool_card
#print axioms Sude.screened_pool_after_reservations
#print axioms Sude.screened_pool_phase_inputs
#print axioms Sude.screened_pool_narrow_prefix
#check Sude.screened_pool_narrow_prefix
#print axioms Sude.BTGrowingTrace.install_screened_narrow
#check Sude.BTGrowingTrace.install_screened_narrow
#print axioms Sude.fw_seed_quota_gate
#print axioms Sude.fw_allocation_depth_gate
#print axioms Sude.fw_floor_capacity
#print axioms Sude.fw_reflected_band_geometry
#print axioms Sude.Lucas.Generated.first625_valid
#print axioms Sude.Lucas.Generated.first625_orders
#print axioms Sude.Lucas.Generated.first625_cover
#print axioms Sude.Lucas.Generated.first1250_valid
#print axioms Sude.Lucas.Generated.first1250_orders
#print axioms Sude.Lucas.Generated.first1250_cover
#print axioms Sude.Lucas.Generated.first2500_valid
#print axioms Sude.Lucas.Generated.first2500_orders
#print axioms Sude.Lucas.Generated.first2500_cover
#check Sude.mv_iterate_growing_interval_stages

#print axioms Sude.Lucas.Generated.first3750_valid
#print axioms Sude.Lucas.Generated.first3750_orders
#print axioms Sude.Lucas.Generated.first3750_cover
#print axioms Sude.GeneratedPrefix.LStage4.checkedLows_valid
#print axioms Sude.GeneratedPrefix.LStage5.checkedLows_valid
#print axioms Sude.GeneratedPrefix.actualFirstSixStageFamily
#print axioms Sude.GeneratedPrefix.actualFirstSixStageValues_injective
#print axioms Sude.GeneratedPrefix.actualFirstSixStageValues_gap

#print axioms Sude.fw_seed_bridge_disjoint
#print axioms Sude.fw_seed_candidates_after_bridges

#print axioms Sude.fw_poolMaximum_gt_four_seed
#print axioms Sude.fw_actual_seed_candidates_after_bridges

#print axioms Sude.narrow_seed_width_budget
#print axioms Sude.exists_narrowest_seed_groups
#print axioms Sude.narrowest_seed_groups_bound
#print axioms Sude.narrowest_seed_variance_bound
#print axioms Sude.sorted_seed_group_widths
#print axioms Sude.sorted_seed_narrowest_variance
#print axioms Sude.sortedSeedEndpoint_injective
#print axioms Sude.sortedSeedCandidates_variance
#print axioms Sude.retainedSeedEndpoints_card
#print axioms Sude.discardedSeedEndpoint_not_retained
#print axioms Sude.fw_actual_narrow_seed
#print axioms Sude.fw_actual_narrow_seed_reservation

#print axioms Sude.sortedSeedMidpoint_slot
#print axioms Sude.sortedSeedMidpoint_range

#print axioms Sude.unchosenSeedEndpoint_not_retained
#print axioms Sude.retainedSeedStageIndex_mem
#print axioms Sude.retainedSeedPoolValues_injective
#print axioms Sude.retainedSeedPoolValues_gap
#print axioms Sude.install_retained_seed_pairs
#print axioms Sude.retainedSeedMidpoint_spread
#print axioms Sude.retainedSeed_placed_network_midpoints
#print axioms Sude.retainedSeed_placed_rectangle_midpoints
#print axioms Sude.fw_install_narrow_seed
#check Sude.fw_install_narrow_seed

#print axioms Sude.twinBitsetLowers_spec
#print axioms Sude.twinBitsetCountScan_spec
#print axioms Sude.twinBitsetCountScan_append
#print axioms Sude.mem_finiteTwinSeeds
#print axioms Sude.finiteTwinSeeds_matching
#print axioms Sude.finiteTwinSeeds_count_of_scan
#print axioms Sude.twinBoundaryExample_mathematical
#print axioms Sude.streamTwinCount_eq
#print axioms Sude.streamingTwinScan_eq
#print axioms Sude.prunedStreamingTwinScan_eq
#print axioms Sude.streamingTwinScan_append
#print axioms Sude.finiteTwinSeeds_at_least_500
#print axioms Sude.fw_candidates_of_finiteTwin_scan
#check Sude.finiteTwinSeeds_count_of_scan

#print axioms Sude.finiteTwinSeeds_count_of_partition
#print axioms Sude.combineTwinPrimeSegments

#print axioms Sude.activeMarkingBase_bits_eq
#print axioms Sude.activeStreamTwinCount_eq
#print axioms Sude.activeStreamingTwinScan_eq
#print axioms Sude.finiteTwinSeeds_count_of_active_partition
#check Sude.finiteTwinSeeds_count_of_active_partition

#print axioms Sude.Lucas.Generated.prime_7577
#print axioms Sude.Lucas.Generated.prime_19231
#print axioms Sude.Lucas.Generated.prime_24109
#print axioms Sude.Lucas.Generated.prime_27997
#print axioms Sude.Lucas.Generated.prime_31687

#print axioms Sude.finiteTwinOddBase_sorted
#print axioms Sude.finiteTwinOddBase_all
#print axioms Sude.finiteTwinOddBase_card
#print axioms Sude.finiteTwinOddBase_exhaustive
#print axioms Sude.finiteTwinCheckedBase_complete
#check Sude.finiteTwinCheckedBase_complete

#print axioms Sude.finiteTwinHighActive1024_mathematical
#print axioms Sude.finiteTwinHighActive16384_mathematical
#print axioms Sude.finiteTwinSeeds_at_least_1611

#print axioms Sude.GeneratedTwinScan.S000C00.total
#print axioms Sude.GeneratedTwinScan.S000C01.total
#print axioms Sude.finiteTwinLow131072_mathematical
#print axioms Sude.finiteTwinSeeds_at_least_2764

#print axioms Sude.prefixPhysicalInput_injective
#print axioms Sude.prefixPhysicalInput_bijective
#print axioms Sude.retainedSeedSlot_image
#print axioms Sude.prefixPhysicalInput_retained_image
#print axioms Sude.prefixPhysical_realizes_retained
#print axioms Sude.prefixPhysicalCells_realizes_retained
#check Sude.prefixPhysicalCells_realizes_retained

#print axioms Sude.prefixNetworkInput_cast_comp
#print axioms Sude.install_retained_seed_pairs_exhaustively
#check Sude.install_retained_seed_pairs_exhaustively

#print axioms Sude.permutationHistoryNext_card_eq
#print axioms Sude.permutationHistory_next_uniform
#print axioms Sude.permutationHistoryNext_card_pos
#print axioms Sude.permutationHistory_event_uniform_all
#print axioms Sude.permutationHistory_next_sum
#print axioms Sude.permutationHistory_weighted_sum
#print axioms Sude.permutationHistoryNext_eq_insert
#print axioms Sude.permutationHistoryNext_image_insert
#print axioms Sude.weightedReveal_increment
#print axioms Sude.weightedReveal_coefficient
#print axioms Sude.weightedReveal_last
#print axioms Sude.weightedRemaining_sum_bounds
#check Sude.permutationHistory_weighted_sum

#print axioms Sude.uniformPermutation_isProbability
#print axioms Sude.permutationHistoryMeasure_isProbability
#print axioms Sude.permutationHistoryMeasure_eq_cond
#print axioms Sude.permutationHistoryMeasure_event
#print axioms Sude.permutationHistoryMeasure_event_uniform
#check Sude.permutationHistoryMeasure_event_uniform

#print axioms Sude.permutationHistory_next_subgaussian
#print axioms Sude.permutationHistory_integral
#print axioms Sude.permutationHistory_next_mean
#print axioms Sude.permutationHistory_next_explicit_subgaussian
#check Sude.permutationHistory_next_explicit_subgaussian
#print axioms Sude.permutationHistory_weighted_mean
#check Sude.permutationHistory_weighted_mean

#print axioms Sude.permutationHistory_insert_remaining_card
#print axioms Sude.permutationHistory_insert_unused_sum
#print axioms Sude.permutationHistory_after_weighted_mean
#print axioms Sude.permutationHistory_reveal_increment
#print axioms Sude.permutationHistory_reveal_subgaussian
#print axioms Sude.permutationHistory_reveal_coefficient_bounds
#print axioms Sude.permutationHistory_reveal_ordered_subgaussian
#print axioms Sude.subgaussian_parameter_mono
#print axioms Sude.permutationHistory_reveal_source_subgaussian
#check Sude.permutationHistory_reveal_source_subgaussian

#print axioms Sude.permutationHistory_last_value
#print axioms Sude.permutationHistory_last_remaining
#print axioms Sude.permutationHistory_last_increment_ae
#print axioms Sude.permutationHistory_last_subgaussian
#check Sude.permutationHistory_last_subgaussian

#print axioms Sude.permutationHistory_sum_by_next
#print axioms Sude.permutationHistoryExtension_mem
#print axioms Sude.permutationHistory_integral_tower
#print axioms Sude.permutationHistory_integral_le_of_next
#check Sude.permutationHistory_integral_tower

#print axioms Sude.permutationHistory_integral_compare_of_next
#print axioms Sude.permutationHistory_mgf_add_of_next_mgf
#print axioms Sude.permutationRevealIncrement_constant_on_next
#print axioms Sude.permutationRevealIncrement_mgf_step
#check Sude.permutationRevealIncrement_mgf_step

#print axioms Sude.permutationWeightedCentered_decompose
#print axioms Sude.permutationHistoryMeasure_eq_of_next
#print axioms Sude.permutationWeighted_future_ae
#print axioms Sude.permutationWeighted_mgf_bound
#print axioms Sude.permutationHistory_integrable
#print axioms Sude.permutationWeighted_hasSubgaussian
#print axioms Sude.permutationWeighted_two_sided
#print axioms Sude.permutationWeightedProxy_real
#check Sude.permutationWeighted_two_sided

#print axioms Sude.stagePermutationMeasure_isProbability
#print axioms Sude.permutationHistoryMeasure_empty
#print axioms Sude.stageWeighted_hasSubgaussian
#print axioms Sude.stageWeighted_two_sided
#print axioms Sude.stageWeightedProxy_real
#print axioms Sude.stageLines_failure_bound
#print axioms Sude.stageLines_simultaneous_exists
#print axioms Sude.stageWeighted_zero_proxy_strict_failure
#print axioms Sude.stageWeighted_strict_failure_bound
#print axioms Sude.stageLines_strict_failure_bound
#print axioms Sude.stageLines_simultaneous_exists_le
#check Sude.stageLines_simultaneous_exists_le

#print axioms Sude.zeroAwareTailBound_log_budget
#print axioms Sude.zeroAwareTailBound_sum_log_budget
#print axioms Sude.stageLines_exists_of_proxy_cap
#check Sude.stageLines_exists_of_proxy_cap

#print axioms Sude.stagePairPermutation
#print axioms Sude.permutedRetainedSeedValues_injective
#print axioms Sude.install_permuted_retained_seed_pairs
#print axioms Sude.install_permuted_retained_seed_pairs_exhaustively
#print axioms Sude.permutedRetainedSeed_pair_midpoint
#print axioms Sude.retainedStageMidpoint_bounds
#print axioms Sude.retainedStageMidpoint_range
#print axioms Sude.permutedSeed_placed_rectangle_midpoint
#print axioms Sude.permutedSeed_placed_network_midpoint
#print axioms Sude.stageWeightedProxy_le_of_invoice
#print axioms Sude.stageLines_exists_of_squared_invoice
#print axioms Sude.exists_permuted_retained_seed_pairs_with_weighted_budget
#check Sude.exists_permuted_retained_seed_pairs_with_weighted_budget

#print axioms Sude.fixed_seed_layout_accepts_all_permutations
#print axioms Sude.exists_fixed_seed_layout
#print axioms Sude.fixed_seed_layout_has_weighted_allocation
#check Sude.exists_fixed_seed_layout
#check Sude.fixed_seed_layout_has_weighted_allocation

#print axioms Sude.LayerPacking.layerRowWeight_eq
#print axioms Sude.LayerPacking.layerColumnWeight_eq
#print axioms Sude.LayerPacking.layerRowWeight_sq_sum
#print axioms Sude.LayerPacking.layerColumnWeight_sq_sum
#print axioms Sude.LayerPacking.transposedLayerRowWeight_eq
#print axioms Sude.LayerPacking.ordinary_stage_row_squared_invoice
#check Sude.LayerPacking.ordinary_stage_row_squared_invoice

#print axioms Sude.LayerPacking.transposedLayerColumnWeight_eq
#print axioms Sude.LayerPacking.ordinary_stage_column_squared_invoice
#check Sude.LayerPacking.ordinary_stage_column_squared_invoice

#print axioms Sude.LayerPacking.pairRowContribution_midpoint
#print axioms Sude.LayerPacking.layerRowContribution_midpoint
#check Sude.LayerPacking.layerRowContribution_midpoint

#print axioms Sude.packedRectangles_same_row
#print axioms Sude.packedRectangles_same_column
#print axioms Sude.squared_incidence_le_four
#print axioms Sude.packedRectangle_row_card_le_two
#print axioms Sude.packedRectangle_column_card_le_two
#check Sude.packedRectangle_row_card_le_two
#check Sude.packedRectangle_column_card_le_two

#print axioms Sude.rectanglePairWeight_sum_eq_card
#print axioms Sude.packedRectangle_row_pair_invoice
#print axioms Sude.packedRectangle_column_pair_invoice
#print axioms Sude.stage_squared_invoice_of_ordinary_and_rectangles
#print axioms Sude.prefixRectanglePairSlot_injective
#print axioms Sude.prefixRectangle_row_pair_invoice
#print axioms Sude.prefixRectangle_column_pair_invoice
#print axioms Sude.prefixRectangle_row_stage_invoice
#print axioms Sude.prefixRectangle_column_stage_invoice
#print axioms Sude.prefix_row_combined_width_invoice
#print axioms Sude.prefix_column_combined_width_invoice
#check Sude.prefix_row_combined_width_invoice
#check Sude.prefix_column_combined_width_invoice

#print axioms Sude.LayerPacking.PackedLayers.get_derange
#print axioms Sude.physicalRowStageInvoice_eq
#print axioms Sude.physicalColumnStageInvoice_eq
#print axioms Sude.physical_prefix_row_width_invoice
#print axioms Sude.physical_prefix_column_width_invoice
#print axioms Sude.prefixStageLayer_sequenceCell
#print axioms Sude.prefixStageLayer_networkInput
#check Sude.physical_prefix_row_width_invoice
#check Sude.physical_prefix_column_width_invoice

#print axioms Sude.prefixStagePairSlot_injective
#print axioms Sude.prefixStageRowIncidence_sq_sum
#print axioms Sude.prefixStageColumnIncidence_sq_sum
#print axioms Sude.liftedSlotWeight_at
#print axioms Sude.liftedSlotWeight_sq_sum
#print axioms Sude.physicalRowSlotWeight_sq_sum
#print axioms Sude.physicalColumnSlotWeight_sq_sum
#print axioms Sude.physicalRowSlot_weighted_invoice
#print axioms Sude.physicalColumnSlot_weighted_invoice
#check Sude.physicalRowSlot_weighted_invoice
#check Sude.physicalColumnSlot_weighted_invoice

#print axioms Sude.prefixStageRowIncidence_nonneg
#print axioms Sude.prefixStageColumnIncidence_nonneg
#print axioms Sude.liftedSlotWeight_nonneg
#print axioms Sude.physicalRowSlotWeight_nonneg
#print axioms Sude.physicalColumnSlotWeight_nonneg
#print axioms Sude.physical_row_column_midpoint_allocation
#check Sude.physical_row_column_midpoint_allocation

#print axioms Sude.fixed_retained_row_column_allocation
#print axioms Sude.rectanglePairWeight_main
#print axioms Sude.rectanglePairWeight_anti
#check Sude.fixed_retained_row_column_allocation

#print axioms Sude.prefixRectangle_main_stage_invoice
#print axioms Sude.prefixRectangle_anti_stage_invoice
#print axioms Sude.prefixStageLayer_off_diagonals
#print axioms Sude.prefixStageLayer_swap_off_diagonals
#print axioms Sude.physicalDiagonalSlotWeight_nonneg
#print axioms Sude.physicalDiagonalSlotWeight_sq_sum
#print axioms Sude.physicalMainSlot_weighted_invoice
#print axioms Sude.physicalAntiSlot_weighted_invoice
#print axioms Sude.physical_all_line_midpoint_allocation
#print axioms Sude.fixed_retained_all_line_allocation
#check Sude.fixed_retained_all_line_allocation

#print axioms Sude.retainedStageIndex_val_mem
#print axioms Sude.retainedStage_sum
#print axioms Sude.retainedStage_midpoint_width_sq_sum
#print axioms Sude.retainedStage_midpoint_width_sq_le
#print axioms Sude.fixed_retained_all_line_source_width
#print axioms Sude.exists_retained_all_line_source_allocation
#print axioms Sude.rectanglePairContribution_midpoint
#print axioms Sude.placedRectangleContribution_midpoint
#check Sude.exists_retained_all_line_source_allocation
#check Sude.placedRectangleContribution_midpoint

#print axioms Sude.fw_selected_all_line_midpoint_allocation
#check Sude.fw_selected_all_line_midpoint_allocation

#print axioms Sude.physicalPair_line_sum_midpoint
#print axioms Sude.prefixPairCells_injective
#print axioms Sude.prefixPairCells_line_sum
#print axioms Sude.fullLine_sum_pair_and_residual
#print axioms Sude.center_mem_both_line_residuals
#print axioms Sude.prefixPhysicalCells_avoid_center
#print axioms Sude.prefixPairCells_center_in_both_residuals
#print axioms Sude.prefixStagePairSlot_bijective
#print axioms Sude.physicalPrefixSlots_eq_univ
#print axioms Sude.prefixPairCells_rectangle
#print axioms Sude.prefixPairCells_row_network
#print axioms Sude.prefixPairCells_column_network
#check Sude.fullLine_sum_pair_and_residual
#check Sude.prefixPairCells_center_in_both_residuals

#print axioms Sude.stageWeightedCentered_eq_explicit_mean
#print axioms Sude.stageLineCentered_eq_explicit_mean
#print axioms Sude.stageLineWeightedSum_eq_centered_add_mean
#print axioms Sude.physicalPair_line_sum_eq_centered
#print axioms Sude.prefixPairCells_row_weight_at_label
#print axioms Sude.prefixPairCells_column_weight_at_label
#print axioms Sude.prefixPairCells_main_weight_at_label
#print axioms Sude.prefixPairCells_anti_weight_at_label
#print axioms Sude.physicalAllLineWeight_eq_pair_incidence
#print axioms Sude.prefixPhysicalCells_injective_of_placement
#print axioms Sude.prefix_actual_line_eq_centered
#print axioms Sude.fullLine_sum_eq_centered_and_residual
#print axioms Sude.finiteTwinSeeds_at_least_61546
#print axioms Sude.finiteTwinSeeds_at_least_68352
#check Sude.prefix_actual_line_eq_centered
#check Sude.fullLine_sum_eq_centered_and_residual

#print axioms Sude.fullLine_deviation_le_centered_bound
#print axioms Sude.prefix_actual_line_deviation_le
#print axioms Sude.fw_selected_actual_line_allocation
#check Sude.fw_selected_actual_line_allocation

#print axioms Sude.matched_bin_stock_sq_le
#print axioms Sude.matched_bins_repeated_difference
#print axioms Sude.matched_bin_stock_after_deletion
#print axioms Sude.matched_bins_repeated_after_deletion
#print axioms Sude.matched_bins_depleted_valid_block
#print axioms Sude.matched_bin_square_gate_of_budget
#print axioms Sude.select_double_pairs_from_depletion_supply
#print axioms Sude.select_matched_bin_double_pairs
#print axioms Sude.select_and_install_matched_bin_blocks
#print axioms Sude.bmor_two_separated_bin_supplies
#print axioms Sude.bmor_two_matched_bin_inputs
#print axioms Sude.bmor_select_and_install_matched_blocks
#check Sude.bmor_select_and_install_matched_blocks

-- Final all-odd theorem, band theorems, and explicit-formula bridge audit
#check @Sude.hasSquare_iff_values
#check @Sude.bmorExplicitFormulaImports_of_published
#check @Sude.fc2k_hasSquare
#check @Sude.fw_first_band_hasSquare
#check @Sude.fw_and_ew_hasSquare
#check @Sude.upper_tail_hasSquare
#check @Sude.tail_hasSquare
#check @Sude.sude_first_theorem
#check @Sude.sude_first_theorem_values

#print axioms Sude.bmorExplicitFormulaImports_of_published
#print axioms Sude.fc2k_hasSquare
#print axioms Sude.fw_first_band_hasSquare
#print axioms Sude.fw_and_ew_hasSquare
#print axioms Sude.upper_tail_hasSquare
#print axioms Sude.tail_hasSquare
#print axioms Sude.sude_first_theorem
#print axioms Sude.sude_first_theorem_values
