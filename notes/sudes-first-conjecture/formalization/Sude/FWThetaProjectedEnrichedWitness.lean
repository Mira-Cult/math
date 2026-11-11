import Sude.FWThetaFamilyWitness
import Sude.FWThetaNetworkWitness
import Sude.FWThetaGrowthDiagonalWitness
import Sude.FWThetaRoleValueInputs

/-! Project the family, network, growth-diagonal and role-value inputs from
one actual theta witness. The result supplies no DQ/RF completion, numerical
or primality gate and asserts no later-flow bound. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 20000000

theorem fw_theta_projected_enriched_witness
    (mv : MVBrunTitchmarsh) (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (lower : RSIndexLower)
    (sharp : RSIndexLowerSharp) (upperSharp : RSIndexUpperSharp)
    (n : ℕ) (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (a : Cell n ≃ Fin (n*n)) (seeds : Finset ℕ)
    (hseed : ∀ p ∈ seeds, p + 2 ≤ 2 ^ 30)
    (hprime : ∀ p ∈ seeds, 43 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
    (hcount : 6 * (n + 8) * (16 + 2 - 1) ≤ seeds.card) :
    let hrect := (fw_reserved_wide_rectangle_capacity hnlo (by decide) (by decide)).1
    let hseedrect := (fw_reserved_wide_rectangle_capacity hnlo (by decide) (by decide)).2.1
    let hwide := (fw_reserved_wide_rectangle_capacity hnlo (by decide) (by decide)).2.2.1
    let hmax := fw_growth_offset_rectangle_capacity (n := n) (P := 238) (P₀ := 254) (by decide)
    let choice := fwBridgeSeedRectangleChoice hrect hseedrect
      (fwWideRectangleChoice hwide (fwGrowthRectangleChoice hmax otherChoice))
    ∃ (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) choice)
      (p : Fin 3 → Equiv.Perm (Fin n)) (b₀ : Cell n ≃ Fin (n*n)) (roles : Finset (Cell n)),
      (∀ i v, p i v ≠ v) ∧
      (∀ S : Finset (Fin n), 519 * min S.card (n - S.card) ≤
        500 * (cutEdges (fun e : Fin 3 × Fin n => e.2) (fun e => p e.1 e.2) S).card) ∧
      Nonempty (FWThetaNetworkWitness n f.stages.length f.hrect f.hseedrect f.hwide f.hoff f.hs choice
        f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc
        f.hrows f.hcols p f.ordered b₀ roles) ∧
      Nonempty (FWThetaGrowthDiagonalWitness n (fwJointRectangleCount n 254) choice f) ∧
      Nonempty (FWThetaRoleValueInputs f seeds) := by
  classical
  dsimp only
  have hθ := bmor_fw_all_family_midpoint_reference_of_theta mv bmor upper lower sharp upperSharp
    n hnlo hnhi otherChoice a seeds hseed hprime hcount
  rcases hθ with ⟨p, hder, hexp, hθ⟩
  rcases hθ with ⟨batches, hvalid, candidates, hcard, kept, hsub, hkept, hcand, hθ⟩
  rcases hθ with ⟨rows, cols, hr, hc, sr, sc, hsr, hsc, wr, wc, hwr, hwc,
    blocks, hlen, old, stock, last, stages, hθ⟩
  rcases hθ with ⟨trace, hoff, gr, gc, hgr, hgc, grown, hθ⟩
  rcases hθ with ⟨hcap, hstocksub, hstockcard, hcross, hpairwise, havoidTrace, hnarrow, hfixed, hθ⟩
  rcases hθ with ⟨hrmap, hcmap, hsrmap, hscmap, hgrmap, hgcmap, hjointrow, hjointcol,
    hplaced, hmatched, hwidecoords, hθ⟩
  rcases hθ with ⟨ω, b, hθ⟩
  rcases hθ with ⟨hperm, hgrowthPres, hset, hgap, hcenter, hselected, hbdB, hboB, hwpB, hθ⟩
  rcases hθ with ⟨πb, sb, πw, sw, new, hθ⟩
  rcases hθ with ⟨hbe, hwe, hseedNew, hgrowthNew, hgrowthRoleNew, hsetNew, hnewOutside,
    hbstage, hwstage, hbgap, hwgap, hwpos, hbscore, hwscore, hpermNew, hgapNew, hselectedNew, hθ⟩
  rcases hθ with ⟨T, U, V, τ, final, hθ⟩
  rcases hθ with ⟨hsel2, hmap2, hperm2, hfix2, hsf, hbf, hwf, hstage2, hgap2, hθ⟩
  rcases hθ with ⟨hmain2, hanti2, hfinalBridge, hfinalWide, hfinalSeed, hdiag, hnetwork⟩
  rcases hdiag with ⟨hE1, hD2, hE2, hE3, hE3s, hbmain, hbanti, hrow, hcol⟩
  rcases hnetwork with ⟨hjointrow', hjointcol', hrowGap, hcolGap, BR, BC, hθ⟩
  rcases hθ with ⟨hends, hrowBlocks, hcolBlocks, hcapacity, b₀, hθ⟩
  rcases hθ with ⟨hinvoice, hmidrow, hmidcol, hmain, hanti, hrectfixed, houtside, hrowPairs,
    hcolPairs, hgrowth, hdiag₀, hearly, himage, hpool₀, hinj, hflows⟩
  rcases hdiag₀ with ⟨hrow₀, hcol₀⟩
  let hrect := (fw_reserved_wide_rectangle_capacity (P₀ := 254) hnlo (by decide) (by decide)).1
  let hseedrect := (fw_reserved_wide_rectangle_capacity (P₀ := 254) hnlo (by decide) (by decide)).2.1
  let hwide := (fw_reserved_wide_rectangle_capacity (P₀ := 254) hnlo (by decide) (by decide)).2.2.1
  let hs := (fw_reserved_wide_rectangle_capacity (P₀ := 254) hnlo (by decide) (by decide)).2.2.2
  let hmax := fw_growth_offset_rectangle_capacity (n := n) (P := 238) (P₀ := 254) (by decide)
  let choice := fwBridgeSeedRectangleChoice hrect hseedrect
    (fwWideRectangleChoice hwide (fwGrowthRectangleChoice hmax otherChoice))
  let initial := ((poolFinset n).filter (fun p => 43 < p)) \
    fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks
  have hpool : ∀ p ∈ initial, p ∈ pool n := by
    intro v hv
    exact mem_poolFinset.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).1
  let gapb := fun j k => (fwBridgeStageBlock n ∅ batches hvalid j (πb j k)).high₁ -
    (fwBridgeStageBlock n ∅ batches hvalid j (πb j k)).low₁
  let gapw := fun j k =>
    let block := blocks.get (Fin.cast hlen.symm (finProdFinEquiv (j,πw j k)))
    block.high₁ - block.low₁
  let f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) choice := {
    stages := stages, stageCap := hcap, hrect := hrect, hseedrect := hseedrect, hwide := hwide,
    hoff := hoff, hs := hs, br := rows, bc := cols, sr := sr, sc := sc, wr := wr, wc := wc,
    gr := gr, gc := gc, hbr := hr, hbc := hc, hsr := hsr, hsc := hsc, hwr := hwr, hwc := hwc,
    hgr := hgr, hgc := hgc, hrows := hjointrow', hcols := hjointcol', source := b, grown := grown,
    ordered := final, batches := batches, hvalid := hvalid, blocks := blocks, hlen := hlen,
    hdiag := hbdB, hord := hboB, hplaced := hwpB, hmatched := hmatched,
    πb := πb, sb := fun j k => sb (j,k), πw := πw, sw := fun j k => sw (j,k),
    hbridge := by
      intro j k q side
      exact (hbf ((j,k,q),side)).trans (hbe j k q side),
    hwideEntry := by
      intro j k q side
      exact (hwf ((j,k,q),side)).trans (hwe j k q side),
    gapb := gapb, gapw := gapw,
    hinvoiceb := by
      intro j k q
      rw [hbf ((j,k,q),true), hbf ((j,k,q),false)]
      exact hbgap j k q,
    hinvoicew := by
      intro j k q
      rw [hwf ((j,k,q),true), hwf ((j,k,q),false)]
      exact hwgap j k q,
    hpairgap := hgap2,
    hseedgap := by
      intro j i
      rw [hsf ((j,i),true), hsf ((j,i),false)]
      exact hgapNew j i,
    hBridgeScore := hfinalBridge, hWideScore := hfinalWide,
    initial := initial, stock := stock, last := last, trace := trace, hpool := hpool,
    ωseed := ω, τ := τ,
    hseedPlace := by
      intro j i side
      exact (hsf ((j,i),side)).trans (hpermNew j i side),
    hgrowthPlace := hperm2, hseedScore := hfinalSeed, hgrowthRow := hrow, hgrowthCol := hcol }
  let roles := fwGrowthEarlyRoleCells hrect hseedrect hwide hs choice rows cols hr hc sr sc hsr hsc wr wc hwr hwc ∪
    Finset.univ.image (btGrowingOffsetCells
      (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc)
  refine ⟨f, p, b₀, roles, hder, hexp, ⟨?_⟩, ⟨?_⟩, ⟨?_⟩⟩
  · exact {
      roles_eq := rfl
      row_gap := hrowGap
      col_gap := hcolGap
      row_network := BR
      col_network := BC
      endpoints := hends
      row_blocks := hrowBlocks
      col_blocks := hcolBlocks
      invoice := hinvoice
      row_midpoint := hmidrow
      col_midpoint := hmidcol
      main_eq := hmain
      anti_eq := hanti
      rectangle_fixed := hrectfixed
      off_roles := houtside
      roles_image := himage
      old_pool := hpool₀
      old_injective := hinj
      flows := hflows
    }
  · exact {
      T := T
      U := U
      V := V
      selected := hsel2
      slot_images := hmap2
      main_identity := hmain2
      anti_identity := hanti2
      midpoint_bounds := ⟨hE1, hD2, hE2, hE3, hE3s⟩
      main_deviation := hbmain
      anti_deviation := hbanti
    }
  · exact {
      candidates := candidates
      candidate_card := hcard
      kept := kept
      kept_sub := hsub
      kept_card := hkept
      candidates_sub := hcand
      initial_eq := rfl
      intermediate := new
      seed_base := hset
      bridge_stage := hbstage
      wide_stage := hwstage
      seed_intermediate := hsetNew
      bridge_final := hbf
      wide_final := hwf
      seed_final := hsf
    }

end
end Sude
