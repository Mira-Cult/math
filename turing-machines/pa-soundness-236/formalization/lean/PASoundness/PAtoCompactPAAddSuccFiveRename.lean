import PASoundness.PAtoCompactScopedActiveReplace
import PASoundness.PAtoCompactAlphaMapOne
import PASoundness.PAtoCompactMapNamesCongr

/-! Capture-safe, simultaneous relabeling of the five fixed addition-successor
operand names. The targets may alias and may coincide with any original name.
The caller supplies binder freshness and fresh staging names; no arithmetic or
semantic soundness result is assumed. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPAAddSuccFiveRename
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactAlphaMapOne PASoundness.PAtoCompactMapNamesCongr
open PASoundness.PAtoCompactScopedActiveReplace PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactGuardElimination

def mapping (x y z u v n : Nat) : Nat :=
  if n = 30 then x else if n = 31 then y else if n = 32 then z else if n = 38 then u else if n = 45 then v else n

def staged (q : Nat) (f : Formula) : Formula :=
  replace 45 (q+4) (replace 38 (q+3) (replace 32 (q+2) (replace 31 (q+1) (replace 30 q f))))

def finished (q x y z u v : Nat) (f : Formula) : Formula :=
  replace (q+4) v (replace (q+3) u (replace (q+2) z (replace (q+1) y (replace q x (staged q f)))))

/-- Five fresh stages preserve simultaneous substitution even for aliased
or swapped target names. -/
theorem finished_eq_map (f : Formula) (q x y z u v : Nat)
    (hq : 45 < q) (hx : x < q) (hy : y < q) (hz : z < q) (hu : u < q) (hv : v < q)
    (h30 : 30 ∉ f.binders) (h31 : 31 ∉ f.binders) (h32 : 32 ∉ f.binders)
    (h38 : 38 ∉ f.binders) (h45 : 45 ∉ f.binders)
    (hqn : ∀ i, i < 5 → q+i ∉ f.names) :
    finished q x y z u v f = mapNames (mapping x y z u v) f := by
  have hqB (i : Nat) (hi : i < 5) : q+i ∉ f.binders := by
    intro h; exact hqn i hi (Formula.binders_subset_names f h)
  have hq0 : q ∉ f.binders := by simpa using hqB 0 (by omega)
  have hq1 := hqB 1 (by omega)
  have hq2 := hqB 2 (by omega)
  have hq3 := hqB 3 (by omega)
  have hq4 := hqB 4 (by omega)
  unfold finished staged
  rw [← map_eq_replace (q+4) v _ (by simpa only [replace_binders] using hq4),
      ← map_eq_replace (q+3) u _ (by simpa only [replace_binders] using hq3),
      ← map_eq_replace (q+2) z _ (by simpa only [replace_binders] using hq2),
      ← map_eq_replace (q+1) y _ (by simpa only [replace_binders] using hq1),
      ← map_eq_replace q x _ (by simpa only [replace_binders] using hq0),
      ← map_eq_replace 45 (q+4) _ (by simpa only [replace_binders] using h45),
      ← map_eq_replace 38 (q+3) _ (by simpa only [replace_binders] using h38),
      ← map_eq_replace 32 (q+2) _ (by simpa only [replace_binders] using h32),
      ← map_eq_replace 31 (q+1) _ (by simpa only [replace_binders] using h31),
      ← map_eq_replace 30 q f h30]
  repeat' rw [mapNames_compose]
  apply mapNames_congr
  intro n hn
  have hnq (i : Nat) (hi : i < 5) : n ≠ q+i := fun h => hqn i hi (h ▸ hn)
  have hnq0 : n ≠ q := by simpa using hnq 0 (by omega)
  have hnq1 := hnq 1 (by omega)
  have hnq2 := hnq 2 (by omega)
  have hnq3 := hnq 3 (by omega)
  have hnq4 := hnq 4 (by omega)
  have h_stage_0_src_30 : q ≠ 30 := by omega
  have h_stage_0_src_31 : q ≠ 31 := by omega
  have h_stage_0_src_32 : q ≠ 32 := by omega
  have h_stage_0_src_38 : q ≠ 38 := by omega
  have h_stage_0_src_45 : q ≠ 45 := by omega
  have h_stage_0_stage_1 : q ≠ q+1 := by omega
  have h_stage_0_stage_2 : q ≠ q+2 := by omega
  have h_stage_0_stage_3 : q ≠ q+3 := by omega
  have h_stage_0_stage_4 : q ≠ q+4 := by omega
  have h_stage_1_src_30 : q+1 ≠ 30 := by omega
  have h_stage_1_src_31 : q+1 ≠ 31 := by omega
  have h_stage_1_src_32 : q+1 ≠ 32 := by omega
  have h_stage_1_src_38 : q+1 ≠ 38 := by omega
  have h_stage_1_src_45 : q+1 ≠ 45 := by omega
  have h_stage_1_stage_0 : q+1 ≠ q := by omega
  have h_stage_1_stage_2 : q+1 ≠ q+2 := by omega
  have h_stage_1_stage_3 : q+1 ≠ q+3 := by omega
  have h_stage_1_stage_4 : q+1 ≠ q+4 := by omega
  have h_stage_2_src_30 : q+2 ≠ 30 := by omega
  have h_stage_2_src_31 : q+2 ≠ 31 := by omega
  have h_stage_2_src_32 : q+2 ≠ 32 := by omega
  have h_stage_2_src_38 : q+2 ≠ 38 := by omega
  have h_stage_2_src_45 : q+2 ≠ 45 := by omega
  have h_stage_2_stage_0 : q+2 ≠ q := by omega
  have h_stage_2_stage_1 : q+2 ≠ q+1 := by omega
  have h_stage_2_stage_3 : q+2 ≠ q+3 := by omega
  have h_stage_2_stage_4 : q+2 ≠ q+4 := by omega
  have h_stage_3_src_30 : q+3 ≠ 30 := by omega
  have h_stage_3_src_31 : q+3 ≠ 31 := by omega
  have h_stage_3_src_32 : q+3 ≠ 32 := by omega
  have h_stage_3_src_38 : q+3 ≠ 38 := by omega
  have h_stage_3_src_45 : q+3 ≠ 45 := by omega
  have h_stage_3_stage_0 : q+3 ≠ q := by omega
  have h_stage_3_stage_1 : q+3 ≠ q+1 := by omega
  have h_stage_3_stage_2 : q+3 ≠ q+2 := by omega
  have h_stage_3_stage_4 : q+3 ≠ q+4 := by omega
  have h_stage_4_src_30 : q+4 ≠ 30 := by omega
  have h_stage_4_src_31 : q+4 ≠ 31 := by omega
  have h_stage_4_src_32 : q+4 ≠ 32 := by omega
  have h_stage_4_src_38 : q+4 ≠ 38 := by omega
  have h_stage_4_src_45 : q+4 ≠ 45 := by omega
  have h_stage_4_stage_0 : q+4 ≠ q := by omega
  have h_stage_4_stage_1 : q+4 ≠ q+1 := by omega
  have h_stage_4_stage_2 : q+4 ≠ q+2 := by omega
  have h_stage_4_stage_3 : q+4 ≠ q+3 := by omega
  have h_out_x_0 : x ≠ q := by omega
  have h_out_x_1 : x ≠ q+1 := by omega
  have h_out_x_2 : x ≠ q+2 := by omega
  have h_out_x_3 : x ≠ q+3 := by omega
  have h_out_x_4 : x ≠ q+4 := by omega
  have h_out_y_0 : y ≠ q := by omega
  have h_out_y_1 : y ≠ q+1 := by omega
  have h_out_y_2 : y ≠ q+2 := by omega
  have h_out_y_3 : y ≠ q+3 := by omega
  have h_out_y_4 : y ≠ q+4 := by omega
  have h_out_z_0 : z ≠ q := by omega
  have h_out_z_1 : z ≠ q+1 := by omega
  have h_out_z_2 : z ≠ q+2 := by omega
  have h_out_z_3 : z ≠ q+3 := by omega
  have h_out_z_4 : z ≠ q+4 := by omega
  have h_out_u_0 : u ≠ q := by omega
  have h_out_u_1 : u ≠ q+1 := by omega
  have h_out_u_2 : u ≠ q+2 := by omega
  have h_out_u_3 : u ≠ q+3 := by omega
  have h_out_u_4 : u ≠ q+4 := by omega
  have h_out_v_0 : v ≠ q := by omega
  have h_out_v_1 : v ≠ q+1 := by omega
  have h_out_v_2 : v ≠ q+2 := by omega
  have h_out_v_3 : v ≠ q+3 := by omega
  have h_out_v_4 : v ≠ q+4 := by omega
  by_cases h30n : n = 30
  · subst n; simp only [Function.comp_apply, rename, mapping, if_pos, if_false, Nat.reduceEqDiff, *]
  · by_cases h31n : n = 31
    · subst n; simp only [Function.comp_apply, rename, mapping, if_pos, if_false, Nat.reduceEqDiff, *]
    · by_cases h32n : n = 32
      · subst n; simp only [Function.comp_apply, rename, mapping, if_pos, if_false, Nat.reduceEqDiff, *]
      · by_cases h38n : n = 38
        · subst n; simp only [Function.comp_apply, rename, mapping, if_pos, if_false, Nat.reduceEqDiff, *]
        · by_cases h45n : n = 45
          · subst n; simp only [Function.comp_apply, rename, mapping, if_pos, if_false, *]
          · simp [Function.comp_apply, rename, mapping, h30n, h31n, h32n, h38n, h45n,
              hnq0, hnq1, hnq2, hnq3, hnq4]

/-- Derivations are relabeled by the same capture-safe staged substitution. -/
def simultaneous_derivation (f : Formula) (q x y z u v : Nat)
    (hq : 45 < q) (hx : x < q) (hy : y < q) (hz : z < q) (hu : u < q) (hv : v < q)
    (h30 : 30 ∉ f.binders) (h31 : 31 ∉ f.binders) (h32 : 32 ∉ f.binders)
    (h38 : 38 ∉ f.binders) (h45 : 45 ∉ f.binders)
    (hxB : x ∉ f.binders) (hyB : y ∉ f.binders) (hzB : z ∉ f.binders)
    (huB : u ∉ f.binders) (hvB : v ∉ f.binders)
    (hqn : ∀ i, i < 5 → q+i ∉ f.names) (d : KDerivation f.encode) :
    KDerivation (mapNames (mapping x y z u v) f).encode := by
  have hqB (i : Nat) (hi : i < 5) : q+i ∉ f.binders := by
    intro h; exact hqn i hi (Formula.binders_subset_names f h)
  have hq0 : q ∉ f.binders := by simpa using hqB 0 (by omega)
  have hq1 := hqB 1 (by omega)
  have hq2 := hqB 2 (by omega)
  have hq3 := hqB 3 (by omega)
  have hq4 := hqB 4 (by omega)
  have d1 := replace_derivation 30 q f h30 hq0 d
  have d2 := replace_derivation 31 (q+1) _ (by simpa only [replace_binders] using h31) (by simpa only [replace_binders] using hq1) d1
  have d3 := replace_derivation 32 (q+2) _ (by simpa only [replace_binders] using h32) (by simpa only [replace_binders] using hq2) d2
  have d4 := replace_derivation 38 (q+3) _ (by simpa only [replace_binders] using h38) (by simpa only [replace_binders] using hq3) d3
  have d5 := replace_derivation 45 (q+4) _ (by simpa only [replace_binders] using h45) (by simpa only [replace_binders] using hq4) d4
  have d6 := replace_derivation q x _ (by simpa only [replace_binders] using hq0) (by simpa only [replace_binders] using hxB) d5
  have d7 := replace_derivation (q+1) y _ (by simpa only [replace_binders] using hq1) (by simpa only [replace_binders] using hyB) d6
  have d8 := replace_derivation (q+2) z _ (by simpa only [replace_binders] using hq2) (by simpa only [replace_binders] using hzB) d7
  have d9 := replace_derivation (q+3) u _ (by simpa only [replace_binders] using hq3) (by simpa only [replace_binders] using huB) d8
  have d10 := replace_derivation (q+4) v _ (by simpa only [replace_binders] using hq4) (by simpa only [replace_binders] using hvB) d9
  change KDerivation (finished q x y z u v f).encode at d10
  rw [finished_eq_map f q x y z u v hq hx hy hz hu hv h30 h31 h32 h38 h45 hqn] at d10
  exact d10
theorem simultaneous_derivation_certificate (f : Formula) (q x y z u v : Nat)
    (hq : 45 < q) (hx : x < q) (hy : y < q) (hz : z < q) (hu : u < q) (hv : v < q)
    (h30 : 30 ∉ f.binders) (h31 : 31 ∉ f.binders) (h32 : 32 ∉ f.binders)
    (h38 : 38 ∉ f.binders) (h45 : 45 ∉ f.binders)
    (hxB : x ∉ f.binders) (hyB : y ∉ f.binders) (hzB : z ∉ f.binders)
    (huB : u ∉ f.binders) (hvB : v ∉ f.binders)
    (hqn : ∀ i, i < 5 → q+i ∉ f.names) (d : KDerivation f.encode) :
    theoremCode (certificate (simultaneous_derivation f q x y z u v hq hx hy hz hu hv
      h30 h31 h32 h38 h45 hxB hyB hzB huB hvB hqn d)) =
        (mapNames (mapping x y z u v) f).encode := certificate_correct _
end PASoundness.PAtoCompactPAAddSuccFiveRename
#print axioms PASoundness.PAtoCompactPAAddSuccFiveRename.finished_eq_map
#print axioms PASoundness.PAtoCompactPAAddSuccFiveRename.simultaneous_derivation
#print axioms PASoundness.PAtoCompactPAAddSuccFiveRename.simultaneous_derivation_certificate
