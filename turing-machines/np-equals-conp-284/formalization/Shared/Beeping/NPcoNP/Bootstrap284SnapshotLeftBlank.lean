import Shared.Beeping.NPcoNP.Bootstrap284ReachableRecurrence

/-! A blank ray to the left of the checked initial marker runway. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284SnapshotLeftBlank
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeAllZeroRecurrence
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
open Shared.Beeping.NPcoNP.UnaryBank
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.Bootstrap284BitSnapshot
open Shared.Beeping.NPcoNP.Bootstrap284PackedStep
open Shared.Beeping.NPcoNP.Bootstrap284SecondDispatch
open Shared.Beeping.NPcoNP.Bootstrap284SecondReturnTimed
open Shared.Beeping.NPcoNP.Bootstrap284TerminalUnit
open Shared.Beeping.NPcoNP.Bootstrap284NextReturnExact
open Shared.Beeping.NPcoNP.Bootstrap284NextSelectorExact
open Shared.Beeping.NPcoNP.Bootstrap284ReachableRecurrence
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 0

/-- The remaining 274 snapshot positions immediately beyond the marker
runway are all blank. This finite packed computation is kernel checked. -/
theorem snapshot_left_blank_prefix : ∀ i : Fin 274,
    returnTape (-3823-(i.val : Int))=false := by
  have h : ∀ i : Fin 274, postReturn (-3823-(i.val : Int))=false := by
    rw [postReturn_eq]
    unfold returnedTape currentTape
    rw [run_2133586]
    decide
  intro i
  rw [return_left_source _ (by omega)]
  exact h i

/-- The entire infinite left ray beyond the runway is blank: the finite
snapshot supplies its in-range cells and its declared exterior is blank. -/
theorem snapshot_left_blank_ray : ∀ q : Int, q≤ -3823 → returnTape q=false := by
  intro q hq
  by_cases hlow : q< -4096
  · rw [return_left_source q (by omega),postReturn_eq]
    unfold returnedTape currentTape
    rw [run_2133586]
    have hn : ¬((-4096:Int)≤q ∧ q<(-4096:Int)+(4104:Int)) := by omega
    simp [setAt,fillRange,toConfig,cfg,bitSnapshot,hn,show q≠ -3 by omega,show q≠6 by omega,
      show q≠ -2 by omega,show ¬((0:Int)≤q ∧ q<3) by omega]
    omega
  · let i := (-3823-q).toNat
    have hi : (i : Int)= -3823-q := Int.toNat_of_nonneg (by omega)
    have hib : i<274 := by omega
    have hh := snapshot_left_blank_prefix ⟨i,hib⟩
    have he : (-3823:Int)-(i : Int)=q := by omega
    simpa only [he] using hh

/-- After the 1,891 reachable marker-present cycles, both the entire left
blank ray and the right bank blank ray remain available. -/
theorem blank_start_runway_end_with_left_ray :
    ∃ (m n : Nat) (out : Int → Bool), 0<m ∧ 1891≤n ∧
      Stage (-3820) 3789 0 (List.replicate 1894 0) 0 out ∧
      (∀ q, q≤ -3823 → out q=false) ∧
      (∀ q, 5+((encode (List.replicate 1895 0)).length : Int)≤q → out q=false) ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-3820) out) (2134479+m+29+n) := by
  obtain ⟨m,seed,hm,hstage,hseedframe,hseedblank,hstart⟩ :=
    blank_start_recurrence_seed_with_frame 1891 (by omega)
  obtain ⟨n,out,hn,hcycles,hfinal,hframe,hblank⟩ :=
    stage_iterate_with_blank_ray 1891 (-38) 7 0 [0,0,0] seed hstage (by simpa using hseedblank)
  have hvalues : [0,0,0] ++ List.replicate 1891 0=List.replicate 1894 0 := by decide
  norm_num only [Nat.cast_ofNat] at hcycles hfinal hframe hblank
  rw [hvalues] at hfinal hblank
  have hbankvalues : 0::List.replicate 1894 0=List.replicate 1895 0 := by decide
  rw [hbankvalues] at hblank
  have hleft : ∀ q, q≤ -3823 → out q=false := by
    intro q hq
    rw [hframe q (by omega),hseedframe q (by omega)]
    exact snapshot_left_blank_ray q hq
  have hall := segAdd machine _ _ _ (2134479+m+29) n hstart hcycles
  exact ⟨m,n,out,hm,hn,hfinal,hleft,by simpa using hblank,hall⟩

#print axioms blank_start_runway_end_with_left_ray
#print axioms snapshot_left_blank_ray
end Shared.Beeping.NPcoNP.Bootstrap284SnapshotLeftBlank
