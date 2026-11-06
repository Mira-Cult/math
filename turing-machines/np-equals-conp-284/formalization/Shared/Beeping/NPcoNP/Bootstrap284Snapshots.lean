import Shared.Beeping.NPcoNP.Bootstrap284WindowReplay

/-! Finite tape snapshots and a checked block interface for the bootstrap.
The block test compares every window cell and derives the exterior from the
window-preserving replay, so no hidden tape data can be discarded. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284Snapshots
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.Bootstrap284Checkpoint
open Shared.Beeping.NPcoNP.Bootstrap284Certificate
open Shared.Beeping.NPcoNP.Bootstrap284WindowReplay

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

def snapshot (ones : List Int) (p : Int) : Bool := decide (p ∈ ones)

def snapshotFits (lo : Int) (width : Nat) (ones : List Int) : Bool :=
  ones.all fun p => decide (lo≤p ∧ p<lo+(width : Int))

theorem snapshot_inWindow (lo : Int) (width : Nat) (ones : List Int)
    (hf : snapshotFits lo width ones=true) : InWindow lo width (snapshot ones) := by
  intro p hp
  by_cases hm : p ∈ ones
  · have hh := (List.all_eq_true.mp hf) p hm
    have hh' : lo≤p ∧ p<lo+(width : Int) := of_decide_eq_true hh
    omega
  · simp [snapshot,hm]

/-- Check the replay, exact duration and complete finite-window checkpoint. -/
def checkBlock (lo : Int) (width : Nat) (ops : List Op)
    (c checkpoint : Config 284) (duration : Nat) : Bool :=
  match replayWindow lo width ops c with
  | none => false
  | some (mid,n) => (n == duration) && sameWindow lo width mid checkpoint

/-- A successful block test is an exact silent physical segment, provided
the input and proposed output snapshots are blank outside the window. -/
theorem checkBlock_sound (lo : Int) (width : Nat) (ops : List Op)
    (c checkpoint : Config 284) (duration : Nat)
    (hc : InWindow lo width c.tape) (hd : InWindow lo width checkpoint.tape)
    (hcheck : checkBlock lo width ops c checkpoint duration=true) :
    silentSegment machine c checkpoint duration := by
  cases hr : replayWindow lo width ops c with
  | none => simp [checkBlock,hr] at hcheck
  | some x =>
    rcases x with ⟨mid,n⟩
    simp only [checkBlock,hr,Bool.and_eq_true,beq_iff_eq] at hcheck
    obtain ⟨hn,hm⟩ := hcheck
    have ⟨hseg,hmid⟩ := replayWindow_sound lo width ops c mid n hc hr
    have he := configs_eq lo width mid checkpoint hmid hd hm
    subst mid
    subst n
    exact hseg
end Shared.Beeping.NPcoNP.Bootstrap284Snapshots
