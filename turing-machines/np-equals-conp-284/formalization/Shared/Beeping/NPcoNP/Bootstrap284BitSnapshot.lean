import Shared.Beeping.NPcoNP.Bootstrap284Snapshots

/-! Bit-packed finite snapshots for checkpoint replay. Their declared bounds
force a blank exterior even if the supplied integer contains higher bits. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284BitSnapshot
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.Bootstrap284Checkpoint
open Shared.Beeping.NPcoNP.Bootstrap284Snapshots

def bitSnapshot (base : Int) (span bits : Nat) (p : Int) : Bool :=
  if base≤p ∧ p<base+(span : Int) then bits.testBit (p-base).toNat else false

/-- Enclosing the declared snapshot interval proves blankness of every
cell outside the larger window, without a premise about the integer's size. -/
theorem bitSnapshot_inWindow (lo base : Int) (width span bits : Nat)
    (hlo : lo≤base) (hhi : base+(span : Int)≤lo+(width : Int)) :
    InWindow lo width (bitSnapshot base span bits) := by
  intro p hp
  have hn : ¬ (base≤p ∧ p<base+(span : Int)) := by omega
  simp [bitSnapshot,hn]

/-- Any successful bounded block can target a bit-packed snapshot while
retaining the original unbounded physical tape semantics. -/
theorem checked_bitBlock (lo base : Int) (width span bits : Nat)
    (ops : List Bootstrap284Certificate.Op) (c : Config 284)
    (q : Fin 284) (head : Int) (duration : Nat)
    (hc : InWindow lo width c.tape)
    (hlo : lo≤base) (hhi : base+(span : Int)≤lo+(width : Int))
    (ht : checkBlock lo width ops c (cfg q head (bitSnapshot base span bits)) duration=true) :
    silentSegment machine c (cfg q head (bitSnapshot base span bits)) duration := by
  apply checkBlock_sound lo width ops c _ duration hc
  · exact bitSnapshot_inWindow lo base width span bits hlo hhi
  · exact ht

end Shared.Beeping.NPcoNP.Bootstrap284BitSnapshot
