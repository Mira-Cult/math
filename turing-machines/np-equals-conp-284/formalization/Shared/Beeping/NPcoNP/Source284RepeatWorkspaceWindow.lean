import Shared.Beeping.NPcoNP.Source284RepeatWorkspaceSource
import Shared.Beeping.NPcoNP.Source284Truncation

/-! The paid workspace supplies an actual low-bit window for a bounded
continuation; the right-hand scratch value is retained exactly. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace Shared.Beeping.NPcoNP.Source284RepeatWorkspaceWindow

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284BitWindow (Agree)
open Shared.Beeping.NPcoNP.Source284Relative (Window)
open Shared.Beeping.NPcoNP.Source284RepeatWorkspace
open Shared.Beeping.NPcoNP.Source284RepeatWorkspaceSource

/-- The number of repeated passes for an affine target is fixed by its
coefficients, not computed from the tested input. -/
def affinePasses (a b : Nat) : Nat := a+b

theorem affine_bound (a b n : Nat) : a*n+b ≤ affinePasses a b*(3*(n+1)) := by
  unfold affinePasses
  nlinarith

/-- The initial workspace agrees with a blank negative half for every window
that fits in the produced zero block, regardless of the high certificate. -/
theorem initial_window (k wlen certificate right radius : Nat)
    (hsize : radius ≤ k*(3*(wlen+1))) :
    Window radius ⟨2^(k*(3*(wlen+1)))*certificate,right,active 0⟩
      (Source284Relative.initial right 0) := by
  have hd : 2^radius ∣ 2^(k*(3*(wlen+1)))*certificate :=
    dvd_trans (pow_dvd_pow 2 hsize) (dvd_mul_right _ _)
  refine ⟨rfl,?_,?_⟩
  · simp [Agree,Source284Relative.initial,Nat.mod_eq_zero_of_dvd hd]
  · simp [Agree,Source284Relative.initial]

/-- Relocation of both controls preserves the compared tape window. -/
theorem lift_window (radius offset : Nat) (a b : Source284Relative.Config)
    (h : Window radius a b) :
    Window radius (Source284SourceRelocation.lift offset a)
      (Source284SourceRelocation.lift offset b) := by
  rcases h with ⟨hs,hl,hr⟩
  refine ⟨?_,hl,hr⟩
  simp only [Source284SourceRelocation.lift]
  rw [hs]

/-- The paid initialization supplies both the continuation's execution
window and a further `radius` output window, when their sum fits in the
produced block. The positive half is the actual retained scratch input. -/
theorem source_bounded_window (k states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix clock radius : Nat)
    (hn : 0 < states) (hv : Closed states continuation)
    (hsize : radius+clock ≤ k*(3*(w.length+1))) :
    let right := 2*flipped (w++[false]) (iterateTail k w.length ((suffix/4)/4))
    Window radius
      (Source284Relative.run (description k states continuation)
        (Source284Relative.initial (Source284Parser.encodeFrame w suffix) certificate)
        (elapsed k w+clock))
      (Source284SourceRelocation.lift (155+226*k)
        (Source284Relative.run (encode states continuation 1)
          (Source284Relative.initial right 0) clock)) := by
  dsimp only
  let right := 2*flipped (w++[false]) (iterateTail k w.length ((suffix/4)/4))
  let c : Config := ⟨2^(k*(3*(w.length+1)))*certificate,right,some 0⟩
  have hc : Valid states c := by intro q hq; simp [c] at hq; omega
  have hr := run_toSource states continuation 1 c hv hc clock
  have hw : Window (radius+clock) (toSource c) (Source284Relative.initial right 0) := by
    exact initial_window k w.length certificate right (radius+clock) hsize
  have hrun := Source284Relative.run_window (encode states continuation 1) clock radius
    (toSource c) (Source284Relative.initial right 0) hw
  have h := lift_window radius (155+226*k) _ _ hrun
  rw [hr] at h
  rw [Source284SourceRelocation.lift_toSource] at h
  dsimp [c,right] at h
  rw [source_then k states continuation w certificate suffix clock hn hv]
  exact h

/-- A fixed affine bound on execution plus output observation is met by a
fixed number of table copies chosen from its coefficients. -/
theorem affine_bounded_window (a b states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix clock radius : Nat)
    (hn : 0 < states) (hv : Closed states continuation) (hsize : radius+clock ≤ a*w.length+b) :
    let k := affinePasses a b
    let right := 2*flipped (w++[false]) (iterateTail k w.length ((suffix/4)/4))
    Window radius
      (Source284Relative.run (description k states continuation)
        (Source284Relative.initial (Source284Parser.encodeFrame w suffix) certificate)
        (elapsed k w+clock))
      (Source284SourceRelocation.lift (155+226*k)
        (Source284Relative.run (encode states continuation 1)
          (Source284Relative.initial right 0) clock)) := by
  exact source_bounded_window (affinePasses a b) states continuation w certificate suffix clock radius hn hv
    (le_trans hsize (affine_bound a b w.length))

/-- A continuation running for at most the produced window cannot observe
the preserved high certificate on the negative half. Its right input is the
actual retained scratch stream, not an assumed canonical pair encoding. -/
theorem source_bounded_control (k states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix clock : Nat)
    (hn : 0 < states) (hv : Closed states continuation)
    (hclock : clock ≤ k*(3*(w.length+1))) :
    let right := 2*flipped (w++[false]) (iterateTail k w.length ((suffix/4)/4))
    (Source284Relative.run (description k states continuation)
      (Source284Relative.initial (Source284Parser.encodeFrame w suffix) certificate)
      (elapsed k w+clock)).state =
    (Source284SourceRelocation.lift (155+226*k)
      (Source284Relative.run (encode states continuation 1)
        (Source284Relative.initial right 0) clock)).state := by
  dsimp only
  let right := 2*flipped (w++[false]) (iterateTail k w.length ((suffix/4)/4))
  let c : Config := ⟨2^(k*(3*(w.length+1)))*certificate,right,some 0⟩
  have hc : Valid states c := by intro q hq; simp [c] at hq; omega
  have hr := run_toSource states continuation 1 c hv hc clock
  have hw : Window clock (toSource c) (Source284Relative.initial right 0) := by
    exact initial_window k w.length certificate right clock hclock
  have hrun := Source284Relative.run_window (encode states continuation 1) clock 0
    (toSource c) (Source284Relative.initial right 0) (by simpa using hw)
  have hs : (toSource (run continuation c clock)).state =
      (Source284Relative.run (encode states continuation 1) (Source284Relative.initial right 0) clock).state := by
    rw [← hr]
    exact hrun.1
  dsimp [c,right] at hs
  rw [source_then k states continuation w certificate suffix clock hn hv,
    ← Source284SourceRelocation.lift_toSource]
  simp only [Source284SourceRelocation.lift,hs]

/-- Certificates with arbitrary high data give the same bounded control,
provided the observation remains inside the generated blank block. -/
theorem certificate_independent (k states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (first second suffix clock : Nat)
    (hn : 0 < states) (hv : Closed states continuation)
    (hclock : clock ≤ k*(3*(w.length+1))) :
    (Source284Relative.run (description k states continuation)
      (Source284Relative.initial (Source284Parser.encodeFrame w suffix) first)
      (elapsed k w+clock)).state =
    (Source284Relative.run (description k states continuation)
      (Source284Relative.initial (Source284Parser.encodeFrame w suffix) second)
      (elapsed k w+clock)).state := by
  rw [source_bounded_control k states continuation w first suffix clock hn hv hclock,
    source_bounded_control k states continuation w second suffix clock hn hv hclock]

/-- Every fixed affine clock can be accommodated by a fixed finite table. -/
theorem affine_bounded_control (a b states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix clock : Nat)
    (hn : 0 < states) (hv : Closed states continuation) (hclock : clock ≤ a*w.length+b) :
    let k := affinePasses a b
    let right := 2*flipped (w++[false]) (iterateTail k w.length ((suffix/4)/4))
    (Source284Relative.run (description k states continuation)
      (Source284Relative.initial (Source284Parser.encodeFrame w suffix) certificate)
      (elapsed k w+clock)).state =
    (Source284SourceRelocation.lift (155+226*k)
      (Source284Relative.run (encode states continuation 1)
        (Source284Relative.initial right 0) clock)).state := by
  exact source_bounded_control (affinePasses a b) states continuation w certificate suffix clock hn hv
    (le_trans hclock (affine_bound a b w.length))

end Shared.Beeping.NPcoNP.Source284RepeatWorkspaceWindow
