import Shared.Beeping.NPcoNP.Source284RepeatWorkspaceAliases

/-! Exact suffix sensitivity of the retained scratch stream and its transfer
through the paid workspace continuation. This makes an input-side runway
obligation explicit; it does not construct one or prove candidate coverage. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Shared.Beeping.NPcoNP.Source284ScratchWindowExact
open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284BitWindow
open Shared.Beeping.NPcoNP.Source284Relative (Window)
open Shared.Beeping.NPcoNP.Source284RepeatWorkspace
open Shared.Beeping.NPcoNP.Source284RepeatWorkspaceSource
open Shared.Beeping.NPcoNP.Source284RepeatWorkspaceWindow
open Shared.Beeping.NPcoNP.Source284RepeatWorkspaceAliases

/-- Beyond the fixed prefix, every additional observed bit is exactly one
observed bit of the retained tail. This is an equivalence, including extra=0. -/
theorem right_agree_iff_tail (w : List Bool) (first second extra : Nat) :
    Agree (2*w.length+3+extra) (2*flipped w first) (2*flipped w second) ↔
      Agree extra first second := by
  have hp : 2*2^(2*w.length+2) = 2^(2*w.length+3) := by
    rw [show 2*w.length+3 = (2*w.length+2)+1 by omega,pow_succ]
    ring
  unfold Agree
  rw [flipped_tail w first,flipped_tail w second]
  simp only [Nat.mul_add,← Nat.mul_assoc,hp]
  rw [show 2^(2*w.length+3+extra) = 2^(2*w.length+3)*2^extra from pow_add 2 _ _]
  change Nat.ModEq (2^(2*w.length+3)*2^extra)
    (2*flipped w 0+2^(2*w.length+3)*first)
    (2*flipped w 0+2^(2*w.length+3)*second) ↔ Nat.ModEq (2^extra) first second
  rw [(Nat.ModEq.refl (2*flipped w 0)).add_iff_left]
  exact Nat.ModEq.mul_left_cancel_iff' (pow_ne_zero _ (by decide : 2 ≠ 0))

/-- Exact suffix condition for every observation depth, including depths
inside the frame prefix. -/
theorem right_agree_iff (w : List Bool) (first second depth : Nat) :
    Agree depth (2*flipped w first) (2*flipped w second) ↔
      Agree (depth-(2*w.length+3)) first second := by
  by_cases h : depth ≤ 2*w.length+3
  · have hz : depth-(2*w.length+3)=0 := by omega
    rw [hz]
    exact ⟨fun _ => by simp [Agree,Nat.mod_one],fun _ => right_agree w first second depth h⟩
  · have he : depth = 2*w.length+3+(depth-(2*w.length+3)) := by omega
    nth_rw 1 [he]
    exact right_agree_iff_tail w first second _

/-- A retained-tail window of exactly the needed extra width gives the full
requested scratch-stream window. The width need not be limited to the frame. -/
theorem right_agree_of_tail (w : List Bool) (first second depth : Nat)
    (htail : Agree (depth-(2*w.length+3)) first second) :
    Agree depth (2*flipped w first) (2*flipped w second) := by
  by_cases h : depth ≤ 2*w.length+3
  · exact right_agree w first second depth h
  · have he : depth = 2*w.length+3+(depth-(2*w.length+3)) := by omega
    rw [he]
    exact (right_agree_iff_tail w first second _).2 htail

/-- A continuation may observe past the protected frame when its retained
input suffixes agree over the exact extra window. Both certificates remain
arbitrary, provided the paid certificate-side workspace covers the run. -/
theorem source_alias_window_of_tail (k states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (firstCert secondCert firstSuffix secondSuffix clock radius : Nat)
    (hn : 0 < states) (hv : Closed states continuation)
    (hblank : radius+clock ≤ k*(3*(w.length+1)))
    (htail : Agree (radius+clock-(2*(w.length+1)+3))
      (iterateTail k w.length ((firstSuffix/4)/4))
      (iterateTail k w.length ((secondSuffix/4)/4))) :
    Window radius
      (Source284Relative.run (description k states continuation)
        (Source284Relative.initial (Source284Parser.encodeFrame w firstSuffix) firstCert)
        (elapsed k w+clock))
      (Source284Relative.run (description k states continuation)
        (Source284Relative.initial (Source284Parser.encodeFrame w secondSuffix) secondCert)
        (elapsed k w+clock)) := by
  let right₁ := 2*flipped (w++[false]) (iterateTail k w.length ((firstSuffix/4)/4))
  let right₂ := 2*flipped (w++[false]) (iterateTail k w.length ((secondSuffix/4)/4))
  have ha := source_bounded_window k states continuation w firstCert firstSuffix clock radius hn hv hblank
  have hb := source_bounded_window k states continuation w secondCert secondSuffix clock radius hn hv hblank
  have hright : Agree (radius+clock) right₁ right₂ := by
    apply right_agree_of_tail (w++[false]) _ _ _
    simpa using htail
  have hinit : Window (radius+clock) (Source284Relative.initial right₁ 0)
      (Source284Relative.initial right₂ 0) := by
    exact ⟨rfl,agree_refl _ _,hright⟩
  have hrun := Source284Relative.run_window (encode states continuation 1) clock radius _ _ hinit
  have hrel := lift_window radius (155+226*k) _ _ hrun
  exact window_trans ha (window_trans hrel (window_symm hb))

end Shared.Beeping.NPcoNP.Source284ScratchWindowExact
