import Shared.Beeping.NPcoNP.Source284RepeatWorkspaceWindow
import Shared.Beeping.NPcoNP.Source284NormalizedWindow

/-! A finite observation after the paid workspace loader is insensitive to
arbitrary certificate tails and high input-frame suffixes, provided both
observation bounds fit the actually constructed low-bit windows. This does
not yet construct the canonical verifier's full polynomial workspace. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace Shared.Beeping.NPcoNP.Source284RepeatWorkspaceAliases
open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284BitWindow
open Shared.Beeping.NPcoNP.Source284Relative (Window)
open Shared.Beeping.NPcoNP.Source284RepeatWorkspace
open Shared.Beeping.NPcoNP.Source284RepeatWorkspaceSource
open Shared.Beeping.NPcoNP.Source284RepeatWorkspaceWindow

/-- The retained suffix begins strictly above the two-bit flipped records
and the two-bit terminator. -/
theorem flipped_tail (w : List Bool) (tail : Nat) :
    flipped w tail = flipped w 0 + 2^(2*w.length+2)*tail := by
  induction w with
  | nil => simp [flipped]
  | cons b bs ih =>
    have he : 2*(b::bs).length+2 = (2*bs.length+2)+2 := by simp; omega
    rw [he,pow_add]
    simp only [flipped,ih]
    ring

/-- No high suffix bit can influence the indicated low prefix of the
actual post-loader scratch stream. -/
theorem right_agree (w : List Bool) (first second depth : Nat)
    (hdepth : depth ≤ 2*w.length+3) :
    Agree depth (2*flipped w first) (2*flipped w second) := by
  apply agree_mono hdepth
  have hp : 2*2^(2*w.length+2) = 2^(2*w.length+3) := by
    rw [show 2*w.length+3 = (2*w.length+2)+1 by omega,pow_succ]
    ring
  unfold Agree
  rw [flipped_tail w first,flipped_tail w second]
  simp only [Nat.mul_add,← Nat.mul_assoc,hp,Nat.add_mul_mod_self_left]

theorem window_symm {k : Nat} {a b : Source284Relative.Config} (h : Window k a b) : Window k b a :=
  ⟨h.1.symm,agree_symm h.2.1,agree_symm h.2.2⟩

theorem window_trans {k : Nat} {a b c : Source284Relative.Config}
    (h : Window k a b) (g : Window k b c) : Window k a c :=
  ⟨h.1.trans g.1,h.2.1.trans g.2.1,h.2.2.trans g.2.2⟩

/-- For any two original certificates and any two high frame suffixes, the
same fixed source table gives equal control and equal `radius`-cell tape
windows after the paid initialization and `clock` continuation steps. -/
theorem source_alias_window (k states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (firstCert secondCert firstSuffix secondSuffix clock radius : Nat)
    (hn : 0 < states) (hv : Closed states continuation)
    (hblank : radius+clock ≤ k*(3*(w.length+1)))
    (hframe : radius+clock ≤ 2*(w.length+1)+3) :
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
    apply right_agree (w++[false]) _ _ _
    simpa using hframe
  have hinit : Window (radius+clock) (Source284Relative.initial right₁ 0)
      (Source284Relative.initial right₂ 0) := by
    exact ⟨rfl,agree_refl _ _,hright⟩
  have hrun := Source284Relative.run_window (encode states continuation 1) clock radius _ _ hinit
  have hrel := lift_window radius (155+226*k) _ _ hrun
  exact window_trans ha (window_trans hrel (window_symm hb))

/-- Two compiled passes always supply enough blank cells for the entire
fixed low prefix of the flipped frame, including the terminator. -/
theorem two_pass_alias_window (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (firstCert secondCert firstSuffix secondSuffix clock radius : Nat)
    (hn : 0 < states) (hv : Closed states continuation)
    (hframe : radius+clock ≤ 2*(w.length+1)+3) :
    Window radius
      (Source284Relative.run (description 2 states continuation)
        (Source284Relative.initial (Source284Parser.encodeFrame w firstSuffix) firstCert)
        (elapsed 2 w+clock))
      (Source284Relative.run (description 2 states continuation)
        (Source284Relative.initial (Source284Parser.encodeFrame w secondSuffix) secondCert)
        (elapsed 2 w+clock)) := by
  apply source_alias_window 2 states continuation w firstCert secondCert firstSuffix secondSuffix clock radius hn hv
  · omega
  · exact hframe

/-- At this explicit linear clock the continuation's control state is
independent of both high suffixes and certificates. -/
theorem two_pass_alias_control (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (firstCert secondCert firstSuffix secondSuffix clock : Nat)
    (hn : 0 < states) (hv : Closed states continuation)
    (hclock : clock ≤ 2*(w.length+1)+3) :
    (Source284Relative.run (description 2 states continuation)
      (Source284Relative.initial (Source284Parser.encodeFrame w firstSuffix) firstCert)
      (elapsed 2 w+clock)).state =
    (Source284Relative.run (description 2 states continuation)
      (Source284Relative.initial (Source284Parser.encodeFrame w secondSuffix) secondCert)
      (elapsed 2 w+clock)).state := by
  exact (two_pass_alias_window states continuation w firstCert secondCert firstSuffix secondSuffix clock 0
    hn hv (by simpa using hclock)).1

/-- The same result for arbitrary numeric inputs whose parsed payloads agree,
including noncanonical frames and arbitrary ignored high suffixes. -/
theorem numeric_payload_alias_window (states : Nat) (continuation : Nat → Bool → Row)
    (firstInput secondInput firstCert secondCert clock radius : Nat)
    (hn : 0 < states) (hv : Closed states continuation)
    (halias : Source284RawParse.payload firstInput.bits = Source284RawParse.payload secondInput.bits)
    (hframe : radius+clock ≤ 2*(Source284Parser.length firstInput+1)+3) :
    let w := Source284RawParse.payload firstInput.bits
    Window radius
      (Source284Relative.run (description 2 states continuation)
        (Source284Relative.initial firstInput firstCert) (elapsed 2 w+clock))
      (Source284Relative.run (description 2 states continuation)
        (Source284Relative.initial secondInput secondCert) (elapsed 2 w+clock)) := by
  obtain ⟨w₁,s₁,h₁⟩ := Source284Parser.encodeFrame_surjective firstInput
  obtain ⟨w₂,s₂,h₂⟩ := Source284Parser.encodeFrame_surjective secondInput
  have hp₁ : Source284RawParse.payload firstInput.bits=w₁ := by
    rw [← h₁]
    exact Source284NormalizedWindow.payload_encodeFrame w₁ s₁
  have hp₂ : Source284RawParse.payload secondInput.bits=w₂ := by
    rw [← h₂]
    exact Source284NormalizedWindow.payload_encodeFrame w₂ s₂
  have he : w₁=w₂ := by rw [← hp₁,← hp₂,halias]
  subst w₂
  have hlen : Source284Parser.length firstInput=w₁.length := by
    rw [← h₁]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  have hbound : radius+clock ≤ 2*(w₁.length+1)+3 := by simpa [hlen] using hframe
  have hsecond : Source284Parser.encodeFrame w₁ s₂ = secondInput := by
    rw [← hp₁,halias]
    exact h₂
  have h := two_pass_alias_window states continuation w₁ firstCert secondCert s₁ s₂ clock radius hn hv hbound
  simp only [hp₁]
  rw [← h₁,← hsecond]
  exact h

/-- In the same range, every such alias and every certificate has identical
control behavior after initialization. -/
theorem numeric_payload_alias_control (states : Nat) (continuation : Nat → Bool → Row)
    (firstInput secondInput firstCert secondCert clock : Nat)
    (hn : 0 < states) (hv : Closed states continuation)
    (halias : Source284RawParse.payload firstInput.bits = Source284RawParse.payload secondInput.bits)
    (hclock : clock ≤ 2*(Source284Parser.length firstInput+1)+3) :
    let w := Source284RawParse.payload firstInput.bits
    (Source284Relative.run (description 2 states continuation)
      (Source284Relative.initial firstInput firstCert) (elapsed 2 w+clock)).state =
    (Source284Relative.run (description 2 states continuation)
      (Source284Relative.initial secondInput secondCert) (elapsed 2 w+clock)).state := by
  exact (numeric_payload_alias_window states continuation firstInput secondInput firstCert secondCert
    clock 0 hn hv halias (by simpa using hclock)).1

end Shared.Beeping.NPcoNP.Source284RepeatWorkspaceAliases
