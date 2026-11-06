import Shared.Beeping.NPcoNP.Source284MatchLoopSource
import Shared.Beeping.NPcoNP.Source284RawScannerCutoff
import Shared.Beeping.NPcoNP.Source284TaggedWitnessCodec
import Shared.Beeping.NPcoNP.Source284WindowRewind

/-! Autonomous bounded witness-length comparison for prepared tape halves.
The unary bound and flipped witness frame are supplied on the tape, not
preloaded as free control states. A fixed finite table marks them in lockstep,
routes an overlong frame to a nonaccepting sink, and exposes the other two
outcomes to a supplied continuation. Constructing this prepared arrangement
from the original source input and a polynomial witness bound remains open. -/
set_option maxRecDepth 4096
namespace Shared.Beeping.NPcoNP.Source284PreparedCutoff

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)

/-- On the comparator's result entries, mode one is a nonaccepting sink.
Modes zero and two take a paid turn into the supplied finite verifier.
Mode three is also a sink. -/
def router (verifier : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 ∨ q = 2 then ⟨b,true,some 4⟩
  else if q = 1 ∨ q = 3 then ⟨b,false,some 1⟩
  else shiftRow 4 (verifier (q-4) b)

theorem router_closed (states : Nat) (verifier : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states verifier) : Closed (4+states) (router verifier) := by
  intro q hq b q' hnext
  by_cases hs : q < 4
  · interval_cases q <;> simp [router] at hnext <;> omega
  · have h02 : ¬ (q = 0 ∨ q = 2) := by omega
    have h13 : ¬ (q = 1 ∨ q = 3) := by omega
    have ht : (shiftRow 4 (verifier (q-4) b)).next = some q' := by
      simpa [router,h02,h13] using hnext
    cases he : (verifier (q-4) b).next with
    | none => simp [shiftRow,he] at ht
    | some r =>
      have h := hv (q-4) (by omega) b r he
      simp [shiftRow,he] at ht
      subst q'; omega

theorem reject_run (verifier : Nat → Bool → Row) (left right fuel : Nat) :
    (run (router verifier) ⟨left,right,some 1⟩ fuel).state = some 1 := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    cases hc : run (router verifier) ⟨left,right,some 1⟩ fuel with
    | mk l r q =>
      have hq : q = some 1 := by simpa [hc] using ih
      subst q
      simp [run,hc,step,router]

theorem router_row (verifier : Nat → Bool → Row) (q : Nat) (b : Bool) :
    router verifier (4+q) b = shiftRow 4 (verifier q b) := by
  simp [router, show 4+q ≠ 2 by omega, show 4+q ≠ 1 by omega,
    show 4+q ≠ 3 by omega]

theorem router_step (verifier : Nat → Bool → Row) (c : Config) :
    step (router verifier) (shiftConfig 4 c) = shiftConfig 4 (step verifier c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,router_row,shiftRow]
      split <;> rfl

theorem router_run (verifier : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (router verifier) (shiftConfig 4 c) fuel = shiftConfig 4 (run verifier c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,router_step]

theorem router_good_turn (verifier : Nat → Bool → Row) (mode left right : Nat)
    (hm : mode = 0 ∨ mode = 2) :
    step (router verifier) ⟨left,right,some mode⟩ = ⟨right,left,some 4⟩ := by
  apply Source284WindowRewind.generic_turn
  intro b
  simp [router,hm]

/-- The raw frame length is precisely the fixed-window decoder's cutoff
criterion, including arbitrary high suffixes and missing virtual payload bits. -/
theorem decode_none_iff_length (limit : Nat) (w : List Bool) (suffix : Nat) :
    Source284WitnessWindow.decode limit (encodeFrame w suffix) = none ↔ limit < w.length := by
  have h₁ := Source284RawScannerCutoff.raw_source_reject limit (encodeFrame w suffix) 0 1
  have h₂ := Source284ScannerCutoffBridge.source_frame_marker limit w 0 suffix 1
  exact h₁.symm.trans h₂

def description (states : Nat) (verifier : Nat → Bool → Row) : Nat :=
  Source284MatchLoopSource.description (4+states) (router verifier)

/-- The finite table autonomously compares any prepared unary cutoff against
any prepared framed payload. The overlong branch is exact for the original
window decoder, and the number of steps is at most quadratic in the cutoff,
even when the payload or its high suffix is arbitrarily large. -/
theorem prepared_comparison (states : Nat) (verifier : Nat → Bool → Row)
    (limit : Nat) (w : List Bool) (suffix otherHalf : Nat)
    (hn : 0 < states) (hv : Closed states verifier) :
    ∃ left right mode t,
      t ≤ 4*limit*limit+20*limit+16 ∧
      Source284Relative.run (description states verifier)
        (Source284Relative.initial (2*flipped (w++[false]) suffix)
          (pairTape (List.replicate limit false) otherHalf)) t =
        ⟨left,right,active (48+mode)⟩ ∧
      (mode = 1 ↔ Source284WitnessWindow.decode limit (encodeFrame w suffix) = none) ∧
      (mode = 0 ↔ w.length < limit) ∧ (mode = 2 ↔ limit = w.length) := by
  have hc := router_closed states verifier hn hv
  obtain ⟨left,right,mode,hr,h0,h1,h2⟩ := Source284MatchLoopSource.total_compare
    (4+states) (router verifier) limit w otherHalf suffix (by omega) hc
  refine ⟨left,right,mode,Source284MatchLoopSource.compareCost (min limit w.length),?_,hr,?_,h0,h2⟩
  · have hm : min limit w.length ≤ limit := Nat.min_le_left _ _
    unfold Source284MatchLoopSource.compareCost
    have hp : min limit w.length * min limit w.length ≤ limit*limit := Nat.mul_le_mul hm hm
    nlinarith
  · rw [decode_none_iff_length]
    exact h1

/-- With the original zero tag, the dynamic comparison has exactly the
original tagged decoder's rejection condition. -/
theorem tagged_decode_none_iff (limit : Nat) (w : List Bool) (suffix : Nat) :
    Source284TaggedWitnessCodec.decode limit (4*encodeFrame w suffix) = none ↔ limit < w.length := by
  simpa [Source284TaggedWitnessCodec.decode] using decode_none_iff_length limit w suffix

/-- The mode-one continuation is a real source-level nonaccepting sink. -/
theorem source_reject_forever (states : Nat) (verifier : Nat → Bool → Row)
    (left right fuel : Nat) (hn : 0 < states) (hv : Closed states verifier) :
    (Source284Relative.run (description states verifier) ⟨left,right,active 49⟩ fuel).state ≠ 0 := by
  have hc := router_closed states verifier hn hv
  have hr := Source284MatchLoopSource.source_after (4+states) (router verifier) 1 left right fuel
    (by omega) (by omega) hc
  change Source284Relative.run (description states verifier) ⟨left,right,active (48+1)⟩ fuel = _ at hr
  rw [hr]
  have hs := reject_run verifier left right fuel
  cases hc' : run (router verifier) ⟨left,right,some 1⟩ fuel with
  | mk l r q =>
    have hq : q = some 1 := by simpa [hc'] using hs
    subst q
    simp [shiftConfig,toSource,nextState,active]

/-- Both successful comparison modes take one paid, tape-preserving turn
to the verifier entry. The original half orientation is therefore reversed. -/
theorem source_good_turn (states : Nat) (verifier : Nat → Bool → Row)
    (mode left right : Nat) (hn : 0 < states) (hv : Closed states verifier)
    (hm : mode = 0 ∨ mode = 2) :
    Source284Relative.run (description states verifier) ⟨left,right,active (48+mode)⟩ 1 =
      ⟨right,left,active 52⟩ := by
  have hc := router_closed states verifier hn hv
  have hr := Source284MatchLoopSource.source_after (4+states) (router verifier) mode left right 1
    (by omega) (by omega) hc
  change Source284Relative.run (description states verifier) _ _ = _ at hr
  change Source284Relative.run (description states verifier) _ _ =
    toSource (shiftConfig 48 (step (router verifier) ⟨left,right,some mode⟩)) at hr
  rw [router_good_turn verifier mode left right hm] at hr
  exact hr

/-- After the paid turn, the supplied verifier runs inside the same finite
source table with its usual finite-state closure hypothesis. -/
theorem source_after_verifier (states : Nat) (verifier : Nat → Bool → Row)
    (mode left right fuel : Nat) (hn : 0 < states) (hm : mode < states) (hv : Closed states verifier) :
    Source284Relative.run (description states verifier) ⟨left,right,active (52+mode)⟩ fuel =
      toSource (shiftConfig 48 (shiftConfig 4 (run verifier ⟨left,right,some mode⟩ fuel))) := by
  have hc := router_closed states verifier hn hv
  have hr := Source284MatchLoopSource.source_after (4+states) (router verifier) (4+mode)
    left right fuel (by omega) (by omega) hc
  have he : 48+(4+mode) = 52+mode := by omega
  rw [he] at hr
  change Source284Relative.run (description states verifier) _ _ = _ at hr
  change Source284Relative.run (description states verifier) _ _ =
    toSource (shiftConfig 48 (run (router verifier) (shiftConfig 4 ⟨left,right,some mode⟩) fuel)) at hr
  rw [router_run] at hr
  exact hr

/-- An overlong prepared witness reaches the sink within the quadratic
bound and cannot have accepted even before reaching it. -/
theorem prepared_overlong_never_accepts (states : Nat) (verifier : Nat → Bool → Row)
    (limit : Nat) (w : List Bool) (suffix otherHalf : Nat)
    (hn : 0 < states) (hv : Closed states verifier)
    (hover : Source284WitnessWindow.decode limit (encodeFrame w suffix) = none) :
    ∀ clock, Source284Relative.accepts (description states verifier)
      (2*flipped (w++[false]) suffix) (pairTape (List.replicate limit false) otherHalf) clock = false := by
  obtain ⟨left,right,mode,t,_,hr,hm,_,_⟩ :=
    prepared_comparison states verifier limit w suffix otherHalf hn hv
  have hmode : mode = 1 := hm.mpr hover
  subst mode
  have hstate : ∀ extra, (Source284Relative.run (description states verifier)
      (Source284Relative.initial (2*flipped (w++[false]) suffix)
        (pairTape (List.replicate limit false) otherHalf)) (t+extra)).state ≠ 0 := by
    intro extra
    rw [Source284Relative.run_add_clock,hr]
    exact source_reject_forever states verifier left right extra hn hv
  intro clock
  apply Bool.eq_false_iff.mpr
  intro ha
  have hs := (Source284Relative.accepts_iff _ _ _ _).mp ha
  by_cases ht : t ≤ clock
  · have he : clock = t+(clock-t) := by omega
    rw [he] at hs
    exact hstate (clock-t) hs
  · have he : t = clock+(t-clock) := by omega
    have hr' : Source284Relative.run (description states verifier)
        (Source284Relative.initial (2*flipped (w++[false]) suffix)
          (pairTape (List.replicate limit false) otherHalf)) t =
      Source284Relative.run (description states verifier)
        (Source284Relative.run (description states verifier)
          (Source284Relative.initial (2*flipped (w++[false]) suffix)
            (pairTape (List.replicate limit false) otherHalf)) clock) (t-clock) := by
      conv_lhs => rw [he,Source284Relative.run_add_clock]
    have habs := Source284Relative.run_absorbing (description states verifier)
      (Source284Relative.run (description states verifier)
        (Source284Relative.initial (2*flipped (w++[false]) suffix)
          (pairTape (List.replicate limit false) otherHalf)) clock) hs (t-clock)
    have hf := hstate 0
    simp only [Nat.add_zero] at hf
    apply hf
    rw [hr',habs]
    exact hs

/-- A within-cutoff prepared witness reaches the supplied verifier entry,
after the explicit final turn, in a time bounded only by the unary limit. -/
theorem prepared_within_reaches_verifier (states : Nat) (verifier : Nat → Bool → Row)
    (limit : Nat) (w : List Bool) (suffix otherHalf : Nat)
    (hn : 0 < states) (hv : Closed states verifier)
    (hwithin : Source284WitnessWindow.decode limit (encodeFrame w suffix) ≠ none) :
    ∃ left right t, t ≤ 4*limit*limit+20*limit+17 ∧
      Source284Relative.run (description states verifier)
        (Source284Relative.initial (2*flipped (w++[false]) suffix)
          (pairTape (List.replicate limit false) otherHalf)) t =
        ⟨right,left,active 52⟩ := by
  obtain ⟨left,right,mode,t,ht,hr,_,h0,h2⟩ :=
    prepared_comparison states verifier limit w suffix otherHalf hn hv
  have hle : w.length ≤ limit := by
    have hd := decode_none_iff_length limit w suffix
    by_contra h
    have hnone : Source284WitnessWindow.decode limit (encodeFrame w suffix) = none := hd.mpr (by omega)
    exact hwithin hnone
  have hm : mode = 0 ∨ mode = 2 := by
    rcases Nat.lt_or_eq_of_le hle with h | h
    · exact Or.inl (h0.mpr h)
    · exact Or.inr (h2.mpr h.symm)
  refine ⟨left,right,t+1,by omega,?_⟩
  rw [Source284Relative.run_add_clock,hr,source_good_turn states verifier mode left right hn hv hm]

/-- The same rejection guarantee in the tagged codec used by the candidate
coverage interface; high certificate suffixes remain arbitrary. -/
theorem prepared_tagged_overlong_never_accepts (states : Nat) (verifier : Nat → Bool → Row)
    (limit : Nat) (w : List Bool) (suffix otherHalf : Nat)
    (hn : 0 < states) (hv : Closed states verifier)
    (hover : Source284TaggedWitnessCodec.decode limit (4*encodeFrame w suffix) = none) :
    ∀ clock, Source284Relative.accepts (description states verifier)
      (2*flipped (w++[false]) suffix) (pairTape (List.replicate limit false) otherHalf) clock = false := by
  apply prepared_overlong_never_accepts states verifier limit w suffix otherHalf hn hv
  exact (decode_none_iff_length limit w suffix).mpr ((tagged_decode_none_iff limit w suffix).mp hover)

namespace Fixtures

def acceptImmediately (_ : Nat) (b : Bool) : Row := ⟨b,false,none⟩

theorem accept_closed : Closed 1 acceptImmediately := by
  intro q hq b q' hn
  simp [acceptImmediately] at hn

/-- A two-bit witness exceeds unary bound one. Even an accepting verifier
cannot accept this prepared input at any clock. -/
example : ∀ clock, Source284Relative.accepts (description 1 acceptImmediately) 86 120 clock = false := by
  have h := prepared_overlong_never_accepts 1 acceptImmediately 1 [true,false] 0 7
    (by omega) accept_closed (by decide +kernel)
  simpa [flipped,pairTape,Source284PayloadLoop.scratch,bit] using h

/-- A two-bit witness at bound two does reach the verifier entry. -/
example : ∃ left right t, t ≤ 73 ∧
    Source284Relative.run (description 1 acceptImmediately)
      (Source284Relative.initial 86 480) t = ⟨right,left,active 52⟩ := by
  have h := prepared_within_reaches_verifier 1 acceptImmediately 2 [true,false] 0 7
    (by omega) accept_closed (by decide +kernel)
  simpa [flipped,pairTape,Source284PayloadLoop.scratch,bit] using h

example : Source284TaggedWitnessCodec.decode 1 (4*encodeFrame [true,false] 0) = none := by
  decide +kernel
end Fixtures

end Shared.Beeping.NPcoNP.Source284PreparedCutoff
