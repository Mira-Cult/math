import Shared.Beeping.NPcoNP.Source284CutoffPreparation
import Shared.Beeping.NPcoNP.Source284TaggedHandoff

/-! A paid two-bit tag gate followed by raw witness conversion and the
autonomous cutoff comparator. Crossing the two zero tag bits adds one zero
unary pair on the opposite tape half: therefore `k` initially supplied pairs
represent exactly cutoff `k+1`, not cutoff `k`. The unary data remain supplied
at entry; the original input-to-bound construction and zero-cutoff case remain
separate obligations. -/
set_option maxRecDepth 4096
namespace Shared.Beeping.NPcoNP.Source284PositiveTaggedCutoff

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)

def rawStates (states : Nat) : Nat := 155+(48+(4+states))

def rawTable (verifier : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284ScratchFlipPipeline.table
    (Source284PayloadSentinel.table (Source284CutoffPreparation.comparator verifier))

theorem raw_closed (states : Nat) (verifier : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states verifier) : Closed (rawStates states) (rawTable verifier) := by
  have hc := Source284CutoffPreparation.comparator_closed states verifier hn hv
  have hs := Source284PayloadSentinel.closed (48+(4+states))
    (Source284CutoffPreparation.comparator verifier) (by omega) hc
  have hf := Source284ScratchFlipPipeline.closed (13+(48+(4+states)))
    (Source284PayloadSentinel.table (Source284CutoffPreparation.comparator verifier)) (by omega) hs
  have he : 142+(13+(48+(4+states))) = rawStates states := by simp [rawStates]; omega
  rw [he] at hf
  exact hf

theorem raw_description (states : Nat) (verifier : Nat → Bool → Row) :
    encode (rawStates states) (rawTable verifier) 1 = Source284CutoffPreparation.description states verifier := by
  simp [rawStates,rawTable,Source284CutoffPreparation.description,
    Source284PayloadSentinelPipeline.description,Source284ScratchFlipPipeline.description]
  congr 1; omega

def table (states : Nat) (verifier : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284TaggedHandoff.table (rawStates states) (rawTable verifier) Source284TaggedHandoff.rejectTable

def description (states : Nat) (verifier : Nat → Bool → Row) : Nat :=
  encode (3+rawStates states+1) (table states verifier) 1

theorem table_closed (states : Nat) (verifier : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states verifier) : Closed (3+rawStates states+1) (table states verifier) := by
  exact Source284TaggedHandoff.closed (rawStates states) 1 (rawTable verifier)
    Source284TaggedHandoff.rejectTable (by simp [rawStates]) (by omega)
    (raw_closed states verifier hn hv) Source284TaggedHandoff.reject_closed

theorem extra_zero_pair (k otherHalf : Nat) :
    4*pairTape (List.replicate k false) otherHalf = pairTape (List.replicate (k+1) false) otherHalf := by
  simp [pairTape,Source284PayloadLoop.scratch,bit,List.replicate_succ]

/-- A valid tag is crossed in two paid steps. Its two zero cells become
exactly one additional unary pair, including when `k = 0`. -/
theorem source_tag_dispatch (states : Nat) (verifier : Nat → Bool → Row)
    (k certificate otherHalf : Nat) (hn : 0 < states) (hv : Closed states verifier)
    (htag : certificate%4 = 0) :
    Source284Relative.run (description states verifier)
      (Source284Relative.initial certificate (pairTape (List.replicate k false) otherHalf)) 2 =
      ⟨pairTape (List.replicate (k+1) false) otherHalf,certificate/4,active 3⟩ := by
  let c : Config := ⟨pairTape (List.replicate k false) otherHalf,certificate,some 0⟩
  have hc : Valid (3+rawStates states+1) c := by
    intro q hq; simp [c] at hq; subst q; omega
  have hr := run_toSource (3+rawStates states+1) (table states verifier) 1 c
    (table_closed states verifier hn hv) hc 2
  change Source284Relative.run (description states verifier)
    (Source284Relative.initial certificate (pairTape (List.replicate k false) otherHalf)) _ = _ at hr
  rw [hr]
  dsimp only [c,table]
  rw [Source284TaggedHandoff.dispatch]
  have h0 : certificate%2 = 0 := by omega
  have h1 : (certificate/2)%2 = 0 := by omega
  simp [htag,h0,h1,extra_zero_pair,toSource,nextState,active]

/-- After the two-step tag check, every subsequent step has precisely the
same accepting behavior as the raw cutoff program at the original positive
cutoff `k+1`. Both tables are finite and the simulation is charged. -/
theorem accepts_after_valid_tag (states : Nat) (verifier : Nat → Bool → Row)
    (k certificate otherHalf clock : Nat) (hn : 0 < states) (hv : Closed states verifier)
    (htag : certificate%4 = 0) :
    Source284Relative.accepts (description states verifier) certificate
      (pairTape (List.replicate k false) otherHalf) (2+clock) =
    Source284Relative.accepts (Source284CutoffPreparation.description states verifier) (certificate/4)
      (pairTape (List.replicate (k+1) false) otherHalf) clock := by
  let c : Config := ⟨pairTape (List.replicate (k+1) false) otherHalf,certificate/4,some 0⟩
  have hv0 : Valid (rawStates states) c := by
    intro q hq; simp [c] at hq; subst q; simp [rawStates]
  have hv1 : Valid (3+rawStates states+1) (shiftConfig 3 c) := by
    intro q hq; simp [c,shiftConfig] at hq; subst q; simp [rawStates]
  have hr0 := run_toSource (rawStates states) (rawTable verifier) 1 c (raw_closed states verifier hn hv) hv0 clock
  have hr1 := run_toSource (3+rawStates states+1) (table states verifier) 1 (shiftConfig 3 c)
    (table_closed states verifier hn hv) hv1 clock
  rw [raw_description] at hr0
  change Source284Relative.run (Source284CutoffPreparation.description states verifier)
    (Source284Relative.initial (certificate/4) (pairTape (List.replicate (k+1) false) otherHalf)) clock = _ at hr0
  change Source284Relative.run (description states verifier)
    ⟨pairTape (List.replicate (k+1) false) otherHalf,certificate/4,active 3⟩ clock = _ at hr1
  change Source284Relative.run (description states verifier)
    ⟨pairTape (List.replicate (k+1) false) otherHalf,certificate/4,active 3⟩ clock =
    toSource (run (Source284TaggedHandoff.table (rawStates states) (rawTable verifier)
      Source284TaggedHandoff.rejectTable) (shiftConfig 3 c) clock) at hr1
  rw [Source284TaggedHandoff.good_run (rawStates states) (rawTable verifier)
    Source284TaggedHandoff.rejectTable c (raw_closed states verifier hn hv) hv0] at hr1
  unfold Source284Relative.accepts
  rw [Source284Relative.run_add_clock,source_tag_dispatch states verifier k certificate otherHalf hn hv htag,
    hr1,hr0]
  cases hs : (run (rawTable verifier) c clock).state <;>
    simp [toSource,shiftConfig,nextState,hs,active]

/-- If all executions from a fixed clock onward reject, absorbing acceptance
also rules out acceptance at every earlier clock. -/
theorem never_of_after (desc input certificate start : Nat)
    (h : ∀ extra, Source284Relative.accepts desc input certificate (start+extra) = false) :
    ∀ clock, Source284Relative.accepts desc input certificate clock = false := by
  intro clock
  by_cases ht : start ≤ clock
  · have he : clock = start+(clock-start) := by omega
    rw [he]
    exact h _
  · apply Bool.eq_false_iff.mpr
    intro ha
    have hm := Source284Relative.accepts_clock_mono desc input certificate clock (start-clock) ha
    have he : clock+(start-clock) = start := by omega
    rw [he] at hm
    have h0 := h 0
    simp only [Nat.add_zero] at h0
    rw [h0] at hm
    contradiction

/-- A valid tagged witness exceeding the original positive cutoff `k+1`
never accepts at any clock, even if the verifier accepts immediately. -/
theorem valid_overlong_never_accepts (states : Nat) (verifier : Nat → Bool → Row)
    (k certificate otherHalf : Nat) (hn : 0 < states) (hv : Closed states verifier)
    (htag : certificate%4 = 0)
    (hover : Source284TaggedWitnessCodec.decode (k+1) certificate = none) :
    ∀ clock, Source284Relative.accepts (description states verifier) certificate
      (pairTape (List.replicate k false) otherHalf) clock = false := by
  apply never_of_after _ _ _ 2
  intro extra
  rw [accepts_after_valid_tag states verifier k certificate otherHalf extra hn hv htag]
  exact Source284CutoffPreparation.source_tagged_overlong_never_accepts states verifier
    (k+1) certificate otherHalf hn hv htag hover extra

/-- A malformed tag reaches the explicit nonaccepting branch in two steps. -/
theorem source_bad_dispatch (states : Nat) (verifier : Nat → Bool → Row)
    (k certificate otherHalf : Nat) (hn : 0 < states) (hv : Closed states verifier)
    (htag : certificate%4 ≠ 0) :
    Source284Relative.run (description states verifier)
      (Source284Relative.initial certificate (pairTape (List.replicate k false) otherHalf)) 2 =
      ⟨4*pairTape (List.replicate k false) otherHalf+2*(certificate%2)+(certificate/2)%2,
        certificate/4,active (3+rawStates states)⟩ := by
  let c : Config := ⟨pairTape (List.replicate k false) otherHalf,certificate,some 0⟩
  have hc : Valid (3+rawStates states+1) c := by
    intro q hq; simp [c] at hq; subst q; omega
  have hr := run_toSource (3+rawStates states+1) (table states verifier) 1 c
    (table_closed states verifier hn hv) hc 2
  change Source284Relative.run (description states verifier)
    (Source284Relative.initial certificate (pairTape (List.replicate k false) otherHalf)) _ = _ at hr
  rw [hr]
  dsimp only [c,table]
  rw [Source284TaggedHandoff.dispatch]
  simp [htag,toSource,nextState,active]

theorem reject_entry_never_accepts (states : Nat) (verifier : Nat → Bool → Row)
    (left right clock : Nat) (hn : 0 < states) (hv : Closed states verifier) :
    (Source284Relative.run (description states verifier)
      ⟨left,right,active (3+rawStates states)⟩ clock).state ≠ 0 := by
  let c : Config := ⟨left,right,some 0⟩
  have hc : Valid (3+rawStates states+1) (shiftConfig (3+rawStates states) c) := by
    intro q hq; simp [c,shiftConfig] at hq; subst q; omega
  have hr := run_toSource (3+rawStates states+1) (table states verifier) 1
    (shiftConfig (3+rawStates states) c) (table_closed states verifier hn hv) hc clock
  change Source284Relative.run (description states verifier)
    ⟨left,right,active (3+rawStates states)⟩ clock = _ at hr
  change Source284Relative.run (description states verifier)
    ⟨left,right,active (3+rawStates states)⟩ clock =
    toSource (run (Source284TaggedHandoff.table (rawStates states) (rawTable verifier)
      Source284TaggedHandoff.rejectTable) (shiftConfig (3+rawStates states) c) clock) at hr
  rw [Source284TaggedHandoff.bad_run] at hr
  rw [hr]
  have hs := Source284TaggedHandoff.reject_run_state left right clock
  change (run Source284TaggedHandoff.rejectTable c clock).state = some 0 at hs
  cases hrun : run Source284TaggedHandoff.rejectTable c clock with
  | mk l r q =>
    have hq : q = some 0 := by simpa [hrun] using hs
    subst q
    simp [shiftConfig,toSource,nextState,active,rawStates]

/-- All malformed tags are rejected at every clock in the same table. -/
theorem invalid_tag_never_accepts (states : Nat) (verifier : Nat → Bool → Row)
    (k certificate otherHalf : Nat) (hn : 0 < states) (hv : Closed states verifier)
    (htag : certificate%4 ≠ 0) :
    ∀ clock, Source284Relative.accepts (description states verifier) certificate
      (pairTape (List.replicate k false) otherHalf) clock = false := by
  apply never_of_after _ _ _ 2
  intro extra
  unfold Source284Relative.accepts
  rw [Source284Relative.run_add_clock,source_bad_dispatch states verifier k certificate otherHalf hn hv htag]
  simp only [beq_eq_false_iff_ne]
  exact reject_entry_never_accepts states verifier _ _ extra hn hv

/-- Either a malformed tag or a witness beyond the original positive
cutoff is rejected by the same executable table at every clock. -/
theorem decoded_none_never_accepts (states : Nat) (verifier : Nat → Bool → Row)
    (k certificate otherHalf : Nat) (hn : 0 < states) (hv : Closed states verifier)
    (hbad : Source284TaggedWitnessCodec.decode (k+1) certificate = none) :
    ∀ clock, Source284Relative.accepts (description states verifier) certificate
      (pairTape (List.replicate k false) otherHalf) clock = false := by
  by_cases htag : certificate%4 = 0
  · exact valid_overlong_never_accepts states verifier k certificate otherHalf hn hv htag hbad
  · exact invalid_tag_never_accepts states verifier k certificate otherHalf hn hv htag

namespace Fixtures
open Source284PreparedCutoff.Fixtures (acceptImmediately accept_closed)

/-- For the original cutoff one, the tag contributes the sole pair; a
two-bit witness is rejected even by an immediately accepting verifier. -/
example : ∀ clock, Source284Relative.accepts (description 1 acceptImmediately) 28 30 clock = false := by
  have h := decoded_none_never_accepts 1 acceptImmediately 0 28 7
    (by omega) accept_closed (by decide +kernel)
  simpa [pairTape,Source284PayloadLoop.scratch,bit] using h

/-- A malformed tag is rejected for every clock, independent of the verifier. -/
example : ∀ clock, Source284Relative.accepts (description 1 acceptImmediately) 3 30 clock = false := by
  have h := invalid_tag_never_accepts 1 acceptImmediately 0 3 7
    (by omega) accept_closed (by decide +kernel)
  simpa [pairTape,Source284PayloadLoop.scratch,bit] using h

/-- With one pre-positioned pair, the valid zero tag produces two pairs,
so a two-bit witness is not incorrectly rejected by an off-by-one bound. -/
theorem exact_bound_accepts : Source284Relative.accepts (description 1 acceptImmediately) 28 120 172 = true := by
  have ht := accepts_after_valid_tag 1 acceptImmediately 1 28 7 170
    (by omega) accept_closed (by decide +kernel)
  have hraw := Source284CutoffPreparation.Fixtures.exact_bound_accepts
  simpa [pairTape,Source284PayloadLoop.scratch,bit] using ht.trans hraw
end Fixtures

end Shared.Beeping.NPcoNP.Source284PositiveTaggedCutoff
