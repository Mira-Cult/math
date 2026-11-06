import Shared.Beeping.NPcoNP.Source284LastPayloadCopy

/-! One finite source-table pass removes the last payload bit from a nonempty
frame and moves it into the ignored suffix. Repeating this operation could
construct a scratch stream, but this module does not yet implement a loop,
the canonical packed-window loader, or a physical-machine refinement. -/
namespace Shared.Beeping.NPcoNP.Source284PayloadPop

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284WitnessScanArithmetic (pushPairs)
open Shared.Beeping.NPcoNP.Source284TaggedWitnessRoundtrip (pushPairs_snoc rawPairs rawPairs_frame)

/-- Four entry modes turn and cross the delimiter. The first reverse marker
is cleared if it is one; all remaining return states are relocated from the
proved self-delimiting return. -/
def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q < 4 then ⟨b,true,some (q+4)⟩
  else if q < 8 then ⟨b,false,some (q+4)⟩
  else if q < 12 then ⟨b,false,some (12+2*(q-8)+bit b)⟩
  else if q < 20 then ⟨false,false,some (if b then 28+(q-12)/2 else 40+(q-12)/2)⟩
  else shiftRow 20 (Source284ModePrefixReturn.table continuation (q-20) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (20+(32+states)) (table continuation) := by
  have hc := Source284ModePrefixReturn.closed states continuation hn hv
  intro q hq b q' hnext
  by_cases h0 : q < 4
  · simp [table,h0] at hnext; omega
  · by_cases h1 : q < 8
    · simp [table,h0,h1] at hnext; omega
    · by_cases h2 : q < 12
      · cases b <;> simp [table,h0,h1,h2,bit] at hnext <;> omega
      · by_cases h3 : q < 20
        · cases b <;> simp [table,h0,h1,h2,h3] at hnext <;> omega
        · have ht : (shiftRow 20 (Source284ModePrefixReturn.table continuation (q-20) b)).next = some q' := by
            simpa [table,h0,h1,h2,h3] using hnext
          have hq0 : q-20 < 32+states := by omega
          cases he : (Source284ModePrefixReturn.table continuation (q-20) b).next with
          | none => simp [shiftRow,he] at ht
          | some r =>
            have h := hc (q-20) hq0 b r he
            simp [shiftRow,he] at ht
            subst q'
            omega

theorem run_add (t : Nat → Bool → Row) (c : Config) (a b : Nat) :
    run t c (a+b) = run t (run t c a) b := by
  induction b with
  | zero => simp [run]
  | succ b ih =>
    change step t (run t c (a+b)) = step t (run t (run t c a) b)
    rw [ih]

theorem start (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4)
    (left suffix : Nat) :
    run (table continuation) ⟨2*left,suffix,some mode⟩ 2 =
      ⟨2*suffix,left,some (8+mode)⟩ := by
  interval_cases mode <;>
    simp [run,step,table,bit,Nat.testBit_zero] <;>
    congr 1 <;> try split_ifs
  all_goals repeat' constructor
  all_goals omega

/-- The first reversed pair's marker is changed from one to zero. -/
theorem first_pair (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4)
    (left right : Nat) (b : Bool) :
    run (table continuation) ⟨left,4*right+2+(if b then 1 else 0),some (8+mode)⟩ 2 =
      shiftConfig 20 ⟨4*left+2*(if b then 1 else 0),right,some (8+mode)⟩ := by
  interval_cases mode <;> cases b <;>
    simp [run,step,table,bit,shiftConfig,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;>
    congr 1 <;> try split_ifs
  all_goals repeat' constructor
  all_goals omega

/-- If the input frame is empty, the `00` boundary is left unchanged. -/
theorem first_empty (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4)
    (left higher : Nat) :
    run (table continuation) ⟨left,4*higher,some (8+mode)⟩ 2 =
      shiftConfig 20 ⟨4*left,higher,some (20+mode)⟩ := by
  interval_cases mode <;>
    simp [run,step,table,bit,shiftConfig,Nat.testBit_zero,Nat.mul_mod] <;>
    congr 1 <;> try split_ifs
  all_goals repeat' constructor
  all_goals omega

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (20+q) b = shiftRow 20 (Source284ModePrefixReturn.table continuation q b) := by
  have h4 : ¬ 20+q < 4 := by omega
  have h8 : ¬ 20+q < 8 := by omega
  have h12 : ¬ 20+q < 12 := by omega
  have h20 : ¬ 20+q < 20 := by omega
  simp [table,h4,h8,h12,h20]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 20 c) =
      shiftConfig 20 (step (Source284ModePrefixReturn.table continuation) c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (clock : Nat) :
    run (table continuation) (shiftConfig 20 c) clock =
      shiftConfig 20 (run (Source284ModePrefixReturn.table continuation) c clock) := by
  induction clock with
  | zero => rfl
  | succ clock ih => simp only [run,ih,relocated_step]

/-- The remaining unchanged pairs are returned, then the saved certificate
bits are restored. -/
theorem rest (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4)
    (xs : List Bool) (higher suffix : Nat) :
    run (Source284ModePrefixReturn.table continuation)
      ⟨2*suffix,pushPairs (4*higher) xs,some (8+mode)⟩ (2*xs.length+5) =
      ⟨4*higher+mode,encodeFrame xs suffix,some 32⟩ := by
  have ht : 2*xs.length+5 = (2*xs.length)+2+3 := by omega
  rw [ht,Source284ModePrefixReturn.run_add,Source284ModePrefixReturn.run_add,
    Source284ModePrefixReturn.reverse_pairs _ _ hm,rawPairs_frame,
    Source284ModePrefixReturn.boundary _ _ hm,Source284ModePrefixReturn.restore _ _ hm]

/-- A nonempty frame loses its final payload bit; that bit is retained in the
low suffix cell and the former delimiter follows it. -/
theorem pop_return (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4)
    (xs : List Bool) (b : Bool) (higher suffix : Nat) :
    run (table continuation) ⟨2*pushPairs (4*higher) (xs++[b]),suffix,some mode⟩
      (2*(xs++[b]).length+7) =
      ⟨4*higher+mode,encodeFrame xs (4*suffix+bit b),some 52⟩ := by
  have ht : 2*(xs++[b]).length+7 = 2+(2+(2*xs.length+5)) := by simp; omega
  rw [ht,run_add,start _ _ hm,pushPairs_snoc,run_add,first_pair _ _ hm]
  have he : 4*(2*suffix)+2*(if b then 1 else 0) = 2*(4*suffix+bit b) := by
    cases b <;> simp [bit] <;> omega
  rw [he]
  change run (table continuation)
    (shiftConfig 20 ⟨2*(4*suffix+bit b),pushPairs (4*higher) xs,some (8+mode)⟩) _ = _
  rw [relocated_run,rest _ _ hm]
  rfl

/-- The empty frame is a fixed point of the same self-delimiting pass. -/
theorem empty_return (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4)
    (higher suffix : Nat) :
    run (table continuation) ⟨2*pushPairs (4*higher) [],suffix,some mode⟩ 7 =
      ⟨4*higher+mode,encodeFrame [] suffix,some 52⟩ := by
  have ht : 7 = 2+(2+3) := by omega
  rw [ht,run_add,start _ _ hm,run_add]
  simp only [pushPairs]
  rw [first_empty _ _ hm]
  change run (table continuation)
    (shiftConfig 20 ⟨4*(2*suffix),higher,some (20+mode)⟩) 3 = _
  rw [relocated_run,Source284ModePrefixReturn.restore _ _ hm]
  rfl

/-- After the forward scan, the encoded source program returns while moving
the final payload bit across the delimiter into the retained suffix. -/
theorem source_pop_return (states : Nat) (continuation : Nat → Bool → Row)
    (mode : Nat) (hm : mode < 4) (xs : List Bool) (b : Bool) (higher suffix : Nat)
    (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run
      (Source284InputSentinel.description (8+(20+(32+states)))
        (Source284ModePrefixScan.table (table continuation)))
      ⟨2*pushPairs (4*higher) (xs++[b]),suffix,active (16+mode)⟩
      (2*(xs++[b]).length+7) =
      ⟨4*higher+mode,encodeFrame xs (4*suffix+bit b),active 68⟩ := by
  let c : Config := ⟨2*pushPairs (4*higher) (xs++[b]),suffix,some mode⟩
  have hc := closed states continuation hn hv
  have hcm := Source284ModePrefixScan.closed (20+(32+states)) (table continuation) (by omega) hc
  have hcs := Source284InputSentinel.closed (8+(20+(32+states)))
    (Source284ModePrefixScan.table (table continuation)) (by omega) hcm
  have hvalid : Valid (8+(8+(20+(32+states)))) (shiftConfig 8 (shiftConfig 8 c)) := by
    intro q hq
    simp [shiftConfig,c] at hq
    subst q
    omega
  have hr := run_toSource (8+(8+(20+(32+states))))
    (Source284InputSentinel.table (Source284ModePrefixScan.table (table continuation))) 1
    (shiftConfig 8 (shiftConfig 8 c)) hcs hvalid (2*(xs++[b]).length+7)
  have hs : 8+(8+mode) = 16+mode := by omega
  change Source284Relative.run
      (Source284InputSentinel.description (8+(20+(32+states)))
        (Source284ModePrefixScan.table (table continuation)))
      ⟨2*pushPairs (4*higher) (xs++[b]),suffix,active (8+(8+mode))⟩ _ = _ at hr
  rw [hs] at hr
  rw [hr,Source284InputSentinel.relocated_run,Source284ModePrefixScan.relocated_run,
    pop_return _ _ hm]
  rfl

/-- On an original nonempty input, a complete finite source program moves its
last payload bit into the suffix and restores the certificate. Its exact cost
is linear in the original parsed length. -/
theorem source_pop (states : Nat) (continuation : Nat → Bool → Row)
    (xs : List Bool) (b : Bool) (certificate suffix : Nat)
    (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run
      (Source284InputSentinel.description (8+(20+(32+states)))
        (Source284ModePrefixScan.table (table continuation)))
      (Source284Relative.initial (encodeFrame (xs++[b]) suffix) certificate)
      (4*(xs++[b]).length+12) =
      ⟨certificate,encodeFrame xs (4*suffix+bit b),active 68⟩ := by
  have hm : certificate%4 < 4 := Nat.mod_lt certificate (by decide)
  have ht : 4*(xs++[b]).length+12 =
      (4+(2*(xs++[b]).length+1))+(2*(xs++[b]).length+7) := by omega
  have hc := closed states continuation hn hv
  rw [ht,Source284Relative.run_add_clock,
    Source284ModePrefixScan.source_prepare_scan (20+(32+states)) (table continuation)
      (xs++[b]) certificate suffix (by omega) hc,
    source_pop_return states continuation (certificate%4) hm xs b (certificate/4) suffix hn hv,
    Source284InputSentinel.certificate_recovered]

/-- The source-level empty return restores both halves without changing the
frame. -/
theorem source_empty_return (states : Nat) (continuation : Nat → Bool → Row)
    (mode : Nat) (hm : mode < 4) (higher suffix : Nat)
    (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run
      (Source284InputSentinel.description (8+(20+(32+states)))
        (Source284ModePrefixScan.table (table continuation)))
      ⟨2*pushPairs (4*higher) [],suffix,active (16+mode)⟩ 7 =
      ⟨4*higher+mode,encodeFrame [] suffix,active 68⟩ := by
  let c : Config := ⟨2*pushPairs (4*higher) [],suffix,some mode⟩
  have hc := closed states continuation hn hv
  have hcm := Source284ModePrefixScan.closed (20+(32+states)) (table continuation) (by omega) hc
  have hcs := Source284InputSentinel.closed (8+(20+(32+states)))
    (Source284ModePrefixScan.table (table continuation)) (by omega) hcm
  have hvalid : Valid (8+(8+(20+(32+states)))) (shiftConfig 8 (shiftConfig 8 c)) := by
    intro q hq
    simp [shiftConfig,c] at hq
    subst q
    omega
  have hr := run_toSource (8+(8+(20+(32+states))))
    (Source284InputSentinel.table (Source284ModePrefixScan.table (table continuation))) 1
    (shiftConfig 8 (shiftConfig 8 c)) hcs hvalid 7
  have hs : 8+(8+mode) = 16+mode := by omega
  change Source284Relative.run
      (Source284InputSentinel.description (8+(20+(32+states)))
        (Source284ModePrefixScan.table (table continuation)))
      ⟨2*pushPairs (4*higher) [],suffix,active (8+(8+mode))⟩ 7 = _ at hr
  rw [hs] at hr
  rw [hr,Source284InputSentinel.relocated_run,Source284ModePrefixScan.relocated_run,
    empty_return _ _ hm]
  rfl

theorem source_empty (states : Nat) (continuation : Nat → Bool → Row)
    (certificate suffix : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run
      (Source284InputSentinel.description (8+(20+(32+states)))
        (Source284ModePrefixScan.table (table continuation)))
      (Source284Relative.initial (encodeFrame [] suffix) certificate) 12 =
      ⟨certificate,encodeFrame [] suffix,active 68⟩ := by
  have hm : certificate%4 < 4 := Nat.mod_lt certificate (by decide)
  have hc := closed states continuation hn hv
  have ht : 12 = (4+(2*(([] : List Bool).length)+1))+7 := by decide
  rw [ht,Source284Relative.run_add_clock,
    Source284ModePrefixScan.source_prepare_scan (20+(32+states)) (table continuation)
      [] certificate suffix (by omega) hc,
    source_empty_return states continuation (certificate%4) hm (certificate/4) suffix hn hv,
    Source284InputSentinel.certificate_recovered]

/-- The transformed source frame is shorter by one, and the removed bit is
present as the low suffix bit. Higher original suffix bits are retained. -/
theorem pop_data (xs : List Bool) (b : Bool) (suffix : Nat) :
    Source284Parser.length (encodeFrame xs (4*suffix+bit b)) = xs.length ∧
      (4*suffix+bit b)%2 = bit b ∧ (4*suffix+bit b)/4 = suffix := by
  constructor
  · simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  · cases b <;> simp [bit] <;> omega

/-- The transformation clears exactly the former last marker: no other tape
bit is changed. -/
theorem pop_marker (xs : List Bool) (b : Bool) (suffix : Nat) :
    encodeFrame (xs++[b]) suffix = encodeFrame xs (4*suffix+bit b)+4^xs.length := by
  induction xs with
  | nil => cases b <;> simp [encodeFrame,bit] <;> omega
  | cons a xs ih =>
    simp only [List.cons_append,encodeFrame,ih,List.length_cons,pow_succ]
    ring

/-- For every positive-length raw input, the pass has a finite exact cost
and reduces the parsed length by one, with the removed bit in the suffix. -/
theorem source_pop_positive (states : Nat) (continuation : Nat → Bool → Row)
    (input certificate : Nat) (hi : 0 < Source284Parser.length input)
    (hn : 0 < states) (hv : Closed states continuation) :
    ∃ (xs : List Bool) (b : Bool) (suffix : Nat),
      input = encodeFrame (xs++[b]) suffix ∧
      Source284Parser.length input = xs.length+1 ∧
      Source284Relative.run
        (Source284InputSentinel.description (8+(20+(32+states)))
          (Source284ModePrefixScan.table (table continuation)))
        (Source284Relative.initial input certificate) (4*Source284Parser.length input+12) =
        ⟨certificate,encodeFrame xs (4*suffix+bit b),active 68⟩ := by
  obtain ⟨w,suffix,hw⟩ := Source284Parser.encodeFrame_surjective input
  have hlen : Source284Parser.length input = w.length := by
    rw [← hw]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  rcases List.eq_nil_or_concat' w with hz | ⟨xs,b,hx⟩
  · subst w
    simp at hlen
    omega
  · refine ⟨xs,b,suffix,?_,?_,?_⟩
    · simpa [hx] using hw.symm
    · simpa [hx] using hlen
    · rw [hlen,hx,← hw,hx]
      exact source_pop states continuation xs b certificate suffix hn hv

/-- The finite continuation runs after the paid pop on its resulting two
tape halves; no initialization or execution steps are implicit. -/
theorem source_after_pop (states : Nat) (continuation : Nat → Bool → Row)
    (xs : List Bool) (b : Bool) (certificate suffix clock : Nat)
    (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.accepts
      (Source284InputSentinel.description (8+(20+(32+states)))
        (Source284ModePrefixScan.table (table continuation)))
      (encodeFrame (xs++[b]) suffix) certificate (4*(xs++[b]).length+12+clock) =
    Source284Relative.accepts (encode states continuation 1)
      (encodeFrame xs (4*suffix+bit b)) certificate clock := by
  let input := encodeFrame xs (4*suffix+bit b)
  let c : Config := ⟨certificate,input,some 0⟩
  have h0 : Valid states c := by
    intro q hq
    simp [c] at hq
    subst q
    exact hn
  have h1 : Valid (8+(8+(20+(32+states))))
      (shiftConfig 8 (shiftConfig 8 (shiftConfig 20 (shiftConfig 32 c)))) := by
    intro q hq
    simp [shiftConfig,c] at hq
    subst q
    omega
  have hc := closed states continuation hn hv
  have hcm := Source284ModePrefixScan.closed (20+(32+states)) (table continuation) (by omega) hc
  have hcs := Source284InputSentinel.closed (8+(20+(32+states)))
    (Source284ModePrefixScan.table (table continuation)) (by omega) hcm
  have hr1 := run_toSource (8+(8+(20+(32+states))))
    (Source284InputSentinel.table (Source284ModePrefixScan.table (table continuation))) 1
    (shiftConfig 8 (shiftConfig 8 (shiftConfig 20 (shiftConfig 32 c)))) hcs h1 clock
  have hr0 := run_toSource states continuation 1 c hv h0 clock
  change Source284Relative.run
      (Source284InputSentinel.description (8+(20+(32+states)))
        (Source284ModePrefixScan.table (table continuation)))
      ⟨certificate,input,active (8+(8+(20+32)))⟩ clock = _ at hr1
  have hs : 8+(8+(20+32)) = 68 := by omega
  rw [hs] at hr1
  change Source284Relative.run (encode states continuation 1)
      (Source284Relative.initial input certificate) clock = _ at hr0
  unfold Source284Relative.accepts
  rw [Source284Relative.run_add_clock,source_pop states continuation xs b certificate suffix hn hv,
    hr1,hr0,Source284InputSentinel.relocated_run,Source284ModePrefixScan.relocated_run,
    relocated_run,Source284ModePrefixReturn.relocated_run]
  cases h : (run continuation c clock).state <;>
    simp [toSource,shiftConfig,nextState,h,active]

end Shared.Beeping.NPcoNP.Source284PayloadPop
