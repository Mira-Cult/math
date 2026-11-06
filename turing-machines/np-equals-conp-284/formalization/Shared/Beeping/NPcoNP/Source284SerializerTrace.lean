import Shared.Codes.FiniteProgramMarkedCycle
import Shared.Beeping.NPcoNP.Source284DetectorExit
import Shared.Beeping.NPcoNP.Source284FiniteRelativeRun
import Shared.Beeping.NPcoNP.Source284WitnessScratch

/-! The finite tagged serializer observes exactly one source bit per full
cycle. The first theorem concerns the finite binary program; source-level
orientation and marked-row correspondence are proved separately below. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284SerializerTrace

open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel)
open Shared.Codes.FiniteProgramTaggedLoop (canonical result totalCost cost output)
open Shared.Codes.FiniteProgramMarkedCycle (observed)
open Shared.Beeping.NPcoNP.Source284TaggedCyclesSource (processed)

/-- Observations concatenate across an actual live finite-program handoff. -/
theorem observed_append (program : Program) (c d : Config) (n m : Nat)
    (hr : run program c n = some (.inr d)) :
    observed program c (n+m) = observed program c n ++ observed program d m := by
  induction m with
  | zero => simp [observed]
  | succ m ih =>
    rw [Nat.add_succ]
    simp only [observed,ih]
    rw [Shared.ComplexityBridge.TM0FiniteProgram.run_continue _ _ _ _ _ hr]
    simp [List.append_assoc]

/-- Every completed finite sequence of serializer cycles marks exactly the
processed source bits, in order. The returned final head bit has not yet been
processed. -/
theorem cycles_observed (zero one remaining : List Bool) (b : Bool) (xs L : List Bool)
    (c : Config) (hq : c.1 = 0) (ht : TapeRel c.2 (canonical (remaining++L) b xs).2) :
    observed (Shared.Codes.FiniteProgramTaggedLoop.program zero one) c
      (totalCost zero one remaining b xs) = processed remaining b := by
  induction remaining generalizing b xs c with
  | nil => rfl
  | cons p ps ih =>
    have ht' : TapeRel c.2 (canonical (p::(ps++L)) b xs).2 := by simpa using ht
    obtain ⟨d,hd,hq',htape⟩ := Shared.Codes.FiniteProgramTaggedLoop.cycle_related
      zero one b p xs (ps++L) c hq ht'
    have hp : 0 < cost zero one b xs := by simp [cost]
    have hone := Shared.Codes.FiniteProgramMarkedCycle.observed_cycle zero one b p xs (ps++L)
      c hq ht' (cost zero one b xs) hp (by omega)
    change observed _ c (cost zero one b xs + totalCost zero one ps p (output zero one b xs)) = _
    rw [observed_append _ _ _ _ _ hd,hone]
    simpa [processed] using ih p (output zero one b xs) d hq' htape

open Shared.Beeping.NPcoNP.Source284TableRun (Valid toSource)
open Shared.Beeping.NPcoNP.Source284FiniteTapeStep (represented)
open Shared.Beeping.NPcoNP.Source284FiniteRelativeRows (index rows)
open Shared.Beeping.NPcoNP.Source284CompileRecords (codeState)

/-- The source's finite relative state and the numeric tape halves for a
finite-program configuration and its current physical orientation. -/
def logical (t : Tape) (rev : Bool) (q : Nat) : Source284TableRun.Config :=
  let r := represented t rev (codeState q rev)
  ⟨r.left,r.right,some (index q rev)⟩

theorem logical_toSource (t : Tape) (rev : Bool) (q : Nat) :
    toSource (logical t rev q) = represented t rev (codeState q rev) := by
  cases rev <;> simp [logical,toSource,Shared.Beeping.NPcoNP.Source284TableEncode.nextState,
    Shared.Beeping.NPcoNP.Source284FiniteRelativeRows.active_index,
    Shared.Beeping.NPcoNP.Source284FiniteTapeStep.represented]

theorem logical_valid (program : Program) (t : Tape) (rev : Bool) (q : Nat)
    (hq : q < program.length) : Valid (rows program).length (logical t rev q) := by
  intro r hr
  simp [logical] at hr
  subst r
  cases rev <;> simp [Shared.Beeping.NPcoNP.Source284FiniteRelativeRows.index,
    Shared.Beeping.NPcoNP.Source284CompileRecords.bit] <;> omega

/-- A continuing finite-program run has an exact logical relative-table
configuration, including whichever direction is under the head. -/
theorem logical_run (program : Program) (hv : valid program = true)
    (t tape' : Tape) (rev : Bool) (q q' n : Nat) (hq : q < program.length)
    (hr : run program (q,t) n = some (.inr (q',tape'))) :
    ∃ rev', Shared.Beeping.NPcoNP.Source284TableRun.run
      (Source284ListTables.table (rows program)) (logical t rev q) n = logical tape' rev' q' := by
  have hc := logical_valid program t rev q hq
  have hsrc := Shared.Beeping.NPcoNP.Source284TableRun.run_toSource (rows program).length
    (Source284ListTables.table (rows program)) 1 (logical t rev q)
    (Shared.Beeping.NPcoNP.Source284FiniteRelativeRows.closed program hv) hc n
  rw [Shared.Beeping.NPcoNP.Source284FiniteRelativeRun.encode_eq_compile,logical_toSource] at hsrc
  have hrel := Source284FiniteProgramRun.run_related program
    (Source284FiniteProgramRun.closed_of_valid program hv) q t rev hq n
  rw [hr] at hrel
  obtain ⟨rev',he⟩ := Source284EncoderSourceWindow.live_invert program q' tape' _ hrel
  refine ⟨rev',?_⟩
  apply Source284WitnessScratch.toSource_injective
  rw [logical_toSource,← hsrc]
  exact he

theorem logical_mark (zero one : List Bool) (t : Tape) (rev : Bool) (q : Nat)
    (hq : q < (Shared.Codes.FiniteProgramTaggedLoop.program zero one).length) :
    ((Source284DetectorProduct.serializerMarks zero one)[index q rev]?).getD false = decide (q=0) := by
  have hi : index q rev < (Source284DetectorProduct.serializerRows zero one).length := by
    cases rev <;> simp [Source284DetectorProduct.serializerRows,
      Shared.Beeping.NPcoNP.Source284FiniteRelativeRows.index,
      Shared.Beeping.NPcoNP.Source284CompileRecords.bit] <;> omega
  rw [Source284DetectorProduct.serializer_mark zero one (index q rev) hi]
  cases rev <;> simp [Shared.Beeping.NPcoNP.Source284FiniteRelativeRows.index,
    Shared.Beeping.NPcoNP.Source284CompileRecords.bit] <;> omega

theorem logical_read (t : Tape) (rev : Bool) (q : Nat) :
    (logical t rev q).right.testBit 0 = t.2.1 := by
  have h := Shared.Beeping.NPcoNP.Source284FiniteTapeStep.represented_read t rev (codeState q rev)
  cases hb : t.2.1 <;>
    simp [logical,Nat.testBit_zero,Shared.Beeping.NPcoNP.Source284FiniteTapeStep.digit,hb] at h ⊢ <;> omega

/-- The detector product's source-row observations equal finite-program
entry observations for every prefix of a known continuing run. -/
theorem source_observed_eq (zero one : List Bool) (t : Tape) (rev : Bool)
    (q : Nat) (last : Config) (N : Nat)
    (hq : q < (Shared.Codes.FiniteProgramTaggedLoop.program zero one).length)
    (hfinal : run (Shared.Codes.FiniteProgramTaggedLoop.program zero one) (q,t) N = some (.inr last)) :
    ∀ n ≤ N,
      Source284DetectorProduct.observed (Source284DetectorProduct.serializerMarks zero one)
        (Source284ListTables.table (Source284DetectorProduct.serializerRows zero one)) (logical t rev q) n =
      observed (Shared.Codes.FiniteProgramTaggedLoop.program zero one) (q,t) n := by
  let program := Shared.Codes.FiniteProgramTaggedLoop.program zero one
  let original := Source284ListTables.table (rows program)
  have hv : valid program = true := Shared.Codes.FiniteProgramTaggedLoop.program_valid zero one
  intro n hn
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn' : n ≤ N := by omega
    obtain ⟨d,hd⟩ := Shared.Codes.FiniteProgramMarkedCycle.live_prefix program (q,t) last N n hn' hfinal
    have hin := Shared.Codes.FiniteProgramLink.run_in_range program hv (q,t) hq n
    rw [hd] at hin
    change d.1 < program.length at hin
    obtain ⟨rev',hs⟩ := logical_run program hv t d.2 rev q d.1 n hq (by simpa using hd)
    change Shared.Beeping.NPcoNP.Source284TableRun.run
      (Source284ListTables.table (Source284DetectorProduct.serializerRows zero one)) (logical t rev q) n =
        logical d.2 rev' d.1 at hs
    change run (Shared.Codes.FiniteProgramTaggedLoop.program zero one) (q,t) n = some (.inr d) at hd
    change Source284DetectorProduct.observed (Source284DetectorProduct.serializerMarks zero one)
        (Source284ListTables.table (Source284DetectorProduct.serializerRows zero one)) (logical t rev q) n ++
      (match (Shared.Beeping.NPcoNP.Source284TableRun.run
        (Source284ListTables.table (Source284DetectorProduct.serializerRows zero one)) (logical t rev q) n).state with
        | none => []
        | some r => if ((Source284DetectorProduct.serializerMarks zero one)[r]?).getD false then
            [(Shared.Beeping.NPcoNP.Source284TableRun.run
              (Source284ListTables.table (Source284DetectorProduct.serializerRows zero one)) (logical t rev q) n).right.testBit 0]
          else []) =
      observed (Shared.Codes.FiniteProgramTaggedLoop.program zero one) (q,t) n ++
        (match run (Shared.Codes.FiniteProgramTaggedLoop.program zero one) (q,t) n with
          | some (.inr e) => if e.1 = 0 then [e.2.2.1] else []
          | _ => [])
    rw [ih hn',hs,hd]
    have hm := logical_mark zero one d.2 rev' d.1 hin
    have hb := logical_read d.2 rev' d.1
    change _ ++ (if ((Source284DetectorProduct.serializerMarks zero one)[index d.1 rev']?).getD false then
      [(logical d.2 rev' d.1).right.testBit 0] else []) = _
    rw [hm,hb]
    simp


/-- For any exact finite-tape initialization, the source row marks during
all completed cycles are exactly the processed raw bits. -/
theorem source_cycles_observed (zero one remaining : List Bool) (b : Bool)
    (xs L : List Bool) (c : Config) (rev : Bool) (hq : c.1 = 0)
    (ht : TapeRel c.2 (canonical (remaining++L) b xs).2) :
    Source284DetectorProduct.observed (Source284DetectorProduct.serializerMarks zero one)
      (Source284ListTables.table (Source284DetectorProduct.serializerRows zero one))
      (logical c.2 rev 0) (totalCost zero one remaining b xs) = processed remaining b := by
  obtain ⟨last,hfinal,_,_⟩ := Shared.Codes.FiniteProgramTaggedLoop.cycles zero one remaining b xs L c hq ht
  have hpos : 0 < (Shared.Codes.FiniteProgramTaggedLoop.program zero one).length :=
    Shared.Codes.FiniteProgramLink.valid_nonempty _ (Shared.Codes.FiniteProgramTaggedLoop.program_valid zero one)
  cases c with
  | mk q tape =>
    simp only at hq; subst q
    have he := source_observed_eq zero one tape rev 0 last (totalCost zero one remaining b xs)
      hpos hfinal (totalCost zero one remaining b xs) (by omega)
    exact he.trans (cycles_observed zero one remaining b xs L (0,tape) rfl ht)

/-- Adding one unused predecessor ensures that the previously final head bit
is processed too; the unused predecessor remains under the head. -/
theorem processed_append (rest : List Bool) (first dummy : Bool) :
    processed (rest++[dummy]) first = first::rest := by
  induction rest generalizing first with
  | nil => rfl
  | cons b bs ih => simpa [processed] using congrArg (List.cons first) (ih b)

/-- Observations of any deterministic source run grow only by appending
symbols, so an earlier marked visit gives a proper prefix of the later trace. -/
theorem source_observed_prefix (marks : List Bool) (original : Nat → Bool → Source284TableEncode.Row)
    (c : Source284TableRun.Config) (i n : Nat) (hi : i ≤ n) :
    ∃ extra, Source284DetectorProduct.observed marks original c n =
      Source284DetectorProduct.observed marks original c i ++ extra := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hi
  induction d with
  | zero => exact ⟨[],by simp⟩
  | succ d ih =>
    obtain ⟨extra,he⟩ := ih (by omega)
    refine ⟨extra ++ (match (Source284TableRun.run original c (i+d)).state with
      | none => []
      | some q => if (marks[q]?).getD false then [(Source284TableRun.run original c (i+d)).right.testBit 0] else []),?_⟩
    rw [Nat.add_succ]
    change Source284DetectorProduct.observed marks original c (i+d) ++ _ = _
    rw [he]
    simp [List.append_assoc]
    rfl

/-- At a marked source visit strictly before a known complete trace, the
observations already made form a proper prefix of that complete trace. -/
theorem marked_proper_prefix (marks : List Bool) (original : Nat → Bool → Source284TableEncode.Row)
    (c : Source284TableRun.Config) (i n : Nat) (hi : i < n) (body : List Bool)
    (hfull : Source284DetectorProduct.observed marks original c n = body)
    (hmarked : ∃ q, (Source284TableRun.run original c i).state = some q ∧
      (marks[q]?).getD false = true) :
    ∃ j, j < body.length ∧ Source284DetectorProduct.observed marks original c i = body.take j := by
  obtain ⟨q,hstate,hmark⟩ := hmarked
  obtain ⟨extra,he⟩ := source_observed_prefix marks original c (i+1) n (by omega)
  have hnext : Source284DetectorProduct.observed marks original c (i+1) =
      Source284DetectorProduct.observed marks original c i ++
        [(Source284TableRun.run original c i).right.testBit 0] := by
    simp [Source284DetectorProduct.observed,hstate,hmark]
  rw [hnext] at he
  rw [hfull] at he
  refine ⟨(Source284DetectorProduct.observed marks original c i).length,?_,?_⟩
  · have hlen := congrArg List.length he
    simp only [List.length_append,List.length_singleton] at hlen
    omega
  · rw [he]
    simp

/-- Equivalent finite tapes give identical logical relative configurations. -/
theorem logical_tapeRel (t u : Tape) (rev : Bool) (q : Nat) (h : TapeRel t u) :
    logical t rev q = logical u rev q := by
  have hr := Source284TaggedCyclesSource.represented_tapeRel t u rev (codeState q rev) h
  simp only [logical]
  rw [hr]

/-- The last predecessor supplied to the cycle loop remains under the head. -/
theorem result_last (zero one rest : List Bool) (first dummy : Bool) (xs : List Bool) :
    (result zero one (rest++[dummy]) first xs).1 = dummy := by
  induction rest generalizing first xs with
  | nil => rfl
  | cons b bs ih => simpa [result] using ih b (output zero one first xs)

/-- A completed prepared source run reaches the canonical tagged-buffer tape
in one of the two explicit relative orientations. -/
theorem source_cycles_final (zero one remaining : List Bool) (b : Bool)
    (xs L : List Bool) (c : Config) (rev : Bool) (hq : c.1 = 0)
    (ht : TapeRel c.2 (canonical (remaining++L) b xs).2) :
    ∃ rev', Source284TableRun.run
      (Source284ListTables.table (Source284DetectorProduct.serializerRows zero one))
      (logical c.2 rev 0) (totalCost zero one remaining b xs) =
      logical (canonical L (result zero one remaining b xs).1
        (result zero one remaining b xs).2).2 rev' 0 := by
  obtain ⟨last,hfinal,hlast,htape⟩ := Shared.Codes.FiniteProgramTaggedLoop.cycles
    zero one remaining b xs L c hq ht
  have hpos : 0 < (Shared.Codes.FiniteProgramTaggedLoop.program zero one).length :=
    Shared.Codes.FiniteProgramLink.valid_nonempty _ (Shared.Codes.FiniteProgramTaggedLoop.program_valid zero one)
  cases c with
  | mk q tape =>
    simp only at hq; subst q
    cases last with
    | mk q' tape' =>
      simp only at hlast; subst q'
      obtain ⟨rev',hr⟩ := logical_run (Shared.Codes.FiniteProgramTaggedLoop.program zero one)
        (Shared.Codes.FiniteProgramTaggedLoop.program_valid zero one) tape tape' rev 0 0
        (totalCost zero one remaining b xs) hpos hfinal
      refine ⟨rev',?_⟩
      change Source284TableRun.run (Source284ListTables.table
        (Source284FiniteRelativeRows.rows (Shared.Codes.FiniteProgramTaggedLoop.program zero one)))
        (logical tape rev 0) (totalCost zero one remaining b xs) = _
      rw [hr,logical_tapeRel tape' _ rev' 0 htape]

/-- On a prepared tagged buffer whose source side contains the whole
reversed joined body plus one unused predecessor, the actual serializer
visits marked source rows for exactly the whole body and takes the paid
first exit. This does not construct the prepared buffer or prove a physical
284-state table refinement. -/
theorem serializer_exit_prepared (zero one : List Bool) (continuationStates : Nat)
    (continuation : Nat → Bool → Source284TableEncode.Row) (hn : 0 < continuationStates)
    (hcont : Source284TableRun.Closed continuationStates continuation)
    (x w rest : List Bool) (dummy : Bool) (xs L : List Bool) (c : Config) (rev : Bool)
    (hbody : (Source284JoinedPrefixScan.joinedBody x w).reverse = false::rest)
    (hq : c.1 = 0) (ht : TapeRel c.2 (canonical ((rest++[dummy])++L) false xs).2) :
    let remaining := rest++[dummy]
    let N := totalCost zero one remaining false xs
    let states := (Source284DetectorProduct.serializerRows zero one).length
    let marks := Source284DetectorProduct.serializerMarks zero one
    let original := Source284ListTables.table (Source284DetectorProduct.serializerRows zero one)
    let csrc := logical c.2 rev 0
    let last := Source284TableRun.run original csrc N
    Source284Relative.run (Source284TableEncode.encode (Source284DetectorExit.entry states+continuationStates)
      (Source284DetectorExit.table states marks original continuation) 1)
      (toSource (Source284DetectorProduct.lifted .lead csrc)) (N+2+fuel) =
    Source284SourceRelocation.lift (Source284DetectorExit.entry states)
      (Source284Relative.run (Source284TableEncode.encode continuationStates continuation 1)
        ⟨last.left,last.right,Source284TableEncode.active 0⟩ fuel) := by
  dsimp only
  let remaining := rest++[dummy]
  let N := totalCost zero one remaining false xs
  let states := (Source284DetectorProduct.serializerRows zero one).length
  let marks := Source284DetectorProduct.serializerMarks zero one
  let original := Source284ListTables.table (Source284DetectorProduct.serializerRows zero one)
  let csrc := logical c.2 rev 0
  have hfull : Source284DetectorProduct.observed marks original csrc N =
      (Source284JoinedPrefixScan.joinedBody x w).reverse := by
    have h := source_cycles_observed zero one remaining false xs L c rev hq ht
    change Source284DetectorProduct.observed marks original csrc N = processed remaining false at h
    rw [h,processed_append,hbody]
  have hprefix : ∀ i < N,
      (∃ q, (Source284TableRun.run original csrc i).state = some q ∧ (marks[q]?).getD false = true) →
      ∃ j, j < (Source284JoinedPrefixScan.joinedBody x w).length ∧
        Source284DetectorProduct.observed marks original csrc i =
          (Source284JoinedPrefixScan.joinedBody x w).reverse.take j := by
    intro i hi hm
    obtain ⟨j,hj,he⟩ := marked_proper_prefix marks original csrc i N hi
      (Source284JoinedPrefixScan.joinedBody x w).reverse hfull hm
    exact ⟨j,by simpa using hj,he⟩
  have hmarked : ∃ q, (Source284TableRun.run original csrc N).state = some q ∧
      (marks[q]?).getD false = true := by
    obtain ⟨last,hfinal,hlast,_⟩ := Shared.Codes.FiniteProgramTaggedLoop.cycles
      zero one remaining false xs L c hq ht
    have hpos : 0 < (Shared.Codes.FiniteProgramTaggedLoop.program zero one).length :=
      Shared.Codes.FiniteProgramLink.valid_nonempty _ (Shared.Codes.FiniteProgramTaggedLoop.program_valid zero one)
    cases c with
    | mk q tape =>
      simp only at hq; subst q
      cases last with
      | mk q' tape' =>
        simp only at hlast; subst q'
        have hrun : run (Shared.Codes.FiniteProgramTaggedLoop.program zero one) (0,tape) N =
            some (.inr (0,tape')) := hfinal
        obtain ⟨rev',he⟩ := logical_run (Shared.Codes.FiniteProgramTaggedLoop.program zero one)
          (Shared.Codes.FiniteProgramTaggedLoop.program_valid zero one) tape tape' rev 0 0 N hpos hrun
        change Source284TableRun.run original csrc N = logical tape' rev' 0 at he
        refine ⟨index 0 rev',?_,?_⟩
        · rw [he]; rfl
        · have hm := logical_mark zero one tape' rev' 0 hpos
          simpa [marks] using hm
  have hvalid : Valid states csrc := logical_valid _ _ _ _
    (Shared.Codes.FiniteProgramLink.valid_nonempty _ (Shared.Codes.FiniteProgramTaggedLoop.program_valid zero one))
  exact Source284DetectorExit.serializer_body_exit zero one continuationStates continuation hn hcont
    csrc hvalid x w N fuel hprefix hfull hmarked

end Shared.Beeping.NPcoNP.Source284SerializerTrace
