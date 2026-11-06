import Shared.Beeping.NPcoNP.Source284PayloadPopPrecise

/-! A fixed source table intended to repeat the payload-pop pass. The table
redirects the pass's final transition to state zero, and takes a two-step
empty-frame exit to a supplied continuation. Progress is proved separately. -/
namespace Shared.Beeping.NPcoNP.Source284PayloadLoop

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)

def sink (_ : Nat) (b : Bool) : Row := ⟨b,false,some 0⟩

def base : Nat → Bool → Row :=
  Source284InputSentinel.table
    (Source284ModePrefixScan.table (Source284PayloadPop.table sink))

/-- State 0 detects the empty marker. States 64--67 are the four final
certificate-restoration rows of the pop pass. State 68 is the paid turn back;
the supplied finite continuation starts at state 69. -/
def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 ∧ b = false then ⟨false,true,some 68⟩
  else if 64 ≤ q ∧ q < 68 then
    let r := base q b
    ⟨r.write,r.turn,some 0⟩
  else if q = 68 then ⟨b,true,some 69⟩
  else if 69 ≤ q then shiftRow 69 (continuation (q-69) b)
  else base q b

theorem sink_closed : Closed 1 sink := by
  intro q hq b q' h
  simp [sink] at h
  omega

theorem base_closed : Closed 69 base := by
  have hp := Source284PayloadPop.closed 1 sink (by decide) sink_closed
  have hm := Source284ModePrefixScan.closed (20+(32+1)) (Source284PayloadPop.table sink) (by omega) hp
  have hs := Source284InputSentinel.closed (8+(20+(32+1)))
    (Source284ModePrefixScan.table (Source284PayloadPop.table sink)) (by omega) hm
  simpa [base] using hs

/-- Every nonzero base state has a nonzero, continuing successor. This is a
kernel-checked finite table fact, not a claim about arbitrary programs. -/
theorem base_positive_successor :
    ∀ q : Fin 69, q.val ≠ 0 → ∀ b : Bool,
      (base q.val b).next ≠ none ∧ (base q.val b).next ≠ some 0 := by
  decide +kernel

/-- The last four rows enter the base's permanent sink, and its sink remains
in the sink regardless of the scanned bit. -/
theorem base_final_rows :
    ∀ q : Fin 69, 64 ≤ q.val → q.val < 68 → ∀ b : Bool,
      (base q.val b).next = some 68 := by
  decide +kernel

theorem base_sink_row (b : Bool) : base 68 b = ⟨b,false,some 68⟩ := by
  cases b <;> rfl

theorem row_agree (continuation : Nat → Bool → Row) (q : Nat) (b : Bool)
    (hq : q < 69) (hnotfinal : ¬ (64 ≤ q ∧ q < 68)) (hnotexit : q ≠ 68)
    (hstart : q = 0 → b = true) : table continuation q b = base q b := by
  have hzero : ¬ (q = 0 ∧ b = false) := by
    intro h
    have hh := hstart h.1
    cases b <;> simp_all
  simp [table,hzero,hnotfinal,hnotexit,Nat.not_le_of_gt hq]

theorem sink_step (c : Config) (h : c.state = some 68) :
    (step base c).state = some 68 := by
  cases c with
  | mk left right state =>
    simp only at h
    subst state
    simp [step,base_sink_row]

theorem sink_run (c : Config) (h : c.state = some 68) (fuel : Nat) :
    (run base c fuel).state = some 68 := by
  induction fuel with
  | zero => exact h
  | succ fuel ih => exact sink_step _ ih

/-- After the first transition of a positive input, state zero cannot recur. -/
theorem positive_step (c : Config) (hvalid : Valid 69 c)
    (hpos : ∃ q, c.state = some q ∧ 0 < q) :
    ∃ q, (step base c).state = some q ∧ 0 < q := by
  rcases c with ⟨left,right,state⟩
  obtain ⟨q,hq,hpos⟩ := hpos
  simp only at hq
  subst state
  have hqbound := hvalid q rfl
  have hne : (⟨q,hqbound⟩ : Fin 69).val ≠ 0 := Nat.ne_of_gt hpos
  have h := base_positive_successor ⟨q,hqbound⟩ hne (right.testBit 0)
  cases hr : (base q (right.testBit 0)).next with
  | none => exact False.elim (h.1 hr)
  | some r =>
    have hrpos : 0 < r := by
      by_contra hz
      have : r = 0 := by omega
      subst r
      exact h.2 hr
    refine ⟨r,?_,hrpos⟩
    simp only [Nat.testBit_zero] at hr
    simp [step,hr]
    split <;> simp [hr]

theorem positive_run (c : Config) (hvalid : Valid 69 c)
    (hpos : ∃ q, c.state = some q ∧ 0 < q) (fuel : Nat) :
    ∃ q, (run base c fuel).state = some q ∧ 0 < q := by
  induction fuel with
  | zero => exact hpos
  | succ fuel ih =>
    exact positive_step _ (valid_run 69 base c base_closed hvalid fuel) ih

theorem initial_step (input certificate : Nat) :
    step base ⟨certificate,input,some 0⟩ = ⟨input,certificate,some 1⟩ := by
  exact Source284InputSentinel.turn_to_certificate _ input certificate

theorem after_start_positive (input certificate fuel : Nat) :
    ∃ q, (run base ⟨certificate,input,some 0⟩ (fuel+1)).state = some q ∧ 0 < q := by
  rw [Source284HardwireTable.run_front,initial_step]
  apply positive_run
  · intro q hq
    simp only [Option.some.injEq] at hq
    subst q
    omega
  · exact ⟨1,rfl,by decide⟩

theorem final_step (c : Config) (q : Nat) (hvalid : Valid 69 c)
    (hstate : c.state = some q) (hl : 64 ≤ q) (hu : q < 68) :
    (step base c).state = some 68 := by
  cases c with
  | mk left right state =>
    simp only at hstate
    subst state
    have hq := hvalid q rfl
    have hr := base_final_rows ⟨q,hq⟩ hl hu (right.testBit 0)
    simp only [Nat.testBit_zero] at hr
    simp [step,hr]
    split <;> simp [hr]

/-- A run that is at a final restoration state at `limit` has not visited
that state range, or the sink, at any strictly earlier time. -/
theorem avoid_before_final (c : Config) (hvalid : Valid 69 c) (limit : Nat)
    (q : Nat) (hfinal : (run base c limit).state = some q)
    (hl : 64 ≤ q) (hu : q < 68) :
    ∀ t < limit, (run base c t).state ≠ some 68 ∧
      ∀ r, (run base c t).state = some r → ¬ (64 ≤ r ∧ r < 68) := by
  intro t ht
  constructor
  · intro hs
    have h := sink_run (run base c t) hs (limit-t)
    rw [← Source284PayloadPop.run_add] at h
    have he : t+(limit-t) = limit := by omega
    rw [he,hfinal] at h
    have : q = 68 := Option.some.inj h
    omega
  · intro r hr hrange
    have hs : (run base c (t+1)).state = some 68 := by
      simp only [run]
      exact final_step _ r (valid_run 69 base c base_closed hvalid t) hr hrange.1 hrange.2
    have h := sink_run (run base c (t+1)) hs (limit-(t+1))
    rw [← Source284PayloadPop.run_add] at h
    have he : t+1+(limit-(t+1)) = limit := by omega
    rw [he,hfinal] at h
    have : q = 68 := Option.some.inj h
    omega

/-- Two tables agree through a finite prefix when their rows agree at every
configuration actually visited by the base. -/
theorem run_agree (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat)
    (hrows : ∀ t < fuel, ∀ q, (run base c t).state = some q →
      table continuation q ((run base c t).right.testBit 0) =
        base q ((run base c t).right.testBit 0)) :
    run (table continuation) c fuel = run base c fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    have hp : ∀ t < fuel, ∀ q, (run base c t).state = some q →
        table continuation q ((run base c t).right.testBit 0) =
          base q ((run base c t).right.testBit 0) := by
      intro t ht q hq
      exact hrows t (by omega) q hq
    simp only [run,ih hp]
    cases hc : run base c fuel with
    | mk left right state =>
      cases state with
      | none => rfl
      | some q =>
        have hs := hrows fuel (by omega) q (by simp [hc])
        simp only [hc] at hs
        simp only [Nat.testBit_zero] at hs
        simp [step,hs]

/-- The redirected final restoration transition returns to state zero with
the full certificate and the popped input at the head. -/
theorem redirected_final (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4)
    (higher input : Nat) :
    step (table continuation) ⟨2*higher+mode/2,2*input,some (64+mode)⟩ =
      ⟨4*higher+mode,input,some 0⟩ := by
  interval_cases mode <;>
    simp [step,table,base,Source284InputSentinel.table,Source284ModePrefixScan.table,
      Source284PayloadPop.table,Source284ModePrefixReturn.table,shiftRow,bit,Nat.testBit_zero]
  all_goals repeat' constructor
  all_goals omega

/-- One complete positive-frame pass of the fixed loop. Its final source
transition returns to state zero, with the last bit moved into scratch. -/
theorem iteration (continuation : Nat → Bool → Row) (xs : List Bool) (b : Bool)
    (certificate suffix : Nat) :
    run (table continuation) ⟨certificate,encodeFrame (xs++[b]) suffix,some 0⟩
      (4*(xs++[b]).length+12) =
      ⟨certificate,encodeFrame xs (4*suffix+bit b),some 0⟩ := by
  let input := encodeFrame (xs++[b]) suffix
  let c : Config := ⟨certificate,input,some 0⟩
  let limit := 4*(xs++[b]).length+11
  let mode := certificate%4
  have hm : mode < 4 := Nat.mod_lt certificate (by decide)
  have hv : Valid 69 c := by
    intro q hq
    simp [c] at hq
    subst q
    decide
  have hpre := Source284PayloadPopPrecise.full_pre sink xs b certificate suffix
  change run base c limit =
      ⟨2*(certificate/4)+mode/2,2*encodeFrame xs (4*suffix+bit b),some (64+mode)⟩ at hpre
  have hf : (run base c limit).state = some (64+mode) := by rw [hpre]
  have ha := avoid_before_final c hv limit (64+mode) hf (by omega) (by omega)
  have hlen : Source284Parser.length input = (xs++[b]).length := by
    simp [input,Source284Parser.length,Source284Parser.parse_encodeFrame]
  have hi : 0 < Source284Parser.length input := by rw [hlen]; simp
  have heven : input%2 ≠ 0 := by
    intro h
    have hh := (Source284EmptyPrefix.empty_iff_even input).2 h
    omega
  have hodd : input%2 = 1 := by omega
  have hbit : input.testBit 0 = true := by simpa [Nat.testBit_zero] using hodd
  have hrows : ∀ t < limit, ∀ q, (run base c t).state = some q →
      table continuation q ((run base c t).right.testBit 0) =
        base q ((run base c t).right.testBit 0) := by
    intro t ht q hq
    have hqbound := (valid_run 69 base c base_closed hv t) q hq
    have hnfinal : ¬ (64 ≤ q ∧ q < 68) := (ha t ht).2 q hq
    have hnexit : q ≠ 68 := by
      intro h
      subst q
      exact (ha t ht).1 hq
    apply row_agree continuation q _ hqbound hnfinal hnexit
    intro hq0
    subst q
    cases t with
    | zero => simpa [c,run] using hbit
    | succ t =>
      obtain ⟨r,hr,hpos⟩ := after_start_positive input certificate t
      change (run base c (t+1)).state = some r at hr
      rw [hq] at hr
      have : r = 0 := (Option.some.inj hr).symm
      omega
  have heq := run_agree continuation c limit hrows
  have ht : 4*(xs++[b]).length+12 = limit+1 := by dsimp [limit]
  change run (table continuation) c _ = _
  rw [ht,run,heq,hpre,redirected_final _ _ hm]
  exact congrArg (fun x => Config.mk x (encodeFrame xs (4*suffix+bit b)) (some 0))
    (Source284InputSentinel.certificate_recovered certificate)

/-- On an empty frame, two turns preserve both tape halves and enter the
finite continuation. -/
theorem empty_exit (continuation : Nat → Bool → Row) (input certificate : Nat)
    (hzero : input%2 = 0) :
    run (table continuation) ⟨certificate,input,some 0⟩ 2 =
      ⟨certificate,input,some 69⟩ := by
  simp [run,step,table,bit,Nat.testBit_zero,hzero]
  split_ifs <;> congr 1 <;> omega

/-- Low-first scratch representation. Each payload bit is followed by a
zero marker; all higher original suffix bits remain in the tail. -/
def scratch : List Bool → Nat → Nat
  | [], suffix => suffix
  | b::bs, suffix => bit b+4*scratch bs suffix

def scratchBits : List Bool → List Bool
  | [] => []
  | b::bs => b::false::scratchBits bs

theorem scratchBits_length (w : List Bool) : (scratchBits w).length = 2*w.length := by
  induction w with
  | nil => rfl
  | cons b bs ih => simp [scratchBits,ih]; omega

/-- The produced suffix is the explicit low-first payload/zero stream
followed by the complete original higher suffix. -/
theorem scratch_stack (w : List Bool) (suffix : Nat) :
    scratch w suffix = Source284LoaderAlgebra.stack (scratchBits w) suffix := by
  induction w with
  | nil => rfl
  | cons b bs ih =>
    cases b <;> simp [scratch,scratchBits,Source284LoaderAlgebra.stack,bit,ih] <;> omega

/-- Finite arithmetic extraction confirms the complete high suffix remains
present after the output stream. This is not a separate machine operation. -/
theorem scratch_transfer (w : List Bool) (suffix left : Nat) :
    Source284LoaderAlgebra.transfer (2*w.length) left (scratch w suffix) =
      (Source284Parser.payloadFold left (scratchBits w),suffix) := by
  rw [scratch_stack,← scratchBits_length]
  exact Source284LoaderAlgebra.transfer_stack (scratchBits w) left suffix

theorem scratch_snoc (xs : List Bool) (b : Bool) (suffix : Nat) :
    scratch (xs++[b]) suffix = scratch xs (4*suffix+bit b) := by
  induction xs with
  | nil => simp [scratch]; omega
  | cons a xs ih => simp [scratch,ih]

/-- Without an explicit terminator, the scratch tape alone cannot determine
the payload length when the original ignored suffix is arbitrary. -/
theorem scratch_collision (suffix : Nat) :
    scratch [false] suffix = scratch [] (4*suffix) := by
  simp [scratch,bit]

def cost (n : Nat) : Nat := 2*n*n+14*n+2

theorem cost_succ (n : Nat) : cost (n+1) = (4*(n+1)+12)+cost n := by
  simp [cost]
  ring

/-- A single finite table repeatedly moves the last payload bit to scratch,
then exits on the empty frame. Every pass and the final two transitions are
charged. -/
theorem loop_frame (continuation : Nat → Bool → Row) (w : List Bool)
    (certificate suffix : Nat) :
    run (table continuation) ⟨certificate,encodeFrame w suffix,some 0⟩ (cost w.length) =
      ⟨certificate,encodeFrame [] (scratch w suffix),some 69⟩ := by
  induction w using List.reverseRecOn generalizing suffix with
  | nil =>
    simpa [cost,scratch,encodeFrame] using
      empty_exit continuation (2*suffix) certificate (by omega)
  | append_singleton xs b ih =>
    have ht : cost (xs++[b]).length =
        (4*(xs++[b]).length+12)+cost xs.length := by
      simpa using cost_succ xs.length
    rw [ht,Source284PayloadPop.run_add,iteration,ih,scratch_snoc]

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (69+states) (table continuation) := by
  intro q hq b q' hnext
  by_cases hz : q = 0 ∧ b = false
  · simp [table,hz] at hnext
    omega
  · by_cases hf : 64 ≤ q ∧ q < 68
    · simp [table,hz,hf] at hnext
      omega
    · by_cases hs : q = 68
      · simp [table,hz,hf,hs] at hnext
        omega
      · by_cases hc : 69 ≤ q
        · have ht : (shiftRow 69 (continuation (q-69) b)).next = some q' := by
            simpa [table,hz,hf,hs,hc] using hnext
          have hq0 : q-69 < states := by omega
          cases he : (continuation (q-69) b).next with
          | none => simp [shiftRow,he] at ht
          | some r =>
            have h := hv (q-69) hq0 b r he
            simp [shiftRow,he] at ht
            subst q'
            omega
        · have hq0 : q < 69 := by omega
          have ht : (base q b).next = some q' := by simpa [table,hz,hf,hs,hc] using hnext
          have h := base_closed q hq0 b q' ht
          omega

/-- The actual encoded source program implements the complete loop, with a
quadratic bound in parsed input length and arbitrary original tape tails. -/
theorem source_loop_frame (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (encode (69+states) (table continuation) 1)
      (Source284Relative.initial (encodeFrame w suffix) certificate) (cost w.length) =
      ⟨certificate,encodeFrame [] (scratch w suffix),active 69⟩ := by
  have hvalid : Valid (69+states) ⟨certificate,encodeFrame w suffix,some 0⟩ := by
    intro q hq
    simp only [Option.some.injEq] at hq
    subst q
    omega
  have hr := run_toSource (69+states) (table continuation) 1
    ⟨certificate,encodeFrame w suffix,some 0⟩ (closed states continuation hn hv) hvalid (cost w.length)
  change Source284Relative.run (encode (69+states) (table continuation) 1)
    (Source284Relative.initial (encodeFrame w suffix) certificate) _ = _ at hr
  rw [hr,loop_frame]
  rfl

/-- Every numeric input reaches the continuation, including virtual-zero
terminators. The decomposition is mathematical evidence, not runtime input. -/
theorem source_total_progress (states : Nat) (continuation : Nat → Bool → Row)
    (input certificate : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    ∃ (w : List Bool) (suffix : Nat),
      encodeFrame w suffix = input ∧ w.length = Source284Parser.length input ∧
      Source284Relative.run (encode (69+states) (table continuation) 1)
        (Source284Relative.initial input certificate) (cost (Source284Parser.length input)) =
      ⟨certificate,encodeFrame [] (scratch w suffix),active 69⟩ := by
  obtain ⟨w,suffix,hw⟩ := Source284Parser.encodeFrame_surjective input
  have hlen : Source284Parser.length input = w.length := by
    rw [← hw]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  refine ⟨w,suffix,hw,hlen.symm,?_⟩
  rw [hlen,← hw]
  exact source_loop_frame states continuation w certificate suffix hn hv

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (69+q) b = shiftRow 69 (continuation q b) := by
  have hz : ¬ (69+q = 0 ∧ b = false) := by omega
  have hf : ¬ (64 ≤ 69+q ∧ 69+q < 68) := by omega
  have hs : 69+q ≠ 68 := by omega
  simp [table,hz,hf,hs]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 69 c) = shiftConfig 69 (step continuation c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (clock : Nat) :
    run (table continuation) (shiftConfig 69 c) clock = shiftConfig 69 (run continuation c clock) := by
  induction clock with
  | zero => rfl
  | succ clock ih => simp only [run,ih,relocated_step]

/-- The linked verifier receives the scratch result in the same execution;
the quadratic setup and verifier clock are both charged. -/
theorem source_after_loop (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix clock : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.accepts (encode (69+states) (table continuation) 1)
      (encodeFrame w suffix) certificate (cost w.length+clock) =
    Source284Relative.accepts (encode states continuation 1)
      (encodeFrame [] (scratch w suffix)) certificate clock := by
  let c : Config := ⟨certificate,encodeFrame [] (scratch w suffix),some 0⟩
  have h0 : Valid states c := by
    intro q hq
    simp [c] at hq
    subst q
    exact hn
  have h1 : Valid (69+states) (shiftConfig 69 c) := by
    intro q hq
    simp [shiftConfig,c] at hq
    subst q
    omega
  have hr1 := run_toSource (69+states) (table continuation) 1
    (shiftConfig 69 c) (closed states continuation hn hv) h1 clock
  have hr0 := run_toSource states continuation 1 c hv h0 clock
  change Source284Relative.run (encode (69+states) (table continuation) 1)
    ⟨certificate,encodeFrame [] (scratch w suffix),active 69⟩ clock = _ at hr1
  change Source284Relative.run (encode states continuation 1)
    (Source284Relative.initial (encodeFrame [] (scratch w suffix)) certificate) clock = _ at hr0
  unfold Source284Relative.accepts
  rw [Source284Relative.run_add_clock,source_loop_frame states continuation w certificate suffix hn hv,
    hr1,hr0,relocated_run]
  cases h : (run continuation c clock).state <;>
    simp [toSource,shiftConfig,nextState,h,active]

example : scratch [true,false,true] 5 = 337 := rfl
example : cost 0 = 2 := rfl
example : cost 3 = 62 := rfl

end Shared.Beeping.NPcoNP.Source284PayloadLoop
