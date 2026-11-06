import Shared.Codes.FiniteProgramMarkedWitness
import Shared.Codes.FiniteProgramWitnessFirst
import Shared.Codes.FiniteProgramFirstEntryMany
set_option maxHeartbeats 3000000
set_option linter.constructorNameAsVariable false

/-! Patch both outcomes of the marked witness-block probe into one finite
continuation. The aligned entry and the first-component nonemptiness remain
explicit assumptions. -/
namespace Shared.Codes.FiniteProgramMarkedContinuation
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramLink (link shiftPair shiftConfig shiftStatus run_shift)
open Shared.Codes.FiniteProgramExtendAdvance (branch bridge)
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel StatusRel run_related)
open Shared.Codes.FiniteProgramTaggedLoop (canonical output cost totalCost)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.ComplexityBridge.PairReverseFirst (expanded)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

abbrev base := Shared.Codes.FiniteProgramMarkedWitness.program
abbrev payload := Shared.Codes.FiniteProgramWitnessFirst.program
abbrev boundary := Shared.Codes.FiniteProgramWitnessFirst.boundary
abbrev moffset := Shared.Codes.FiniteProgramMarkedWitness.offset
abbrev stride := Shared.Codes.FiniteProgramWitnessPhases.stride
abbrev markedPhase := Shared.Codes.FiniteProgramMarkedWitness.markedPhase

def more (mz mo z o : List Bool) : Nat := moffset mz mo + 2*stride z o + 3
def done (mz mo z o : List Bool) : Nat := moffset mz mo + 2*stride z o + 4

def pre (mz mo z o : List Bool) : Program :=
  let p := base mz mo z o
  let k := p.length+2
  (p.set (more mz mo z o) (branch p.length)).set (done mz mo z o) (branch (p.length+1)) ++
    [bridge k,bridge (k+boundary z o)]

def program (mz mo z o : List Bool) : Program := link (pre mz mo z o) (payload z o) []

theorem base_length (mz mo z o : List Bool) :
    (base mz mo z o).length = moffset mz mo + 2*stride z o + 5 := by
  change (Shared.Codes.FiniteProgramMarkedWitness.program mz mo z o).length = _
  have hm : moffset mz mo = 40+3*mz.length+3*mo.length :=
    Shared.Codes.FiniteProgramPhaseProbe.stride_length mz mo
  have hu : stride z o = 40+3*z.length+3*o.length :=
    Shared.Codes.FiniteProgramPhaseProbe.stride_length z o
  rw [Shared.Codes.FiniteProgramMarkedWitness.program_length,hm,hu]
  omega

theorem more_bound (mz mo z o : List Bool) : more mz mo z o < (base mz mo z o).length := by
  simp [more,base_length]
theorem done_bound (mz mo z o : List Bool) : done mz mo z o < (base mz mo z o).length := by
  simp [done,base_length]
theorem distinct (mz mo z o : List Bool) : more mz mo z o ≠ done mz mo z o := by simp [more,done]

theorem payload_boundary_bound (z o : List Bool) : boundary z o < (payload z o).length := by
  have hb := Shared.Codes.FiniteProgramWitnessFirst.boundary_bound z o
  have hs := Shared.Codes.FiniteProgramWitnessController.program_length z o
  have hdlen := Shared.Codes.FiniteProgramWitnessFirst.program_length z o
  change (payload z o).length = _ at hdlen
  change boundary z o < (Shared.Codes.FiniteProgramWitnessController.program z o).length at hb
  omega

theorem pre_length (mz mo z o : List Bool) : (pre mz mo z o).length = (base mz mo z o).length+2 := by
  simp [pre]

theorem program_length (mz mo z o : List Bool) :
    (program mz mo z o).length = 539+3*mz.length+3*mo.length+36*z.length+36*o.length := by
  simp [program,link,pre_length,Shared.Codes.FiniteProgramMarkedWitness.program_length,
    Shared.Codes.FiniteProgramWitnessFirst.program_length]
  omega

/-- Both probe outcomes are terminal in the unpatched table. -/
theorem base_stop (mz mo z o : List Bool) (j : Nat) (hj : j = 3 ∨ j = 4) (t : Tape) :
    step (base mz mo z o) (moffset mz mo+2*stride z o+j,t) = some (.inl false) := by
  let probe := Shared.Codes.FiniteProgramWitnessPhases.probe
  let rest := Shared.Codes.FiniteProgramWitnessPhases.phases z o 2
  have hc : ((j,t) : Config).1 < probe.length := by
    rcases hj with rfl | rfl <;> simp [probe,Shared.Codes.FiniteProgramWitnessPhases.probe]
  have hp := Shared.Codes.FiniteProgramWitnessPhases.probe_segment z o 2 (j,t) hc 1
  have hprobe : run probe (j,t) 1 = some (.inl false) := by
    rcases hj with rfl | rfl <;> cases ht : t.2.1 <;>
      simp [run,advance,step,probe,Shared.Codes.FiniteProgramWitnessPhases.probe,
        Shared.Codes.FiniteProgramWitnessPhases.dummy,ht]
  rw [hprobe] at hp
  have hr : run rest (2*stride z o+j,t) 1 = some (.inl false) := by
    simpa [rest,shiftConfig,shiftStatus] using hp
  have hin : ((2*stride z o+j,t) : Config).1 < rest.length := by
    simp only [rest,Shared.Codes.FiniteProgramWitnessPhases.phases_length]
    rcases hj with rfl | rfl <;> simp [Shared.Codes.FiniteProgramWitnessPhases.probe]
  have hs := Shared.Codes.FiniteProgramSplice.second_run (markedPhase mz mo) rest
    (Shared.Codes.FiniteProgramWitnessPhases.phases_valid z o 2) (2*stride z o+j,t) hin 1
  rw [hr] at hs
  simpa [base,Shared.Codes.FiniteProgramMarkedWitness.program,Shared.Codes.FiniteProgramMarkedWitness.offset,shiftConfig,shiftStatus,run,advance,
    Nat.add_assoc] using hs

theorem base_other (mz mo z o : List Bool) (d : Config)
    (hd : d.1 < (base mz mo z o).length)
    (hm : d.1 ≠ more mz mo z o) (he : d.1 ≠ done mz mo z o) :
    step (base mz mo z o) d = step (program mz mo z o) d := by
  have hl : (program mz mo z o)[d.1]? = (base mz mo z o)[d.1]? := by
    simp [program,link,pre,List.getElem?_append_left,hd,Ne.symm hm,Ne.symm he]
  simp [step,hl]

theorem more_row (mz mo z o : List Bool) :
    (program mz mo z o)[more mz mo z o]? = some (branch (base mz mo z o).length) := by
  have hb := more_bound mz mo z o
  have hd := distinct mz mo z o
  simp [program,link,pre,List.getElem?_append_left,hb,Ne.symm hd]

theorem done_row (mz mo z o : List Bool) :
    (program mz mo z o)[done mz mo z o]? = some (branch ((base mz mo z o).length+1)) := by
  have hb := done_bound mz mo z o
  simp [program,link,pre,List.getElem?_append_left,hb]

theorem bridge_more_row (mz mo z o : List Bool) :
    (program mz mo z o)[(base mz mo z o).length]? = some (bridge ((base mz mo z o).length+2)) := by
  simp [program,link,pre]

theorem bridge_done_row (mz mo z o : List Bool) :
    (program mz mo z o)[(base mz mo z o).length+1]? =
      some (bridge ((base mz mo z o).length+2+boundary z o)) := by
  simp [program,link,pre]

theorem handoff_more (mz mo z o : List Bool) (b : Bool) (L R : List Bool) :
    run (program mz mo z o) (more mz mo z o,tapeAt L (b::false::R)) 2 =
      some (.inr ((pre mz mo z o).length,tapeAt L (b::false::R))) := by
  have h := more_row mz mo z o
  have hb := bridge_more_row mz mo z o
  cases b <;> simp [run,advance,step,h,hb,branch,bridge,tapeAt,moveTape,pre_length]

theorem handoff_done (mz mo z o : List Bool) (b : Bool) (L R : List Bool) :
    run (program mz mo z o) (done mz mo z o,tapeAt L (b::false::R)) 2 =
      some (.inr ((pre mz mo z o).length+boundary z o,tapeAt L (b::false::R))) := by
  have h := done_row mz mo z o
  have hb := bridge_done_row mz mo z o
  cases b <;> simp [run,advance,step,h,hb,branch,bridge,tapeAt,moveTape,pre_length]

private theorem payload_link (z o : List Bool) :
    link (Shared.Codes.FiniteProgramWitnessFirst.handoffPre z o)
      (Shared.Codes.FiniteProgramSeparatorFirst.program z o) [] = payload z o := rfl

private theorem program_link (mz mo z o : List Bool) :
    link (pre mz mo z o) (payload z o) [] = program mz mo z o := rfl

attribute [local irreducible] Shared.Codes.FiniteProgramMarkedWitness.program
attribute [local irreducible] Shared.Codes.FiniteProgramWitnessFirst.program

/-- Every row of the two-exit linked table has a finite in-range target. -/
theorem program_valid (mz mo z o : List Bool) : valid (program mz mo z o) = true := by
  let p := base mz mo z o
  let d := payload z o
  let k := p.length+2
  let m := k+d.length
  have hl : (program mz mo z o).length = m := by simp [program,link,pre_length,m,k,p,d]
  have hp : ∀ r ∈ p, validRow p.length r.1 = true ∧ validRow p.length r.2 = true := by
    intro r hr
    have hv := Shared.Codes.FiniteProgramMarkedWitness.program_valid mz mo z o
    change valid p = true at hv
    simp only [valid,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at hv
    simpa only [Bool.and_eq_true] using hv.2 r hr
  have hd : ∀ r ∈ d, validRow d.length r.1 = true ∧ validRow d.length r.2 = true := by
    intro r hr
    have hv := Shared.Codes.FiniteProgramWitnessFirst.program_valid z o
    change valid d = true at hv
    simp only [valid,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at hv
    simpa only [Bool.and_eq_true] using hv.2 r hr
  have hbd : boundary z o < d.length := payload_boundary_bound z o
  have hp_m : p.length ≤ m := by dsimp [m,k]; omega
  have hb0 : validRow m (branch p.length).1 = true ∧ validRow m (branch p.length).2 = true := by
    have hlt : p.length < m := by dsimp [m,k]; omega
    simp [branch,validRow,hlt]
  have hb1 : validRow m (branch (p.length+1)).1 = true ∧ validRow m (branch (p.length+1)).2 = true := by
    have hlt : p.length+1 < m := by dsimp [m,k]; omega
    simp [branch,validRow,hlt]
  have ht0 : validRow m (bridge k).1 = true ∧ validRow m (bridge k).2 = true := by
    have hlt : k < m := by dsimp [m]; omega
    simp [bridge,validRow,hlt]
  have ht1 : validRow m (bridge (k+boundary z o)).1 = true ∧ validRow m (bridge (k+boundary z o)).2 = true := by
    have hlt : k+boundary z o < m := by dsimp [m]; omega
    simp [bridge,validRow,hlt]
  have hset : ∀ r ∈ (p.set (more mz mo z o) (branch p.length)).set
        (done mz mo z o) (branch (p.length+1)),
      validRow m r.1 = true ∧ validRow m r.2 = true := by
    intro r hr
    rcases List.mem_or_eq_of_mem_set hr with hr | he
    · rcases List.mem_or_eq_of_mem_set hr with hr | he
      · obtain ⟨h₁,h₂⟩ := hp r hr
        exact ⟨Shared.Codes.FiniteProgramShuttleSelect.validRow_mono _ _ _ hp_m h₁,
          Shared.Codes.FiniteProgramShuttleSelect.validRow_mono _ _ _ hp_m h₂⟩
      · subst r; exact hb0
    · subst r; exact hb1
  have hall : (program mz mo z o).all
      (fun r => validRow (program mz mo z o).length r.1 && validRow (program mz mo z o).length r.2) = true := by
    rw [List.all_eq_true]
    intro r hr
    have hr' : r ∈ (p.set (more mz mo z o) (branch p.length)).set
          (done mz mo z o) (branch (p.length+1)) ∨ r = bridge k ∨ r = bridge (k+boundary z o) ∨
        r ∈ d.map (shiftPair k) := by
      simpa [program,link,pre,pre_length,p,d,k,List.mem_append] using hr
    rw [hl]
    rcases hr' with hset' | ht0' | ht1' | hmap
    · simpa only [Bool.and_eq_true] using hset r hset'
    · subst r; simpa only [Bool.and_eq_true] using ht0
    · subst r; simpa only [Bool.and_eq_true] using ht1
    · obtain ⟨r',hr',rfl⟩ := List.mem_map.mp hmap
      obtain ⟨h₁,h₂⟩ := hd r' hr'
      simp only [Bool.and_eq_true]
      exact ⟨Shared.Codes.FiniteProgramTaggedExtend.shifted_valid r'.1 k d.length h₁,
        Shared.Codes.FiniteProgramTaggedExtend.shifted_valid r'.2 k d.length h₂⟩
  have hn : (program mz mo z o).isEmpty = false := by
    cases h : program mz mo z o with
    | nil => simp [h] at hl; dsimp [m,k] at hl; omega
    | cons r rs => rfl
  change (!(program mz mo z o).isEmpty && (program mz mo z o).all
    (fun r => validRow (program mz mo z o).length r.1 && validRow (program mz mo z o).length r.2)) = true
  rw [hn,hall]
  rfl

attribute [local irreducible] Shared.Codes.FinitePrograms.run

/-- Both patched rows preserve a source run through its first live entry to
one of them. No implicit jump is taken in this lemma. -/
theorem marked_prefix (mz mo z o : List Bool) (c last : Config) (n : Nat)
    (hc : c.1 < (base mz mo z o).length)
    (h : run (base mz mo z o) c n = some (.inr last)) :
    run (program mz mo z o) c n = some (.inr last) := by
  let stops : Set Nat := {more mz mo z o,done mz mo z o}
  apply Shared.Codes.FiniteProgramFirstEntry.first_entry_many
    (base mz mo z o) (program mz mo z o) c last n stops
    (Shared.Codes.FiniteProgramMarkedWitness.program_valid mz mo z o) hc ?_ ?_ h
  · intro q hq
    simp only [stops,Set.mem_insert_iff,Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl
    · exact ⟨false,fun t => base_stop mz mo z o 3 (Or.inl rfl) t⟩
    · exact ⟨false,fun t => base_stop mz mo z o 4 (Or.inr rfl) t⟩
  · intro d hd hnot
    have hm : d.1 ≠ more mz mo z o := by
      intro he; apply hnot; simp [stops,he]
    have he : d.1 ≠ done mz mo z o := by
      intro he; apply hnot; simp [stops,he]
    exact base_other mz mo z o d hd hm he

private theorem status_live (s : Status) (q : Nat) (t : Tape)
    (h : StatusRel s (some (.inr (q,t)))) :
    ∃ c, s = some (.inr c) ∧ c.1 = q ∧ TapeRel c.2 t := by
  cases s with
  | none => exact False.elim h
  | some v => cases v with
    | inl b => exact False.elim h
    | inr c => exact ⟨c,rfl,h.1,h.2⟩

attribute [local irreducible] program pre

/-- Entering the linked payload at its separator state handles the singleton
witness case: restore the marker and scan the nonempty first component. -/
theorem payload_from_marker (z o x xs L : List Bool) (hx : x ≠ []) (c : Config)
    (hq : c.1 = boundary z o)
    (ht : TapeRel c.2 (Shared.Codes.FiniteProgramWitnessPhases.witnessTape [] xs
      ((expanded x).reverse ++ false::false::L))) :
    ∃ d, run (payload z o) c
        (2+(cost z o false xs + Shared.Codes.FiniteProgramSeparatorFirst.firstCost z o x.reverse
          (output z o false xs))) = some (.inr d) ∧
      d.1 = (Shared.Codes.FiniteProgramWitnessFirst.handoffPre z o).length +
        Shared.Codes.FiniteProgramSeparatorFirst.offset z o +
        Shared.Codes.FiniteProgramFirstBlocksController.boundary z o ∧
      TapeRel d.2 (Shared.Codes.FiniteProgramSeparatorFirst.firstTape []
        (Shared.Codes.FiniteProgramSeparatorFirst.firstOutput z o x.reverse (output z o false xs)) L) := by
  let left := (expanded x).reverse ++ false::false::L
  let marked := tapeAt left (true::false::Shared.Codes.FiniteProgramBitShuttle.tagged xs ++ [false,false,false])
  let restored := (canonical left false xs).2
  let k := (Shared.Codes.FiniteProgramWitnessFirst.handoffPre z o).length
  let pc := cost z o false xs + Shared.Codes.FiniteProgramSeparatorFirst.firstCost z o x.reverse (output z o false xs)
  have hmarked : Shared.Codes.FiniteProgramWitnessPhases.witnessTape [] xs left = marked := rfl
  rw [hmarked] at ht
  have hrestore := Shared.Codes.FiniteProgramWitnessFirst.restore_handoff z o left
    (Shared.Codes.FiniteProgramBitShuttle.tagged xs ++ [false,false,false])
  change run (payload z o) (boundary z o,marked) 2 = some (.inr (k,restored)) at hrestore
  have hrel := run_related (payload z o) c (boundary z o,marked) hq ht 2
  rw [hrestore] at hrel
  obtain ⟨start,hstart,hstate,htape⟩ := status_live _ _ _ hrel
  obtain ⟨last,hlast,hlastq,hlastt⟩ := Shared.Codes.FiniteProgramSeparatorFirst.run_separator_first
    z o x xs L hx (0,start.2) rfl htape
  have hin : ((0,start.2) : Config).1 < (Shared.Codes.FiniteProgramSeparatorFirst.program z o).length :=
    Shared.Codes.FiniteProgramLink.valid_nonempty _ (Shared.Codes.FiniteProgramSeparatorFirst.program_valid z o)
  have hs := run_shift (Shared.Codes.FiniteProgramWitnessFirst.handoffPre z o)
    (Shared.Codes.FiniteProgramSeparatorFirst.program z o) []
    (Shared.Codes.FiniteProgramSeparatorFirst.program_valid z o) (0,start.2) hin pc
  rw [hlast,payload_link] at hs
  have hcfg := Shared.Codes.FiniteProgramWitnessPhases.shift_from_state start k hstate
  refine ⟨shiftConfig k last,?_,?_,hlastt⟩
  · change run (payload z o) c (2+pc) = _
    rw [run_continue _ _ _ _ _ hstart,hcfg]
    simpa only [shiftStatus] using hs
  · simp only [shiftConfig,hlastq]
    omega

/-- The payload handles either an empty remaining witness at its separator
entry or a nonempty remaining witness at state zero. -/
theorem payload_remaining (z o earlier x xs L : List Bool) (hx : x ≠ []) (c : Config)
    (hq : c.1 = (if earlier.isEmpty then boundary z o else 0))
    (ht : TapeRel c.2 (Shared.Codes.FiniteProgramWitnessPhases.witnessTape earlier xs
      ((expanded x).reverse ++ false::false::L))) :
    let buf := Shared.Codes.FiniteProgramWitnessController.loopOutput z o earlier.reverse xs
    ∃ d, run (payload z o) c
        (Shared.Codes.FiniteProgramWitnessController.loopCost z o earlier.reverse xs + 2 +
          (cost z o false buf + Shared.Codes.FiniteProgramSeparatorFirst.firstCost z o x.reverse
            (output z o false buf))) = some (.inr d) ∧
      d.1 = (Shared.Codes.FiniteProgramWitnessFirst.handoffPre z o).length +
        Shared.Codes.FiniteProgramSeparatorFirst.offset z o +
        Shared.Codes.FiniteProgramFirstBlocksController.boundary z o ∧
      TapeRel d.2 (Shared.Codes.FiniteProgramSeparatorFirst.firstTape []
        (Shared.Codes.FiniteProgramSeparatorFirst.firstOutput z o x.reverse (output z o false buf)) L) := by
  dsimp only
  cases earlier with
  | nil =>
    have hq' : c.1 = boundary z o := by simpa using hq
    have h := payload_from_marker z o x xs L hx c hq' ht
    simpa [Shared.Codes.FiniteProgramWitnessController.loopOutput,
      Shared.Codes.FiniteProgramWitnessController.loopCost] using h
  | cons b bs =>
    have hq' : c.1 = 0 := by simpa using hq
    have hne : (b::bs).reverse ≠ [] := by simp
    have ht' : TapeRel c.2 (Shared.Codes.FiniteProgramWitnessPhases.witnessTape
        ((b::bs).reverse).reverse xs ((expanded x).reverse ++ false::false::L)) := by
      simpa using ht
    simpa using Shared.Codes.FiniteProgramWitnessFirst.run_witness_first
      z o (b::bs).reverse x xs L hne hx c hq' ht'

private theorem shifted_state (c : Config) (k q : Nat) (h : c.1 = k+q) :
    c = shiftConfig k (q,c.2) := by
  apply Prod.ext
  · simpa only [shiftConfig] using h
  · rfl

/-- The marked first block, the remaining witness if any, and a nonempty
first component run in a single table. Both probe outcomes use two charged
transitions, and all later costs are included. -/
theorem run_marked_witness_first (mz mo z o earlier x xs L : List Bool) (b : Bool)
    (hx : x ≠ []) (c : Config) (hq : c.1 = 0)
    (ht : TapeRel c.2 (Shared.Codes.FiniteProgramWitnessPhases.witnessTape (earlier++[b]) xs
      ((expanded x).reverse ++ false::false::L))) :
    let firstBuf := Shared.Codes.FiniteProgramMarkedWitness.markedBuffer mz mo z o earlier b xs
    let buf := Shared.Codes.FiniteProgramWitnessController.loopOutput z o earlier.reverse firstBuf
    let mc := cost mz mo false xs + (totalCost z o [true,earlier.isEmpty] b (output mz mo false xs)+2)
    ∃ d, run (program mz mo z o) c
        (mc+2+(Shared.Codes.FiniteProgramWitnessController.loopCost z o earlier.reverse firstBuf+2+
          (cost z o false buf + Shared.Codes.FiniteProgramSeparatorFirst.firstCost z o x.reverse
            (output z o false buf)))) = some (.inr d) ∧
      d.1 = (pre mz mo z o).length + (Shared.Codes.FiniteProgramWitnessFirst.handoffPre z o).length +
        Shared.Codes.FiniteProgramSeparatorFirst.offset z o +
        Shared.Codes.FiniteProgramFirstBlocksController.boundary z o ∧
      TapeRel d.2 (Shared.Codes.FiniteProgramSeparatorFirst.firstTape []
        (Shared.Codes.FiniteProgramSeparatorFirst.firstOutput z o x.reverse (output z o false buf)) L) := by
  dsimp only
  let left := (expanded x).reverse ++ false::false::L
  let firstBuf := Shared.Codes.FiniteProgramMarkedWitness.markedBuffer mz mo z o earlier b xs
  let buf := Shared.Codes.FiniteProgramWitnessController.loopOutput z o earlier.reverse firstBuf
  let mc := cost mz mo false xs + (totalCost z o [true,earlier.isEmpty] b (output mz mo false xs)+2)
  let pc := Shared.Codes.FiniteProgramWitnessController.loopCost z o earlier.reverse firstBuf+2+
    (cost z o false buf + Shared.Codes.FiniteProgramSeparatorFirst.firstCost z o x.reverse (output z o false buf))
  let q := if earlier.isEmpty then done mz mo z o else more mz mo z o
  let entry := if earlier.isEmpty then boundary z o else 0
  let t := Shared.Codes.FiniteProgramWitnessPhases.witnessTape earlier firstBuf left
  obtain ⟨mid,hm,hmid,htape⟩ := Shared.Codes.FiniteProgramMarkedWitness.run_marked_block
    mz mo z o earlier b xs left c hq ht
  change run (base mz mo z o) c mc = _ at hm
  change TapeRel mid.2 t at htape
  have hqmid : mid.1 = q := by
    cases he : earlier.isEmpty <;> simp [q,more,done,he] at hmid ⊢ <;> omega
  have hc : c.1 < (base mz mo z o).length := by
    rw [hq]
    exact Shared.Codes.FiniteProgramLink.valid_nonempty _
      (Shared.Codes.FiniteProgramMarkedWitness.program_valid mz mo z o)
  have hfirst := marked_prefix mz mo z o c mid mc hc hm
  let source := Shared.Codes.FiniteProgramWitnessPhases.witnessSource earlier left
  let right := Shared.Codes.FiniteProgramBitShuttle.tagged firstBuf ++ [false,false,false]
  have hhead : source.head?.getD false = earlier.isEmpty :=
    Shared.Codes.FiniteProgramWitnessPhases.witness_boundary_head earlier left
  have hshape : t = tapeAt source.tail (earlier.isEmpty::false::right) := by
    change (source.tail,source.head?.getD false,false::right) = _
    simp [tapeAt,hhead]
  have hh : run (program mz mo z o) (q,t) 2 =
      some (.inr ((pre mz mo z o).length+entry,t)) := by
    rw [hshape]
    cases he : earlier.isEmpty with
    | false =>
      simpa [q,entry,he] using handoff_more mz mo z o false source.tail right
    | true =>
      simpa [q,entry,he] using handoff_done mz mo z o true source.tail right
  have hr := run_related (program mz mo z o) mid (q,t) hqmid htape 2
  rw [hh] at hr
  obtain ⟨start,hstart,hstate,ht'⟩ := status_live _ _ _ hr
  obtain ⟨last,hlast,hlastq,hlastt⟩ := payload_remaining z o earlier x firstBuf L hx
    (entry,start.2) rfl ht'
  have hin : ((entry,start.2) : Config).1 < (payload z o).length := by
    cases he : earlier.isEmpty with
    | false =>
      simp only [entry,he,Bool.false_eq_true,reduceIte]
      exact Shared.Codes.FiniteProgramLink.valid_nonempty _
        (Shared.Codes.FiniteProgramWitnessFirst.program_valid z o)
    | true =>
      simpa [entry,he] using payload_boundary_bound z o
  have hshift := run_shift (pre mz mo z o) (payload z o) []
    (Shared.Codes.FiniteProgramWitnessFirst.program_valid z o) (entry,start.2) hin pc
  rw [hlast,program_link] at hshift
  have hcfg := shifted_state start (pre mz mo z o).length entry hstate
  refine ⟨shiftConfig (pre mz mo z o).length last,?_,?_,hlastt⟩
  · change run (program mz mo z o) c ((mc+2)+pc) = _
    rw [Nat.add_assoc,run_continue _ _ _ _ _ hfirst,run_continue _ _ _ _ _ hstart,hcfg]
    simpa only [shiftStatus] using hshift
  · simp only [shiftConfig,hlastq]
    omega

theorem marked_buffer_length (mz mo z o earlier : List Bool) (b : Bool) (xs : List Bool) :
    (Shared.Codes.FiniteProgramMarkedWitness.markedBuffer mz mo z o earlier b xs).length ≤
      xs.length+1+mz.length+2*(1+Shared.Codes.FiniteProgramTaggedLoop.maxWord z o) := by
  have h := Shared.Codes.FiniteProgramFirstBlocksController.result_length_le z o
    [true,earlier.isEmpty] b (output mz mo false xs)
  simp only [List.length_cons,List.length_nil,output,Bool.false_eq_true,reduceIte,
    List.length_append] at h
  unfold Shared.Codes.FiniteProgramMarkedWitness.markedBuffer
  simp only [output,Bool.false_eq_true,reduceIte]
  omega

/-- An explicit polynomial bound for the entire marked-block and continuation
run, including both two-step handoffs. -/
theorem total_cost_bound (mz mo z o earlier x xs : List Bool) (b : Bool) :
    let w := Shared.Codes.FiniteProgramTaggedLoop.maxWord z o
    let gw := 3*(1+w)
    let gx := 6*(1+w)
    let start := xs.length+1+mz.length+2*(1+w)
    let bulk := start+earlier.length*gw
    let firstBuf := Shared.Codes.FiniteProgramMarkedWitness.markedBuffer mz mo z o earlier b xs
    let buf := Shared.Codes.FiniteProgramWitnessController.loopOutput z o earlier.reverse firstBuf
    let mc := cost mz mo false xs + (totalCost z o [true,earlier.isEmpty] b (output mz mo false xs)+2)
    mc+2+(Shared.Codes.FiniteProgramWitnessController.loopCost z o earlier.reverse firstBuf+2+
      (cost z o false buf + Shared.Codes.FiniteProgramSeparatorFirst.firstCost z o x.reverse
        (output z o false buf))) ≤
      (16*xs.length+16*mz.length+31 +
        (2*(16*(xs.length+1+mz.length+2*(1+w))+16*w+31)+2)) + 2 +
      (earlier.length*(3*(16*(start+earlier.length*gw+gw)+16*w+31)+4)+2+
        (16*bulk+16*w+31 + x.length*(6*(16*(bulk+1+w+x.length*gx+gx)+16*w+31)+4))) := by
  dsimp only
  let w := Shared.Codes.FiniteProgramTaggedLoop.maxWord z o
  let gw := 3*(1+w)
  let gx := 6*(1+w)
  let start := xs.length+1+mz.length+2*(1+w)
  let bulk := start+earlier.length*gw
  let firstBuf := Shared.Codes.FiniteProgramMarkedWitness.markedBuffer mz mo z o earlier b xs
  let buf := Shared.Codes.FiniteProgramWitnessController.loopOutput z o earlier.reverse firstBuf
  have hbuf : firstBuf.length ≤ start := by
    simpa [firstBuf,start,w] using marked_buffer_length mz mo z o earlier b xs
  have hm := Shared.Codes.FiniteProgramMarkedWitness.marked_block_cost_bound mz mo z o earlier b xs
  have hp := Shared.Codes.FiniteProgramWitnessFirst.total_cost_bound z o earlier.reverse x firstBuf
  simp only [List.length_reverse] at hp
  have hp' : Shared.Codes.FiniteProgramWitnessController.loopCost z o earlier.reverse firstBuf+2+
      (cost z o false buf + Shared.Codes.FiniteProgramSeparatorFirst.firstCost z o x.reverse (output z o false buf)) ≤
      earlier.length*(3*(16*(start+earlier.length*gw+gw)+16*w+31)+4)+2+
        (16*bulk+16*w+31 + x.length*(6*(16*(bulk+1+w+x.length*gx+gx)+16*w+31)+4)) := by
    apply le_trans hp
    dsimp [buf,start,bulk,gw,gx,w] at *
    gcongr
  exact Nat.add_le_add (Nat.add_le_add hm (Nat.le_refl 2)) hp'

/-- The actual combined table leaves a framed buffer whose list-level
metadata removal is the canonical translated TM2 input. This does not yet
implement that removal on the tape. -/
theorem run_tm2_marked_witness_first (tm : Turing.FinTM2) {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet tm → List.Vector Bool width)
    (inp : tm.Γ tm.k₀ ≃ Bool) (earlier x L : List Bool) (b : Bool) (hx : x ≠ [])
    (c : Config) (hq : c.1 = 0)
    (ht : TapeRel c.2 (Shared.Codes.FiniteProgramWitnessPhases.witnessTape (earlier++[b]) []
      ((expanded x).reverse ++ false::false::L))) :
    let mz := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true false
    let mo := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true true
    let z := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false false
    let o := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false true
    let firstBuf := Shared.Codes.FiniteProgramMarkedWitness.markedBuffer mz mo z o earlier b []
    let buf := Shared.Codes.FiniteProgramWitnessController.loopOutput z o earlier.reverse firstBuf
    let finalBuf := Shared.Codes.FiniteProgramSeparatorFirst.firstOutput z o x.reverse (output z o false buf)
    let mc := cost mz mo false [] + (totalCost z o [true,earlier.isEmpty] b (output mz mo false [])+2)
    let rest := [b,true] ++ (BitstringEncoding.bitEncode earlier).reverse ++ [false] ++ (expanded x).reverse
    ∃ d, run (program mz mo z o) c
        (mc+2+(Shared.Codes.FiniteProgramWitnessController.loopCost z o earlier.reverse firstBuf+2+
          (cost z o false buf + Shared.Codes.FiniteProgramSeparatorFirst.firstCost z o x.reverse
            (output z o false buf)))) = some (.inr d) ∧
      d.1 = (pre mz mo z o).length + (Shared.Codes.FiniteProgramWitnessFirst.handoffPre z o).length +
        Shared.Codes.FiniteProgramSeparatorFirst.offset z o +
        Shared.Codes.FiniteProgramFirstBlocksController.boundary z o ∧
      TapeRel d.2 (Shared.Codes.FiniteProgramSeparatorFirst.firstTape [] finalBuf L) ∧
      Shared.ComplexityBridge.FirstBlocksContent.unframe width (rest.length+1) finalBuf =
        Shared.ComplexityBridge.TM2BinaryPostCosts.inputBits tm enc
          ((BitstringEncoding.bitEncode (x,earlier++[b])).map inp.symm) := by
  dsimp only
  obtain ⟨d,hr,hd,htape⟩ := run_marked_witness_first
    (Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true false)
    (Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true true)
    (Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false false)
    (Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false true)
    earlier x [] L b hx c hq ht
  refine ⟨d,hr,hd,htape,?_⟩
  exact Shared.Codes.FiniteProgramMarkedWitness.marked_buffer_unframes_tm2 tm enc inp x earlier b

namespace Fixtures
example : run (program [] [] [] []) (more [] [] [] [],([],false,[false])) 2 =
    some (.inr ((pre [] [] [] []).length,([],false,[false]))) := by
  simpa [tapeAt] using handoff_more [] [] [] [] false [] []
example : run (program [] [] [] []) (done [] [] [] [],([],true,[false])) 2 =
    some (.inr ((pre [] [] [] []).length+boundary [] [],([],true,[false]))) := by
  simpa [tapeAt] using handoff_done [] [] [] [] true [] []
example : valid (program [true] [false] [false] [true]) = true :=
  program_valid [true] [false] [false] [true]
example : (program [true] [false] [false] [true]).length = 617 := by
  simpa using program_length [true] [false] [false] [true]
end Fixtures

end Shared.Codes.FiniteProgramMarkedContinuation
