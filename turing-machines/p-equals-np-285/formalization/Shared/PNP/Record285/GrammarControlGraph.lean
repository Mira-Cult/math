import Shared.PNP.Record285.GrammarAdministrative

/-! Extract a finite, register-branching control-flow graph from the frozen
grammar. The graph is intended as the boundary at which the producer's
control-flow rewrite certificates can be checked. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.GrammarControlGraph
open Shared.Beeping
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.GrammarExact
open Shared.PNP.Record285.GrammarPure

/-- The only bank-dependent part of a grammar control transfer. -/
def test (e : Edge) (fields : List Nat) : Bool :=
  match e with
  | .dec i => decide ((fields.drop i).headD 0 = 0)
  | .half i => decide ((fields.drop i).headD 0 % 2 = 0)
  | _ => false

def transfer (e : Edge) (code : List Bool) (branch : Bool) : Option (List Bool) :=
  match e with
  | .dec _ | .half _ => if branch then returnPathSkipOne code else returnPath code
  | _ => controlStep e [] code

theorem transfer_correct (e : Edge) (fields : List Nat) (code : List Bool) :
    transfer e code (test e fields) = controlStep e fields code := by
  cases e with
  | dec i => simp [transfer,test,controlStep]
  | half i => simp [transfer,test,controlStep]
  | brk i =>
    have h := GrammarAdministrative.admin_ignores_bank (.brk i) fields code rfl
    exact h.1.symm
  | cont i =>
    have h := GrammarAdministrative.admin_ignores_bank (.cont i) fields code rfl
    exact h.1.symm
  | node i => rfl
  | inc i => rfl
  | beep => rfl

/-- A successor is a complete next leaf address. The two outgoing entries
represent the two test results, even if one cannot arise from an invariant. -/
def successor (e : Edge) (code : List Bool) (branch : Bool) : Option (List Bool) := do
  let control ← transfer e code branch
  let (_,len) ← descend 163 rootIndex (pureBits control) 0
  pure (window (pureBits control) 0 len)

structure Row where
  code : List Bool
  edge : Edge
  no : Option (List Bool)
  yes : Option (List Bool)
  deriving DecidableEq, Repr

def makeRow (code : List Bool) (e : Edge) : Row :=
  ⟨code,e,successor e code false,successor e code true⟩

/-- Enumerate unfolded leaf occurrences, not just shared grammar nodes. -/
def rows : Nat → Nat → List Bool → List Row
  | 0,_,_ => []
  | fuel+1,n,pre =>
    [false,true].flatMap fun b =>
      match nodeEdge n b with
      | none => []
      | some (.node j) => rows fuel j (pre++[b])
      | some e => [makeRow (pre++[b]) e]

def table : List Row := rows 43 rootIndex []

theorem table_size : table.length = 259 := by decide

/-- Neither branch of any extracted occurrence has a missing successor. -/
theorem all_successors_checked :
    table.all (fun row => row.no.isSome && row.yes.isSome) = true := by decide

/-- Tree-indexed lookup avoids a linear search through the unfolded table. -/
def lookup (code : List Bool) : Option Row :=
  (walk rootIndex code).map (makeRow code)

/-- Any grammar walk to a leaf is among the extracted occurrences. The
separate path checker rules out exhausted traversal fuel and missing nodes. -/
theorem walk_mem_rows (fuel n : Nat) (pre code : List Bool) (e : Edge)
    (hcheck : GrammarAdministrative.checkPaths fuel n pre = true)
    (hwalk : walk n code = some e) : makeRow (pre++code) e ∈ rows fuel n pre := by
  induction fuel generalizing n pre code with
  | zero => simp [GrammarAdministrative.checkPaths] at hcheck
  | succ fuel ih =>
    cases code with
    | nil => simp [walk] at hwalk
    | cons bit rest =>
      have hbranch : (match nodeEdge n bit with
          | none => false
          | some (.node j) => GrammarAdministrative.checkPaths fuel j (pre++[bit])
          | some edge => GrammarAdministrative.leafSafe (pre++[bit]) edge) = true := by
        have ha := List.all_eq_true.mp hcheck bit
        apply ha
        cases bit <;> simp
      simp only [rows, List.mem_flatMap]
      refine ⟨bit,by cases bit <;> simp,?_⟩
      cases hedge : nodeEdge n bit with
      | none => simp [hedge] at hbranch
      | some found =>
        cases found with
        | node j =>
          have hs : GrammarAdministrative.checkPaths fuel j (pre++[bit]) = true := by
            simpa only [hedge] using hbranch
          have hw : walk j rest = some e := by simpa only [walk,hedge] using hwalk
          simpa only [hedge,List.append_assoc,List.singleton_append] using ih j (pre++[bit]) rest hs hw
        | inc i =>
          cases rest <;> simp [walk,hedge] at hwalk
          subst e
          simp
        | dec i =>
          cases rest <;> simp [walk,hedge] at hwalk
          subst e
          simp
        | half i =>
          cases rest <;> simp [walk,hedge] at hwalk
          subst e
          simp
        | beep =>
          cases rest <;> simp [walk,hedge] at hwalk
          subst e
          simp
        | brk i =>
          cases rest <;> simp [walk,hedge] at hwalk
          subst e
          simp
        | cont i =>
          cases rest <;> simp [walk,hedge] at hwalk
          subst e
          simp

theorem lookup_of_walk (code : List Bool) (e : Edge) (hwalk : walk rootIndex code = some e) :
    lookup code = some (makeRow code e) := by
  simp [lookup,hwalk]

/-- All rows returned by tree lookup occur in the finite unfolded table. -/
theorem lookup_in_table (code : List Bool) (row : Row) (h : lookup code = some row) :
    row ∈ table := by
  cases hw : walk rootIndex code with
  | none => simp [lookup,hw] at h
  | some e =>
    have hr : row = makeRow code e := by simpa [lookup,hw] using h.symm
    subst row
    simpa only [table,List.nil_append,rootIndex] using
      walk_mem_rows 43 162 [] code e GrammarAdministrative.all_paths_checked hw

/-- A computed successor is itself a genuine leaf occurrence. -/
theorem successor_closed (e : Edge) (code : List Bool) (branch : Bool) (next : List Bool)
    (h : successor e code branch = some next) :
    ∃ row, lookup next = some row ∧ row ∈ table := by
  unfold successor at h
  cases hc : transfer e code branch with
  | none => simp [hc] at h
  | some control =>
    cases hd : descend 163 rootIndex (pureBits control) 0 with
    | none => simp [hc,hd] at h
    | some pair =>
      obtain ⟨edge,len⟩ := pair
      simp [hc,hd] at h
      subst next
      obtain ⟨len',_,_,hend,hwalk⟩ := descend_trace 163 rootIndex (pureBits control) 0 edge len hd
      have heq : len' = len := by omega
      subst len'
      let row := makeRow (window (pureBits control) 0 len) edge
      have hl := lookup_of_walk (window (pureBits control) 0 len) edge hwalk
      exact ⟨row,hl,lookup_in_table _ row hl⟩

structure State where
  pc : List Bool
  fields : List Nat
  deriving DecidableEq, Repr

def initial : State := ⟨[false],List.replicate 1909 0⟩

/-- A total graph executor. Its fallbacks are unreachable under `Related`. -/
def step (s : State) : State × Bool :=
  let row := (lookup s.pc).getD (makeRow [] .beep)
  let next := if test row.edge s.fields then row.yes else row.no
  (⟨next.getD [],applyUpdate row.edge s.fields⟩,decide (row.edge = .beep))

def system : EventSystem State := ⟨initial,step⟩

def Valid (s : State) : Prop := ∃ row, lookup s.pc = some row

/-- Every valid graph state has a valid successor for every finite bank,
without assuming reachability or any zero-register invariant. -/
theorem step_preserves_valid (s : State) (h : Valid s) : Valid (step s).1 := by
  obtain ⟨row,hl⟩ := h
  have hm := lookup_in_table s.pc row hl
  have hb := Bool.and_eq_true_iff.mp (List.all_eq_true.mp all_successors_checked row hm)
  cases hw : walk rootIndex s.pc with
  | none => simp [lookup,hw] at hl
  | some e =>
    have hr : row = makeRow s.pc e := by simpa [lookup,hw] using hl.symm
    subst row
    cases ht : test e s.fields with
    | false =>
      have hs : (successor e s.pc false).isSome = true := hb.1
      cases hn : successor e s.pc false with
      | none => simp [hn] at hs
      | some pc =>
        obtain ⟨r,hr,_⟩ := successor_closed e s.pc false pc hn
        refine ⟨r,?_⟩
        simpa [step,lookup,hw,makeRow,ht,hn] using hr
    | true =>
      have hs : (successor e s.pc true).isSome = true := hb.2
      cases hn : successor e s.pc true with
      | none => simp [hn] at hs
      | some pc =>
        obtain ⟨r,hr,_⟩ := successor_closed e s.pc true pc hn
        refine ⟨r,?_⟩
        simpa [step,lookup,hw,makeRow,ht,hn] using hr

def Related (g : State) (p : GrammarPure.State) : Prop :=
  g.fields = p.fields ∧
  ∃ s, GrammarPure.Related p s ∧
    ∃ e len control, 0 < len ∧
      descend 163 rootIndex (pureBits p.control) 0 = some (e,len) ∧
      controlStep e p.fields (window (pureBits p.control) 0 len) = some control ∧
      g.pc = window (pureBits p.control) 0 len

theorem initial_related : Related initial GrammarPure.initial := by
  refine ⟨rfl,GrammarOperationalRun.initial,GrammarPure.initial_related,
    .inc 6,1,[true],by decide,by decide,by decide,by decide⟩

theorem step_related (g : State) (p : GrammarPure.State) (h : Related g p) :
    (step g).2 = (GrammarPure.step p).2 ∧ Related (step g).1 (GrammarPure.step p).1 := by
  obtain ⟨hf,s,hphys,e,len,control,hlen,hdesc,hcontrol,hpc⟩ := h
  obtain ⟨len',_,_,hend,hwalk⟩ := descend_trace 163 rootIndex (pureBits p.control) 0 e len hdesc
  have heq : len' = len := by omega
  subst len'
  let code := window (pureBits p.control) 0 len
  have hw : walk rootIndex code = some e := hwalk
  have hl : lookup g.pc = some (makeRow code e) := by rw [hpc]; exact lookup_of_walk code e hw
  have hp : GrammarPure.step p = (⟨control,applyUpdate e p.fields⟩,decide (e = .beep)) := by
    simp [GrammarPure.step,hdesc,hcontrol]
  have hphys' := (GrammarPure.step_related p s hphys).2
  obtain ⟨e',len',control',hpos',hdesc',hctrl'⟩ :=
    GrammarPure.related_step_defined (GrammarPure.step p).1 (GrammarOperationalRun.next s) hphys'
  rw [hp] at hdesc' hctrl'
  have hn : successor e code (test e p.fields) =
      some (window (pureBits control) 0 len') := by
    unfold successor
    rw [transfer_correct,hcontrol]
    simp [hdesc']
  have hg : step g =
      (⟨window (pureBits control) 0 len',applyUpdate e p.fields⟩,decide (e = .beep)) := by
    simp only [step,hl,Option.getD_some,makeRow]
    rw [hf]
    cases ht : test e p.fields <;> rw [ht] at hn <;> simp [hn]
  rw [hp,hg]
  refine ⟨rfl,rfl,GrammarOperationalRun.next s,?_,e',len',control',hpos',hdesc',hctrl',rfl⟩
  simpa only [hp] using hphys'

theorem related_run (n : Nat) : Related (system.run n) (GrammarPure.system.run n) := by
  induction n with
  | zero => exact initial_related
  | succ n ih =>
    have h := (step_related (system.run n) (GrammarPure.system.run n) ih).2
    simpa only [EventSystem.run_succ,system,GrammarPure.system] using h

/-- Each reachable graph PC denotes an actual extracted leaf occurrence. -/
theorem reachable_row (n : Nat) :
    ∃ row, lookup (system.run n).pc = some row ∧ row ∈ table ∧
      row.no.isSome = true ∧ row.yes.isSome = true := by
  obtain ⟨_,s,hphys,e,len,control,hlen,hdesc,hctrl,hpc⟩ := related_run n
  obtain ⟨len',_,_,hend,hwalk⟩ :=
    descend_trace 163 rootIndex (pureBits (GrammarPure.system.run n).control) 0 e len hdesc
  have heq : len' = len := by omega
  subst len'
  let code := window (pureBits (GrammarPure.system.run n).control) 0 len
  let row := makeRow code e
  have hl : lookup (system.run n).pc = some row := by rw [hpc]; exact lookup_of_walk code e hwalk
  have hm : row ∈ table := lookup_in_table _ row hl
  have hv := List.all_eq_true.mp all_successors_checked row hm
  have hv' := Bool.and_eq_true_iff.mp hv
  exact ⟨row,hl,hm,hv'.1,hv'.2⟩

/-- The finite graph executes exactly one physical-grammar action per step,
including its marked-event bit. -/
noncomputable def simulation : SegmentSimulation system GrammarPure.system where
  Rel := Related
  initial := initial_related
  duration := fun _ _ => 1
  positive := by intros; decide
  next := by
    intro g p h
    have hs := (step_related g p h).2
    simpa [system,GrammarPure.system,EventSystem.advance] using hs
  event_iff := by
    intro g p h
    have hs := (step_related g p h).1
    change ((step g).2 = true ↔ ∃ j, j < 1 ∧ GrammarPure.system.BeepFrom p j)
    constructor
    · intro he
      refine ⟨0,by decide,?_⟩
      simpa [EventSystem.BeepFrom,EventSystem.advance,GrammarPure.system] using hs.symm.trans he
    · rintro ⟨j,hj,he⟩
      have hz : j = 0 := by omega
      subst j
      have hh : (GrammarPure.system.step p).2 = true := by
        simpa [EventSystem.BeepFrom,EventSystem.advance] using he
      exact hs.trans hh
  event_unique := by
    intro g p h j k hj hk _ _
    omega

noncomputable def refinement : EventRefinement system GrammarPure.system := simulation.toEventRefinement

noncomputable def physicalRefinement : EventRefinement system GrammarOperationalRun.physicalSystem :=
  refinement.trans GrammarPure.physicalRefinement

theorem eventuallySilent_iff_blank_start :
    system.EventuallySilent ↔ Record285.machine.system.EventuallySilent :=
  refinement.eventuallySilent_iff.trans GrammarPure.eventuallySilent_iff_blank_start

theorem infinitelyMany_iff_blank_start :
    system.InfinitelyManyBeeps ↔ Record285.machine.system.InfinitelyManyBeeps :=
  refinement.infinitelyManyBeeps_iff.trans GrammarPure.infinitelyMany_iff_blank_start

end Shared.PNP.Record285.GrammarControlGraph
