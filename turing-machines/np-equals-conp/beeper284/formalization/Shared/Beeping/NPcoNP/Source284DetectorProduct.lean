import Shared.Beeping.NPcoNP.Source284JoinedEndDetectorTable
import Shared.Beeping.NPcoNP.Source284ListTables
import Shared.Beeping.NPcoNP.Source284TaggedCyclesSource

/-! An executable finite-state product carries the joined-body detector
through an existing relative source table. Only explicitly marked source rows
feed a bit to the detector; all original writes, moves, and termination remain
unchanged. Proving that a particular serializer marks exactly one row per
input bit and dispatching on `done` are separate obligations. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284DetectorProduct

open Shared.Beeping.NPcoNP.Source284JoinedEndDetector
open Shared.Beeping.NPcoNP.Source284JoinedEndDetectorTable (index)
open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun

/-- Inverse of the detector's nine finite state codes. Values outside the
allocated range are interpreted as `done` but are excluded on live paths. -/
def decode : Nat → State
  | 0 => .lead | 1 => .witnessData | 2 => .witnessZeroMarker
  | 3 => .witnessOneMarker | 4 => .gap | 5 => .inputMarker
  | 6 => .inputData | 7 => .bad | _ => .done

@[simp] theorem decode_index (q : State) : decode (index q) = q := by cases q <;> rfl
@[simp] theorem index_lt (q : State) : index q < 9 := by cases q <;> decide

/-- The allocated bound is a finite pairing rectangle. -/
def allocated (states : Nat) : Nat := Nat.pair 9 states

def lifted (phase : State) (c : Config) : Config :=
  ⟨c.left,c.right,c.state.map (fun q => Nat.pair (index phase) q)⟩

/-- A finite marks list determines the rows whose scanned symbol enters the
detector. Missing entries default to false. -/
def update (marks : List Bool) (c : Config) (phase : State) : State :=
  match c.state with
  | none => phase
  | some q => if (marks[q]?).getD false then
      Source284JoinedEndDetector.step phase (c.right.testBit 0) else phase

/-- Out-of-range product states use a nonaccepting self-loop. -/
def table (states : Nat) (marks : List Bool) (original : Nat → Bool → Row)
    (s : Nat) (read : Bool) : Row :=
  let p := Nat.unpair s
  if p.1 < 9 ∧ p.2 < states then
    let r := original p.2 read
    let phase := if (marks[p.2]?).getD false then
      Source284JoinedEndDetector.step (decode p.1) read else decode p.1
    ⟨r.write,r.turn,r.next.map (fun q => Nat.pair (index phase) q)⟩
  else ⟨read,false,some s⟩

/-- Finite concrete data: the original rows and marks are lists, and product
rows use only total list lookup and the detector's fixed transition table. -/
def finiteTable (rows : Source284ListTables.Rows) (marks : List Bool) : Nat → Bool → Row :=
  table rows.length marks (Source284ListTables.table rows)

theorem pair_lt_allocated (states q : Nat) (phase : State) (hq : q < states) :
    Nat.pair (index phase) q < allocated states := by
  exact lt_trans (Nat.pair_lt_pair_left q (index_lt phase))
    (Nat.pair_lt_pair_right 9 hq)

/-- All product rows remain within the finite allocation. -/
theorem closed (states : Nat) (marks : List Bool) (original : Nat → Bool → Row)
    (hv : Closed states original) : Closed (allocated states) (table states marks original) := by
  intro s hs b target hnext
  by_cases hp : (Nat.unpair s).1 < 9 ∧ (Nat.unpair s).2 < states
  · cases he : (original (Nat.unpair s).2 b).next with
    | none => simp [table,hp,he] at hnext
    | some q =>
      have hq := hv (Nat.unpair s).2 hp.2 b q he
      simp [table,hp,he] at hnext
      subst target
      exact pair_lt_allocated states q _ hq
  · simp [table,hp] at hnext
    subst target
    exact hs

/-- One product transition has the original tape effect and the specified
finite-control update. -/
theorem step_lifted (states : Nat) (marks : List Bool) (original : Nat → Bool → Row)
    (phase : State) (c : Config) (hc : Valid states c) :
    Source284TableRun.step (table states marks original) (lifted phase c) =
      lifted (update marks c phase) (Source284TableRun.step original c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      have hq : q < states := hc q rfl
      cases hr : (original q (right.testBit 0)).next with
      | none =>
        cases ht : (original q (right.testBit 0)).turn <;>
          simp only [Nat.testBit_zero] at hr ht <;>
          simp [lifted,update,Source284TableRun.step,table,Nat.unpair_pair,hq,hr,ht]
      | some q' =>
        cases ht : (original q (right.testBit 0)).turn <;>
          simp only [Nat.testBit_zero] at hr ht <;>
          simp [lifted,update,Source284TableRun.step,table,Nat.unpair_pair,hq,hr,ht]

/-- The monitor state after any finite number of original source steps. -/
def monitor (marks : List Bool) (original : Nat → Bool → Row) (c : Config)
    (phase : State) : Nat → State
  | 0 => phase
  | n+1 => update marks (run original c n) (monitor marks original c phase n)

/-- For every finite clock, the executable product preserves the complete
source configuration and carries exactly the marked-row detector state. -/
theorem run_lifted (states : Nat) (marks : List Bool) (original : Nat → Bool → Row)
    (phase : State) (c : Config) (hc : Valid states c) (hv : Closed states original) (n : Nat) :
    run (table states marks original) (lifted phase c) n =
      lifted (monitor marks original c phase n) (run original c n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [run,monitor,ih]
    exact step_lifted states marks original _ _ (valid_run states original c hv hc n)

/-- The finite word of symbols encountered on marked rows, in temporal
order. Rows after an ordinary terminating state contribute no symbols. -/
def observed (marks : List Bool) (original : Nat → Bool → Row) (c : Config) : Nat → List Bool
  | 0 => []
  | n+1 => observed marks original c n ++
      match (run original c n).state with
      | none => []
      | some q => if (marks[q]?).getD false then [(run original c n).right.testBit 0] else []

/-- The product monitor is exactly the finite automaton folded over the
symbols actually read on marked rows. -/
theorem monitor_observed (marks : List Bool) (original : Nat → Bool → Row)
    (c : Config) (phase : State) (n : Nat) :
    monitor marks original c phase n =
      (observed marks original c n).foldl Source284JoinedEndDetector.step phase := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [monitor,observed,List.foldl_append,← ih]
    cases hs : (run original c n).state with
    | none => simp [update,hs]
    | some q =>
      cases hm : (marks[q]?).getD false <;> simp [update,hs,hm]

/-- A successful first-detection result entails that the finite automaton
is in `done` after exactly the reported number of input symbols. -/
theorem scan_fold_done (phase : State) (bits : List Bool) (n : Nat) (suffix : List Bool)
    (h : scan phase bits = some (n,suffix)) :
    (bits.take n).foldl Source284JoinedEndDetector.step phase = .done := by
  induction bits generalizing phase n suffix with
  | nil =>
    cases phase <;> simp [scan] at h
    case done => rcases h with ⟨rfl,rfl⟩; rfl
  | cons b bs ih =>
    cases phase with
    | done => simp [scan] at h; rcases h with ⟨rfl,rfl⟩; rfl
    | bad => simp [scan] at h
    | lead | witnessData | witnessZeroMarker | witnessOneMarker | gap | inputMarker | inputData =>
      simp only [scan] at h
      obtain ⟨⟨j,rest⟩,hs,he⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at he
      rcases he with ⟨rfl,rfl⟩
      simpa [List.take_succ_cons,List.foldl_cons] using ih _ _ _ hs

/-- If the marked source-row trace is the whole reversed joined body, the
product monitor is `done` at that exact finite source time. -/
theorem monitor_done_of_body (marks : List Bool) (original : Nat → Bool → Row)
    (c : Config) (n : Nat) (x w : List Bool)
    (htrace : observed marks original c n = (Source284JoinedPrefixScan.joinedBody x w).reverse) :
    monitor marks original c .lead n = .done := by
  rw [monitor_observed,htrace]
  have h := scan_fold_done .lead
    ((Source284JoinedPrefixScan.joinedBody x w).reverse ++ [])
    (Source284JoinedPrefixScan.joinedBody x w).length [] (scan_body x w [])
  have ht : ((Source284JoinedPrefixScan.joinedBody x w).reverse ++ []).take
      (Source284JoinedPrefixScan.joinedBody x w).length =
        (Source284JoinedPrefixScan.joinedBody x w).reverse := by simp
  rw [ht] at h
  exact h

theorem fold_bad (bits : List Bool) :
    bits.foldl Source284JoinedEndDetector.step .bad = .bad := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simpa [List.foldl_cons,Source284JoinedEndDetector.step] using ih

/-- If a finite fold reaches `done`, the first-detection scanner has a
successful finite result on that same prefix. -/
theorem scan_of_fold_done (bits : List Bool) (phase : State)
    (h : bits.foldl Source284JoinedEndDetector.step phase = .done) :
    ∃ n suffix, scan phase bits = some (n,suffix) := by
  induction bits generalizing phase with
  | nil =>
    cases phase <;> simp at h
    case done => exact ⟨0,[],rfl⟩
  | cons b bs ih =>
    cases phase with
    | done => exact ⟨0,b::bs,rfl⟩
    | bad =>
      simp only [List.foldl_cons,Source284JoinedEndDetector.step,fold_bad] at h
      contradiction
    | lead | witnessData | witnessZeroMarker | witnessOneMarker | gap | inputMarker | inputData =>
      simp only [List.foldl_cons] at h
      obtain ⟨n,suffix,hs⟩ := ih _ h
      refine ⟨n+1,suffix,?_⟩
      simp only [scan,hs,Option.map_some,Prod.fst,Prod.snd]

/-- The automaton's state cannot be `done` at any proper joined-body prefix. -/
theorem fold_body_no_early (x w : List Bool) (j : Nat)
    (hj : j < (Source284JoinedPrefixScan.joinedBody x w).length) :
    (((Source284JoinedPrefixScan.joinedBody x w).reverse.take j).foldl
      Source284JoinedEndDetector.step .lead) ≠ .done := by
  intro hf
  obtain ⟨n,suffix,hs⟩ := scan_of_fold_done _ _ hf
  rw [no_early_detection x w j hj] at hs
  contradiction

/-- A marked-row trace equal to a proper body prefix cannot put the product
monitor in `done`. -/
theorem monitor_no_early (marks : List Bool) (original : Nat → Bool → Row)
    (c : Config) (n : Nat) (x w : List Bool) (j : Nat)
    (hj : j < (Source284JoinedPrefixScan.joinedBody x w).length)
    (htrace : observed marks original c n = (Source284JoinedPrefixScan.joinedBody x w).reverse.take j) :
    monitor marks original c .lead n ≠ .done := by
  rw [monitor_observed,htrace]
  exact fold_body_no_early x w j hj

/-- The lifted source configuration stays within the paired allocation. -/
theorem lifted_valid (states : Nat) (phase : State) (c : Config) (hc : Valid states c) :
    Valid (allocated states) (lifted phase c) := by
  intro target ht
  cases hq : c.state with
  | none => simp [lifted,hq] at ht
  | some q =>
    have hq' := hc q hq
    simp [lifted,hq] at ht
    subst target
    exact pair_lt_allocated states q phase hq'

/-- The numeric unary-record source executes the same monitored product
for every clock, with one source transition for each original transition. -/
theorem source_run (states : Nat) (marks : List Bool) (original : Nat → Bool → Row)
    (phase : State) (c : Config) (hc : Valid states c) (hv : Closed states original)
    (tail n : Nat) :
    Source284Relative.run (encode (allocated states) (table states marks original) tail)
      (toSource (lifted phase c)) n =
      toSource (lifted (monitor marks original c phase n) (run original c n)) := by
  rw [run_toSource _ _ _ _ (closed states marks original hv) (lifted_valid states phase c hc),
    run_lifted states marks original phase c hc hv]

/-- The actual finite serializer rows with a mark on each orientation of
absolute state zero. Whether these marks occur exactly once per useful cycle
is a further theorem, not an assumption hidden in the table. -/
def serializerRows (zero one : List Bool) : Source284ListTables.Rows :=
  Source284FiniteRelativeRows.rows (Shared.Codes.FiniteProgramTaggedLoop.program zero one)

def serializerMarks (zero one : List Bool) : List Bool :=
  [true,true] ++ List.replicate ((serializerRows zero one).length-2) false

theorem serializer_mark (zero one : List Bool) (q : Nat) (hq : q < (serializerRows zero one).length) :
    ((serializerMarks zero one)[q]?).getD false = decide (q < 2) := by
  cases q with
  | zero => rfl
  | succ q => cases q with
    | zero => rfl
    | succ q => simp [serializerMarks]

/-- The detector product of the actual finite serializer rows is closed and
continues to reproduce the uninstrumented source run. -/
theorem serializer_product_closed (zero one : List Bool) :
    Closed (allocated (serializerRows zero one).length)
      (finiteTable (serializerRows zero one) (serializerMarks zero one)) := by
  apply closed
  exact Source284FiniteRelativeRows.closed _ (Shared.Codes.FiniteProgramTaggedLoop.program_valid zero one)

/-- A finite list presentation yields a closed finite product, without
reifying an arbitrary Lean function as executable data. -/
theorem finite_closed (rows : Source284ListTables.Rows) (marks : List Bool)
    (hv : Source284ListTables.valid rows = true) : Closed (allocated rows.length) (finiteTable rows marks) :=
  closed rows.length marks (Source284ListTables.table rows) (Source284ListTables.valid_closed rows hv)

/-- Source-level product theorem instantiated with the actual finite
serializer table and explicit entry marks. -/
theorem serializer_source_run (zero one : List Bool) (c : Config)
    (hc : Valid (serializerRows zero one).length c) (n : Nat) :
    Source284Relative.run
      (encode (allocated (serializerRows zero one).length)
        (finiteTable (serializerRows zero one) (serializerMarks zero one)) 1)
      (toSource (lifted .lead c)) n =
    toSource (lifted (monitor (serializerMarks zero one)
      (Source284ListTables.table (serializerRows zero one)) c .lead n)
      (run (Source284ListTables.table (serializerRows zero one)) c n)) := by
  exact source_run _ _ _ .lead c hc
    (Source284FiniteRelativeRows.closed _ (Shared.Codes.FiniteProgramTaggedLoop.program_valid zero one)) 1 n

/-- A coarse explicit bound for the product's allocated logical states. -/
theorem allocated_bound (states : Nat) : allocated states ≤ (max 9 states+1)^2 := by
  have h := Nat.pair_lt_max_add_one_sq 9 states
  exact Nat.le_of_lt (by simpa [allocated] using h)

namespace Fixtures

def rows : Source284ListTables.Rows :=
  [(⟨false,false,some 1⟩,⟨true,false,some 1⟩),
   (⟨false,false,some 1⟩,⟨true,false,some 1⟩)]
example : Source284ListTables.valid rows = true := by decide +kernel
example : update [true,false] ⟨0,0,some 0⟩ .lead = .witnessData := by decide +kernel
example : update [true,false] ⟨0,1,some 1⟩ .witnessData = .witnessData := by decide +kernel
example : (run (finiteTable rows [true,false]) (lifted .lead ⟨0,0,some 0⟩) 2).state =
    some (Nat.pair (index .witnessData) 1) := by decide +kernel
end Fixtures

end Shared.Beeping.NPcoNP.Source284DetectorProduct
