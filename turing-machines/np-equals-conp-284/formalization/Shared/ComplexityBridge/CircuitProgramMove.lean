import Shared.ComplexityBridge.CircuitTable
import Shared.ComplexityBridge.CircuitTapeMove

/-! Wiring finite-program row selection to the bounded tape-movement circuit.
This module handles a continuing row; state updates, terminal/error handling,
and a polynomial bit-cost generator remain separate obligations. -/
namespace Shared.ComplexityBridge.CircuitProgramMove
open Shared.ComplexityBridge.CircuitCNF
open Shared.ComplexityBridge.CircuitSelect
open Shared.ComplexityBridge.CircuitRelocate
open Shared.ComplexityBridge.CircuitTable
open Shared.Codes.FinitePrograms
open Shared.ComplexityBridge

/-- The input wires of a table selector are the one-hot state and a designated
read-symbol wire in the enclosing circuit. -/
def tableRefs (n read : Nat) : List Nat := List.range n ++ [read]

theorem tableRefs_state (n read i : Nat) (hi : i < n) :
    ((tableRefs n read)[i]?).getD 0 = i := by
  simp [tableRefs,List.getElem?_append_left,hi]

theorem tableRefs_read (n read : Nat) : ((tableRefs n read)[n]?).getD 0 = read := by
  simp [tableRefs,List.getElem?_append_right]

theorem tableRefs_bound (n read base : Nat) (hn : n ≤ base) (hr : read < base) :
    ∀ i < n+1, ((tableRefs n read)[i]?).getD 0 < base := by
  intro i hi
  by_cases h : i < n
  · rw [tableRefs_state n read i h]; omega
  · have he : i = n := by omega
    subst i
    simpa [tableRefs_read] using hr

/-- Relocate a concrete row-field selector into the enclosing wire space. -/
def tableBlock (p : Program) (read : Nat) (project : Row → Bool) (base : Nat) : List Gate :=
  relocate (p.length+1) base (tableRefs p.length read) (lookupGates p.length (projectRows project p))

def tableResult (p : Program) (read : Nat) (project : Row → Bool) (base : Nat) : Nat :=
  remap (p.length+1) base (tableRefs p.length read) (lookupOutput p.length (projectRows project p))

theorem tableBlock_length (p : Program) (read : Nat) (project : Row → Bool) (base : Nat) :
    (tableBlock p read project base).length = 2+4*p.length := by
  simp [tableBlock,relocate_length,lookupGates_length,projectRows]

theorem tableBlock_valid (p : Program) (read : Nat) (project : Row → Bool) (base : Nat)
    (hn : p.length ≤ base) (hr : read < base) : validGates base (tableBlock p read project base) := by
  apply relocate_valid
  · exact tableRefs_bound p.length read base hn hr
  · apply lookup_valid
    simp [projectRows]

theorem tableResult_bound (p : Program) (read : Nat) (project : Row → Bool) (base : Nat)
    (hn : p.length ≤ base) (hr : read < base) :
    tableResult p read project base < base+(tableBlock p read project base).length := by
  have he := remap_bound (p.length+1) base (tableRefs p.length read)
    (tableRefs_bound p.length read base hn hr)
    (lookupGates p.length (projectRows project p)).length
    (lookupOutput p.length (projectRows project p)) (lookupOutput_bound _ _)
  simpa [tableResult,tableBlock,relocate_length] using he

/-- Every relocated selector computes the corresponding field of the row
selected by the shared finite-program evaluator. -/
theorem tableBlock_simulate (p : Program) (read : Nat) (project : Row → Bool)
    (wires : List Bool) (c : Config) (row : Row) (hrow : rowAt p c = some row)
    (hn : p.length ≤ wires.length) (hr : read < wires.length)
    (hstate : ∀ j, j < p.length → wire wires j = decide (j = c.1))
    (hread : wire wires read = c.2.2.1) :
    wire (simulate wires (tableBlock p read project wires.length))
      (tableResult p read project wires.length) = project row := by
  let refs := tableRefs p.length read
  let source := readState wires (p.length+1) refs
  have hs : source.length = p.length+1 := readState_length _ _ _
  have hstate' : ∀ j, j < p.length → wire source j = decide (j = c.1) := by
    intro j hj
    rw [readState_wire wires (p.length+1) refs j (by omega)]
    rw [tableRefs_state p.length read j hj]
    exact hstate j hj
  have hread' : wire source p.length = c.2.2.1 := by
    rw [readState_wire wires (p.length+1) refs p.length (by omega)]
    rw [tableRefs_read]
    exact hread
  have hg := lookup_valid p.length (projectRows project p) (by simp [projectRows])
  have he := relocate_simulate wires (p.length+1) refs
    (lookupGates p.length (projectRows project p))
    (tableRefs_bound p.length read wires.length hn hr) hg
    (lookupOutput p.length (projectRows project p)) (lookupOutput_bound _ _)
  have hk := lookup_rowAt p project c row source hrow hs hstate' hread'
  exact he.trans hk

def rowWrite (row : Row) : Bool := row.1
def rowLeft (row : Row) : Bool := !row.2.1

def rowControls (p : Program) (read base : Nat) : List Gate :=
  tableBlock p read rowWrite base ++
    tableBlock p read rowLeft (base+(tableBlock p read rowWrite base).length)

def writeResult (p : Program) (read base : Nat) : Nat := tableResult p read rowWrite base

def leftResult (p : Program) (read base : Nat) : Nat :=
  tableResult p read rowLeft (base+(tableBlock p read rowWrite base).length)

theorem rowControls_length (p : Program) (read base : Nat) :
    (rowControls p read base).length = 2*(2+4*p.length) := by
  simp only [rowControls,List.length_append,tableBlock_length]
  omega

theorem rowControls_valid (p : Program) (read base : Nat)
    (hn : p.length ≤ base) (hr : read < base) : validGates base (rowControls p read base) := by
  simp only [rowControls,validGates_append]
  refine ⟨tableBlock_valid p read rowWrite base hn hr,?_⟩
  apply tableBlock_valid <;> omega

theorem writeResult_bound (p : Program) (read base : Nat)
    (hn : p.length ≤ base) (hr : read < base) :
    writeResult p read base < base+(rowControls p read base).length := by
  have h := tableResult_bound p read rowWrite base hn hr
  simp only [writeResult,rowControls,List.length_append]
  omega

theorem leftResult_bound (p : Program) (read base : Nat)
    (hn : p.length ≤ base) (hr : read < base) :
    leftResult p read base < base+(rowControls p read base).length := by
  have h := tableResult_bound p read rowLeft (base+(tableBlock p read rowWrite base).length)
    (by omega) (by omega)
  simp only [leftResult,rowControls,List.length_append]
  omega

/-- Both control bits come from the same actually selected transition row. -/
theorem rowControls_simulate (p : Program) (read : Nat) (wires : List Bool)
    (c : Config) (row : Row) (hrow : rowAt p c = some row)
    (hn : p.length ≤ wires.length) (hr : read < wires.length)
    (hstate : ∀ j, j < p.length → wire wires j = decide (j = c.1))
    (hread : wire wires read = c.2.2.1) :
    wire (simulate wires (rowControls p read wires.length)) (writeResult p read wires.length) = row.1 ∧
    wire (simulate wires (rowControls p read wires.length)) (leftResult p read wires.length) = !row.2.1 := by
  let first := tableBlock p read rowWrite wires.length
  let mid := simulate wires first
  have hm : mid.length = wires.length+first.length := by simp [mid,simulate_length]
  have keep (i : Nat) (hi : i < wires.length) : wire mid i = wire wires i := wire_simulate wires first i hi
  have hs : ∀ j, j < p.length → wire mid j = decide (j = c.1) := by
    intro j hj
    rw [keep j (by omega)]
    exact hstate j hj
  have hread' : wire mid read = c.2.2.1 := by rw [keep read hr]; exact hread
  have hw := tableBlock_simulate p read rowWrite wires c row hrow hn hr hstate hread
  have hd := tableBlock_simulate p read rowLeft mid c row hrow (by rw [hm]; omega)
    (by rw [hm]; omega) hs hread'
  have hwb := tableResult_bound p read rowWrite wires.length hn hr
  rw [hm] at hd
  simp only [rowControls,simulate_append]
  change wire (simulate mid (tableBlock p read rowLeft (wires.length+first.length))) _ = _ ∧
    wire (simulate mid (tableBlock p read rowLeft (wires.length+first.length))) _ = _
  constructor
  · rw [wire_simulate mid _ _ (by rw [hm]; exact hwb)]
    exact hw
  · exact hd

/-- State bits followed by the bounded left/head/right tape window. -/
def inputWidth (p : Program) (k : Nat) : Nat := p.length+(2*k+1)

def machineBit (p : Program) (k : Nat) (c : Config) (i : Nat) : Bool :=
  if i < p.length then decide (i = c.1) else CircuitTapeMove.tapeView k c.2 (i-p.length)

def machineWires (p : Program) (k : Nat) (c : Config) : List Bool :=
  seed (inputWidth p k) (machineBit p k c)

theorem machineWires_length (p : Program) (k : Nat) (c : Config) :
    (machineWires p k c).length = inputWidth p k := seed_length _ _

theorem machineWires_state (p : Program) (k : Nat) (c : Config) (i : Nat) (hi : i < p.length) :
    wire (machineWires p k c) i = decide (i = c.1) := by
  unfold machineWires
  rw [seed_wire _ _ _ (by simp [inputWidth]; omega)]
  simp [machineBit,hi]

theorem machineWires_tape (p : Program) (k : Nat) (c : Config) (i : Nat) (hi : i < 2*k+1) :
    wire (machineWires p k c) (p.length+i) = CircuitTapeMove.tapeView k c.2 i := by
  unfold machineWires
  rw [seed_wire _ _ _ (by simp [inputWidth]; omega)]
  simp [machineBit]

theorem machineWires_read (p : Program) (k : Nat) (c : Config) :
    wire (machineWires p k c) (p.length+k) = c.2.2.1 := by
  rw [machineWires_tape p k c k (by omega)]
  simp [CircuitTapeMove.tapeView]

def readIndex (p : Program) (k : Nat) : Nat := p.length+k

def controls (p : Program) (k base : Nat) : List Gate := rowControls p (readIndex p k) base

def tapeRefs (p : Program) (k base : Nat) : List Nat :=
  writeResult p (readIndex p k) base :: leftResult p (readIndex p k) base ::
    (List.range (2*k+1)).map (p.length+·)

theorem tapeRefs_write (p : Program) (k base : Nat) :
    ((tapeRefs p k base)[0]?).getD 0 = writeResult p (readIndex p k) base := by simp [tapeRefs]

theorem tapeRefs_left (p : Program) (k base : Nat) :
    ((tapeRefs p k base)[1]?).getD 0 = leftResult p (readIndex p k) base := by simp [tapeRefs]

theorem tapeRefs_tape (p : Program) (k base i : Nat) (hi : i < 2*k+1) :
    ((tapeRefs p k base)[2+i]?).getD 0 = p.length+i := by
  have he : 2+i = Nat.succ (Nat.succ i) := by omega
  rw [he]
  simp [tapeRefs,hi]

theorem tapeRefs_bound (p : Program) (k base : Nat) (hb : inputWidth p k ≤ base) :
    ∀ i < CircuitTapeMove.width k, ((tapeRefs p k base)[i]?).getD 0 < base+(controls p k base).length := by
  intro i hi
  have hn : p.length ≤ base := by simp only [inputWidth] at hb; omega
  have hr : readIndex p k < base := by simp only [readIndex,inputWidth] at *; omega
  cases i with
  | zero =>
    rw [tapeRefs_write]
    exact writeResult_bound p (readIndex p k) base hn hr
  | succ i =>
    cases i with
    | zero =>
      rw [tapeRefs_left]
      exact leftResult_bound p (readIndex p k) base hn hr
    | succ j =>
      have hj : j < 2*k+1 := by simp only [CircuitTapeMove.width] at hi; omega
      have he : j+1+1 = 2+j := by omega
      rw [he,tapeRefs_tape p k base j hj]
      simp only [inputWidth] at hb
      omega

/-- One pair of row selectors followed by a wired tape-movement circuit. -/
def programMoveGates (p : Program) (k base : Nat) : List Gate :=
  controls p k base ++
    relocate (CircuitTapeMove.width k) (base+(controls p k base).length) (tapeRefs p k base) (CircuitTapeMove.moveGates k)

def programMoveOutput (p : Program) (k base i : Nat) : Nat :=
  remap (CircuitTapeMove.width k) (base+(controls p k base).length) (tapeRefs p k base) (CircuitTapeMove.outputIndex k i)

theorem programMoveGates_length (p : Program) (k base : Nat) :
    (programMoveGates p k base).length = 2*(2+4*p.length)+(1+4*(2*k+1)) := by
  simp [programMoveGates,controls,rowControls_length,relocate_length,CircuitTapeMove.moveGates_length]

theorem programMoveGates_valid (p : Program) (k base : Nat) (hb : inputWidth p k ≤ base) :
    validGates base (programMoveGates p k base) := by
  simp only [programMoveGates,validGates_append]
  constructor
  · apply rowControls_valid
    · simp only [inputWidth] at hb; omega
    · simp only [inputWidth,readIndex] at *; omega
  · apply relocate_valid
    · exact tapeRefs_bound p k base hb
    · exact CircuitTapeMove.moveGates_valid k

/-- The row-selected control wires and the original tape window form exactly
the input expected by the independently verified movement circuit. -/
theorem connectedTapeInput (p : Program) (k : Nat) (c : Config) (row : Row)
    (hrow : rowAt p c = some row) :
    readState
      (simulate (machineWires p k c) (controls p k (inputWidth p k)))
      (CircuitTapeMove.width k) (tapeRefs p k (inputWidth p k)) =
    CircuitTapeMove.inputWires k row.1 (!row.2.1) c.2 := by
  let wires := machineWires p k c
  let base := inputWidth p k
  let mid := simulate wires (controls p k base)
  have hw : wires.length = base := machineWires_length p k c
  have hb : p.length ≤ wires.length := by rw [hw]; simp [base,inputWidth]
  have hr : readIndex p k < wires.length := by rw [hw]; simp [base,inputWidth,readIndex]; omega
  have hs : ∀ j, j < p.length → wire wires j = decide (j = c.1) := machineWires_state p k c
  have hrbit : wire wires (readIndex p k) = c.2.2.1 := machineWires_read p k c
  have hc := rowControls_simulate p (readIndex p k) wires c row hrow hb hr hs hrbit
  rw [hw] at hc
  change wire mid (writeResult p (readIndex p k) base) = row.1 ∧
    wire mid (leftResult p (readIndex p k) base) = !row.2.1 at hc
  have hm : mid.length = base+(controls p k base).length := by simp [mid,simulate_length,hw]
  apply List.ext_getElem
  · simp [readState_length,CircuitTapeMove.inputWires_length]
  · intro i hi₁ hi₂
    have hi : i < CircuitTapeMove.width k := by simpa [readState_length] using hi₁
    rw [← wire_get _ i hi₁,readState_wire mid _ _ i hi]
    rw [← wire_get _ i hi₂,CircuitTapeMove.inputWires_bit k row.1 (!row.2.1) c.2 i hi]
    cases i with
    | zero => simpa [tapeRefs_write,CircuitTapeMove.inputBit] using hc.1
    | succ i =>
      cases i with
      | zero => simpa [tapeRefs_left,CircuitTapeMove.inputBit] using hc.2
      | succ j =>
        have hj : j < 2*k+1 := by simp only [CircuitTapeMove.width] at hi; omega
        have he : j+1+1 = 2+j := by omega
        rw [he,tapeRefs_tape p k base j hj]
        rw [wire_simulate wires _ (p.length+j) (by rw [hw]; simp [base,inputWidth]; omega)]
        rw [machineWires_tape p k c j hj]
        exact (CircuitTapeMove.inputBit_view k row.1 (!row.2.1) c.2 j).symm

/-- The wired table and movement blocks compute each tape-window bit for the
selected row of the actual finite-program step. -/
theorem programMove_correct (p : Program) (k : Nat) (c : Config) (row : Row)
    (hrow : rowAt p c = some row) (i : Nat) (hi : i < 2*k+1)
    (hl : c.2.1.length ≤ k) (hr : c.2.2.2.length ≤ k) :
    wire (simulate (machineWires p k c) (programMoveGates p k (inputWidth p k)))
      (programMoveOutput p k (inputWidth p k) i) =
    CircuitTapeMove.tapeView k (moveTape (!row.2.1) row.1 c.2) i := by
  let wires := machineWires p k c
  let base := inputWidth p k
  let mid := simulate wires (controls p k base)
  have hw : wires.length = base := machineWires_length p k c
  have hm : mid.length = base+(controls p k base).length := by simp [mid,simulate_length,hw]
  have hin : ∀ j < CircuitTapeMove.width k, ((tapeRefs p k base)[j]?).getD 0 < mid.length := by
    rw [hm]
    exact tapeRefs_bound p k base le_rfl
  have hout : CircuitTapeMove.outputIndex k i < CircuitTapeMove.width k+(CircuitTapeMove.moveGates k).length := by
    simp only [CircuitTapeMove.outputIndex,CircuitTapeMove.moveGates_length]
    omega
  have he := relocate_simulate mid (CircuitTapeMove.width k) (tapeRefs p k base)
    (CircuitTapeMove.moveGates k) hin (CircuitTapeMove.moveGates_valid k)
    (CircuitTapeMove.outputIndex k i) hout
  change wire (simulate mid (relocate (CircuitTapeMove.width k) mid.length (tapeRefs p k base)
      (CircuitTapeMove.moveGates k)))
      (remap (CircuitTapeMove.width k) mid.length (tapeRefs p k base) (CircuitTapeMove.outputIndex k i)) =
    wire (simulate (readState mid (CircuitTapeMove.width k) (tapeRefs p k base))
      (CircuitTapeMove.moveGates k)) (CircuitTapeMove.outputIndex k i) at he
  rw [connectedTapeInput p k c row hrow] at he
  rw [CircuitTapeMove.move_correct k row.1 (!row.2.1) c.2 i hi hl hr] at he
  rw [hm] at he
  simpa [programMoveGates,programMoveOutput,simulate_append,mid,wires,base] using he

/-- For a continuing row, this circuit computes the tape of the actual
`FinitePrograms.step` transition. The next-state one-hot vector is not yet
part of the circuit output. -/
theorem programMove_continuing (p : Program) (k : Nat) (c : Config) (row : Row)
    (hrow : rowAt p c = some row) (htag : row.2.2.2 = 0)
    (hl : c.2.1.length ≤ k) (hr : c.2.2.2.length ≤ k) :
    step p c = some (.inr (row.2.2.1,moveTape (!row.2.1) row.1 c.2)) ∧
    ∀ i < 2*k+1,
      wire (simulate (machineWires p k c) (programMoveGates p k (inputWidth p k)))
        (programMoveOutput p k (inputWidth p k) i) =
      CircuitTapeMove.tapeView k (moveTape (!row.2.1) row.1 c.2) i := by
  constructor
  · rw [step_eq_executeRow p c row hrow]
    simp [executeRow,htag]
  · intro i hi
    exact programMove_correct p k c row hrow i hi hl hr

def rowNextIs (q : Nat) (row : Row) : Bool := decide (row.2.2.1 = q)

def stateGates (p : Program) (read : Nat) : Nat → Nat → Nat → List Gate
  | _, _, 0 => []
  | base, start, count+1 =>
    tableBlock p read (rowNextIs start) base ++
      stateGates p read (base+(2+4*p.length)) (start+1) count

def stateResult (p : Program) (read base start j : Nat) : Nat :=
  tableResult p read (rowNextIs (start+j)) (base+j*(2+4*p.length))

theorem stateGates_length (p : Program) (read base start count : Nat) :
    (stateGates p read base start count).length = count*(2+4*p.length) := by
  induction count generalizing base start with
  | zero => simp [stateGates]
  | succ count ih =>
    simp only [stateGates,List.length_append,tableBlock_length,ih,Nat.succ_mul]
    omega

theorem stateGates_valid (p : Program) (read base start count : Nat)
    (hn : p.length ≤ base) (hr : read < base) : validGates base (stateGates p read base start count) := by
  induction count generalizing base start with
  | zero => trivial
  | succ count ih =>
    simp only [stateGates,validGates_append,tableBlock_length]
    exact ⟨tableBlock_valid p read (rowNextIs start) base hn hr,
      ih (base+(2+4*p.length)) (start+1) (by omega) (by omega)⟩

theorem stateResult_bound (p : Program) (read base start count j : Nat)
    (hn : p.length ≤ base) (hr : read < base) (hj : j < count) :
    stateResult p read base start j < base+(stateGates p read base start count).length := by
  have hh := tableResult_bound p read (rowNextIs (start+j)) (base+j*(2+4*p.length))
    (by omega) (by omega)
  simp only [tableBlock_length] at hh
  simp only [stateResult,stateGates_length]
  have hm := Nat.mul_le_mul_right (2+4*p.length) (show j+1 ≤ count by omega)
  rw [Nat.add_mul] at hm
  omega

/-- Each generated output is one bit of the selected row's next-state code. -/
theorem stateGates_simulate (p : Program) (read : Nat) (wires : List Bool)
    (start count j : Nat) (hj : j < count) (c : Config) (row : Row)
    (hrow : rowAt p c = some row) (hn : p.length ≤ wires.length) (hr : read < wires.length)
    (hstate : ∀ q, q < p.length → wire wires q = decide (q = c.1))
    (hread : wire wires read = c.2.2.1) :
    wire (simulate wires (stateGates p read wires.length start count))
      (stateResult p read wires.length start j) = decide (row.2.2.1 = start+j) := by
  induction count generalizing wires start j with
  | zero => omega
  | succ count ih =>
    let first := tableBlock p read (rowNextIs start) wires.length
    let mid := simulate wires first
    have hm : mid.length = wires.length+(2+4*p.length) := by simp [mid,simulate_length,first,tableBlock_length]
    have keep (i : Nat) (hi : i < wires.length) : wire mid i = wire wires i := wire_simulate wires first i hi
    have hs : ∀ q, q < p.length → wire mid q = decide (q = c.1) := by
      intro q hq
      rw [keep q (by omega)]
      exact hstate q hq
    have hread' : wire mid read = c.2.2.1 := by rw [keep read hr]; exact hread
    have hfirst := tableBlock_simulate p read (rowNextIs start) wires c row hrow hn hr hstate hread
    simp only [stateGates,simulate_append,tableBlock_length]
    change wire (simulate mid (stateGates p read (wires.length+(2+4*p.length)) (start+1) count)) _ = _
    cases j with
    | zero =>
      have hbound := tableResult_bound p read (rowNextIs start) wires.length hn hr
      have hsimp : stateResult p read wires.length start 0 = tableResult p read (rowNextIs start) wires.length := by
        simp [stateResult]
      rw [hsimp,wire_simulate mid _ _ (by rw [hm]; simpa [first,tableBlock_length] using hbound)]
      simpa [rowNextIs] using hfirst
    | succ j =>
      have hh := ih mid (start+1) j (by omega) (by rw [hm]; omega)
        (by rw [hm]; omega) hs hread'
      rw [hm] at hh
      have he : stateResult p read wires.length start (j+1) =
          stateResult p read (wires.length+(2+4*p.length)) (start+1) j := by
        simp [stateResult,Nat.add_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      rw [he,hh]
      simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem programMoveOutput_bound (p : Program) (k base i : Nat)
    (hb : inputWidth p k ≤ base) (hi : i < 2*k+1) :
    programMoveOutput p k base i < base+(programMoveGates p k base).length := by
  have hbound : CircuitTapeMove.outputIndex k i <
      CircuitTapeMove.width k+(CircuitTapeMove.moveGates k).length := by
    simp only [CircuitTapeMove.outputIndex,CircuitTapeMove.moveGates_length]
    omega
  have h := remap_bound (CircuitTapeMove.width k) (base+(controls p k base).length)
    (tapeRefs p k base) (tapeRefs_bound p k base hb) (CircuitTapeMove.moveGates k).length
    (CircuitTapeMove.outputIndex k i) hbound
  simpa [programMoveOutput,programMoveGates,relocate_length,Nat.add_assoc] using h

/-- Extend the tape circuit with one output bit for each possible next state. -/
def continuingGates (p : Program) (k base : Nat) : List Gate :=
  programMoveGates p k base ++
    stateGates p (readIndex p k) (base+(programMoveGates p k base).length) 0 p.length

def nextStateOutput (p : Program) (k base j : Nat) : Nat :=
  stateResult p (readIndex p k) (base+(programMoveGates p k base).length) 0 j

theorem continuingGates_length (p : Program) (k base : Nat) :
    (continuingGates p k base).length =
      (2*(2+4*p.length)+(1+4*(2*k+1))) + p.length*(2+4*p.length) := by
  simp [continuingGates,programMoveGates_length,stateGates_length]

theorem continuingGates_valid (p : Program) (k base : Nat) (hb : inputWidth p k ≤ base) :
    validGates base (continuingGates p k base) := by
  simp only [continuingGates,validGates_append]
  refine ⟨programMoveGates_valid p k base hb,?_⟩
  apply stateGates_valid
  · simp only [inputWidth] at hb; omega
  · simp only [readIndex,inputWidth] at *; omega

/-- The combined continuing-row circuit computes both the new one-hot state
bits and the bounded tape of the shared finite-program transition. -/
theorem continuingGates_correct (p : Program) (k : Nat) (c : Config) (row : Row)
    (hrow : rowAt p c = some row) (htag : row.2.2.2 = 0)
    (hl : c.2.1.length ≤ k) (hr : c.2.2.2.length ≤ k) :
    step p c = some (.inr (row.2.2.1,moveTape (!row.2.1) row.1 c.2)) ∧
    (∀ j < p.length,
      wire (simulate (machineWires p k c) (continuingGates p k (inputWidth p k)))
        (nextStateOutput p k (inputWidth p k) j) = decide (row.2.2.1 = j)) ∧
    (∀ i < 2*k+1,
      wire (simulate (machineWires p k c) (continuingGates p k (inputWidth p k)))
        (programMoveOutput p k (inputWidth p k) i) =
      CircuitTapeMove.tapeView k (moveTape (!row.2.1) row.1 c.2) i) := by
  let wires := machineWires p k c
  let base := inputWidth p k
  let first := programMoveGates p k base
  let mid := simulate wires first
  have hw : wires.length = base := machineWires_length p k c
  have hm : mid.length = base+first.length := by simp [mid,simulate_length,hw]
  have keep (i : Nat) (hi : i < wires.length) : wire mid i = wire wires i := wire_simulate wires first i hi
  have hs : ∀ q, q < p.length → wire mid q = decide (q = c.1) := by
    intro q hq
    rw [keep q (by rw [hw]; simp [base,inputWidth]; omega)]
    exact machineWires_state p k c q hq
  have hread : wire mid (readIndex p k) = c.2.2.1 := by
    rw [keep _ (by rw [hw]; simp [base,inputWidth,readIndex]; omega)]
    exact machineWires_read p k c
  have hstep := programMove_continuing p k c row hrow htag hl hr
  refine ⟨hstep.1,?_,?_⟩
  · intro j hj
    have h := stateGates_simulate p (readIndex p k) mid 0 p.length j hj c row hrow
      (by rw [hm]; simp [base,inputWidth]; omega)
      (by rw [hm]; simp [base,inputWidth,readIndex]; omega) hs hread
    rw [hm] at h
    simpa [continuingGates,nextStateOutput,simulate_append,mid,wires,base] using h
  · intro i hi
    have hbound := programMoveOutput_bound p k base i le_rfl hi
    have hkeep := wire_simulate mid
      (stateGates p (readIndex p k) (base+first.length) 0 p.length)
      (programMoveOutput p k base i) (by rw [hm]; exact hbound)
    have ht := hstep.2 i hi
    change wire mid (programMoveOutput p k base i) = _ at ht
    have he := hkeep.trans ht
    simpa [continuingGates,simulate_append,mid,wires,base,first] using he

/-- Output layout is the same one-hot-state/tape layout as the next input. -/
def continuingOutputs (p : Program) (k base : Nat) : List Nat :=
  (List.range p.length).map (nextStateOutput p k base) ++
    (List.range (2*k+1)).map (programMoveOutput p k base)

theorem continuingOutputs_length (p : Program) (k base : Nat) :
    (continuingOutputs p k base).length = inputWidth p k := by
  simp [continuingOutputs,inputWidth]

theorem continuingOutputs_state (p : Program) (k base j : Nat) (hj : j < p.length) :
    ((continuingOutputs p k base)[j]?).getD 0 = nextStateOutput p k base j := by
  simp [continuingOutputs,List.getElem?_append_left,hj]

theorem continuingOutputs_tape (p : Program) (k base i : Nat) (hi : i < 2*k+1) :
    ((continuingOutputs p k base)[p.length+i]?).getD 0 = programMoveOutput p k base i := by
  simp [continuingOutputs,List.getElem?_append_right,hi]

theorem continuingOutputs_bound (p : Program) (k base : Nat) (hb : inputWidth p k ≤ base) :
    ∀ o ∈ continuingOutputs p k base, o < base+(continuingGates p k base).length := by
  intro o ho
  simp only [continuingOutputs,List.mem_append,List.mem_map,List.mem_range] at ho
  rcases ho with ⟨j,hj,rfl⟩ | ⟨i,hi,rfl⟩
  · have h := stateResult_bound p (readIndex p k) (base+(programMoveGates p k base).length)
      0 p.length j (by simp only [inputWidth] at hb; omega)
      (by simp only [readIndex,inputWidth] at *; omega) hj
    simpa [nextStateOutput,continuingGates,Nat.add_assoc] using h
  · have h := programMoveOutput_bound p k base i hb hi
    simp only [continuingGates,List.length_append]
    omega

theorem stepState_wire (gates : List Gate) (outs : List Nat) (wires : List Bool)
    (i : Nat) (hi : i < outs.length) :
    wire (stepState gates outs wires) i = wire (simulate wires gates) ((outs[i]?).getD 0) := by
  simp [stepState,wire,hi]

/-- A continuing program step produces precisely the next input encoding. -/
theorem continuing_stepState (p : Program) (k : Nat) (c : Config) (row : Row)
    (hrow : rowAt p c = some row) (htag : row.2.2.2 = 0)
    (hl : c.2.1.length ≤ k) (hr : c.2.2.2.length ≤ k) :
    stepState (continuingGates p k (inputWidth p k))
        (continuingOutputs p k (inputWidth p k)) (machineWires p k c) =
    machineWires p k (row.2.2.1,moveTape (!row.2.1) row.1 c.2) := by
  have hc := continuingGates_correct p k c row hrow htag hl hr
  apply List.ext_getElem
  · simp [stepState,continuingOutputs_length,machineWires_length]
  · intro i hi₁ hi₂
    have ho : i < (continuingOutputs p k (inputWidth p k)).length := by simpa [stepState] using hi₁
    rw [←wire_get _ i hi₁,stepState_wire _ _ _ i ho,←wire_get _ i hi₂]
    by_cases hs : i < p.length
    · rw [continuingOutputs_state p k (inputWidth p k) i hs,hc.2.1 i hs]
      rw [machineWires_state p k _ i hs]
      simp [eq_comm]
    · have hwidth : i < inputWidth p k := by simpa [machineWires_length] using hi₂
      let j := i-p.length
      have hj : j < 2*k+1 := by dsimp [j]; simp only [inputWidth] at hwidth; omega
      have he : p.length+j = i := by dsimp [j]; omega
      rw [←he,continuingOutputs_tape p k (inputWidth p k) j hj,hc.2.2 j hj]
      rw [machineWires_tape p k _ j hj]

/-- A finite sequence of continuing transitions, with a checked tape-window
bound at every source configuration. Terminal and invalid rows are excluded. -/
def ContinuingTrace (p : Program) (k : Nat) : Nat → Config → Config → Prop
  | 0, c, d => d = c
  | n+1, c, d => ∃ row : Row,
      rowAt p c = some row ∧ row.2.2.2 = 0 ∧
      c.2.1.length ≤ k ∧ c.2.2.2.length ≤ k ∧
      ContinuingTrace p k n (row.2.2.1,moveTape (!row.2.1) row.1 c.2) d

theorem run_after_first (p : Program) (c d : Config) (n : Nat)
    (hstep : step p c = some (.inr d)) : run p c (n+1) = run p d n := by
  induction n with
  | zero => simp [run,advance,hstep]
  | succ n ih =>
    change advance p (run p c (n+1)) = advance p (run p d n)
    rw [ih]

/-- The trace assumption refers to the evaluator's actual bounded run. -/
theorem continuingTrace_run (p : Program) (k n : Nat) (c d : Config)
    (h : ContinuingTrace p k n c d) : run p c n = some (.inr d) := by
  induction n generalizing c with
  | zero => simp only [ContinuingTrace] at h; subst d; rfl
  | succ n ih =>
    obtain ⟨row,hrow,htag,hl,hr,htail⟩ := h
    have hs := (continuingGates_correct p k c row hrow htag hl hr).1
    rw [run_after_first p c _ n hs]
    exact ih _ htail

/-- The repeated concrete circuit computes exactly the same continuing trace. -/
theorem continuingTrace_runState (p : Program) (k n : Nat) (c d : Config)
    (h : ContinuingTrace p k n c d) :
    runState (continuingGates p k (inputWidth p k))
      (continuingOutputs p k (inputWidth p k)) n (machineWires p k c) = machineWires p k d := by
  induction n generalizing c with
  | zero => simp only [ContinuingTrace] at h; subst d; rfl
  | succ n ih =>
    obtain ⟨row,hrow,htag,hl,hr,htail⟩ := h
    simp only [runState]
    rw [continuing_stepState p k c row hrow htag hl hr]
    exact ih _ htail

/-- The unrolled gate list implements every such bounded continuing run. -/
theorem continuingTrace_unroll (p : Program) (k n : Nat) (c d : Config)
    (h : ContinuingTrace p k n c d) :
    readState
      (simulate (machineWires p k c)
        (unroll (inputWidth p k) (continuingGates p k (inputWidth p k))
          (continuingOutputs p k (inputWidth p k)) (inputWidth p k) (List.range (inputWidth p k)) n))
      (inputWidth p k)
      (finalRefs (inputWidth p k) (continuingGates p k (inputWidth p k))
        (continuingOutputs p k (inputWidth p k)) (inputWidth p k) (List.range (inputWidth p k)) n) =
      machineWires p k d := by
  have hw := machineWires_length p k c
  have hin : ∀ i < inputWidth p k, ((List.range (inputWidth p k))[i]?).getD 0 < (machineWires p k c).length := by
    intro i hi
    simp [hi,hw]
  have he := unroll_readState (machineWires p k c) (inputWidth p k) (List.range (inputWidth p k))
    (continuingOutputs p k (inputWidth p k)) (continuingGates p k (inputWidth p k)) hin
    (continuingGates_valid p k (inputWidth p k) le_rfl)
    (continuingOutputs_length p k (inputWidth p k))
    (continuingOutputs_bound p k (inputWidth p k) le_rfl) n
  rw [hw,CircuitTapeMove.readState_identity _ _ hw,continuingTrace_runState p k n c d h] at he
  exact he

theorem run_after_invalid (p : Program) (c : Config) (n : Nat) (h : step p c = none) :
    run p c (n+1) = none := by
  induction n with
  | zero => simp [run,advance,h]
  | succ n ih =>
    change advance p (run p c (n+1)) = none
    rw [ih]
    rfl

theorem run_after_result (p : Program) (c : Config) (n : Nat) (b : Bool)
    (h : step p c = some (.inl b)) : run p c (n+1) = some (.inl b) := by
  induction n with
  | zero => simp [run,advance,h]
  | succ n ih =>
    change advance p (run p c (n+1)) = some (.inl b)
    rw [ih]
    rfl

/-- A bounded run ending in a live configuration cannot have passed through
an invalid or terminal result. One extra window cell per step suffices. -/
theorem continuingTrace_of_run (p : Program) (k n : Nat) (c d : Config)
    (h : run p c n = some (.inr d))
    (hl : c.2.1.length+n ≤ k) (hr : c.2.2.2.length+n ≤ k) :
    ContinuingTrace p k n c d := by
  induction n generalizing c with
  | zero =>
    simp only [run_zero,Option.some.injEq,Sum.inr.injEq] at h
    simp [ContinuingTrace,h]
  | succ n ih =>
    cases hs : step p c with
    | none =>
      have hx := run_after_invalid p c n hs
      rw [hx] at h
      contradiction
    | some result =>
      cases result with
      | inl b =>
        have hx := run_after_result p c n b hs
        rw [hx] at h
        cases h
      | inr c1 =>
        have ht : run p c1 n = some (.inr d) := by
          rw [← run_after_first p c c1 n hs]
          exact h
        cases hp : p[c.1]? with
        | none => simp [step,hp] at hs
        | some pair =>
          let row : Row := if c.2.2.1 then pair.2 else pair.1
          have hrow : rowAt p c = some row := by simp [rowAt,hp,row]
          have hex := step_eq_executeRow p c row hrow
          rw [hex] at hs
          have htag : row.2.2.2 = 0 := by
            cases hv : row.2.2.2 with
            | zero => rfl
            | succ t =>
              cases t with
              | zero => simp [executeRow,hv] at hs
              | succ t =>
                cases t with
                | zero => simp [executeRow,hv] at hs
                | succ t => simp [executeRow,hv] at hs
          have hc1 : (row.2.2.1,moveTape (!row.2.1) row.1 c.2) = c1 := by
            simpa [executeRow,htag] using hs
          subst c1
          have hm := CircuitTapeMove.moveTape_lengths row.1 (!row.2.1) c.2
          refine ⟨row,hrow,htag,by omega,by omega,?_⟩
          apply ih _ ht <;> simp only [Prod.fst,Prod.snd] <;> omega

/-- The circuit covers every bounded live run once the finite tape window has
the explicit input-length-plus-time slack. -/
theorem unroll_of_live_run (p : Program) (k n : Nat) (c d : Config)
    (h : run p c n = some (.inr d))
    (hl : c.2.1.length+n ≤ k) (hr : c.2.2.2.length+n ≤ k) :
    readState
      (simulate (machineWires p k c)
        (unroll (inputWidth p k) (continuingGates p k (inputWidth p k))
          (continuingOutputs p k (inputWidth p k)) (inputWidth p k) (List.range (inputWidth p k)) n))
      (inputWidth p k)
      (finalRefs (inputWidth p k) (continuingGates p k (inputWidth p k))
        (continuingOutputs p k (inputWidth p k)) (inputWidth p k) (List.range (inputWidth p k)) n) =
      machineWires p k d :=
  continuingTrace_unroll p k n c d (continuingTrace_of_run p k n c d h hl hr)

theorem continuingTrace_unroll_length (p : Program) (k n : Nat) :
    (unroll (inputWidth p k) (continuingGates p k (inputWidth p k))
      (continuingOutputs p k (inputWidth p k)) (inputWidth p k) (List.range (inputWidth p k)) n).length =
    n*((2*(2+4*p.length)+(1+4*(2*k+1))) + p.length*(2+4*p.length)) := by
  rw [unroll_length,continuingGates_length]

namespace Fixtures

def twoState : Program :=
  [((true,true,1,0),(true,true,1,0)), ((false,false,0,0),(false,false,0,0))]
def start : Config := (0,[],false,[])
def finish : Config := (0,[],true,[false])

theorem twoState_run : run twoState start 2 = some (.inr finish) := by decide

/-- Two steps change both the control state and movement direction. -/
example :
    readState
      (simulate (machineWires twoState 2 start)
        (unroll (inputWidth twoState 2) (continuingGates twoState 2 (inputWidth twoState 2))
          (continuingOutputs twoState 2 (inputWidth twoState 2))
          (inputWidth twoState 2) (List.range (inputWidth twoState 2)) 2))
      (inputWidth twoState 2)
      (finalRefs (inputWidth twoState 2) (continuingGates twoState 2 (inputWidth twoState 2))
        (continuingOutputs twoState 2 (inputWidth twoState 2))
        (inputWidth twoState 2) (List.range (inputWidth twoState 2)) 2) =
      machineWires twoState 2 finish := by
  apply unroll_of_live_run twoState 2 2 start finish twoState_run <;> decide

example : run [((false,false,0,1),(false,false,0,1))] start 2 = some (.inl false) := by decide
example : run [] start 2 = none := by decide
end Fixtures

end Shared.ComplexityBridge.CircuitProgramMove
