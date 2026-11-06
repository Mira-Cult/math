import Shared.ComplexityBridge.CircuitRelocate
import Shared.Codes.FinitePrograms

/-! An explicit circuit for selecting a Boolean field of a finite binary
machine's transition table. State wires are one-hot and the symbol wire is
binary. This is one part of a future complete transition circuit. -/
namespace Shared.ComplexityBridge.CircuitTable
open Shared.ComplexityBridge.CNF
open Shared.ComplexityBridge.CircuitCNF
open Shared.ComplexityBridge.CircuitSelect
open Shared.ComplexityBridge.CircuitRelocate
open Shared.Codes.FinitePrograms

/-- Four gates add one state's selected row bit to an accumulator. -/
def rowGates (base q read negRead acc : Nat) (row : Bool × Bool) : List Gate :=
  [if row.1 then .conj q negRead else .constant false,
   if row.2 then .conj q read else .constant false,
   .disj base (base+1), .disj acc (base+2)]

theorem rowGates_length (base q read negRead acc : Nat) (row : Bool × Bool) :
    (rowGates base q read negRead acc row).length = 4 := by cases row <;> rfl

theorem rowGates_valid (base q read negRead acc : Nat) (row : Bool × Bool)
    (hq : q < base) (hr : read < base) (hn : negRead < base) (ha : acc < base) :
    validGates base (rowGates base q read negRead acc row) := by
  rcases row with ⟨f,t⟩
  cases f <;> cases t <;> simp [rowGates,validGates,validGate] <;> omega

theorem rowGates_equations (a : Valuation) (base q read negRead acc : Nat) (row : Bool × Bool)
    (hneg : a negRead = !a read) (h : Equations a base (rowGates base q read negRead acc row)) :
    a (base+3) = (a acc || (a q && (if a read then row.2 else row.1))) := by
  rcases row with ⟨f,t⟩
  cases f <;> cases t
  all_goals simp only [rowGates,Equations,evalGate, Bool.false_eq_true, if_false, if_true] at h
  all_goals obtain ⟨h0,h1,h2,h3,_⟩ := h
  all_goals have h2' : a (base+2) = (a base || a (base+1)) := by simpa [Nat.add_assoc] using h2
  all_goals have h3' : a (base+3) = (a acc || a (base+2)) := by simpa [Nat.add_assoc] using h3
  all_goals rw [h3',h2',h0,h1]
  all_goals simp only [hneg]
  all_goals cases hq : a q <;> cases hr : a read <;> cases ha : a acc <;> simp [hq,hr,ha]

theorem rowGates_simulate (wires : List Bool) (q read negRead acc : Nat) (row : Bool × Bool)
    (hq : q < wires.length) (hr : read < wires.length) (hn : negRead < wires.length)
    (ha : acc < wires.length) (hneg : wire wires negRead = !wire wires read) :
    wire (simulate wires (rowGates wires.length q read negRead acc row)) (wires.length+3) =
      (wire wires acc || (wire wires q && (if wire wires read then row.2 else row.1))) := by
  let final := simulate wires (rowGates wires.length q read negRead acc row)
  have hv := rowGates_valid wires.length q read negRead acc row hq hr hn ha
  have hkeep (i : Nat) (hi : i < wires.length) : wire final i = wire wires i :=
    wire_simulate wires _ i hi
  have hne : wire final negRead = !wire final read := by rw [hkeep negRead hn,hkeep read hr]; exact hneg
  have he := rowGates_equations (wire final) wires.length q read negRead acc row hne
    (simulate_equations wires _ hv)
  rw [he,hkeep acc ha,hkeep q hq,hkeep read hr]

/-- List-fold semantics of the one-hot table selector. -/
def evalRows (a : Nat → Bool) (read : Bool) : Nat → List (Bool × Bool) → Bool → Bool
  | _, [], acc => acc
  | q, row::rows, acc =>
      evalRows a read (q+1) rows (acc || (a q && (if read then row.2 else row.1)))

theorem evalRows_congr (a b : Nat → Bool) (read : Bool) (q : Nat) (rows : List (Bool × Bool))
    (acc : Bool) (h : ∀ i, q ≤ i → i < q+rows.length → a i = b i) :
    evalRows a read q rows acc = evalRows b read q rows acc := by
  induction rows generalizing q acc with
  | nil => rfl
  | cons row rows ih =>
    simp only [evalRows]
    rw [h q (by omega) (by simp)]
    apply ih
    intro i hi hj
    apply h i (by omega)
    simp only [List.length_cons]
    omega

/-- The accumulator output index is explicit even for an empty table. -/
def rowOutput (base acc : Nat) : List (Bool × Bool) → Nat
  | [] => acc
  | _::rows => rowOutput (base+4) (base+3) rows

def rowsGates (base q read negRead acc : Nat) : List (Bool × Bool) → List Gate
  | [] => []
  | row::rows => rowGates base q read negRead acc row ++
      rowsGates (base+4) (q+1) read negRead (base+3) rows

theorem rowsGates_length (base q read negRead acc : Nat) (rows : List (Bool × Bool)) :
    (rowsGates base q read negRead acc rows).length = 4*rows.length := by
  induction rows generalizing base q acc with
  | nil => rfl
  | cons row rows ih => simp [rowsGates,rowGates_length,ih]; omega

theorem rowOutput_bound (base acc : Nat) (rows : List (Bool × Bool)) (ha : acc < base) :
    rowOutput base acc rows < base+4*rows.length := by
  induction rows generalizing base acc with
  | nil => simpa [rowOutput] using ha
  | cons row rows ih =>
    have h := ih (base+4) (base+3) (by omega)
    simp only [rowOutput,List.length_cons] at *
    omega

theorem rowsGates_valid (base q read negRead acc : Nat) (rows : List (Bool × Bool))
    (hq : q+rows.length ≤ base) (hr : read < base) (hn : negRead < base) (ha : acc < base) :
    validGates base (rowsGates base q read negRead acc rows) := by
  induction rows generalizing base q acc with
  | nil => trivial
  | cons row rows ih =>
    simp only [rowsGates,validGates_append,rowGates_length]
    refine ⟨rowGates_valid base q read negRead acc row (by simp only [List.length_cons] at hq; omega) hr hn ha,?_⟩
    apply ih (base+4) (q+1) (base+3) <;> simp only [List.length_cons] at hq <;> omega

/-- The row circuit computes the table fold, preserving its original input wires. -/
theorem rowsGates_simulate (wires : List Bool) (q read negRead acc : Nat) (rows : List (Bool × Bool))
    (hq : q+rows.length ≤ wires.length) (hr : read < wires.length)
    (hn : negRead < wires.length) (ha : acc < wires.length)
    (hneg : wire wires negRead = !wire wires read) :
    wire (simulate wires (rowsGates wires.length q read negRead acc rows))
        (rowOutput wires.length acc rows) =
      evalRows (wire wires) (wire wires read) q rows (wire wires acc) := by
  induction rows generalizing wires q acc with
  | nil => rfl
  | cons row rows ih =>
    let mid := simulate wires (rowGates wires.length q read negRead acc row)
    have hm : mid.length = wires.length+4 := by simp [mid,simulate_length,rowGates_length]
    have hq0 : q < wires.length := by simp only [List.length_cons] at hq; omega
    have hkeep (i : Nat) (hi : i < wires.length) : wire mid i = wire wires i := wire_simulate wires _ i hi
    have hneg' : wire mid negRead = !wire mid read := by rw [hkeep negRead hn,hkeep read hr]; exact hneg
    have hout := rowGates_simulate wires q read negRead acc row hq0 hr hn ha hneg
    have hh := ih mid (q+1) (wires.length+3) (by rw [hm]; simp only [List.length_cons] at hq; omega)
      (by rw [hm]; omega) (by rw [hm]; omega) (by rw [hm]; omega) hneg'
    rw [hm] at hh
    simp only [rowsGates,simulate_append,rowOutput,evalRows]
    change wire (simulate mid (rowsGates (wires.length+4) (q+1) read negRead (wires.length+3) rows)) _ = _
    rw [hh,hout,hkeep read hr]
    apply evalRows_congr
    intro i hi hj
    apply hkeep i
    simp only [List.length_cons] at hq
    omega

/-- If all remaining state bits are zero, no row changes the accumulator. -/
theorem evalRows_allFalse (a : Nat → Bool) (read : Bool) (q : Nat) (rows : List (Bool × Bool))
    (acc : Bool) (h : ∀ j, j < rows.length → a (q+j) = false) : evalRows a read q rows acc = acc := by
  induction rows generalizing q acc with
  | nil => rfl
  | cons row rows ih =>
    simp only [evalRows]
    have hq : a q = false := by simpa using h 0 (by simp)
    rw [hq]
    simp only [Bool.false_and,Bool.or_false]
    apply ih
    intro j hj
    have hh := h (j+1) (by simp only [List.length_cons]; omega)
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- One-hot state inputs select exactly the indexed row, even when the initial
accumulator is already true. -/
theorem evalRows_oneHot (a : Nat → Bool) (read : Bool) (q k : Nat) (rows : List (Bool × Bool))
    (acc : Bool) (row : Bool × Bool) (hrow : rows[k]? = some row)
    (hstate : ∀ j, j < rows.length → a (q+j) = decide (j = k)) :
    evalRows a read q rows acc = (acc || (if read then row.2 else row.1)) := by
  induction rows generalizing q k acc with
  | nil => simp at hrow
  | cons r rs ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at hrow
      subst r
      have hq : a q = true := by simpa using hstate 0 (by simp)
      have htail : ∀ j, j < rs.length → a (q+1+j) = false := by
        intro j hj
        have h := hstate (j+1) (by simp only [List.length_cons]; omega)
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
      simp only [evalRows,hq,Bool.true_and]
      exact evalRows_allFalse a read (q+1) rs _ htail
    | succ k =>
      simp only [List.getElem?_cons_succ] at hrow
      have hq : a q = false := by simpa using hstate 0 (by simp)
      have htail : ∀ j, j < rs.length → a (q+1+j) = decide (j = k) := by
        intro j hj
        have h := hstate (j+1) (by simp only [List.length_cons]; omega)
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
      simp only [evalRows,hq,Bool.false_and,Bool.or_false]
      exact ih (q+1) k acc hrow htail

/-- State wires occupy positions `0..n-1`, and the symbol wire is `n`. -/
def lookupGates (n : Nat) (rows : List (Bool × Bool)) : List Gate :=
  [.neg n,.constant false] ++ rowsGates (n+3) 0 n (n+1) (n+2) rows

def lookupOutput (n : Nat) (rows : List (Bool × Bool)) : Nat :=
  rowOutput (n+3) (n+2) rows

theorem lookupGates_length (n : Nat) (rows : List (Bool × Bool)) :
    (lookupGates n rows).length = 2+4*rows.length := by simp [lookupGates,rowsGates_length]; omega

theorem lookup_valid (n : Nat) (rows : List (Bool × Bool)) (hlen : rows.length = n) :
    validGates (n+1) (lookupGates n rows) := by
  simp only [lookupGates,validGates_append,List.length_cons,List.length_nil]
  constructor
  · simp [validGates,validGate]
  · apply rowsGates_valid <;> omega

theorem lookupOutput_bound (n : Nat) (rows : List (Bool × Bool)) :
    lookupOutput n rows < n+1+(lookupGates n rows).length := by
  have h := rowOutput_bound (n+3) (n+2) rows (by omega)
  simp only [lookupOutput,lookupGates_length]
  omega

/-- The finite gate list computes its declared table-fold semantics. -/
theorem lookup_simulate (wires : List Bool) (n : Nat) (rows : List (Bool × Bool))
    (hw : wires.length = n+1) (hlen : rows.length = n) :
    wire (simulate wires (lookupGates n rows)) (lookupOutput n rows) =
      evalRows (wire wires) (wire wires n) 0 rows false := by
  let prep : List Gate := [.neg n,.constant false]
  let mid := simulate wires prep
  have hv : validGates wires.length prep := by
    simp [prep,validGates,validGate,hw]
  have he := simulate_equations wires prep hv
  simp only [prep,Equations,evalGate] at he
  have keep (i : Nat) (hi : i < wires.length) : wire mid i = wire wires i :=
    wire_simulate wires prep i hi
  have hm : mid.length = n+3 := by simp [mid,prep,simulate_length,hw]
  have hn : wire mid (n+1) = !wire mid n := by simpa [mid,hw] using he.1
  have ha : wire mid (n+2) = false := by simpa [mid,hw] using he.2.1
  have hr : wire mid n = wire wires n := keep n (by rw [hw]; omega)
  have hc := rowsGates_simulate mid 0 n (n+1) (n+2) rows
    (by rw [hm,hlen]; omega) (by rw [hm]; omega) (by rw [hm]; omega) (by rw [hm]; omega) hn
  rw [hm,ha,hr] at hc
  simp only [lookupGates,lookupOutput,simulate_append]
  change wire (simulate mid (rowsGates (n+3) 0 n (n+1) (n+2) rows)) (rowOutput (n+3) (n+2) rows) = _
  rw [hc]
  apply evalRows_congr
  intro i _ hi
  apply keep i
  rw [hw,hlen] at *
  omega

/-- Extract a Boolean field from both rows of each finite program state. -/
def projectRows (project : Row → Bool) (p : Program) : List (Bool × Bool) :=
  p.map fun rows => (project rows.1, project rows.2)

/-- Under the one-hot state convention, the circuit implements the actual
finite-program table lookup for any Boolean projection of a row. -/
theorem lookup_program_row (p : Program) (project : Row → Bool) (wires : List Bool)
    (q : Nat) (lo hi : Row) (hrow : p[q]? = some (lo,hi))
    (hw : wires.length = p.length+1)
    (hstate : ∀ j, j < p.length → wire wires j = decide (j = q)) :
    wire (simulate wires (lookupGates p.length (projectRows project p)))
      (lookupOutput p.length (projectRows project p)) =
      project (if wire wires p.length then hi else lo) := by
  have hlen : (projectRows project p).length = p.length := by simp [projectRows]
  rw [lookup_simulate wires p.length _ hw hlen]
  have hproj : (projectRows project p)[q]? = some (project lo,project hi) := by
    simp [projectRows,List.getElem?_map,hrow]
  have hs : ∀ j, j < (projectRows project p).length → wire wires (0+j) = decide (j = q) := by
    simpa [hlen] using hstate
  have h := evalRows_oneHot (wire wires) (wire wires p.length) 0 q
    (projectRows project p) false (project lo,project hi) hproj hs
  cases hb : wire wires p.length <;> simpa [hb] using h

/-- The same result stated directly against the shared bounded evaluator's
`rowAt` operation. -/
theorem lookup_rowAt (p : Program) (project : Row → Bool) (c : Config) (row : Row)
    (wires : List Bool) (hrow : rowAt p c = some row)
    (hw : wires.length = p.length+1)
    (hstate : ∀ j, j < p.length → wire wires j = decide (j = c.1))
    (hread : wire wires p.length = c.2.2.1) :
    wire (simulate wires (lookupGates p.length (projectRows project p)))
      (lookupOutput p.length (projectRows project p)) = project row := by
  cases hp : p[c.1]? with
  | none => simp [rowAt,hp] at hrow
  | some pair =>
    rcases pair with ⟨lo,hi⟩
    cases hb : c.2.2.1 with
    | false =>
      have hr : lo = row := by simpa [rowAt,hp,hb] using hrow
      rw [← hr]
      have hh := lookup_program_row p project wires c.1 lo hi hp hw hstate
      simpa [hread,hb] using hh
    | true =>
      have hr : hi = row := by simpa [rowAt,hp,hb] using hrow
      rw [← hr]
      have hh := lookup_program_row p project wires c.1 lo hi hp hw hstate
      simpa [hread,hb] using hh

/-- The row selected by `rowAt` is exactly the row executed by `step`. -/
theorem step_eq_executeRow (p : Program) (c : Config) (row : Row)
    (hrow : rowAt p c = some row) : step p c = executeRow row c.2 := by
  cases hp : p[c.1]? with
  | none => simp [rowAt,hp] at hrow
  | some pair =>
    have hr : (if c.2.2.1 then pair.2 else pair.1) = row := by
      simpa [rowAt,hp] using hrow
    simp only [step,hp]
    rw [hr]
    rfl

/-- The circuit output identifies a field of the row actually executed by the
shared finite-program transition. -/
theorem lookup_step (p : Program) (project : Row → Bool) (c : Config) (row : Row)
    (wires : List Bool) (hrow : rowAt p c = some row)
    (hw : wires.length = p.length+1)
    (hstate : ∀ j, j < p.length → wire wires j = decide (j = c.1))
    (hread : wire wires p.length = c.2.2.1) :
    wire (simulate wires (lookupGates p.length (projectRows project p)))
        (lookupOutput p.length (projectRows project p)) = project row ∧
      step p c = executeRow row c.2 :=
  ⟨lookup_rowAt p project c row wires hrow hw hstate hread, step_eq_executeRow p c row hrow⟩

/-- The concrete table-selection circuit feeds the canonical SAT language. -/
theorem lookup_fixed_sat (fixed : List Bool) (free n : Nat) (rows : List (Bool × Bool))
    (hbase : fixed.length+free = n+1) (hlen : rows.length = n) :
    sat (BitstringEncoding.bitEncode
      (compileFixed fixed free (lookupOutput n rows) (lookupGates n rows))) = true ↔
    ∃ wires : List Bool, wires.length = fixed.length+free ∧ Fixed (wire wires) 0 fixed ∧
      evalRows (wire wires) (wire wires n) 0 rows false = true := by
  have hv : validGates (fixed.length+free) (lookupGates n rows) := by
    rw [hbase]; exact lookup_valid n rows hlen
  have ho : lookupOutput n rows < fixed.length+free+(lookupGates n rows).length := by
    rw [hbase]; exact lookupOutput_bound n rows
  rw [fixed_sat_compiled_iff fixed free _ _ hv ho]
  apply exists_congr
  intro wires
  apply and_congr_right
  intro hw
  apply and_congr_right
  intro _
  rw [lookup_simulate wires n rows (by rw [hw,hbase]) hlen]

/-- Actual canonical CNF size for a finite transition-table bit lookup. -/
theorem lookup_cnf_encoded_length (fixed : List Bool) (free n : Nat) (rows : List (Bool × Bool))
    (hbase : fixed.length+free = n+1) (hlen : rows.length = n) :
    (BitstringEncoding.bitEncode
      (compileFixed fixed free (lookupOutput n rows) (lookupGates n rows))).length ≤
      (fixed.length+3*(2+4*n)+1)*(24*(n+1+2+4*n)+31) := by
  have hv : validGates (fixed.length+free) (lookupGates n rows) := by
    rw [hbase]; exact lookup_valid n rows hlen
  have ho : lookupOutput n rows < fixed.length+free+(lookupGates n rows).length := by
    rw [hbase]; exact lookupOutput_bound n rows
  have h := compileFixed_encoded_length fixed free (lookupOutput n rows) (lookupGates n rows) hv ho
  rw [lookupGates_length,hlen,hbase] at h
  convert h using 1 <;> ring

namespace Fixtures
example :
    wire (simulate [true,true] (lookupGates 1 (projectRows Prod.fst
      [((false,false,0,0),(true,false,0,0))])))
      (lookupOutput 1 (projectRows Prod.fst [((false,false,0,0),(true,false,0,0))])) = true := by
  apply lookup_rowAt [((false,false,0,0),(true,false,0,0))] Prod.fst
    (0,[],true,[]) (true,false,0,0) [true,true]
  · decide
  · decide
  · intro j hj
    have : j = 0 := by simp at hj; omega
    subst j
    decide
  · decide
example : wire (simulate [true,false,false] (lookupGates 2 [(true,false),(false,true)]))
    (lookupOutput 2 [(true,false),(false,true)]) = true := by decide
example : wire (simulate [false,true,true] (lookupGates 2 [(true,false),(false,true)]))
    (lookupOutput 2 [(true,false),(false,true)]) = true := by decide
example : wire (simulate [false,true,false] (lookupGates 2 [(true,false),(false,true)]))
    (lookupOutput 2 [(true,false),(false,true)]) = false := by decide
end Fixtures

end Shared.ComplexityBridge.CircuitTable
