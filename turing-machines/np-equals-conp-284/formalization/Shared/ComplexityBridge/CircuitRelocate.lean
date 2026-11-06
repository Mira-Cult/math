import Shared.ComplexityBridge.CircuitSelect

/-! Relocation of a topologically ordered Boolean circuit into an existing
wire environment. This is a compositional prerequisite for unrolling a finite
state-update circuit; it does not yet construct a TM2 simulation or a
polynomial-time reduction. -/
namespace Shared.ComplexityBridge.CircuitRelocate
open Shared.ComplexityBridge.CircuitCNF
open Shared.ComplexityBridge.CircuitSelect
open Shared.ComplexityBridge.CNF

/-- Original inputs are connected to explicit existing wires. The circuit's
internal outputs are laid out consecutively beginning at `base`. -/
def remap (width base : Nat) (inputs : List Nat) (i : Nat) : Nat :=
  if i < width then (inputs[i]?).getD 0 else base + (i-width)

def renameGate (f : Nat → Nat) : Gate → Gate
  | .constant b => .constant b
  | .neg x => .neg (f x)
  | .conj x y => .conj (f x) (f y)
  | .disj x y => .disj (f x) (f y)

def relocate (width base : Nat) (inputs : List Nat) (gates : List Gate) : List Gate :=
  gates.map (renameGate (remap width base inputs))

theorem relocate_length (width base : Nat) (inputs : List Nat) (gates : List Gate) :
    (relocate width base inputs gates).length = gates.length := by simp [relocate]

theorem remap_output (width base : Nat) (inputs : List Nat) (j : Nat) :
    remap width base inputs (width+j) = base+j := by
  simp [remap]

theorem remap_bound (width base : Nat) (inputs : List Nat)
    (hinputs : ∀ i < width, (inputs[i]?).getD 0 < base) (j i : Nat)
    (hi : i < width+j) : remap width base inputs i < base+j := by
  by_cases h : i < width
  · simp only [remap,if_pos h]
    have hh := hinputs i h
    omega
  · simp only [remap,if_neg h]
    omega

theorem renameGate_valid (f : Nat → Nat) (old new : Nat) (g : Gate)
    (hv : validGate old g) (hf : ∀ i < old, f i < new) :
    validGate new (renameGate f g) := by
  cases g with
  | constant b => trivial
  | neg x => exact hf x hv
  | conj x y => exact ⟨hf x hv.1,hf y hv.2⟩
  | disj x y => exact ⟨hf x hv.1,hf y hv.2⟩

theorem relocate_valid_aux (width base : Nat) (inputs : List Nat) (gates : List Gate)
    (hinputs : ∀ i < width, (inputs[i]?).getD 0 < base) (j : Nat)
    (hv : validGates (width+j) gates) :
    validGates (base+j) (relocate width base inputs gates) := by
  induction gates generalizing j with
  | nil => trivial
  | cons g gs ih =>
    simp only [validGates] at hv
    simp only [relocate,List.map_cons,validGates]
    refine ⟨renameGate_valid _ _ _ g hv.1 (remap_bound width base inputs hinputs j),?_⟩
    have hr := ih (j+1) (by simpa [Nat.add_assoc] using hv.2)
    simpa [relocate,Nat.add_assoc] using hr

theorem relocate_valid (width base : Nat) (inputs : List Nat) (gates : List Gate)
    (hinputs : ∀ i < width, (inputs[i]?).getD 0 < base)
    (hv : validGates width gates) :
    validGates base (relocate width base inputs gates) := by
  simpa using relocate_valid_aux width base inputs gates hinputs 0 (by simpa using hv)

theorem evalGate_rename (a : Valuation) (f : Nat → Nat) (g : Gate) :
    evalGate a (renameGate f g) = evalGate (a ∘ f) g := by
  cases g <;> rfl

theorem relocate_equations_aux (width base : Nat) (inputs : List Nat) (gates : List Gate)
    (a : Valuation) (j : Nat) :
    Equations a (base+j) (relocate width base inputs gates) ↔
      Equations (a ∘ remap width base inputs) (width+j) gates := by
  induction gates generalizing j with
  | nil => rfl
  | cons g gs ih =>
    simp only [relocate,List.map_cons,Equations,evalGate_rename,Function.comp_apply,remap_output]
    have hr := ih (j+1)
    simpa [relocate,Nat.add_assoc] using and_congr Iff.rfl hr

theorem relocate_equations (width base : Nat) (inputs : List Nat) (gates : List Gate)
    (a : Valuation) :
    Equations a base (relocate width base inputs gates) ↔
      Equations (a ∘ remap width base inputs) width gates := by
  simpa using relocate_equations_aux width base inputs gates a 0

/-- Relocated execution agrees at every original input or output wire with the
standalone execution on the connected inputs. -/
theorem relocate_simulate (wires : List Bool) (width : Nat) (inputs : List Nat)
    (gates : List Gate)
    (hinputs : ∀ i < width, (inputs[i]?).getD 0 < wires.length)
    (hv : validGates width gates) (out : Nat) (hout : out < width+gates.length) :
    wire (simulate wires (relocate width wires.length inputs gates))
      (remap width wires.length inputs out) =
    wire (simulate (seed width (wire wires ∘ remap width wires.length inputs)) gates) out := by
  let f := remap width wires.length inputs
  let original := seed width (wire wires ∘ f)
  let relocated := simulate wires (relocate width wires.length inputs gates)
  have hlen : original.length = width := seed_length width _
  have holdvalid : validGates original.length gates := by simpa [hlen] using hv
  have hold : Equations (wire (simulate original gates)) width gates := by
    have hh := simulate_equations original gates holdvalid
    simpa [hlen] using hh
  have hnewvalid := relocate_valid width wires.length inputs gates hinputs hv
  have hnew : Equations (wire relocated ∘ f) width gates := by
    apply (relocate_equations width wires.length inputs gates (wire relocated)).1
    exact simulate_equations wires _ hnewvalid
  have heq : ∀ i < width, (wire relocated ∘ f) i = wire (simulate original gates) i := by
    intro i hi
    simp only [Function.comp_apply]
    rw [wire_simulate original gates i (by rw [hlen]; exact hi)]
    rw [seed_wire width _ i hi]
    simp only [Function.comp_apply]
    apply wire_simulate wires _ (f i)
    exact remap_bound width wires.length inputs hinputs 0 i (by simpa using hi)
  exact equations_agree (wire relocated ∘ f) (wire (simulate original gates))
    width gates hv hnew hold heq out hout

/-- Connect each next-state input to the chosen output of the current copy. -/
def nextRefs (width base : Nat) (inputs outputs : List Nat) : List Nat :=
  outputs.map (remap width base inputs)

/-- A sequence of identical transition circuits; there is no implicit input
or free iteration. Each copy contributes exactly the original gate list. -/
def unroll (width : Nat) (gates : List Gate) (outputs : List Nat) :
    Nat → List Nat → Nat → List Gate
  | _, _, 0 => []
  | base, inputs, n+1 =>
      relocate width base inputs gates ++
        unroll width gates outputs (base+gates.length) (nextRefs width base inputs outputs) n

theorem unroll_length (width : Nat) (gates : List Gate) (outputs : List Nat)
    (base : Nat) (inputs : List Nat) (n : Nat) :
    (unroll width gates outputs base inputs n).length = n*gates.length := by
  induction n generalizing base inputs with
  | zero => simp [unroll]
  | succ n ih => simp [unroll,relocate_length,ih,Nat.succ_mul,Nat.add_comm]

theorem nextRefs_bound (width base : Nat) (inputs outputs : List Nat) (gates : List Gate)
    (hinputs : ∀ i < width, (inputs[i]?).getD 0 < base)
    (hlen : outputs.length = width)
    (houtputs : ∀ o ∈ outputs, o < width+gates.length) :
    ∀ i < width, ((nextRefs width base inputs outputs)[i]?).getD 0 < base+gates.length := by
  intro i hi
  have hi' : i < outputs.length := by rw [hlen]; exact hi
  have hm : outputs[i] ∈ outputs := List.getElem_mem hi'
  have hbound := houtputs _ hm
  have hr := remap_bound width base inputs hinputs gates.length outputs[i] hbound
  simpa [nextRefs,List.getElem?_map,hi'] using hr

theorem unroll_valid (width : Nat) (gates : List Gate) (outputs : List Nat)
    (hv : validGates width gates) (hlen : outputs.length = width)
    (houtputs : ∀ o ∈ outputs, o < width+gates.length)
    (base : Nat) (inputs : List Nat)
    (hinputs : ∀ i < width, (inputs[i]?).getD 0 < base) (n : Nat) :
    validGates base (unroll width gates outputs base inputs n) := by
  induction n generalizing base inputs with
  | zero => trivial
  | succ n ih =>
    simp only [unroll,validGates_append,relocate_length]
    exact ⟨relocate_valid width base inputs gates hinputs hv,
      ih (base+gates.length) (nextRefs width base inputs outputs)
        (nextRefs_bound width base inputs outputs gates hinputs hlen houtputs)⟩

/-- Read a logical Boolean state from the explicitly connected wires. -/
def readState (wires : List Bool) (width : Nat) (inputs : List Nat) : List Bool :=
  seed width (wire wires ∘ remap width wires.length inputs)

def stepState (gates : List Gate) (outputs : List Nat) (state : List Bool) : List Bool :=
  outputs.map (wire (simulate state gates))

def runState (gates : List Gate) (outputs : List Nat) : Nat → List Bool → List Bool
  | 0, state => state
  | n+1, state => runState gates outputs n (stepState gates outputs state)

theorem readState_length (wires : List Bool) (width : Nat) (inputs : List Nat) :
    (readState wires width inputs).length = width := seed_length width _

theorem readState_wire (wires : List Bool) (width : Nat) (inputs : List Nat)
    (i : Nat) (hi : i < width) :
    wire (readState wires width inputs) i = wire wires ((inputs[i]?).getD 0) := by
  rw [readState,seed_wire width _ i hi]
  simp [remap,hi,Function.comp_apply]

theorem wire_get (xs : List Bool) (i : Nat) (hi : i < xs.length) : wire xs i = xs[i] := by
  simp [wire,hi]

/-- One relocated copy produces precisely the logical next state. -/
theorem readState_after_copy (wires : List Bool) (width : Nat) (inputs outputs : List Nat)
    (gates : List Gate)
    (hinputs : ∀ i < width, (inputs[i]?).getD 0 < wires.length)
    (hv : validGates width gates) (hlen : outputs.length = width)
    (houtputs : ∀ o ∈ outputs, o < width+gates.length) :
    readState (simulate wires (relocate width wires.length inputs gates)) width
        (nextRefs width wires.length inputs outputs) =
      stepState gates outputs (readState wires width inputs) := by
  let mid := simulate wires (relocate width wires.length inputs gates)
  have hm : mid.length = wires.length+gates.length := by simp [mid,simulate_length,relocate_length]
  apply List.ext_getElem
  · simp [readState_length,stepState,hlen]
  · intro i hi₁ hi₂
    have hi : i < width := by simpa [readState_length] using hi₁
    have hio : i < outputs.length := by rw [hlen]; exact hi
    have ho : outputs[i] < width+gates.length := houtputs _ (List.getElem_mem hio)
    rw [← wire_get _ i hi₁,readState_wire _ _ _ i hi]
    simp only [stepState,List.getElem_map]
    have hr := relocate_simulate wires width inputs gates hinputs hv outputs[i] ho
    have hx : ((nextRefs width wires.length inputs outputs)[i]?).getD 0 =
        remap width wires.length inputs outputs[i] := by
      simp [nextRefs,hio]
    rw [hx]
    exact hr

/-- Wire references of the final state after all copies. -/
def finalRefs (width : Nat) (gates : List Gate) (outputs : List Nat) :
    Nat → List Nat → Nat → List Nat
  | _, inputs, 0 => inputs
  | base, inputs, n+1 =>
      finalRefs width gates outputs (base+gates.length) (nextRefs width base inputs outputs) n

theorem finalRefs_bound (width : Nat) (gates : List Gate) (outputs : List Nat)
    (hlen : outputs.length = width)
    (houtputs : ∀ o ∈ outputs, o < width+gates.length)
    (base : Nat) (inputs : List Nat)
    (hinputs : ∀ i < width, (inputs[i]?).getD 0 < base) (n : Nat) :
    ∀ i < width, ((finalRefs width gates outputs base inputs n)[i]?).getD 0 < base+n*gates.length := by
  induction n generalizing base inputs with
  | zero => simpa [finalRefs] using hinputs
  | succ n ih =>
    have hn := nextRefs_bound width base inputs outputs gates hinputs hlen houtputs
    have hr := ih (base+gates.length) (nextRefs width base inputs outputs) hn
    simpa [finalRefs,Nat.succ_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hr

/-- The finite unrolled circuit computes exactly the iterated transition. -/
theorem unroll_readState (wires : List Bool) (width : Nat) (inputs outputs : List Nat)
    (gates : List Gate)
    (hinputs : ∀ i < width, (inputs[i]?).getD 0 < wires.length)
    (hv : validGates width gates) (hlen : outputs.length = width)
    (houtputs : ∀ o ∈ outputs, o < width+gates.length) (n : Nat) :
    readState (simulate wires (unroll width gates outputs wires.length inputs n)) width
      (finalRefs width gates outputs wires.length inputs n) =
      runState gates outputs n (readState wires width inputs) := by
  induction n generalizing wires inputs with
  | zero => rfl
  | succ n ih =>
    let mid := simulate wires (relocate width wires.length inputs gates)
    have hm : mid.length = wires.length+gates.length := by simp [mid,simulate_length,relocate_length]
    have hn : ∀ i < width, ((nextRefs width wires.length inputs outputs)[i]?).getD 0 < mid.length := by
      rw [hm]
      exact nextRefs_bound width wires.length inputs outputs gates hinputs hlen houtputs
    have hr := ih mid (nextRefs width wires.length inputs outputs) hn
    rw [hm] at hr
    have hc := readState_after_copy wires width inputs outputs gates hinputs hv hlen houtputs
    change readState mid width (nextRefs width wires.length inputs outputs) = _ at hc
    rw [hc] at hr
    simpa [unroll,finalRefs,runState,simulate_append,mid] using hr

/-- Acceptance of one output of an unrolled circuit is reduced to the
project's actual all-bitstrings SAT language. -/
theorem unroll_fixed_sat (fixed : List Bool) (free width : Nat) (inputs outputs : List Nat)
    (gates : List Gate) (n i : Nat)
    (hinputs : ∀ j < width, (inputs[j]?).getD 0 < fixed.length+free)
    (hv : validGates width gates) (hlen : outputs.length = width)
    (houtputs : ∀ o ∈ outputs, o < width+gates.length) (hi : i < width) :
    sat (BitstringEncoding.bitEncode
      (compileFixed fixed free
        (((finalRefs width gates outputs (fixed.length+free) inputs n)[i]?).getD 0)
        (unroll width gates outputs (fixed.length+free) inputs n))) = true ↔
    ∃ wires : List Bool, wires.length = fixed.length+free ∧ Fixed (wire wires) 0 fixed ∧
      wire (runState gates outputs n (readState wires width inputs)) i = true := by
  let base := fixed.length+free
  let gs := unroll width gates outputs base inputs n
  let out := ((finalRefs width gates outputs base inputs n)[i]?).getD 0
  have hg : validGates base gs := unroll_valid width gates outputs hv hlen houtputs base inputs hinputs n
  have ho : out < base+gs.length := by
    dsimp [out,gs]
    rw [unroll_length]
    exact finalRefs_bound width gates outputs hlen houtputs base inputs hinputs n i hi
  change sat (BitstringEncoding.bitEncode (compileFixed fixed free out gs)) = true ↔ _
  rw [fixed_sat_compiled_iff fixed free out gs hg ho]
  apply exists_congr
  intro wires
  apply and_congr_right
  intro hwlen
  apply and_congr_right
  intro _
  have hin : ∀ j < width, (inputs[j]?).getD 0 < wires.length := by
    simpa only [hwlen] using hinputs
  have hr := unroll_readState wires width inputs outputs gates hin hv hlen houtputs n
  have hh := readState_wire (simulate wires (unroll width gates outputs wires.length inputs n)) width
    (finalRefs width gates outputs wires.length inputs n) i hi
  rw [hr] at hh
  apply iff_of_eq
  have he := congrArg (fun b => b = true) hh.symm
  simpa [out,gs,base,hwlen] using he

/-- Canonical CNF size of the unrolled finite transition circuit. -/
theorem unroll_cnf_encoded_length (fixed : List Bool) (free width : Nat) (inputs outputs : List Nat)
    (gates : List Gate) (n i : Nat)
    (hinputs : ∀ j < width, (inputs[j]?).getD 0 < fixed.length+free)
    (hv : validGates width gates) (hlen : outputs.length = width)
    (houtputs : ∀ o ∈ outputs, o < width+gates.length) (hi : i < width) :
    (BitstringEncoding.bitEncode
      (compileFixed fixed free
        (((finalRefs width gates outputs (fixed.length+free) inputs n)[i]?).getD 0)
        (unroll width gates outputs (fixed.length+free) inputs n))).length ≤
      (fixed.length+3*(n*gates.length)+1)*
        (24*(fixed.length+free+n*gates.length)+31) := by
  let base := fixed.length+free
  let gs := unroll width gates outputs base inputs n
  let out := ((finalRefs width gates outputs base inputs n)[i]?).getD 0
  have hg : validGates base gs := unroll_valid width gates outputs hv hlen houtputs base inputs hinputs n
  have ho : out < base+gs.length := by
    dsimp [out,gs]
    rw [unroll_length]
    exact finalRefs_bound width gates outputs hlen houtputs base inputs hinputs n i hi
  have h := compileFixed_encoded_length fixed free out gs hg ho
  simpa only [out,gs,base,unroll_length] using h

namespace Fixtures
example : runState [.neg 0] [1] 0 [false] = [false] := by decide
example : runState [.neg 0] [1] 3 [false] = [true] := by decide
example : runState [.neg 0] [1] 4 [false] = [false] := by decide
example : wire (simulate [false] (unroll 1 [.neg 0] [1] 1 [0] 3)) 3 = true := by decide
example : relocate 2 3 [2,0] [.conj 0 1,.neg 2] = [.conj 2 0,.neg 3] := by decide
example : wire (simulate [true,false,true] (relocate 2 3 [2,0] [.conj 0 1,.neg 2])) 4 = false := by decide
end Fixtures
end Shared.ComplexityBridge.CircuitRelocate
