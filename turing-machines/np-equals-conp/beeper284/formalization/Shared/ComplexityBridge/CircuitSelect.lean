import Shared.ComplexityBridge.CircuitCNF

/-! Explicit multiplexers for Boolean circuits. They provide a bounded-size
building block for data-dependent selection in a future bounded-machine
simulation. They do not construct that simulation or establish SAT hardness. -/
namespace Shared.ComplexityBridge.CircuitSelect
open Shared.ComplexityBridge.CircuitCNF
open Shared.ComplexityBridge.CNF

/-- Append one selected Boolean: if `selector` then `yes` else `no`.
The four output wires are numbered `base` through `base + 3`. -/
def mux (base selector yes no : Nat) : List Gate :=
  [.neg selector, .conj selector yes, .conj base no, .disj (base+1) (base+2)]

theorem mux_length (base selector yes no : Nat) :
    (mux base selector yes no).length = 4 := rfl

theorem mux_valid (base selector yes no : Nat)
    (hs : selector < base) (hy : yes < base) (hn : no < base) :
    validGates base (mux base selector yes no) := by
  simp [mux,validGates,validGate]
  omega

/-- The multiplexer equations have the selected input as their final wire. -/
theorem mux_equations (a : Valuation) (base selector yes no : Nat)
    (h : Equations a base (mux base selector yes no)) :
    a (base+3) = if a selector then a yes else a no := by
  simp only [mux,Equations,evalGate] at h
  obtain ⟨h0,h1,h2,h3,_⟩ := h
  have h3' : a (base+3) = (a (base+1) || a (base+2)) := by
    simpa only [Nat.add_assoc] using h3
  have h2' : a (base+2) = (a base && a no) := by
    simpa only [Nat.add_assoc] using h2
  have h1' : a (base+1) = (a selector && a yes) := by
    simpa using h1
  rw [h3',h1',h2',h0]
  cases a selector <;> simp

/-- The executable circuit really computes the selector on the original wires. -/
theorem mux_simulate (wires : List Bool) (selector yes no : Nat)
    (hs : selector < wires.length) (hy : yes < wires.length) (hn : no < wires.length) :
    wire (simulate wires (mux wires.length selector yes no)) (wires.length+3) =
      if wire wires selector then wire wires yes else wire wires no := by
  have hv := mux_valid wires.length selector yes no hs hy hn
  have he := mux_equations (wire (simulate wires (mux wires.length selector yes no)))
    wires.length selector yes no (simulate_equations wires _ hv)
  rw [he, wire_simulate wires _ selector hs, wire_simulate wires _ yes hy,
    wire_simulate wires _ no hn]

/-- The canonical SAT front end agrees with selection of any initial assignment
whose fixed prefix is the given input. -/
theorem mux_fixed_sat (fixed : List Bool) (free selector yes no : Nat)
    (hs : selector < fixed.length+free) (hy : yes < fixed.length+free)
    (hn : no < fixed.length+free) :
    sat (BitstringEncoding.bitEncode
      (compileFixed fixed free (fixed.length+free+3) (mux (fixed.length+free) selector yes no))) = true ↔
      ∃ inputs : List Bool, inputs.length = fixed.length+free ∧ Fixed (wire inputs) 0 fixed ∧
        (if wire inputs selector then wire inputs yes else wire inputs no) = true := by
  have hv := mux_valid (fixed.length+free) selector yes no hs hy hn
  have hout : fixed.length+free+3 < fixed.length+free+(mux (fixed.length+free) selector yes no).length := by
    rw [mux_length]; omega
  rw [fixed_sat_compiled_iff fixed free _ _ hv hout]
  apply exists_congr
  intro inputs
  apply and_congr_right
  intro hlen
  apply and_congr_right
  intro _
  have hh := mux_simulate inputs selector yes no (by rw [hlen]; exact hs)
    (by rw [hlen]; exact hy) (by rw [hlen]; exact hn)
  simpa only [hlen] using iff_of_eq (congrArg (fun b => b = true) hh)

/-- Consecutive circuit fragments preserve their topological interface. -/
theorem validGates_append (base : Nat) (left right : List Gate) :
    validGates base (left ++ right) ↔
      validGates base left ∧ validGates (base+left.length) right := by
  induction left generalizing base with
  | nil => simp [validGates]
  | cons g gs ih => simp [validGates,ih,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm,and_assoc]

theorem simulate_append (wires : List Bool) (left right : List Gate) :
    simulate wires (left++right) = simulate (simulate wires left) right := by
  induction left generalizing wires with
  | nil => rfl
  | cons g gs ih => simp [simulate,ih]

/-- Parallel bitwise selection, with one common selector and independent
input pairs. Each output occupies the last wire of its four-gate fragment. -/
def muxes (base selector : Nat) : List (Nat × Nat) → List Gate
  | [] => []
  | (yes,no)::rest => mux base selector yes no ++ muxes (base+4) selector rest

theorem muxes_length (base selector : Nat) (pairs : List (Nat × Nat)) :
    (muxes base selector pairs).length = 4*pairs.length := by
  induction pairs generalizing base with
  | nil => rfl
  | cons pair rest ih =>
    cases pair with
    | mk yes no => simp [muxes,mux_length,ih]; omega

theorem muxes_valid (base selector : Nat) (pairs : List (Nat × Nat))
    (hs : selector < base) (hp : ∀ p ∈ pairs, p.1 < base ∧ p.2 < base) :
    validGates base (muxes base selector pairs) := by
  induction pairs generalizing base with
  | nil => trivial
  | cons pair rest ih =>
    rcases pair with ⟨yes,no⟩
    have hh : yes < base ∧ no < base := hp (yes,no) (by simp)
    have ht : ∀ p ∈ rest, p.1 < base+4 ∧ p.2 < base+4 := by
      intro p hmem
      have h := hp p (by simp [hmem])
      omega
    simp only [muxes,validGates_append,mux_length]
    exact ⟨mux_valid base selector yes no hs hh.1 hh.2,
      ih (base+4) (by omega) ht⟩

/-- Every output in the generated fragment has the selected original value;
the other fragments cannot overwrite its wire. -/
theorem muxes_simulate (wires : List Bool) (selector : Nat) (pairs : List (Nat × Nat))
    (hs : selector < wires.length)
    (hp : ∀ p ∈ pairs, p.1 < wires.length ∧ p.2 < wires.length)
    (i yes no : Nat) (hi : pairs[i]? = some (yes,no)) :
    wire (simulate wires (muxes wires.length selector pairs)) (wires.length+4*i+3) =
      if wire wires selector then wire wires yes else wire wires no := by
  induction pairs generalizing wires i with
  | nil => simp at hi
  | cons pair rest ih =>
    rcases pair with ⟨y,n⟩
    have hh : y < wires.length ∧ n < wires.length := hp (y,n) (by simp)
    let mid := simulate wires (mux wires.length selector y n)
    have hlen : mid.length = wires.length+4 := by simp [mid,simulate_length,mux_length]
    have htail : ∀ p ∈ rest, p.1 < mid.length ∧ p.2 < mid.length := by
      intro p hm
      have hp' := hp p (by simp [hm])
      rw [hlen]
      omega
    have hs' : selector < mid.length := by rw [hlen]; omega
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq,Prod.mk.injEq] at hi
      rcases hi with ⟨rfl,rfl⟩
      simp only [muxes,simulate_append]
      change wire (simulate mid (muxes (wires.length+4) selector rest)) (wires.length+4*0+3) = _
      rw [wire_simulate mid _ _ (by rw [hlen]; omega)]
      simpa [mid] using mux_simulate wires selector y n hs hh.1 hh.2
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      have hr := ih mid hs' htail i hi
      rw [hlen] at hr
      have heq : wires.length+4*(i+1)+3 = (wires.length+4)+4*i+3 := by omega
      simp only [muxes,simulate_append]
      change wire (simulate mid (muxes (wires.length+4) selector rest)) (wires.length+4*(i+1)+3) = _
      rw [heq,hr]
      dsimp [mid]
      rw [wire_simulate wires _ selector hs]
      have hpyn : yes < wires.length ∧ no < wires.length := by
        have hm : (yes,no) ∈ rest := List.mem_of_getElem? hi
        exact hp (yes,no) (by simp [hm])
      rw [wire_simulate wires _ yes hpyn.1,wire_simulate wires _ no hpyn.2]

/-- A selected output of the vector circuit reduces to the actual SAT front end. -/
theorem muxes_fixed_sat (fixed : List Bool) (free selector : Nat) (pairs : List (Nat × Nat))
    (hs : selector < fixed.length+free)
    (hp : ∀ p ∈ pairs, p.1 < fixed.length+free ∧ p.2 < fixed.length+free)
    (i yes no : Nat) (hi : pairs[i]? = some (yes,no)) :
    sat (BitstringEncoding.bitEncode
      (compileFixed fixed free (fixed.length+free+4*i+3)
        (muxes (fixed.length+free) selector pairs))) = true ↔
      ∃ inputs : List Bool, inputs.length = fixed.length+free ∧ Fixed (wire inputs) 0 fixed ∧
        (if wire inputs selector then wire inputs yes else wire inputs no) = true := by
  have hv := muxes_valid (fixed.length+free) selector pairs hs hp
  have hidx : i < pairs.length := (List.getElem?_eq_some_iff.mp hi).1
  have hout : fixed.length+free+4*i+3 < fixed.length+free+(muxes (fixed.length+free) selector pairs).length := by
    rw [muxes_length]; omega
  rw [fixed_sat_compiled_iff fixed free _ _ hv hout]
  apply exists_congr
  intro inputs
  apply and_congr_right
  intro hlen
  apply and_congr_right
  intro _
  have hp' : ∀ p ∈ pairs, p.1 < inputs.length ∧ p.2 < inputs.length := by
    simpa only [hlen] using hp
  have hh := muxes_simulate inputs selector pairs (by rw [hlen]; exact hs) hp' i yes no hi
  simpa only [hlen] using iff_of_eq (congrArg (fun b => b = true) hh)

/-- Concrete canonical-encoding size of the vector-selector CNF. -/
theorem muxes_cnf_encoded_length (fixed : List Bool) (free selector : Nat) (pairs : List (Nat × Nat))
    (hs : selector < fixed.length+free)
    (hp : ∀ p ∈ pairs, p.1 < fixed.length+free ∧ p.2 < fixed.length+free)
    (i yes no : Nat) (hi : pairs[i]? = some (yes,no)) :
    (BitstringEncoding.bitEncode
      (compileFixed fixed free (fixed.length+free+4*i+3)
        (muxes (fixed.length+free) selector pairs))).length ≤
      (fixed.length+12*pairs.length+1)*(24*(fixed.length+free+4*pairs.length)+31) := by
  have hv := muxes_valid (fixed.length+free) selector pairs hs hp
  have hidx : i < pairs.length := (List.getElem?_eq_some_iff.mp hi).1
  have hout : fixed.length+free+4*i+3 < fixed.length+free+(muxes (fixed.length+free) selector pairs).length := by
    rw [muxes_length]; omega
  have h := compileFixed_encoded_length fixed free (fixed.length+free+4*i+3)
    (muxes (fixed.length+free) selector pairs) hv hout
  rw [muxes_length] at h
  convert h using 1 <;> ring

namespace Fixtures
example : wire (simulate [true,false,true] (mux 3 0 1 2)) 6 = false := by decide
example : wire (simulate [false,false,true] (mux 3 0 1 2)) 6 = true := by decide
example : (mux 3 0 1 2).length = 4 := rfl
example : wire (simulate [true,false,true,true,false] (muxes 5 0 [(1,2),(3,4)])) 8 = false := by decide
example : wire (simulate [true,false,true,true,false] (muxes 5 0 [(1,2),(3,4)])) 12 = true := by decide
example : wire (simulate [false,false,true,true,false] (muxes 5 0 [(1,2),(3,4)])) 12 = false := by decide
end Fixtures
end Shared.ComplexityBridge.CircuitSelect
