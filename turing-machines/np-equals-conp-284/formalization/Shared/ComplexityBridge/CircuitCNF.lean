import Shared.ComplexityBridge.CNF

/-! A concrete Tseitin encoding into the project's actual CNF syntax. This
is a circuit-to-CNF layer; it does not yet construct a circuit for a TM2
computation, prove the encoder polynomial-time, or establish SAT hardness. -/
namespace Shared.ComplexityBridge.CircuitCNF
open Shared.ComplexityBridge.CNF

/-- Inputs are the initial wires. Each gate appends one wire. -/
inductive Gate where
  | constant (value : Bool)
  | neg (x : Nat)
  | conj (x y : Nat)
  | disj (x y : Nat)
  deriving DecidableEq, Repr

def evalGate (a : Valuation) : Gate → Bool
  | .constant b => b
  | .neg x => !(a x)
  | .conj x y => a x && a y
  | .disj x y => a x || a y

/-- Every reference to a gate input is strictly earlier than its output wire. -/
def validGate (bound : Nat) : Gate → Prop
  | .constant _ => True
  | .neg x => x < bound
  | .conj x y | .disj x y => x < bound ∧ y < bound

def validGates (base : Nat) : List Gate → Prop
  | [] => True
  | g::gs => validGate base g ∧ validGates (base+1) gs

/-- A gate contributes at most three clauses, each containing at most three
literals. The Boolean in a literal is its satisfying wire value. -/
def gateCNF (out : Nat) : Gate → Formula
  | .constant b => [[(out,b)]]
  | .neg x => [[(out,false),(x,false)],[(out,true),(x,true)]]
  | .conj x y => [[(out,false),(x,true)],[(out,false),(y,true)],[(out,true),(x,false),(y,false)]]
  | .disj x y => [[(out,true),(x,false)],[(out,true),(y,false)],[(out,false),(x,true),(y,true)]]

def gateConstraints (base : Nat) : List Gate → Formula
  | [] => []
  | g::gs => gateCNF base g ++ gateConstraints (base+1) gs

def compile (base output : Nat) (gates : List Gate) : Formula :=
  gateConstraints base gates ++ [[(output,true)]]

theorem evalFormula_append (a : Valuation) (f g : Formula) :
    evalFormula a (f++g) = (evalFormula a f && evalFormula a g) := by
  simp [evalFormula,List.all_append]

/-- The clauses for one gate force exactly its truth-table equation. -/
theorem gateCNF_correct (a : Valuation) (out : Nat) (g : Gate) :
    evalFormula a (gateCNF out g) = true ↔ a out = evalGate a g := by
  cases g with
  | constant b => cases b <;> cases h : a out <;> simp [gateCNF,evalFormula,evalClause,evalLiteral,evalGate,h]
  | neg x => cases ho : a out <;> cases hx : a x <;> simp [gateCNF,evalFormula,evalClause,evalLiteral,evalGate,ho,hx]
  | conj x y => cases ho : a out <;> cases hx : a x <;> cases hy : a y <;> simp [gateCNF,evalFormula,evalClause,evalLiteral,evalGate,ho,hx,hy]
  | disj x y => cases ho : a out <;> cases hx : a x <;> cases hy : a y <;> simp [gateCNF,evalFormula,evalClause,evalLiteral,evalGate,ho,hx,hy]

def Equations (a : Valuation) (base : Nat) : List Gate → Prop
  | [] => True
  | g::gs => a base = evalGate a g ∧ Equations a (base+1) gs

theorem gateConstraints_correct (a : Valuation) (base : Nat) (gates : List Gate) :
    evalFormula a (gateConstraints base gates) = true ↔ Equations a base gates := by
  induction gates generalizing base with
  | nil => simp [gateConstraints,evalFormula,Equations]
  | cons g gs ih =>
    simp only [gateConstraints,evalFormula_append,Bool.and_eq_true,Equations]
    rw [gateCNF_correct,ih]

theorem compile_correct (a : Valuation) (base output : Nat) (gates : List Gate) :
    evalFormula a (compile base output gates) = true ↔ Equations a base gates ∧ a output = true := by
  rw [compile,evalFormula_append,Bool.and_eq_true,gateConstraints_correct]
  simp [evalFormula,evalClause,evalLiteral]

theorem satisfiable_iff (base output : Nat) (gates : List Gate) :
    Satisfiable (compile base output gates) ↔ ∃ a : Valuation, Equations a base gates ∧ a output = true := by
  simp only [Satisfiable,compile_correct]

theorem gateCNF_length (out : Nat) (g : Gate) : (gateCNF out g).length ≤ 3 := by cases g <;> simp [gateCNF]
theorem gateConstraints_length (base : Nat) (gates : List Gate) :
    (gateConstraints base gates).length ≤ 3*gates.length := by
  induction gates generalizing base with
  | nil => simp [gateConstraints]
  | cons g gs ih =>
    simp only [gateConstraints,List.length_append,List.length_cons]
    have hg := gateCNF_length base g
    have hh := ih (base+1)
    omega

theorem compile_length (base output : Nat) (gates : List Gate) :
    (compile base output gates).length ≤ 3*gates.length+1 := by
  have h := gateConstraints_length base gates
  simp only [compile,List.length_append,List.length_cons,List.length_nil] at *
  omega

theorem gateCNF_clause_length (out : Nat) (g : Gate) (c : Clause) (h : c ∈ gateCNF out g) : c.length ≤ 3 := by
  cases g <;> simp [gateCNF] at h
  all_goals rcases h with rfl | rfl | rfl <;> simp

theorem compile_clause_length (base output : Nat) (gates : List Gate) (c : Clause) (h : c ∈ compile base output gates) : c.length ≤ 3 := by
  have hconstraints : ∀ base gates c, c ∈ gateConstraints base gates → c.length ≤ 3 := by
    intro base gates
    induction gates generalizing base with
    | nil => simp [gateConstraints]
    | cons g gs ih =>
      intro c hc
      simp only [gateConstraints,List.mem_append] at hc
      rcases hc with hc | hc
      · exact gateCNF_clause_length base g c hc
      · exact ih (base+1) c hc
  simp only [compile,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h | rfl
  · exact hconstraints base gates c h
  · simp


/-- A finite wire list denotes a total valuation, defaulting to false beyond
its end. Valid gate references never consult that default. -/
def wire (xs : List Bool) (i : Nat) : Bool := xs[i]?.getD false

def simulate (wires : List Bool) : List Gate → List Bool
  | [] => wires
  | g::gs => simulate (wires ++ [evalGate (wire wires) g]) gs

theorem simulate_length (wires : List Bool) (gates : List Gate) :
    (simulate wires gates).length = wires.length+gates.length := by
  induction gates generalizing wires with
  | nil => simp [simulate]
  | cons g gs ih => simp [simulate,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem simulate_prefix (wires : List Bool) (gates : List Gate) :
    ∃ tail, simulate wires gates = wires ++ tail := by
  induction gates generalizing wires with
  | nil => exact ⟨[],by simp [simulate]⟩
  | cons g gs ih =>
    obtain ⟨tail,h⟩ := ih (wires ++ [evalGate (wire wires) g])
    refine ⟨[evalGate (wire wires) g] ++ tail,?_⟩
    simpa [simulate,List.append_assoc] using h

theorem wire_append (xs ys : List Bool) (i : Nat) (h : i < xs.length) :
    wire (xs++ys) i = wire xs i := by
  simp [wire,List.getElem?_append_left h]

theorem wire_simulate (wires : List Bool) (gates : List Gate) (i : Nat) (h : i < wires.length) :
    wire (simulate wires gates) i = wire wires i := by
  obtain ⟨tail,htail⟩ := simulate_prefix wires gates
  rw [htail]
  exact wire_append wires tail i h

theorem evalGate_agree (g : Gate) (bound : Nat) (a b : Valuation)
    (hvalid : validGate bound g) (h : ∀ i < bound, a i = b i) :
    evalGate a g = evalGate b g := by
  cases g with
  | constant v => rfl
  | neg x => simp [validGate] at hvalid; simp [evalGate,h x hvalid]
  | conj x y => simp [validGate] at hvalid; simp [evalGate,h x hvalid.1,h y hvalid.2]
  | disj x y => simp [validGate] at hvalid; simp [evalGate,h x hvalid.1,h y hvalid.2]

theorem wire_last (xs : List Bool) (b : Bool) : wire (xs ++ [b]) xs.length = b := by
  simp [wire,List.getElem?_append_right]

/-- A topological finite evaluation satisfies every generated gate equation. -/
theorem simulate_equations (wires : List Bool) (gates : List Gate)
    (hvalid : validGates wires.length gates) :
    Equations (wire (simulate wires gates)) wires.length gates := by
  induction gates generalizing wires with
  | nil => trivial
  | cons g gs ih =>
    simp only [validGates] at hvalid
    let next := wires ++ [evalGate (wire wires) g]
    have hn : next.length = wires.length+1 := by simp [next]
    have htail : Equations (wire (simulate next gs)) (wires.length+1) gs := by
      have hh := ih next (by simpa [hn] using hvalid.2)
      simpa [hn] using hh
    have hbefore : ∀ i < wires.length, wire (simulate next gs) i = wire wires i := by
      intro i hi
      have hni : i < next.length := by rw [hn]; omega
      rw [wire_simulate next gs i hni]
      exact wire_append wires [evalGate (wire wires) g] i hi
    have hgate := evalGate_agree g wires.length (wire (simulate next gs)) (wire wires) hvalid.1 hbefore
    have hout : wire (simulate next gs) wires.length = evalGate (wire wires) g := by
      have hi : wires.length < next.length := by rw [hn]; omega
      rw [wire_simulate next gs wires.length hi]
      exact wire_last wires (evalGate (wire wires) g)
    change wire (simulate next gs) wires.length = evalGate (wire (simulate next gs)) g ∧
      Equations (wire (simulate next gs)) (wires.length+1) gs
    exact ⟨hout.trans hgate.symm,htail⟩

/-- Gate equations determine all circuit wires once the initial wires agree. -/
theorem equations_agree (a b : Valuation) (base : Nat) (gates : List Gate)
    (hvalid : validGates base gates) (ha : Equations a base gates) (hb : Equations b base gates)
    (hinput : ∀ i < base, a i = b i) :
    ∀ i < base+gates.length, a i = b i := by
  induction gates generalizing base with
  | nil => simpa using hinput
  | cons g gs ih =>
    simp only [validGates] at hvalid
    simp only [Equations] at ha hb
    have hgate := evalGate_agree g base a b hvalid.1 hinput
    have hout : a base = b base := ha.1.trans (hgate.trans hb.1.symm)
    have hnext : ∀ i < base+1, a i = b i := by
      intro i hi
      by_cases hlt : i < base
      · exact hinput i hlt
      · have he : i = base := by omega
        subst i; exact hout
    have hh := ih (base+1) hvalid.2 ha.2 hb.2 hnext
    intro i hi
    apply hh
    simp only [List.length_cons] at hi
    omega

def seed (n : Nat) (a : Valuation) : List Bool := (List.range n).map a

theorem seed_length (n : Nat) (a : Valuation) : (seed n a).length = n := by simp [seed]

theorem seed_wire (n : Nat) (a : Valuation) (i : Nat) (h : i < n) : wire (seed n a) i = a i := by
  simp [wire,seed,List.getElem?_map,h]

/-- Circuit satisfiability is equivalent to accepting some finite initial
assignment. Output must name a wire in the finite circuit, and every gate
must read earlier wires. -/
theorem circuit_satisfiable_iff (base output : Nat) (gates : List Gate)
    (hvalid : validGates base gates) (hout : output < base+gates.length) :
    Satisfiable (compile base output gates) ↔
      ∃ inputs : List Bool, inputs.length = base ∧ wire (simulate inputs gates) output = true := by
  rw [satisfiable_iff]
  constructor
  · rintro ⟨a,ha,haccept⟩
    let inputs := seed base a
    have hlen : inputs.length = base := seed_length base a
    have hv : validGates inputs.length gates := by simpa [hlen] using hvalid
    have heq := simulate_equations inputs gates hv
    have hb : Equations (wire (simulate inputs gates)) base gates := by simpa [hlen] using heq
    have hinput : ∀ i < base, a i = wire (simulate inputs gates) i := by
      intro i hi
      rw [wire_simulate inputs gates i (by simpa [hlen] using hi)]
      exact (seed_wire base a i hi).symm
    have hagree := equations_agree a (wire (simulate inputs gates)) base gates hvalid ha hb hinput
    refine ⟨inputs,hlen,?_⟩
    rw [← hagree output hout]
    exact haccept
  · rintro ⟨inputs,hlen,haccept⟩
    have hv : validGates inputs.length gates := by simpa [hlen] using hvalid
    have heq := simulate_equations inputs gates hv
    refine ⟨wire (simulate inputs gates),?_,haccept⟩
    simpa [hlen] using heq


/-- Every variable used by a valid gate is bounded by its output index. -/
theorem gateCNF_variable_bound (out bound : Nat) (g : Gate)
    (hvalid : validGate out g) (hout : out ≤ bound) :
    ∀ c ∈ gateCNF out g, ∀ lit ∈ c, lit.1 ≤ bound := by
  cases g <;> simp [gateCNF,validGate] at *
  all_goals grind

theorem gateConstraints_variable_bound (base bound : Nat) (gates : List Gate)
    (hvalid : validGates base gates) (hbound : base+gates.length ≤ bound) :
    ∀ c ∈ gateConstraints base gates, ∀ lit ∈ c, lit.1 ≤ bound := by
  induction gates generalizing base with
  | nil => simp [gateConstraints]
  | cons g gs ih =>
    simp only [validGates] at hvalid
    intro c hc lit hl
    simp only [gateConstraints,List.mem_append] at hc
    rcases hc with hc | hc
    · exact gateCNF_variable_bound base bound g hvalid.1 (by simp only [List.length_cons] at hbound; omega) c hc lit hl
    · exact ih (base+1) hvalid.2 (by simp only [List.length_cons] at hbound; omega) c hc lit hl

theorem compile_variable_bound (base output : Nat) (gates : List Gate)
    (hvalid : validGates base gates) (hout : output < base+gates.length) :
    ∀ c ∈ compile base output gates, ∀ lit ∈ c, lit.1 ≤ base+gates.length := by
  intro c hc lit hl
  simp only [compile,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with hc | rfl
  · exact gateConstraints_variable_bound base (base+gates.length) gates hvalid (by rfl) c hc lit hl
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
    subst lit
    simp only
    omega

theorem encodePosNum_length_le (p : PosNum) : (Computability.encodePosNum p).length ≤ (p : Nat) := by
  induction p with
  | one => rfl
  | bit0 p ih =>
    have hp := PosNum.to_nat_pos p
    simp only [Computability.encodePosNum,List.length_cons,PosNum.cast_bit0] at *
    omega
  | bit1 p ih =>
    have hp := PosNum.to_nat_pos p
    simp only [Computability.encodePosNum,List.length_cons,PosNum.cast_bit1] at *
    omega

theorem encodeNat_length_le (n : Nat) : (Computability.encodeNat n).length ≤ n := by
  have h : ((n : Num) : Nat) = n := Num.to_of_nat n
  cases hn : (n : Num) with
  | zero => simp [Computability.encodeNat,hn,Computability.encodeNum]
  | pos p =>
    have hp := encodePosNum_length_le p
    rw [hn] at h
    change (p : Nat) = n at h
    simp [Computability.encodeNat,hn,Computability.encodeNum,h] at hp ⊢
    exact hp

theorem literal_encoded_length (n : Nat) (b : Bool) :
    (BitstringEncoding.bitEncode ((n,b) : Literal)).length = 2*(Computability.encodeNat n).length+2 := by
  change (BitstringEncoding.delimit (Computability.encodeNat n) ++ [b]).length = _
  simp [BitstringEncoding.length_delimit]


/-- A bounded variable name has a bounded canonical literal encoding. -/
theorem literal_length_le (lit : Literal) (bound : Nat) (h : lit.1 ≤ bound) :
    (BitstringEncoding.bitEncode lit).length ≤ 2*bound+2 := by
  rcases lit with ⟨n,b⟩
  rw [literal_encoded_length]
  have hn := encodeNat_length_le n
  simp only at h
  omega

theorem clause_encoded_length_le (clause : Clause) (bound : Nat)
    (h : ∀ lit ∈ clause, lit.1 ≤ bound) :
    (BitstringEncoding.bitEncode clause).length ≤ clause.length*(4*bound+5) := by
  have hs : ∀ lit ∈ clause, (BitstringEncoding.delimit (BitstringEncoding.bitEncode lit)).length ≤ 4*bound+5 := by
    intro lit hl
    have hh := literal_length_le lit bound (h lit hl)
    rw [BitstringEncoding.length_delimit]
    omega
  have hsum := List.sum_le_sum (l := clause) (f := fun lit => (BitstringEncoding.delimit (BitstringEncoding.bitEncode lit)).length)
    (g := fun _ => 4*bound+5) hs
  change (((clause.map (fun lit : Literal => BitstringEncoding.bitEncode lit)).map BitstringEncoding.delimit).flatten).length ≤ _
  simp only [List.length_flatten,List.map_map]
  change (clause.map (fun lit => (BitstringEncoding.delimit (BitstringEncoding.bitEncode lit)).length)).sum ≤ _
  simpa only [List.map_const',List.sum_replicate_nat] using hsum

/-- The canonical CNF serialization has a concrete polynomial size bound in
the gate count and largest allowed wire index. -/
theorem compile_encoded_length (base output : Nat) (gates : List Gate)
    (hvalid : validGates base gates) (hout : output < base+gates.length) :
    (BitstringEncoding.bitEncode (compile base output gates)).length ≤
      (3*gates.length+1)*(24*(base+gates.length)+31) := by
  let f := compile base output gates
  let bound := base+gates.length
  have hv := compile_variable_bound base output gates hvalid hout
  have hc : ∀ c ∈ f, (BitstringEncoding.delimit (BitstringEncoding.bitEncode c)).length ≤ 24*bound+31 := by
    intro c hmem
    have hl := compile_clause_length base output gates c hmem
    have he := clause_encoded_length_le c bound (hv c hmem)
    rw [BitstringEncoding.length_delimit]
    have hm := Nat.mul_le_mul_right (4*bound+5) hl
    omega
  have hsum := List.sum_le_sum (l := f) (f := fun c => (BitstringEncoding.delimit (BitstringEncoding.bitEncode c)).length)
    (g := fun _ => 24*bound+31) hc
  have hlen := compile_length base output gates
  have hm := Nat.mul_le_mul_right (24*bound+31) hlen
  change (((f.map (fun c : Clause => BitstringEncoding.bitEncode c)).map BitstringEncoding.delimit).flatten).length ≤ _
  have hsum' : (((f.map (fun c : Clause => BitstringEncoding.bitEncode c)).map BitstringEncoding.delimit).flatten).length ≤
      f.length*(24*bound+31) := by
    simp only [List.length_flatten,List.map_map]
    change (f.map (fun c => (BitstringEncoding.delimit (BitstringEncoding.bitEncode c)).length)).sum ≤ _
    simpa only [List.map_const',List.sum_replicate_nat] using hsum
  change f.length ≤ 3*gates.length+1 at hlen
  exact le_trans hsum' hm


/-- The generated canonical input is accepted by the repository's total SAT
front end exactly when the finite circuit has an accepting initial assignment. -/
theorem sat_compiled_iff (base output : Nat) (gates : List Gate)
    (hvalid : validGates base gates) (hout : output < base+gates.length) :
    sat (BitstringEncoding.bitEncode (compile base output gates)) = true ↔
      ∃ inputs : List Bool, inputs.length = base ∧ wire (simulate inputs gates) output = true := by
  rw [sat_encode_correct]
  exact circuit_satisfiable_iff base output gates hvalid hout

/-- Unit clauses pin a prefix of the initial circuit wires to the given input. -/
def fixInputs (offset : Nat) : List Bool → Formula
  | [] => []
  | b::bs => [(offset,b)] :: fixInputs (offset+1) bs

def Fixed (a : Valuation) (offset : Nat) : List Bool → Prop
  | [] => True
  | b::bs => a offset = b ∧ Fixed a (offset+1) bs

theorem fixInputs_correct (a : Valuation) (offset : Nat) (bits : List Bool) :
    evalFormula a (fixInputs offset bits) = true ↔ Fixed a offset bits := by
  induction bits generalizing offset with
  | nil => simp [fixInputs,evalFormula,Fixed]
  | cons b bs ih =>
    simp only [fixInputs,evalFormula,List.all_cons,evalClause,List.any_cons,List.any_nil,
      Bool.or_false,Bool.and_eq_true,evalLiteral,beq_iff_eq,Fixed]
    exact and_congr Iff.rfl (ih (offset+1))

theorem Fixed_congr (a b : Valuation) (offset : Nat) (bits : List Bool)
    (h : ∀ i, offset ≤ i → i < offset+bits.length → a i = b i) :
    Fixed a offset bits ↔ Fixed b offset bits := by
  induction bits generalizing offset with
  | nil => rfl
  | cons v vs ih =>
    simp only [Fixed,List.length_cons] at *
    have hfirst : a offset = b offset := h offset (by omega) (by omega)
    have htail : ∀ i, offset+1 ≤ i → i < offset+1+vs.length → a i = b i := by
      intro i hi hj
      exact h i (by omega) (by omega)
    rw [hfirst,ih (offset+1) htail]

def compileFixed (fixed : List Bool) (free output : Nat) (gates : List Gate) : Formula :=
  fixInputs 0 fixed ++ compile (fixed.length+free) output gates

theorem compileFixed_correct (a : Valuation) (fixed : List Bool) (free output : Nat) (gates : List Gate) :
    evalFormula a (compileFixed fixed free output gates) = true ↔
      Fixed a 0 fixed ∧ Equations a (fixed.length+free) gates ∧ a output = true := by
  simp only [compileFixed,evalFormula_append,Bool.and_eq_true,fixInputs_correct,compile_correct]

/-- With a fixed input prefix, SAT corresponds exactly to an accepting finite
wire assignment whose initial prefix agrees with the input. -/
theorem fixed_circuit_satisfiable_iff (fixed : List Bool) (free output : Nat) (gates : List Gate)
    (hvalid : validGates (fixed.length+free) gates) (hout : output < fixed.length+free+gates.length) :
    Satisfiable (compileFixed fixed free output gates) ↔
      ∃ inputs : List Bool, inputs.length = fixed.length+free ∧ Fixed (wire inputs) 0 fixed ∧
        wire (simulate inputs gates) output = true := by
  simp only [Satisfiable,compileFixed_correct]
  constructor
  · rintro ⟨a,hfixed,ha,haccept⟩
    let base := fixed.length+free
    let inputs := seed base a
    have hlen : inputs.length = base := seed_length base a
    have hv : validGates inputs.length gates := by simpa [hlen,base] using hvalid
    have hb : Equations (wire (simulate inputs gates)) base gates := by
      have heq := simulate_equations inputs gates hv
      simpa [hlen] using heq
    have hinput : ∀ i < base, a i = wire (simulate inputs gates) i := by
      intro i hi
      rw [wire_simulate inputs gates i (by simpa [hlen] using hi)]
      exact (seed_wire base a i hi).symm
    have hprefix : Fixed (wire inputs) 0 fixed := by
      apply (Fixed_congr a (wire inputs) 0 fixed ?_).1 hfixed
      intro i _ hi
      exact (seed_wire base a i (by dsimp [base]; omega)).symm
    have hagree := equations_agree a (wire (simulate inputs gates)) base gates hvalid ha hb hinput
    refine ⟨inputs,hlen,hprefix,?_⟩
    rw [← hagree output hout]
    exact haccept
  · rintro ⟨inputs,hlen,hprefix,haccept⟩
    have hv : validGates inputs.length gates := by simpa [hlen] using hvalid
    have heq := simulate_equations inputs gates hv
    refine ⟨wire (simulate inputs gates),?_,?_,haccept⟩
    · apply (Fixed_congr (wire inputs) (wire (simulate inputs gates)) 0 fixed ?_).1 hprefix
      intro i _ hi
      symm
      exact wire_simulate inputs gates i (by rw [hlen]; omega)
    · simpa [hlen] using heq

theorem fixed_sat_compiled_iff (fixed : List Bool) (free output : Nat) (gates : List Gate)
    (hvalid : validGates (fixed.length+free) gates) (hout : output < fixed.length+free+gates.length) :
    sat (BitstringEncoding.bitEncode (compileFixed fixed free output gates)) = true ↔
      ∃ inputs : List Bool, inputs.length = fixed.length+free ∧ Fixed (wire inputs) 0 fixed ∧
        wire (simulate inputs gates) output = true := by
  rw [sat_encode_correct]
  exact fixed_circuit_satisfiable_iff fixed free output gates hvalid hout

theorem fixInputs_length (offset : Nat) (bits : List Bool) :
    (fixInputs offset bits).length = bits.length := by
  induction bits generalizing offset with
  | nil => rfl
  | cons b bs ih => simp [fixInputs,ih]

theorem fixInputs_clause_length (offset : Nat) (bits : List Bool) :
    ∀ c ∈ fixInputs offset bits, c.length ≤ 3 := by
  induction bits generalizing offset with
  | nil => simp [fixInputs]
  | cons b bs ih =>
    intro c hc
    simp only [fixInputs,List.mem_cons] at hc
    rcases hc with rfl | hc
    · simp
    · exact ih (offset+1) c hc

theorem fixInputs_variable_bound (offset : Nat) (bits : List Bool) :
    ∀ c ∈ fixInputs offset bits, ∀ lit ∈ c, lit.1 < offset+bits.length := by
  induction bits generalizing offset with
  | nil => simp [fixInputs]
  | cons b bs ih =>
    intro c hc lit hl
    simp only [fixInputs,List.mem_cons] at hc
    rcases hc with rfl | hc
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
      subst lit
      simp only [List.length_cons]
      omega
    · have h := ih (offset+1) c hc lit hl
      simp only [List.length_cons]
      omega

theorem formula_encoded_length_le (f : Formula) (bound : Nat)
    (hclauses : ∀ c ∈ f, c.length ≤ 3)
    (hvars : ∀ c ∈ f, ∀ lit ∈ c, lit.1 ≤ bound) :
    (BitstringEncoding.bitEncode f).length ≤ f.length*(24*bound+31) := by
  have hc : ∀ c ∈ f, (BitstringEncoding.delimit (BitstringEncoding.bitEncode c)).length ≤ 24*bound+31 := by
    intro c hmem
    have he := clause_encoded_length_le c bound (hvars c hmem)
    rw [BitstringEncoding.length_delimit]
    have hm := Nat.mul_le_mul_right (4*bound+5) (hclauses c hmem)
    omega
  have hsum := List.sum_le_sum (l := f) (f := fun c => (BitstringEncoding.delimit (BitstringEncoding.bitEncode c)).length)
    (g := fun _ => 24*bound+31) hc
  change (((f.map (fun c : Clause => BitstringEncoding.bitEncode c)).map BitstringEncoding.delimit).flatten).length ≤ _
  simp only [List.length_flatten,List.map_map]
  change (f.map (fun c => (BitstringEncoding.delimit (BitstringEncoding.bitEncode c)).length)).sum ≤ _
  simpa only [List.map_const',List.sum_replicate_nat] using hsum

/-- Explicit encoded-size bound for the fixed-input circuit reduction. -/
theorem compileFixed_encoded_length (fixed : List Bool) (free output : Nat) (gates : List Gate)
    (hvalid : validGates (fixed.length+free) gates) (hout : output < fixed.length+free+gates.length) :
    (BitstringEncoding.bitEncode (compileFixed fixed free output gates)).length ≤
      (fixed.length+3*gates.length+1)*(24*(fixed.length+free+gates.length)+31) := by
  let f := compileFixed fixed free output gates
  let bound := fixed.length+free+gates.length
  have hc : ∀ c ∈ f, c.length ≤ 3 := by
    intro c hmem
    simp only [f,compileFixed,List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · exact fixInputs_clause_length 0 fixed c hmem
    · exact compile_clause_length (fixed.length+free) output gates c hmem
  have hv : ∀ c ∈ f, ∀ lit ∈ c, lit.1 ≤ bound := by
    intro c hmem lit hl
    simp only [f,compileFixed,List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · have h := fixInputs_variable_bound 0 fixed c hmem lit hl
      dsimp [bound]
      omega
    · exact compile_variable_bound (fixed.length+free) output gates hvalid hout c hmem lit hl
  have hlen : f.length ≤ fixed.length+3*gates.length+1 := by
    dsimp [f,compileFixed]
    rw [List.length_append,fixInputs_length]
    have h := compile_length (fixed.length+free) output gates
    omega
  exact le_trans (formula_encoded_length_le f bound hc hv)
    (Nat.mul_le_mul_right (24*bound+31) hlen)

namespace Fixtures
example : validGates 1 [.neg 0, .disj 0 1] := by simp [validGates, validGate]
example : evalFormula (fun _ => false) (compileFixed [false] 0 0 []) = false := by decide
example : evalFormula (fun _ => true) (compileFixed [true] 0 0 []) = true := by decide
example : sat (BitstringEncoding.bitEncode (compile 0 0 [.constant true])) = true := by decide
example : sat (BitstringEncoding.bitEncode (compile 0 0 [.constant false])) = false := by decide
example : (evalGate (wire (simulate [true] [.neg 0])) (.conj 0 1)) = false := by decide
example : (evalGate (wire (simulate [true] [.neg 0])) (.disj 0 1)) = true := by decide
example : sat (BitstringEncoding.bitEncode (compile 1 0 [])) = true := by decide
end Fixtures

end Shared.ComplexityBridge.CircuitCNF
