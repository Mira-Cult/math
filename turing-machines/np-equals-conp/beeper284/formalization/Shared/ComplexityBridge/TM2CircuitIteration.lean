import Shared.ComplexityBridge.TM2CircuitCopy
import Shared.ComplexityBridge.CircuitRelocateComputability
import Shared.ComplexityBridge.TM2PolynomialFold
import Mathlib.Data.Nat.Size

set_option backward.isDefEq.respectTransparency false

/-! One charged unroller iteration with an explicit unary width, including
preserved parameters and the accumulated output gate list. -/
namespace Shared.ComplexityBridge.TM2CircuitIteration
open Shared.ComplexityBridge
open Shared.ComplexityBridge.CircuitCNF
open Shared.ComplexityBridge.CircuitRelocateComputability

abbrev Parameters := (List Bool × List Gate) × List Nat
abbrev State := Nat × List Nat × List Gate
abbrev Work := Parameters × State

def copyArgs (w : Work) : TM2CircuitCopy.Input :=
  ((w.1.1.1,w.2.1),((w.2.2.1,w.1.1.2),w.1.2))

def advance (w : Work) : Work :=
  let c := TM2CircuitCopy.copy (copyArgs w)
  (w.1,(w.2.1+w.1.1.2.length,c.2,w.2.2.2++c.1))

def step (p : Work × Bool) : Work := advance p.1

theorem advance_isPolyTime : ComplexityTheory.IsPolyTime advance := by
  let param : Work → Parameters := fun w => w.1
  let state : Work → State := fun w => w.2
  let pg : Work → List Bool × List Gate := fun w => w.1.1
  let width : Work → List Bool := fun w => w.1.1.1
  let gates : Work → List Gate := fun w => w.1.1.2
  let outputs : Work → List Nat := fun w => w.1.2
  let base : Work → Nat := fun w => w.2.1
  let stail : Work → List Nat × List Gate := fun w => w.2.2
  let inputs : Work → List Nat := fun w => w.2.2.1
  let acc : Work → List Gate := fun w => w.2.2.2
  let args : Work → TM2CircuitCopy.Input := copyArgs
  let copied : Work → List Gate × List Nat := fun w => TM2CircuitCopy.copy (args w)
  let frag : Work → List Gate := fun w => (copied w).1
  let refs : Work → List Nat := fun w => (copied w).2
  let count : Work → Nat := fun w => (gates w).length
  let nextBase : Work → Nat := fun w => base w+count w
  let appended : Work → List Gate := fun w => acc w++frag w
  let after : Work → State := fun w => (nextBase w,refs w,appended w)
  have hp : ComplexityTheory.IsPolyTime param := TM2PairFirst.first_isPolyTime
  have hs : ComplexityTheory.IsPolyTime state := TM2GuardAllStep.second_isPolyTime
  have hpg : ComplexityTheory.IsPolyTime pg := TM2Compose.isPolyTime_comp param (fun p : Parameters => p.1) hp TM2PairFirst.first_isPolyTime
  have hw : ComplexityTheory.IsPolyTime width := TM2Compose.isPolyTime_comp pg (fun p : List Bool × List Gate => p.1) hpg TM2PairFirst.first_isPolyTime
  have hg : ComplexityTheory.IsPolyTime gates := TM2Compose.isPolyTime_comp pg (fun p : List Bool × List Gate => p.2) hpg TM2GuardAllStep.second_isPolyTime
  have ho : ComplexityTheory.IsPolyTime outputs := TM2Compose.isPolyTime_comp param (fun p : Parameters => p.2) hp TM2GuardAllStep.second_isPolyTime
  have hb : ComplexityTheory.IsPolyTime base := TM2Compose.isPolyTime_comp state (fun s : State => s.1) hs TM2PairFirst.first_isPolyTime
  have hst : ComplexityTheory.IsPolyTime stail := TM2Compose.isPolyTime_comp state (fun s : State => s.2) hs TM2GuardAllStep.second_isPolyTime
  have hin : ComplexityTheory.IsPolyTime inputs := TM2Compose.isPolyTime_comp stail (fun p : List Nat × List Gate => p.1) hst TM2PairFirst.first_isPolyTime
  have hacc : ComplexityTheory.IsPolyTime acc := TM2Compose.isPolyTime_comp stail (fun p : List Nat × List Gate => p.2) hst TM2GuardAllStep.second_isPolyTime
  have ha : ComplexityTheory.IsPolyTime args := TM2GuardAllStep.pair_isPolyTime (fun w => (width w,base w))
    (fun w => ((inputs w,gates w),outputs w)) (TM2GuardAllStep.pair_isPolyTime width base hw hb)
    (TM2GuardAllStep.pair_isPolyTime (fun w => (inputs w,gates w)) outputs (TM2GuardAllStep.pair_isPolyTime inputs gates hin hg) ho)
  have hc : ComplexityTheory.IsPolyTime copied := TM2Compose.isPolyTime_comp args TM2CircuitCopy.copy ha TM2CircuitCopy.copy_isPolyTime
  have hfrag : ComplexityTheory.IsPolyTime frag := TM2Compose.isPolyTime_comp copied (fun p : List Gate × List Nat => p.1) hc TM2PairFirst.first_isPolyTime
  have hrefs : ComplexityTheory.IsPolyTime refs := TM2Compose.isPolyTime_comp copied (fun p : List Gate × List Nat => p.2) hc TM2GuardAllStep.second_isPolyTime
  have hcount : ComplexityTheory.IsPolyTime count := TM2Compose.isPolyTime_comp gates List.length hg TM2BinaryListLength.length_isPolyTime
  have hbase : ComplexityTheory.IsPolyTime nextBase := TM2Compose.isPolyTime_comp (fun w => (base w,count w)) CNFBinaryPairAdd.addPair
    (TM2GuardAllStep.pair_isPolyTime base count hb hcount) CNFBinaryPairAdd.addPair_isPolyTime
  have happ : ComplexityTheory.IsPolyTime appended := TM2RowGates.append_isPolyTime acc frag hacc hfrag
  have hafter : ComplexityTheory.IsPolyTime after := TM2GuardAllStep.pair_isPolyTime nextBase (fun w => (refs w,appended w)) hbase
    (TM2GuardAllStep.pair_isPolyTime refs appended hrefs happ)
  have h := TM2GuardAllStep.pair_isPolyTime param after hp hafter
  change ComplexityTheory.IsPolyTime advance at h
  exact h

theorem step_isPolyTime : ComplexityTheory.IsPolyTime step :=
  TM2Compose.isPolyTime_comp (fun p : Work × Bool => p.1) advance TM2PairFirst.first_isPolyTime advance_isPolyTime

/-- When the fixed template is valid and output references are in range, the
charged iteration agrees exactly with the original unroller's iteration. -/
theorem advance_correct (tokens : List Bool) (gates : List Gate) (outputs : List Nat) (s : State)
    (hv : validGates tokens.length gates)
    (ho : ∀ o ∈ outputs, o < tokens.length+gates.length) :
    advance (((tokens,gates),outputs),s) =
      (((tokens,gates),outputs), unrollStep (tokens.length,gates,outputs) s) := by
  have h := TM2CircuitCopy.copy_correct tokens s.1 s.2.1 gates outputs hv ho
  simp only [advance,copyArgs,unrollStep,h]

/-- Folding any unary token list corresponds to exactly that many source
unroller iterations. Token values are irrelevant; their length is charged. -/
theorem fold_correct (tokens : List Bool) (gates : List Gate) (outputs : List Nat) (s : State)
    (hv : validGates tokens.length gates)
    (ho : ∀ o ∈ outputs, o < tokens.length+gates.length) (clock : List Bool) :
    TM2PolynomialFold.fold step (((tokens,gates),outputs),s) clock =
      (((tokens,gates),outputs), (unrollStep (tokens.length,gates,outputs))^[clock.length] s) := by
  induction clock generalizing s with
  | nil => simp [TM2PolynomialFold.fold]
  | cons b clock ih =>
    change TM2PolynomialFold.fold step (step ((((tokens,gates),outputs),s),b)) clock = _
    rw [show step ((((tokens,gates),outputs),s),b) =
      (((tokens,gates),outputs), unrollStep (tokens.length,gates,outputs) s) by
        exact advance_correct tokens gates outputs s hv ho]
    rw [ih]
    simp [Function.iterate_succ_apply]

/-- These size invariants hold even for malformed or non-valid circuit
inputs: the bounded workers remain total and each copy emits one gate per
input gate and one reference per requested output. -/
theorem advance_base (w : Work) : (advance w).2.1 = w.2.1+w.1.1.2.length := rfl

theorem advance_refs_length (w : Work) : (advance w).2.2.1.length = w.1.2.length := by
  simp [advance,copyArgs,TM2CircuitCopy.copy,TM2BoundedNextRefs.next,TM2ContextMapGeneric.contextMap]

theorem advance_gates_length (w : Work) :
    (advance w).2.2.2.length = w.2.2.2.length+w.1.1.2.length := by
  simp [advance,copyArgs,TM2CircuitCopy.copy,TM2BoundedGateRename.relocate,TM2ContextMapGeneric.contextMap]

theorem fold_base (p : Parameters) (s : State) (clock : List Bool) :
    (TM2PolynomialFold.fold step (p,s) clock).2.1 = s.1+clock.length*p.1.2.length := by
  induction clock generalizing s with
  | nil => simp [TM2PolynomialFold.fold]
  | cons b clock ih =>
    change (TM2PolynomialFold.fold step (advance (p,s)) clock).2.1 = _
    change (TM2PolynomialFold.fold step (p,(advance (p,s)).2) clock).2.1 = _
    rw [ih,advance_base]
    simp only [List.length_cons,Nat.succ_mul]
    omega

theorem fold_gates_length (p : Parameters) (s : State) (clock : List Bool) :
    (TM2PolynomialFold.fold step (p,s) clock).2.2.2.length = s.2.2.length+clock.length*p.1.2.length := by
  induction clock generalizing s with
  | nil => simp [TM2PolynomialFold.fold]
  | cons b clock ih =>
    change (TM2PolynomialFold.fold step (advance (p,s)) clock).2.2.2.length = _
    change (TM2PolynomialFold.fold step (p,(advance (p,s)).2) clock).2.2.2.length = _
    rw [ih,advance_gates_length]
    simp only [List.length_cons,Nat.succ_mul]
    omega

theorem fold_refs_length (p : Parameters) (s : State) (clock : List Bool) (h : clock ≠ []) :
    (TM2PolynomialFold.fold step (p,s) clock).2.2.1.length = p.2.length := by
  cases clock with
  | nil => contradiction
  | cons b clock =>
    cases clock with
    | nil => simpa [TM2PolynomialFold.fold,step] using advance_refs_length (p,s)
    | cons c rest =>
      have hne : c::rest ≠ [] := by simp
      have ih := fold_refs_length p (advance (p,s)).2 (c::rest) hne
      change (TM2PolynomialFold.fold step (p,(advance (p,s)).2) (c::rest)).2.2.1.length = p.2.length
      exact ih

/-- A default-zero lookup cannot exceed an upper bound on every supplied
reference. This bound does not assume that the index is in range. -/
theorem getD_bound (xs : List Nat) (index bound : Nat) (h : ∀ x ∈ xs, x ≤ bound) :
    (xs[index]?).getD 0 ≤ bound := by
  induction xs generalizing index with
  | nil => simp
  | cons x xs ih =>
    cases index with
    | zero => simpa using h x (by simp)
    | succ index =>
      have ht : ∀ y ∈ xs, y ≤ bound := by intro y hy; exact h y (by simp [hy])
      simpa using ih index ht

/-- The total bounded remapper cannot introduce a reference larger than the
old reference bound plus the current base and unary budget length. -/
theorem remap_value_bound (budget : List Bool) (width base : Nat) (refs : List Nat) (index bound : Nat)
    (h : ∀ x ∈ refs, x ≤ bound) :
    TM2BoundedRemap.remap (budget,((width,base),(refs,index))) ≤ bound+base+budget.length := by
  change (if TM2BoundedWitnessGuard.guard (TM2BoundedUnary.expand (budget,width),index) then
    (refs[index]?).getD 0 else base + TM2BoundedSubtract.subtract (budget,(index,width))) ≤ _
  split
  · have hh := getD_bound refs index bound h
    omega
  · have hh := TM2BoundedSubtract.subtract_correct budget index width
    have hm : min index budget.length ≤ budget.length := Nat.min_le_right _ _
    omega

/-- Every reference after one iteration has a uniform numeric bound, even
when the template is invalid and the bounded remapper clamps its inputs. -/
theorem advance_refs_bound (p : Parameters) (s : State) (bound : Nat)
    (h : ∀ x ∈ s.2.1, x ≤ bound) :
    ∀ x ∈ (advance (p,s)).2.2.1, x ≤ bound+s.1+p.1.1.length+p.1.2.length := by
  intro x hx
  change x ∈ TM2BoundedNextRefs.next
    ((TM2CircuitCopy.budget (copyArgs (p,s)),((p.1.1.length,s.1),s.2.1)),p.2) at hx
  simp only [TM2BoundedNextRefs.next,TM2ContextMapGeneric.contextMap,List.mem_map] at hx
  obtain ⟨i,_,rfl⟩ := hx
  have hh := remap_value_bound (TM2CircuitCopy.budget (copyArgs (p,s))) p.1.1.length s.1 s.2.1 i bound h
  simpa [TM2BoundedNextRefs.step,TM2CircuitCopy.budget,copyArgs,Nat.add_assoc] using hh

/-- A quadratic numeric envelope for every intermediate reference, valid for
all inputs. This is an invariant toward a separate encoded-size and runtime
proof; the initial reference bound can itself be large in binary. -/
theorem fold_refs_bound (p : Parameters) (s : State) (clock : List Bool) (bound : Nat)
    (h : ∀ x ∈ s.2.1, x ≤ bound) :
    ∀ x ∈ (TM2PolynomialFold.fold step (p,s) clock).2.2.1,
      x ≤ bound+clock.length*(s.1+clock.length*p.1.2.length+p.1.1.length) := by
  induction clock generalizing s bound with
  | nil =>
    intro x hx
    simpa [TM2PolynomialFold.fold] using h x (by simpa [TM2PolynomialFold.fold] using hx)
  | cons b clock ih =>
    let s' := (advance (p,s)).2
    have hs : ∀ x ∈ s'.2.1, x ≤ bound+s.1+p.1.1.length+p.1.2.length :=
      advance_refs_bound p s bound h
    intro x hx
    change x ∈ (TM2PolynomialFold.fold step (p,s') clock).2.2.1 at hx
    have hh := ih s' (bound+s.1+p.1.1.length+p.1.2.length) hs x hx
    have hb : s'.1 = s.1+p.1.2.length := by exact advance_base (p,s)
    rw [hb] at hh
    simp only [List.length_cons]
    nlinarith

/-- Renaming any gate preserves a uniform bound on each referenced wire. -/
theorem rename_refs_bound (budget : List Bool) (width base : Nat) (refs : List Nat) (g : Gate) (bound : Nat)
    (h : ∀ x ∈ refs, x ≤ bound) :
    ∀ i, TM2BoundedGateRename.refers
      (TM2BoundedGateRename.rename ((budget,((width,base),refs)),g)) i →
        i ≤ bound+base+budget.length := by
  intro i hi
  cases g with
  | constant b => simp [TM2BoundedGateRename.rename,CircuitRelocate.renameGate,TM2BoundedGateRename.refers] at hi
  | neg x =>
    simp only [TM2BoundedGateRename.rename,CircuitRelocate.renameGate,TM2BoundedGateRename.refers] at hi
    subst i
    exact remap_value_bound budget width base refs x bound h
  | conj x y =>
    simp only [TM2BoundedGateRename.rename,CircuitRelocate.renameGate,TM2BoundedGateRename.refers] at hi
    rcases hi with hx | hy
    · subst i; exact remap_value_bound budget width base refs x bound h
    · subst i; exact remap_value_bound budget width base refs y bound h
  | disj x y =>
    simp only [TM2BoundedGateRename.rename,CircuitRelocate.renameGate,TM2BoundedGateRename.refers] at hi
    rcases hi with hx | hy
    · subst i; exact remap_value_bound budget width base refs x bound h
    · subst i; exact remap_value_bound budget width base refs y bound h

theorem advance_gate_refs_bound (p : Parameters) (s : State) (referenceBound gateBound : Nat)
    (hr : ∀ x ∈ s.2.1, x ≤ referenceBound)
    (hg : ∀ g ∈ s.2.2, ∀ i, TM2BoundedGateRename.refers g i → i ≤ gateBound) :
    ∀ g ∈ (advance (p,s)).2.2.2, ∀ i, TM2BoundedGateRename.refers g i →
      i ≤ max gateBound (referenceBound+s.1+p.1.1.length+p.1.2.length) := by
  intro g hm i hi
  change g ∈ s.2.2 ++ TM2BoundedGateRename.relocate
    ((TM2CircuitCopy.budget (copyArgs (p,s)),((p.1.1.length,s.1),s.2.1)),p.1.2) at hm
  rcases List.mem_append.mp hm with old | new
  · have hh := hg g old i hi
    exact le_trans hh (Nat.le_max_left _ _)
  · simp only [TM2BoundedGateRename.relocate,TM2ContextMapGeneric.contextMap,List.mem_map] at new
    obtain ⟨orig,_,rfl⟩ := new
    have hh := rename_refs_bound (TM2CircuitCopy.budget (copyArgs (p,s))) p.1.1.length s.1 s.2.1 orig referenceBound hr i hi
    simp only [TM2CircuitCopy.budget,copyArgs,List.length_append,List.length_map] at hh
    have hm := Nat.le_max_right gateBound (referenceBound+s.1+p.1.1.length+p.1.2.length)
    omega

/-- One polynomial numeric envelope covers both the live reference list and
every reference in the accumulated gates, even for invalid source circuits.
Translating this envelope to canonical bit lengths remains a separate step. -/
theorem fold_all_refs_bound (p : Parameters) (s : State) (clock : List Bool) (bound : Nat)
    (hr : ∀ x ∈ s.2.1, x ≤ bound)
    (hg : ∀ g ∈ s.2.2, ∀ i, TM2BoundedGateRename.refers g i → i ≤ bound) :
    (∀ x ∈ (TM2PolynomialFold.fold step (p,s) clock).2.2.1,
      x ≤ bound+clock.length*(s.1+clock.length*p.1.2.length+p.1.1.length)) ∧
    (∀ g ∈ (TM2PolynomialFold.fold step (p,s) clock).2.2.2, ∀ i,
      TM2BoundedGateRename.refers g i →
        i ≤ bound+clock.length*(s.1+clock.length*p.1.2.length+p.1.1.length)) := by
  induction clock generalizing s bound with
  | nil => simpa [TM2PolynomialFold.fold] using And.intro hr hg
  | cons b clock ih =>
    let s' := (advance (p,s)).2
    let nextBound := bound+s.1+p.1.1.length+p.1.2.length
    have hs : ∀ x ∈ s'.2.1, x ≤ nextBound := advance_refs_bound p s bound hr
    have hgs : ∀ g ∈ s'.2.2, ∀ i, TM2BoundedGateRename.refers g i → i ≤ nextBound := by
      intro g hm i hi
      have hh := advance_gate_refs_bound p s bound bound hr hg g hm i hi
      have hb : bound ≤ nextBound := by dsimp [nextBound]; omega
      simpa [nextBound,Nat.max_eq_right hb] using hh
    have hh := ih s' nextBound hs hgs
    have hb : s'.1 = s.1+p.1.2.length := by exact advance_base (p,s)
    rw [hb] at hh
    change (∀ x ∈ (TM2PolynomialFold.fold step (p,s') clock).2.2.1, _) ∧
      (∀ g ∈ (TM2PolynomialFold.fold step (p,s') clock).2.2.2, ∀ i, _ → _)
    constructor
    · intro x hx
      have hx' := hh.1 x hx
      simp only [List.length_cons]
      dsimp [nextBound] at hx'
      nlinarith
    · intro g hm i hi
      have hi' := hh.2 g hm i hi
      simp only [List.length_cons]
      dsimp [nextBound] at hi'
      nlinarith

/-- Tight bound: the old reference maximum is not added to the binary base. -/
theorem remap_value_bound_max (budget : List Bool) (width base : Nat) (refs : List Nat) (index bound : Nat)
    (h : ∀ x ∈ refs, x ≤ bound) :
    TM2BoundedRemap.remap (budget,((width,base),(refs,index))) ≤ max bound (base+budget.length) := by
  change (if TM2BoundedWitnessGuard.guard (TM2BoundedUnary.expand (budget,width),index) then
    (refs[index]?).getD 0 else base + TM2BoundedSubtract.subtract (budget,(index,width))) ≤ _
  split
  · exact le_trans (getD_bound refs index bound h) (Nat.le_max_left _ _)
  · have hh := TM2BoundedSubtract.subtract_correct budget index width
    have hm : min index budget.length ≤ budget.length := Nat.min_le_right _ _
    have hmax := Nat.le_max_right bound (base+budget.length)
    omega

theorem advance_all_refs_bound_max (p : Parameters) (s : State) (bound : Nat)
    (hr : ∀ x ∈ s.2.1, x ≤ bound)
    (hg : ∀ g ∈ s.2.2, ∀ i, TM2BoundedGateRename.refers g i → i ≤ bound) :
    (∀ x ∈ (advance (p,s)).2.2.1, x ≤ max bound (s.1+p.1.1.length+p.1.2.length)) ∧
    (∀ g ∈ (advance (p,s)).2.2.2, ∀ i, TM2BoundedGateRename.refers g i →
      i ≤ max bound (s.1+p.1.1.length+p.1.2.length)) := by
  let budget := TM2CircuitCopy.budget (copyArgs (p,s))
  have hlen : budget.length = p.1.1.length+p.1.2.length := by simp [budget,TM2CircuitCopy.budget,copyArgs]
  have hrename (g : Gate) (i : Nat) :
      TM2BoundedGateRename.refers
        (TM2BoundedGateRename.rename ((budget,((p.1.1.length,s.1),s.2.1)),g)) i →
      i ≤ max bound (s.1+budget.length) := by
    intro hi
    cases g with
    | constant b => simp [TM2BoundedGateRename.rename,CircuitRelocate.renameGate,TM2BoundedGateRename.refers] at hi
    | neg x =>
      simp only [TM2BoundedGateRename.rename,CircuitRelocate.renameGate,TM2BoundedGateRename.refers] at hi
      subst i
      exact remap_value_bound_max budget p.1.1.length s.1 s.2.1 x bound hr
    | conj x y =>
      simp only [TM2BoundedGateRename.rename,CircuitRelocate.renameGate,TM2BoundedGateRename.refers] at hi
      rcases hi with hx | hy
      · subst i; exact remap_value_bound_max budget p.1.1.length s.1 s.2.1 x bound hr
      · subst i; exact remap_value_bound_max budget p.1.1.length s.1 s.2.1 y bound hr
    | disj x y =>
      simp only [TM2BoundedGateRename.rename,CircuitRelocate.renameGate,TM2BoundedGateRename.refers] at hi
      rcases hi with hx | hy
      · subst i; exact remap_value_bound_max budget p.1.1.length s.1 s.2.1 x bound hr
      · subst i; exact remap_value_bound_max budget p.1.1.length s.1 s.2.1 y bound hr
  constructor
  · intro x hx
    change x ∈ TM2BoundedNextRefs.next ((budget,((p.1.1.length,s.1),s.2.1)),p.2) at hx
    simp only [TM2BoundedNextRefs.next,TM2ContextMapGeneric.contextMap,List.mem_map] at hx
    obtain ⟨i,_,rfl⟩ := hx
    have hh := remap_value_bound_max budget p.1.1.length s.1 s.2.1 i bound hr
    simpa [TM2BoundedNextRefs.step,hlen,Nat.add_assoc] using hh
  · intro g hm i hi
    change g ∈ s.2.2 ++ TM2BoundedGateRename.relocate ((budget,((p.1.1.length,s.1),s.2.1)),p.1.2) at hm
    rcases List.mem_append.mp hm with old | new
    · exact le_trans (hg g old i hi) (Nat.le_max_left _ _)
    · simp only [TM2BoundedGateRename.relocate,TM2ContextMapGeneric.contextMap,List.mem_map] at new
      obtain ⟨orig,_,rfl⟩ := new
      have hh := hrename orig i hi
      simpa [hlen,Nat.add_assoc] using hh

theorem fold_all_refs_max (p : Parameters) (s : State) (clock : List Bool) (bound : Nat)
    (hr : ∀ x ∈ s.2.1, x ≤ bound)
    (hg : ∀ g ∈ s.2.2, ∀ i, TM2BoundedGateRename.refers g i → i ≤ bound) :
    (∀ x ∈ (TM2PolynomialFold.fold step (p,s) clock).2.2.1,
      x ≤ max bound (s.1+clock.length*p.1.2.length+p.1.1.length)) ∧
    (∀ g ∈ (TM2PolynomialFold.fold step (p,s) clock).2.2.2, ∀ i,
      TM2BoundedGateRename.refers g i →
        i ≤ max bound (s.1+clock.length*p.1.2.length+p.1.1.length)) := by
  induction clock generalizing s bound with
  | nil =>
    constructor
    · intro x hx
      have hh := hr x (by simpa [TM2PolynomialFold.fold] using hx)
      simpa using le_trans hh (Nat.le_max_left bound (s.1+0*p.1.2.length+p.1.1.length))
    · intro g hm i hi
      have hh := hg g (by simpa [TM2PolynomialFold.fold] using hm) i hi
      simpa using le_trans hh (Nat.le_max_left bound (s.1+0*p.1.2.length+p.1.1.length))
  | cons b clock ih =>
    let s' := (advance (p,s)).2
    let nextBound := max bound (s.1+p.1.1.length+p.1.2.length)
    have hs := advance_all_refs_bound_max p s bound hr hg
    have hh := ih s' nextBound hs.1 hs.2
    have hb : s'.1 = s.1+p.1.2.length := by exact advance_base (p,s)
    rw [hb] at hh
    have hbound : max nextBound (s.1+p.1.2.length+clock.length*p.1.2.length+p.1.1.length) ≤
        max bound (s.1+(clock.length+1)*p.1.2.length+p.1.1.length) := by
      apply Nat.max_le.mpr
      constructor
      · dsimp [nextBound]
        apply Nat.max_le.mpr
        constructor
        · exact Nat.le_max_left _ _
        · have hmax := Nat.le_max_right bound (s.1+(clock.length+1)*p.1.2.length+p.1.1.length)
          nlinarith
      · have hmax := Nat.le_max_right bound (s.1+(clock.length+1)*p.1.2.length+p.1.1.length)
        nlinarith
    change (∀ x ∈ (TM2PolynomialFold.fold step (p,s') clock).2.2.1, _) ∧
      (∀ g ∈ (TM2PolynomialFold.fold step (p,s') clock).2.2.2, ∀ i, _ → _)
    constructor
    · intro x hx
      have h := le_trans (hh.1 x hx) hbound
      simpa only [List.length_cons] using h
    · intro g hm i hi
      have h := le_trans (hh.2 g hm i hi) hbound
      simpa only [List.length_cons] using h

/-- Monotonicity and the binary-successor bound turn the numeric envelope
into a bound on binary representation length without expanding its base. -/
theorem size_le_max_add (x bound base delta N : Nat)
    (hx : x ≤ max bound (base+delta)) (hb : Nat.size bound ≤ N) (ha : Nat.size base ≤ N) :
    Nat.size x ≤ N+delta := by
  have hinc := TM2GuardAllStep.index_bits_add base delta
  change (Computability.encodeNat (base+delta)).length ≤ (Computability.encodeNat base).length+delta at hinc
  rw [CNFEncodingComputability.encodeNat_bits,CNFEncodingComputability.encodeNat_bits,
    Nat.size_eq_bits_len,Nat.size_eq_bits_len] at hinc
  have hmax : Nat.size (max bound (base+delta)) ≤ N+delta := by
    by_cases h : bound ≤ base+delta
    · rw [Nat.max_eq_right h]
      omega
    · rw [Nat.max_eq_left (by omega : base+delta ≤ bound)]
      omega
  exact le_trans (Nat.size_le_size hx) hmax

/-- Binary sizes of all intermediate references grow at most by the number
of generated gates plus the unary width; no numeric value is treated as a
unit-cost integer. -/
theorem fold_all_refs_bit_bound (p : Parameters) (s : State) (clock : List Bool) (bound N : Nat)
    (hr : ∀ x ∈ s.2.1, x ≤ bound)
    (hg : ∀ g ∈ s.2.2, ∀ i, TM2BoundedGateRename.refers g i → i ≤ bound)
    (hb : Nat.size bound ≤ N) (hs : Nat.size s.1 ≤ N) :
    (∀ x ∈ (TM2PolynomialFold.fold step (p,s) clock).2.2.1,
      Nat.size x ≤ N+clock.length*p.1.2.length+p.1.1.length) ∧
    (∀ g ∈ (TM2PolynomialFold.fold step (p,s) clock).2.2.2, ∀ i,
      TM2BoundedGateRename.refers g i →
        Nat.size i ≤ N+clock.length*p.1.2.length+p.1.1.length) := by
  have h := fold_all_refs_max p s clock bound hr hg
  let delta := clock.length*p.1.2.length+p.1.1.length
  constructor
  · intro x hx
    have hh := h.1 x hx
    have hx' : x ≤ max bound (s.1+delta) := by simpa [delta,Nat.add_assoc] using hh
    have hz := size_le_max_add x bound s.1 delta N hx' hb hs
    simpa [delta,Nat.add_assoc] using hz
  · intro g hm i hi
    have hh := h.2 g hm i hi
    have hx' : i ≤ max bound (s.1+delta) := by simpa [delta,Nat.add_assoc] using hh
    have hz := size_le_max_add i bound s.1 delta N hx' hb hs
    simpa [delta,Nat.add_assoc] using hz

/-- Each component's encoding fits inside the canonical pair encoding. -/
theorem pair_first_size {α β : Type} [BitstringEncoding α] [BitstringEncoding β] (p : α × β) :
    (BitstringEncoding.bitEncode p.1).length ≤ (BitstringEncoding.bitEncode p).length := by
  change (BitstringEncoding.bitEncode p.1).length ≤
    (BitstringEncoding.delimit (BitstringEncoding.bitEncode p.1) ++ BitstringEncoding.bitEncode p.2).length
  simp only [List.length_append,BitstringEncoding.length_delimit]
  omega

theorem pair_second_size {α β : Type} [BitstringEncoding α] [BitstringEncoding β] (p : α × β) :
    (BitstringEncoding.bitEncode p.2).length ≤ (BitstringEncoding.bitEncode p).length := by
  change (BitstringEncoding.bitEncode p.2).length ≤
    (BitstringEncoding.delimit (BitstringEncoding.bitEncode p.1) ++ BitstringEncoding.bitEncode p.2).length
  simp only [List.length_append]
  omega

theorem nat_size_encoding (n : Nat) : Nat.size n = (BitstringEncoding.bitEncode n).length := by
  change Nat.size n = (Computability.encodeNat n).length
  rw [CNFEncodingComputability.encodeNat_bits,Nat.size_eq_bits_len]

theorem gate_ref_size (g : Gate) (i : Nat) (hi : TM2BoundedGateRename.refers g i) :
    Nat.size i ≤ (BitstringEncoding.bitEncode g).length := by
  let code := TM2GateEncoding.encode g
  have hc : (BitstringEncoding.bitEncode code).length = (BitstringEncoding.bitEncode g).length := by
    exact congrArg List.length (TM2GateEncoding.encode_bits g).symm
  have hp : (BitstringEncoding.bitEncode code.2).length ≤ (BitstringEncoding.bitEncode g).length := by
    rw [←hc]
    exact pair_second_size code
  have hxy : (BitstringEncoding.bitEncode code.2.2).length ≤ (BitstringEncoding.bitEncode g).length :=
    le_trans (pair_second_size code.2) hp
  have hx : Nat.size code.2.2.1 ≤ (BitstringEncoding.bitEncode g).length := by
    rw [nat_size_encoding]
    exact le_trans (pair_first_size code.2.2) hxy
  have hy : Nat.size code.2.2.2 ≤ (BitstringEncoding.bitEncode g).length := by
    rw [nat_size_encoding]
    exact le_trans (pair_second_size code.2.2) hxy
  cases g with
  | constant b => simp [TM2BoundedGateRename.refers] at hi
  | neg x =>
    simp only [TM2BoundedGateRename.refers] at hi
    subst i
    simpa [code,TM2GateEncoding.encode] using hx
  | conj x y =>
    simp only [TM2BoundedGateRename.refers] at hi
    rcases hi with rfl | rfl
    · simpa [code,TM2GateEncoding.encode] using hx
    · simpa [code,TM2GateEncoding.encode] using hy
  | disj x y =>
    simp only [TM2BoundedGateRename.refers] at hi
    rcases hi with rfl | rfl
    · simpa [code,TM2GateEncoding.encode] using hx
    · simpa [code,TM2GateEncoding.encode] using hy

/-- Every original live or accumulated reference is smaller than `2^N`,
where N is the serialized initial state length. -/
theorem initial_state_bounds (s : State) :
    let N := (BitstringEncoding.bitEncode s).length
    Nat.size s.1 ≤ N ∧
    (∀ x ∈ s.2.1, x ≤ 2^N) ∧
    (∀ g ∈ s.2.2, ∀ i, TM2BoundedGateRename.refers g i → i ≤ 2^N) := by
  let N := (BitstringEncoding.bitEncode s).length
  have hb : Nat.size s.1 ≤ N := by rw [nat_size_encoding]; exact pair_first_size s
  have htail : (BitstringEncoding.bitEncode s.2).length ≤ N := pair_second_size s
  have hrefs : (BitstringEncoding.bitEncode s.2.1).length ≤ N := le_trans (pair_first_size s.2) htail
  have hgates : (BitstringEncoding.bitEncode s.2.2).length ≤ N := le_trans (pair_second_size s.2) htail
  refine ⟨hb,?_,?_⟩
  · intro x hx
    have hsize : Nat.size x ≤ N := by
      rw [nat_size_encoding]
      exact le_trans (TM2MapSizeBounds.element_length_le hx) hrefs
    exact Nat.le_of_lt (Nat.size_le.mp hsize)
  · intro g hm i hi
    have hsize : Nat.size i ≤ N := le_trans (gate_ref_size g i hi)
      (le_trans (TM2MapSizeBounds.element_length_le hm) hgates)
    exact Nat.le_of_lt (Nat.size_le.mp hsize)

/-- The initial envelope is derived from serialized bits, so this bound
remains polynomial even when input references denote very large integers. -/
theorem fold_initial_bit_bound (p : Parameters) (s : State) (clock : List Bool) :
    let N := (BitstringEncoding.bitEncode s).length
    (∀ x ∈ (TM2PolynomialFold.fold step (p,s) clock).2.2.1,
      Nat.size x ≤ N+1+clock.length*p.1.2.length+p.1.1.length) ∧
    (∀ g ∈ (TM2PolynomialFold.fold step (p,s) clock).2.2.2, ∀ i,
      TM2BoundedGateRename.refers g i →
        Nat.size i ≤ N+1+clock.length*p.1.2.length+p.1.1.length) := by
  let N := (BitstringEncoding.bitEncode s).length
  have ⟨hb,hr,hg⟩ := initial_state_bounds s
  have hp : Nat.size (2^N) ≤ N+1 := by rw [Nat.size_pow]
  have hs : Nat.size s.1 ≤ N+1 := by omega
  exact fold_all_refs_bit_bound p s clock (2^N) (N+1) hr hg hp hs

theorem pair_encoding_length {α β : Type} [BitstringEncoding α] [BitstringEncoding β] (p : α × β) :
    (BitstringEncoding.bitEncode p).length = 2*(BitstringEncoding.bitEncode p.1).length+1+
      (BitstringEncoding.bitEncode p.2).length := by
  change (BitstringEncoding.delimit (BitstringEncoding.bitEncode p.1) ++ BitstringEncoding.bitEncode p.2).length = _
  simp [BitstringEncoding.length_delimit]

theorem bool_encoding_length (b : Bool) : (BitstringEncoding.bitEncode b).length = 1 := by cases b <;> rfl

/-- A gate with binary references of at most B bits has a canonical encoding
of at most `3*B+13` bits. -/
theorem gate_encoding_bound (g : Gate) (B : Nat)
    (h : ∀ i, TM2BoundedGateRename.refers g i → Nat.size i ≤ B) :
    (BitstringEncoding.bitEncode g).length ≤ 3*B+13 := by
  let c := TM2GateEncoding.encode g
  have hx : Nat.size c.2.2.1 ≤ B := by
    cases g with
    | constant b => simp [c,TM2GateEncoding.encode]
    | neg x => simpa [c,TM2GateEncoding.encode] using h x rfl
    | conj x y => simpa [c,TM2GateEncoding.encode] using h x (Or.inl rfl)
    | disj x y => simpa [c,TM2GateEncoding.encode] using h x (Or.inl rfl)
  have hy : Nat.size c.2.2.2 ≤ B := by
    cases g with
    | constant b => simp [c,TM2GateEncoding.encode]
    | neg x => simp [c,TM2GateEncoding.encode]
    | conj x y => simpa [c,TM2GateEncoding.encode] using h y (Or.inr rfl)
    | disj x y => simpa [c,TM2GateEncoding.encode] using h y (Or.inr rfl)
  have he : (BitstringEncoding.bitEncode g).length = (BitstringEncoding.bitEncode c).length :=
    congrArg List.length (TM2GateEncoding.encode_bits g)
  rw [he,pair_encoding_length,pair_encoding_length,pair_encoding_length,pair_encoding_length]
  simp only [bool_encoding_length,←nat_size_encoding]
  omega

namespace Fixtures
example : advance ((([true], [.neg 0]),[1]),(1,[0],[])) =
    ((([true], [.neg 0]),[1]),(2,[1],[.neg 0])) := rfl
end Fixtures
end Shared.ComplexityBridge.TM2CircuitIteration
