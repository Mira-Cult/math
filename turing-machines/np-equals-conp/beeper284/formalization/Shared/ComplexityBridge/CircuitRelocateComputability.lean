import Shared.ComplexityBridge.CircuitPairComputability
import Shared.ComplexityBridge.CircuitRelocate

/-! Computability of wire remapping and circuit relocation. No polynomial
machine running-time bound is asserted. -/
namespace Shared.ComplexityBridge.CircuitRelocateComputability

open Shared.ComplexityBridge.CircuitCNF
open Shared.ComplexityBridge.CircuitRelocate
open Shared.ComplexityBridge.CircuitGateComputability
open Shared.ComplexityBridge.CircuitWitness
open Shared.ComplexityBridge.CircuitPairComputability
open Shared.ComplexityBridge.CircuitBounded
open Shared.ComplexityBridge.UnaryBounded
open Shared.Codes.FinitePrograms

/-- Primitive-recursive case analysis over the actual gate type. -/
theorem gateCases_primrec {A B : Type} [Primcodable A] [Primcodable B] {f : A → Gate → B}
    (hc : Primrec₂ (fun a b => f a (.constant b)))
    (hn : Primrec₂ (fun a x => f a (.neg x)))
    (ha : Primrec (fun z : A × (Nat × Nat) => f z.1 (.conj z.2.1 z.2.2)))
    (ho : Primrec (fun z : A × (Nat × Nat) => f z.1 (.disj z.2.1 z.2.2))) : Primrec₂ f := by
  let Inner := (Nat × Nat) ⊕ (Nat × Nat)
  let Middle := Nat ⊕ Inner
  have hi : Primrec (fun z : A × Inner => match z.2 with
      | .inl p => f z.1 (.conj p.1 p.2)
      | .inr p => f z.1 (.disj p.1 p.2)) := by
    apply (Primrec.sumCasesOn Primrec.snd
      (ha.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂
      (ho.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂).of_eq
    intro z; cases z.2 <;> rfl
  have hm : Primrec (fun z : A × Middle => match z.2 with
      | .inl x => f z.1 (.neg x)
      | .inr q => match q with
        | .inl p => f z.1 (.conj p.1 p.2)
        | .inr p => f z.1 (.disj p.1 p.2)) := by
    apply (Primrec.sumCasesOn Primrec.snd
      (hn.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
      (hi.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂).of_eq
    intro z; cases z.2 <;> rfl
  have hcode : Primrec (fun z : A × GateCode => match z.2 with
      | .inl b => f z.1 (.constant b)
      | .inr m => match m with
        | .inl x => f z.1 (.neg x)
        | .inr q => match q with
          | .inl p => f z.1 (.conj p.1 p.2)
          | .inr p => f z.1 (.disj p.1 p.2)) := by
    apply (Primrec.sumCasesOn Primrec.snd
      (hc.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
      (hm.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂).of_eq
    intro z; rcases z with ⟨a,b | (x | (p | p))⟩ <;> rfl
  have h := hcode.comp (Primrec.pair Primrec.fst (gateCode_primrec.comp Primrec.snd))
  apply h.to₂.of_eq
  intro a g
  cases g <;> rfl

abbrev RemapArg := Nat × Nat × List Nat × Nat
abbrev Environment := Nat × Nat × List Nat

theorem remap_primrec : Primrec (fun z : RemapArg => remap z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  have hw : Primrec (fun z : RemapArg => z.1) := Primrec.fst
  have hb : Primrec (fun z : RemapArg => z.2.1) := Primrec.fst.comp Primrec.snd
  have hins : Primrec (fun z : RemapArg => z.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hi : Primrec (fun z : RemapArg => z.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hget := Primrec.option_getD.comp (Primrec.list_getElem?.comp hins hi) (Primrec.const 0)
  exact Primrec.ite (Primrec.nat_lt.comp hi hw) hget (Primrec.nat_add.comp hb (Primrec.nat_sub.comp hi hw))

theorem renameGate_primrec : Primrec₂ (fun (e : Environment) (g : Gate) =>
    renameGate (remap e.1 e.2.1 e.2.2) g) := by
  apply gateCases_primrec
  · exact (constant_primrec.comp Primrec.snd).to₂
  · have h : Primrec (fun z : Environment × Nat => remap z.1.1 z.1.2.1 z.1.2.2 z.2) :=
      remap_primrec.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)))
    exact (neg_primrec.comp h).to₂
  · have h (sel : Nat × Nat → Nat) (hs : Primrec sel) :
        Primrec (fun z : Environment × (Nat × Nat) => remap z.1.1 z.1.2.1 z.1.2.2 (sel z.2)) :=
      remap_primrec.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) (hs.comp Primrec.snd))))
    exact conj_primrec.comp (h Prod.fst Primrec.fst) (h Prod.snd Primrec.snd)
  · have h (sel : Nat × Nat → Nat) (hs : Primrec sel) :
        Primrec (fun z : Environment × (Nat × Nat) => remap z.1.1 z.1.2.1 z.1.2.2 (sel z.2)) :=
      remap_primrec.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) (hs.comp Primrec.snd))))
    exact disj_primrec.comp (h Prod.fst Primrec.fst) (h Prod.snd Primrec.snd)

set_option maxHeartbeats 800000 in
theorem relocate_primrec : Primrec (fun z : Environment × List Gate =>
    relocate z.1.1 z.1.2.1 z.1.2.2 z.2) :=
  Primrec.list_map Primrec.snd (renameGate_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂

theorem nextRefs_primrec : Primrec (fun z : Environment × List Nat =>
    nextRefs z.1.1 z.1.2.1 z.1.2.2 z.2) := by
  have heach : Primrec₂ (fun (z : Environment × List Nat) (i : Nat) =>
      remap z.1.1 z.1.2.1 z.1.2.2 i) := by
    exact (remap_primrec.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) Primrec.snd)))).to₂
  exact Primrec.list_map Primrec.snd heach

abbrev Parameters := Nat × List Gate × List Nat
abbrev State := Nat × List Nat × List Gate

def unrollStep (p : Parameters) (s : State) : State :=
  (s.1+p.2.1.length, nextRefs p.1 s.1 s.2.1 p.2.2,
    s.2.2 ++ relocate p.1 s.1 s.2.1 p.2.1)

theorem unrollStep_primrec : Primrec₂ unrollStep := by
  let A := Parameters × State
  have hw : Primrec (fun z : A => z.1.1) := Primrec.fst.comp Primrec.fst
  have hg : Primrec (fun z : A => z.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have ho : Primrec (fun z : A => z.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hb : Primrec (fun z : A => z.2.1) := Primrec.fst.comp Primrec.snd
  have hi : Primrec (fun z : A => z.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have ha : Primrec (fun z : A => z.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have he : Primrec (fun z : A => (z.1.1,z.2.1,z.2.2.1)) := Primrec.pair hw (Primrec.pair hb hi)
  have hnext := nextRefs_primrec.comp (Primrec.pair he ho)
  have hfrag := relocate_primrec.comp (Primrec.pair he hg)
  exact (Primrec.pair (Primrec.nat_add.comp hb (Primrec.list_length.comp hg))
    (Primrec.pair hnext (Primrec.list_append.comp ha hfrag))).to₂

theorem unroll_iterate (p : Parameters) (s : State) (n : Nat) :
    ((unrollStep p)^[n] s).2.2 = s.2.2 ++ unroll p.1 p.2.1 p.2.2 s.1 s.2.1 n := by
  induction n generalizing s with
  | zero => simp [unroll]
  | succ n ih =>
    rw [Function.iterate_succ_apply,ih]
    simp [unrollStep,unroll,List.append_assoc]

theorem finalRefs_iterate (p : Parameters) (s : State) (n : Nat) :
    ((unrollStep p)^[n] s).2.1 = finalRefs p.1 p.2.1 p.2.2 s.1 s.2.1 n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply,ih]
    rfl

abbrev IterateArg := Parameters × Nat × List Nat × Nat

theorem iteration_primrec : Primrec (fun z : IterateArg =>
    (unrollStep z.1)^[z.2.2.2] (z.2.1,z.2.2.1,[])) := by
  have hp : Primrec (fun z : IterateArg => z.1) := Primrec.fst
  have hb : Primrec (fun z : IterateArg => z.2.1) := Primrec.fst.comp Primrec.snd
  have hi : Primrec (fun z : IterateArg => z.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hn : Primrec (fun z : IterateArg => z.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hinitial := Primrec.pair hb (Primrec.pair hi (Primrec.const ([] : List Gate)))
  have hstep : Primrec₂ (fun (z : IterateArg) (s : State) => unrollStep z.1 s) :=
    (unrollStep_primrec.comp (hp.comp Primrec.fst) Primrec.snd).to₂
  exact Primrec.nat_iterate hn hinitial hstep

theorem unroll_primrec : Primrec (fun z : IterateArg =>
    unroll z.1.1 z.1.2.1 z.1.2.2 z.2.1 z.2.2.1 z.2.2.2) := by
  have h := Primrec.snd.comp (Primrec.snd.comp iteration_primrec)
  apply h.of_eq
  intro z
  simpa using unroll_iterate z.1 (z.2.1,z.2.2.1,[]) z.2.2.2

theorem finalRefs_primrec : Primrec (fun z : IterateArg =>
    finalRefs z.1.1 z.1.2.1 z.1.2.2 z.2.1 z.2.2.1 z.2.2.2) := by
  have h := Primrec.fst.comp (Primrec.snd.comp iteration_primrec)
  apply h.of_eq
  intro z
  exact finalRefs_iterate z.1 (z.2.1,z.2.2.1,[]) z.2.2.2

theorem patchRefs_primrec : Primrec (fun z : Nat × Nat × Nat => patchRefs z.1 z.2.1 z.2.2) := by
  let A := Nat × Nat × Nat
  let B := A × Nat
  have hw : Primrec (fun z : B => z.1.1) := Primrec.fst.comp Primrec.fst
  have hs : Primrec (fun z : B => z.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hc : Primrec (fun z : B => z.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hi : Primrec (fun z : B => z.2) := Primrec.snd
  have cond := (Primrec.nat_le.comp hs hi).and (Primrec.nat_lt.comp hi (Primrec.nat_add.comp hs hc))
  have hmap := Primrec.list_map (Primrec.list_range.comp (Primrec.fst : Primrec (fun z : A => z.1)))
    (Primrec.ite cond (Primrec.nat_add.comp hw (Primrec.nat_sub.comp hi hs)) hi).to₂
  exact hmap

theorem innerWidth_primrec : Primrec (fun z : Decoded => innerWidth z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  have hp : Primrec (fun z : Decoded => z.1) := Primrec.fst
  have hx : Primrec (fun z : Decoded => z.2.1) := Primrec.fst.comp Primrec.snd
  have hn : Primrec (fun z : Decoded => z.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have ht : Primrec (fun z : Decoded => z.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact circuitWidth_primrec.comp (Primrec.pair hp (Primrec.pair (dummyInput_primrec.comp hx hn) ht))

theorem witnessStart_primrec : Primrec (fun z : Decoded => witnessStart z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  have hp : Primrec (fun z : Decoded => z.1) := Primrec.fst
  have hx : Primrec (fun z : Decoded => z.2.1) := Primrec.fst.comp Primrec.snd
  have hn : Primrec (fun z : Decoded => z.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have ht : Primrec (fun z : Decoded => z.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact Primrec.nat_add.comp
    (inputStart_primrec.comp (Primrec.pair hp (Primrec.pair (dummyInput_primrec.comp hx hn) ht)))
    (Primrec.list_length.comp hx)

theorem refs_primrec : Primrec (fun z : Decoded => refs z.1 z.2.1 z.2.2.1 z.2.2.2) :=
  patchRefs_primrec.comp (Primrec.pair innerWidth_primrec
    (Primrec.pair witnessStart_primrec (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))

abbrev CircuitArg := Program × List Bool × Nat

theorem unrollArgs_primrec
    (hg : Primrec (fun z : CircuitArg => updateGates z.1 z.2.1 z.2.2))
    (ho : Primrec (fun z : CircuitArg => updateOutputs z.1 z.2.1 z.2.2)) :
    Primrec (fun z : CircuitArg =>
      ((circuitWidth z.1 z.2.1 z.2.2,updateGates z.1 z.2.1 z.2.2,updateOutputs z.1 z.2.1 z.2.2),
        circuitWidth z.1 z.2.1 z.2.2,List.range (circuitWidth z.1 z.2.1 z.2.2),z.2.2)) := by
  have hf : Primrec (fun z : CircuitArg => z.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.pair (Primrec.pair circuitWidth_primrec (Primrec.pair hg ho))
    (Primrec.pair circuitWidth_primrec
      (Primrec.pair (Primrec.list_range.comp circuitWidth_primrec) hf))

theorem circuitGates_primrec_of_updates
    (hg : Primrec (fun z : CircuitArg => updateGates z.1 z.2.1 z.2.2))
    (ho : Primrec (fun z : CircuitArg => updateOutputs z.1 z.2.1 z.2.2)) :
    Primrec (fun z : CircuitArg => circuitGates z.1 z.2.1 z.2.2) :=
  unroll_primrec.comp (unrollArgs_primrec hg ho)

theorem acceptIndex_primrec_of_updates
    (hg : Primrec (fun z : CircuitArg => updateGates z.1 z.2.1 z.2.2))
    (ho : Primrec (fun z : CircuitArg => updateOutputs z.1 z.2.1 z.2.2)) :
    Primrec (fun z : CircuitArg => acceptIndex z.1 z.2.1 z.2.2) := by
  have hindex : Primrec (fun z : CircuitArg => Shared.Codes.FiniteProgramTotalize.trueState z.1) :=
    Primrec.nat_add.comp (Primrec.list_length.comp Primrec.fst) (Primrec.const 2)
  exact Primrec.option_getD.comp
    (Primrec.list_getElem?.comp (finalRefs_primrec.comp (unrollArgs_primrec hg ho)) hindex) (Primrec.const 0)

theorem witnessGates_primrec_of_circuit
    (hg : Primrec (fun z : CircuitArg => circuitGates z.1 z.2.1 z.2.2)) :
    Primrec (fun z : Decoded => witnessGates z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  have hp : Primrec (fun z : Decoded => z.1) := Primrec.fst
  have hx : Primrec (fun z : Decoded => z.2.1) := Primrec.fst.comp Primrec.snd
  have hn : Primrec (fun z : Decoded => z.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have ht : Primrec (fun z : Decoded => z.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hcir := hg.comp (Primrec.pair hp (Primrec.pair (dummyInput_primrec.comp hx hn) ht))
  have he := Primrec.pair innerWidth_primrec
    (Primrec.pair (Primrec.nat_add.comp innerWidth_primrec hn) refs_primrec)
  exact relocate_primrec.comp (Primrec.pair he hcir)

theorem witnessOutput_primrec_of_circuit
    (ha : Primrec (fun z : CircuitArg => acceptIndex z.1 z.2.1 z.2.2)) :
    Primrec (fun z : Decoded => witnessOutput z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  have hp : Primrec (fun z : Decoded => z.1) := Primrec.fst
  have hx : Primrec (fun z : Decoded => z.2.1) := Primrec.fst.comp Primrec.snd
  have hn : Primrec (fun z : Decoded => z.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have ht : Primrec (fun z : Decoded => z.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hc := ha.comp (Primrec.pair hp (Primrec.pair (dummyInput_primrec.comp hx hn) ht))
  exact remap_primrec.comp (Primrec.pair innerWidth_primrec
    (Primrec.pair (Primrec.nat_add.comp innerWidth_primrec hn) (Primrec.pair refs_primrec hc)))

theorem reduction_primrec_of_updates
    (hg : Primrec (fun z : CircuitArg => updateGates z.1 z.2.1 z.2.2))
    (ho : Primrec (fun z : CircuitArg => updateOutputs z.1 z.2.1 z.2.2)) :
    Primrec reduction :=
  reduction_primrec_of_outputs (witnessOutput_primrec_of_circuit (acceptIndex_primrec_of_updates hg ho))
    (witnessGates_primrec_of_circuit (circuitGates_primrec_of_updates hg ho))

namespace Fixtures
example : relocate 1 2 [0] [.neg 0] = [.neg 0] := by decide
example : finalRefs 1 [.neg 0] [1] 1 [0] 2 = [2] := by decide
example : (unroll 1 [.neg 0] [1] 1 [0] 2).length = 2 := by decide
end Fixtures

end Shared.ComplexityBridge.CircuitRelocateComputability
