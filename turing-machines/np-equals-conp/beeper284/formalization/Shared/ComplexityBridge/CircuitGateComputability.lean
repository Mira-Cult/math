import Shared.ComplexityBridge.CNFEncodingComputability
import Shared.ComplexityBridge.CircuitSelect

/-! Effective representation of finite Boolean circuit gates. This is a
recursion-theoretic interface, not a bit-cost machine simulation. -/
namespace Shared.ComplexityBridge.CircuitGateComputability

open Shared.ComplexityBridge.CircuitCNF
open Shared.ComplexityBridge.CircuitSelect
open Shared.ComplexityBridge.CNF

abbrev GateCode := Bool ⊕ (Nat ⊕ ((Nat × Nat) ⊕ (Nat × Nat)))

def gateEquiv : Gate ≃ GateCode where
  toFun
    | .constant b => .inl b
    | .neg x => .inr (.inl x)
    | .conj x y => .inr (.inr (.inl (x,y)))
    | .disj x y => .inr (.inr (.inr (x,y)))
  invFun
    | .inl b => .constant b
    | .inr (.inl x) => .neg x
    | .inr (.inr (.inl (x,y))) => .conj x y
    | .inr (.inr (.inr (x,y))) => .disj x y
  left_inv := by intro g; cases g <;> rfl
  right_inv := by intro g; rcases g with b | (x | (⟨x,y⟩ | ⟨x,y⟩)) <;> rfl

instance gatePrimcodable : Primcodable Gate := Primcodable.ofEquiv GateCode gateEquiv

theorem gateCode_primrec : Primrec gateEquiv := Primrec.of_equiv
theorem gateDecode_primrec : Primrec gateEquiv.symm := Primrec.of_equiv_symm

theorem constant_primrec : Primrec Gate.constant := by
  apply gateDecode_primrec.comp (Primrec.sumInl : Primrec (fun b : Bool => (Sum.inl b : GateCode))) |>.of_eq
  intro b
  rfl

theorem neg_primrec : Primrec Gate.neg := by
  have h : Primrec (fun n : Nat => (Sum.inr (Sum.inl n) : GateCode)) :=
    Primrec.sumInr.comp Primrec.sumInl
  exact (gateDecode_primrec.comp h).of_eq (fun _ => rfl)

theorem conj_primrec : Primrec₂ Gate.conj := by
  have h : Primrec (fun p : Nat × Nat => (Sum.inr (Sum.inr (Sum.inl p)) : GateCode)) :=
    Primrec.sumInr.comp (Primrec.sumInr.comp Primrec.sumInl)
  exact ((gateDecode_primrec.comp h).of_eq (fun _ => rfl)).to₂

theorem disj_primrec : Primrec₂ Gate.disj := by
  have h : Primrec (fun p : Nat × Nat => (Sum.inr (Sum.inr (Sum.inr p)) : GateCode)) :=
    Primrec.sumInr.comp (Primrec.sumInr.comp Primrec.sumInr)
  exact ((gateDecode_primrec.comp h).of_eq (fun _ => rfl)).to₂

private theorem one {α β : Type} [Primcodable α] [Primcodable β]
    {f : α → β} (hf : Primrec f) : Primrec (fun a => [f a]) :=
  Primrec.list_cons.comp hf (Primrec.const [])

private theorem two {α β : Type} [Primcodable α] [Primcodable β]
    {f g : α → β} (hf : Primrec f) (hg : Primrec g) : Primrec (fun a => [f a,g a]) :=
  Primrec.list_cons.comp hf (one hg)

private theorem three {α β : Type} [Primcodable α] [Primcodable β]
    {f g h : α → β} (hf : Primrec f) (hg : Primrec g) (hh : Primrec h) :
    Primrec (fun a => [f a,g a,h a]) :=
  Primrec.list_cons.comp hf (two hg hh)

private theorem literal {α : Type} [Primcodable α] {f : α → Nat} (hf : Primrec f) (b : Bool) :
    Primrec (fun a => (f a,b)) := Primrec.pair hf (Primrec.const b)

theorem gateCNF_constant_primrec : Primrec (fun z : Nat × Bool => gateCNF z.1 (.constant z.2)) := by
  exact one (one (Primrec.pair Primrec.fst Primrec.snd))

theorem gateCNF_neg_primrec : Primrec (fun z : Nat × Nat => gateCNF z.1 (.neg z.2)) := by
  exact two (two (literal Primrec.fst false) (literal Primrec.snd false))
    (two (literal Primrec.fst true) (literal Primrec.snd true))

theorem gateCNF_conj_primrec : Primrec (fun z : Nat × (Nat × Nat) => gateCNF z.1 (.conj z.2.1 z.2.2)) := by
  let out : Primrec (fun z : Nat × (Nat × Nat) => z.1) := Primrec.fst
  let x : Primrec (fun z : Nat × (Nat × Nat) => z.2.1) := Primrec.fst.comp Primrec.snd
  let y : Primrec (fun z : Nat × (Nat × Nat) => z.2.2) := Primrec.snd.comp Primrec.snd
  exact three (two (literal out false) (literal x true))
    (two (literal out false) (literal y true))
    (three (literal out true) (literal x false) (literal y false))

theorem gateCNF_disj_primrec : Primrec (fun z : Nat × (Nat × Nat) => gateCNF z.1 (.disj z.2.1 z.2.2)) := by
  let out : Primrec (fun z : Nat × (Nat × Nat) => z.1) := Primrec.fst
  let x : Primrec (fun z : Nat × (Nat × Nat) => z.2.1) := Primrec.fst.comp Primrec.snd
  let y : Primrec (fun z : Nat × (Nat × Nat) => z.2.2) := Primrec.snd.comp Primrec.snd
  exact three (two (literal out true) (literal x false))
    (two (literal out true) (literal y false))
    (three (literal out false) (literal x true) (literal y true))

theorem gateCNF_primrec : Primrec₂ gateCNF := by
  let A := Nat × GateCode
  let Inner := (Nat × Nat) ⊕ (Nat × Nat)
  let Middle := Nat ⊕ Inner
  have hi : Primrec (fun z : Nat × Inner =>
      match z.2 with
      | .inl p => gateCNF z.1 (.conj p.1 p.2)
      | .inr p => gateCNF z.1 (.disj p.1 p.2)) := by
    apply (Primrec.sumCasesOn Primrec.snd
      (gateCNF_conj_primrec.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂
      (gateCNF_disj_primrec.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂).of_eq
    intro z
    cases z.2 <;> rfl
  have hm : Primrec (fun z : Nat × Middle =>
      match z.2 with
      | .inl x => gateCNF z.1 (.neg x)
      | .inr inner => match inner with
        | .inl p => gateCNF z.1 (.conj p.1 p.2)
        | .inr p => gateCNF z.1 (.disj p.1 p.2)) := by
    apply (Primrec.sumCasesOn Primrec.snd
      (gateCNF_neg_primrec.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂
      (hi.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂).of_eq
    intro z
    cases z.2 <;> rfl
  have hc : Primrec (fun z : A =>
      match z.2 with
      | .inl b => gateCNF z.1 (.constant b)
      | .inr m => match m with
        | .inl x => gateCNF z.1 (.neg x)
        | .inr inner => match inner with
          | .inl p => gateCNF z.1 (.conj p.1 p.2)
          | .inr p => gateCNF z.1 (.disj p.1 p.2)) := by
    apply (Primrec.sumCasesOn Primrec.snd
      (gateCNF_constant_primrec.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂
      (hm.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂).of_eq
    intro z
    rcases z with ⟨o, b | (x | (p | p))⟩ <;> rfl
  have h := hc.comp (Primrec.pair Primrec.fst (gateCode_primrec.comp Primrec.snd))
  apply h.to₂.of_eq
  intro out g
  cases g <;> rfl

def gateSuffix (endIndex : Nat) : List Gate → Formula
  | [] => []
  | g::gs => gateCNF (endIndex-(gs.length+1)) g ++ gateSuffix endIndex gs

theorem gateSuffix_correct (gates : List Gate) (base : Nat) :
    gateSuffix (base+gates.length) gates = gateConstraints base gates := by
  induction gates generalizing base with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.length_cons,gateSuffix,gateConstraints]
    have he : base + (gs.length+1) - (gs.length+1) = base := by omega
    have hn : base + (gs.length+1) = (base+1)+gs.length := by omega
    rw [he,hn,ih]

theorem gateSuffix_primrec : Primrec₂ gateSuffix := by
  let A := Nat × List Gate
  let S := Gate × List Gate × Formula
  have hstep : Primrec₂ (fun (a : A) (s : S) =>
      gateCNF (a.1-(s.2.1.length+1)) s.1 ++ s.2.2) := by
    have hi : Primrec (fun z : A × S => z.1.1-(z.2.2.1.length+1)) :=
      Primrec.nat_sub.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.succ.comp (Primrec.list_length.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
    exact (Primrec.list_append.comp
      (gateCNF_primrec.comp hi (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to₂
  have h := Primrec.list_rec (Primrec.snd : Primrec (fun a : A => a.2)) (Primrec.const ([] : Formula)) hstep
  apply h.to₂.of_eq
  intro endIndex gates
  induction gates with
  | nil => rfl
  | cons g gs ih => simp [gateSuffix,ih]

theorem gateConstraints_primrec : Primrec₂ gateConstraints := by
  have h := gateSuffix_primrec.comp
    (Primrec.nat_add.comp (Primrec.fst : Primrec (fun a : Nat × List Gate => a.1))
      (Primrec.list_length.comp Primrec.snd)) Primrec.snd
  apply h.to₂.of_eq
  intro base gates
  exact gateSuffix_correct gates base

theorem compile_primrec : Primrec (fun z : Nat × Nat × List Gate => compile z.1 z.2.1 z.2.2) := by
  let A := Nat × Nat × List Gate
  have hgate : Primrec (fun z : A => gateConstraints z.1 z.2.2) :=
    gateConstraints_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)
  have hout : Primrec (fun z : A => [[(z.2.1,true)]]) :=
    one (one (literal (Primrec.fst.comp Primrec.snd) true))
  exact Primrec.list_append.comp hgate hout

def fixSuffix (endIndex : Nat) : List Bool → Formula
  | [] => []
  | b::bs => [(endIndex-(bs.length+1),b)] :: fixSuffix endIndex bs

theorem fixSuffix_correct (bits : List Bool) (base : Nat) :
    fixSuffix (base+bits.length) bits = fixInputs base bits := by
  induction bits generalizing base with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.length_cons,fixSuffix,fixInputs]
    have he : base + (bs.length+1) - (bs.length+1) = base := by omega
    have hn : base + (bs.length+1) = (base+1)+bs.length := by omega
    rw [he,hn,ih]

theorem fixSuffix_primrec : Primrec₂ fixSuffix := by
  let A := Nat × List Bool
  let S := Bool × List Bool × Formula
  have hstep : Primrec₂ (fun (a : A) (s : S) =>
      [(a.1-(s.2.1.length+1),s.1)] :: s.2.2) := by
    have hi : Primrec (fun z : A × S => z.1.1-(z.2.2.1.length+1)) :=
      Primrec.nat_sub.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.succ.comp (Primrec.list_length.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
    exact (Primrec.list_cons.comp (one (Primrec.pair hi (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to₂
  have h := Primrec.list_rec (Primrec.snd : Primrec (fun a : A => a.2)) (Primrec.const ([] : Formula)) hstep
  apply h.to₂.of_eq
  intro endIndex bits
  induction bits with
  | nil => rfl
  | cons b bs ih => simp [fixSuffix,ih]

theorem fixInputs_primrec : Primrec₂ fixInputs := by
  have h := fixSuffix_primrec.comp
    (Primrec.nat_add.comp (Primrec.fst : Primrec (fun a : Nat × List Bool => a.1))
      (Primrec.list_length.comp Primrec.snd)) Primrec.snd
  apply h.to₂.of_eq
  intro base bits
  exact fixSuffix_correct bits base

theorem compileFixed_primrec : Primrec (fun z : List Bool × Nat × Nat × List Gate =>
    compileFixed z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  let A := List Bool × Nat × Nat × List Gate
  have hfix : Primrec (fun z : A => fixInputs 0 z.1) := fixInputs_primrec.comp (Primrec.const 0) Primrec.fst
  have hbase : Primrec (fun z : A => z.1.length+z.2.1) :=
    Primrec.nat_add.comp (Primrec.list_length.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
  have houtput : Primrec (fun z : A => z.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hgates : Primrec (fun z : A => z.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_append.comp hfix
    (compile_primrec.comp (Primrec.pair hbase (Primrec.pair houtput hgates)))

theorem compileFixed_computable : Computable (fun z : List Bool × Nat × Nat × List Gate =>
    compileFixed z.1 z.2.1 z.2.2.1 z.2.2.2) := compileFixed_primrec.to_comp

namespace Fixtures
example : gateEquiv.symm (gateEquiv (.conj 7 3)) = .conj 7 3 := by decide
example : gateSuffix 3 [.neg 0,.constant true] = gateConstraints 1 [.neg 0,.constant true] := by decide
example : fixSuffix 3 [true,false] = fixInputs 1 [true,false] := by decide
end Fixtures

end Shared.ComplexityBridge.CircuitGateComputability
