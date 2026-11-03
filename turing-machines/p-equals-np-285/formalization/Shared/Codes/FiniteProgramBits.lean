import Shared.Codes.FinitePrograms
import Shared.ComplexityBridge.CircuitCNF
import Shared.ComplexityBridge.CNFWitness

/-! Binary serialization of the shared finite-program tables, using the
pinned Google bitstring encodings. Parsing is total and rejects malformed or
invalid programs. The step counter below measures a concrete bit-list block
parser; it is not yet a Turing-machine runtime proof for the whole decoder. -/
namespace Shared.Codes.FiniteProgramBits
open Shared.Codes.FinitePrograms
open Shared.ComplexityBridge.ParserComputability
open Shared.ComplexityBridge.CircuitCNF

def serialize (p : Program) : List Bool := BitstringEncoding.bitEncode p

def parse (bits : List Bool) : Option Program := BitstringEncoding.bitDecode bits

def parseValid (bits : List Bool) : Option Program := do
  let p ← parse bits
  if valid p then some p else none

@[simp] theorem parse_serialize (p : Program) : parse (serialize p) = some p :=
  BitstringEncoding.bitDecode_bitEncode p

theorem parseValid_serialize (p : Program) (h : valid p = true) :
    parseValid (serialize p) = some p := by simp [parseValid,h]

theorem parseValid_malformed (bits : List Bool) (h : parse bits = none) : parseValid bits = none := by
  simp [parseValid,h]

theorem parseValid_invalid (bits : List Bool) (p : Program)
    (h : parse bits = some p) (hv : valid p = false) : parseValid bits = none := by
  simp [parseValid,h,hv]

theorem parseValid_some_valid (bits : List Bool) (p : Program)
    (h : parseValid bits = some p) : parse bits = some p ∧ valid p = true := by
  cases hp : parse bits with
  | none => simp [parseValid,hp] at h
  | some q =>
    cases hv : valid q with
    | false => simp [parseValid,hp,hv] at h
    | true => simp [parseValid,hp,hv] at h; subst q; exact ⟨rfl,hv⟩

/-- The decoder is executable recursion-theoretic code on binary lists. -/
theorem parse_primrec : Primrec parse := by
  have hrow : Primrec (@BitstringEncoding.bitDecode Row _) :=
    bitDecode_pair_primrec bitDecode_bool_primrec
      (bitDecode_pair_primrec bitDecode_bool_primrec
        (bitDecode_pair_primrec bitDecode_nat_primrec bitDecode_nat_primrec))
  exact bitDecode_list_primrec (bitDecode_pair_primrec hrow hrow)

theorem parseValid_primrec : Primrec parseValid := by
  have hchoice : Primrec (fun q : List Bool × Program => if valid q.2 then some q.2 else none) := by
    have hh := Primrec.cond (valid_primrec.comp (Primrec.snd : Primrec (fun q : List Bool × Program => q.2)))
      (Primrec.option_some.comp Primrec.snd) (Primrec.const (none : Option Program))
    apply hh.of_eq
    intro q
    cases valid q.2 <;> rfl
  exact Primrec.option_bind parse_primrec hchoice.to₂

theorem parseValid_computable : Computable parseValid := parseValid_primrec.to_comp

def enumerate (n : Nat) : Option Program := parseValid (Shared.Codes.Inputs.inputAt n)

theorem enumerate_computable : Computable enumerate :=
  parseValid_computable.comp Shared.Codes.Inputs.computable

theorem enumerate_covers (p : Program) (h : valid p = true) :
    ∃ n, enumerate n = some p := by
  obtain ⟨n,hn⟩ := Shared.Codes.Inputs.covers (serialize p)
  exact ⟨n,by simp [enumerate,hn,parseValid_serialize p h]⟩

/-- A decoded program has no more states than source bits, including when
its natural-number fields use accepted noncanonical bit representations. -/
theorem parse_state_count (bits : List Bool) (p : Program) (h : parse bits = some p) :
    p.length ≤ bits.length :=
  Shared.ComplexityBridge.CNFWitness.decoded_list_length bits p h

theorem parseValid_state_count (bits : List Bool) (p : Program) (h : parseValid bits = some p) :
    p.length ≤ bits.length := parse_state_count bits p (parseValid_some_valid bits p h).1

/-- A binary description is decoded and validated before bounded execution.
A malformed description, invalid table, timeout or invalid result yields none. -/
def evaluateBits (description input : List Bool) (fuel : Nat) : Option Bool := do
  let p ← parseValid description
  bounded p input fuel

theorem evaluateBits_primrec : Primrec (fun z : (List Bool × List Bool) × Nat =>
    evaluateBits z.1.1 z.1.2 z.2) := by
  let A := (List Bool × List Bool) × Nat
  have hp : Primrec (fun z : A => parseValid z.1.1) :=
    parseValid_primrec.comp (Primrec.fst.comp Primrec.fst)
  have hb : Primrec₂ (fun (z : A) (p : Program) => bounded p z.1.2 z.2) :=
    (bounded_primrec.comp (Primrec.pair
      (Primrec.pair Primrec.snd (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.snd.comp Primrec.fst))).to₂
  exact Primrec.option_bind hp hb

theorem evaluateBits_computable : Computable (fun z : (List Bool × List Bool) × Nat =>
    evaluateBits z.1.1 z.1.2 z.2) := evaluateBits_primrec.to_comp

theorem evaluateBits_parsed (description input : List Bool) (fuel : Nat) (p : Program)
    (h : parseValid description = some p) : evaluateBits description input fuel = bounded p input fuel := by
  simp [evaluateBits,h]

theorem evaluateBits_rejects (description input : List Bool) (fuel : Nat)
    (h : parseValid description = none) : evaluateBits description input fuel = none := by
  simp [evaluateBits,h]

/-- Actual serialized size counts the binary representations of both numeric
fields; halting rows can contain large unused next-state values. -/
def rowBits (r : Row) : Nat :=
  7+2*(Computability.encodeNat r.2.2.1).length+(Computability.encodeNat r.2.2.2).length

def pairBits (pair : Row × Row) : Nat := 3+4*rowBits pair.1+2*rowBits pair.2

theorem row_encoded_length (r : Row) :
    (BitstringEncoding.bitEncode r).length = rowBits r := by
  rcases r with ⟨w,d,next,tag⟩
  change (BitstringEncoding.delimit [w] ++
    (BitstringEncoding.delimit [d] ++
      (BitstringEncoding.delimit (Computability.encodeNat next) ++ Computability.encodeNat tag))).length = _
  simp [rowBits,BitstringEncoding.length_delimit,BitstringEncoding.delimit]
  omega

theorem pair_encoded_length (pair : Row × Row) :
    (BitstringEncoding.delimit (BitstringEncoding.bitEncode pair)).length = pairBits pair := by
  rcases pair with ⟨a,b⟩
  change (BitstringEncoding.delimit (BitstringEncoding.delimit (BitstringEncoding.bitEncode a) ++
    BitstringEncoding.bitEncode b)).length = _
  simp [pairBits,BitstringEncoding.length_delimit,row_encoded_length]
  omega

theorem serialize_length (p : Program) : (serialize p).length = (p.map pairBits).sum := by
  change (((p.map (fun a : Row × Row => BitstringEncoding.bitEncode a)).map BitstringEncoding.delimit).flatten).length = _
  simp only [List.length_flatten,List.map_map]
  congr 1
  apply List.map_congr_left
  intro pair _
  exact pair_encoded_length pair

/-- Costed version of the pinned block parser: each recursive call consumes
at most two input bits and charges one list-processing step. -/
def readBlock : List Bool → Option (List Bool × List Bool) × Nat
  | [] => (none,1)
  | false::xs => (some ([],xs),1)
  | [true] => (none,1)
  | true::b::xs =>
      let r := readBlock xs
      (r.1.map (fun p => (b::p.1,p.2)),r.2+1)

theorem readBlock_correct (bits : List Bool) : (readBlock bits).1 = BitstringEncoding.undelimit bits := by
  induction bits using readBlock.induct with
  | case1 => rfl
  | case2 xs => rfl
  | case3 => rfl
  | case4 b xs ih =>
    simp only [readBlock,Prod.fst,BitstringEncoding.undelimit]
    rw [ih]

theorem readBlock_steps (bits : List Bool) : (readBlock bits).2 ≤ bits.length+1 := by
  induction bits using readBlock.induct with
  | case1 => simp [readBlock]
  | case2 xs => simp [readBlock]
  | case3 => simp [readBlock]
  | case4 b xs ih =>
    simp only [readBlock,Prod.snd,List.length_cons]
    omega

namespace Fixtures
def accepting : Program := [((false,false,0,2),(true,true,0,2))]
example : parseValid (serialize accepting) = some accepting := by
  apply parseValid_serialize
  decide
example : parse [true] = none := by decide
example : parseValid (serialize []) = none :=
  parseValid_invalid _ [] (parse_serialize []) (by decide)
example : readBlock [true,true,false,false] = (some ([true],[false]),2) := by decide
example : readBlock [true] = (none,1) := by decide
example : evaluateBits (serialize accepting) [] 0 = none := by
  rw [evaluateBits_parsed _ _ _ accepting (parseValid_serialize accepting (by decide))]
  decide
example : evaluateBits (serialize accepting) [] 1 = some true := by
  rw [evaluateBits_parsed _ _ _ accepting (parseValid_serialize accepting (by decide))]
  decide
example : evaluateBits [true] [] 1 = none := by
  apply evaluateBits_rejects
  exact parseValid_malformed [true] (by decide)

/-- Natural payload `[false]` and its longer canonical form decode to the
same value; the pinned natural-number parser accepts both representations. -/
example : (BitstringEncoding.bitDecode [false] : Option Nat) = some 2 := by decide
example : (BitstringEncoding.bitDecode [false,true] : Option Nat) = some 2 := by decide
example : ([false] : List Bool) ≠ Computability.encodeNat 2 := by decide
end Fixtures
end Shared.Codes.FiniteProgramBits
