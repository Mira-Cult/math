import Shared.Codes.FiniteProgramBits
import Shared.ComplexityBridge.CNFDisjunction

/-! A concrete all-bitstrings front end for finite-program acceptance with
unary witness and time bounds. Invalid request encodings, invalid program
descriptions and non-unary bounds reject. The executable reference searches
all witnesses; this file does not yet prove NP membership or a polynomial-time
reduction implementation. -/
namespace Shared.ComplexityBridge.UnaryBounded
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramBits
open Shared.Codes.VerifierPrograms
open Shared.ComplexityBridge.CNF
open Shared.ComplexityBridge.CNFDisjunction
open Shared.ComplexityBridge.ParserComputability

/-- Both bounds are actual raw unary bit lists, not binary integers. -/
abbrev Request := (List Bool × List Bool) × (List Bool × List Bool)
abbrev Decoded := Program × List Bool × Nat × Nat

def unaryValue (bits : List Bool) : Option Nat :=
  if bits.all id then some bits.length else none

theorem unaryValue_replicate (n : Nat) : unaryValue (List.replicate n true) = some n := by
  simp [unaryValue]

theorem unaryValue_sound (bits : List Bool) (n : Nat) (h : unaryValue bits = some n) :
    bits = List.replicate n true := by
  unfold unaryValue at h
  split at h
  · rename_i hall
    have hn : bits.length = n := by simpa using h
    have ha : ∀ b ∈ bits, b = true := by simpa [List.all_eq_true] using hall
    apply List.eq_replicate_iff.mpr
    exact ⟨hn,ha⟩
  · simp at h

def parseRequest (raw : List Bool) : Option Request := BitstringEncoding.bitDecode raw

def decodeFields (r : Request) : Option Decoded := do
  let p ← parseValid r.1.1
  let bound ← unaryValue r.2.1
  let fuel ← unaryValue r.2.2
  pure (p,r.1.2,bound,fuel)

def decodeRequest (raw : List Bool) : Option Decoded :=
  (parseRequest raw).bind decodeFields

theorem unaryValue_primrec : Primrec unaryValue := by
  have hall : Primrec (fun xs : List Bool => xs.all id) := by
    apply Shared.ComplexityBridge.CNF.list_all_primrec Primrec.id
    exact (Primrec.snd : Primrec (fun p : List Bool × Bool => p.2)).to₂
  have h := Primrec.cond hall (Primrec.option_some.comp Primrec.list_length) (Primrec.const (none : Option Nat))
  apply h.of_eq
  intro xs
  cases hh : xs.all id <;> simp [unaryValue,hh]

theorem parseRequest_primrec : Primrec parseRequest := by
  have hl := bitDecode_list_primrec bitDecode_bool_primrec
  exact bitDecode_pair_primrec (bitDecode_pair_primrec hl hl) (bitDecode_pair_primrec hl hl)

theorem decodeFields_primrec : Primrec decodeFields := by
  let P := Request × Program
  let B := P × Nat
  have hp : Primrec (fun r : Request => parseValid r.1.1) :=
    parseValid_primrec.comp (Primrec.fst.comp Primrec.fst)
  have hb : Primrec (fun q : P => unaryValue q.1.2.1) :=
    unaryValue_primrec.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
  have ht : Primrec (fun q : B => unaryValue q.1.1.2.2) :=
    unaryValue_primrec.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  have hout : Primrec₂ (fun (q : B) (fuel : Nat) => ((q.1.2,q.1.1.1.2,q.2,fuel) : Decoded)) := by
    have hprog : Primrec (fun z : B × Nat => z.1.1.2) :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    have hx : Primrec (fun z : B × Nat => z.1.1.1.1.2) :=
      Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
    have hbound : Primrec (fun z : B × Nat => z.1.2) := Primrec.snd.comp Primrec.fst
    exact (Primrec.pair hprog (Primrec.pair hx (Primrec.pair hbound Primrec.snd))).to₂
  have h3 : Primrec (fun q : B => (unaryValue q.1.1.2.2).map fun fuel =>
      (q.1.2,q.1.1.1.2,q.2,fuel)) := Primrec.option_map ht hout
  have h2 : Primrec (fun q : P => (unaryValue q.1.2.1).bind fun bound =>
      (unaryValue q.1.2.2).map fun fuel => (q.2,q.1.1.2,bound,fuel)) :=
    Primrec.option_bind hb h3.to₂
  have h1 := Primrec.option_bind hp h2.to₂
  apply h1.of_eq
  intro r
  unfold decodeFields
  cases hp' : parseValid r.1.1 with
  | none => rfl
  | some p =>
    cases hb' : unaryValue r.2.1 with
    | none => simp [hb']
    | some bound =>
      cases ht' : unaryValue r.2.2 <;> simp [hb',ht']

theorem decodeRequest_primrec : Primrec decodeRequest :=
  Primrec.option_bind parseRequest_primrec (decodeFields_primrec.comp Primrec.snd).to₂

theorem decodeRequest_computable : Computable decodeRequest := decodeRequest_primrec.to_comp

/-- Total exhaustive evaluator: timeout and invalid program outcomes do not
count as acceptance. -/
def accept (raw : List Bool) : Bool :=
  match decodeRequest raw with
  | none => false
  | some (p,x,bound,fuel) =>
      (witnesses bound).any fun w => bounded p (BitstringEncoding.bitEncode (x,w)) fuel == some true

def evaluateDecoded (d : Decoded) : Bool :=
  (witnesses d.2.2.1).any fun w => bounded d.1 (BitstringEncoding.bitEncode (d.2.1,w)) d.2.2.2 == some true

theorem evaluateDecoded_primrec : Primrec evaluateDecoded := by
  unfold evaluateDecoded
  have hws : Primrec (fun d : Decoded => witnesses d.2.2.1) :=
    witnesses_primrec.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  let Z := Decoded × List Bool
  have hp : Primrec (fun z : Z => z.1.1) := Primrec.fst.comp Primrec.fst
  have hx : Primrec (fun z : Z => z.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hf : Primrec (fun z : Z => z.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have he : Primrec (fun z : Z => BitstringEncoding.bitEncode (z.1.2.1,z.2)) :=
    pairEncoding_primrec.comp (Primrec.pair hx Primrec.snd)
  have hb : Primrec (fun z : Z => bounded z.1.1 (BitstringEncoding.bitEncode (z.1.2.1,z.2)) z.1.2.2.2) :=
    bounded_primrec.comp (Primrec.pair (Primrec.pair hp he) hf)
  have htest : Primrec₂ (fun (d : Decoded) (w : List Bool) =>
      bounded d.1 (BitstringEncoding.bitEncode (d.2.1,w)) d.2.2.2 == some true) := by
    apply (Primrec.beq.comp hb (Primrec.const (some true : Option Bool))).to₂.of_eq
    intro d w
    cases h : bounded d.1 (BitstringEncoding.bitEncode (d.2.1,w)) d.2.2.2 with
    | none => rfl
    | some b => cases b <;> rfl
  exact Shared.ComplexityBridge.CNF.list_any_primrec hws htest

theorem accept_primrec : Primrec accept := by
  have h := Primrec.option_casesOn decodeRequest_primrec (Primrec.const false)
    (evaluateDecoded_primrec.comp Primrec.snd).to₂
  apply h.of_eq
  intro raw
  cases hr : decodeRequest raw with
  | none => simp [accept,hr]
  | some d => rcases d with ⟨p,x,bound,fuel⟩; simp [accept,evaluateDecoded,hr]

theorem accept_computable : Computable accept := accept_primrec.to_comp

theorem accept_iff (raw : List Bool) :
    accept raw = true ↔ ∃ (p : Program) (x : List Bool) (bound fuel : Nat),
      decodeRequest raw = some (p,x,bound,fuel) ∧
        ∃ w : List Bool, w.length ≤ bound ∧ bounded p (BitstringEncoding.bitEncode (x,w)) fuel = some true := by
  cases h : decodeRequest raw with
  | none => simp [accept,h]
  | some v =>
    rcases v with ⟨p,x,bound,fuel⟩
    simp only [accept,h,List.any_eq_true,beq_iff_eq,mem_witnesses_iff]
    constructor
    · rintro ⟨w,hw,ha⟩
      exact ⟨p,x,bound,fuel,rfl,w,hw,ha⟩
    · rintro ⟨p',x',b',t',he,w,hw,ha⟩
      simp only [Option.some.injEq,Prod.mk.injEq] at he
      rcases he with ⟨rfl,rfl,rfl,rfl⟩
      exact ⟨w,hw,ha⟩

/-- Malformed input reduces to the canonical false CNF; well-formed input
uses the concrete bounded-pair construction. -/
def reduction (raw : List Bool) : List Bool :=
  match decodeRequest raw with
  | none => BitstringEncoding.bitEncode ([[]] : Formula)
  | some (p,x,bound,fuel) => BitstringEncoding.bitEncode (boundedPairFormula p x bound fuel)

theorem reduction_correct (raw : List Bool) : sat (reduction raw) = accept raw := by
  cases h : decodeRequest raw with
  | none =>
    have hz : sat (BitstringEncoding.bitEncode ([[]] : Formula)) = false := by decide
    simp [reduction,accept,h,hz]
  | some v =>
    rcases v with ⟨p,x,bound,fuel⟩
    have hs := sat_boundedPairFormula_iff p x bound fuel
    have ha : accept raw = true ↔ ∃ w : List Bool, w.length ≤ bound ∧
        bounded p (BitstringEncoding.bitEncode (x,w)) fuel = some true := by
      simp [accept,h,List.any_eq_true,mem_witnesses_iff]
    have hiff := hs.trans ha.symm
    simp only [reduction,h]
    cases hv : sat (BitstringEncoding.bitEncode (boundedPairFormula p x bound fuel)) with
    | false =>
      cases he : accept raw with
      | false => rfl
      | true => have hh := hiff.2 he; rw [hv] at hh; contradiction
    | true =>
      cases he : accept raw with
      | false => have hh := hiff.1 hv; rw [he] at hh; contradiction
      | true => rfl

/-- Canonical request bytes contain the whole program, public input and both
unary bounds. -/
def request (description x : List Bool) (bound fuel : Nat) : List Bool :=
  BitstringEncoding.bitEncode (((description,x),(List.replicate bound true,List.replicate fuel true)) : Request)

theorem request_length (description x : List Bool) (bound fuel : Nat) :
    (request description x bound fuel).length = 12*description.length+6*x.length+6*bound+3*fuel+4 := by
  change (BitstringEncoding.delimit (BitstringEncoding.bitEncode (description,x)) ++
    BitstringEncoding.bitEncode (List.replicate bound true,List.replicate fuel true)).length = _
  simp [BitstringEncoding.length_delimit,Shared.ComplexityBridge.bitstring_pair_encoded_length]
  omega

theorem decode_request (p : Program) (x : List Bool) (bound fuel : Nat) (h : valid p = true) :
    decodeRequest (request (serialize p) x bound fuel) = some (p,x,bound,fuel) := by
  simp [decodeRequest,decodeFields,parseRequest,request,parseValid_serialize p h,unaryValue_replicate]

/-- Every successfully decoded pair comes from two framed substrings no
longer than the complete input, even when nested. -/
theorem decoded_pair_parts {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    (raw : List Bool) (a : α) (b : β)
    (h : (BitstringEncoding.bitDecode raw : Option (α × β)) = some (a,b)) :
    ∃ left right : List Bool,
      (BitstringEncoding.bitDecode left : Option α) = some a ∧
      (BitstringEncoding.bitDecode right : Option β) = some b ∧
      left.length ≤ raw.length ∧ right.length ≤ raw.length := by
  change (match BitstringEncoding.undelimit raw with
    | none => none
    | some (l,r) => match (BitstringEncoding.bitDecode l : Option α), (BitstringEncoding.bitDecode r : Option β) with
      | some x, some y => some (x,y)
      | _,_ => none) = some (a,b) at h
  cases hp : BitstringEncoding.undelimit raw with
  | none => simp [hp] at h
  | some pair =>
    rcases pair with ⟨left,right⟩
    cases hl : (BitstringEncoding.bitDecode left : Option α) with
    | none => simp [hp,hl] at h
    | some x =>
      cases hr : (BitstringEncoding.bitDecode right : Option β) with
      | none => simp [hp,hl,hr] at h
      | some y =>
        simp [hp,hl,hr] at h
        rcases h with ⟨rfl,rfl⟩
        have he := Shared.ComplexityBridge.CNFWitness.undelimit_sound raw left right hp
        have hn := congrArg List.length he
        simp only [List.length_append,BitstringEncoding.length_delimit] at hn
        exact ⟨left,right,hl,hr,by omega,by omega⟩

/-- All four decoded raw fields fit in the complete encoded request. -/
theorem parseRequest_lengths (raw : List Bool) (r : Request) (h : parseRequest raw = some r) :
    r.1.1.length ≤ raw.length ∧ r.1.2.length ≤ raw.length ∧
      r.2.1.length ≤ raw.length ∧ r.2.2.length ≤ raw.length := by
  rcases r with ⟨⟨description,x⟩,⟨boundBits,fuelBits⟩⟩
  change description.length ≤ raw.length ∧ x.length ≤ raw.length ∧
    boundBits.length ≤ raw.length ∧ fuelBits.length ≤ raw.length
  obtain ⟨left,right,hl,hr,hll,hrl⟩ := decoded_pair_parts raw (description,x) (boundBits,fuelBits) h
  obtain ⟨d,xs,hd,hx,hdl,hxl⟩ := decoded_pair_parts left description x hl
  obtain ⟨bs,ts,hb,ht,hbl,htl⟩ := decoded_pair_parts right boundBits fuelBits hr
  have hd' := Shared.ComplexityBridge.CNFWitness.decoded_list_length d description hd
  have hx' := Shared.ComplexityBridge.CNFWitness.decoded_list_length xs x hx
  have hb' := Shared.ComplexityBridge.CNFWitness.decoded_list_length bs boundBits hb
  have ht' := Shared.ComplexityBridge.CNFWitness.decoded_list_length ts fuelBits ht
  exact ⟨by omega,by omega,by omega,by omega⟩

theorem unaryValue_length (bits : List Bool) (n : Nat) (h : unaryValue bits = some n) :
    n = bits.length := by
  unfold unaryValue at h
  split at h <;> simp_all

theorem decodeRequest_lengths (raw : List Bool) (p : Program) (x : List Bool) (bound fuel : Nat)
    (h : decodeRequest raw = some (p,x,bound,fuel)) :
    p.length ≤ raw.length ∧ x.length ≤ raw.length ∧ bound ≤ raw.length ∧ fuel ≤ raw.length := by
  cases hreq : parseRequest raw with
  | none => simp [decodeRequest,hreq] at h
  | some r =>
    cases hp : parseValid r.1.1 with
    | none => simp [decodeRequest,decodeFields,hreq,hp] at h
    | some q =>
      cases hb : unaryValue r.2.1 with
      | none => simp [decodeRequest,decodeFields,hreq,hp,hb] at h
      | some b =>
        cases ht : unaryValue r.2.2 with
        | none => simp [decodeRequest,decodeFields,hreq,hp,hb,ht] at h
        | some t =>
          simp [decodeRequest,decodeFields,hreq,hp,hb,ht] at h
          rcases h with ⟨rfl,rfl,rfl,rfl⟩
          have hparts := parseRequest_lengths raw r hreq
          have hstates := parseValid_state_count r.1.1 q hp
          have hbl := unaryValue_length r.2.1 b hb
          have htl := unaryValue_length r.2.2 t ht
          exact ⟨by omega,hparts.2.1,by omega,by omega⟩

theorem canonical_request_correct (p : Program) (x : List Bool) (bound fuel : Nat) (h : valid p = true) :
    accept (request (serialize p) x bound fuel) = true ↔
      ∃ w : List Bool, w.length ≤ bound ∧ bounded p (BitstringEncoding.bitEncode (x,w)) fuel = some true := by
  simp [accept,decode_request p x bound fuel h,List.any_eq_true,mem_witnesses_iff]

namespace Fixtures
example : unaryValue [] = some 0 := by decide
example : unaryValue [true,true] = some 2 := by decide
example : unaryValue [true,false] = none := by decide
example : accept [true] = false := by decide
example : sat (reduction [true]) = false := by
  rw [reduction_correct]
  decide
end Fixtures
end Shared.ComplexityBridge.UnaryBounded
