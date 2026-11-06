import Shared.Beeping.NPcoNP.NativePositiveGraphBank

/-! The producer's grammar-array order differs from the coalesced suffix
order. These facts are mathematical list conversions; they do not establish
that any physical tape has either representation. -/
namespace Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping Shared.Beeping.Machines PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Coalescing284Map
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.Bootstrap284BankDecode
open Shared.Beeping.NPcoNP.UnaryBank
open Shared.Beeping.NPcoNP.NativePositiveGraphBank
open Shared.Beeping.NPcoNP.Parent290Coalesced
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- Producer register-array order for a suffix-indexed graph bank. -/
def arrayBank (bank : Bank 12) : List Nat :=
  List.ofFn (fun i : Fin 12 => bank (arrayToSuffix i))

/-- Array position 0 denotes suffix 9; array position 1 denotes suffix 0. -/
theorem array_head (bank : Bank 12) :
    (arrayBank bank)[0]?=some (bank 9) ∧ (arrayBank bank)[1]?=some (bank 0) := by
  simp [arrayBank,arrayToSuffix]

/-- Graph row 9 increments suffix 0 and returns to row 8. -/
theorem row9 (bank : Bank 12) :
    target.system.step ⟨9,bank⟩=(⟨8,write bank 0 (bank 0+1)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix]

/-- A suffix-indexed write changes exactly its inverse-mapped array index. -/
theorem arrayBank_write (bank : Bank 12) (index : Fin 12) (v : Nat) :
    arrayBank (write bank index v) = (arrayBank bank).set (suffixToArray index).val v := by
  apply List.ext_getElem
  · simp [arrayBank]
  · intro i hi hj
    let j : Fin 12 := ⟨i, by simpa [arrayBank] using hi⟩
    have he : arrayToSuffix j=index ↔ i=(suffixToArray index).val := by
      constructor
      · intro h
        have hh := congrArg suffixToArray h
        rw [array_suffix_inverse] at hh
        exact congrArg Fin.val hh
      · intro h
        have hh : j=suffixToArray index := by apply Fin.ext; exact h
        rw [hh,suffix_array_inverse]
    simp only [arrayBank,List.getElem_ofFn,List.getElem_set,write]
    by_cases h : arrayToSuffix j=index
    · have hi' := he.mp h
      simp [h,hi',suffix_array_inverse]
    · have hi' : i≠(suffixToArray index).val := fun hx => h (he.mpr hx)
      have hx : arrayToSuffix (⟨i, by simpa [arrayBank] using hi⟩ : Fin 12) ≠ index := h
      simp [hx,Ne.symm hi']

/-- The row-9 increment changes array position 1, leaving array position 0
and the other ten positions unchanged. -/
theorem row9_array (bank : Bank 12) :
    arrayBank (target.system.step ⟨9,bank⟩).1.bank =
      (arrayBank bank).set 1 (bank 0+1) := by
  rw [row9]
  simpa [suffixToArray] using arrayBank_write bank 0 (bank 0+1)

/-- Position 10 has the same index in the two orders, so a prepared
positive row-8 update decrements the eleventh producer-array entry. -/
theorem array_write10 (bank : Bank 12) (values : List Nat) (v z : Nat)
    (hlen : values.length=10) (h : arrayBank bank=values ++ [v+1,z]) :
    bank 10=v+1 ∧ arrayBank (write bank 10 v)=values ++ [v,z] := by
  have hget := congrArg (fun xs : List Nat => xs[10]?) h
  have hreg : bank 10=v+1 := by
    simpa [arrayBank,arrayToSuffix,List.getElem?_ofFn,List.getElem?_append,hlen] using hget
  refine ⟨hreg,?_⟩
  rw [arrayBank_write,h]
  have hi : (suffixToArray (10 : Fin 12)).val=10 := by decide
  rw [hi,List.set_append_right 10 v (by omega),hlen]
  simp

/-- Row-8 positive readback in producer-array order. The supplied tape word
must be justified by the physical layout separately. -/
theorem decoded_matches_row8_array (t : Int → Bool) (start : Int) (values : List Nat)
    (v z : Nat) (rest : List Nat) (bank : Bank 12) (hlen : values.length=10)
    (hbank : arrayBank bank=values ++ [v+1,z])
    (hp : Holds t start (encode values))
    (hu : Holds t (start+((encode values).length : Int))
      (encode (v::z::rest) ++ [true,false,false])) :
    let result := (target.system.step ⟨8,bank⟩).1
    let tail := encode rest ++ [true,false,false]
    decode 12 (readCells t start (encode (arrayBank result.bank) ++ tail).length)=
      some (arrayBank result.bank,tail) ∧
    result.state=9 ∧ (target.system.step ⟨8,bank⟩).2=[] := by
  dsimp only
  obtain ⟨hreg,harr⟩ := array_write10 bank values v z hlen hbank
  have hr := row8_positive bank v hreg
  have hw := holds_append_intro t start (encode values)
    (encode (v::z::rest) ++ [true,false,false]) hp hu
  have he : encode (values ++ [v,z]) ++ (encode rest ++ [true,false,false]) =
      encode values ++ (encode (v::z::rest) ++ [true,false,false]) := by
    simp [encode_append,encode,List.append_assoc]
  have hh : Holds t start (encode (values ++ [v,z]) ++ (encode rest ++ [true,false,false])) := by
    rw [he]
    exact hw
  rw [hr]
  simp only [Prod.fst,Prod.snd]
  rw [harr,read_of_holds t start _ hh]
  have hl : (values ++ [v,z]).length=12 := by simp [hlen]
  have hd := decode_encode (values ++ [v,z]) (encode rest ++ [true,false,false])
  rw [hl] at hd
  exact ⟨hd,trivial,trivial⟩

/-- In producer-array order, a positive row-8 decrement followed by row 9
updates positions 10 and 1 respectively. -/
theorem row8_then9_array (bank : Bank 12) (a b : Nat) (prior : List Nat) (v z : Nat)
    (hlen : prior.length=8)
    (hbank : arrayBank bank=(a::b::prior) ++ [v+1,z]) :
    let next := (target.system.step ⟨8,bank⟩).1
    let result := (target.system.step ⟨9,next.bank⟩).1
    next.state=9 ∧ result.state=8 ∧
      arrayBank result.bank=(a::(b+1)::prior) ++ [v,z] ∧
      (target.system.step ⟨8,bank⟩).2=[] ∧ (target.system.step ⟨9,next.bank⟩).2=[] := by
  dsimp only
  have ht : (a::b::prior).length=10 := by simp [hlen]
  obtain ⟨h10,harray⟩ := array_write10 bank (a::b::prior) v z ht hbank
  have hr8 := row8_positive bank v h10
  have h0 : (write bank 10 v) 0=b := by
    have hg := congrArg (fun xs : List Nat => xs[1]?) hbank
    have hb0 : bank 0=b := by simpa [arrayBank,arrayToSuffix] using hg
    simpa [write] using hb0
  have hrow9 := row9 (write bank 10 v)
  have harray9 := row9_array (write bank 10 v)
  rw [hrow9] at harray9
  simp only [Prod.fst] at harray9
  rw [harray,h0] at harray9
  have hs : (((a::b::prior) ++ [v,z]).set 1 (b+1)) =
      (a::(b+1)::prior) ++ [v,z] := by simp
  rw [hs] at harray9
  rw [hr8]
  simp only [Prod.fst,Prod.snd]
  rw [hrow9]
  simpa [h0] using harray9

/-- Suffix-order and producer-array-order banks need not agree, so the
identity relation is not a general conversion. -/
theorem array_order_counterexample :
    ∃ bank : Bank 12, arrayBank bank ≠ List.ofFn bank := by
  let bank : Bank 12 := fun i => if i=0 then 1 else 0
  refine ⟨bank,?_⟩
  intro h
  have hh := congrArg (fun xs : List Nat => xs[0]?) h
  simp [arrayBank,arrayToSuffix,bank] at hh

#print axioms array_head
#print axioms row9
#print axioms arrayBank_write
#print axioms row9_array
#print axioms row8_then9_array
#print axioms array_write10
#print axioms decoded_matches_row8_array
#print axioms array_order_counterexample
end Shared.Beeping.NPcoNP.NativeArrayGraphBank
