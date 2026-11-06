import Shared.Beeping.NPcoNP.NativeArrayGraphBank
import Shared.Beeping.NPcoNP.NativeIncBank

/-! Repackage a completed positive row-8/row-9 bank for the next pass. -/
namespace Shared.Beeping.NPcoNP.NativeRow8Repack
open PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 7000000

/-- The new dummy zero is carried as one more suffix register; the two
explicit blanks remain outside the bank word. -/
theorem next_word (graphBank : Bank 12) (a b : Nat) (prior : List Nat)
    (v z : Nat) (rest : List Nat) (hlen : prior.length=8)
    (hgraph : arrayBank graphBank=(a::b::prior) ++ [v+1,z]) :
    let first := (target.system.step ⟨8,graphBank⟩).1
    let second := (target.system.step ⟨9,first.bank⟩).1
    (encode (arrayBank second.bank) ++ (encode rest ++ [true,false])) ++ [false,false] =
      encode (a::(b+1)::prior) ++ (encode (v::z::(rest++[0])) ++ [false,false]) := by
  dsimp only
  have harr := (row8_then9_array graphBank a b prior v z hlen hgraph).2.2.1
  rw [harr]
  simp [encode_append,encode,block,List.append_assoc]

#print axioms next_word
end Shared.Beeping.NPcoNP.NativeRow8Repack
