import Shared.Beeping.NPcoNP.Grammar284ReservedWindow

/-! The root increment can leave a distinct parser code `111` for the
following beep. This relation is not an ordinary prepared grammar leaf. -/
namespace Shared.Beeping.NPcoNP.Grammar284RootReady
open PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768

def rootReadyPath : Path := [true,true,true]

def RootReady (bank : Bank 12) (origin separator : Int) (t : Int → Bool) : Prop :=
  ∃ more : List Nat, origin+59≤separator ∧ Holds t origin rootReadyPath ∧
    (∀ q, q<origin → t q=false) ∧
    (∀ q, origin+2<q → q<separator-1 → t q=false) ∧
    t (separator-1)=true ∧ t separator=false ∧
    Holds t (separator+1) (encode (arrayBank bank++more) ++ [true,false]) ∧
    (∀ q, separator+2+((encode (arrayBank bank++more)).length : Int)≤q → t q=false)
end Shared.Beeping.NPcoNP.Grammar284RootReady
