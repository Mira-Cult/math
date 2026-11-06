import Shared.Beeping.NPcoNP.Source284RectangleTM2
import Shared.ComplexityBridge.TM2ListLookup
import Shared.ComplexityBridge.TM2UnaryPolynomialIO

/-! A charged finite search for the quotient and remainder of a bounded row
index by five. The time bound is unary input data; arbitrary binary queries
are handled by a total default. -/
namespace Shared.Beeping.NPcoNP.Source284FiveSearchTM2

open ComplexityTheory Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284CountdownSearch (rectangle mem_rectangle)

abbrev Coord := Nat × Nat
abbrev Input := List Bool × Nat

def code (p : Coord) : Nat := 5*p.1+p.2

private theorem add_poly {α : Type} [BitstringEncoding α] (f g : α → Nat)
    (hf : IsPolyTime f) (hg : IsPolyTime g) : IsPolyTime (fun x => f x+g x) := by
  have h := TM2Compose.isPolyTime_comp (fun x => (f x,g x)) CNFBinaryPairAdd.addPair
    (TM2GuardAllStep.pair_isPolyTime f g hf hg) CNFBinaryPairAdd.addPair_isPolyTime
  simpa [CNFBinaryPairAdd.addPair] using h

theorem code_isPolyTime : IsPolyTime code := by
  let a : Coord → Nat := fun p => p.1
  let b : Coord → Nat := fun p => p.2
  have ha : IsPolyTime a := TM2PairFirst.first_isPolyTime
  have hb : IsPolyTime b := TM2GuardAllStep.second_isPolyTime
  have h2 := add_poly a a ha ha
  have h4 := add_poly (fun p => a p+a p) (fun p => a p+a p) h2 h2
  have h5 := add_poly (fun p => (a p+a p)+(a p+a p)) a h4 ha
  have h := add_poly (fun p => ((a p+a p)+(a p+a p))+a p) b h5 hb
  change IsPolyTime (fun p : Coord => 5*p.1+p.2)
  convert h using 1
  funext p
  dsimp [a,b]
  omega

/-- Emit a singleton precisely for a matching coordinate. -/
def hit (p : Nat × Coord) : List Coord :=
  TM2ListMask.mask (!TM2BoundedWitnessGuard.numericNe (code p.2,p.1),[p.2])

theorem hit_isPolyTime : IsPolyTime hit := by
  let query : Nat × Coord → Nat := fun p => p.1
  let coord : Nat × Coord → Coord := fun p => p.2
  let value : Nat × Coord → Nat := fun p => code (coord p)
  let neq : Nat × Coord → Bool := fun p => TM2BoundedWitnessGuard.numericNe (value p,query p)
  let flag : Nat × Coord → Bool := fun p => !neq p
  let single : Nat × Coord → List Coord := fun p => [coord p]
  have hq : IsPolyTime query := TM2PairFirst.first_isPolyTime
  have hc : IsPolyTime coord := TM2GuardAllStep.second_isPolyTime
  have hv : IsPolyTime value := TM2Compose.isPolyTime_comp coord code hc code_isPolyTime
  have hn : IsPolyTime neq := TM2Compose.isPolyTime_comp (fun p => (value p,query p))
    TM2BoundedWitnessGuard.numericNe (TM2GuardAllStep.pair_isPolyTime value query hv hq)
    TM2BoundedWitnessGuard.numericNe_isPolyTime
  have hf : IsPolyTime flag := TM2Compose.isPolyTime_comp neq (fun b => !b) hn TM2GateDispatch.not_isPolyTime
  have hs : IsPolyTime single := TM2GateCNFPieces.singleton_isPolyTime coord hc
  exact TM2Compose.isPolyTime_comp (fun p => (flag p,single p))
    (TM2ListMask.mask (α := Coord)) (TM2GuardAllStep.pair_isPolyTime flag single hf hs)
      TM2ListMask.mask_isPolyTime

def candidates (p : Input) : List Coord :=
  (TM2ContextMapGeneric.contextMap hit
    (p.2,Source284RectangleTM2.generate (List.replicate 5 true,p.1))).flatten

theorem candidates_isPolyTime : IsPolyTime candidates := by
  let ticks : Input → List Bool := fun p => p.1
  let query : Input → Nat := fun p => p.2
  let five : Input → List Bool := fun p => TM2UnaryPolynomialIO.unaryPolynomial (Polynomial.C 5) (ticks p)
  let rect : Input → List Coord := fun p => Source284RectangleTM2.generate (five p,ticks p)
  have ht : IsPolyTime ticks := TM2PairFirst.first_isPolyTime
  have hq : IsPolyTime query := TM2GuardAllStep.second_isPolyTime
  have hf : IsPolyTime five := TM2Compose.isPolyTime_comp ticks
    (TM2UnaryPolynomialIO.unaryPolynomial (Polynomial.C 5)) ht
    (TM2UnaryPolynomialIO.unaryPolynomial_isPolyTime (Polynomial.C 5))
  have hr : IsPolyTime rect := TM2Compose.isPolyTime_comp (fun p => (five p,ticks p))
    Source284RectangleTM2.generate (TM2GuardAllStep.pair_isPolyTime five ticks hf ht)
    Source284RectangleTM2.generate_isPolyTime
  have hm := TM2Compose.isPolyTime_comp (fun p => (query p,rect p))
    (TM2ContextMapGeneric.contextMap hit) (TM2GuardAllStep.pair_isPolyTime query rect hq hr)
    (TM2ContextMapGeneric.contextMap_isPolyTime hit hit_isPolyTime)
  have h := TM2Compose.isPolyTime_comp (fun p : Input => TM2ContextMapGeneric.contextMap hit (query p,rect p))
    (List.flatten : List (List Coord) → List Coord) hm TM2FlattenList.flatten_isPolyTime
  change IsPolyTime (fun p : Input =>
    (TM2ContextMapGeneric.contextMap hit
      (p.2,Source284RectangleTM2.generate (List.replicate 5 true,p.1))).flatten)
  simpa [query,rect,five,ticks,TM2UnaryPolynomialIO.unaryPolynomial,Polynomial.eval_C] using h

theorem candidates_mem (ticks : List Bool) (query i mode : Nat) :
    (i,mode) ∈ candidates (ticks,query) ↔ i < ticks.length ∧ mode < 5 ∧ 5*i+mode = query := by
  simp only [candidates,TM2ContextMapGeneric.contextMap,Source284RectangleTM2.generate_correct,
    List.length_replicate,List.mem_flatten,List.mem_map]
  constructor
  · rintro ⟨ys,⟨p,hp,rfl⟩,hy⟩
    rcases p with ⟨a,b⟩
    have hb := (mem_rectangle 5 ticks.length a b).1 hp
    simp [hit,TM2ListMask.mask,TM2BoundedWitnessGuard.numericNe,code] at hy
    obtain ⟨he,ha,hb'⟩ := hy
    subst a; subst b
    exact ⟨hb.1,hb.2,he⟩
  · rintro ⟨hi,hm,he⟩
    refine ⟨hit (query,(i,mode)),⟨(i,mode),(mem_rectangle _ _ _ _).2 ⟨hi,hm⟩,rfl⟩,?_⟩
    simp [hit,TM2ListMask.mask,TM2BoundedWitnessGuard.numericNe,code,he]

/-- Select the unique matching coordinate, with a total default otherwise. -/
def select (p : Input) : Coord := TM2ListLookup.lookup (candidates p,(0,(0,0)))

theorem select_isPolyTime : IsPolyTime select := by
  let zero : Input → Nat := fun _ => 0
  let fallback : Input → Coord := fun _ => (0,0)
  have hz : IsPolyTime zero := TM2EmptyConstant.zero_isPolyTime
  have hf : IsPolyTime fallback := TM2GuardAllStep.pair_isPolyTime zero zero hz hz
  have hp := TM2GuardAllStep.pair_isPolyTime zero fallback hz hf
  have ha := TM2GuardAllStep.pair_isPolyTime candidates (fun p => (zero p,fallback p))
    candidates_isPolyTime hp
  exact TM2Compose.isPolyTime_comp (fun p : Input => (candidates p,(zero p,fallback p)))
    (TM2ListLookup.lookup (β := Coord)) ha TM2ListLookup.lookup_isPolyTime

theorem select_correct (ticks : List Bool) (query : Nat) (hbound : query < 5*ticks.length) :
    select (ticks,query) = (query/5,query%5) := by
  have hi : query/5 < ticks.length := by omega
  have hm : query%5 < 5 := Nat.mod_lt _ (by decide)
  have he : 5*(query/5)+query%5 = query := by omega
  have hmem := (candidates_mem ticks query (query/5) (query%5)).2 ⟨hi,hm,he⟩
  cases hx : candidates (ticks,query) with
  | nil => simp [hx] at hmem
  | cons head tail =>
      have hh : head ∈ candidates (ticks,query) := by rw [hx]; simp
      rcases head with ⟨a,b⟩
      have hspec := (candidates_mem ticks query a b).1 hh
      have ha : a = query/5 := by omega
      have hb : b = query%5 := by omega
      simp [select,TM2ListLookup.lookup,hx,ha,hb]

end Shared.Beeping.NPcoNP.Source284FiveSearchTM2
