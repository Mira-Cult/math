import Shared.Beeping.NPcoNP.Source284FiveSearchTM2

/-! A polynomial-time bounded decoder for any fixed positive radix.
The quotient bound is explicitly supplied in unary; the fixed radix is a
compile-time parameter, not an uncharged runtime integer. This prepares the
seven-mode guarded-table row generator but does not construct that generator
or the input-dependent source verifier. -/
namespace Shared.Beeping.NPcoNP.Source284FixedBaseSearchTM2

open ComplexityTheory Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284CountdownSearch (rectangle mem_rectangle)

abbrev Coord := Nat × Nat
abbrev Input := List Bool × Nat

def code (radix : Nat) (p : Coord) : Nat := radix*p.1+p.2

private theorem add_poly {α : Type} [BitstringEncoding α] (f g : α → Nat)
    (hf : IsPolyTime f) (hg : IsPolyTime g) : IsPolyTime (fun x => f x+g x) := by
  have h := TM2Compose.isPolyTime_comp (fun x => (f x,g x)) CNFBinaryPairAdd.addPair
    (TM2GuardAllStep.pair_isPolyTime f g hf hg) CNFBinaryPairAdd.addPair_isPolyTime
  simpa [CNFBinaryPairAdd.addPair] using h

/-- The program may depend on the fixed radix; neither argument is charged as
an unbounded machine word. -/
theorem code_isPolyTime (radix : Nat) : IsPolyTime (code radix) := by
  let first : Coord → Nat := fun p => p.1
  let second : Coord → Nat := fun p => p.2
  have hf : IsPolyTime first := TM2PairFirst.first_isPolyTime
  have hs : IsPolyTime second := TM2GuardAllStep.second_isPolyTime
  have hm : ∀ d : Nat, IsPolyTime (fun p : Coord => d*p.1) := by
    intro d
    induction d with
    | zero => simpa using (TM2EmptyConstant.zero_isPolyTime (α := Coord))
    | succ d ih =>
      have h := add_poly (fun p : Coord => d*p.1) first ih hf
      convert h using 1
      funext p
      simp [first,Nat.succ_mul]
  exact add_poly (fun p : Coord => radix*p.1) second (hm radix) hs

/-- Emit the unique matching coordinate as a singleton. -/
def hit (radix : Nat) (p : Nat × Coord) : List Coord :=
  TM2ListMask.mask (!TM2BoundedWitnessGuard.numericNe (code radix p.2,p.1),[p.2])

theorem hit_isPolyTime (radix : Nat) : IsPolyTime (hit radix) := by
  let query : Nat × Coord → Nat := fun p => p.1
  let coord : Nat × Coord → Coord := fun p => p.2
  let value : Nat × Coord → Nat := fun p => code radix (coord p)
  let neq : Nat × Coord → Bool := fun p => TM2BoundedWitnessGuard.numericNe (value p,query p)
  let flag : Nat × Coord → Bool := fun p => !neq p
  let single : Nat × Coord → List Coord := fun p => [coord p]
  have hq : IsPolyTime query := TM2PairFirst.first_isPolyTime
  have hc : IsPolyTime coord := TM2GuardAllStep.second_isPolyTime
  have hv : IsPolyTime value := TM2Compose.isPolyTime_comp coord (code radix) hc (code_isPolyTime radix)
  have hn : IsPolyTime neq := TM2Compose.isPolyTime_comp (fun p => (value p,query p))
    TM2BoundedWitnessGuard.numericNe (TM2GuardAllStep.pair_isPolyTime value query hv hq)
    TM2BoundedWitnessGuard.numericNe_isPolyTime
  have hf : IsPolyTime flag := TM2Compose.isPolyTime_comp neq (fun b => !b) hn TM2GateDispatch.not_isPolyTime
  have hs : IsPolyTime single := TM2GateCNFPieces.singleton_isPolyTime coord hc
  exact TM2Compose.isPolyTime_comp (fun p => (flag p,single p))
    (TM2ListMask.mask (α := Coord)) (TM2GuardAllStep.pair_isPolyTime flag single hf hs)
      TM2ListMask.mask_isPolyTime

def candidates (radix : Nat) (p : Input) : List Coord :=
  (TM2ContextMapGeneric.contextMap (hit radix)
    (p.2,Source284RectangleTM2.generate (List.replicate radix true,p.1))).flatten

theorem candidates_isPolyTime (radix : Nat) : IsPolyTime (candidates radix) := by
  let ticks : Input → List Bool := fun p => p.1
  let query : Input → Nat := fun p => p.2
  let base : Input → List Bool := fun p => TM2UnaryPolynomialIO.unaryPolynomial (Polynomial.C radix) (ticks p)
  let rect : Input → List Coord := fun p => Source284RectangleTM2.generate (base p,ticks p)
  have ht : IsPolyTime ticks := TM2PairFirst.first_isPolyTime
  have hq : IsPolyTime query := TM2GuardAllStep.second_isPolyTime
  have hb : IsPolyTime base := TM2Compose.isPolyTime_comp ticks
    (TM2UnaryPolynomialIO.unaryPolynomial (Polynomial.C radix)) ht
    (TM2UnaryPolynomialIO.unaryPolynomial_isPolyTime (Polynomial.C radix))
  have hr : IsPolyTime rect := TM2Compose.isPolyTime_comp (fun p => (base p,ticks p))
    Source284RectangleTM2.generate (TM2GuardAllStep.pair_isPolyTime base ticks hb ht)
    Source284RectangleTM2.generate_isPolyTime
  have hm := TM2Compose.isPolyTime_comp (fun p => (query p,rect p))
    (TM2ContextMapGeneric.contextMap (hit radix)) (TM2GuardAllStep.pair_isPolyTime query rect hq hr)
    (TM2ContextMapGeneric.contextMap_isPolyTime (hit radix) (hit_isPolyTime radix))
  have h := TM2Compose.isPolyTime_comp (fun p : Input => TM2ContextMapGeneric.contextMap (hit radix) (query p,rect p))
    (List.flatten : List (List Coord) → List Coord) hm TM2FlattenList.flatten_isPolyTime
  change IsPolyTime (fun p : Input =>
    (TM2ContextMapGeneric.contextMap (hit radix)
      (p.2,Source284RectangleTM2.generate (List.replicate radix true,p.1))).flatten)
  simpa [query,rect,base,ticks,TM2UnaryPolynomialIO.unaryPolynomial,Polynomial.eval_C] using h

theorem candidates_mem (radix : Nat) (ticks : List Bool) (query i mode : Nat) :
    (i,mode) ∈ candidates radix (ticks,query) ↔
      i < ticks.length ∧ mode < radix ∧ radix*i+mode = query := by
  simp only [candidates,TM2ContextMapGeneric.contextMap,Source284RectangleTM2.generate_correct,
    List.length_replicate,List.mem_flatten,List.mem_map]
  constructor
  · rintro ⟨ys,⟨p,hp,rfl⟩,hy⟩
    rcases p with ⟨a,b⟩
    have hb := (mem_rectangle radix ticks.length a b).1 hp
    simp [hit,TM2ListMask.mask,TM2BoundedWitnessGuard.numericNe,code] at hy
    obtain ⟨he,ha,hb'⟩ := hy
    subst a; subst b
    exact ⟨hb.1,hb.2,he⟩
  · rintro ⟨hi,hm,he⟩
    refine ⟨hit radix (query,(i,mode)),⟨(i,mode),(mem_rectangle _ _ _ _).2 ⟨hi,hm⟩,rfl⟩,?_⟩
    simp [hit,TM2ListMask.mask,TM2BoundedWitnessGuard.numericNe,code,he]

/-- Total default `(0,0)` outside the searched rectangle. -/
def select (radix : Nat) (p : Input) : Coord := TM2ListLookup.lookup (candidates radix p,(0,(0,0)))

theorem select_isPolyTime (radix : Nat) : IsPolyTime (select radix) := by
  let zero : Input → Nat := fun _ => 0
  let fallback : Input → Coord := fun _ => (0,0)
  have hz : IsPolyTime zero := TM2EmptyConstant.zero_isPolyTime
  have hf : IsPolyTime fallback := TM2GuardAllStep.pair_isPolyTime zero zero hz hz
  have hp := TM2GuardAllStep.pair_isPolyTime zero fallback hz hf
  have ha := TM2GuardAllStep.pair_isPolyTime (candidates radix) (fun p => (zero p,fallback p))
    (candidates_isPolyTime radix) hp
  exact TM2Compose.isPolyTime_comp (fun p : Input => (candidates radix p,(zero p,fallback p)))
    (TM2ListLookup.lookup (β := Coord)) ha TM2ListLookup.lookup_isPolyTime

theorem select_correct (radix : Nat) (ticks : List Bool) (query : Nat)
    (hpos : 0 < radix) (hbound : query < radix*ticks.length) :
    select radix (ticks,query) = (query/radix,query%radix) := by
  have hi : query/radix < ticks.length := by
    apply (Nat.div_lt_iff_lt_mul hpos).2
    simpa [Nat.mul_comm] using hbound
  have hm : query%radix < radix := Nat.mod_lt _ hpos
  have he : radix*(query/radix)+query%radix = query := Nat.div_add_mod query radix
  have hmem := (candidates_mem radix ticks query (query/radix) (query%radix)).2 ⟨hi,hm,he⟩
  cases hx : candidates radix (ticks,query) with
  | nil => simp [hx] at hmem
  | cons head tail =>
    have hh : head ∈ candidates radix (ticks,query) := by rw [hx]; simp
    rcases head with ⟨a,b⟩
    obtain ⟨_,hb,hcode⟩ := (candidates_mem radix ticks query a b).1 hh
    have ha : a = query/radix := by
      rw [← hcode,Nat.mul_add_div hpos,Nat.div_eq_of_lt hb]
      simp
    have hb' : b = query%radix := by
      rw [← hcode,Nat.mul_add_mod,Nat.mod_eq_of_lt hb]
    simp [select,TM2ListLookup.lookup,hx,ha,hb']

namespace Fixtures
example : select 7 ([false,false],13) = (1,6) := by decide +kernel
example : select 7 ([false,false],14) = (0,0) := by decide +kernel
example : select 7 ([],0) = (0,0) := by decide +kernel
end Fixtures

end Shared.Beeping.NPcoNP.Source284FixedBaseSearchTM2
