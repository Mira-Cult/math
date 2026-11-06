import Shared.Beeping.NPcoNP.Source284RectangleTM2
import Shared.Beeping.NPcoNP.Source284BoundedPairTM2
import Shared.ComplexityBridge.TM2ListMask
import Shared.ComplexityBridge.TM2GateDispatch

/-! A finite list-valued search through a unary-bounded rectangle. Each
candidate pair is encoded by a charged bounded pairing computation and a
binary comparison; matching pairs are emitted as singleton lists and the
blocks are flattened. This is a construction on explicitly supplied unary
bounds, not an unbounded natural pairing or a table compiler. -/
namespace Shared.Beeping.NPcoNP.Source284BoundedSearchTM2

open Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284BoundedPairTM2
open Shared.Beeping.NPcoNP.Source284CountdownSearch

abbrev Coord := Nat × Nat
abbrev Context := List Bool × Nat
abbrev Entry := Context × Coord
abbrev Input := (List Bool × List Bool) × Nat

def hit (p : Entry) : List Coord :=
  TM2ListMask.mask
    (!TM2BoundedWitnessGuard.numericNe (pairBounded (p.1.1,p.2),p.1.2), [p.2])

theorem hit_isPolyTime : ComplexityTheory.IsPolyTime hit := by
  let ctx : Entry → Context := fun p => p.1
  let budget : Entry → List Bool := fun p => p.1.1
  let query : Entry → Nat := fun p => p.1.2
  let coord : Entry → Coord := fun p => p.2
  let value : Entry → Nat := fun p => pairBounded (budget p,coord p)
  let neq : Entry → Bool := fun p => TM2BoundedWitnessGuard.numericNe (value p,query p)
  let flag : Entry → Bool := fun p => !neq p
  let singleton : Entry → List Coord := fun p => [coord p]
  have hc : ComplexityTheory.IsPolyTime ctx := TM2PairFirst.first_isPolyTime
  have hb : ComplexityTheory.IsPolyTime budget :=
    TM2Compose.isPolyTime_comp ctx (fun p : Context => p.1) hc TM2PairFirst.first_isPolyTime
  have hq : ComplexityTheory.IsPolyTime query :=
    TM2Compose.isPolyTime_comp ctx (fun p : Context => p.2) hc TM2GuardAllStep.second_isPolyTime
  have hv : ComplexityTheory.IsPolyTime coord := TM2GuardAllStep.second_isPolyTime
  have hp : ComplexityTheory.IsPolyTime value :=
    TM2Compose.isPolyTime_comp (fun p => (budget p,coord p)) pairBounded
      (TM2GuardAllStep.pair_isPolyTime budget coord hb hv) pairBounded_isPolyTime
  have hn : ComplexityTheory.IsPolyTime neq :=
    TM2Compose.isPolyTime_comp (fun p => (value p,query p)) TM2BoundedWitnessGuard.numericNe
      (TM2GuardAllStep.pair_isPolyTime value query hp hq) TM2BoundedWitnessGuard.numericNe_isPolyTime
  have hf : ComplexityTheory.IsPolyTime flag :=
    TM2Compose.isPolyTime_comp neq (fun b => !b) hn TM2GateDispatch.not_isPolyTime
  have hs : ComplexityTheory.IsPolyTime singleton := TM2GateCNFPieces.singleton_isPolyTime coord hv
  have h := TM2Compose.isPolyTime_comp (fun p => (flag p,singleton p))
    (TM2ListMask.mask (α := Coord)) (TM2GuardAllStep.pair_isPolyTime flag singleton hf hs)
      TM2ListMask.mask_isPolyTime
  exact h

/-- Search arbitrary supplied coordinates using one common unary budget.
Coordinates beyond it are explicitly clipped by `pairBounded`. -/
def collect (p : Context × List Coord) : List Coord :=
  (TM2ContextMapGeneric.contextMap hit p).flatten

theorem collect_isPolyTime : ComplexityTheory.IsPolyTime collect := by
  exact TM2Compose.isPolyTime_comp (TM2ContextMapGeneric.contextMap hit)
    (List.flatten : List (List Coord) → List Coord)
    (TM2ContextMapGeneric.contextMap_isPolyTime hit hit_isPolyTime)
    TM2FlattenList.flatten_isPolyTime

/-- The two unary bounds together provide enough tokens for either coordinate. -/
def searchMatches (p : Input) : List Coord :=
  collect ((p.1.1 ++ p.1.2,p.2),Source284RectangleTM2.generate p.1)

theorem searchMatches_isPolyTime : ComplexityTheory.IsPolyTime searchMatches := by
  let bounds : Input → List Bool × List Bool := fun p => p.1
  let query : Input → Nat := fun p => p.2
  let budget : Input → List Bool := fun p => p.1.1 ++ p.1.2
  let rect : Input → List Coord := fun p => Source284RectangleTM2.generate p.1
  have hb : ComplexityTheory.IsPolyTime bounds := TM2PairFirst.first_isPolyTime
  have hq : ComplexityTheory.IsPolyTime query := TM2GuardAllStep.second_isPolyTime
  have hbudget : ComplexityTheory.IsPolyTime budget :=
    TM2Compose.isPolyTime_comp bounds (TM2ListAppend.append (α := Bool)) hb TM2ListAppend.append_isPolyTime
  have hr : ComplexityTheory.IsPolyTime rect :=
    TM2Compose.isPolyTime_comp bounds Source284RectangleTM2.generate hb Source284RectangleTM2.generate_isPolyTime
  have hc := TM2GuardAllStep.pair_isPolyTime budget query hbudget hq
  have ha := TM2GuardAllStep.pair_isPolyTime (fun p => (budget p,query p)) rect hc hr
  exact TM2Compose.isPolyTime_comp (fun p => ((budget p,query p),rect p)) collect ha collect_isPolyTime

/-- Pointwise meaning of the emitted list. This is enough to identify exactly
the finite live coordinate if it exists; list-to-option decoding is separate. -/
theorem searchMatches_mem (nTokens eTokens : List Bool) (s e q : Nat) :
    (e,q) ∈ searchMatches ((nTokens,eTokens),s) ↔
      e < eTokens.length ∧ q < nTokens.length ∧ Nat.pair e q = s := by
  simp only [searchMatches, collect, TM2ContextMapGeneric.contextMap, Source284RectangleTM2.generate_correct,
    List.mem_flatten, List.mem_map]
  constructor
  · rintro ⟨ys, ⟨p, hp, rfl⟩, hy⟩
    rcases p with ⟨a,b⟩
    have hb := (mem_rectangle nTokens.length eTokens.length a b).1 hp
    have hpa := pairBounded_correct (nTokens ++ eTokens) a b (by simp; omega) (by simp; omega)
    simp [hit, TM2ListMask.mask, TM2BoundedWitnessGuard.numericNe, hpa] at hy
    obtain ⟨hpair, heq⟩ := hy
    rcases heq with ⟨rfl,rfl⟩
    exact ⟨hb.1,hb.2,hpair⟩
  · rintro ⟨he,hq,hpair⟩
    refine ⟨hit ((nTokens ++ eTokens,s),(e,q)), ⟨(e,q), (mem_rectangle _ _ _ _).2 ⟨he,hq⟩, rfl⟩, ?_⟩
    have hp := pairBounded_correct (nTokens ++ eTokens) e q (by simp; omega) (by simp; omega)
    simp [hit, TM2ListMask.mask, TM2BoundedWitnessGuard.numericNe, hp, hpair]

theorem searchMatches_mem_iff_search (nTokens eTokens : List Bool) (s e q : Nat) :
    (e,q) ∈ searchMatches ((nTokens,eTokens),s) ↔
      search nTokens.length eTokens.length s = some (e,q) := by
  rw [searchMatches_mem, search_some_iff]

end Shared.Beeping.NPcoNP.Source284BoundedSearchTM2
