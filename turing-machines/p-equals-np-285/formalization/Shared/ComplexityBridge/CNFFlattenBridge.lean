import Shared.ComplexityBridge.TM2FlattenBlocksCanonical
import Shared.ComplexityBridge.TM2WitnessRaw

namespace Shared.ComplexityBridge.CNFFlattenBridge
open Shared.ComplexityBridge.CNF

/-- Factor successful elementwise optional decoding into its two passes. -/
theorem mapM_factor {α β γ : Type} (g : α → Option β) (h : β → Option γ)
    (xs : List α) (ys : List γ) (hh : xs.mapM (fun a => (g a).bind h) = some ys) :
    ∃ zs : List β, xs.mapM g = some zs ∧ zs.mapM h = some ys := by
  induction xs generalizing ys with
  | nil =>
    simp at hh
    subst ys
    exact ⟨[],rfl,rfl⟩
  | cons x xs ih =>
    cases hg : g x with
    | none => simp [List.mapM_cons,hg] at hh
    | some z =>
      cases hz : h z with
      | none => simp [List.mapM_cons,hg,hz] at hh
      | some y =>
        cases ht : xs.mapM (fun a => (g a).bind h) with
        | none => simp [List.mapM_cons,hg,hz,ht] at hh
        | some rest =>
          simp [List.mapM_cons,hg,hz,ht] at hh
          subst ys
          obtain ⟨zs,hg',hh'⟩ := ih rest ht
          exact ⟨z::zs,by simp [List.mapM_cons,hg,hg'],by simp [List.mapM_cons,hz,hh']⟩

/-- Successful elementwise list decoding commutes with flattening. -/
theorem mapM_flatten {α β : Type} (f : α → Option β) (groups : List (List α)) (decoded : List (List β))
    (h : groups.mapM (List.mapM f) = some decoded) :
    groups.flatten.mapM f = some decoded.flatten := by
  induction groups generalizing decoded with
  | nil => simp at h; subst decoded; rfl
  | cons xs groups ih =>
    cases hx : xs.mapM f with
    | none => simp [List.mapM_cons,hx] at h
    | some ys =>
      cases ht : groups.mapM (List.mapM f) with
      | none => simp [List.mapM_cons,hx,ht] at h
      | some rest =>
        simp [List.mapM_cons,hx,ht] at h
        subst decoded
        simp only [List.flatten_cons,List.mapM_append,hx,Option.bind_some]
        rw [ih rest ht]
        rfl

/-- A successful clause-level block parse reconstructs every input clause. -/
theorem blocks_map_sound (raw : List (List Bool)) (groups : List (List (List Bool)))
    (h : raw.mapM BitstringEncoding.undelimitBlocks = some groups) :
    raw = groups.map (fun xs => (xs.map BitstringEncoding.delimit).flatten) := by
  induction raw generalizing groups with
  | nil => simp at h; subst groups; rfl
  | cons x raw ih =>
    cases hx : BitstringEncoding.undelimitBlocks x with
    | none => simp [List.mapM_cons,hx] at h
    | some xs =>
      cases ht : raw.mapM BitstringEncoding.undelimitBlocks with
      | none => simp [List.mapM_cons,hx,ht] at h
      | some rest =>
        simp [List.mapM_cons,hx,ht] at h
        subst groups
        simp only [List.map_cons]
        rw [← Shared.ComplexityBridge.CNFWitness.blocks_sound x xs hx,ih rest ht]

/-- Flattening the input clause payloads preserves the original literal block
framing and the occurrence order. Clause boundaries themselves are discarded. -/
theorem flatten_clause_frames (groups : List (List (List Bool))) :
    (groups.map (fun xs => (xs.map BitstringEncoding.delimit).flatten)).flatten =
      Shared.ComplexityBridge.TM2WitnessLookup.frames groups.flatten := by
  induction groups with
  | nil => rfl
  | cons xs groups ih =>
    simp only [List.map_cons,List.flatten_cons,Shared.ComplexityBridge.TM2WitnessLookup.frames,
      List.flatMap_append] at *
    simp only [List.flatMap] at *
    rw [ih]

/-- For every successful canonical CNF parse, the outer flattening machine's
output is exactly the sequence of framed raw literal encodings in occurrence
order, and those literal encodings decode to the formula's flattened list. -/
theorem parse_flatten_correct (input : List Bool) (formula : Formula) (h : parse input = some formula) :
    ∃ clauses : List (List Bool), ∃ groups : List (List (List Bool)),
      BitstringEncoding.undelimitBlocks input = some clauses ∧
      clauses.mapM BitstringEncoding.undelimitBlocks = some groups ∧
      groups.flatten.mapM (BitstringEncoding.bitDecode (α := Literal)) = some formula.flatten ∧
      Shared.ComplexityBridge.TM2FlattenBlocksTotal.decodeResult input =
        true::Shared.ComplexityBridge.TM2WitnessLookup.frames groups.flatten := by
  change (BitstringEncoding.undelimitBlocks input).bind (List.mapM (BitstringEncoding.bitDecode (α := Clause))) = some formula at h
  cases hc : BitstringEncoding.undelimitBlocks input with
  | none => simp [hc] at h
  | some clauses =>
    have hclause : clauses.mapM (BitstringEncoding.bitDecode (α := Clause)) = some formula := by simpa [hc] using h
    have hfactor : clauses.mapM (fun c => (BitstringEncoding.undelimitBlocks c).bind
        (List.mapM (BitstringEncoding.bitDecode (α := Literal)))) = some formula := by
      exact hclause
    obtain ⟨groups,hgroups,hdecode⟩ := mapM_factor BitstringEncoding.undelimitBlocks
      (List.mapM (BitstringEncoding.bitDecode (α := Literal))) clauses formula hfactor
    refine ⟨clauses,groups,rfl,hgroups,mapM_flatten _ groups formula hdecode,?_⟩
    have hclauses := blocks_map_sound clauses groups hgroups
    simp only [Shared.ComplexityBridge.TM2FlattenBlocksTotal.decodeResult,hc,Option.map]
    change true::clauses.flatten = _
    rw [hclauses,flatten_clause_frames]


/-- Every successfully decoded raw literal has raw name bits whose numeric
decoding is the canonical literal variable. -/
theorem raw_literals_factor (raw : List (List Bool)) (literals : List Literal)
    (h : raw.mapM (BitstringEncoding.bitDecode (α := Literal)) = some literals) :
    ∃ namesAndSigns : List (List Bool × Bool),
      raw.mapM Shared.ComplexityBridge.TM2LiteralParse.literalBits = some namesAndSigns ∧
      namesAndSigns.map (fun p => (Computability.decodeNat p.1,p.2)) = literals := by
  have hh : raw.mapM (fun r => (Shared.ComplexityBridge.TM2LiteralParse.literalBits r).bind
      (fun p => some (Computability.decodeNat p.1,p.2))) = some literals := by
    have he : (fun r => (Shared.ComplexityBridge.TM2LiteralParse.literalBits r).bind
        (fun p => some (Computability.decodeNat p.1,p.2))) =
        (BitstringEncoding.bitDecode (α := Literal)) := by
      funext r
      rw [Shared.ComplexityBridge.TM2LiteralParse.literalBits_decode]
      cases Shared.ComplexityBridge.TM2LiteralParse.literalBits r <;> rfl
    rw [he]
    exact h
  obtain ⟨names,hn,hm⟩ := mapM_factor Shared.ComplexityBridge.TM2LiteralParse.literalBits
    (fun p => some (Computability.decodeNat p.1,p.2)) raw literals hh
  refine ⟨names,hn,?_⟩
  have hpure : ∀ xs : List (List Bool × Bool),
      xs.mapM (fun p => some (Computability.decodeNat p.1,p.2)) =
        some (xs.map (fun p => (Computability.decodeNat p.1,p.2))) := by
    intro xs
    induction xs with
    | nil => rfl
    | cons p xs ih => simp [List.mapM_cons,ih]
  rw [hpure] at hm
  exact Option.some.inj hm

/-- The raw name sequence extracted from successful literal parsing decodes
exactly to the verifier's variable-occurrence sequence. -/
theorem parse_occurrences_correct (input : List Bool) (formula : Formula) (h : parse input = some formula) :
    ∃ clauses : List (List Bool), ∃ groups : List (List (List Bool)), ∃ names : List (List Bool × Bool),
      BitstringEncoding.undelimitBlocks input = some clauses ∧
      clauses.mapM BitstringEncoding.undelimitBlocks = some groups ∧
      groups.flatten.mapM Shared.ComplexityBridge.TM2LiteralParse.literalBits = some names ∧
      (names.map Prod.fst).map Computability.decodeNat = variableOccurrences formula ∧
      Shared.ComplexityBridge.TM2FlattenBlocksTotal.decodeResult input =
        true::Shared.ComplexityBridge.TM2WitnessLookup.frames groups.flatten := by
  obtain ⟨clauses,groups,hc,hg,hl,hflat⟩ := parse_flatten_correct input formula h
  obtain ⟨names,hn,hdecode⟩ := raw_literals_factor groups.flatten formula.flatten hl
  refine ⟨clauses,groups,names,hc,hg,hn,?_,hflat⟩
  unfold variableOccurrences
  have hp := congrArg (List.map Prod.fst) hdecode
  simpa [List.map_map,Function.comp_def] using hp


/-- Once literal parsing produces the raw name list, the proved finite lookup
uses precisely the same first-occurrence valuation as the CNF verifier. -/
theorem parse_lookup_correct (input : List Bool) (formula : Formula) (h : parse input = some formula) :
    ∃ clauses : List (List Bool), ∃ groups : List (List (List Bool)), ∃ names : List (List Bool × Bool),
      groups.flatten.mapM Shared.ComplexityBridge.TM2LiteralParse.literalBits = some names ∧
      Shared.ComplexityBridge.TM2FlattenBlocksTotal.decodeResult input =
        true::Shared.ComplexityBridge.TM2WitnessLookup.frames groups.flatten ∧
      ∀ witness query : List Bool,
        Shared.ComplexityBridge.TM2WitnessLookup.lookupRaw
          (Shared.ComplexityBridge.TM2WitnessLookup.frames (names.map Prod.fst)) witness query =
        assignment (variableOccurrences formula) witness (Computability.decodeNat query) := by
  obtain ⟨clauses,groups,names,hc,hg,hn,hvars,hflat⟩ := parse_occurrences_correct input formula h
  refine ⟨clauses,groups,names,hn,hflat,?_⟩
  intro witness query
  rw [Shared.ComplexityBridge.TM2WitnessLookup.lookupRaw_frames,
    Shared.ComplexityBridge.RawCNFLookup.lookup_correct,hvars]

namespace Fixtures
/-- A missing end marker is rejected by the outer flattening parser. -/
example : Shared.ComplexityBridge.TM2FlattenBlocksTotal.decodeResult [false,true] = [false] := by decide
/-- Flattening does not retain the distinction between zero clauses and one
empty clause; a complete verifier must retain or reparse clause boundaries. -/
example : Shared.ComplexityBridge.TM2FlattenBlocksTotal.decodeResult [] =
    Shared.ComplexityBridge.TM2FlattenBlocksTotal.decodeResult [false] := by decide
example : CNF.sat [] = true ∧ CNF.sat [false] = false := by decide
end Fixtures

end Shared.ComplexityBridge.CNFFlattenBridge
