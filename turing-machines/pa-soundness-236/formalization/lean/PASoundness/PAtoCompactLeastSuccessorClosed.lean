import PASoundness.PAtoCompactLeastSuccessorBranches
import PASoundness.PAtoCompactIntersectionExists

/-! K successor preservation of the represented least-subset property. The
selector's literal code supplies the intersection binder; all syntactic
freshness assumptions are explicit. This does not assert a full arithmetic
domain or proof translation. Compact code 1 is literal self-membership. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactLeastSuccessorClosed
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveClosure
open PASoundness.PAtoCompactPredecessor PASoundness.PAtoCompactGreatestSuccessorCase
open PASoundness.PAtoCompactLeastCounterexample PASoundness.PAtoCompactLeastSuccessorCase
open PASoundness.PAtoCompactLeastSuccessorBranches PASoundness.PAtoCompactIntersectionExists

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def nonempty_vacuity (u v c : Nat) (hcu : c ≠ u) (hcv : c ≠ v) :
    KDerivation (imp (nonemptyCode u v) (allCode c (nonemptyCode u v))) := by
  let f : CompactNamed.Formula := .ex v (.member u v)
  have hf : c ∉ f.names := by simp [f, CompactNamed.Formula.names, hcu, hcv]
  simpa [f, nonemptyCode, CompactNamed.Formula.encode] using f.vacuity c hf

def exists_least_vacuity (u m z c : Nat) (hcu : c ≠ u) (hcm : c ≠ m) (hcz : c ≠ z) :
    KDerivation (imp (existsCode m (leastMemberCode u m z))
      (allCode c (existsCode m (leastMemberCode u m z)))) := by
  let f : CompactNamed.Formula := .ex m (namedLeastMember u m z)
  have hf : c ∉ f.names := by
    simp [f, namedLeastMember, namedBoth, namedEither, CompactNamed.Formula.names, hcu, hcm, hcz]
  simpa [f, namedLeastMember, namedBoth, namedEither, leastMemberCode,
    CompactNamed.Formula.encode, CompactProof.both, CompactProof.neg,
    CompactDerivations.either] using f.vacuity c hf

/-- K constructs and eliminates the selector-chosen intersection witness for
one arbitrary subset u. c is explicitly the selector's predicate code. -/
def least_with_selected_intersection (x y w u k c q a z m r b v : Nat)
    (hc : c = intersectionWitness u x q)
    (fresh : [x,y,w,u,k,c,q,a,z,m,r,b,v].Nodup) :
    KDerivation (imp (successorCode x y w) (imp (subsetCode u y k)
      (imp (leastSubsetsCode x b k a m r)
        (imp (nonemptyCode u v) (existsCode m (leastMemberCode u m z)))))) := by
  have hcu : c ≠ u := by intro h; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil] at fresh; aesop
  have hcv : c ≠ v := by intro h; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil] at fresh; aesop
  have hcx : c ≠ x := by intro h; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil] at fresh; aesop
  have hcy : c ≠ y := by intro h; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil] at fresh; aesop
  have hcw : c ≠ w := by intro h; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil] at fresh; aesop
  have hck : c ≠ k := by intro h; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil] at fresh; aesop
  have hca : c ≠ a := by intro h; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil] at fresh; aesop
  have hcz : c ≠ z := by intro h; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil] at fresh; aesop
  have hcm : c ≠ m := by intro h; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil] at fresh; aesop
  have hcr : c ≠ r := by intro h; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil] at fresh; aesop
  have hcb : c ≠ b := by intro h; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil] at fresh; aesop
  have huq : u ≠ q := by intro h; subst u; simp at fresh
  have hxq : x ≠ q := by intro h; subst x; simp at fresh
  let S := successorCode x y w
  let U := subsetCode u y k
  let L := leastSubsetsCode x b k a m r
  let N := nonemptyCode u v
  let I := intersectionGraph u x c q
  let H := existsCode m (leastMemberCode u m z)
  let Γ := [N,L,U,S]
  have hn : Context Γ N := .hypothesis (by simp [Γ])
  have hl : Context Γ L := .hypothesis (by simp [Γ])
  have hu : Context Γ U := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hpoint : Context Γ (imp I H) := by
    apply Context.deduction
    have hi : Context (I :: Γ) I := Context.head Γ I
    exact .mp (Context.under hn I) (.mp (Context.under hl I) (.mp hi
      (.mp (Context.under hu I) (.mp (Context.under hs I)
        (.closed (least_of_intersection x y w u k c q a z m r b v fresh))))))
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode c h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases h1 : h = N
    · subst h
      exact nonempty_vacuity u v c hcu hcv
    · by_cases h2 : h = L
      · subst h
        exact least_subsets_vacuity x b k a m r c hcx hcb hck hca hcm hcr
      · by_cases h3 : h = U
        · subst h
          exact subset_vacuity u y k c hcu hcy hck
        · have h4 : h = S := ((hh.resolve_left h1).resolve_left h2).resolve_left h3
          subst h
          exact successor_vacuity x y w c hcx hcy hcw
  have hall : Context Γ (allCode c (imp I H)) := Context.generalize c hv hpoint
  have hex : Context Γ (existsCode c I) := by
    have he := intersection_exists u x q huq hxq
    rw [← hc] at he
    exact .closed he
  have hres : Context Γ H := Context.existsElim (exists_least_vacuity u m z c hcu hcm hcz) hall hex
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  exact hres

/-- K successor closure of the displayed least-subset condition. The two
outer subset binders and inner witness binders may be distinct; the fresh
selector witness is eliminated inside the K proof. -/
def successor_least_subsets (x y w u k c q a z m r b v : Nat)
    (hc : c = intersectionWitness u x q)
    (fresh : [x,y,w,u,k,c,q,a,z,m,r,b,v].Nodup) :
    KDerivation (imp (leastSubsetsCode x b k a m r) (imp (successorCode x y w)
      (leastSubsetsCode y u k v m z))) := by
  have hux : u ≠ x := by intro h; subst u; simp at fresh
  have huy : u ≠ y := by intro h; subst u; simp at fresh
  have huw : u ≠ w := by intro h; subst u; simp at fresh
  have huk : u ≠ k := by intro h; subst u; simp at fresh
  have hua : u ≠ a := by intro h; subst u; simp at fresh
  have hum : u ≠ m := by intro h; subst u; simp at fresh
  have hur : u ≠ r := by intro h; subst u; simp at fresh
  have hub : u ≠ b := by intro h; subst u; simp at fresh
  let L := leastSubsetsCode x b k a m r
  let S := successorCode x y w
  let Γ := [S,L]
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hl : Context Γ L := .hypothesis (by simp [Γ])
  have hpoint : Context Γ (imp (subsetCode u y k)
      (imp (nonemptyCode u v) (existsCode m (leastMemberCode u m z)))) := by
    apply Context.deduction
    have hu : Context (subsetCode u y k :: Γ) (subsetCode u y k) := Context.head Γ _
    have himp : Context (subsetCode u y k :: Γ)
        (imp (nonemptyCode u v) (existsCode m (leastMemberCode u m z))) :=
      .mp (Context.under hl _) (.mp hu (.mp (Context.under hs _)
      (.closed (least_with_selected_intersection x y w u k c q a z m r b v hc fresh))))
    exact himp
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode u h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases h1 : h = S
    · subst h
      exact successor_vacuity x y w u hux huy huw
    · have h2 : h = L := hh.resolve_left h1
      subst h
      exact least_subsets_vacuity x b k a m r u hux hub huk hua hum hur
  have hout : Context Γ (leastSubsetsCode y u k v m z) := Context.generalize u hv hpoint
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  exact hout

theorem successor_least_subsets_certificate (x y w u k c q a z m r b v : Nat)
    (hc : c = intersectionWitness u x q)
    (fresh : [x,y,w,u,k,c,q,a,z,m,r,b,v].Nodup) :
    theoremCode (certificate (successor_least_subsets x y w u k c q a z m r b v hc fresh)) =
      imp (leastSubsetsCode x b k a m r) (imp (successorCode x y w)
        (leastSubsetsCode y u k v m z)) :=
  certificate_correct (successor_least_subsets x y w u k c q a z m r b v hc fresh)

end PASoundness.PAtoCompactLeastSuccessorClosed

#print axioms PASoundness.PAtoCompactLeastSuccessorClosed.successor_least_subsets
#print axioms PASoundness.PAtoCompactLeastSuccessorClosed.successor_least_subsets_certificate
