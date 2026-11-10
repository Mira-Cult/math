import PASoundness.PAtoCompactMultiplicationGraph
import PASoundness.PAtoCompactProductIndex

/-! Standard-HF existence of a represented graph for the proposed product.
Finite assembly here is external semantics, not K collection or arithmetic
proof transport. -/
namespace PASoundness.PAtoCompactMultiplicationComplete
open PASoundness.CompactMatrix PASoundness.HFCoding
open PASoundness.PAtoCompactMultiplicationCandidate
open PASoundness.PAtoCompactMultiplicationGraph PASoundness.PAtoCompactProductIndex

private theorem ordinal_bit (i n : Nat) :
    bit (ordinal n).code (ordinal i).code = true ↔ i < n := by
  change ordinal i ∈ ordinal n ↔ i < n
  exact ordinal_mem_ordinal i n

private theorem ordinal_code_eq (i j : Nat) :
    (ordinal i).code = (ordinal j).code ↔ i = j :=
  ⟨fun h => ordinal_code_strictMono.injective h, fun h => h ▸ rfl⟩

private theorem index_of_member (n a : Nat) (h : bit (ordinal n).code a = true) :
    ∃ i < n, a = (ordinal i).code := by
  have hm : (⟨a⟩ : Object) ∈ ordinal n := h
  obtain ⟨i,hi,he⟩ := (mem_ordinal _ _).mp hm
  exact ⟨i,hi,congrArg Object.code he⟩

/-- The explicit standard-HF graph realizes the semantic product relation
at the three finite ordinals. -/
theorem ordinal_product_semantics (m n : Nat) :
    productSemantics (ordinal m).code (ordinal n).code (ordinal (m*n)).code := by
  let g := (productGraph m n).code
  refine ⟨g, ?_, ?_, ?_⟩
  · intro a ha b hb
    obtain ⟨i,hi,rfl⟩ := index_of_member m a ha
    obtain ⟨j,hj,rfl⟩ := index_of_member n b hb
    refine ⟨(ordinal (i*n+j)).code, (ordinal_bit _ _).mpr (linear_lt_product m n i j hi hj), ?_, ?_⟩
    · exact (product_graph_edge m n _ _ _).mpr ⟨i,hi,j,hj,rfl,rfl,rfl⟩
    · intro c' hc' hed
      obtain ⟨i',hi',j',hj',hai,hbj,hc⟩ := (product_graph_edge m n _ _ _).mp hed
      have hii : i = i' := (ordinal_code_eq _ _).mp hai
      have hjj : j = j' := (ordinal_code_eq _ _).mp hbj
      subst i'
      subst j'
      exact hc
  · intro c hc
    obtain ⟨k,hk,hc⟩ := index_of_member (m*n) c hc
    obtain ⟨i,hi,j,hj,hkij⟩ := linear_decompose m n k hk
    subst k
    subst c
    refine ⟨(ordinal i).code,(ordinal j).code, (ordinal_bit _ _).mpr hi,
      (ordinal_bit _ _).mpr hj, (product_graph_edge m n _ _ _).mpr ⟨i,hi,j,hj,rfl,rfl,rfl⟩, ?_⟩
    intro a' b' ha' hb' hed
    obtain ⟨i',hi',j',hj',ha,hb,hc⟩ := (product_graph_edge m n _ _ _).mp hed
    have hnum := (ordinal_code_eq _ _).mp hc
    have ⟨hii,hjj⟩ := linear_unique n i j i' j' hj hj' hnum
    subst i'
    subst j'
    exact ⟨ha,hb⟩
  · intro a b c a' b' c' ha hb hc ha' hb' hc' he he'
    obtain ⟨i,hi,j,hj,rfl,rfl,rfl⟩ := (product_graph_edge m n _ _ _).mp he
    obtain ⟨i',hi',j',hj',rfl,rfl,rfl⟩ := (product_graph_edge m n _ _ _).mp he'
    simp only [ordinal_bit, ordinal_code_eq]
    exact linear_lt_iff n i j i' j' hj hj'

end PASoundness.PAtoCompactMultiplicationComplete

#print axioms PASoundness.PAtoCompactMultiplicationComplete.ordinal_product_semantics
