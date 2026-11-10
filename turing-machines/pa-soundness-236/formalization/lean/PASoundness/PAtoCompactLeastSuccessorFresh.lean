import PASoundness.PAtoCompactLeastSuccessorClosed

/-! Explicit choice of fresh test and selector-witness names for the K
least-subset successor proof. No single-domain closure or induction is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactLeastSuccessorFresh
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactLeastCounterexample
open PASoundness.PAtoCompactIntersectionExists PASoundness.PAtoCompactLeastSuccessorClosed

/-- Two computed names satisfy the selector equality and every distinctness
condition whenever the externally visible syntax names are distinct. -/
def successor_least_subsets_fresh (x y w u k a z m r b v : Nat)
    (fresh : [x,y,w,u,k,a,z,m,r,b,v].Nodup) :
    KDerivation (imp (leastSubsetsCode x b k a m r) (imp (successorCode x y w)
      (leastSubsetsCode y u k v m z))) := by
  let q := x+y+w+u+k+a+z+m+r+b+v+1
  let c := intersectionWitness u x q
  have hqc : q < c := (intersectionWitness_bounds u x q).2.2
  have hq : x < q ∧ y < q ∧ w < q ∧ u < q ∧ k < q ∧ a < q ∧
      z < q ∧ m < q ∧ r < q ∧ b < q ∧ v < q := by
    dsimp [q]
    omega
  have hc : x < c ∧ y < c ∧ w < c ∧ u < c ∧ k < c ∧ a < c ∧
      z < c ∧ m < c ∧ r < c ∧ b < c ∧ v < c := by omega
  have hfull : [x,y,w,u,k,c,q,a,z,m,r,b,v].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil] at fresh ⊢
    have hne : q ≠ c := Nat.ne_of_lt hqc
    have hq' : x ≠ q ∧ y ≠ q ∧ w ≠ q ∧ u ≠ q ∧ k ≠ q ∧ a ≠ q ∧
        z ≠ q ∧ m ≠ q ∧ r ≠ q ∧ b ≠ q ∧ v ≠ q := by omega
    have hc' : x ≠ c ∧ y ≠ c ∧ w ≠ c ∧ u ≠ c ∧ k ≠ c ∧ a ≠ c ∧
        z ≠ c ∧ m ≠ c ∧ r ≠ c ∧ b ≠ c ∧ v ≠ c := by omega
    aesop
  exact successor_least_subsets x y w u k c q a z m r b v rfl hfull

theorem successor_least_subsets_fresh_certificate (x y w u k a z m r b v : Nat)
    (fresh : [x,y,w,u,k,a,z,m,r,b,v].Nodup) :
    theoremCode (certificate (successor_least_subsets_fresh x y w u k a z m r b v fresh)) =
      imp (leastSubsetsCode x b k a m r) (imp (successorCode x y w)
        (leastSubsetsCode y u k v m z)) :=
  certificate_correct (successor_least_subsets_fresh x y w u k a z m r b v fresh)

end PASoundness.PAtoCompactLeastSuccessorFresh

#print axioms PASoundness.PAtoCompactLeastSuccessorFresh.successor_least_subsets_fresh
#print axioms PASoundness.PAtoCompactLeastSuccessorFresh.successor_least_subsets_fresh_certificate
