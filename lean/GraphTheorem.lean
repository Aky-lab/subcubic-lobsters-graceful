import NamedSpine
namespace Lobster
open Geometry SimpleGraph

/-- The usual unrooted definition in terms of graph distance from a simple path. -/
def IsLobster (G : SimpleGraph V) : Prop :=
  ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ ∀ x, ∃ y ∈ p.support, G.dist y x ≤ 2

/-- Vertex labels are exactly 0,...,n-1. The second equivalence assigns
zero-based edge indices, so its value plus one is the actual difference. -/
def IsGraceful (G : SimpleGraph V) [Fintype V] : Prop :=
  ∃ (f : V ≃ Fin (Fintype.card V)) (d : G.edgeSet ≃ Fin (Fintype.card V - 1)),
    ∀ u v (h : G.Adj u v),
      (d ⟨s(u,v),G.mem_edgeSet.mpr h⟩).val + 1 = gap ((f u).val,(f v).val)

theorem every_subcubic_lobster_is_graceful {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (tree : G.IsTree) (degree : G.maxDegree ≤ 3) (lobster : IsLobster G) :
    IsGraceful G := by
  classical
  obtain ⟨_,_,p,hp,cover⟩ := lobster
  have bound : DegreeBound G.Adj := by
    intro v xs nd adj
    have sub : xs.toFinset ⊆ G.neighborFinset v := by
      intro x hx
      exact (G.mem_neighborFinset v x).mpr (adj x (by simpa using hx))
    calc xs.length = xs.toFinset.card := (List.toFinset_card_of_nodup nd).symm
         _ ≤ (G.neighborFinset v).card := Finset.card_le_card sub
         _ = G.degree v := rfl
         _ ≤ 3 := (G.degree_le_maxDegree v).trans degree
  have cv : Covers G p.support := by
    intro x
    obtain ⟨y,hy,hd⟩ := cover x
    obtain ⟨q,hq⟩ := tree.connected.exists_walk_length_eq_dist y x
    exact ⟨y,hy,near_of_short G q (hq.trans_le hd)⟩
  obtain ⟨s,f,nd,full,adj,hg⟩ := spanning_labels G bound p.support
    ⟨hp.support_nodup,p.isChain_adj_support,p.support_ne_nil,cv⟩
  let n := Fintype.card V
  have size : s.nodes.length = n := by
    have e : s.nodes.toFinset = Finset.univ := Finset.eq_univ_of_forall (by simpa using full)
    rw [← List.toFinset_card_of_nodup nd,e,Finset.card_univ]
  rw [size] at hg
  let F (v : V) : Fin n := ⟨f v, List.mem_range.mp (hg.1.mem_iff.mp
    (List.mem_map.mpr ⟨v,full v,rfl⟩))⟩
  have onto : Function.Surjective F := by
    intro i
    have mem := hg.1.mem_iff.mpr (List.mem_range.mpr i.isLt)
    obtain ⟨v,_,hv⟩ := List.mem_map.mp mem
    exact ⟨v,Fin.ext hv⟩
  let vertexEquiv := Equiv.ofBijective F ((Fintype.bijective_iff_surjective_and_card F).mpr
    ⟨onto,by simp [n]⟩)
  let value : Sym2 V → Nat := Sym2.lift ⟨fun u v => gap (f u,f v),fun _ _ => Nat.add_comm ..⟩
  have realizes (i : Fin (n-1)) : ∃ e : G.edgeSet, value e.val = i.val+1 := by
    have mem : i.val+1 ∈ List.range' 1 (n-1) :=
      List.mem_range'.mpr ⟨i.val,i.isLt,by omega⟩
    have m := hg.2.mem_iff.mpr mem
    simp only [lengths,Segment.map,List.map_map,List.mem_map] at m
    obtain ⟨⟨u,v⟩,hm,val⟩ := m
    exact ⟨⟨s(u,v),G.mem_edgeSet.mpr (adj _ hm)⟩,val⟩
  let E (i : Fin (n-1)) := (realizes i).choose
  have evalE (i) : value (E i).val = i.val+1 := (realizes i).choose_spec
  have inj : Function.Injective E := by
    intro i j h
    have eq := congrArg (fun e : G.edgeSet => value e.val) h
    change value (E i).val = value (E j).val at eq
    rw [evalE,evalE] at eq
    exact Fin.ext (by omega)
  have count : Fintype.card (Fin (n-1)) = Fintype.card G.edgeSet := by
    rw [Fintype.card_fin,G.card_edgeSet]
    have e := tree.card_edgeFinset
    dsimp [n]; omega
  let edgeEquiv := Equiv.ofBijective E ((Fintype.bijective_iff_injective_and_card E).mpr ⟨inj,count⟩)
  refine ⟨vertexEquiv,edgeEquiv.symm,?_⟩
  intro u v ha
  let e : G.edgeSet := ⟨s(u,v),G.mem_edgeSet.mpr ha⟩
  have h := evalE (edgeEquiv.symm e)
  change value (edgeEquiv (edgeEquiv.symm e)).val = _ at h
  rw [edgeEquiv.apply_symm_apply] at h
  exact h.symm

#print axioms Lobster.every_subcubic_lobster_is_graceful
end Lobster
