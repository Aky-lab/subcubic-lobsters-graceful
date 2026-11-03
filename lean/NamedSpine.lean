import PathReduction
namespace Lobster
open Geometry SimpleGraph

theorem words_with_caps (w : List Letter) (left : w.head? = some .bare)
    (right : w.getLast? = some .bare) :
    ∃ t, Witness w t ∧ Good t t.nodes.length := by
  cases w with
  | nil => contradiction
  | cons a rest =>
    simp at left; subst a
    cases rest with
    | nil =>
      exact ⟨(Cell.bare 0).seg,⟨[.bare 0],rfl,rfl⟩,by unfold Good lengths Cell.seg; decide⟩
    | cons b bs =>
      have last : (b::bs).getLast? = some Letter.bare := by simpa using right
      obtain ⟨inner,eq⟩ := List.getLast?_eq_some_iff.mp last
      rw [eq]
      cases inner with
      | nil =>
        exact ⟨join (Cell.bare 0).seg (Cell.bare 1).seg,⟨[.bare 0,.bare 1],rfl,rfl⟩,
          by unfold Good lengths join Cell.seg; decide⟩
      | cons c cs => exact graceful_word (c::cs) (by simp)

theorem cell_ends (c : Cell V) : c.seg.exit = c.seg.entry := by cases c <;> rfl

theorem strip_of_chain {A : V → V → Prop} (cell : V → Cell V) (l : List V) (ne : l ≠ [])
    (ch : l.IsChain A) (root : ∀ v ∈ l, (cell v).seg.entry = v)
    (inside : ∀ v ∈ l, ∀ e ∈ (cell v).seg.edges, A e.1 e.2) :
    ∃ s, strip (l.map cell) = some s ∧ some s.entry = l.head? ∧
      s.nodes = l.flatMap (fun v => (cell v).seg.nodes) ∧ ∀ e ∈ s.edges, A e.1 e.2 := by
  induction l with
  | nil => contradiction
  | cons p ps ih =>
    cases ps with
    | nil => exact ⟨(cell p).seg,rfl,by simp [root],by simp,inside _ (by simp)⟩
    | cons q qs =>
      obtain ⟨t,ht,he,hn,ha⟩ := ih (by simp) (List.isChain_cons_cons.mp ch).2
        (fun v h => root _ (by simp [h])) (fun v h => inside _ (by simp [h]))
      have te : t.entry = q := by simpa using he
      refine ⟨join (cell p).seg t, ?_, by simp [join,root], by simp [join,hn], ?_⟩
      · simp only [List.map_cons, strip] at ht ⊢
        rw [ht]; rfl
      · intro e hm
        simp only [join,List.mem_append,List.mem_singleton] at hm
        rcases hm with (h|rfl)|h
        · exact inside p (by simp) _ h
        · simpa [cell_ends,root p (by simp),te] using (List.isChain_cons_cons.mp ch).1
        · exact ha _ h

/-- Named segment spanning the original graph. Distinct names and all edge
inclusions are verified before the certificate labeling is transferred. -/
theorem spanning_labels {V : Type u} [Fintype V] (G : SimpleGraph V)
    (deg : DegreeBound G.Adj) (p : List V) (hp : PathWitness G p) :
    ∃ (s : Segment V) (f : V → Nat), s.nodes.Nodup ∧ (∀ v, v ∈ s.nodes) ∧
      (∀ e ∈ s.edges, G.Adj e.1 e.2) ∧ Good (s.map f) s.nodes.length := by
  classical
  obtain ⟨l,hl,maximal⟩ := maximal_path G p hp
  obtain ⟨nd,ch,ne,cv⟩ := hl
  let L := layersFrom G l cv
  have slots : SpineSlots G.Adj l := fun v hv =>
    ⟨fun he _ ha => endpoint_closed G l ⟨nd,ch,ne,cv⟩ maximal v he ha,
     interior_neighbors G l nd ch v hv⟩
  let all : List V := Finset.univ.toList
  have make (v) (hv : v ∈ l) := decorate L all (Finset.nodup_toList _) (by simp [all]) slots deg
    (fun h => h.symm) v hv
  let cell (v : V) := if hv : v ∈ l then (make v hv).choose.cell else .bare v
  have cellEq (v) (hv : v ∈ l) : cell v = (make v hv).choose.cell := dif_pos hv
  obtain ⟨s,hs,_,hn,adj⟩ := strip_of_chain cell l ne ch
    (fun v hv => cellEq v hv ▸ (make v hv).choose.root)
    (fun v hv => cellEq v hv ▸ (make v hv).choose.edges)
  have fiber (v) (hv : v ∈ l) (x) : x ∈ (cell v).seg.nodes ↔ L.owner x = v := by
    rw [cellEq v hv]; exact (make v hv).choose.covers x
  have uniqueNames : s.nodes.Nodup := by
    rw [hn,List.nodup_flatMap]
    constructor
    · intro v hv; rw [cellEq v hv]; exact (make v hv).choose.uniqueNames
    · apply nd.imp_of_mem
      intro a b ha hb hab x hx hx'
      exact hab (((fiber a ha x).mp hx).symm.trans ((fiber b hb x).mp hx'))
  have ownerOn (x) : L.owner x ∈ l := by
    by_cases h : x ∈ l
    · simp [Layers.owner,h]
    · by_cases h' : L.head x
      · simpa [Layers.owner,h,h'] using (L.head_parent x h').1
      · simpa [Layers.owner,h,h'] using (L.head_parent _ (L.tip_parent x h h').1).1
  have full (v) : v ∈ s.nodes := by
    rw [hn,List.mem_flatMap]
    exact ⟨L.owner v,ownerOn _,(fiber _ (ownerOn _) _).mpr rfl⟩
  let xs := l.map cell
  have bare (v) (he : EndAt l v) (hv : v ∈ l) : (cell v).shape = .bare := by
    rw [cellEq v hv]; exact (make v hv).choose_spec he
  have first := List.head?_eq_some_head ne
  have last := List.getLast?_eq_some_getLast ne
  have hf : (xs.map Cell.shape).head? = some .bare := by
    simp [xs,List.head?_map,first,bare _ (Or.inl first) (List.head_mem ne)]
  have ht : (xs.map Cell.shape).getLast? = some .bare := by
    simp [xs,List.getLast?_map,last,bare _ (Or.inr last) (List.getLast_mem ne)]
  obtain ⟨t,hw,hg⟩ := words_with_caps _ hf ht
  obtain ⟨f,hf⟩ := transfer_labels hs uniqueNames hw hg
  exact ⟨s,f,uniqueNames,full,adj,hf⟩

end Lobster
