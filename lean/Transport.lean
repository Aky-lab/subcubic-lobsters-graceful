import Assembly
namespace Lobster
open Geometry

theorem pair_cells (a : Cell α) (b : Cell β) (h : a.shape = b.shape) :
    ∃ t : Cell (α × β), t.map Prod.fst = a ∧ t.map Prod.snd = b := by
  cases a <;> cases b <;> simp [Cell.shape] at h
  · exact ⟨.bare (_,_),rfl,rfl⟩
  · exact ⟨.leaf (_,_) (_,_),rfl,rfl⟩
  · exact ⟨.arm (_,_) (_,_) (_,_),rfl,rfl⟩
  · exact ⟨.fork (_,_) (_,_) (_,_) (_,_),rfl,rfl⟩

theorem pair_lists {xs : List (Cell α)} {ys : List (Cell β)}
    (h : xs.map Cell.shape = ys.map Cell.shape) :
    ∃ ts : List (Cell (α × β)), ts.map (Cell.map Prod.fst) = xs ∧
      ts.map (Cell.map Prod.snd) = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => contradiction
    | cons y ys =>
      simp only [List.map_cons,List.cons.injEq] at h
      obtain ⟨t,ht,ht'⟩ := pair_cells x y h.1
      obtain ⟨ts,hs,hs'⟩ := ih h.2
      exact ⟨t::ts,by simp [ht,hs],by simp [ht',hs']⟩

theorem lookup_pair [DecidableEq α] {xs : List (α × Nat)} (hn : (xs.map Prod.fst).Nodup)
    {v d} (hx : (v,d) ∈ xs) : xs.lookup v = some d := by
  induction xs with
  | nil => contradiction
  | cons p ps ih =>
    rcases p with ⟨u,c⟩
    simp only [List.map_cons,List.nodup_cons] at hn
    rcases List.mem_cons.mp hx with e | h
    · cases e; simp
    · have ne : v ≠ u := by
        intro eq
        exact hn.1 (List.mem_map.mpr ⟨(v,d),h,eq⟩)
      simp [List.lookup_cons, show (v == u) = false by simpa using ne, ih hn.2 h]

/-- Transfer a certificate labeling to any named spine cells of identical
shape. Unique names ensure a single well-defined label per original vertex. -/
theorem transfer_labels {xs : List (Cell α)} {s : Segment α}
    (hs : strip xs = some s) (hn : s.nodes.Nodup)
    {t : Segment Nat} (hw : Witness (xs.map Cell.shape) t) (hg : Good t t.nodes.length) :
    ∃ f : α → Nat, Good (s.map f) s.nodes.length := by
  classical
  obtain ⟨ys,hy,ht⟩ := hw
  obtain ⟨ts,h₁,h₂⟩ := pair_lists hy.symm
  have e₁ := strip_map Prod.fst ts
  have e₂ := strip_map Prod.snd ts
  rw [h₁,hs] at e₁
  rw [h₂,ht] at e₂
  cases he : strip ts with
  | none => rw [he] at e₁; contradiction
  | some z =>
    rw [he] at e₁ e₂
    simp only [Option.map_some, Option.some.injEq] at e₁ e₂
    subst s; subst t
    let f := fun x => (z.nodes.lookup x).getD 0
    have heq (p : α × Nat) (hp : p ∈ z.nodes) : f p.1 = p.2 := by
      show (z.nodes.lookup p.1).getD 0 = p.2
      rw [lookup_pair hn hp]; rfl
    obtain ⟨hi,ho,hc⟩ := strip_closed he
    have hn' : ((z.map Prod.fst).map f).nodes = (z.map Prod.snd).nodes := by
      simp only [Segment.map,List.map_map]
      exact List.map_congr_left heq
    have he' : ((z.map Prod.fst).map f).edges = (z.map Prod.snd).edges := by
      simp only [Segment.map,List.map_map]
      apply List.map_congr_left
      intro p hp
      exact Prod.ext (heq _ (hc _ hp).1) (heq _ (hc _ hp).2)
    refine ⟨f, ?_⟩
    unfold Good lengths at *
    rw [hn',he']
    simpa [Segment.map] using hg

end Lobster
