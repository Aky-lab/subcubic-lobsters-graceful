import Transport
namespace Lobster
open Geometry

/-- The two off-spine layers are disjoint. In layer one we choose a spine
parent; in layer two we choose a layer-one parent. Choices suffice because
the resulting spanning tree uses edges of the input tree. -/
structure Layers (V : Type u) (A : V → V → Prop) (path : List V) where
  head : V → Prop
  parent : V → V
  head_off : ∀ v, head v → v ∉ path
  head_parent : ∀ v, head v → parent v ∈ path ∧ A (parent v) v
  tip_parent : ∀ v, v ∉ path → ¬head v → head (parent v) ∧ A (parent v) v

noncomputable def Layers.owner {A : V → V → Prop} {path} (L : Layers V A path) (v : V) : V := by
  classical
  exact if v ∈ path then v else if L.head v then L.parent v else L.parent (L.parent v)

structure Decor (V : Type u) (A : V → V → Prop) (owner : V → V) (p : V) where
  cell : Cell V
  root : cell.seg.entry = p
  covers : ∀ x, x ∈ cell.seg.nodes ↔ owner x = p
  uniqueNames : cell.seg.nodes.Nodup
  edges : ∀ e ∈ cell.seg.edges, A e.1 e.2

theorem make_cell {A : V → V → Prop} (p : V) (hs : List V) (kids : V → List V)
    (hh : hs.length ≤ 1) (hk : ∀ h ∈ hs, (kids h).length ≤ 2)
    (ha : ∀ h ∈ hs, A p h) (hb : ∀ h ∈ hs, ∀ v ∈ kids h, A h v) :
    ∃ c : Cell V, c.seg.entry = p ∧ c.seg.nodes = p :: hs.flatMap (fun h => h :: kids h)
       ∧ (∀ e ∈ c.seg.edges, A e.1 e.2) ∧ (hs = [] → c.shape = .bare) := by
  cases hs with
  | nil => exact ⟨.bare p,rfl,rfl, by simp [Cell.seg],fun _ => rfl⟩
  | cons h tail =>
    have empty : tail = [] := by
      apply List.length_eq_zero_iff.mp; simp only [List.length_cons] at hh; omega
    subst tail
    have cap := hk h (by simp)
    have hp := ha h (by simp)
    have adj := hb h (by simp)
    generalize eq : kids h = ts at cap adj
    cases ts with
    | nil => exact ⟨.leaf p h,rfl,by simp_all [Cell.seg],by simp_all [Cell.seg],by simp⟩
    | cons a as =>
      cases as with
      | nil => exact ⟨.arm p h a,rfl,by simp_all [Cell.seg], by simp_all [Cell.seg],by simp⟩
      | cons b bs =>
        have empty : bs = [] := by apply List.length_eq_zero_iff.mp; simp only [List.length_cons] at cap; omega
        subst bs
        exact ⟨.fork p h a b,rfl,by simp_all [Cell.seg],by simp_all [Cell.seg],by simp⟩

def DegreeBound (A : V → V → Prop) := ∀ p (xs : List V),
  xs.Nodup → (∀ x ∈ xs, A p x) → xs.length ≤ 3

def EndAt (path : List V) (p : V) := path.head? = some p ∨ path.getLast? = some p

def SpineSlots (A : V → V → Prop) (path : List V) := ∀ p ∈ path,
  (EndAt path p → ∀ x, A p x → x ∈ path) ∧
  (¬EndAt path p → ∃ u ∈ path, ∃ v ∈ path, u ≠ v ∧ A p u ∧ A p v)

theorem decorate {A : V → V → Prop} {path : List V} (L : Layers V A path)
    (all : List V) (nd : all.Nodup) (full : ∀ x, x ∈ all)
    (slots : SpineSlots A path) (deg : DegreeBound A) (sym : ∀ {x y}, A x y → A y x)
    (p : V) (hp : p ∈ path) :
    ∃ d : Decor V A L.owner p, EndAt path p → d.cell.shape = .bare := by
  classical
  let hs := all.filter (fun h => decide (L.head h ∧ L.parent h = p))
  let kids := fun h => all.filter (fun v => decide (v ∉ path ∧ ¬ L.head v ∧ L.parent v = h))
  have mh (h) : h ∈ hs ↔ L.head h ∧ L.parent h = p := by simp [hs,full]
  have mk (h v) : v ∈ kids h ↔ v ∉ path ∧ ¬L.head v ∧ L.parent v = h := by simp [kids,full]
  have headAdj (h) (hm : h ∈ hs) : A p h := by
    obtain ⟨hh,eq⟩ := (mh h).mp hm
    exact eq ▸ (L.head_parent h hh).2
  have tipAdj (h v) (hm : v ∈ kids h) : A h v := by
    obtain ⟨hv,hn,eq⟩ := (mk h v).mp hm
    exact eq ▸ (L.tip_parent v hv hn).2
  have noHeads (he : EndAt path p) : hs = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro h hm
    exact L.head_off _ ((mh h).mp hm).1 ((slots p hp).1 he h (headAdj h hm))
  have off (h) (hh : h ∈ hs) := L.head_off _ ((mh h).mp hh).1
  have nh : hs.Nodup := nd.sublist (List.filter_sublist ..)
  have nk (h) : (kids h).Nodup := nd.sublist (List.filter_sublist ..)
  have width : hs.length ≤ 1 := by
    by_cases he : EndAt path p
    · simp [noHeads he]
    · obtain ⟨u,hu,v,hv,ne,au,av⟩ := (slots p hp).2 he
      have bound := deg p (u::v::hs) (by simp [nh,ne, show u ∉ hs from fun h => off _ h hu,
        show v ∉ hs from fun h => off _ h hv]) (by simpa using And.intro au (And.intro av headAdj))
      simp only [List.length_cons] at bound; omega
  have childWidth (h) (hh : h ∈ hs) : (kids h).length ≤ 2 := by
    have bound := deg h (p::kids h) (by simp [nk, show p ∉ kids h from fun hm => ((mk h p).mp hm).1 hp])
      (by simpa using And.intro (sym (headAdj h hh)) (tipAdj h))
    simp only [List.length_cons] at bound; omega
  obtain ⟨c,root,names,edges,bare⟩ := make_cell p hs kids width childWidth headAdj (fun h _ => tipAdj h)
  refine ⟨⟨c,root,?_,?_,edges⟩,fun he => bare (noHeads he)⟩
  · intro v
    rw [names]
    simp only [List.mem_cons,List.mem_flatMap,mh,mk]
    by_cases vp : v ∈ path
    · have h := fun (x : V) => L.head_off x
      simp [Layers.owner,vp]
      grind
    · by_cases vh : L.head v
      · simp [Layers.owner,vp,vh]
        grind
      · have h := (L.tip_parent v vp vh).1
        simp [Layers.owner,vp,vh]
        grind
  · rw [names]
    cases eq : hs with
    | nil => simp
    | cons h tail =>
      have empty : tail = [] := by
        rw [eq] at width; apply List.length_eq_zero_iff.mp; simp only [List.length_cons] at width; omega
      subst tail
      have hh : h ∈ hs := by simp [eq]
      have hm := (mh h).mp hh
      have ne : p ≠ h := fun e => off _ hh (e ▸ hp)
      have pk : p ∉ kids h := fun e => ((mk h p).mp e).1 hp
      have hk : h ∉ kids h := fun e => ((mk h h).mp e).2.1 hm.1
      simp [ne,pk,hk,nk]

end Lobster
