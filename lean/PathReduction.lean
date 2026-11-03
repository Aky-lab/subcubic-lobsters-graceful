import Fibres
import Mathlib.Combinatorics.SimpleGraph.Acyclic
namespace Lobster
open Geometry SimpleGraph
variable {V : Type u} (G : SimpleGraph V)

def WithinTwo (u v : V) := u = v ∨ G.Adj u v ∨ ∃ h, G.Adj u h ∧ G.Adj h v
def Covers (l : List V) := ∀ v, ∃ u ∈ l, WithinTwo G u v
def PathWitness (l : List V) := l.Nodup ∧ l.IsChain G.Adj ∧ l ≠ [] ∧ Covers G l

theorem near_of_short {u v : V} (p : G.Walk u v) (h : p.length ≤ 2) : WithinTwo G u v := by
  cases p with
  | nil => exact Or.inl rfl
  | cons e q =>
    cases q with
    | nil => exact Or.inr (Or.inl e)
    | cons e' q' =>
      cases q' with
      | nil => exact Or.inr (Or.inr ⟨_,e,e'⟩)
      | cons _ _ => simp only [Walk.length_cons] at h; omega

theorem maximal_path [Fintype V] (p : List V) (hp : PathWitness G p) :
    ∃ l, PathWitness G l ∧ ∀ q, PathWitness G q → q.length ≤ l.length := by
  classical
  by_cases ex : ∃ q, PathWitness G q ∧ p.length < q.length
  · obtain ⟨q,hq,lt⟩ := ex
    exact maximal_path q hq
  · exact ⟨p,hp,fun q hq => le_of_not_gt (fun h => ex ⟨q,hq,h⟩)⟩
termination_by Fintype.card V - p.length
decreasing_by have := hq.1.length_le_card; omega

theorem endpoint_closed (l : List V) (hl : PathWitness G l)
    (mx : ∀ q, PathWitness G q → q.length ≤ l.length) (p : V)
    (ep : EndAt l p) {x : V} (ha : G.Adj p x) : x ∈ l := by
  classical
  by_contra outside
  obtain ⟨nd,ch,_,cv⟩ := hl
  rcases ep with left | right
  · have extend : PathWitness G ([x]++l) := by
      refine ⟨by simpa using And.intro outside nd, List.isChain_append.mpr ⟨by simp,ch,?_⟩,by simp,?_⟩
      · simpa [left] using ha.symm
      · intro v; obtain ⟨z,hz,h⟩ := cv v; exact ⟨z,by simp [hz],h⟩
    have := mx _ extend; simp at this
  · have extend : PathWitness G (l++[x]) := by
      refine ⟨by simp [List.nodup_append,nd]; grind, List.isChain_append.mpr ⟨ch,by simp,?_⟩,by simp,?_⟩
      · simpa [right] using ha
      · intro v; obtain ⟨z,hz,h⟩ := cv v; exact ⟨z,by simp [hz],h⟩
    have := mx _ extend; simp at this

theorem interior_neighbors (l : List V) (nd : l.Nodup) (ch : l.IsChain G.Adj) (p : V)
    (hp : p ∈ l) (ne : ¬EndAt l p) :
    ∃ u ∈ l, ∃ v ∈ l, u ≠ v ∧ G.Adj p u ∧ G.Adj p v := by
  obtain ⟨i,hi,eq⟩ := List.getElem_of_mem hp
  have pos : 0 < i := by
    by_contra! z
    have zi : i = 0 := by omega
    subst i
    exact ne (Or.inl (by simpa [List.head?_eq_getElem?] using
      (List.getElem?_eq_getElem hi).trans (congrArg some eq)))
  have next : i+1 < l.length := by
    by_contra! h
    apply ne
    right
    rw [List.getLast?_eq_getElem?]
    have leq : l.length-1 = i := by omega
    simp [leq,hi,eq]
  let u := l[i-1]'(by omega)
  let v := l[i+1]
  refine ⟨u,List.getElem_mem _,v,List.getElem_mem _,?_,?_,?_⟩
  · intro same
    have bad := (List.nodup_iff_injective_getElem.mp nd)
      (a₁ := ⟨i-1,by omega⟩) (a₂ := ⟨i+1,next⟩) same
    have eq' := congrArg Fin.val bad
    simp at eq'
  · have hc := (List.isChain_iff_getElem.mp ch) (i-1) (by omega)
    have e : i-1+1 = i := by omega
    simpa [u,e,eq] using hc.symm
  · simpa [v,eq] using (List.isChain_iff_getElem.mp ch) i next

noncomputable def layersFrom (l : List V) (cv : Covers G l) : Layers V G.Adj l := by
  classical
  let head := fun v => v ∉ l ∧ ∃ p ∈ l, G.Adj p v
  let first := fun v => ∃ p ∈ l, G.Adj p v
  let second := fun v => ∃ h, head h ∧ G.Adj h v
  let parent := fun v => if h : first v then h.choose else if h : second v then h.choose else v
  refine ⟨head,parent,fun _ h => h.1,?_,?_⟩
  · intro v h; have hv : first v := h.2; simpa [parent,hv] using hv.choose_spec
  · intro v off nh
    have nf : ¬first v := fun h => nh ⟨off,h⟩
    have sec : second v := by
      obtain ⟨p,hp,near⟩ := cv v
      rcases near with eq | adj | ⟨h,ph,hv⟩
      · exact (off (eq ▸ hp)).elim
      · exact (nf ⟨p,hp,adj⟩).elim
      · exact ⟨h, ⟨fun hin => nf ⟨h,hin,hv⟩,p,hp,ph⟩,hv⟩
    simpa [parent,nf,sec] using sec.choose_spec

end Lobster
