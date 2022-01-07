/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import tactic

open_locale classical
noncomputable theory

universes u v

namespace my

variables {α : Type u} {β : Type v}

section

def _root_.set.least_elements [has_le α] (S : set α) : set α :=
{ x ∈ S | ∀ y ∈ S, x ≤ y }

class well_order (α : Type u) extends linear_order α :=
(exists_min : ∀ (S : set α), S.nonempty → ∃ x ∈ S, ∀ y ∈ S, x ≤ y)

end

def artinian (α : Type u) [has_lt α] : Prop :=
¬∃ f : ℕ → α, ∀ n, f (n + 1) < f n

lemma exists_min [well_order α] (S : set α) : S.nonempty → ∃ x ∈ S, ∀ y ∈ S, x ≤ y :=
well_order.exists_min _

lemma nonempty_least_elements [well_order α] (S : set α) (hS : S.nonempty) : S.least_elements.nonempty :=
let ⟨x, hx, hx'⟩ := exists_min S hS in ⟨x, hx, hx'⟩

lemma subsingleton_least_elements [linear_order α] (S : set α) {x y : α} (hx : x ∈ S.least_elements) (hy : y ∈ S.least_elements) : x = y :=
le_antisymm (hx.2 _ hy.1) (hy.2 _ hx.1)

section
variables [has_lt α] (S : set α) (hS : ∀ x : S, ∃ y : S, (y : α) < x) (s : α) (hs : s ∈ S)

noncomputable def descending_chain : ℕ → S
| 0 := ⟨s, hs⟩
| (n+1) := classical.some $ hS $ descending_chain n

lemma descending_chain_property : ∀ n, (descending_chain S hS s hs (n + 1) : α) < descending_chain S hS s hs n
| 0 := classical.some_spec $ hS $ descending_chain S hS s hs 0
| (n+1) := classical.some_spec $ hS $ descending_chain S hS s hs (n+1)

end

def well_order_of_is_artinian [linear_order α] (h : artinian α) : well_order α :=
{ exists_min := λ S ⟨s, hs⟩,
  begin
    rw artinian at h,
    contrapose! h,
    suffices hS : ∀ x : S, ∃ y : S, (y : α) < x,
    { exact ⟨λ n, descending_chain S hS s hs n, descending_chain_property S hS s hs⟩ },
    rintro ⟨x, hx⟩,
    obtain ⟨y, hy, hy'⟩ := h x hx,
    exact ⟨⟨y, hy⟩, hy'⟩
  end,
  ..(infer_instance : linear_order α) }

lemma is_artinian [well_order α] : artinian α :=
begin
  rintro ⟨f, hf⟩,
  obtain ⟨x, ⟨n, rfl⟩, hx'⟩ := exists_min (set.range f) (set.range_nonempty f),
  exact lt_irrefl _ ((hx' (f (n + 1)) (set.mem_range_self _)).trans_lt (hf n))
end

theorem well_ordered_induction [well_order α] (P : α → Prop) (hP : ∀ x, (∀ y, y < x → P y) → P x) : ∀ x, P x :=
begin
  by_contradiction,
  push_neg at h,
  rcases h with ⟨x, hx⟩,
  obtain ⟨y, hy, hy'⟩ := exists_min { z | ¬P z } ⟨x, hx⟩,
  refine hy (hP _ (λ z hz, _)),
  contrapose! hy',
  exact ⟨z, hy', hz⟩
end

def I [has_lt α] (x : α) : set α :=
{ y | y < x }

@[simp]
lemma mem_I [has_lt α] (x y : α) : x ∈ I y ↔ x < y :=
iff.rfl

lemma iso_apply_least_element [linear_order α] [linear_order β] (f : α ≃o β) (x : α) : f x ∈ (f '' I x)ᶜ.least_elements :=
begin
  refine ⟨by simp, λ y hy, _⟩,
  simp only [not_exists, set.mem_image, not_and, mem_I, set.mem_compl_eq] at hy,
  have := hy (f.symm y),
  contrapose! this,
  simpa only [order_iso.symm_apply_apply, and_true, order_iso.apply_symm_apply, eq_self_iff_true] using f.symm.lt_iff_lt.mpr this
end

instance subsingleton_order_iso [well_order α] [well_order β] : subsingleton (α ≃o β) :=
⟨λ f g, rel_iso.ext $ well_ordered_induction _
  (λ x hx, subsingleton_least_elements (f '' I x)ᶜ
    (iso_apply_least_element _ _)
    ((set.image_congr hx).symm ▸ iso_apply_least_element _ _))⟩

def initial_segment [linear_order α] (Y : set α) : Prop :=
∀ x ∈ Y, ∀ y < x, y ∈ Y

lemma initial_segment_I [linear_order α] (x : α) : initial_segment (I x) :=
λ y hy z hz, hz.trans hy

lemma initial_segment_univ [linear_order α] (x : α) : initial_segment (set.univ : set α) :=
by tidy

lemma initial_segment_def [linear_order α] {Y : set α} (hY : initial_segment Y) {x y : α} (hx : x ∈ Y) (hy : y ≤ x) : y ∈ Y :=
by { rcases eq_or_lt_of_le hy with (h|h), exacts [h.symm ▸ hx, hY _ hx _ h] }

lemma initial_segment_eq [well_order α] {S : set α} (hS : initial_segment S) : S = set.univ ∨ ∃ x, S = I x :=
begin
  refine or_iff_not_imp_left.2 (λ h, _),
  obtain ⟨x', hx'⟩ := (set.ne_univ_iff_exists_not_mem _).1 h,
  obtain ⟨x, hx₁, hx₂⟩ := exists_min Sᶜ ⟨x', hx'⟩,
  refine ⟨x, set.ext (λ y, ⟨λ hy, _, λ hy, _⟩)⟩,
  { contrapose! hx₁,
    exact not_not.2 (initial_segment_def hS hy (not_lt.1 hx₁)) },
  { contrapose! hx₂,
    exact ⟨y, hx₂, hy⟩ }
end

section recursion
variables [well_order α] {G : Π (I : set α), (I → β) → β}

section
variables (G)

structure attempt :=
(to_fun : α → β)
(J : set α)
(hJ : initial_segment J)
(hh : ∀ x ∈ J, to_fun x = G _ (set.restrict to_fun (I x)))

end

instance : has_coe_to_fun (attempt G) (λ _, α → β) := ⟨attempt.to_fun⟩

lemma initial_segment_J (h : attempt G) : initial_segment h.J :=
attempt.hJ _

lemma attempt_eq (h : attempt G) {x : α} : x ∈ h.J → h x = G _ (set.restrict h (I x)) :=
attempt.hh _ _

lemma attempt_well_defined (h h' : attempt G) : ∀ (x : α) (hx : x ∈ h.J) (hx' : x ∈ h'.J), h x = h' x :=
begin
  refine well_ordered_induction _ (λ x hx hx₁ hx₂, _),
  rw [attempt_eq _ hx₁, attempt_eq _ hx₂],
  congr' 1,
  exact funext (λ y, hx _ y.2 (initial_segment_J h _ hx₁ _ y.2) (initial_segment_J h' _ hx₂ _ y.2))
end

def assemble (J : set α) (hJ : initial_segment J) (data : Π x ∈ J, { h : attempt G // x ∈ h.J }) : attempt G :=
{ to_fun := λ x, if h : x ∈ J then (data x h).1 x else G ∅ $ λ ⟨_, h⟩, false.elim h,
  J := J,
  hJ := hJ,
  hh := λ x hx,
  begin
    simp only [hx, dif_pos, subtype.val_eq_coe],
    rw attempt_eq ((data x hx) : attempt G) (data _ hx).2,
    congr' 1,
    ext y,
    have hy : (y : α) ∈ J := hJ _ hx _ y.2,
    simpa [hy] using attempt_well_defined _ _ _ (initial_segment_J _ _ (data _ hx).2 _ y.2) (data _ hy).2
  end }

lemma exists_attempt : ∀ x, ∃ (h : attempt G), x ∈ h.J :=
begin
  refine well_ordered_induction _ (λ x hx, _),

end



end recursion

end my