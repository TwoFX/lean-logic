/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import tactic

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
  obtain ⟨x, ⟨n, hn⟩, hx'⟩ := exists_min (set.range f) (set.range_nonempty f),
  subst hn,
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

end my