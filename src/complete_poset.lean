/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import tactic
import order.hom.basic
import data.set.lattice

universes u v

variables {α : Type u} {β : Type v}

namespace my

section
variables [partial_order α]

@[ext] class has_supremum (S : set α) :=
(supremum : α)
(upper_bound : ∀ x ∈ S, x ≤ supremum)
(least_upper_bound : ∀ (y : α), (∀ x ∈ S, x ≤ y) → supremum ≤ y)

def _root_.set.supremum (S : set α) [has_supremum S] : α :=
has_supremum.supremum S

lemma le_supremum (S : set α) [has_supremum S] {x : α} (hx : x ∈ S) : x ≤ S.supremum :=
has_supremum.upper_bound _ hx

lemma supremum_le (S : set α) [has_supremum S] {y : α} (hy : ∀ x ∈ S, x ≤ y) : S.supremum ≤ y :=
has_supremum.least_upper_bound _ hy

instance (S : set α) : subsingleton (has_supremum S) :=
⟨λ s₁ s₂, has_supremum.ext _ _ (le_antisymm
  (@has_supremum.least_upper_bound _ _ _ s₁ _ $ @has_supremum.upper_bound _ _ _ s₂)
  (@has_supremum.least_upper_bound _ _ _ s₂ _ $ @has_supremum.upper_bound _ _ _ s₁))⟩

end

class complete_partial_order (α : Type u) extends partial_order α :=
(has_supremum : ∀ (S : set α), has_supremum S)

instance complete_partial_order_has_supremum [complete_partial_order α] (S : set α) : has_supremum S :=
complete_partial_order.has_supremum _

instance : complete_partial_order (set α) :=
{ has_supremum := λ S,
  { supremum := ⋃₀ S,
    upper_bound := λ T, set.subset_sUnion_of_mem,
    least_upper_bound := λ T hT x ⟨y, ⟨hy, hy'⟩⟩, hT _ hy hy' },
  ..(infer_instance : partial_order (set α)) }

theorem knaster_tarski [complete_partial_order α] (f : α → α) (hf : monotone f) : ∃ x, f x = x :=
let s := {x | x ≤ f x}.supremum in
have s ≤ f s, from supremum_le _ $ λ x hx, le_trans hx $ hf $ le_supremum _ hx,
⟨s, le_antisymm (le_supremum _ $ hf this) this⟩

theorem cantor_schroeder_bernstein (f : α → β) (hf : function.injective f) (g : β → α) (hg : function.injective g) :
  nonempty (α ≃ β) :=
begin
  by_cases hβ : nonempty β,
  { haveI hα : nonempty α := nonempty.map g hβ,
    have h : monotone (compl ∘ set.image g ∘ compl ∘ set.image f),
    { exact (compl_antitone _).comp (set.monotone_image.comp_antitone ((compl_antitone _).comp_monotone set.monotone_image)) },
    obtain ⟨P, hP : (g '' (f '' P)ᶜ)ᶜ = P⟩ := knaster_tarski _ h,
    classical,
    refine ⟨equiv.of_bijective (P.piecewise f (function.inv_fun g)) ⟨λ x y hxy, _, _⟩⟩,
    { by_cases hx : x ∈ P,
      { rw [set.piecewise_eq_of_mem _ _ _ hx] at hxy,
        have : y ∈ P,
        { rw [←hP],
          rintro ⟨z, ⟨hz, rfl⟩⟩,
          refine hz ⟨x, ⟨hx, _⟩⟩,
          have : g z ∉ P,
          { rw [←hP, set.mem_compl_iff, not_not],
            exact set.mem_image_of_mem _ hz },
          rw [hxy, set.piecewise_eq_of_not_mem _ _ _ this, function.left_inverse_inv_fun hg] },
        rw [set.piecewise_eq_of_mem _ _ _ this] at hxy,
        exact hf hxy },
      { rw [set.piecewise_eq_of_not_mem _ _ _ hx] at hxy,
        rw [←hP, set.mem_compl_iff, not_not] at hx,
        rcases hx with ⟨z, ⟨hz, rfl⟩⟩,
        rw [function.left_inverse_inv_fun hg] at hxy,
        have hyP : y ∉ P,
        { refine λ hy, hz ⟨y, ⟨hy, _⟩⟩,
          rw [hxy, set.piecewise_eq_of_mem _ _ _ hy] },
        have := hyP,
        rw [←hP, set.mem_compl_iff, not_not] at this,
        rcases this with ⟨w, ⟨hw, rfl⟩⟩,
        rw [hxy, set.piecewise_eq_of_not_mem _ _ _ hyP, function.left_inverse_inv_fun hg] } },
    { simp only [←set.range_iff_surjective, set.range_piecewise, set.eq_univ_iff_forall, set.mem_union, or_iff_not_imp_left],
      refine λ x hx, ⟨g x, ⟨_, function.left_inverse_inv_fun hg _⟩⟩,
      rw [←hP, compl_compl],
      exact set.mem_image_of_mem _ hx } },
  { haveI := not_nonempty_iff.1 hβ,
    refine ⟨⟨f, g, λ x, false.elim (is_empty.false (f x)), λ x, false.elim (is_empty.false x)⟩⟩ }
end

end my