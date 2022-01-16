/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import tactic well_order logic.small

open_locale classical
noncomputable theory

universes u v

namespace my

@[ext]
structure well_ordered_type :=
(type : Type u)
[well_order_type : well_order type]

instance : has_coe_to_sort well_ordered_type.{u} (Type u) := ⟨well_ordered_type.type⟩

instance well_order_well_ordered_type (α : well_ordered_type.{u}) : well_order α :=
well_ordered_type.well_order_type _

instance order_iso_setoid : setoid (well_ordered_type.{u}) :=
{ r := λ α β, nonempty (α ≃o β),
  iseqv := ⟨λ α, ⟨order_iso.refl _⟩, λ α β ⟨f⟩, ⟨f.symm⟩, λ α β γ ⟨f⟩ ⟨g⟩, ⟨f.trans g⟩⟩ }

def ordinal := quotient my.order_iso_setoid.{u}
def order_type (α : Type u) [well_order α] : ordinal.{u} := ⟦⟨α⟩⟧

instance : linear_order ordinal.{u} :=
{ le := quotient.lift₂ (λ α β, ↥α ≺ ↥β)
  begin
    rintro α β α' β' ⟨f⟩ ⟨g⟩,
    simp only [eq_iff_iff, iis_iff_exists_strict_mono],
    refine ⟨_, _⟩,
    { rintro ⟨u, hu, hu'⟩,
      refine ⟨(g ∘ u) ∘ f.symm, g.strict_mono.comp (hu.comp f.symm.strict_mono), _⟩,
      rwa [f.symm.surjective.range_comp, set.range_comp, initial_segment_of_order_iso] },
    { rintro ⟨u, hu, hu'⟩,
      refine ⟨(g.symm ∘ u) ∘ f, (g.symm.strict_mono.comp hu).comp f.strict_mono, _⟩,
      rwa [f.surjective.range_comp, set.range_comp, initial_segment_of_order_iso] }
  end,
  le_refl := by { rintro ⟨α⟩, exact well_order_refl },
  le_trans := by { rintro ⟨α⟩ ⟨β⟩ ⟨γ⟩, exact well_order_trans },
  le_antisymm := by { rintro ⟨α⟩ ⟨β⟩ hαβ hβα, exact quotient.sound (well_order_antisymm hαβ hβα) },
  le_total := by { rintro ⟨α⟩ ⟨β⟩, exact well_order_total },
  decidable_le := infer_instance,
  decidable_eq := infer_instance,
  decidable_lt := infer_instance }

@[simp] lemma mk_eq_order_type {α : Type u} [well_order α] : (⟦⟨α⟩⟧ : ordinal.{u}) = order_type α :=
rfl

@[simp] lemma quot_mk_eq_order_type {α : well_ordered_type.{u}} : quot.mk setoid.r α = order_type α :=
begin
  rw [order_type],
  congr' 1,
  ext; refl
end

@[simp] lemma order_type_le_iff {α β : Type u} [well_order α] [well_order β] : order_type α ≤ order_type β ↔ α ≺ β :=
iff.rfl

lemma order_type_eq_iff {α β : Type u} [well_order α] [well_order β] : order_type α = order_type β ↔ nonempty (α ≃o β) :=
quotient.eq

lemma order_type_lt_iff {α β : Type u} [well_order α] [well_order β] :
  order_type α < order_type β ↔ ∃ (f : α → β), strict_mono f ∧ ∃ y, set.range f = I y :=
begin
  rw [lt_iff_le_and_ne, order_type_le_iff, iis_iff_exists_strict_mono],
  refine ⟨_, _⟩,
  { rintro ⟨⟨f, ⟨hf, hf'⟩⟩, h⟩,
    refine ⟨f, hf, _⟩,
    rcases initial_segment_eq hf' with (hrf|h),
    { exact false.elim (h (order_type_eq_iff.2 ⟨hf.order_iso_of_surjective _ (set.range_iff_surjective.1 hrf)⟩)) },
    { exact h } },
  { rintro ⟨f, hf, ⟨y, hy⟩⟩,
    refine ⟨⟨f, hf, hy.symm ▸ initial_segment_I _⟩, λ h, _⟩,
    obtain ⟨g⟩ := order_type_eq_iff.1 h,
    have := surjective_of_initial_segment_range (f ∘ g.symm) (hf.comp g.symm.strict_mono) _,
    { rw [←set.range_iff_surjective, g.symm.surjective.range_comp, hy] at this,
      exact I_ne_univ _ this },
    { rw [g.symm.surjective.range_comp, hy],
      exact initial_segment_I _ } }
end

def order_iso_I_order_type (α : Type u) [well_order α] : α ≃o I (order_type α) :=
begin
  refine strict_mono.order_iso_of_surjective
    (λ x, ⟨order_type (I x), order_type_lt_iff.2 ⟨subtype.val, λ x y, id, ⟨x, subtype.range_val⟩⟩⟩) _ _,
  { intros x y hxy,
    simp only [subtype.mk_lt_mk, order_type_lt_iff],
    refine ⟨λ x, ⟨x.1, lt_trans x.2 hxy⟩, λ x y, id, ⟨⟨x, hxy⟩, set.ext _⟩⟩,
    rintro ⟨z, hz⟩,
    refine ⟨_, _⟩,
    { rintro ⟨w, hw⟩,
      simp only [subtype.mk_eq_mk, subtype.val_eq_coe] at hw,
      subst hw,
      exact w.2 },
    { rintro (hz' : z < x),
      exact ⟨⟨z, hz'⟩, rfl⟩ } },
  { rintro ⟨⟨β⟩, hβ⟩,
    simp only [quot_mk_eq_order_type, mem_I, order_type_lt_iff] at hβ,
    rcases hβ with ⟨f, hf, ⟨y, hy⟩⟩,
    refine ⟨y, _⟩,
    simp only [quot_mk_eq_order_type, subtype.mk_eq_mk, order_type_eq_iff],
    refine ⟨order_iso.symm _⟩,
    rw ←hy,
    exact hf.order_iso _ }
end

instance well_order_ordinals : well_order ordinal.{u} :=
{ exists_min :=
  begin
    rintro S ⟨⟨α⟩, hα⟩,
    simp only [quot_mk_eq_order_type] at hα,
    by_cases h : ∀ β ∈ S, order_type α ≤ β,
    { exact ⟨order_type α, hα, h⟩ },
    { simp only [exists_prop, not_le, not_forall] at h,
      rcases h with ⟨β, hβ, hβα⟩,
      let T : set (I (order_type α)) := { γ | γ.1 ∈ S },
      let f := (order_iso_I_order_type α).symm,
      have hT : set.nonempty (f '' T) := ⟨f ⟨β, hβα⟩, ⟨⟨β, hβα⟩, ⟨hβ, rfl⟩⟩⟩,
      obtain ⟨a, ⟨⟨δ, hδ'⟩, ⟨hδ'', rfl⟩⟩, ha'⟩ := exists_min _ hT,
      refine ⟨δ, hδ'', λ ε hε, _⟩,
      by_cases hε' : ε < order_type α,
      { exact f.le_iff_le.1 (ha' (f ⟨ε, hε'⟩) ⟨⟨ε, hε'⟩, ⟨hε, rfl⟩⟩) },
      { exact le_of_lt (lt_of_lt_of_le hδ' (not_lt.1 hε')) } }
  end,
  ..(infer_instance : linear_order ordinal.{u})}

def well_order_transfer {α : Type u} {β : Type v} [well_order β] (f : α ≃ β) : well_order α :=
{ le := λ x y, f x ≤ f y,
  le_refl := λ x, le_refl _,
  le_trans := λ x y z, le_trans,
  le_antisymm := λ x y hxy hyx, f.injective $ le_antisymm hxy hyx,
  le_total := λ x y, @le_total _ _ (f x) (f y),
  decidable_le := by apply_instance,
  decidable_eq := by apply_instance,
  decidable_lt := by apply_instance,
  exists_min :=
  begin
    rintro S ⟨s, hs⟩,
    obtain ⟨b, ⟨a, ⟨ha, rfl⟩⟩, ha'⟩ := exists_min (f '' S) ⟨f s, ⟨s, hs, rfl⟩⟩,
    exact ⟨a, ha, λ b hb, ha' (f b) ⟨b, hb, rfl⟩⟩
  end }

theorem burali_forti : ¬small.{u} ordinal.{u} :=
begin
  rintro ⟨α, ⟨f⟩⟩,
  letI := well_order_transfer f.symm,
  let g : ordinal.{u} ≃o α := f.to_order_iso (λ x y hxy, _) (λ x y, id),
  { exact I_ne_univ _ (iis_self (I (order_type α)) (initial_segment_I _) ⟨g.trans (order_iso_I_order_type α)⟩) },
  { rwa [←f.symm_apply_apply x, ←f.symm_apply_apply y] at hxy }
end

end my