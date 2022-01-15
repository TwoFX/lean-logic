/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import tactic well_order

open_locale classical
noncomputable theory

universes u v

namespace my

structure well_ordered_type :=
(type : Type u)
[well_order_type : well_order type]

instance : has_coe_to_sort well_ordered_type.{u} (Type u) := ⟨well_ordered_type.type⟩

instance well_order_well_ordered_type (α : well_ordered_type.{u}) : well_order α :=
well_ordered_type.well_order_type _

instance order_iso_setoid : setoid (well_ordered_type.{u}) :=
{ r := λ α β, nonempty (α ≃o β),
  iseqv := ⟨λ α, ⟨order_iso.refl _⟩, λ α β ⟨f⟩, ⟨f.symm⟩, λ α β γ ⟨f⟩ ⟨g⟩, ⟨f.trans g⟩⟩ }

def ordinal : Type (u+1) := quotient my.order_iso_setoid.{u}

def order_type {α : Type u} [well_order α] : ordinal.{u} :=
⟦⟨α⟩⟧

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

end my