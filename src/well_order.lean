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

def I [has_lt α] (x : α) : set α := { y | y < x }
def J [has_le α] (x : α) : set α := { y | y ≤ x }

@[simp] lemma mem_I [has_lt α] (x y : α) : x ∈ I y ↔ x < y := iff.rfl
@[simp] lemma mem_J [has_le α] (x y : α) : x ∈ J y ↔ x ≤ y := iff.rfl

lemma mem_J_iff [linear_order α] (x y : α) : x ∈ J y ↔ x = y ∨ x ∈ I y :=
le_iff_eq_or_lt

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

lemma I_subset_initial_segment [linear_order α] {Y : set α} (hY : initial_segment Y) : ∀ x ∈ Y, I x ⊆ Y :=
λ x hx y hy, hY _ hx _ hy

lemma initial_segment_I [linear_order α] (x : α) : initial_segment (I x) :=
λ y hy z hz, hz.trans hy

lemma initial_segment_J [linear_order α] (x : α) : initial_segment (J x) :=
λ y hy z hz, le_of_lt $ hz.trans_le hy

lemma initial_segment_univ [linear_order α] : initial_segment (set.univ : set α) :=
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
variables [well_order α] {G : Π (x : α), (I x → β) → β}

section
variables (G)

structure attempt :=
(definition_set : set α)
(initial_definition_set : initial_segment definition_set)
(to_fun : α → β)
(hh : ∀ x ∈ definition_set, to_fun x = G _ (set.restrict to_fun (I x)))

end

instance : has_coe_to_fun (attempt G) (λ _, α → β) := ⟨attempt.to_fun⟩

namespace attempt

lemma initial_segment_definition_set (h : attempt G) : initial_segment h.definition_set :=
attempt.initial_definition_set _

def defined_at (h : attempt G) (x : α) : Prop :=
x ∈ h.definition_set

lemma defined_at_iff (h : attempt G) {x : α} : h.defined_at x ↔ x ∈ h.definition_set :=
iff.rfl

lemma attempt_eq (h : attempt G) {x : α} : h.defined_at x → h x = G _ (set.restrict h (I x)) :=
attempt.hh _ _

lemma attempt_well_defined (h h' : attempt G) : ∀ (x : α) (hx : h.defined_at x) (hx' : h'.defined_at x), h x = h' x :=
begin
  refine well_ordered_induction _ (λ x hx hx₁ hx₂, _),
  rw [attempt_eq _ hx₁, attempt_eq _ hx₂],
  congr' 1,
  exact funext (λ y, hx _ y.2 (h.initial_segment_definition_set _ hx₁ _ y.2) (h'.initial_segment_definition_set _ hx₂ _ y.2))
end

section
variables (G)
include G

def attempt_defined_at (x : α) :=
{ h : attempt G // h.defined_at x }

lemma nonempty_β (x : α) : nonempty β :=
begin
  obtain ⟨m, hm, hm'⟩ := exists_min set.univ ⟨x, trivial⟩,
  refine ⟨G m _⟩,
  rintro ⟨y, hy⟩,
  exact false.elim (lt_irrefl m ((hm' y trivial).trans_lt hy))
end

def any (x : α) : β :=
classical.choice $ nonempty_β G x

lemma exists_assemble (S : set α) (hS : initial_segment S) (hS' : ∀ x ∈ S, nonempty (attempt_defined_at G x)) :
  ∃ h : attempt G, h.definition_set = S :=
begin
  have : ∀ x : S, ∃ h : attempt G, h.defined_at x,
  { rintro ⟨x, hx⟩,
    obtain ⟨h, hh⟩ := hS' x hx,
    exact ⟨h, hh⟩ },
  choose h hh using this,
  refine ⟨⟨_, hS, λ x, if hx : x ∈ S then h ⟨x, hx⟩ x else any G x, λ x hx, _⟩, rfl⟩,
  rw [dif_pos hx, attempt_eq (h ⟨x, hx⟩) _],
  { congr' 1,
    ext y,
    have : (y : α) ∈ S := hS _ hx _ y.2,
    simp only [this, dif_pos, set.restrict_apply],
    exact attempt_well_defined _ _ _ (initial_segment_definition_set _ _ (hh _) _ y.2) (hh _) },
  { exact hh _ }
end


lemma exists_extend (x : α) (h : ∃ h' : attempt G, h'.definition_set = I x) : ∃ h : attempt G, h.definition_set = J x :=
begin
  rcases h with ⟨h, hh⟩,
  refine ⟨⟨_, initial_segment_J x, function.update h x (G _ (set.restrict h (I x))), _⟩, rfl⟩,
  simp only [mem_J_iff, forall_eq_or_imp, function.update_same],
  refine ⟨_, _⟩,
  { congr' 1,
    ext y,
    rw [set.restrict_apply, set.restrict_apply, function.update_noteq (show (y : α) ≠ x, from ne_of_lt y.2)] },
  { intros y hy,
    rw [function.update_noteq (show (y : α) ≠ x, from ne_of_lt hy),
      h.attempt_eq (h.defined_at_iff.2 (hh.symm ▸ hy : y ∈ h.definition_set))],
    congr' 1,
    ext z,
    rw [set.restrict_apply, set.restrict_apply, function.update_noteq (show (z : α) ≠ x, from ne_of_lt (lt_trans z.2 hy))] }
end

lemma exists_attempt : ∀ x, nonempty (attempt_defined_at G x) :=
begin
  refine well_ordered_induction _ (λ x hx, _),
  obtain ⟨h, hh⟩ := exists_extend G x (exists_assemble G (I x) (initial_segment_I x) (λ y hy, hx _ hy)),
  exact ⟨⟨h, h.defined_at_iff.2 (hh.symm ▸ (le_refl _ : x ∈ J x))⟩⟩
end

end

end attempt

variables (G)

theorem recursion : ∃! f : α → β, ∀ x, f x = G x (set.restrict f _) :=
begin
  obtain ⟨f, hf⟩ := attempt.exists_assemble G set.univ initial_segment_univ (λ x hx, attempt.exists_attempt G x),
  have hf : ∀ x, f x = G x (set.restrict f _) := λ x, f.attempt_eq (f.defined_at_iff.2 (hf.symm ▸ set.mem_univ x)),
  refine ⟨f, ⟨hf, λ g hg, funext (well_ordered_induction _ (λ x hx, _))⟩⟩,
  rw [hf x, hg x],
  exact congr_arg _ (funext (λ y, hx _ y.2))
end

end recursion

section subset_collapse

instance well_order_set [well_order α] (S : set α) : well_order S :=
{ exists_min :=
   begin
     rintros T ⟨t, ht⟩,
     let T' := { x | ∃ (h : x ∈ S), (⟨x, h⟩ : S) ∈ T },
     have hT' : T'.nonempty := ⟨t, ⟨t.2, _⟩⟩,
     { obtain ⟨x, ⟨hx, hx'⟩, hx''⟩ := exists_min T' hT',
       refine ⟨⟨x, hx⟩, hx', λ y hy, hx'' _ ⟨y.2, _⟩⟩,
       simpa only [subtype.coe_eta, subtype.val_eq_coe] using hy },
     { simpa only [subtype.coe_eta] using ht }
   end,
  ..(infer_instance : linear_order S)}

theorem subset_collapse [well_order α] (Y : set α) : ∃! (S : set α), initial_segment S ∧ nonempty (Y ≃o S) :=
begin
  suffices : ∃! f : Y → α, ∀ (x : Y), f x ∈ (f '' I x)ᶜ.least_elements,
  { rcases this with ⟨f, hf, hf'⟩,
    refine ⟨set.range f, ⟨_, _⟩, _⟩,
    { rintros x ⟨y, rfl⟩ z hz,
      have := hf y,
      simp [set.least_elements] at this,
     }


   },
  { sorry,

   }
end

end subset_collapse

end my