/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import tactic
import order.zorn

universe u

variables {P : Type u}

section
variables (P)

inductive proposition : Type u
| primitive : P → proposition
| false : proposition
| implication : proposition → proposition → proposition

end

instance : has_bot (proposition P) := ⟨proposition.false⟩
local infix ⇒:80 := proposition.implication
local notation `¬'`:90 p:90 := p ⇒ ⊥

section
variables (P)

structure valuation :=
(to_fun : proposition P → bool)
(to_fun_false : to_fun ⊥ = ff)
(to_fun_implication : ∀ {p q}, to_fun (p ⇒ q) = if to_fun p = tt ∧ to_fun q = ff then ff else tt)

instance : has_coe_to_fun (valuation P) (λ _, proposition P → bool) := ⟨valuation.to_fun⟩

end

namespace valuation

@[simp]
lemma apply_false (v : valuation P) : v proposition.false = ff :=
valuation.to_fun_false _

@[simp]
lemma apply_bot (v : valuation P) : v ⊥ = ff :=
valuation.to_fun_false _

section
variables (v : valuation P) (p q : proposition P)

lemma apply_implication : v (p ⇒ q) = if v p = tt ∧ v q = ff then ff else tt :=
valuation.to_fun_implication _

lemma apply_implication_eq_true_left (h : v p = ff) : v (p ⇒ q) = tt :=
by { rw apply_implication, finish }

lemma apply_implication_eq_true_right (h : v q = tt) : v (p ⇒ q) = tt :=
by { rw apply_implication, finish }

lemma apply_implication_eq_false (h₁ : v p = tt) (h₂ : v q = ff) : v (p ⇒ q) = ff :=
by { rw apply_implication, finish }

@[simp]
lemma apply_not (v : valuation P) (p : proposition P) : v (¬'p) = !v p :=
begin
  simp only [apply_implication, apply_bot, bnot, apply_bot, and_true, eq_self_iff_true],
  by_cases v p = tt,
  { simp [h] },
  { simp [h], simp at h, simp [h]  }
end


end

section
local attribute [ext] valuation

lemma ext'' {v v' : valuation P} (h : (v : proposition P → bool) = v') : v = v' :=
by { ext, exact congr_fun h _ }

local attribute [ext] ext''

@[ext]
lemma ext' {v v' : valuation P} (h : ∀ p, v (proposition.primitive p) = v' (proposition.primitive p)) :
  v = v' :=
begin
  ext,
  induction x,
  { exact h _ },
  { simp only [apply_false] },
  { simp [apply_implication, *] }
end

end

def extension_fun (w : P → bool) : proposition P → bool
| (proposition.primitive p) := w p
| ⊥ := ff
| (p ⇒ q) := if extension_fun p = tt ∧ extension_fun q = ff then ff else tt

def extension (w : P → bool) : valuation P :=
{ to_fun := extension_fun w,
  to_fun_false := by simp only [extension_fun],
  to_fun_implication := by simp only [extension_fun, forall_2_true_iff, eq_self_iff_true] }

@[simp]
lemma extension_primitive (w : P → bool) (p : P) : (extension w) (proposition.primitive p) = w p :=
rfl 

end valuation

def semantically_entails (S : set (proposition P)) (p : proposition P) : Prop :=
∀ (v : valuation P), (∀ s ∈ S, v s = tt) → v p = tt

notation S ` ⊨ `:70 p:70 := semantically_entails S p

def tautology (p : proposition P) : Prop :=
∅ ⊨ p

notation `⊨ `:62 p:62 := tautology p

lemma tautology_iff (p : proposition P) : ⊨ p ↔ ∀ (v : valuation P), v p = tt :=
by { rw [tautology, semantically_entails], finish }

def axiom₁ (p q : proposition P) : proposition P := p ⇒ (q ⇒ p)
def axiom₂ (p q r : proposition P) : proposition P := (p ⇒ (q ⇒ r)) ⇒ ((p ⇒ q) ⇒ (p ⇒ r))
def axiom₃ (p : proposition P) : proposition P := (¬'¬'p) ⇒ p

lemma tautology_axiom₁ {p q : proposition P} : ⊨ axiom₁ p q :=
by { intro v, simp only [axiom₁, valuation.apply_implication], finish }
lemma tautology_axiom₂ {p q r : proposition P} : ⊨ axiom₂ p q r :=
by { intro v, simp only [axiom₂, valuation.apply_implication], finish }
lemma tautology_axiom₃ {p : proposition P} : ⊨ axiom₃ p :=
by { intro v, simp only [axiom₃, valuation.apply_implication], finish }

inductive proves (S : set (proposition P)) : proposition P → Prop
| ax₁ {p q : proposition P} : proves (axiom₁ p q)
| ax₂ {p q r : proposition P} : proves (axiom₂ p q r)
| ax₃ {p : proposition P} : proves (axiom₃ p)
| hypothesis {p : proposition P} (h : p ∈ S) : proves p
| modus_ponens {p q : proposition P} : proves (p ⇒ q) → proves p → proves q

notation S ` ⊢ `:70 p:70 := proves S p

namespace proves

lemma subset {S T : set (proposition P)} (hST : S ⊆ T) {p : proposition P} (h : S ⊢ p) : T ⊢ p :=
by { induction h, exacts [ax₁, ax₂, ax₃, hypothesis (hST (by assumption)), modus_ponens (by assumption) (by assumption)] }

end proves

def is_theorem (p : proposition P) : Prop :=
proves ∅ p

notation `⊢ `:70 p:70 := is_theorem p

section
open proves

lemma implies_self {p : proposition P} : ⊢ p ⇒ p :=
have h1 : ⊢ (p ⇒ ((p ⇒ p) ⇒ p)) ⇒ ((p ⇒ (p ⇒ p)) ⇒ (p ⇒ p)), from ax₂,
have h2 : ⊢ p ⇒ ((p ⇒ p) ⇒ p),                               from ax₁,
have h3 : ⊢ (p ⇒ (p ⇒ p)) ⇒ (p ⇒ p),                         from modus_ponens h1 h2,
have h4 : ⊢ p ⇒ (p ⇒ p),                                     from ax₁,
show      ⊢ p ⇒ p,                                           from modus_ponens h3 h4

end

section deduction_theorem
open proves

theorem deduction (S : set (proposition P)) (p q : proposition P) : S ⊢ p ⇒ q ↔ (S ∪ {p}) ⊢ q :=
begin
  refine ⟨λ h, modus_ponens (subset (by simp) h) $ hypothesis $ by simp, λ h, _⟩,
  induction h with _ _ _ _ _ _ _ hpS _ _ _ _ π₁ π₂,
  { exact modus_ponens ax₁ ax₁ },
  { exact modus_ponens ax₁ ax₂ },
  { exact modus_ponens ax₁ ax₃ },
  { cases (set.mem_union _ _ _).1 hpS,
    { exact modus_ponens ax₁  (hypothesis h) },
    { rw set.mem_singleton_iff.1 h,
      exact subset (set.empty_subset _) implies_self } },
  { exact modus_ponens (modus_ponens ax₂ π₁) π₂ }
end

lemma deduction_single {p q : proposition P} : ⊢ p ⇒ q ↔ {p} ⊢ q :=
by { convert deduction ∅ p q, rw set.empty_union }

end deduction_theorem

section soundness_theorem
open proves

theorem soundness (S : set (proposition P)) (p : proposition P) (h : S ⊢ p) : S ⊨ p :=
begin
  intros v hv,
  induction h,
  { exact (tautology_iff _).1 tautology_axiom₁ _ },
  { exact (tautology_iff _).1 tautology_axiom₂ _ },
  { exact (tautology_iff _).1 tautology_axiom₃ _ },
  { exact hv _ h_h },
  { rw [valuation.apply_implication] at *,
    finish }
end

end soundness_theorem

def consistent (S : set (proposition P)) : Prop :=
¬(S ⊢ ⊥)

lemma consistent_or_consistent_not {S : set (proposition P)} (hS : consistent S) (p : proposition P) :
  consistent (S ∪ {p}) ∨ consistent (S ∪ {¬'p}) :=
begin
  contrapose! hS,
  simp only [consistent, not_not, ←deduction] at *,
  exact proves.modus_ponens hS.2 hS.1
end

lemma exists_deductive_closure (S : set (proposition P)) (hS : consistent S) :
  ∃ (S' : set (proposition P)), S ⊆ S' ∧ consistent S' ∧ (∀ p, S' ⊢ p → p ∈ S') ∧ (∀ p, p ∈ S' ∨ ¬'p ∈ S') :=
begin
  let T := { S' : set (proposition P) | S ⊆ S' ∧ consistent S' },
  suffices hS' : ∃ S' ∈ T, S ⊆ S' ∧ ∀ S'' ∈ T, S' ⊆ S'' → S'' = S',
  { rcases hS' with ⟨S', ⟨hS'₁, hS'₂⟩, hS'₃, hS'₄⟩,
    have hS : ∀ p, p ∈ S' ∨ ¬'p ∈ S',
    { intro p,
      cases consistent_or_consistent_not hS'₂ p,
      { suffices : S' ∪ {p} = S',
        { rw ←this, left, simp only [set.mem_insert_iff, true_or, eq_self_iff_true, set.union_singleton] },
        exact hS'₄ _ ⟨set.subset_union_of_subset_left hS'₃ _, h⟩ (set.subset_union_left _ _) },
      { suffices : S' ∪ {¬'p} = S',
        { rw ←this, right, simp only [set.mem_insert_iff, true_or, eq_self_iff_true, and_self, set.union_singleton] },
        exact hS'₄ _ ⟨set.subset_union_of_subset_left hS'₃ _, h⟩ (set.subset_union_left _ _) } },
    refine ⟨S', ⟨hS'₃, hS'₂, λ p hp, _, hS⟩⟩,
    { cases hS p,
      { exact h },
      { exact false.elim (hS'₂ (proves.modus_ponens (proves.hypothesis h) hp)) } } },
  refine zorn.zorn_subset_nonempty _ (λ c hcT hc hc', ⟨set.sUnion c, ⟨⟨_, _⟩, λ S' hS', _⟩⟩) _ ⟨set.subset.refl _, hS⟩,
  { rcases hc' with ⟨c₀, hc₀⟩,
    exact set.subset_sUnion_of_subset _ _ (hcT hc₀).1 hc₀ },
  { rw [consistent],
    by_contradiction,
    suffices : ∃ S₀ ∈ c, S₀ ⊢ ⊥,
    { rcases this with ⟨S₀, hS₀, hS₀'⟩,
      exact (hcT hS₀).2 hS₀' },
    rcases hc' with ⟨c₀, hc₀⟩,
    induction h with _ _ _ _ _ _ p hp p q hpq hp hc₁ hc₂,
    { exact ⟨c₀, hc₀, proves.ax₁⟩ },
    { exact ⟨c₀, hc₀, proves.ax₂⟩ },
    { exact ⟨c₀, hc₀, proves.ax₃⟩ },
    { obtain ⟨c₁, ⟨hc₁c, hpc₁⟩⟩ := set.mem_sUnion.1 hp,
      exact ⟨c₁, hc₁c, proves.hypothesis hpc₁⟩ },
    { obtain ⟨c₁, ⟨hc₁c, hc₁pq⟩⟩ := hc₁,
      obtain ⟨c₂, ⟨hc₂c, hc₂p⟩⟩ := hc₂,
      refine ⟨c₁ ∪ c₂, _, _⟩,
      { cases zorn.chain.total_of_refl hc hc₁c hc₂c,
        { convert hc₂c,
          exact set.union_eq_right_iff_subset.2 h },
        { convert hc₁c,
          exact set.union_eq_left_iff_subset.2 h } },
      { exact proves.modus_ponens (proves.subset (set.subset_union_left _ _) hc₁pq) (proves.subset (set.subset_union_right _ _) hc₂p) } } },
  { exact set.subset_sUnion_of_mem hS' }
end

section
open proves

lemma false_elimination_tautology {p : proposition P} : ⊢ ⊥ ⇒ p :=
deduction_single.2 $ modus_ponens ax₃ $ deduction_single.1 ax₁

lemma false_elimination {S : set (proposition P)} {p : proposition P} : S ⊢ ⊥ ⇒ p :=
proves.subset (set.empty_subset _) false_elimination_tautology

end

theorem model_existence (S : set (proposition P)) (hS : consistent S) :
  ∃ (v : valuation P), ∀ s ∈ S, v s = tt :=
begin
  obtain ⟨S', ⟨hSS', hS'₁, hS'₂, hS'₃⟩⟩ := exists_deductive_closure S hS,
  classical,
  refine ⟨⟨λ p, if p ∈ S' then tt else ff, _, _⟩, _⟩,
  { simp only [if_false_left_eq_and, and_true, eq_self_iff_true, ite_eq_ff_distrib],
    simp only [consistent] at hS'₁,
    contrapose! hS'₁,
    exact proves.hypothesis hS'₁ },
  { intros p q,
    by_cases h₁ : p ∈ S',
    { by_cases h₂ : q ∈ S',
      { simp only [*, and_true, eq_self_iff_true, ite_eq_right_iff, if_false, forall_true_left, if_false_right_eq_and, ite_eq_tt_distrib,
          and_false],
        exact hS'₂ _ (proves.modus_ponens proves.ax₁ (proves.hypothesis h₂)) },
      { simp only [*, forall_false_left, if_false_left_eq_and, and_true, if_true, eq_self_iff_true, not_true, ite_eq_right_iff, and_self,
          ite_eq_ff_distrib, ite_eq_left_iff, not_false_iff],
          refine λ h₃, h₂ (hS'₂ _ (proves.modus_ponens (proves.hypothesis h₃) (proves.hypothesis h₁))) } },
    { simp only [*, and_true, eq_self_iff_true, if_false, if_false_right_eq_and, ite_eq_tt_distrib, false_and],
      have h₂ : ¬'p ∈ S',
      { cases hS'₃ p,
        { exact false.elim (h₁ h) },
        { exact h } },
      refine hS'₂ _ _,
      rw deduction,
      refine proves.modus_ponens false_elimination
        (proves.modus_ponens (proves.subset (set.subset_union_left _ _) (proves.hypothesis h₂)) (proves.hypothesis _)),
      simp only [set.mem_insert_iff, true_or, eq_self_iff_true, set.union_singleton] } },
  { intros s hs,
    change ite (s ∈ S') tt ff = tt,
    simp only [and_true, eq_self_iff_true, if_false_right_eq_and, ite_eq_tt_distrib],
    exact hSS' hs },
end

lemma model_existence' (S : set (proposition P)) (h : S ⊨ ⊥) : S ⊢ ⊥ :=
begin
  by_contradiction h',
  obtain ⟨v, hv⟩ := model_existence _ h',
  simpa only [valuation.apply_bot] using h v hv
end

theorem adequacy (S : set (proposition P)) (p : proposition P) (h : S ⊨ p) : S ⊢ p :=
begin
  have : S ∪ {¬'p} ⊨ ⊥,
  { intros v hv,
    have h₁ := h v (λ p hp, hv _ (set.mem_union_left _ hp)),
    have h₂ := hv (¬'p) (set.mem_union_right _ (set.mem_singleton _)),
    rw valuation.apply_not at h₂,
    finish },
  replace this := model_existence' _ this,
  rw ←deduction at this,
  exact proves.modus_ponens proves.ax₃ this
end

theorem completeness (S : set (proposition P)) (p : proposition P) : S ⊨ p ↔ S ⊢ p :=
⟨adequacy _ _, soundness _ _⟩

theorem compactness (S : set (proposition P)) (p : proposition P) (h : S ⊨ p) : ∃ S' ⊆ S, S'.finite ∧ S' ⊨ p :=
begin
  simp only [completeness] at ⊢ h,
  induction h with _ _ _ _ _ _ q hq q r hqr hq hS₁ hS₂,
  { exact ⟨∅, set.empty_subset _, set.finite_empty, proves.ax₁⟩ },
  { exact ⟨∅, set.empty_subset _, set.finite_empty, proves.ax₂⟩ },
  { exact ⟨∅, set.empty_subset _, set.finite_empty, proves.ax₃⟩ },
  { refine ⟨{q}, set.singleton_subset_iff.2 hq, set.finite_singleton _, proves.hypothesis (set.mem_singleton _)⟩ },
  { rcases hS₁ with ⟨S₁, hS₁S, hS₁, hS₁qr⟩,
    rcases hS₂ with ⟨S₂, hS₂S, hS₂, hS₂q⟩,
    refine ⟨S₁ ∪ S₂, set.union_subset hS₁S hS₂S, set.finite.union hS₁ hS₂, _⟩,
    exact proves.modus_ponens (proves.subset (set.subset_union_left _ _) hS₁qr) (proves.subset (set.subset_union_right _ _) hS₂q) }
end