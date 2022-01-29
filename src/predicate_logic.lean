/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import tactic

open_locale classical
noncomputable theory

section

structure context :=
(var function relation : Type*)
(fun_arity : function → ℕ)
(rel_arity : relation → ℕ)

open context

variable (C : context)

inductive term
| tvar (i : var C) : term
| app (f : function C) (arg : fin (fun_arity C f) → term) : term

inductive formula
| false : formula
| fterm : term C → formula
| eq : term C → term C → formula
| rel (φ : relation C) : (fin (rel_arity C φ) → term C) → formula
| imp : formula → formula → formula
| uni : var C → formula → formula

instance : has_bot (formula C) := ⟨formula.false⟩
local infix ⇒:80 := formula.imp
local notation `¬'`:90 p:90 := p ⇒ ⊥
instance : has_coe (term C) (formula C) := ⟨formula.fterm⟩
local infix `='`:50 := formula.eq
local notation `∀'`:40 x:40 `: `:40 p:40 := formula.uni x p

end

open context

namespace term
variables {C : context}

noncomputable def subst (x : var C) (t : term C) : term C → term C
| (tvar i) := if i = x then t else tvar i
| (app f arg) := app f (subst ∘ arg)

end term

namespace formula
variables {C : context}

def subst (x : var C) (t : term C) : formula C → formula C
| false := false
| (fterm t) := fterm t

end formula