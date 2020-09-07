/-
Copyright (c) Ian Riley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Riley
-/
import .basic

namespace scope

meta def tactic.dec_trivial := `[exact dec_trivial]

@[simp] lemma update_apply (name : string) (val : Prop) (s : scope) :
  s{name ↦ val} name = val := if_pos rfl

@[simp] lemma update_apply_ne (name name' : string) (val : Prop)
    (s : scope) (hname : name' ≠ name . tactic.dec_trivial) :
        s{name ↦ val} name' = s name' := if_neg hname

@[simp] lemma update_id (name : string) (s : scope) :
    s{name ↦ s name} = s :=
begin
    apply funext,
    intro name',
    by_cases name' = name,
    {
        rw h,
        exact update_apply name (s name) s,
    },
    {
        apply update_apply_ne,
        exact h,
    }
end

@[simp] lemma update_squash (name : string) (val₁ val₂ : Prop)
    (s : scope) : s{name ↦ val₂}{name ↦ val₁} = s{name ↦ val₁} :=
begin
    apply funext,
    intro name',
    by_cases name' = name,
    {
        rw h,
        repeat {rw update_apply},
    },
    {
        repeat {rw update_apply_ne name name' _ _ h},
    }
end

@[simp] lemma update_swap (name₁ name₂ : string) (val₁ val₂ : Prop)
    (s: scope) (hname : name₁ ≠ name₂ . tactic.dec_trivial) :
        s{name₂ ↦ val₂}{name₁ ↦ val₁} = s{name₁ ↦ val₁}{name₂ ↦ val₂} :=
begin
    apply funext,
    intro name',
    by_cases name' = name₁; have h₁ := h;
        by_cases name' = name₂; have h₂ := h,
        {
            exfalso,
            apply hname,
            rw h₁ at h₂,
            exact h₂,
        },
        {
            rw h₁,
            rw update_apply,
            rw update_apply_ne _ _ _ _ hname,
            rw update_apply,
        },
        {
            rw h₂,
            rw update_apply,
            have hname := ne.symm hname,
            rw update_apply_ne _ _ _ _ hname,
            rw update_apply,
        },
        {
            rw update_apply_ne _ _ _ _ h₁,
            rw update_apply_ne _ _ _ _ h₂,
            rw update_apply_ne _ _ _ _ h₂,
            rw update_apply_ne _ _ _ _ h₁,
        }
end

end scope
