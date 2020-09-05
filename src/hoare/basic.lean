/-
Copyright (c) Ian Riley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Riley
-/
import common big_step.basic

def partial_hoare (P : scope → Prop) (S : stmt) (Q : scope → Prop) : Prop :=
    ∀ (s t : scope), P s → (S, s) ⟹ t → Q t

notation `{* ` P : 1 ` *} ` S : 1 ` {* ` Q : 1 ` *}` := partial_hoare P S Q
