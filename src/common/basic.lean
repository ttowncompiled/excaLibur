/-
Copyright (c) Ian Riley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Riley
-/

constant Ill    : Prop  -- indeterminate "ill-defined" predicate
constant Nil    : Prop  -- null predicate
constant Undfn  : Prop  -- undefined predicate ; not within scope

notation `γ₀`   := Ill      -- \gamma\zero
notation `ω₀`   := Nil      -- \omega\zero
notation `Υ₀`   := Undfn    -- \Upsilon\zero

/-
Mapping of a variable name to an assertion about that variable.

The Prop type has been selected for a few reasons :
    (a) Most efficient Type (Sort 0) to generalize over program data types. An
    inductive type can't be eliminated without multiple intermediate steps,
    which inflates the resulting proof.
    (b) Using a Prop types lifts program data types to the level of a
    proposition, so that we can better employ existing Lean libraries as well
    as define new libraries over a single Prop type.
    (c) In addition, using a Prop type retains predicate (variable propositions)
    in both hypotheses and goals for later analysis.

The term 'scope' is used rather than the traditional term 'state'. There is
an existing 'state' type in Lean core. In addition, the use of 'scope' implies
a distinction about its propositions that is not commonly emphasized. The
propositions are not assertions about the state of the program but about the
state of the currently accessible scope.
-/
def scope := string → Prop

def scope.update (name : string) (val : Prop) (s : scope) : scope :=
λ (name' : string), if name' = name then val else s name'

notation s `{` name ` ↦ ` val `}` := scope.update name val s

instance : has_emptyc scope := { emptyc := λ _, Υ₀ }

notation `[∅]` := empty.scope

notation `[` name ` ↦ ` val `]` := scope.update name val [∅]
