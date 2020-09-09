/-
Copyright (c) Ian Riley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Riley
-/

constant Ill    : Prop  -- indeterminate "ill-defined" proposition
constant Nil    : Prop  -- null proposition
constant Undfn  : Prop  -- undefined proposition ; not within scope

notation `γ₀`   := Ill      -- γ₀ \gamma\zero
notation `ω₀`   := Nil      -- ω₀ \omega\zero
notation `Υ₀`   := Undfn    -- Υ₀ \Upsilon\zero

/-
Mapping of a variable name to an assertion about that variable.

The Prop type has been selected for a few reasons :
    (a) Most efficient Type (Sort 0) to generalize over program data types. An
    inductive type can't be eliminated without multiple intermediate steps,
    which inflates the resulting proof.
    (b) Using a Prop types lifts program data types to the level of a
    proposition, so that we can better employ existing Lean libraries as well
    as define new libraries over a single Prop type.
    (c) In addition, using a Prop type retains variables as propositional
    variables in both hypotheses and goals for later analysis.

The term 'scope' is used rather than the traditional term 'state'. There is
an existing 'state' type in Lean core. In addition, the use of 'scope' implies
a distinction about its propositions that is not commonly emphasized. The
propositions are not assertions about the state of the program but about the
state of the currently accessible scope.
-/
def scope := Π (name : string), Prop    -- Π \Pi

@[simp] def scope.update (name : string) (val : Prop) (s : scope) : scope :=
λ (name' : string), if name' = name then val else s name'   -- λ \lam

@[simp] def empty.scope := (λ (_ : string), Υ₀)

notation s `{` name ` ↦ ` val `}` := scope.update name val s    -- ↦ \mapsto

notation `[∅]` := empty.scope   -- ∅ \empty

notation `[` name ` ↦ ` val `]` := scope.update name val [∅]

/-
Instructions for how to use scope and its notation

The type of scope is string → Prop . It is defined as Π (name : string), Prop
to emphasize that instances of scope are defined using λ-expressions. We use
the informal notation [x ↦ 0, y ↦ 8] to refer to the scope where the
program variable x has value 0 and the program variable y has value 8.
This same scope can be implemented in Lean using the following λ-expression.

                                    CORRECT

            (λ {x y : ℕ} (name : string), if name = "x" then (x = 0) else
                if name = "y" then (y = 8) else Υ₀)

Since the type of scope is string → Prop , we must take extra care when
inserting data types such as ℕ, ℤ, ℝ, bool, char, and string into a scope. The
following λ-expression is incorrect for the scope [x ↦ 0, y ↦ 8].

                                    INCORRECT

           (λ {x y : ℕ} (name : string), if name = "x" then 0 else
                if name = "y" then 8 else 0)

The values of x and y returned by the above λ-expression are not Prop; they are
ℕ. In Lean, Prop is of type Sort 0, while ℕ is of type Type. These types,
Sort 0 and Type, are not compatible. Therefore, to include the value of x
into a scope, rather than including its value into the scope, we must include
an assertion about its value. Thus, we must use (x = 0) rather than 0 when
asserting that the value of program variable x is 0 in the current scope.

By constructing scopes this way, we have mapped the common understanding of a
scope (a mapping of variables to values) to a more formal understanding of a
scope (a mapping of propositional variables to propositions). Thus, the scope
[x ↦ 0, y ↦ 8] becomes [Px ↦ (x = 0), Py ↦ (y = 8)], where Px and Py are the
propositional variables related to program variables x and y, respectively.


Our motivation for using this construction is to define a scope that can
include assertions about program variables of different types. In Lean,
the following λ-expression is prohibited.

                                    INVALID

           (λ {x y : ℕ} (name : string), if name = "x" then 0 else
                if name = "y" then "hello" else Υ₀)

This λ-expression is prohibited because it has three distinct types depending
on the value of name. If name = "x", then the λ-expression has type string → ℕ.
If name = "y", then the λ-expression has type string → string. Otherwise,
it has type string → Prop. Lean's type checker cannot determine the type of
this λ-expression without knowing the value of the input parameter name, so
this expression has been prohibited.

The most basic scope provided by this library is the empty scope, defined as
[∅], which is a scope where every propositional variable is mapped to the
proposition Υ₀ (undefined). The proposition Υ₀ is used to indicate that a
propositional variable has no corresponding proposition. Seeing Υ₀ in a proof
is generally considered to be an indication that the proof state is incorrect
and that any resulting proof would be invalid.

Note: Propositions γ₀ (ill-defined) and ω₀ (null) are also provided. γ₀ is used
to indicate a propositional variable that has an indeterminate proposition.
This occurs when a program variable is modified non-deterministically. In such
cases, γ₀ should be used when the propositional variable can be any proposition
of an infinite set of propositions or a finite set of unknown propositions. If
there is a finite set of known propositions, then a disjunction can be used
rather γ₀. The ω₀ proposition is provided to represent program variables that
can be assigned the null value or its equivalent (nil, option.none, etc.).

A scope, such as [x ↦ 8] (which we know to be [Px ↦ (x = 8)]), can be defined
in Lean using the following notation, ["x" ↦ (x = 8)]. This notation applies
to the scope.update definition to the empty scope using "x" and (x = 8) as
its other inputs. By doing so, the propositional variable Px, denoted "x", maps
to the proposition (x = 8), while all other propositional variables are
undefined. Note that the left-hand side of ↦ (\mapsto) must be a string.

Given a scope s with propositional variable "x", the proposition of "x" can be
updated using the following notation, s{"x" ↦ (x = 0)}. This updates the
proposition of "x" to be the proposition (x = 0). Thus, we can represent
changes to program variables using this notation.

Given a scope s with only propositional variable "x", we can include a new
proposition for propositional variable "y" in s using the same notation
as before, s{"y" ↦ (y = 5)}. This, in essence, updates the proposition of
propositional variable "y" from Υ₀ to (y = 5), which asserts that the program
variable y has a value of 5. This notation can be used to insert a new
propositional variable into any scope.

As a final important note, it should be stressed that, since we are utilizing
Prop as the implied type of scope, we must approach lemmas and theorems
differently than we would otherwise. For example, the following lemmas would
be, at worst, invalid and, at best, illicit.

                                    INVALID

                example {x : ℕ} (s : ["x" ↦ (x = 0)]) : (x = 0)
                example {x : ℕ} (s : ["x" ↦ (x = 0)]) : (s "x")

Each lemma presented above is, by equivalence, an assertion about the value of
program variable x given the scope s. While we can clearly see that the goals
are each a proposition within the stated scope, we cannot make such claims
about a scope.

In Lean terms, scope is defined as a proof of propositions of the
form string → Prop. The goals of the above examples are each of type Prop
and the stated hypothesis in each example is a particular proof of
one string → Prop. If we are attempting to construct a proof that a
particular Prop follows from a particular proof of string → Prop, then we
should rightfully inquire what string justifies such a proof. We can easily
tell that the string "x" justifies the proof. However, given the proof
construction, can we be justified in saying that there is such a string "x"? No.
That a string "x" could exist is not the same as stating that the string "x"
does exist in the current proof context. The following constructions would
be more appropriate.

        example {x : ℕ} (s : ["x" ↦ (x = 0)]) : ∃ name, name → (x = 0)
    example {x : ℕ} (s : ["x" ↦ (x = 0)]) : ∀ name, (name = "x") → (x = 0)

Once we have incorporated this understanding into our proof construction, there
is one last hiccup that we must avoid. The following construction would also
be invalid.
                                    INVALID

    example {x : ℕ} (s : ["x" ↦ (x = 0)]) (name : string) : (name = "x") → 0

The example above is invalid because it's a claim about a particular value of
the program variable x. In this case, the value 0, which is a ℕ. However,
for x to have the value 0, there must a program variable x. While the
construction above asserts the existence of a name with value "x", it does
not assert the existence of a program variable x. As such, while we can
assert (x = 0), 0 does not follow from (x = 0) unless we can also assert the
existence of x. We must continue to remember that the definition of scope
asserts propositions about program variables rather than their exact value.
The following construction would be more appropriate.

  example {x : ℕ} (s : ["x" ↦ (x = 0)]) (name : _) (x' : x): (name = "x") → 0

The primary lesson that we can take away from these examples is that a scope
does not imply the existence of its constituent propositional variables or the
existence of program variables. This error in thinking will often arise if
scope is treated as a data structure, as a map/dictionary or as a list.
It is neither. In Lean, a scope is a family of proofs.

The following examples illustrate the suggested approach to verify assertions
about program variables.

                                    CORRECT

                    example {x : ℕ} : (∃ s, s "x" → (x = 0))
                    example {x : ℕ} : (∃ s, s "x" = (x = 0))
    example {x : ℕ} : (∀ s, (s = ["x" ↦ (x = 0)]) → (s "x" → (x = 0)))
    example {x : ℕ} : (∀ s, (s = ["x" ↦ (x = 0)]) → (s "x" = (x = 0)))

The above examples are an assertion about a particular propositional variable
in a scope. They are essentially asking whether the particular
proof ["x" ↦ (x = 0)] in the family of proofs (represented by scope) is
the proof s "x" = (x = 0), which is a valid and licit inquiry.
-/
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
