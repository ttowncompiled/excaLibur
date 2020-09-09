/-
Copyright (c) Ian Riley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Riley
-/
import .basic

inductive stmt : Type
| skip      : stmt
| assign    : string → (scope → Prop) → stmt
| comp      : stmt → stmt → stmt
| ite       : (scope → Prop) → stmt → stmt → stmt
| while     : (scope → Prop) → stmt → stmt
| call      : string → (scope → Prop) → (scope → Prop) →
                (scope → scope) → stmt → stmt

notation ` _skip_ ` := stmt.skip

/-
This notation can be read as, "let the propositional variable for x be bound
to the proposition a."
-/
notation ` _let_ ` x ` ⇒ ` a `, ` := stmt.assign x (λ (s : scope), a) -- ⇒ \=>
notation ` _let_ ` x ` => ` a `, ` := stmt.assign x (λ (s : scope), a)

infixr ` ;; `:90 := stmt.comp

notation ` _if_ ` b ` _then_ ` `{ ` S ` }` ` _else_ ` `{ ` T ` } ` :=
stmt.ite b S T

notation ` _while_ ` b ` _do_ ` `{ ` S ` } ` := stmt.while b S

/-
This notation can be read as, "call procedure f with bindings v₀ and bindings
v₁ scoped through σ, which executes statement T."
-/
notation ` _call_ ` f ` _with_ ` `(` n₀ ` ⇒ `:110 v₀ `, ` n₁ ` ⇒ `:110 v₁ `)` ` |↦| ` σ ` _do_ ` `{ ` T ` } ` :=
stmt.call f (λ (s : scope), s n₀ → v₀) (λ (s : scope), s n₁ → v₁) σ T
notation ` _call_ ` f ` _with_ ` `(` n₀ ` => `:110 v₀ `, ` n₁ ` => `:110 v₁ `)` ` |->| ` σ ` _do_ ` `{ ` T ` } ` :=
stmt.call f (λ (s : scope), s n₀ → v₀) (λ (s : scope), s n₁ → v₁) σ T
