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

notation ` _let_ ` x ` := ` a := stmt.assign x a

infixr ` ;; `:90 := stmt.comp

notation ` _if_ ` b ` _then_ ` S ` _else_ ` T ` _end_ ` := stmt.ite b S T

notation ` _while_ ` b ` _do_ ` S ` _end_ ` := stmt.while b S

notation ` _call_ ` f ` _with_ ` `(` v₀ `, ` v₁ `)` ` | ` σ ` _do_ ` T ` _end_ ` := stmt.call f v₀ v₁ σ T
