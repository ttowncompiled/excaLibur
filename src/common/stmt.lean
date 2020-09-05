/-
Copyright (c) Ian Riley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Riley
-/
import .basic

inductive stmt : Type
| skip      : stmt
| assign    : string → (scope → Prop) → stmt
| seq       : stmt → stmt → stmt
| ite       : (scope → Prop) → stmt → stmt → stmt
| while     : (scope → Prop) → stmt → stmt

infixr ` ;; `:90 := stmt.seq
