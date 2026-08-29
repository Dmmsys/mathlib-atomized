/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Kim Morrison, Johannes Hölzl, Reid Barton
-/
module

public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Tactic.PPWithUniv
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.TryThis

/-!
# Categories

Defines a category, as a type class parametrised by the type of objects.

## Notation

Introduces notations in the `CategoryTheory` scope
* `X ⟶ Y` for the morphism spaces (type as `\hom`),
* `𝟙 X` for the identity morphism on `X` (type as `\b1`),
* `f ≫ g` for composition in the 'arrows' convention (type as `\gg`).

Users may like to add `g ⊚ f` for composition in the standard convention, using
```lean
local notation:80 g " ⊚ " f:80 => CategoryTheory.CategoryStruct.comp f g -- type as \oo
```

-/

@[expose] public section


library_note «category theory universes»
/--
The typeclass `Category C` describes morphisms associated to objects of type `C : Type u`.

The universe levels of the objects and morphisms are independent, and will often need to be
specified explicitly, as `Category.{v} C`.

Typically any concrete example will either be a `SmallCategory`, where `v = u`,
which can be introduced as
```
universe u
variable {C : Type u} [SmallCategory C]
```
or a `LargeCategory`, where `u = v+1`, which can be introduced as
```
universe u
variable {C : Type (u+1)} [LargeCategory C]
```

In order for the library to handle these cases uniformly,
we generally work with the unconstrained `Category.{v u}`,
for which objects live in `Type u` and morphisms live in `Type v`.

Because the universe parameter `u` for the objects can be inferred from `C`
when we write `Category C`, while the universe parameter `v` for the morphisms
cannot be automatically inferred, through the category theory library
we introduce universe parameters with morphism levels listed first,
as in
```
universe v u
```
or
```
universe v₁ v₂ u₁ u₂
```
when multiple independent universes are needed.

This has the effect that we can simply write `Category.{v} C`
(that is, only specifying a single parameter) while `u` will be inferred.

Often, however, it's not even necessary to include the `.{v}`.
(Although it was in earlier versions of Lean.)
If it is omitted a "free" universe will be used.
-/

library_note «universe output parameters and typeclass caching»
/--
Many classes in Mathlib have universe parameters that do not appear in their
input parameter types. For example:
* `Category.{v} (C : Type u)` — the morphism universe `v` is not determined by `C`
* `HasLimitsOfSize.{v₁, u₁} (C : Type u) [Category.{v} C]` — the shape universes `v₁, u₁`
  are not determined by `C`
* `Small.{w} (α : Type v)` — the target universe `w` is not determined by `α`
  (but `v` is determined by `α`, so `v` *is* an output)
* `Functor.IsContinuous.{t} (F) (J) (K)` — the sheaf type universe `t` is not determined
  by `F`, `J`, `K`
* `UnivLE.{u, v}` — has no input parameters at all

By default (since https://github.com/leanprover/lean4/pull/12286), Lean treats any universe
parameter not occurring in input types as an output parameter, and erases it from typeclass
resolution cache keys. This means that queries differing only in such a universe share a
cache entry — the first result found is reused.

This is correct when the universe truly is determined by the inputs (e.g., `v` in
`Small.{w} (α : Type v)`), but incorrect when the universe is part of the *question*
(e.g., `v` in `Category.{v} C`). Cache collisions cause "stuck at solving universe constraint"
errors or silent misresolution.

The `@[univ_out_params]` attribute
(from https://github.com/leanprover/lean4/pull/12423) overrides the default:
* `@[univ_out_params]` — no universe parameters are output (all kept in cache key)
* `@[univ_out_params v]` — only `v` is output

**Rule of thumb:** if the class is typically used with explicit universe annotations
(e.g., `HasLimitsOfSize.{v₁, u₁} C`) or is marked `@[pp_with_univ]`, its "extra" universe
parameters are likely inputs, not outputs, and the class should be annotated with
`@[univ_out_params]`.
-/

universe v u

namespace CategoryTheory

/-- A preliminary structure on the way to defining a category,
containing the data, but none of the axioms. -/
@[pp_with_univ]
/--
Definition of `CategoryStruct` / `CategoryStruct` 的定义

English:
class CategoryStruct
  parameters: (obj : Type u)
  extends: Quiver.{v} obj
  axioms and operations (2):
    - id : forall X : obj, Hom X X
    - comp : forall {X Y Z : obj}, (X ⟶ Y) -> (Y ⟶ Z) -> (X ⟶ Z)

中文:
类 CategoryStruct
  参数: (obj : 类型u)
  继承: 箭图.{v} obj
  公理与运算 (2 个):
    - id : 对任意 X : obj, 态射 X X
    - comp : 对任意 {X Y Z : obj}, (X ⟶ Y) -> (Y ⟶ Z) -> (X ⟶ Z)

Depends on / 依赖: CategoryStruct, CategoryStruct.comp
-/
class CategoryStruct (obj : Type u) : Type max u (v + 1) extends Quiver.{v} obj where
  /-- The identity morphism on an object. -/
  id : forall X : obj, Hom X X
  /-- Composition of morphisms in a category, written `f ≫ g`. -/
  comp : forall {X Y Z : obj}, (X ⟶ Y) -> (Y ⟶ Z) -> (X ⟶ Z)

attribute [trans, to_dual self (reorder := X Z, 6 7)] CategoryStruct.comp
attribute [to_dual self (reorder := comp (X Z, 4 5))] CategoryStruct.mk

initialize_simps_projections CategoryStruct (-toQuiver_Hom, -Hom)

/-- Notation for the identity morphism in a category. -/
scoped notation "𝟙" => CategoryStruct.id -- type as \b1

/-- Notation for composition of morphisms in a category. -/
scoped infixr:80 " ≫ " => CategoryStruct.comp -- type as \gg

/-- Close the main goal with `sorry` if its type contains `sorry`, and fail otherwise. -/
syntax (name := sorryIfSorry) "sorry_if_sorry" : tactic

open Lean Meta Elab.Tactic in
@[tactic sorryIfSorry, inherit_doc sorryIfSorry] meta def evalSorryIfSorry : Tactic := fun _ => do
  let goalType ← getMainTarget
  if goalType.hasSorry then
    closeMainGoal `sorry_if_sorry (← mkSorry goalType true)
  else
    throwError "The goal does not contain `sorry`"

/--
`rfl_cat` is a macro for `intros; rfl` which is attempted in `aesop_cat` before
doing the more expensive `aesop` tactic.

This gives a speedup because `simp` (called by `aesop`) can be very slow.
https://github.com/leanprover-community/mathlib4/pull/25475 contains measurements from June 2025.

Implementation notes:
* `refine id ?_`:
  In some cases it is important that the type of the proof matches the expected type exactly.
  e.g. if the goal is `2 = 1 + 1`, the `rfl` tactic will give a proof of type `2 = 2`.
  Starting a proof with `refine id ?_` is a trick to make sure that the proof has exactly
  the expected type, in this case `2 = 1 + 1`. See also
  https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/changing.20a.20proof.20can.20break.20a.20later.20proof
* `apply_rfl`:
  `rfl` is a macro that attempts both `eq_refl` and `apply_rfl`. Since `apply_rfl`
  subsumes `eq_refl`, we can use `apply_rfl` instead. This fails twice as fast as `rfl`.

-/
macro (name := rfl_cat) "rfl_cat" : tactic => do `(tactic| (refine id ?_; intros; apply_rfl))

/--
A thin wrapper for `aesop` which adds the `CategoryTheory` rule set and
allows `aesop` to look through semireducible definitions when calling `intros`.
This tactic fails when it is unable to solve the goal, making it suitable for
use in auto-params.
-/
macro (name := aesop_cat) "aesop_cat" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  first | sorry_if_sorry | rfl_cat |
aesop c* (config := { introsTransparency? := some .default, terminal := true })
            (rule_sets := [$(Lean.mkIdent `CategoryTheory):ident]))

/--
We also use `aesop_cat?` to pass along a `Try this` suggestion when using `aesop_cat`
-/
macro (name := aesop_cat?) "aesop_cat?" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  first | sorry_if_sorry | try_this rfl_cat |
aesop? c* (config := { introsTransparency? := some .default, terminal := true })
             (rule_sets := [$(Lean.mkIdent `CategoryTheory):ident]))
/--
A variant of `aesop_cat` which does not fail when it is unable to solve the
goal. Use this only for exploration! Nonterminal `aesop` is even worse than
nonterminal `simp`.
-/
macro (name := aesop_cat_nonterminal) "aesop_cat_nonterminal" c:Aesop.tactic_clause* : tactic =>
  `(tactic|
aesop c* (config := { introsTransparency? := some .default, warnOnNonterminal := false })
              (rule_sets := [$(Lean.mkIdent `CategoryTheory):ident]))

attribute [aesop safe (rule_sets := [CategoryTheory])] Subsingleton.elim

open Lean Elab Tactic in
/-- A tactic for discharging easy category theory goals, widely used as an autoparameter.
Currently this defaults to the `aesop_cat` wrapper around `aesop`, but by setting
the option `mathlib.tactic.category.grind` to `true`, it will use the `grind` tactic instead.
-/
meta def categoryTheoryDischarger : TacticM Unit := do
  if ← getBoolOption `mathlib.tactic.category.grind then
    if ← getBoolOption `mathlib.tactic.category.log_grind then
      logInfo "Category theory discharger using `grind`."
    evalTacticSeq (← `(tacticSeq|
      intros; (try dsimp only) <;> ((try ext) <;> grind (gen := 20) (ematch := 20))))
  else
    if ← getBoolOption `mathlib.tactic.category.log_aesop then
      logInfo "Category theory discharger using `aesop`."
    evalTactic (← `(tactic| aesop_cat))

@[inherit_doc categoryTheoryDischarger]
elab (name := cat_disch) "cat_disch" : tactic =>
  categoryTheoryDischarger

set_option mathlib.tactic.category.grind true

/-- The typeclass `Category C` describes morphisms associated to objects of type `C`.
The universe levels of the objects and morphisms are unconstrained, and will often need to be
specified explicitly, as `Category.{v} C`. (See also `LargeCategory` and `SmallCategory`.) -/
-- After https://github.com/leanprover/lean4/pull/12286 and
-- https://github.com/leanprover/lean4/pull/12423, the morphism universe `v` would default to
-- being a universe output parameter.
-- See Note [universe output parameters and typeclass caching].
@[univ_out_params, pp_with_univ, stacks 0014, wikidata Q719395]
/--
Definition of `Category` / `Category` 的定义

English:
class Category
  parameters: (obj : Type u)
  extends: CategoryStruct.{v} obj
  axioms and operations (3):
    - id_comp : forall {X Y : obj} (f : X ⟶ Y), 𝟙 X ≫ f = f  [default: by cat_disch]
    - comp_id : forall {X Y : obj} (f : X ⟶ Y), f ≫ 𝟙 Y = f  [default: by cat_disch]
    - assoc : forall {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z), (f ≫ g) ≫ h = f ≫ g ≫ h  [default: by cat_disch]

中文:
类 范畴
  参数: (obj : 类型u)
  继承: CategoryStruct.{v} obj
  公理与运算 (3 个):
    - id_comp : 对任意 {X Y : obj} (f : X ⟶ Y), 𝟙 X ≫ f = f  [默认: by cat_disch]
    - comp_id : 对任意 {X Y : obj} (f : X ⟶ Y), f ≫ 𝟙 Y = f  [默认: by cat_disch]
    - assoc : 对任意 {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z), (f ≫ g) ≫ h = f ≫ g ≫ h  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
class Category (obj : Type u) : Type max u (v + 1) extends CategoryStruct.{v} obj where
  /-- Identity morphisms are left identities for composition. -/
  id_comp : forall {X Y : obj} (f : X ⟶ Y), 𝟙 X ≫ f = f := by cat_disch
  /-- Identity morphisms are right identities for composition. -/
  comp_id : forall {X Y : obj} (f : X ⟶ Y), f ≫ 𝟙 Y = f := by cat_disch
  /-- Composition in a category is associative. -/
  assoc : forall {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z), (f ≫ g) ≫ h = f ≫ g ≫ h := by
    cat_disch

attribute [to_dual existing (attr := simp, grind =) id_comp] Category.comp_id
attribute [simp, grind _=_] Category.assoc

initialize_simps_projections Category (-Hom)

/-- `Category.mk'` is the dual of `Category.mk`, which we need for `to_dual`.
Please avoid using this directly. -/
@[to_dual existing mk]
/--
Definition of `Category.mk'` / `Category.mk'` 的定义

English:
abbreviation Category.mk'
  signature: {obj : Type u} [CategoryStruct.{v} obj]
  body: by simp
example {C} [Category C] {X Y : C} (f : X ⟶ Y) : f ≫ 𝟙 Y = f := by simp

中文:
缩写 范畴.mk'
  签名: {obj : 类型u} [CategoryStruct.{v} obj]
  定义体: by simp
example {C} [Category C] {X Y : C} (f : X ⟶ Y) : f ≫ 𝟙 Y = f := by simp

Depends on / 依赖: Category, example
-/
abbrev Category.mk' {obj : Type u} [CategoryStruct.{v} obj]
    (id_comp : forall {X Y : obj} (f : Y ⟶ X), f ≫ 𝟙 X = f)
    (comp_id : forall {X Y : obj} (f : Y ⟶ X), 𝟙 Y ≫ f = f)
    (assoc : forall {W X Y Z : obj} (f : X ⟶ W) (g : Y ⟶ X) (h : Z ⟶ Y), h ≫ g ≫ f = (h ≫ g) ≫ f) :
    Category.{v, u} obj where

example {C} [Category C] {X Y : C} (f : X ⟶ Y) : 𝟙 X ≫ f = f := by simp
example {C} [Category C] {X Y : C} (f : X ⟶ Y) : f ≫ 𝟙 Y = f := by simp

/--
Definition of `LargeCategory` / `LargeCategory` 的定义

English:
abbreviation LargeCategory
  signature: (C : Type (u + 1))
  body: Category.{u} C

中文:
缩写 大范畴
  签名: (C : 类型 (u + 1))
  定义体: Category.{u} C

Depends on / 依赖: Category
-/
abbrev LargeCategory (C : Type (u + 1)) : Type (u + 1) := Category.{u} C

/--
Definition of `SmallCategory` / `SmallCategory` 的定义

English:
abbreviation SmallCategory
  signature: (C : Type u)
  body: Category.{u} C

中文:
缩写 小范畴
  签名: (C : 类型u)
  定义体: Category.{u} C

Depends on / 依赖: Category
-/
abbrev SmallCategory (C : Type u) : Type (u + 1) := Category.{u} C

section

variable {C : Type u} [Category.{v} C] {X Y Z : C}

@[to_dual existing assoc]
/--
lemma `Category.assoc'` / 引理 `Category.assoc'`

English:
lemma Category.assoc'
  given: {W X Y Z : C} (f : X ⟶ W) (g : Y ⟶ X) (h : Z ⟶ Y)
  proof: (Category.assoc h g f).symm

中文:
引理 范畴.assoc'
  条件: {W X Y Z : C} (f : X ⟶ W) (g : Y ⟶ X) (h : Z ⟶ Y)
  证明: (Category.assoc h g f).symm

Depends on / 依赖: Category, Category.assoc
-/
lemma Category.assoc' {W X Y Z : C} (f : X ⟶ W) (g : Y ⟶ X) (h : Z ⟶ Y) :
    h ≫ g ≫ f = (h ≫ g) ≫ f := (Category.assoc h g f).symm

/-- Postcompose an equation between morphisms by another morphism -/
@[to_dual (reorder := w h) whisker_eq
/-- Precompose an equation between morphisms by another morphism -/]
/--
theorem `eq_whisker` / 定理 `eq_whisker`

English:
theorem eq_whisker
  given: {f g : X ⟶ Y} (w : f = g) (h : Y ⟶ Z)
  statement: f ≫ h = g ≫ h
  proof: by rw [w]

中文:
定理 eq_whisker
  条件: {f g : X ⟶ Y} (w : f = g) (h : Y ⟶ Z)
  结论: f ≫ h = g ≫ h
  证明: by rw [w]
-/
theorem eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶ Z) : f ≫ h = g ≫ h := by rw [w]

/--
Notation for whiskering an equation by a morphism (on the right).
If `f g : X ⟶ Y` and `w : f = g` and `h : Y ⟶ Z`, then `w =≫ h : f ≫ h = g ≫ h`.
-/
scoped infixr:80 " =≫ " => eq_whisker

/--
Notation for whiskering an equation by a morphism (on the left).
If `g h : Y ⟶ Z` and `w : g = h` and `f : X ⟶ Y`, then `f ≫= w : f ≫ g = f ≫ h`.
-/
scoped infixr:80 " ≫= " => whisker_eq

@[to_dual eq_of_comp_right_eq]
/--
theorem `eq_of_comp_left_eq` / 定理 `eq_of_comp_left_eq`

English:
theorem eq_of_comp_left_eq
  given: {f g : X ⟶ Y} (w : forall {Z : C} (h : Y ⟶ Z), f ≫ h = g ≫ h)
  proof: by
  convert! w (𝟙 Y) <;> simp

@[to_dual eq_of_comp_right_eq']

中文:
定理 eq_of_comp_left_eq
  条件: {f g : X ⟶ Y} (w : 对任意 {Z : C} (h : Y ⟶ Z), f ≫ h = g ≫ h)
  证明: by
  convert! w (𝟙 Y) <;> simp

@[to_dual eq_of_comp_right_eq']

Depends on / 依赖: convert
-/
theorem eq_of_comp_left_eq {f g : X ⟶ Y} (w : forall {Z : C} (h : Y ⟶ Z), f ≫ h = g ≫ h) :
    f = g := by
  convert! w (𝟙 Y) <;> simp

@[to_dual eq_of_comp_right_eq']
/--
theorem `eq_of_comp_left_eq'` / 定理 `eq_of_comp_left_eq'`

English:
theorem eq_of_comp_left_eq'
  statement: (f g : X ⟶ Y)
  proof: eq_of_comp_left_eq @fun Z h => by convert! congr_fun (congr_fun w Z) h

@[to_dual id_of_comp_right_id]

中文:
定理 eq_of_comp_left_eq'
  结论: (f g : X ⟶ Y)
  证明: eq_of_comp_left_eq @fun Z h => by convert! congr_fun (congr_fun w Z) h

@[to_dual id_of_comp_right_id]

Depends on / 依赖: congr_fun, convert, eq_of_comp_left_eq
-/
theorem eq_of_comp_left_eq' (f g : X ⟶ Y)
    (w : (fun {Z} (h : Y ⟶ Z) => f ≫ h) = fun {Z} (h : Y ⟶ Z) => g ≫ h) : f = g :=
  eq_of_comp_left_eq @fun Z h => by convert! congr_fun (congr_fun w Z) h

@[to_dual id_of_comp_right_id]
/--
theorem `id_of_comp_left_id` / 定理 `id_of_comp_left_id`

English:
theorem id_of_comp_left_id
  given: (f : X ⟶ X) (w : forall {Y : C} (g : X ⟶ Y), f ≫ g = g)
  statement: f = 𝟙 X
  proof: by
  convert! w (𝟙 X)
  simp

@[to_dual (reorder := f g' g) ite_comp]

中文:
定理 id_of_comp_left_id
  条件: (f : X ⟶ X) (w : 对任意 {Y : C} (g : X ⟶ Y), f ≫ g = g)
  结论: f = 𝟙 X
  证明: by
  convert! w (𝟙 X)
  simp

@[to_dual (reorder := f g' g) ite_comp]

Depends on / 依赖: convert
-/
theorem id_of_comp_left_id (f : X ⟶ X) (w : forall {Y : C} (g : X ⟶ Y), f ≫ g = g) : f = 𝟙 X := by
  convert! w (𝟙 X)
  simp

@[to_dual (reorder := f g' g) ite_comp]
/--
theorem `comp_ite` / 定理 `comp_ite`

English:
theorem comp_ite
  given: {P : Prop} [Decidable P] {X Y Z : C} (f : X ⟶ Y) (g g' : Y ⟶ Z)
  proof: by aesop

@[to_dual (reorder := f g' g) dite_comp]

中文:
定理 comp_ite
  条件: {P : 命题} [可判定 P] {X Y Z : C} (f : X ⟶ Y) (g g' : Y ⟶ Z)
  证明: by aesop

@[to_dual (reorder := f g' g) dite_comp]

Depends on / 依赖: Category
-/
theorem comp_ite {P : Prop} [Decidable P] {X Y Z : C} (f : X ⟶ Y) (g g' : Y ⟶ Z) :
    (f ≫ if P then g else g') = if P then f ≫ g else f ≫ g' := by aesop

@[to_dual (reorder := f g' g) dite_comp]
/--
theorem `comp_dite` / 定理 `comp_dite`

English:
theorem comp_dite
  statement: {P : Prop} [Decidable P]
  proof: by aesop

中文:
定理 comp_dite
  结论: {P : 命题} [可判定 P]
  证明: by aesop

Depends on / 依赖: Category
-/
theorem comp_dite {P : Prop} [Decidable P]
    {X Y Z : C} (f : X ⟶ Y) (g : P -> (Y ⟶ Z)) (g' : ¬P -> (Y ⟶ Z)) :
    (f ≫ if h : P then g h else g' h) = if h : P then f ≫ g h else f ≫ g' h := by aesop

/--
Definition of `Epi` / `Epi` 的定义

English:
class Epi
  parameters: (f : X ⟶ Y)
  axioms and operations (1):
    - left_cancellation : forall {Z : C} (g h : Y ⟶ Z), f ≫ g = f ≫ h -> g = h

中文:
类 满态射
  参数: (f : X ⟶ Y)
  公理与运算 (1 个):
    - left_cancellation : 对任意 {Z : C} (g h : Y ⟶ Z), f ≫ g = f ≫ h -> g = h
-/
class Epi (f : X ⟶ Y) : Prop where
  /-- A morphism `f` is an epimorphism if it can be cancelled when precomposed. -/
  left_cancellation : forall {Z : C} (g h : Y ⟶ Z), f ≫ g = f ≫ h -> g = h

/-- A morphism `f` is a monomorphism if it can be cancelled when postcomposed:
`g ≫ f = h ≫ f` implies `g = h`. -/
@[to_dual (attr := stacks 003B) Epi]
/--
Definition of `Mono` / `Mono` 的定义

English:
class Mono
  parameters: (f : X ⟶ Y)
  axioms and operations (1):
    - right_cancellation : forall {Z : C} (g h : Z ⟶ X), g ≫ f = h ≫ f -> g = h

中文:
类 单态射
  参数: (f : X ⟶ Y)
  公理与运算 (1 个):
    - right_cancellation : 对任意 {Z : C} (g h : Z ⟶ X), g ≫ f = h ≫ f -> g = h
-/
class Mono (f : X ⟶ Y) : Prop where
  /-- A morphism `f` is a monomorphism if it can be cancelled when postcomposed. -/
  right_cancellation : forall {Z : C} (g h : Z ⟶ X), g ≫ f = h ≫ f -> g = h

@[to_dual]
instance (X : C) : Epi (𝟙 X) :=
  ⟨fun g h w => by aesop⟩

@[to_dual]
/--
theorem `cancel_epi` / 定理 `cancel_epi`

English:
theorem cancel_epi
  given: (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z}
  statement: f ≫ g = f ≫ h ↔ g = h
  proof: ⟨fun p => Epi.left_cancellation g h p, congr_arg _⟩

@[to_dual]

中文:
定理 cancel_epi
  条件: (f : X ⟶ Y) [满态射 f] {g h : Y ⟶ Z}
  结论: f ≫ g = f ≫ h ↔ g = h
  证明: ⟨fun p => Epi.left_cancellation g h p, congr_arg _⟩

@[to_dual]

Depends on / 依赖: Epi.left_cancellation, congr_arg, left_cancellation
-/
theorem cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} : f ≫ g = f ≫ h ↔ g = h :=
  ⟨fun p => Epi.left_cancellation g h p, congr_arg _⟩

@[to_dual]
/--
theorem `cancel_epi_assoc_iff` / 定理 `cancel_epi_assoc_iff`

English:
theorem cancel_epi_assoc_iff
  given: (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} {W : C} {k l : Z ⟶ W}
  proof: ⟨fun p => (cancel_epi f).1 by simpa using p, fun p => by simp only [Category.assoc, p]⟩

@[to_dual]

中文:
定理 cancel_epi_assoc_iff
  条件: (f : X ⟶ Y) [满态射 f] {g h : Y ⟶ Z} {W : C} {k l : Z ⟶ W}
  证明: ⟨fun p => (cancel_epi f).1 by simpa using p, fun p => by simp only [Category.assoc, p]⟩

@[to_dual]

Depends on / 依赖: Category, Category.assoc, cancel_epi
-/
theorem cancel_epi_assoc_iff (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} {W : C} {k l : Z ⟶ W} :
    (f ≫ g) ≫ k = (f ≫ h) ≫ l ↔ g ≫ k = h ≫ l :=
⟨fun p => (cancel_epi f).1 by simpa using p, fun p => by simp only [Category.assoc, p]⟩

@[to_dual]
/--
theorem `cancel_epi_id` / 定理 `cancel_epi_id`

English:
theorem cancel_epi_id
  given: (f : X ⟶ Y) [Epi f] {h : Y ⟶ Y}
  statement: f ≫ h = f ↔ h = 𝟙 Y
  proof: by
  convert! cancel_epi f
  simp

中文:
定理 cancel_epi_id
  条件: (f : X ⟶ Y) [满态射 f] {h : Y ⟶ Y}
  结论: f ≫ h = f ↔ h = 𝟙 Y
  证明: by
  convert! cancel_epi f
  simp

Depends on / 依赖: cancel_epi, convert
-/
theorem cancel_epi_id (f : X ⟶ Y) [Epi f] {h : Y ⟶ Y} : f ≫ h = f ↔ h = 𝟙 Y := by
  convert! cancel_epi f
  simp

/-- The composition of epimorphisms is again an epimorphism. This version takes `Epi f` and `Epi g`
as typeclass arguments. For a version taking them as explicit arguments, see `epi_comp'`. -/
@[to_dual (reorder := f g, 7 9)
/-- The composition of monomorphisms is again a monomorphism. This version takes `Mono f` and
`Mono g` as typeclass arguments. For a version taking them as explicit arguments, see `mono_comp'`.
-/]
/--
Instance `epi_comp` / 实例 `epi_comp`

English:
instance epi_comp
  signature: (f : X ⟶ Y) [Epi f] (g : Y ⟶ Z) [Epi g]
  body: ⟨fun _ _ w => (cancel_epi g).1 (cancel_epi_assoc_iff f).1 w⟩

中文:
实例 epi_comp
  签名: (f : X ⟶ Y) [满态射 f] (g : Y ⟶ Z) [满态射 g]
  定义体: ⟨fun _ _ w => (cancel_epi g).1 (cancel_epi_assoc_iff f).1 w⟩

Depends on / 依赖: cancel_epi, cancel_epi_assoc_iff
-/
instance epi_comp (f : X ⟶ Y) [Epi f] (g : Y ⟶ Z) [Epi g] : Epi (f ≫ g) :=
⟨fun _ _ w => (cancel_epi g).1 (cancel_epi_assoc_iff f).1 w⟩

/-- The composition of epimorphisms is again an epimorphism. This version takes `Epi f` and `Epi g`
as explicit arguments. For a version taking them as typeclass arguments, see `epi_comp`. -/
@[to_dual (reorder := hf hg)
/-- The composition of monomorphisms is again a monomorphism. This version takes `Mono f` and
`Mono g` as explicit arguments. For a version taking them as typeclass arguments, see `mono_comp`.
-/]
/--
theorem `epi_comp'` / 定理 `epi_comp'`

English:
theorem epi_comp'
  given: {f : X ⟶ Y} {g : Y ⟶ Z} (hf : Epi f) (hg : Epi g)
  statement: Epi (f ≫ g)
  proof: inferInstance

@[to_dual (reorder := f g)]

中文:
定理 epi_comp'
  条件: {f : X ⟶ Y} {g : Y ⟶ Z} (hf : 满态射 f) (hg : 满态射 g)
  结论: 满态射 (f ≫ g)
  证明: inferInstance

@[to_dual (reorder := f g)]
-/
theorem epi_comp' {f : X ⟶ Y} {g : Y ⟶ Z} (hf : Epi f) (hg : Epi g) : Epi (f ≫ g) :=
  inferInstance

@[to_dual (reorder := f g)]
/--
theorem `epi_of_epi` / 定理 `epi_of_epi`

English:
theorem epi_of_epi
  given: (f : X ⟶ Y) (g : Y ⟶ Z) [Epi (f ≫ g)]
  statement: Epi g
  proof: ⟨fun _ _ w => (cancel_epi (f ≫ g)).1 by simp only [Category.assoc, w]⟩

@[to_dual]

中文:
定理 epi_of_epi
  条件: (f : X ⟶ Y) (g : Y ⟶ Z) [满态射 (f ≫ g)]
  结论: 满态射 g
  证明: ⟨fun _ _ w => (cancel_epi (f ≫ g)).1 by simp only [Category.assoc, w]⟩

@[to_dual]

Depends on / 依赖: Category, Category.assoc, cancel_epi
-/
theorem epi_of_epi (f : X ⟶ Y) (g : Y ⟶ Z) [Epi (f ≫ g)] : Epi g :=
⟨fun _ _ w => (cancel_epi (f ≫ g)).1 by simp only [Category.assoc, w]⟩

@[to_dual]
/--
theorem `epi_of_epi_fac` / 定理 `epi_of_epi_fac`

English:
theorem epi_of_epi_fac
  given: {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} [Epi h] (w : f ≫ g = h)
  statement: Epi g
  proof: by
  subst h; exact epi_of_epi f g

中文:
定理 epi_of_epi_fac
  条件: {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} [满态射 h] (w : f ≫ g = h)
  结论: 满态射 g
  证明: by
  subst h; exact epi_of_epi f g

Depends on / 依赖: epi_of_epi
-/
theorem epi_of_epi_fac {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} [Epi h] (w : f ≫ g = h) : Epi g := by
  subst h; exact epi_of_epi f g

/-- `f : X ⟶ Y` is an epimorphism iff for all `Z`, composition of morphisms `Y ⟶ Z` with `f`
is injective. -/
@[to_dual
/-- `f : X ⟶ Y` is a monomorphism iff for all `Z`, composition of morphisms `Z ⟶ X` with `f`
is injective. -/]
/--
lemma `epi_iff_forall_injective` / 引理 `epi_iff_forall_injective`

English:
lemma epi_iff_forall_injective
  given: (f : X ⟶ Y)
  statement: Epi f ↔ forall Z, (fun g : Y ⟶ Z => f ≫ g).Injective
  proof: ⟨fun _ _ _ _ hg => (cancel_epi f).1 hg, fun h => ⟨fun _ _ hg => h _ hg⟩⟩

@[to_dual]

中文:
引理 epi_iff_对任意_injective
  条件: (f : X ⟶ Y)
  结论: 满态射 f ↔ 对任意 Z, (fun g : Y ⟶ Z => f ≫ g).单射
  证明: ⟨fun _ _ _ _ hg => (cancel_epi f).1 hg, fun h => ⟨fun _ _ hg => h _ hg⟩⟩

@[to_dual]

Depends on / 依赖: cancel_epi
-/
lemma epi_iff_forall_injective (f : X ⟶ Y) : Epi f ↔ forall Z, (fun g : Y ⟶ Z => f ≫ g).Injective :=
  ⟨fun _ _ _ _ hg => (cancel_epi f).1 hg, fun h => ⟨fun _ _ hg => h _ hg⟩⟩

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Quiver.IsThin
  signature: C] (f
  body: Subsingleton.elim _ _

中文:
实例 [箭图.IsThin
  签名: C] (f
  定义体: Subsingleton.elim _ _

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
instance [Quiver.IsThin C] (f : X ⟶ Y) : Epi f where
  left_cancellation _ _ _ := Subsingleton.elim _ _

end

section

variable (C : Type u)
variable [Category.{v} C]

universe u'

/-- The category structure on `ULift C` that is induced from the category
structure on `C`. This is not made a global instance because of a diamond
when `C` is a preordered type. -/
@[instance_reducible]
/--
Definition of `uliftCategory` / `uliftCategory` 的定义

English:
definition uliftCategory
  signature: : Category.{v} (ULift.{u'} C) where
  body: X.down ⟶ Y.down
  id X := 𝟙 X.down
  comp f g := f ≫ g

中文:
定义 uliftCategory
  签名: : 范畴.{v} (类型层提升.{u'} C) where
  定义体: X.down ⟶ Y.down
  id X := 𝟙 X.down
  comp f g := f ≫ g

Depends on / 依赖: X.down, Y.down
-/
def uliftCategory : Category.{v} (ULift.{u'} C) where
  Hom X Y := X.down ⟶ Y.down
  id X := 𝟙 X.down
  comp f g := f ≫ g

attribute [local instance] uliftCategory in
-- We verify that this previous instance can lift small categories to large categories.
example (D : Type u) [SmallCategory D] : LargeCategory (ULift.{u + 1} D) := by infer_instance

end

end CategoryTheory
