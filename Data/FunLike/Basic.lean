/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public meta import Lean.Meta.CoeAttr
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Unique
public import Mathlib.Util.CompileInductive
public import Mathlib.Tactic.Simps.NotationClass
public import Mathlib.Tactic.SplitIfs

/-!
# Typeclass for a type `F` with an injective map to `A → B`

This typeclass is primarily for use by homomorphisms like `MonoidHom` and `LinearMap`.

There is the "D"ependent version `DFunLike` and the non-dependent version `FunLike`.

## Basic usage of `DFunLike` and `FunLike`

A typical type of morphisms should be declared as:
```
structure MyHom (A B : Type*) [MyClass A] [MyClass B] where
  (toFun : A → B)
  (map_op' : ∀ (x y : A), toFun (MyClass.op x y) = MyClass.op (toFun x) (toFun y))

namespace MyHom

variable (A B : Type*) [MyClass A] [MyClass B]

instance : FunLike (MyHom A B) A B where
  coe := MyHom.toFun
  coe_injective := fun f g h => by cases f; cases g; congr

@[ext] theorem ext {f g : MyHom A B} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : MyHom A B) (f' : A -> B) (h : f' = ⇑f)
  body: f'
  map_op' := h.symm ▸ f.map_op'

中文:
定义 copy
  签名: (f : My态射 A B) (f' : A -> B) (h : f' = ⇑f)
  定义体: f'
  map_op' := h.symm ▸ f.map_op'
-/
protected def copy (f : MyHom A B) (f' : A -> B) (h : f' = ⇑f) : MyHom A B where
  toFun := f'
  map_op' := h.symm ▸ f.map_op'

end MyHom
```

This file will then provide a `CoeFun` instance and various
extensionality and simp lemmas.

## Morphism classes extending `DFunLike` and `FunLike`

The `FunLike` design provides further benefits if you put in a bit more work.
The first step is to extend `FunLike` to create a class of those types satisfying
the axioms of your new type of morphisms.
Continuing the example above:

```
/--
Definition of `MyHomClass` / `MyHomClass` 的定义

English:
class MyHomClass
  parameters: (F : Type*) (A B : outParam Type*) [MyClass A] [MyClass B]
  (no additional axioms)

中文:
类 My态射类
  参数: (F : 类型) (A B : outParam 类型) [MyClass A] [MyClass B]
  (无附加公理)

Depends on / 依赖: MyClass, MyClass.op, map_op
-/
class MyHomClass (F : Type*) (A B : outParam Type*) [MyClass A] [MyClass B]
    [FunLike F A B] : Prop :=
  (map_op : forall (f : F) (x y : A), f (MyClass.op x y) = MyClass.op (f x) (f y))

@[simp]
/--
lemma `map_op` / 引理 `map_op`

English:
lemma map_op
  statement: {F A B : Type*} [MyClass A] [MyClass B] [FunLike F A B] [MyHomClass F A B]
  proof: MyHomClass.map_op _ _ _

中文:
引理 map_op
  结论: {F A B : 类型} [MyClass A] [MyClass B] [函数状 F A B] [My态射类 F A B]
  证明: MyHomClass.map_op _ _ _

Depends on / 依赖: MyHomClass, MyHomClass.map_op, map_op
-/
lemma map_op {F A B : Type*} [MyClass A] [MyClass B] [FunLike F A B] [MyHomClass F A B]
    (f : F) (x y : A) :
    f (MyClass.op x y) = MyClass.op (f x) (f y) :=
  MyHomClass.map_op _ _ _

-- You can add the below instance next to `MyHomClass.instFunLike`:
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MyHomClass (MyHom A B) A B
  body: MyHom.map_op'

中文:
实例 :
  签名: My态射类 (My态射 A B) A B
  定义体: MyHom.map_op'

Depends on / 依赖: MyHom.map_op, map_op
-/
instance : MyHomClass (MyHom A B) A B where
  map_op := MyHom.map_op'

-- [Insert `ext` and `copy` here]
```

Note that `A B` are marked as `outParam` even though they are not purely required to be so
due to the `FunLike` parameter already filling them in. This is required to see through
type synonyms, which is important in the category theory library. Also, it appears having them as
`outParam` is slightly faster.

The second step is to add instances of your new `MyHomClass` for all types extending `MyHom`.
Typically, you can just declare a new class analogous to `MyHomClass`:

```
/--
Definition of `CoolerHom` / `CoolerHom` 的定义

English:
structure CoolerHom
  parameters: (A B : Type*) [CoolClass A] [CoolClass B]
  extends: MyHom A B
  axioms and operations (1):
    - (map_cool' : toFun CoolClass.cool = CoolClass.cool)

中文:
结构 余oler态射
  参数: (A B : 类型) [CoolClass A] [CoolClass B]
  继承: My态射 A B
  公理与运算 (1 个):
    - (map_cool' : toFun CoolClass.cool = CoolClass.cool)
-/
structure CoolerHom (A B : Type*) [CoolClass A] [CoolClass B] extends MyHom A B where
  (map_cool' : toFun CoolClass.cool = CoolClass.cool)

/--
Definition of `CoolerHomClass` / `CoolerHomClass` 的定义

English:
class CoolerHomClass
  parameters: (F : Type*) (A B : outParam Type*) [CoolClass A] [CoolClass B]
  extends: MyHomClass F A B
  (no additional axioms)

中文:
类 余oler态射类
  参数: (F : 类型) (A B : outParam 类型) [CoolClass A] [CoolClass B]
  继承: My态射类 F A B
  (无附加公理)

Depends on / 依赖: CoolClass, CoolClass.cool, map_cool
-/
class CoolerHomClass (F : Type*) (A B : outParam Type*) [CoolClass A] [CoolClass B]
  [FunLike F A B] extends MyHomClass F A B :=
    (map_cool : forall (f : F), f CoolClass.cool = CoolClass.cool)

/--
lemma `map_cool` / 引理 `map_cool`

English:
lemma map_cool
  statement: {F A B : Type*} [CoolClass A] [CoolClass B] [FunLike F A B]
  proof: CoolerHomClass.map_cool _

中文:
引理 map_cool
  结论: {F A B : 类型} [CoolClass A] [CoolClass B] [函数状 F A B]
  证明: CoolerHomClass.map_cool _
-/
@[simp] lemma map_cool {F A B : Type*} [CoolClass A] [CoolClass B] [FunLike F A B]
    [CoolerHomClass F A B] (f : F) : f CoolClass.cool = CoolClass.cool :=
  CoolerHomClass.map_cool _

variable {A B : Type*} [CoolClass A] [CoolClass B]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (CoolerHom A B) A B
  body: f.toFun
  coe_injective := fun f g h => by cases f; cases g; congr; apply DFunLike.coe_injective; congr

中文:
实例 :
  签名: 函数状 (余oler态射 A B) A B
  定义体: f.toFun
  coe_injective := fun f g h => by cases f; cases g; congr; apply DFunLike.coe_injective; congr

Depends on / 依赖: f.toFun
-/
instance : FunLike (CoolerHom A B) A B where
  coe f := f.toFun
  coe_injective := fun f g h => by cases f; cases g; congr; apply DFunLike.coe_injective; congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoolerHomClass (CoolerHom A B) A B
  body: f.map_op'
  map_cool f := f.map_cool'

中文:
实例 :
  签名: 余oler态射类 (余oler态射 A B) A B
  定义体: f.map_op'
  map_cool f := f.map_cool'

Depends on / 依赖: f.map_op, map_op
-/
instance : CoolerHomClass (CoolerHom A B) A B where
  map_op f := f.map_op'
  map_cool f := f.map_cool'

-- [Insert `ext` and `copy` here]
```

Then any declaration taking a specific type of morphisms as parameter can instead take the
/--
Definition of `you` / `you` 的定义

English:
class you
  parameters: just defined
  (no additional axioms)

中文:
类 you
  参数: just defined
  (无附加公理)
-/
class you just defined:
```
-- Compare with: lemma do_something (f : MyHom A B) : sorry := sorry
/--
lemma `do_something` / 引理 `do_something`

English:
lemma do_something
  given: {F : Type*} [FunLike F A B] [MyHomClass F A B] (f : F)
  statement: sorry
  proof: sorry
```

This means anything set up for `MyHom`s will automatically work for `CoolerHomClass`es,
and defining `CoolerHomClass` only takes a constant amount of effort,
instead of linearly increasing the work per `MyHom`-related declaration.

## Design rationale

The current form of FunLike was set up in pull request https://github.com/leanprover-community/mathlib4/pull/8386:
https://github.com/leanprover-community/mathlib4/pull/8386
We made `FunLike` *unbundled*: child classes don't extend `FunLike`, they take a `[FunLike F A B]`
parameter instead. This suits the instance synthesis algorithm better: it's easy to verify a type
does **not** have a `FunLike` instance by checking the discrimination tree once instead of searching
the entire `extends` hierarchy.
-/

@[expose] public section

中文:
引理 do_something
  条件: {F : 类型} [函数状 F A B] [My态射类 F A B] (f : F)
  结论: sorry
  证明: sorry
```

This means anything set up for `MyHom`s will automatically work for `CoolerHomClass`es,
and defining `CoolerHomClass` only takes a constant amount of effort,
instead of linearly increasing the work per `MyHom`-related declaration.

## Design rationale

The current form of FunLike was set up in pull request https://github.com/leanprover-community/mathlib4/pull/8386:
https://github.com/leanprover-community/mathlib4/pull/8386
We made `FunLike` *unbundled*: child classes don't extend `FunLike`, they take a `[FunLike F A B]`
parameter instead. This suits the instance synthesis algorithm better: it's easy to verify a type
does **not** have a `FunLike` instance by checking the discrimination tree once instead of searching
the entire `extends` hierarchy.
-/

@[expose] public section
-/
lemma do_something {F : Type*} [FunLike F A B] [MyHomClass F A B] (f : F) : sorry :=
  sorry
```

This means anything set up for `MyHom`s will automatically work for `CoolerHomClass`es,
and defining `CoolerHomClass` only takes a constant amount of effort,
instead of linearly increasing the work per `MyHom`-related declaration.

## Design rationale

The current form of FunLike was set up in pull request https://github.com/leanprover-community/mathlib4/pull/8386:
https://github.com/leanprover-community/mathlib4/pull/8386
We made `FunLike` *unbundled*: child classes don't extend `FunLike`, they take a `[FunLike F A B]`
parameter instead. This suits the instance synthesis algorithm better: it's easy to verify a type
does **not** have a `FunLike` instance by checking the discrimination tree once instead of searching
the entire `extends` hierarchy.
-/

@[expose] public section

/-- The class `DFunLike F α β` expresses that terms of type `F` have an
injective coercion to (dependent) functions from `α` to `β`.

For non-dependent functions you can also use the abbreviation `FunLike`.

This typeclass is used in the definition of the homomorphism typeclasses,
such as `ZeroHomClass`, `MulHomClass`, `MonoidHomClass`, ....
-/
@[notation_class* toFun Simps.findCoercionArgs]
/--
Definition of `DFunLike` / `DFunLike` 的定义

English:
class DFunLike
  parameters: (F : Sort*) (α : outParam (Sort*)) (β : outParam <| α -> Sort*)
  axioms and operations (2):
    - coe : F -> forall a : α, β a
    - coe_injective : Function.Injective coe

中文:
类 依赖函数状
  参数: (F : 类型层*) (α : outParam (类型层*)) (β : outParam <| α -> 类型层*)
  公理与运算 (2 个):
    - coe : F -> 对任意 a : α, β a
    - coe_injective : 函数.单射 coe
-/
class DFunLike (F : Sort*) (α : outParam (Sort*)) (β : outParam <| α -> Sort*) where
  /-- The coercion from `F` to a function. -/
  coe : F -> forall a : α, β a
  /-- The coercion to functions must be injective. -/
  coe_injective : Function.Injective coe

/--
Definition of `FunLike` / `FunLike` 的定义

English:
abbreviation FunLike
  signature: F α β
  body: DFunLike F α fun _ => β

中文:
缩写 函数状
  签名: F α β
  定义体: DFunLike F α fun _ => β

Depends on / 依赖: DFunLike
-/
abbrev FunLike F α β := DFunLike F α fun _ => β

section Dependent

/-! ### `DFunLike F α β` where `β` depends on `a : α` -/

variable (F α : Sort*) (β : α -> Sort*)

namespace DFunLike

variable {F α β} [i : DFunLike F α β]

@[deprecated (since := "2026-06-04")] alias coe_injective' := coe_injective

instance (priority := 100) toCoeFun : CoeFun F (fun _ => forall a : α, β a) where
  coe := @DFunLike.coe _ _ β _ -- need to make explicit to beta reduce for non-dependent functions

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.Meta.registerCoercion ``DFunLike.coe
    (some { numArgs := 5, coercee := 4, type := .coeFun })

@[deprecated "Now a syntactic tautology" (since := "2026-06-04")]
/--
theorem `coe_eq_coe_fn` / 定理 `coe_eq_coe_fn`

English:
theorem coe_eq_coe_fn
  statement: (DFunLike.coe (F := F)) = (fun f => ↑f)
  proof: rfl

@[simp]

中文:
定理 coe_eq_coe_fn
  结论: (依赖函数状.coe (F := F)) = (fun f => ↑f)
  证明: rfl

@[simp]
-/
theorem coe_eq_coe_fn : (DFunLike.coe (F := F)) = (fun f => ↑f) := rfl

@[simp]
/--
theorem `coe_fn_eq` / 定理 `coe_fn_eq`

English:
theorem coe_fn_eq
  given: {f g : F}
  statement: (f : forall a : α, β a) = (g : forall a : α, β a) ↔ f = g
  proof: ⟨fun h => DFunLike.coe_injective h, fun h => by cases h; rfl⟩

中文:
定理 coe_fn_eq
  条件: {f g : F}
  结论: (f : 对任意 a : α, β a) = (g : 对任意 a : α, β a) ↔ f = g
  证明: ⟨fun h => DFunLike.coe_injective h, fun h => by cases h; rfl⟩

Depends on / 依赖: DFunLike, DFunLike.coe_injective, Subtype, Subtype.val, coe_injective
-/
theorem coe_fn_eq {f g : F} : (f : forall a : α, β a) = (g : forall a : α, β a) ↔ f = g :=
  ⟨fun h => DFunLike.coe_injective h, fun h => by cases h; rfl⟩

/--
theorem `ext'` / 定理 `ext'`

English:
theorem ext'
  given: {f g : F} (h : (f : forall a : α, β a) = (g : forall a : α, β a))
  statement: f = g
  proof: DFunLike.coe_injective h

中文:
定理 ext'
  条件: {f g : F} (h : (f : 对任意 a : α, β a) = (g : 对任意 a : α, β a))
  结论: f = g
  证明: DFunLike.coe_injective h

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall a : α, β a)) : f = g :=
  DFunLike.coe_injective h

/--
theorem `ext'_iff` / 定理 `ext'_iff`

English:
theorem ext'_iff
  given: {f g : F}
  statement: f = g ↔ (f : forall a : α, β a) = (g : forall a : α, β a)
  proof: coe_fn_eq.symm

中文:
定理 ext'_iff
  条件: {f g : F}
  结论: f = g ↔ (f : 对任意 a : α, β a) = (g : 对任意 a : α, β a)
  证明: coe_fn_eq.symm
-/
theorem ext'_iff {f g : F} : f = g ↔ (f : forall a : α, β a) = (g : forall a : α, β a) :=
  coe_fn_eq.symm

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (f g : F) (h : forall x : α, f x = g x)
  statement: f = g
  proof: DFunLike.coe_injective (funext h)

中文:
定理 ext
  条件: (f g : F) (h : 对任意 x : α, f x = g x)
  结论: f = g
  证明: DFunLike.coe_injective (funext h)

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem ext (f g : F) (h : forall x : α, f x = g x) : f = g :=
  DFunLike.coe_injective (funext h)

/--
theorem `ext_iff` / 定理 `ext_iff`

English:
theorem ext_iff
  given: {f g : F}
  statement: f = g ↔ forall x, f x = g x
  proof: coe_fn_eq.symm.trans funext_iff

中文:
定理 ext_iff
  条件: {f g : F}
  结论: f = g ↔ 对任意 x, f x = g x
  证明: coe_fn_eq.symm.trans funext_iff

Depends on / 依赖: coe_fn_eq, coe_fn_eq.symm.trans, funext_iff
-/
theorem ext_iff {f g : F} : f = g ↔ forall x, f x = g x :=
  coe_fn_eq.symm.trans funext_iff

/--
theorem `congr_fun` / 定理 `congr_fun`

English:
theorem congr_fun
  given: {f g : F} (h₁ : f = g) (x : α)
  statement: f x = g x
  proof: congr_fun (congr_arg _ h₁) x

中文:
定理 congr_fun
  条件: {f g : F} (h₁ : f = g) (x : α)
  结论: f x = g x
  证明: congr_fun (congr_arg _ h₁) x
-/
protected theorem congr_fun {f g : F} (h₁ : f = g) (x : α) : f x = g x :=
  congr_fun (congr_arg _ h₁) x

/--
theorem `ne_iff` / 定理 `ne_iff`

English:
theorem ne_iff
  given: {f g : F}
  statement: f != g ↔ exists a, f a != g a
  proof: ext_iff.not.trans not_forall

中文:
定理 ne_iff
  条件: {f g : F}
  结论: f != g ↔ 存在 a, f a != g a
  证明: ext_iff.not.trans not_forall

Depends on / 依赖: ext_iff, ext_iff.not.trans, not_forall
-/
theorem ne_iff {f g : F} : f != g ↔ exists a, f a != g a :=
  ext_iff.not.trans not_forall

/--
theorem `exists_ne` / 定理 `exists_ne`

English:
theorem exists_ne
  given: {f g : F} (h : f != g)
  statement: exists x, f x != g x
  proof: ne_iff.mp h

中文:
定理 存在_ne
  条件: {f g : F} (h : f != g)
  结论: 存在 x, f x != g x
  证明: ne_iff.mp h

Depends on / 依赖: ne_iff, ne_iff.mp
-/
theorem exists_ne {f g : F} (h : f != g) : exists x, f x != g x :=
  ne_iff.mp h

/--
lemma `subsingleton_cod` / 引理 `subsingleton_cod`

English:
lemma subsingleton_cod
  given: [forall a, Subsingleton (β a)]
  statement: Subsingleton F
  proof: coe_injective.subsingleton

include β in

中文:
引理 subsingleton_cod
  条件: [对任意 a, 子单例 (β a)]
  结论: 子单例 F
  证明: coe_injective.subsingleton

include β in

Depends on / 依赖: coe_injective, coe_injective.subsingleton, subsingleton
-/
lemma subsingleton_cod [forall a, Subsingleton (β a)] : Subsingleton F :=
  coe_injective.subsingleton

include β in
/--
lemma `subsingleton_dom` / 引理 `subsingleton_dom`

English:
lemma subsingleton_dom
  given: [IsEmpty α]
  statement: Subsingleton F
  proof: coe_injective.subsingleton

中文:
引理 subsingleton_dom
  条件: [是空 α]
  结论: 子单例 F
  证明: coe_injective.subsingleton

Depends on / 依赖: coe_injective, coe_injective.subsingleton, subsingleton
-/
lemma subsingleton_dom [IsEmpty α] : Subsingleton F :=
  coe_injective.subsingleton

end DFunLike

end Dependent

section NonDependent

/-! ### `FunLike F α β` where `β` does not depend on `a : α` -/

variable {F α β : Sort*} [i : FunLike F α β]

namespace DFunLike

/--
theorem `congr` / 定理 `congr`

English:
theorem congr
  given: {f g : F} {x y : α} (h₁ : f = g) (h₂ : x = y)
  statement: f x = g y
  proof: congr (congr_arg _ h₁) h₂

中文:
定理 congr
  条件: {f g : F} {x y : α} (h₁ : f = g) (h₂ : x = y)
  结论: f x = g y
  证明: congr (congr_arg _ h₁) h₂

Depends on / 依赖: Nat.zero_le, le_stable, zero_le
-/
protected theorem congr {f g : F} {x y : α} (h₁ : f = g) (h₂ : x = y) : f x = g y :=
  congr (congr_arg _ h₁) h₂

/--
theorem `congr_arg` / 定理 `congr_arg`

English:
theorem congr_arg
  given: (f : F) {x y : α} (h₂ : x = y)
  statement: f x = f y
  proof: congr_arg _ h₂

中文:
定理 congr_arg
  条件: (f : F) {x y : α} (h₂ : x = y)
  结论: f x = f y
  证明: congr_arg _ h₂
-/
protected theorem congr_arg (f : F) {x y : α} (h₂ : x = y) : f x = f y :=
  congr_arg _ h₂

/--
theorem `dite_apply` / 定理 `dite_apply`

English:
theorem dite_apply
  given: {P : Prop} [Decidable P] (f : P -> F) (g : ¬P -> F) (x : α)
  proof: by
  split_ifs <;> rfl

中文:
定理 dite_apply
  条件: {P : 命题} [可判定 P] (f : P -> F) (g : ¬P -> F) (x : α)
  证明: by
  split_ifs <;> rfl

Depends on / 依赖: split_ifs
-/
theorem dite_apply {P : Prop} [Decidable P] (f : P -> F) (g : ¬P -> F) (x : α) :
    (if h : P then f h else g h) x = if h : P then f h x else g h x := by
  split_ifs <;> rfl

/--
theorem `ite_apply` / 定理 `ite_apply`

English:
theorem ite_apply
  given: {P : Prop} [Decidable P] (f g : F) (x : α)
  proof: dite_apply _ _ _

中文:
定理 ite_apply
  条件: {P : 命题} [可判定 P] (f g : F) (x : α)
  证明: dite_apply _ _ _

Depends on / 依赖: dite_apply
-/
theorem ite_apply {P : Prop} [Decidable P] (f g : F) (x : α) :
    (if P then f else g) x = if P then f x else g x :=
  dite_apply _ _ _

end DFunLike

end NonDependent
