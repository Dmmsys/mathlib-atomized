/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Data.FunLike.Basic

/-!
# Typeclass for a type `F` with an injective map to `A ↪ B`

This typeclass is primarily for use by embeddings such as `RelEmbedding`.

## Basic usage of `EmbeddingLike`

A typical type of embeddings should be declared as:
```
structure MyEmbedding (A B : Type*) [MyClass A] [MyClass B] where
  (toFun : A → B)
  (injective' : Function.Injective toFun)
  (map_op' : ∀ (x y : A), toFun (MyClass.op x y) = MyClass.op (toFun x) (toFun y))

namespace MyEmbedding

variable (A B : Type*) [MyClass A] [MyClass B]

instance : FunLike (MyEmbedding A B) A B where
  coe := MyEmbedding.toFun
  coe_injective := fun f g h ↦ by cases f; cases g; congr

-- This instance is optional if you follow the "Embedding class" design below:
instance : EmbeddingLike (MyEmbedding A B) A B where
  injective' := MyEmbedding.injective'

@[ext] theorem ext {f g : MyEmbedding A B} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : MyEmbedding A B) (f' : A -> B) (h : f' = ⇑f)
  body: { toFun := f'
    injective' := h.symm ▸ f.injective'
    map_op' := h.symm ▸ f.map_op' }

中文:
定义 copy
  签名: (f : My嵌入 A B) (f' : A -> B) (h : f' = ⇑f)
  定义体: { toFun := f'
    injective' := h.symm ▸ f.injective'
    map_op' := h.symm ▸ f.map_op' }
-/
protected def copy (f : MyEmbedding A B) (f' : A -> B) (h : f' = ⇑f) : MyEmbedding A B :=
  { toFun := f'
    injective' := h.symm ▸ f.injective'
    map_op' := h.symm ▸ f.map_op' }

end MyEmbedding
```

This file will then provide a `CoeFun` instance and various
extensionality and simp lemmas.

## Embedding classes extending `EmbeddingLike`

The `EmbeddingLike` design provides further benefits if you put in a bit more work.
The first step is to extend `EmbeddingLike` to create a class of those types satisfying
the axioms of your new type of morphisms.
Continuing the example above:

```
/--
Definition of `MyEmbeddingClass` / `MyEmbeddingClass` 的定义

English:
class MyEmbeddingClass
  parameters: (F : Type*) (A B : outParam Type*) [MyClass A] [MyClass B]
  extends: EmbeddingLike F A B
  axioms and operations (1):
    - map_op : forall (f : F) (x y : A), f (MyClass.op x y) = MyClass.op (f x) (f y)

中文:
类 My嵌入类
  参数: (F : 类型) (A B : outParam 类型) [MyClass A] [MyClass B]
  继承: EmbeddingLike F A B
  公理与运算 (1 个):
    - map_op : 对任意 (f : F) (x y : A), f (MyClass.op x y) = MyClass.op (f x) (f y)
-/
class MyEmbeddingClass (F : Type*) (A B : outParam Type*) [MyClass A] [MyClass B]
    [FunLike F A B]
    extends EmbeddingLike F A B where
  map_op : forall (f : F) (x y : A), f (MyClass.op x y) = MyClass.op (f x) (f y)

@[simp]
/--
lemma `map_op` / 引理 `map_op`

English:
lemma map_op
  statement: {F A B : Type*} [MyClass A] [MyClass B] [FunLike F A B] [MyEmbeddingClass F A B]
  proof: MyEmbeddingClass.map_op _ _ _

中文:
引理 map_op
  结论: {F A B : 类型} [MyClass A] [MyClass B] [函数状 F A B] [My嵌入类 F A B]
  证明: MyEmbeddingClass.map_op _ _ _
-/
lemma map_op {F A B : Type*} [MyClass A] [MyClass B] [FunLike F A B] [MyEmbeddingClass F A B]
    (f : F) (x y : A) :
    f (MyClass.op x y) = MyClass.op (f x) (f y) :=
  MyEmbeddingClass.map_op _ _ _

namespace MyEmbedding

variable {A B : Type*} [MyClass A] [MyClass B]

-- You can replace `MyEmbedding.EmbeddingLike` with the below instance:
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MyEmbeddingClass (MyEmbedding A B) A B
  body: MyEmbedding.injective'
  map_op := MyEmbedding.map_op'

中文:
实例 :
  签名: My嵌入类 (My嵌入 A B) A B
  定义体: MyEmbedding.injective'
  map_op := MyEmbedding.map_op'

Depends on / 依赖: MyEmbedding, MyEmbedding.injective, injective
-/
instance : MyEmbeddingClass (MyEmbedding A B) A B where
  injective' := MyEmbedding.injective'
  map_op := MyEmbedding.map_op'

end MyEmbedding
```

The second step is to add instances of your new `MyEmbeddingClass` for all types extending
`MyEmbedding`.
Typically, you can just declare a new class analogous to `MyEmbeddingClass`:

```
/--
Definition of `CoolerEmbedding` / `CoolerEmbedding` 的定义

English:
structure CoolerEmbedding
  parameters: (A B : Type*) [CoolClass A] [CoolClass B]
  extends: MyEmbedding A B
  axioms and operations (1):
    - (map_cool' : toFun CoolClass.cool = CoolClass.cool)

中文:
结构 余oler嵌入
  参数: (A B : 类型) [CoolClass A] [CoolClass B]
  继承: My嵌入 A B
  公理与运算 (1 个):
    - (map_cool' : toFun CoolClass.cool = CoolClass.cool)
-/
structure CoolerEmbedding (A B : Type*) [CoolClass A] [CoolClass B] extends MyEmbedding A B where
  (map_cool' : toFun CoolClass.cool = CoolClass.cool)

/--
Definition of `CoolerEmbeddingClass` / `CoolerEmbeddingClass` 的定义

English:
class CoolerEmbeddingClass
  parameters: (F : Type*) (A B : outParam Type*) [CoolClass A] [CoolClass B]
  extends: MyEmbeddingClass F A B
  axioms and operations (1):
    - (map_cool : forall (f : F), f CoolClass.cool = CoolClass.cool)

中文:
类 余oler嵌入类
  参数: (F : 类型) (A B : outParam 类型) [CoolClass A] [CoolClass B]
  继承: My嵌入类 F A B
  公理与运算 (1 个):
    - (map_cool : 对任意 (f : F), f CoolClass.cool = CoolClass.cool)
-/
class CoolerEmbeddingClass (F : Type*) (A B : outParam Type*) [CoolClass A] [CoolClass B]
    [FunLike F A B]
    extends MyEmbeddingClass F A B where
  (map_cool : forall (f : F), f CoolClass.cool = CoolClass.cool)

@[simp]
/--
lemma `map_cool` / 引理 `map_cool`

English:
lemma map_cool
  statement: {F A B : Type*} [CoolClass A] [CoolClass B]
  proof: CoolerEmbeddingClass.map_cool _

中文:
引理 map_cool
  结论: {F A B : 类型} [CoolClass A] [CoolClass B]
  证明: CoolerEmbeddingClass.map_cool _

Depends on / 依赖: CoolerEmbeddingClass, CoolerEmbeddingClass.map_cool, map_cool
-/
lemma map_cool {F A B : Type*} [CoolClass A] [CoolClass B]
    [FunLike F A B] [CoolerEmbeddingClass F A B] (f : F) :
    f CoolClass.cool = CoolClass.cool :=
  CoolerEmbeddingClass.map_cool _

variable {A B : Type*} [CoolClass A] [CoolClass B]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (CoolerEmbedding A B) A B
  body: f.toFun
  coe_injective f g h := by cases f; cases g; congr; apply DFunLike.coe_injective; congr

中文:
实例 :
  签名: 函数状 (余oler嵌入 A B) A B
  定义体: f.toFun
  coe_injective f g h := by cases f; cases g; congr; apply DFunLike.coe_injective; congr

Depends on / 依赖: f.toFun
-/
instance : FunLike (CoolerEmbedding A B) A B where
  coe f := f.toFun
  coe_injective f g h := by cases f; cases g; congr; apply DFunLike.coe_injective; congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoolerEmbeddingClass (CoolerEmbedding A B) A B
  body: f.injective'
  map_op f := f.map_op'
  map_cool f := f.map_cool'

中文:
实例 :
  签名: 余oler嵌入类 (余oler嵌入 A B) A B
  定义体: f.injective'
  map_op f := f.map_op'
  map_cool f := f.map_cool'

Depends on / 依赖: f.injective, injective
-/
instance : CoolerEmbeddingClass (CoolerEmbedding A B) A B where
  injective' f := f.injective'
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
-- Compare with: lemma do_something (f : MyEmbedding A B) : sorry := sorry
/--
lemma `do_something` / 引理 `do_something`

English:
lemma do_something
  given: {F : Type*} [FunLike F A B] [MyEmbeddingClass F A B] (f : F)
  statement: sorry
  proof: sorry
```

This means anything set up for `MyEmbedding`s will automatically work for `CoolerEmbeddingClass`es,
and defining `CoolerEmbeddingClass` only takes a constant amount of effort,
instead of linearly increasing the work per `MyEmbedding`-related declaration.
-/

@[expose] public section

中文:
引理 do_something
  条件: {F : 类型} [函数状 F A B] [My嵌入类 F A B] (f : F)
  结论: sorry
  证明: sorry
```

This means anything set up for `MyEmbedding`s will automatically work for `CoolerEmbeddingClass`es,
and defining `CoolerEmbeddingClass` only takes a constant amount of effort,
instead of linearly increasing the work per `MyEmbedding`-related declaration.
-/

@[expose] public section
-/
lemma do_something {F : Type*} [FunLike F A B] [MyEmbeddingClass F A B] (f : F) : sorry := sorry
```

This means anything set up for `MyEmbedding`s will automatically work for `CoolerEmbeddingClass`es,
and defining `CoolerEmbeddingClass` only takes a constant amount of effort,
instead of linearly increasing the work per `MyEmbedding`-related declaration.
-/

@[expose] public section


/--
Definition of `EmbeddingLike` / `EmbeddingLike` 的定义

English:
class EmbeddingLike
  parameters: (F : Sort*) (α β : outParam (Sort*)) [FunLike F α β]
  axioms and operations (1):
    - injective' : forall f : F, Function.Injective (DFunLike.coe f)

中文:
类 EmbeddingLike
  参数: (F : 类型层*) (α β : outParam (类型层*)) [函数状 F α β]
  公理与运算 (1 个):
    - injective' : 对任意 f : F, 函数.单射 (依赖函数状.coe f)
-/
class EmbeddingLike (F : Sort*) (α β : outParam (Sort*)) [FunLike F α β] : Prop where
  /-- The coercion to functions must produce injective functions. -/
  injective' : forall f : F, Function.Injective (DFunLike.coe f)

namespace EmbeddingLike

variable {F α β γ : Sort*} [FunLike F α β] [i : EmbeddingLike F α β]

/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  given: (f : F)
  statement: Function.Injective f
  proof: injective' f

@[simp]

中文:
定理 injective
  条件: (f : F)
  结论: 函数.单射 f
  证明: injective' f

@[simp]
-/
protected theorem injective (f : F) : Function.Injective f :=
  injective' f

@[simp]
/--
theorem `apply_eq_iff_eq` / 定理 `apply_eq_iff_eq`

English:
theorem apply_eq_iff_eq
  given: (f : F) {x y : α}
  statement: f x = f y ↔ x = y
  proof: (EmbeddingLike.injective f).eq_iff

@[simp]

中文:
定理 apply_eq_iff_eq
  条件: (f : F) {x y : α}
  结论: f x = f y ↔ x = y
  证明: (EmbeddingLike.injective f).eq_iff

@[simp]

Depends on / 依赖: EmbeddingLike, EmbeddingLike.injective, eq_iff, injective
-/
theorem apply_eq_iff_eq (f : F) {x y : α} : f x = f y ↔ x = y :=
  (EmbeddingLike.injective f).eq_iff

@[simp]
/--
theorem `comp_injective` / 定理 `comp_injective`

English:
theorem comp_injective
  given: {F : Sort*} [FunLike F β γ] [EmbeddingLike F β γ] (f : α -> β) (e : F)
  proof: (EmbeddingLike.injective e).of_comp_iff f

中文:
定理 comp_injective
  条件: {F : 类型层*} [函数状 F β γ] [EmbeddingLike F β γ] (f : α -> β) (e : F)
  证明: (EmbeddingLike.injective e).of_comp_iff f

Depends on / 依赖: EmbeddingLike, EmbeddingLike.injective, injective, of_comp_iff
-/
theorem comp_injective {F : Sort*} [FunLike F β γ] [EmbeddingLike F β γ] (f : α -> β) (e : F) :
    Function.Injective (e ∘ f) ↔ Function.Injective f :=
  (EmbeddingLike.injective e).of_comp_iff f

end EmbeddingLike
