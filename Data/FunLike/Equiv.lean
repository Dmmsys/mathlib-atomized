/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Data.FunLike.Embedding

/-!
# Typeclass for a type `F` with an injective map to `A ≃ B`

This typeclass is primarily for use by isomorphisms like `MonoidEquiv` and `LinearEquiv`.

## Basic usage of `EquivLike`

A typical type of isomorphisms should be declared as:
```
structure MyIso (A B : Type*) [MyClass A] [MyClass B] extends Equiv A B where
  (map_op' : ∀ (x y : A), toFun (MyClass.op x y) = MyClass.op (toFun x) (toFun y))

namespace MyIso

variable (A B : Type*) [MyClass A] [MyClass B]

instance instEquivLike : EquivLike (MyIso A B) A B where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by cases f; cases g; congr; exact EquivLike.coe_injective' _ _ h₁ h₂

@[ext] theorem ext {f g : MyIso A B} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : MyIso A B) (f' : A -> B) (f_inv : B -> A)
  body: f'
  invFun := f_inv
  left_inv := h₁.symm ▸ h₂.symm ▸ f.left_inv
  right_inv := h₁.symm ▸ h₂.symm ▸ f.right_inv
  map_op' := h₁.symm ▸ f.map_op'

中文:
定义 copy
  签名: (f : MyIso A B) (f' : A -> B) (f_inv : B -> A)
  定义体: f'
  invFun := f_inv
  left_inv := h₁.symm ▸ h₂.symm ▸ f.left_inv
  right_inv := h₁.symm ▸ h₂.symm ▸ f.right_inv
  map_op' := h₁.symm ▸ f.map_op'
-/
protected def copy (f : MyIso A B) (f' : A -> B) (f_inv : B -> A)
    (h₁ : f' = f) (h₂ : f_inv = f.invFun) : MyIso A B where
  toFun := f'
  invFun := f_inv
  left_inv := h₁.symm ▸ h₂.symm ▸ f.left_inv
  right_inv := h₁.symm ▸ h₂.symm ▸ f.right_inv
  map_op' := h₁.symm ▸ f.map_op'

end MyIso
```

This file will then provide a `CoeFun` instance and various
extensionality and simp lemmas.

## Isomorphism classes extending `EquivLike`

The `EquivLike` design provides further benefits if you put in a bit more work.
The first step is to extend `EquivLike` to create a class of those types satisfying
the axioms of your new type of isomorphisms.
Continuing the example above:

```
/--
Definition of `MyIsoClass` / `MyIsoClass` 的定义

English:
class MyIsoClass
  parameters: (F : Type*) (A B : outParam Type*) [MyClass A] [MyClass B]
  extends: MyHomClass F A B
  (no additional axioms)

中文:
类 MyIsoClass
  参数: (F : 类型) (A B : outParam 类型) [MyClass A] [MyClass B]
  继承: MyHomClass F A B
  (无附加公理)
-/
class MyIsoClass (F : Type*) (A B : outParam Type*) [MyClass A] [MyClass B]
    [EquivLike F A B]
    extends MyHomClass F A B

namespace MyIso

variable {A B : Type*} [MyClass A] [MyClass B]

-- This goes after `MyIsoClass.instEquivLike`:
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MyIsoClass (MyIso A B) A B
  body: MyIso.map_op'

中文:
实例 :
  签名: MyIsoClass (MyIso A B) A B
  定义体: MyIso.map_op'

Depends on / 依赖: MyIso.map_op, map_op
-/
instance : MyIsoClass (MyIso A B) A B where
  map_op := MyIso.map_op'

-- [Insert `ext` and `copy` here]

end MyIso
```

The second step is to add instances of your new `MyIsoClass` for all types extending `MyIso`.
Typically, you can just declare a new class analogous to `MyIsoClass`:

```
/--
Definition of `CoolerIso` / `CoolerIso` 的定义

English:
structure CoolerIso
  parameters: (A B : Type*) [CoolClass A] [CoolClass B]
  extends: MyIso A B
  axioms and operations (1):
    - (map_cool' : toFun CoolClass.cool = CoolClass.cool)

中文:
结构 CoolerIso
  参数: (A B : 类型) [CoolClass A] [CoolClass B]
  继承: MyIso A B
  公理与运算 (1 个):
    - (map_cool' : toFun CoolClass.cool = CoolClass.cool)
-/
structure CoolerIso (A B : Type*) [CoolClass A] [CoolClass B] extends MyIso A B where
  (map_cool' : toFun CoolClass.cool = CoolClass.cool)

/--
Definition of `CoolerIsoClass` / `CoolerIsoClass` 的定义

English:
class CoolerIsoClass
  parameters: (F : Type*) (A B : outParam Type*) [CoolClass A] [CoolClass B]
  extends: MyIsoClass F A B
  axioms and operations (1):
    - (map_cool : forall (f : F), f CoolClass.cool = CoolClass.cool)

中文:
类 CoolerIsoClass
  参数: (F : 类型) (A B : outParam 类型) [CoolClass A] [CoolClass B]
  继承: MyIsoClass F A B
  公理与运算 (1 个):
    - (map_cool : 对任意 (f : F), f CoolClass.cool = CoolClass.cool)
-/
class CoolerIsoClass (F : Type*) (A B : outParam Type*) [CoolClass A] [CoolClass B]
    [EquivLike F A B]
    extends MyIsoClass F A B where
  (map_cool : forall (f : F), f CoolClass.cool = CoolClass.cool)

/--
lemma `map_cool` / 引理 `map_cool`

English:
lemma map_cool
  statement: {F A B : Type*} [CoolClass A] [CoolClass B]
  proof: CoolerIsoClass.map_cool _

中文:
引理 map_cool
  结论: {F A B : 类型} [CoolClass A] [CoolClass B]
  证明: CoolerIsoClass.map_cool _
-/
@[simp] lemma map_cool {F A B : Type*} [CoolClass A] [CoolClass B]
    [EquivLike F A B] [CoolerIsoClass F A B] (f : F) :
    f CoolClass.cool = CoolClass.cool :=
  CoolerIsoClass.map_cool _

namespace CoolerIso

variable {A B : Type*} [CoolClass A] [CoolClass B]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EquivLike (CoolerIso A B) A B
  body: f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by cases f; cases g; congr; exact EquivLike.coe_injective' _ _ h₁ h₂

中文:
实例 :
  签名: EquivLike (CoolerIso A B) A B
  定义体: f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by cases f; cases g; congr; exact EquivLike.coe_injective' _ _ h₁ h₂

Depends on / 依赖: f.toFun
-/
instance : EquivLike (CoolerIso A B) A B where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by cases f; cases g; congr; exact EquivLike.coe_injective' _ _ h₁ h₂

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoolerIsoClass (CoolerIso A B) A B
  body: f.map_op'
  map_cool f := f.map_cool'

中文:
实例 :
  签名: CoolerIsoClass (CoolerIso A B) A B
  定义体: f.map_op'
  map_cool f := f.map_cool'

Depends on / 依赖: f.map_op, map_op
-/
instance : CoolerIsoClass (CoolerIso A B) A B where
  map_op f := f.map_op'
  map_cool f := f.map_cool'

-- [Insert `ext` and `copy` here]

end CoolerIso
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
-- Compare with: lemma do_something (f : MyIso A B) : sorry := sorry
/--
lemma `do_something` / 引理 `do_something`

English:
lemma do_something
  given: {F : Type*} [EquivLike F A B] [MyIsoClass F A B] (f : F)
  statement: sorry
  proof: sorry
```

This means anything set up for `MyIso`s will automatically work for `CoolerIsoClass`es,
and defining `CoolerIsoClass` only takes a constant amount of effort,
instead of linearly increasing the work per `MyIso`-related declaration.

-/

@[expose] public section

中文:
引理 do_something
  条件: {F : 类型} [EquivLike F A B] [MyIsoClass F A B] (f : F)
  结论: sorry
  证明: sorry
```

This means anything set up for `MyIso`s will automatically work for `CoolerIsoClass`es,
and defining `CoolerIsoClass` only takes a constant amount of effort,
instead of linearly increasing the work per `MyIso`-related declaration.

-/

@[expose] public section
-/
lemma do_something {F : Type*} [EquivLike F A B] [MyIsoClass F A B] (f : F) : sorry := sorry
```

This means anything set up for `MyIso`s will automatically work for `CoolerIsoClass`es,
and defining `CoolerIsoClass` only takes a constant amount of effort,
instead of linearly increasing the work per `MyIso`-related declaration.

-/

@[expose] public section


/--
Definition of `EquivLike` / `EquivLike` 的定义

English:
class EquivLike
  parameters: (E : Sort*) (α β : outParam (Sort*))
  axioms and operations (5):
    - coe : E -> α -> β
    - inv : E -> β -> α
    - left_inv : forall e, Function.LeftInverse (inv e) (coe e)
    - right_inv : forall e, Function.RightInverse (inv e) (coe e)
    - coe_injective' : forall e g, coe e = coe g -> inv e = inv g -> e = g

中文:
类 EquivLike
  参数: (E : Sort*) (α β : outParam (Sort*))
  公理与运算 (5 个):
    - coe : E -> α -> β
    - inv : E -> β -> α
    - left_inv : 对任意 e, Function.LeftInverse (inv e) (coe e)
    - right_inv : 对任意 e, Function.RightInverse (inv e) (coe e)
    - coe_injective' : 对任意 e g, coe e = coe g -> inv e = inv g -> e = g
-/
class EquivLike (E : Sort*) (α β : outParam (Sort*)) where
  /-- The coercion to a function in the forward direction. -/
  coe : E -> α -> β
  /-- The coercion to a function in the backwards direction. -/
  inv : E -> β -> α
  /-- The coercions are left inverses. -/
  left_inv : forall e, Function.LeftInverse (inv e) (coe e)
  /-- The coercions are right inverses. -/
  right_inv : forall e, Function.RightInverse (inv e) (coe e)
  /-- The two coercions to functions are jointly injective. -/
  coe_injective' : forall e g, coe e = coe g -> inv e = inv g -> e = g
  -- This is mathematically equivalent to either of the coercions to functions being injective, but
  -- the `inv` hypothesis makes this easier to prove with `congr'`

namespace EquivLike

variable {E F α β γ : Sort*} [EquivLike E α β] [EquivLike F β γ]

/--
theorem `inv_injective` / 定理 `inv_injective`

English:
theorem inv_injective
  statement: Function.Injective (EquivLike.inv : E -> β -> α)
  proof: fun e g h =>
  coe_injective' e g ((right_inv e).eq_rightInverse (h.symm ▸ left_inv g)) h

中文:
定理 inv_injective
  结论: Function.Injective (EquivLike.inv : E -> β -> α)
  证明: fun e g h =>
  coe_injective' e g ((right_inv e).eq_rightInverse (h.symm ▸ left_inv g)) h
-/
theorem inv_injective : Function.Injective (EquivLike.inv : E -> β -> α) := fun e g h =>
  coe_injective' e g ((right_inv e).eq_rightInverse (h.symm ▸ left_inv g)) h

instance (priority := 100) toFunLike : FunLike E α β where
  coe := (coe : E -> α -> β)
  coe_injective e g h :=
    coe_injective' e g h ((left_inv e).eq_rightInverse (h.symm ▸ right_inv g))

/--
theorem `coe_apply` / 定理 `coe_apply`

English:
theorem coe_apply
  given: {e : E} {a : α}
  statement: coe e a = e a
  proof: rfl

中文:
定理 coe_apply
  条件: {e : E} {a : α}
  结论: coe e a = e a
  证明: rfl
-/
@[simp] theorem coe_apply {e : E} {a : α} : coe e a = e a := rfl

/--
theorem `inv_apply_eq` / 定理 `inv_apply_eq`

English:
theorem inv_apply_eq
  given: {e : E} {b : β} {a : α}
  statement: inv e b = a ↔ b = e a
  proof: by
  constructor <;> rintro ⟨_, rfl⟩
  exacts [(right_inv e b).symm, left_inv e a]

中文:
定理 inv_apply_eq
  条件: {e : E} {b : β} {a : α}
  结论: inv e b = a ↔ b = e a
  证明: by
  constructor <;> rintro ⟨_, rfl⟩
  exacts [(right_inv e b).symm, left_inv e a]

Depends on / 依赖: exacts, left_inv, right_inv
-/
theorem inv_apply_eq {e : E} {b : β} {a : α} : inv e b = a ↔ b = e a := by
  constructor <;> rintro ⟨_, rfl⟩
  exacts [(right_inv e b).symm, left_inv e a]

instance (priority := 100) toEmbeddingLike : EmbeddingLike E α β where
  injective' e := (left_inv e).injective

/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  given: (e : E)
  statement: Function.Injective e
  proof: EmbeddingLike.injective e

中文:
定理 injective
  条件: (e : E)
  结论: Function.Injective e
  证明: EmbeddingLike.injective e
-/
protected theorem injective (e : E) : Function.Injective e :=
  EmbeddingLike.injective e

/--
theorem `surjective` / 定理 `surjective`

English:
theorem surjective
  given: (e : E)
  statement: Function.Surjective e
  proof: (right_inv e).surjective

中文:
定理 surjective
  条件: (e : E)
  结论: Function.Surjective e
  证明: (right_inv e).surjective
-/
protected theorem surjective (e : E) : Function.Surjective e :=
  (right_inv e).surjective

/--
theorem `bijective` / 定理 `bijective`

English:
theorem bijective
  given: (e : E)
  statement: Function.Bijective (e : α -> β)
  proof: ⟨EquivLike.injective e, EquivLike.surjective e⟩

中文:
定理 bijective
  条件: (e : E)
  结论: Function.Bijective (e : α -> β)
  证明: ⟨EquivLike.injective e, EquivLike.surjective e⟩
-/
protected theorem bijective (e : E) : Function.Bijective (e : α -> β) :=
  ⟨EquivLike.injective e, EquivLike.surjective e⟩

/--
theorem `apply_eq_iff_eq` / 定理 `apply_eq_iff_eq`

English:
theorem apply_eq_iff_eq
  given: (f : E) {x y : α}
  statement: f x = f y ↔ x = y
  proof: EmbeddingLike.apply_eq_iff_eq f

@[simp]

中文:
定理 apply_eq_iff_eq
  条件: (f : E) {x y : α}
  结论: f x = f y ↔ x = y
  证明: EmbeddingLike.apply_eq_iff_eq f

@[simp]

Depends on / 依赖: EmbeddingLike, EmbeddingLike.apply_eq_iff_eq, apply_eq_iff_eq
-/
theorem apply_eq_iff_eq (f : E) {x y : α} : f x = f y ↔ x = y :=
  EmbeddingLike.apply_eq_iff_eq f

@[simp]
/--
theorem `injective_comp` / 定理 `injective_comp`

English:
theorem injective_comp
  given: (e : E) (f : β -> γ)
  statement: Function.Injective (f ∘ e) ↔ Function.Injective f
  proof: Function.Injective.of_comp_iff' f (EquivLike.bijective e)

@[simp]

中文:
定理 injective_comp
  条件: (e : E) (f : β -> γ)
  结论: Function.Injective (f ∘ e) ↔ Function.Injective f
  证明: Function.Injective.of_comp_iff' f (EquivLike.bijective e)

@[simp]

Depends on / 依赖: EquivLike, EquivLike.bijective, Function, Function.Injective.of_comp_iff, Injective, bijective, of_comp_iff
-/
theorem injective_comp (e : E) (f : β -> γ) : Function.Injective (f ∘ e) ↔ Function.Injective f :=
  Function.Injective.of_comp_iff' f (EquivLike.bijective e)

@[simp]
/--
theorem `surjective_comp` / 定理 `surjective_comp`

English:
theorem surjective_comp
  given: (e : E) (f : β -> γ)
  statement: Function.Surjective (f ∘ e) ↔ Function.Surjective f
  proof: (EquivLike.surjective e).of_comp_iff f

@[simp]

中文:
定理 surjective_comp
  条件: (e : E) (f : β -> γ)
  结论: Function.Surjective (f ∘ e) ↔ Function.Surjective f
  证明: (EquivLike.surjective e).of_comp_iff f

@[simp]

Depends on / 依赖: EquivLike, EquivLike.surjective, Terminates, length, of_comp_iff, s.Terminates, s.length, surjective
-/
theorem surjective_comp (e : E) (f : β -> γ) : Function.Surjective (f ∘ e) ↔ Function.Surjective f :=
  (EquivLike.surjective e).of_comp_iff f

@[simp]
/--
theorem `bijective_comp` / 定理 `bijective_comp`

English:
theorem bijective_comp
  given: (e : E) (f : β -> γ)
  statement: Function.Bijective (f ∘ e) ↔ Function.Bijective f
  proof: (EquivLike.bijective e).of_comp_iff f

中文:
定理 bijective_comp
  条件: (e : E) (f : β -> γ)
  结论: Function.Bijective (f ∘ e) ↔ Function.Bijective f
  证明: (EquivLike.bijective e).of_comp_iff f

Depends on / 依赖: EquivLike, EquivLike.bijective, bijective, of_comp_iff
-/
theorem bijective_comp (e : E) (f : β -> γ) : Function.Bijective (f ∘ e) ↔ Function.Bijective f :=
  (EquivLike.bijective e).of_comp_iff f

/-- This lemma is only supposed to be used in the generic context, when working with instances
of classes extending `EquivLike`.
For concrete isomorphism types such as `Equiv`, you should use `Equiv.symm_apply_apply`
or its equivalent.

TODO: define a generic form of `Equiv.symm`. -/
@[simp]
/--
theorem `inv_apply_apply` / 定理 `inv_apply_apply`

English:
theorem inv_apply_apply
  given: (e : E) (a : α)
  statement: inv e (e a) = a
  proof: left_inv _ _

中文:
定理 inv_apply_apply
  条件: (e : E) (a : α)
  结论: inv e (e a) = a
  证明: left_inv _ _

Depends on / 依赖: left_inv
-/
theorem inv_apply_apply (e : E) (a : α) : inv e (e a) = a := left_inv _ _

/-- This lemma is only supposed to be used in the generic context, when working with instances
of classes extending `EquivLike`.
For concrete isomorphism types such as `Equiv`, you should use `Equiv.apply_symm_apply`
or its equivalent.

TODO: define a generic form of `Equiv.symm`. -/
@[simp]
/--
theorem `apply_inv_apply` / 定理 `apply_inv_apply`

English:
theorem apply_inv_apply
  given: (e : E) (b : β)
  statement: e (inv e b) = b
  proof: right_inv _ _

中文:
定理 apply_inv_apply
  条件: (e : E) (b : β)
  结论: e (inv e b) = b
  证明: right_inv _ _

Depends on / 依赖: right_inv
-/
theorem apply_inv_apply (e : E) (b : β) : e (inv e b) = b := right_inv _ _

/--
theorem `comp_injective` / 定理 `comp_injective`

English:
theorem comp_injective
  given: (f : α -> β) (e : F)
  statement: Function.Injective (e ∘ f) ↔ Function.Injective f
  proof: EmbeddingLike.comp_injective f e

@[simp]

中文:
定理 comp_injective
  条件: (f : α -> β) (e : F)
  结论: Function.Injective (e ∘ f) ↔ Function.Injective f
  证明: EmbeddingLike.comp_injective f e

@[simp]

Depends on / 依赖: EmbeddingLike, EmbeddingLike.comp_injective, comp_injective
-/
theorem comp_injective (f : α -> β) (e : F) : Function.Injective (e ∘ f) ↔ Function.Injective f :=
  EmbeddingLike.comp_injective f e

@[simp]
/--
theorem `comp_surjective` / 定理 `comp_surjective`

English:
theorem comp_surjective
  given: (f : α -> β) (e : F)
  statement: Function.Surjective (e ∘ f) ↔ Function.Surjective f
  proof: Function.Surjective.of_comp_iff' (EquivLike.bijective e) f

@[simp]

中文:
定理 comp_surjective
  条件: (f : α -> β) (e : F)
  结论: Function.Surjective (e ∘ f) ↔ Function.Surjective f
  证明: Function.Surjective.of_comp_iff' (EquivLike.bijective e) f

@[simp]

Depends on / 依赖: EquivLike, EquivLike.bijective, Function, Function.Surjective.of_comp_iff, Surjective, bijective, of_comp_iff
-/
theorem comp_surjective (f : α -> β) (e : F) : Function.Surjective (e ∘ f) ↔ Function.Surjective f :=
  Function.Surjective.of_comp_iff' (EquivLike.bijective e) f

@[simp]
/--
theorem `comp_bijective` / 定理 `comp_bijective`

English:
theorem comp_bijective
  given: (f : α -> β) (e : F)
  statement: Function.Bijective (e ∘ f) ↔ Function.Bijective f
  proof: (EquivLike.bijective e).of_comp_iff' f

include β in

中文:
定理 comp_bijective
  条件: (f : α -> β) (e : F)
  结论: Function.Bijective (e ∘ f) ↔ Function.Bijective f
  证明: (EquivLike.bijective e).of_comp_iff' f

include β in

Depends on / 依赖: EquivLike, EquivLike.bijective, bijective, of_comp_iff
-/
theorem comp_bijective (f : α -> β) (e : F) : Function.Bijective (e ∘ f) ↔ Function.Bijective f :=
  (EquivLike.bijective e).of_comp_iff' f

include β in
/--
lemma `subsingleton_dom` / 引理 `subsingleton_dom`

English:
lemma subsingleton_dom
  given: [Subsingleton α]
  statement: Subsingleton E
  proof: ⟨fun f g => DFunLike.ext f g fun _ => (right_inv f).injective Subsingleton.elim _ _⟩

中文:
引理 subsingleton_dom
  条件: [Subsingleton α]
  结论: Subsingleton E
  证明: ⟨fun f g => DFunLike.ext f g fun _ => (right_inv f).injective Subsingleton.elim _ _⟩

Depends on / 依赖: DFunLike, DFunLike.ext, Subsingleton, Subsingleton.elim, injective, right_inv
-/
lemma subsingleton_dom [Subsingleton α] : Subsingleton E :=
⟨fun f g => DFunLike.ext f g fun _ => (right_inv f).injective Subsingleton.elim _ _⟩

end EquivLike
