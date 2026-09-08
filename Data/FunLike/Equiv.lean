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

/-- Copy of a `MyIso` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : MyIso A B) (f' : A → B) (f_inv : B → A)
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
/-- `MyIsoClass F A B` states that `F` is a type of `MyClass.op`-preserving morphisms.
You should extend this class when you extend `MyIso`. -/
class MyIsoClass (F : Type*) (A B : outParam Type*) [MyClass A] [MyClass B]
    [EquivLike F A B]
    extends MyHomClass F A B

namespace MyIso

variable {A B : Type*} [MyClass A] [MyClass B]

-- This goes after `MyIsoClass.instEquivLike`:
instance : MyIsoClass (MyIso A B) A B where
  map_op := MyIso.map_op'

-- [Insert `ext` and `copy` here]

end MyIso
```

The second step is to add instances of your new `MyIsoClass` for all types extending `MyIso`.
Typically, you can just declare a new class analogous to `MyIsoClass`:

```
structure CoolerIso (A B : Type*) [CoolClass A] [CoolClass B] extends MyIso A B where
  (map_cool' : toFun CoolClass.cool = CoolClass.cool)

class CoolerIsoClass (F : Type*) (A B : outParam Type*) [CoolClass A] [CoolClass B]
    [EquivLike F A B]
    extends MyIsoClass F A B where
  (map_cool : ∀ (f : F), f CoolClass.cool = CoolClass.cool)

@[simp] lemma map_cool {F A B : Type*} [CoolClass A] [CoolClass B]
    [EquivLike F A B] [CoolerIsoClass F A B] (f : F) :
    f CoolClass.cool = CoolClass.cool :=
  CoolerIsoClass.map_cool _

namespace CoolerIso

variable {A B : Type*} [CoolClass A] [CoolClass B]

instance : EquivLike (CoolerIso A B) A B where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by cases f; cases g; congr; exact EquivLike.coe_injective' _ _ h₁ h₂

instance : CoolerIsoClass (CoolerIso A B) A B where
  map_op f := f.map_op'
  map_cool f := f.map_cool'

-- [Insert `ext` and `copy` here]

end CoolerIso
```

Then any declaration taking a specific type of morphisms as parameter can instead take the
class you just defined:
```
-- Compare with: lemma do_something (f : MyIso A B) : sorry := sorry
lemma do_something {F : Type*} [EquivLike F A B] [MyIsoClass F A B] (f : F) : sorry := sorry
```

This means anything set up for `MyIso`s will automatically work for `CoolerIsoClass`es,
and defining `CoolerIsoClass` only takes a constant amount of effort,
instead of linearly increasing the work per `MyIso`-related declaration.

-/

@[expose] public section


/-- The class `EquivLike E α β` expresses that terms of type `E` have an
injective coercion to bijections between `α` and `β`.

Note that this does not directly extend `FunLike`, nor take `FunLike` as a parameter,
so we can state `coe_injective'` in a nicer way.

This typeclass is used in the definition of the isomorphism (or equivalence) typeclasses,
such as `ZeroEquivClass`, `MulEquivClass`, `MonoidEquivClass`, ....
-/
/-
**EquivLike** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Sort u_1 → outParam (Sort u_2) → outParam (Sort u_3) → Sort (max (max (max
 1 u_1) u_2) u_3)
参数：Sort u_2；Sort u_3；max (max (max 1 u_1) u_2) u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The class `EquivLike E α β` expresses that terms of type `E` have an
injective coercion to bijections between `α` and `β`.

Note that this does not directly extend `FunLike`, nor take `FunLike` as a param
eter,
so we can state `coe_injective'` in a nicer way.

This typeclass is used in the definition of the isomorphism (or equivalence) typ
eclasses,
such as `ZeroEquivClass`, `MulEquivClass`, `MonoidEquivClass`, ....
-/
class EquivLike (E : Sort*) (α β : outParam (Sort*)) where
  /-- The coercion to a function in the forward direction. -/
  coe : E → α → β
  /-- The coercion to a function in the backwards direction. -/
  inv : E → β → α
  /-- The coercions are left inverses. -/
  left_inv : ∀ e, Function.LeftInverse (inv e) (coe e)
  /-- The coercions are right inverses. -/
  right_inv : ∀ e, Function.RightInverse (inv e) (coe e)
  /-- The two coercions to functions are jointly injective. -/
  coe_injective' : ∀ e g, coe e = coe g → inv e = inv g → e = g
  -- This is mathematically equivalent to either of the coercions to functions being injective, but
  -- the `inv` hypothesis makes this easier to prove with `congr'`

namespace EquivLike

variable {E F α β γ : Sort*} [EquivLike E α β] [EquivLike F β γ]

/-
**EquivLike.inv_injective** 是 Mathlib 中的一个定理，位于命名空间 `EquivLike`。
形式化陈述：inv_injective : Function.Injective (EquivLike.inv : E -> β -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquivLike.coe_injective'`：∀ {E : Sort u_1} {α : outParam (Sort u_2)} {β 
: outParam (Sort u_3)} [self : EquivLike E α β] (e g : E),   EquivLike.coe e = E
quivLike.coe g…
· 使用定理 `Function.LeftInverse.eq_rightInverse`：∀ {α : Sort u_1} {β : Sort u_2} {f
 : α → β} {g₁ g₂ : β → α},   Function.LeftInverse g₁ f → Function.RightInverse g
₂ f → g₁ = g₂
· 使用定理 `EquivLike.right_inv`：∀ {E : Sort u_1} {α : outParam (Sort u_2)} {β : out
Param (Sort u_3)} [self : EquivLike E α β] (e : E),   Function.RightInverse (Equ
ivLike.in…
· 使用定理 `EquivLike.left_inv`：∀ {E : Sort u_1} {α : outParam (Sort u_2)} {β : outP
aram (Sort u_3)} [self : EquivLike E α β] (e : E),   Function.LeftInverse (Equiv
Like.inv…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem inv_injective : Function.Injective (EquivLike.inv : E → β → α) := fun e g h ↦
  coe_injective' e g ((right_inv e).eq_rightInverse (h.symm ▸ left_inv g)) h
/-
**EquivLike.** 是 Mathlib 中的一个实例，位于命名空间 `EquivLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) toFunLike : FunLike E α β where
  coe := (coe : E → α → β)
  coe_injective e g h :=
    coe_injective' e g h ((left_inv e).eq_rightInverse (h.symm ▸ right_inv g))
/-
**EquivLike.coe_apply** 是 Mathlib 中的一个定理，位于命名空间 `EquivLike`。
形式化陈述：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [inst : EquivLike E α β] {e
 : E} {a : α}, EquivLike.coe e a = e a
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_apply {e : E} {a : α} : coe e a = e a := rfl
/-
**EquivLike.inv_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `EquivLike`。
形式化陈述：inv_apply_eq {e : E} {b : β} {a : α} : inv e b = a ↔ b = e a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EquivLike.right_inv`：∀ {E : Sort u_1} {α : outParam (Sort u_2)} {β : out
Param (Sort u_3)} [self : EquivLike E α β] (e : E),   Function.RightInverse (Equ
ivLike.in…
· 使用定理 `EquivLike.left_inv`：∀ {E : Sort u_1} {α : outParam (Sort u_2)} {β : outP
aram (Sort u_3)} [self : EquivLike E α β] (e : E),   Function.LeftInverse (Equiv
Like.inv…
-/
theorem inv_apply_eq {e : E} {b : β} {a : α} : inv e b = a ↔ b = e a := by
  constructor <;> rintro ⟨_, rfl⟩
  exacts [(right_inv e b).symm, left_inv e a]
/-
**EquivLike.** 是 Mathlib 中的一个实例，位于命名空间 `EquivLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) toEmbeddingLike : EmbeddingLike E α β where
  injective' e := (left_inv e).injective
/-
**EquivLike.injective** 是 Mathlib 中的一个定理，位于命名空间 `EquivLike`。
形式化陈述：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [inst : EquivLike E α β] (e
 : E), Function.Injective ⇑e
参数：e : E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EmbeddingLike.injective`：∀ {F : Sort u_1} {α : Sort u_2} {β : Sort u_3} 
[inst : FunLike F α β] [i : EmbeddingLike F α β] (f : F),   Function.Injective ⇑
f
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
-/
protected theorem injective (e : E) : Function.Injective e :=
  EmbeddingLike.injective e
/-
**EquivLike.surjective** 是 Mathlib 中的一个定理，位于命名空间 `EquivLike`。
形式化陈述：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [inst : EquivLike E α β] (e
 : E), Function.Surjective ⇑e
参数：e : E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.RightInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} {g : β → α}, Function.RightInverse g f → Function.Surjective f
· 使用定理 `EquivLike.right_inv`：∀ {E : Sort u_1} {α : outParam (Sort u_2)} {β : out
Param (Sort u_3)} [self : EquivLike E α β] (e : E),   Function.RightInverse (Equ
ivLike.in…
-/
protected theorem surjective (e : E) : Function.Surjective e :=
  (right_inv e).surjective
/-
**EquivLike.bijective** 是 Mathlib 中的一个定理，位于命名空间 `EquivLike`。
形式化陈述：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [inst : EquivLike E α β] (e
 : E), Function.Bijective ⇑e
参数：e : E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquivLike.injective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [ins
t : EquivLike E α β] (e : E), Function.Injective ⇑e
· 使用定理 `EquivLike.surjective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [in
st : EquivLike E α β] (e : E), Function.Surjective ⇑e
-/
protected theorem bijective (e : E) : Function.Bijective (e : α → β) :=
  ⟨EquivLike.injective e, EquivLike.surjective e⟩
/-
**EquivLike.apply_eq_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `EquivLike`。
形式化陈述：apply_eq_iff_eq (f : E) {x y : α} : f x = f y ↔ x = y
参数：f : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EmbeddingLike.apply_eq_iff_eq`：apply_eq_iff_eq (f : F) {x y : α} : f x =
 f y ↔ x = y
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
-/
theorem apply_eq_iff_eq (f : E) {x y : α} : f x = f y ↔ x = y :=
  EmbeddingLike.apply_eq_iff_eq f

@[simp]
/-
**EquivLike.injective_comp** 是 Mathlib 中的一个定理，位于命名空间 `EquivLike`。
形式化陈述：injective_comp (e : E) (f : β -> γ) : Function.Injective (f ∘ e) ↔ Functio
n.Injective f
参数：e : E；f : β -> γ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} (f : α → β) {g : γ → α},   Function.Bijective g → (Function.Injective (f
 ∘ g) ↔ Function.Inje…
· 使用定理 `EquivLike.bijective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [ins
t : EquivLike E α β] (e : E), Function.Bijective ⇑e
-/
theorem injective_comp (e : E) (f : β → γ) : Function.Injective (f ∘ e) ↔ Function.Injective f :=
  Function.Injective.of_comp_iff' f (EquivLike.bijective e)

@[simp]
/-
**EquivLike.surjective_comp** 是 Mathlib 中的一个定理，位于命名空间 `EquivLike`。
形式化陈述：surjective_comp (e : E) (f : β -> γ) : Function.Surjective (f ∘ e) ↔ Funct
ion.Surjective f
参数：e : E；f : β -> γ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.of_comp_iff`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} (f : α → β) {g : γ → α},   Function.Surjective g → (Function.Surjective 
(f ∘ g) ↔ Function.Su…
· 使用定理 `EquivLike.surjective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [in
st : EquivLike E α β] (e : E), Function.Surjective ⇑e
-/
theorem surjective_comp (e : E) (f : β → γ) : Function.Surjective (f ∘ e) ↔ Function.Surjective f :=
  (EquivLike.surjective e).of_comp_iff f

@[simp]
/-
**EquivLike.bijective_comp** 是 Mathlib 中的一个定理，位于命名空间 `EquivLike`。
形式化陈述：bijective_comp (e : E) (f : β -> γ) : Function.Bijective (f ∘ e) ↔ Functio
n.Bijective f
参数：e : E；f : β -> γ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.of_comp_iff`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} (f : α → β) {g : γ → α},   Function.Bijective g → (Function.Bijective (f 
∘ g) ↔ Function.Bije…
· 使用定理 `EquivLike.bijective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [ins
t : EquivLike E α β] (e : E), Function.Bijective ⇑e
-/
theorem bijective_comp (e : E) (f : β → γ) : Function.Bijective (f ∘ e) ↔ Function.Bijective f :=
  (EquivLike.bijective e).of_comp_iff f

/-- This lemma is only supposed to be used in the generic context, when working with instances
of classes extending `EquivLike`.
For concrete isomorphism types such as `Equiv`, you should use `Equiv.symm_apply_apply`
or its equivalent.

TODO: define a generic form of `Equiv.symm`. -/
@[simp]
/-
**EquivLike.inv_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `EquivLike`。
形式化陈述：inv_apply_apply (e : E) (a : α) : inv e (e a) = a
参数：e : E；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquivLike.left_inv`：∀ {E : Sort u_1} {α : outParam (Sort u_2)} {β : outP
aram (Sort u_3)} [self : EquivLike E α β] (e : E),   Function.LeftInverse (Equiv
Like.inv…

--- 原说明 ---
This lemma is only supposed to be used in the generic context, when working with
 instances
of classes extending `EquivLike`.
For concrete isomorphism types such as `Equiv`, you should use `Equiv.symm_apply
_apply`
or its equivalent.

TODO: define a generic form of `Equiv.symm`.
-/
theorem inv_apply_apply (e : E) (a : α) : inv e (e a) = a := left_inv _ _

/-- This lemma is only supposed to be used in the generic context, when working with instances
of classes extending `EquivLike`.
For concrete isomorphism types such as `Equiv`, you should use `Equiv.apply_symm_apply`
or its equivalent.

TODO: define a generic form of `Equiv.symm`. -/
@[simp]
/-
**EquivLike.apply_inv_apply** 是 Mathlib 中的一个定理，位于命名空间 `EquivLike`。
形式化陈述：apply_inv_apply (e : E) (b : β) : e (inv e b) = b
参数：e : E；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquivLike.right_inv`：∀ {E : Sort u_1} {α : outParam (Sort u_2)} {β : out
Param (Sort u_3)} [self : EquivLike E α β] (e : E),   Function.RightInverse (Equ
ivLike.in…

--- 原说明 ---
This lemma is only supposed to be used in the generic context, when working with
 instances
of classes extending `EquivLike`.
For concrete isomorphism types such as `Equiv`, you should use `Equiv.apply_symm
_apply`
or its equivalent.

TODO: define a generic form of `Equiv.symm`.
-/
theorem apply_inv_apply (e : E) (b : β) : e (inv e b) = b := right_inv _ _
/-
**EquivLike.comp_injective** 是 Mathlib 中的一个定理，位于命名空间 `EquivLike`。
形式化陈述：comp_injective (f : α -> β) (e : F) : Function.Injective (e ∘ f) ↔ Functio
n.Injective f
参数：f : α -> β；e : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EmbeddingLike.comp_injective`：comp_injective {F : Sort*} [FunLike F β γ]
 [EmbeddingLike F β γ] (f : α -> β) (e : F) : Function.Injective (e ∘ f) ↔ Funct
ion.Injective f
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
-/
theorem comp_injective (f : α → β) (e : F) : Function.Injective (e ∘ f) ↔ Function.Injective f :=
  EmbeddingLike.comp_injective f e

@[simp]
/-
**EquivLike.comp_surjective** 是 Mathlib 中的一个定理，位于命名空间 `EquivLike`。
形式化陈述：comp_surjective (f : α -> β) (e : F) : Function.Surjective (e ∘ f) ↔ Funct
ion.Surjective f
参数：f : α -> β；e : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.of_comp_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {γ : S
ort u_3} {f : α → β},   Function.Bijective f → ∀ (g : γ → α), Function.Surjectiv
e (f ∘ g) ↔ Function.S…
· 使用定理 `EquivLike.bijective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [ins
t : EquivLike E α β] (e : E), Function.Bijective ⇑e
-/
theorem comp_surjective (f : α → β) (e : F) : Function.Surjective (e ∘ f) ↔ Function.Surjective f :=
  Function.Surjective.of_comp_iff' (EquivLike.bijective e) f

@[simp]
/-
**EquivLike.comp_bijective** 是 Mathlib 中的一个定理，位于命名空间 `EquivLike`。
形式化陈述：comp_bijective (f : α -> β) (e : F) : Function.Bijective (e ∘ f) ↔ Functio
n.Bijective f
参数：f : α -> β；e : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.of_comp_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Bijective f → ∀ (g : γ → α), Function.Bijective 
(f ∘ g) ↔ Function.Bi…
· 使用定理 `EquivLike.bijective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [ins
t : EquivLike E α β] (e : E), Function.Bijective ⇑e
-/
theorem comp_bijective (f : α → β) (e : F) : Function.Bijective (e ∘ f) ↔ Function.Bijective f :=
  (EquivLike.bijective e).of_comp_iff' f

include β in
/-- This is not an instance to avoid slowing down every single `Subsingleton` typeclass search. -/
/-
**EquivLike.subsingleton_dom** 是 Mathlib 中的一个引理，位于命名空间 `EquivLike`。
形式化陈述：subsingleton_dom [Subsingleton α] : Subsingleton E
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `Function.RightInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β} {g : β → α}, Function.RightInverse f g → Function.Injective f
· 使用定理 `EquivLike.right_inv`：∀ {E : Sort u_1} {α : outParam (Sort u_2)} {β : out
Param (Sort u_3)} [self : EquivLike E α β] (e : E),   Function.RightInverse (Equ
ivLike.in…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b

--- 原说明 ---
This is not an instance to avoid slowing down every single `Subsingleton` typecl
ass search.
-/
lemma subsingleton_dom [Subsingleton α] : Subsingleton E :=
  ⟨fun f g ↦ DFunLike.ext f g fun _ ↦ (right_inv f).injective <| Subsingleton.elim _ _⟩

end EquivLike

