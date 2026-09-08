/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis, Heather Macbeth
-/
module

public import Mathlib.Algebra.Ring.Equiv

/-!
# Propositional typeclasses on several ring homs

This file contains three typeclasses used in the definition of (semi)linear maps:
* `RingHomId σ`, which expresses the fact that `σ₂₃ = id`
* `RingHomCompTriple σ₁₂ σ₂₃ σ₁₃`, which expresses the fact that `σ₂₃.comp σ₁₂ = σ₁₃`
* `RingHomInvPair σ₁₂ σ₂₁`, which states that `σ₁₂` and `σ₂₁` are inverses of each other
* `RingHomSurjective σ`, which states that `σ` is surjective

These typeclasses ensure that objects such as `σ₂₃.comp σ₁₂` never end up in the type of a
semilinear map; instead, the typeclass system directly finds the appropriate `RingHom` to use.
A typical use-case is conjugate-linear maps, i.e. when `σ = Complex.conj`; this system ensures that
composing two conjugate-linear maps is a linear map, and not a `conj.comp conj`-linear map.

Instances of these typeclasses mostly involving `RingHom.id` are also provided:
* `RingHomInvPair (RingHom.id R) (RingHom.id R)`
* `[RingHomInvPair σ₁₂ σ₂₁] : RingHomCompTriple σ₁₂ σ₂₁ (RingHom.id R₁)`
* `RingHomCompTriple (RingHom.id R₁) σ₁₂ σ₁₂`
* `RingHomCompTriple σ₁₂ (RingHom.id R₂) σ₁₂`
* `RingHomSurjective (RingHom.id R)`
* `[RingHomInvPair σ₁ σ₂] : RingHomSurjective σ₁`

## Implementation notes

* For the typeclass `RingHomInvPair σ₁₂ σ₂₁`, `σ₂₁` is marked as an `outParam`,
  as it must typically be found via the typeclass inference system.

* Likewise, for `RingHomCompTriple σ₁₂ σ₂₃ σ₁₃`, `σ₁₃` is marked as an `outParam`,
  for the same reason.

## Tags

`RingHomCompTriple`, `RingHomInvPair`, `RingHomSurjective`
-/

@[expose] public section


variable {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}
variable [Semiring R₁] [Semiring R₂] [Semiring R₃]

/-- Class that expresses that a ring homomorphism is in fact the identity. -/
-- This at first seems not very useful. However we need this when considering
-- modules over some diagram in the category of rings,
-- e.g. when defining presheaves over a presheaf of rings.
-- See `Mathlib/Algebra/Category/ModuleCat/Presheaf.lean`.
/-
**RingHomId** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{R : Type u_4} → [inst : Semiring R] → (R →+* R) → Prop
参数：R →+* R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
class RingHomId {R : Type*} [Semiring R] (σ : R →+* R) : Prop where
  eq_id : σ = RingHom.id R
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : Type*} [Semiring R] : RingHomId (RingHom.id R) where
  eq_id := rfl

/-- Class that expresses the fact that three ring homomorphisms form a composition triple. This is
used to handle composition of semilinear maps. -/
/-
**RingHomCompTriple** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{R₁ : Type u_1} →   {R₂ : Type u_2} →     {R₃ : Type u_3} →       [inst : 
Semiring R₁] →         [inst_1 : Semiring R₂] → [inst_2 : Semiring R₃] → (R₁ →+*
 R₂) → (R₂ →+* R₃) → outParam (R₁ →+* R₃) → Prop
参数：R₁ →+* R₂；R₂ →+* R₃；R₁ →+* R₃。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Class that expresses the fact that three ring homomorphisms form a composition t
riple. This is
used to handle composition of semilinear maps.
-/
class RingHomCompTriple (σ₁₂ : R₁ →+* R₂) (σ₂₃ : R₂ →+* R₃) (σ₁₃ : outParam (R₁ →+* R₃)) :
  Prop where
  /-- The morphisms form a commutative triangle -/
  comp_eq : σ₂₃.comp σ₁₂ = σ₁₃

attribute [simp] RingHomCompTriple.comp_eq

variable {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃}

namespace RingHomCompTriple

@[simp]
/-
**RingHomCompTriple.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `RingHomCompTriple`。
形式化陈述：comp_apply [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] {x : R₁} : σ₂₃ (σ₁₂ x) = σ₁₃ x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.congr_fun`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring
 α} {x_1 : NonAssocSemiring β} {f g : α →+* β},   f = g → ∀ (x_2 : α), f x_2 = g
 x_2
· 使用定理 `RingHomCompTriple.comp_eq`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {R₃ : Type 
u_3} {inst : Semiring R₁} {inst_1 : Semiring R₂} {inst_2 : Semiring R₃}   {σ₁₂ :
 R₁ →+* R₂} {σ₂…
-/
theorem comp_apply [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] {x : R₁} : σ₂₃ (σ₁₂ x) = σ₁₃ x :=
  RingHom.congr_fun comp_eq x

end RingHomCompTriple

/-- Class that expresses the fact that two ring homomorphisms are inverses of each other. This is
used to handle `symm` for semilinear equivalences. -/
/-
**RingHomInvPair** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{R₁ : Type u_1} →   {R₂ : Type u_2} → [inst : Semiring R₁] → [inst_1 : Sem
iring R₂] → (R₁ →+* R₂) → outParam (R₂ →+* R₁) → Prop
参数：R₁ →+* R₂；R₂ →+* R₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Class that expresses the fact that two ring homomorphisms are inverses of each o
ther. This is
used to handle `symm` for semilinear equivalences.
-/
class RingHomInvPair (σ : R₁ →+* R₂) (σ' : outParam (R₂ →+* R₁)) : Prop where
  /-- `σ'` is a left inverse of `σ` -/
  comp_eq : σ'.comp σ = RingHom.id R₁
  /-- `σ'` is a left inverse of `σ'` -/
  comp_eq₂ : σ.comp σ' = RingHom.id R₂

variable {σ : R₁ →+* R₂} {σ' : R₂ →+* R₁}

namespace RingHomInvPair

variable [RingHomInvPair σ σ']

/-
**RingHomInvPair.comp_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `RingHomInvPair`。
形式化陈述：comp_apply_eq {x : R₁} : σ' (σ x) = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.comp_apply`：comp_apply (hnp : β ->+* γ) (hmn : α ->+* β) (x : α)
 : (hnp.comp hmn : α -> γ) x = hnp (hmn x)
· 使用定理 `RingHomInvPair.comp_eq`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {inst : Semiri
ng R₁} {inst_1 : Semiring R₂} {σ : R₁ →+* R₂}   {σ' : outParam (R₂ →+* R₁)} [sel
f : RingHomI…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_apply_eq {x : R₁} : σ' (σ x) = x := by
  rw [← RingHom.comp_apply, comp_eq]
  simp
/-
**RingHomInvPair.comp_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `RingHomInvPair`。
形式化陈述：comp_apply_eq {x : R₁} : σ' (σ x) = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.comp_apply`：comp_apply (hnp : β ->+* γ) (hmn : α ->+* β) (x : α)
 : (hnp.comp hmn : α -> γ) x = hnp (hmn x)
· 使用定理 `RingHomInvPair.comp_eq`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {inst : Semiri
ng R₁} {inst_1 : Semiring R₂} {σ : R₁ →+* R₂}   {σ' : outParam (R₂ →+* R₁)} [sel
f : RingHomI…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_apply_eq₂ {x : R₂} : σ (σ' x) = x := by
  rw [← RingHom.comp_apply, comp_eq₂]
  simp
/-
**RingHomInvPair.ids** 是 Mathlib 中的一个实例，位于命名空间 `RingHomInvPair`。
形式化陈述：ids : RingHomInvPair (RingHom.id R₁) (RingHom.id R₁)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ids : RingHomInvPair (RingHom.id R₁) (RingHom.id R₁) :=
  ⟨rfl, rfl⟩
/-
**RingHomInvPair.triples** 是 Mathlib 中的一个实例，位于命名空间 `RingHomInvPair`。
形式化陈述：triples {σ₂₁ : R₂ ->+* R₁} [RingHomInvPair σ₁₂ σ₂₁] : RingHomCompTriple σ₁
₂ σ₂₁ (RingHom.id R₁)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHomInvPair.comp_eq`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {inst : Semiri
ng R₁} {inst_1 : Semiring R₂} {σ : R₁ →+* R₂}   {σ' : outParam (R₂ →+* R₁)} [sel
f : RingHomI…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance triples {σ₂₁ : R₂ →+* R₁} [RingHomInvPair σ₁₂ σ₂₁] :
    RingHomCompTriple σ₁₂ σ₂₁ (RingHom.id R₁) :=
  ⟨by simp only [comp_eq]⟩
/-
**RingHomInvPair.triples** 是 Mathlib 中的一个实例，位于命名空间 `RingHomInvPair`。
形式化陈述：triples {σ₂₁ : R₂ ->+* R₁} [RingHomInvPair σ₁₂ σ₂₁] : RingHomCompTriple σ₁
₂ σ₂₁ (RingHom.id R₁)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHomInvPair.comp_eq`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {inst : Semiri
ng R₁} {inst_1 : Semiring R₂} {σ : R₁ →+* R₂}   {σ' : outParam (R₂ →+* R₁)} [sel
f : RingHomI…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance triples₂ {σ₂₁ : R₂ →+* R₁} [RingHomInvPair σ₁₂ σ₂₁] :
    RingHomCompTriple σ₂₁ σ₁₂ (RingHom.id R₂) :=
  ⟨by simp only [comp_eq₂]⟩

variable (σ σ') in
/-- The ring equivalence defined by a pair of ring homomorphisms satisfying `RingHomInvPair`. -/
@[simps!]
/-
**RingHomInvPair.toRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `RingHomInvPair`。
形式化陈述：toRingEquiv : R₁ ≃+* R₂
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.comp_eq₂`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {inst : Semir
ing R₁} {inst_1 : Semiring R₂} {σ : R₁ →+* R₂}   {σ' : outParam (R₂ →+* R₁)} [se
lf : RingHomI…
· 使用定理 `RingHomInvPair.comp_eq`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {inst : Semiri
ng R₁} {inst_1 : Semiring R₂} {σ : R₁ →+* R₂}   {σ' : outParam (R₂ →+* R₁)} [sel
f : RingHomI…

--- 原说明 ---
The ring equivalence defined by a pair of ring homomorphisms satisfying `RingHom
InvPair`.
-/
def toRingEquiv : R₁ ≃+* R₂ := .ofRingHom σ σ' comp_eq₂ comp_eq

/-- Construct a `RingHomInvPair` from both directions of a ring equiv.

This is not an instance, as for equivalences that are involutions, a better instance
would be `RingHomInvPair e e`.
-/
/-
**RingHomInvPair.of_ringEquiv** 是 Mathlib 中的一个引理，位于命名空间 `RingHomInvPair`。
形式化陈述：of_ringEquiv (e : R₁ ≃+* R₂) : RingHomInvPair (↑e : R₁ ->+* R₂) ↑e.symm
参数：e : R₁ ≃+* R₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `RingEquiv.symm_toRingHom_comp_toRingHom`：symm_toRingHom_comp_toRingHom (
e : R ≃+* S) : e.symm.toRingHom.comp e.toRingHom = RingHom.id _

--- 原说明 ---
Construct a `RingHomInvPair` from both directions of a ring equiv.

This is not an instance, as for equivalences that are involutions, a better inst
ance
would be `RingHomInvPair e e`.
-/
lemma of_ringEquiv (e : R₁ ≃+* R₂) : RingHomInvPair (↑e : R₁ →+* R₂) ↑e.symm :=
  ⟨e.symm_toRingHom_comp_toRingHom, e.symm.symm_toRingHom_comp_toRingHom⟩

/-- Construct a `RingHomInvPair` from both directions of a ring equiv.

This is not an instance, as for equivalences that are involutions, a better instance
would be `RingHomInvPair e e`.
-/
/-
**RingHomInvPair.of_ringEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `RingHomInvPair`。
形式化陈述：of_ringEquiv_symm (e : R₁ ≃+* R₂) : RingHomInvPair (↑e.symm : R₂ ->+* R₁) 
↑e
参数：e : R₁ ≃+* R₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RingHomInvPair.of_ringEquiv`：of_ringEquiv (e : R₁ ≃+* R₂) : RingHomInvPa
ir (↑e : R₁ ->+* R₂) ↑e.symm

--- 原说明 ---
Construct a `RingHomInvPair` from both directions of a ring equiv.

This is not an instance, as for equivalences that are involutions, a better inst
ance
would be `RingHomInvPair e e`.
-/
theorem of_ringEquiv_symm (e : R₁ ≃+* R₂) : RingHomInvPair (↑e.symm : R₂ →+* R₁) ↑e :=
  of_ringEquiv e.symm

/--
Swap the direction of a `RingHomInvPair`. This is not an instance as it would loop, and better
instances are often available and may often be preferable to using this one. Indeed, this
declaration is not currently used in mathlib.
-/
/-
**RingHomInvPair.symm** 是 Mathlib 中的一个定理，位于命名空间 `RingHomInvPair`。
形式化陈述：symm (σ₁₂ : R₁ ->+* R₂) (σ₂₁ : R₂ ->+* R₁) [RingHomInvPair σ₁₂ σ₂₁] : Ring
HomInvPair σ₂₁ σ₁₂
参数：σ₁₂ : R₁ ->+* R₂；σ₂₁ : R₂ ->+* R₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.comp_eq₂`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {inst : Semir
ing R₁} {inst_1 : Semiring R₂} {σ : R₁ →+* R₂}   {σ' : outParam (R₂ →+* R₁)} [se
lf : RingHomI…
· 使用定理 `RingHomInvPair.comp_eq`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {inst : Semiri
ng R₁} {inst_1 : Semiring R₂} {σ : R₁ →+* R₂}   {σ' : outParam (R₂ →+* R₁)} [sel
f : RingHomI…

--- 原说明 ---
Swap the direction of a `RingHomInvPair`. This is not an instance as it would lo
op, and better
instances are often available and may often be preferable to using this one. Ind
eed, this
declaration is not currently used in mathlib.
-/
theorem symm (σ₁₂ : R₁ →+* R₂) (σ₂₁ : R₂ →+* R₁) [RingHomInvPair σ₁₂ σ₂₁] :
    RingHomInvPair σ₂₁ σ₁₂ :=
  ⟨RingHomInvPair.comp_eq₂, RingHomInvPair.comp_eq⟩

end RingHomInvPair

namespace RingHomCompTriple

/-
**RingHomCompTriple.ids** 是 Mathlib 中的一个实例，位于命名空间 `RingHomCompTriple`。
形式化陈述：ids : RingHomCompTriple (RingHom.id R₁) σ₁₂ σ₁₂
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.comp_id`：comp_id (f : α ->+* β) : f.comp (id α) = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance ids : RingHomCompTriple (RingHom.id R₁) σ₁₂ σ₁₂ :=
  ⟨by
    simp⟩
/-
**RingHomCompTriple.right_ids** 是 Mathlib 中的一个实例，位于命名空间 `RingHomCompTriple`。
形式化陈述：right_ids : RingHomCompTriple σ₁₂ (RingHom.id R₂) σ₁₂
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.id_comp`：id_comp (f : α ->+* β) : (id β).comp f = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance right_ids : RingHomCompTriple σ₁₂ (RingHom.id R₂) σ₁₂ :=
  ⟨by
    simp⟩

end RingHomCompTriple

/-- Class expressing the fact that a `RingHom` is surjective. This is needed in the context
of semilinear maps, where some lemmas require this. -/
/-
**RingHomSurjective** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{R₁ : Type u_1} → {R₂ : Type u_2} → [inst : Semiring R₁] → [inst_1 : Semir
ing R₂] → (R₁ →+* R₂) → Prop
参数：R₁ →+* R₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Class expressing the fact that a `RingHom` is surjective. This is needed in the 
context
of semilinear maps, where some lemmas require this.
-/
class RingHomSurjective (σ : R₁ →+* R₂) : Prop where
  /-- The ring homomorphism is surjective -/
  is_surjective : Function.Surjective σ
/-
**RingHom.surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.surjective (σ : R₁ ->+* R₂) [t : RingHomSurjective σ] : Function.S
urjective σ
参数：σ : R₁ ->+* R₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.is_surjective`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {inst
 : Semiring R₁} {inst_1 : Semiring R₂} {σ : R₁ →+* R₂}   [self : RingHomSurjecti
ve σ], Function.Surje…
-/
theorem RingHom.surjective (σ : R₁ →+* R₂) [t : RingHomSurjective σ] : Function.Surjective σ :=
  t.is_surjective

namespace RingHomSurjective

/-
**RingHomSurjective.** 是 Mathlib 中的一个实例，位于命名空间 `RingHomSurjective`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) invPair {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁} [RingHomInvPair σ₁ σ₂] :
    RingHomSurjective σ₁ :=
  ⟨fun x => ⟨σ₂ x, RingHomInvPair.comp_apply_eq₂⟩⟩
/-
**RingHomSurjective.ids** 是 Mathlib 中的一个实例，位于命名空间 `RingHomSurjective`。
形式化陈述：ids : RingHomSurjective (RingHom.id R₁)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.is_surjective`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {inst
 : Semiring R₁} {inst_1 : Semiring R₂} {σ : R₁ →+* R₂}   [self : RingHomSurjecti
ve σ], Function.Surje…
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
-/
instance ids : RingHomSurjective (RingHom.id R₁) :=
  ⟨is_surjective⟩

/-- This cannot be an instance as there is no way to infer `σ₁₂` and `σ₂₃`. -/
/-
**RingHomSurjective.comp** 是 Mathlib 中的一个定理，位于命名空间 `RingHomSurjective`。
形式化陈述：comp [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomSurjective σ₁₂] [RingHomSurje
ctive σ₂₃] : RingHomSurjective σ₁₃
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `RingHom.surjective`：RingHom.surjective (σ : R₁ ->+* R₂) [t : RingHomSurj
ective σ] : Function.Surjective σ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHomCompTriple.comp_eq`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {R₃ : Type 
u_3} {inst : Semiring R₁} {inst_1 : Semiring R₂} {inst_2 : Semiring R₃}   {σ₁₂ :
 R₁ →+* R₂} {σ₂…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.coe_comp`：coe_comp (hnp : β ->+* γ) (hmn : α ->+* β) : (hnp.comp
 hmn : α -> γ) = hnp ∘ hmn

--- 原说明 ---
This cannot be an instance as there is no way to infer `σ₁₂` and `σ₂₃`.
-/
theorem comp [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomSurjective σ₁₂] [RingHomSurjective σ₂₃] :
    RingHomSurjective σ₁₃ :=
  { is_surjective := by
      have := σ₂₃.surjective.comp σ₁₂.surjective
      rwa [← RingHom.coe_comp, RingHomCompTriple.comp_eq] at this }
/-
**RingHomSurjective.** 是 Mathlib 中的一个实例，位于命名空间 `RingHomSurjective`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (σ : R₁ ≃+* R₂) : RingHomSurjective (σ : R₁ →+* R₂) := ⟨σ.surjective⟩

end RingHomSurjective

