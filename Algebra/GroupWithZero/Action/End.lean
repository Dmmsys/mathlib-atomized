/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Action.Hom
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Units

/-!
# Group actions and (endo)morphisms
-/

@[expose] public section

assert_not_exists RelIso Equiv.Perm.equivUnitsEnd Prod.fst_mul Ring

open Function

variable {M N A α β : Type*}

/-- Push forward the action of `R` on `M` along a compatible surjective map `f : R →* S`.

See also `Function.Surjective.mulActionLeft` and `Function.Surjective.moduleLeft`.
-/
/-
**Function.Surjective.distribMulActionLeft** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Function.Surjective.distribMulActionLeft {R S M : Type*} [Monoid R] [AddMo
noid M] [DistribMulAction R M] [Monoid S] [SMul S M] (f : R ->* S) (hf : Functio
n.Surjective f) (hsmul : forall (c) (x : M), f c • x = c • x) : DistribMulAction
 S M
参数：f : R ->* S；hf : Function.Surjective f；hsmul : forall (c) (x : M), f c • x = 
c • x。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.one_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Monoid α} [
self : MulAction α β] (b : β), 1 • b = b

--- 原说明 ---
Push forward the action of `R` on `M` along a compatible surjective map `f : R →
* S`.

See also `Function.Surjective.mulActionLeft` and `Function.Surjective.moduleLeft
`.
-/
abbrev Function.Surjective.distribMulActionLeft {R S M : Type*} [Monoid R] [AddMonoid M]
    [DistribMulAction R M] [Monoid S] [SMul S M] (f : R →* S) (hf : Function.Surjective f)
    (hsmul : ∀ (c) (x : M), f c • x = c • x) : DistribMulAction S M :=
  { hf.distribSMulLeft f hsmul, hf.mulActionLeft f hsmul with }

section AddMonoid

variable (A) [AddMonoid A] [Monoid M] [DistribMulAction M A]

/-- Compose a `DistribMulAction` with a `MonoidHom`, with action `f r' • m`.
See note [reducible non-instances]. -/
/-
**DistribMulAction.compHom** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：DistribMulAction.compHom [Monoid N] (f : N ->* M) : DistribMulAction N A
参数：f : N ->* M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.one_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Monoid α} [
self : MulAction α β] (b : β), 1 • b = b

--- 原说明 ---
Compose a `DistribMulAction` with a `MonoidHom`, with action `f r' • m`.
See note [reducible non-instances].
-/
abbrev DistribMulAction.compHom [Monoid N] (f : N →* M) : DistribMulAction N A :=
  { DistribSMul.compFun A f, MulAction.compHom A f with }

end AddMonoid

section Monoid

variable (A) [Monoid A] [Monoid M] [MulDistribMulAction M A]

/-- Compose a `MulDistribMulAction` with a `MonoidHom`, with action `f r' • m`.
See note [reducible non-instances]. -/
/-
**MulDistribMulAction.compHom** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：MulDistribMulAction.compHom [Monoid N] (f : N ->* M) : MulDistribMulAction
 N A
参数：f : N ->* M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Compose a `MulDistribMulAction` with a `MonoidHom`, with action `f r' • m`.
See note [reducible non-instances].
-/
abbrev MulDistribMulAction.compHom [Monoid N] (f : N →* M) : MulDistribMulAction N A :=
  { MulAction.compHom A f with
    smul_one := fun x => smul_one (f x),
    smul_mul := fun x => smul_mul' (f x) }

end Monoid

/-- The tautological action by `AddMonoid.End α` on `α`.

This generalizes `Function.End.applyMulAction`. -/
/-
**AddMonoid.End.applyDistribMulAction** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AddMonoid.End.applyDistribMulAction [AddMonoid α] : DistribMulAction (AddM
onoid.End α) α where smul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tautological action by `AddMonoid.End α` on `α`.

This generalizes `Function.End.applyMulAction`.
-/
instance AddMonoid.End.applyDistribMulAction [AddMonoid α] :
    DistribMulAction (AddMonoid.End α) α where
  smul := (· <| ·)
  smul_zero := map_zero
  smul_add := map_add
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]
/-
**AddMonoid.End.smul_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddMonoid.End.smul_def [AddMonoid α] (f : AddMonoid.End α) (a : α) : f • a
 = f a
参数：f : AddMonoid.End α；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AddMonoid.End.smul_def [AddMonoid α] (f : AddMonoid.End α) (a : α) : f • a = f a :=
  rfl

/-- `AddMonoid.End.applyDistribMulAction` is faithful. -/
/-
**AddMonoid.End.applyFaithfulSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AddMonoid.End.applyFaithfulSMul [AddMonoid α] : FaithfulSMul (AddMonoid.En
d α) α
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g

--- 原说明 ---
`AddMonoid.End.applyDistribMulAction` is faithful.
-/
instance AddMonoid.End.applyFaithfulSMul [AddMonoid α] :
    FaithfulSMul (AddMonoid.End α) α :=
  ⟨fun {_ _ h} => AddMonoidHom.ext h⟩

/-- Each non-zero element of a `GroupWithZero` defines an additive monoid isomorphism of an
`AddMonoid` on which it acts distributively.
This is a stronger version of `DistribSMul.toAddMonoidHom`. -/
/-
**DistribMulAction.toAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：DistribMulAction.toAddEquiv [DistribMulAction G A] (x : G) : A ≃+ A where 
__
参数：x : G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun

--- 原说明 ---
Each non-zero element of a `GroupWithZero` defines an additive monoid isomorphis
m of an
`AddMonoid` on which it acts distributively.
This is a stronger version of `DistribSMul.toAddMonoidHom`.
-/
def DistribMulAction.toAddEquiv₀ {α : Type*} (β : Type*) [GroupWithZero α] [AddMonoid β]
    [DistribMulAction α β] (x : α) (hx : x ≠ 0) : β ≃+ β :=
  { DistribSMul.toAddMonoidHom β x with
    invFun := fun b ↦ x⁻¹ • b
    left_inv := fun b ↦ inv_smul_smul₀ hx b
    right_inv := fun b ↦ smul_inv_smul₀ hx b }
