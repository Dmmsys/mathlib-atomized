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

/--
Definition of `Function.Surjective.distribMulActionLeft` / `Function.Surjective.distribMulActionLeft` 的定义

English:
abbreviation Function.Surjective.distribMulActionLeft
  signature: {R S M : Type*} [Monoid R] [AddMonoid M]
  body: { hf.distribSMulLeft f hsmul, hf.mulActionLeft f hsmul with }

中文:
缩写 函数.满射.distribMulActionLeft
  签名: {R S M : 类型} [幺半群 R] [加法幺半群 M]
  定义体: { hf.distribSMulLeft f hsmul, hf.mulActionLeft f hsmul with }

Depends on / 依赖: distribSMulLeft, hf.distribSMulLeft, hf.mulActionLeft, mulActionLeft
-/
abbrev Function.Surjective.distribMulActionLeft {R S M : Type*} [Monoid R] [AddMonoid M]
    [DistribMulAction R M] [Monoid S] [SMul S M] (f : R ->* S) (hf : Function.Surjective f)
    (hsmul : forall (c) (x : M), f c • x = c • x) : DistribMulAction S M :=
  { hf.distribSMulLeft f hsmul, hf.mulActionLeft f hsmul with }

section AddMonoid

variable (A) [AddMonoid A] [Monoid M] [DistribMulAction M A]

/--
Definition of `DistribMulAction.compHom` / `DistribMulAction.compHom` 的定义

English:
abbreviation DistribMulAction.compHom
  signature: [Monoid N] (f : N ->* M)
  body: { DistribSMul.compFun A f, MulAction.compHom A f with }

中文:
缩写 分配乘法作用.compHom
  签名: [幺半群 N] (f : N ->* M)
  定义体: { DistribSMul.compFun A f, MulAction.compHom A f with }

Depends on / 依赖: DistribSMul, DistribSMul.compFun, MulAction, MulAction.compHom, compFun, compHom
-/
abbrev DistribMulAction.compHom [Monoid N] (f : N ->* M) : DistribMulAction N A :=
  { DistribSMul.compFun A f, MulAction.compHom A f with }

end AddMonoid

section Monoid

variable (A) [Monoid A] [Monoid M] [MulDistribMulAction M A]

/--
Definition of `MulDistribMulAction.compHom` / `MulDistribMulAction.compHom` 的定义

English:
abbreviation MulDistribMulAction.compHom
  signature: [Monoid N] (f : N ->* M)
  body: { MulAction.compHom A f with
    smul_one := fun x => smul_one (f x),
    smul_mul := fun x => smul_mul' (f x) }

中文:
缩写 MulDistribMul作用.compHom
  签名: [幺半群 N] (f : N ->* M)
  定义体: { MulAction.compHom A f with
    smul_one := fun x => smul_one (f x),
    smul_mul := fun x => smul_mul' (f x) }

Depends on / 依赖: MulAction, MulAction.compHom, compHom, smul_mul, smul_one
-/
abbrev MulDistribMulAction.compHom [Monoid N] (f : N ->* M) : MulDistribMulAction N A :=
  { MulAction.compHom A f with
    smul_one := fun x => smul_one (f x),
    smul_mul := fun x => smul_mul' (f x) }

end Monoid

/--
Instance `AddMonoid.End.applyDistribMulAction` / 实例 `AddMonoid.End.applyDistribMulAction`

English:
instance AddMonoid.End.applyDistribMulAction
  signature: [AddMonoid α]
  body: (· <| ·)
  smul_zero := map_zero
  smul_add := map_add
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]

中文:
实例 加法幺半群.End.applyDistribMulAction
  签名: [加法幺半群 α]
  定义体: (· <| ·)
  smul_zero := map_zero
  smul_add := map_add
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]
-/
instance AddMonoid.End.applyDistribMulAction [AddMonoid α] :
    DistribMulAction (AddMonoid.End α) α where
  smul := (· <| ·)
  smul_zero := map_zero
  smul_add := map_add
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]
/--
theorem `AddMonoid.End.smul_def` / 定理 `AddMonoid.End.smul_def`

English:
theorem AddMonoid.End.smul_def
  given: [AddMonoid α] (f : AddMonoid.End α) (a : α)
  statement: f • a = f a
  proof: rfl

中文:
定理 加法幺半群.End.smul_def
  条件: [加法幺半群 α] (f : 加法幺半群.End α) (a : α)
  结论: f • a = f a
  证明: rfl
-/
theorem AddMonoid.End.smul_def [AddMonoid α] (f : AddMonoid.End α) (a : α) : f • a = f a :=
  rfl

/--
Instance `AddMonoid.End.applyFaithfulSMul` / 实例 `AddMonoid.End.applyFaithfulSMul`

English:
instance AddMonoid.End.applyFaithfulSMul
  signature: [AddMonoid α]
  body: ⟨fun {_ _ h} => AddMonoidHom.ext h⟩

中文:
实例 加法幺半群.End.applyFaithfulSMul
  签名: [加法幺半群 α]
  定义体: ⟨fun {_ _ h} => AddMonoidHom.ext h⟩

Depends on / 依赖: AddMonoidHom, AddMonoidHom.ext
-/
instance AddMonoid.End.applyFaithfulSMul [AddMonoid α] :
    FaithfulSMul (AddMonoid.End α) α :=
  ⟨fun {_ _ h} => AddMonoidHom.ext h⟩

/--
Definition of `DistribMulAction.toAddEquiv₀` / `DistribMulAction.toAddEquiv₀` 的定义

English:
definition DistribMulAction.toAddEquiv₀
  signature: {α : Type*} (β : Type*) [GroupWithZero α] [AddMonoid β]
  body: { DistribSMul.toAddMonoidHom β x with
    invFun := fun b => x⁻¹ • b
    left_inv := fun b => inv_smul_smul₀ hx b
    right_inv := fun b => smul_inv_smul₀ hx b }

中文:
定义 分配乘法作用.toAddEquiv₀
  签名: {α : 类型} (β : 类型) [带零群 α] [加法幺半群 β]
  定义体: { DistribSMul.toAddMonoidHom β x with
    invFun := fun b => x⁻¹ • b
    left_inv := fun b => inv_smul_smul₀ hx b
    right_inv := fun b => smul_inv_smul₀ hx b }

Depends on / 依赖: DistribSMul, DistribSMul.toAddMonoidHom, invFun, left_inv, right_inv, toAddMonoidHom
-/
def DistribMulAction.toAddEquiv₀ {α : Type*} (β : Type*) [GroupWithZero α] [AddMonoid β]
    [DistribMulAction α β] (x : α) (hx : x != 0) : β ≃+ β :=
  { DistribSMul.toAddMonoidHom β x with
    invFun := fun b => x⁻¹ • b
    left_inv := fun b => inv_smul_smul₀ hx b
    right_inv := fun b => smul_inv_smul₀ hx b }
