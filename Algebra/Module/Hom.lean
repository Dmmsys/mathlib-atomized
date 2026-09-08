/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.GroupWithZero.Action.End
public import Mathlib.Algebra.GroupWithZero.Action.Hom
public import Mathlib.Algebra.Module.End
public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.GroupTheory.GroupAction.DomAct.Basic

/-!
# Bundled Hom instances for module and multiplicative actions

This file defines instances for `Module` on bundled `Hom` types.

These are analogous to the instances in `Algebra.Module.Pi`, but for bundled instead of unbundled
functions.

We also define a bundled versions of `(· • ·)` as `AddMonoidHom.smul`.
-/

@[expose] public section

variable {R S M A B : Type*}

namespace ZeroHom

/-
**ZeroHom.instModule** 是 Mathlib 中的一个实例，位于命名空间 `ZeroHom`。
形式化陈述：instModule [Semiring R] [AddMonoid A] [AddCommMonoid B] [Module R B] : Mod
ule R (ZeroHom A B) where __ : MulActionWithZero _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instModule [Semiring R] [AddMonoid A] [AddCommMonoid B] [Module R B] :
    Module R (ZeroHom A B) where
  __ : MulActionWithZero _ _ := ZeroHom.instMulActionWithZero
  add_smul _ _ _ := ext fun _ => add_smul _ _ _
  smul_add _ _ _ := ext fun _ => smul_add _ _ _

end ZeroHom

/-! ### Instances for `AddMonoidHom` -/

namespace AddMonoidHom

/-
**AddMonoidHom.instModule** 是 Mathlib 中的一个实例，位于命名空间 `AddMonoidHom`。
形式化陈述：instModule [Semiring R] [AddMonoid A] [AddCommMonoid B] [Module R B] : Mod
ule R (A ->+ B) where add_smul _ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instModule [Semiring R] [AddMonoid A] [AddCommMonoid B] [Module R B] :
    Module R (A →+ B) where
  add_smul _ _ _ := ext fun _ => add_smul _ _ _
  zero_smul _ := ext fun _ => zero_smul _ _

set_option backward.isDefEq.respectTransparency false in
/-
**AddMonoidHom.instDomMulActModule** 是 Mathlib 中的一个实例，位于命名空间 `AddMonoidHom`。
形式化陈述：instDomMulActModule {S M M₂ : Type*} [Semiring S] [AddCommMonoid M] [AddCo
mmMonoid M₂] [Module S M] : Module Sᵈᵐᵃ (M ->+ M₂) where add_smul s s' f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDomMulActModule
    {S M M₂ : Type*} [Semiring S] [AddCommMonoid M] [AddCommMonoid M₂] [Module S M] :
    Module Sᵈᵐᵃ (M →+ M₂) where
  add_smul s s' f := AddMonoidHom.ext fun m ↦ by
    simp_rw [AddMonoidHom.add_apply, DomMulAct.smul_addMonoidHom_apply, ← map_add, ← add_smul]; rfl
  zero_smul _ := AddMonoidHom.ext fun _ ↦ by
    rw [DomMulAct.smul_addMonoidHom_apply]
    -- TODO there should be a simp lemma for `DomMulAct.mk.symm 0`
    simp [DomMulAct.mk, MulOpposite.opEquiv]

end AddMonoidHom

/-!
### Instances for `AddMonoid.End`

These are direct copies of the instances above.
-/

namespace AddMonoid.End

section

variable [Monoid R] [Monoid S] [AddCommMonoid A]

/-
**AddMonoid.End.instDistribSMul** 是 Mathlib 中的一个实例，位于命名空间 `AddMonoid.End`。
形式化陈述：instDistribSMul [DistribSMul M A] : DistribSMul M (AddMonoid.End A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDistribSMul [DistribSMul M A] : DistribSMul M (AddMonoid.End A) :=
  inferInstanceAs <| DistribSMul M (A →+ A)

variable [DistribMulAction R A] [DistribMulAction S A]
/-
**AddMonoid.End.instDistribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `AddMonoid.End`。
形式化陈述：instDistribMulAction : DistribMulAction R (AddMonoid.End A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDistribMulAction : DistribMulAction R (AddMonoid.End A) :=
  inferInstanceAs <| DistribMulAction R (A →+ A)
/-
**AddMonoid.End.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoid.End`。
形式化陈述：∀ {R : Type u_1} {A : Type u_4} [inst : Monoid R] [inst_1 : AddCommMonoid 
A] [inst_2 : DistribMulAction R A] (r : R)   (f : AddMonoid.End A), ⇑(r • f) = r
 • ⇑f
参数：r : R；f : AddMonoid.End A；r • f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_smul (r : R) (f : AddMonoid.End A) : ⇑(r • f) = r • ⇑f := rfl
/-
**AddMonoid.End.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoid.End`。
形式化陈述：smul_apply (r : R) (f : AddMonoid.End A) (x : A) : (r • f) x = r • f x
参数：r : R；f : AddMonoid.End A；x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_apply (r : R) (f : AddMonoid.End A) (x : A) : (r • f) x = r • f x :=
  rfl
/-
**AddMonoid.End.smulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `AddMonoid.End`。
形式化陈述：smulCommClass [SMulCommClass R S A] : SMulCommClass R S (AddMonoid.End A)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.instSMulCommClass`：∀ {M : Type u_1} {N : Type u_2} {A : Typ
e u_3} {B : Type u_4} [inst : AddZeroClass A] [inst_1 : AddZeroClass B]   [inst_
2 : DistribSMul M B]…
-/
instance smulCommClass [SMulCommClass R S A] : SMulCommClass R S (AddMonoid.End A) :=
  AddMonoidHom.instSMulCommClass
/-
**AddMonoid.End.isScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `AddMonoid.End`。
形式化陈述：isScalarTower [SMul R S] [IsScalarTower R S A] : IsScalarTower R S (AddMon
oid.End A)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.instIsScalarTower`：∀ {M : Type u_1} {N : Type u_2} {A : Typ
e u_3} {B : Type u_4} [inst : AddZeroClass A] [inst_1 : AddZeroClass B]   [inst_
2 : SMul M N] [inst_…
-/
instance isScalarTower [SMul R S] [IsScalarTower R S A] : IsScalarTower R S (AddMonoid.End A) :=
  AddMonoidHom.instIsScalarTower
/-
**AddMonoid.End.isCentralScalar** 是 Mathlib 中的一个实例，位于命名空间 `AddMonoid.End`。
形式化陈述：isCentralScalar [DistribMulAction Rᵐᵒᵖ A] [IsCentralScalar R A] : IsCentra
lScalar R (AddMonoid.End A)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.instIsCentralScalar`：∀ {M : Type u_1} {A : Type u_3} {B : T
ype u_4} [inst : AddZeroClass A] [inst_1 : AddZeroClass B]   [inst_2 : DistribSM
ul M B] [inst_3 : Dist…
-/
instance isCentralScalar [DistribMulAction Rᵐᵒᵖ A] [IsCentralScalar R A] :
    IsCentralScalar R (AddMonoid.End A) :=
  AddMonoidHom.instIsCentralScalar

end

/-
**AddMonoid.End.instModule** 是 Mathlib 中的一个实例，位于命名空间 `AddMonoid.End`。
形式化陈述：instModule [Semiring R] [AddCommMonoid A] [Module R A] : Module R (AddMono
id.End A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instModule [Semiring R] [AddCommMonoid A] [Module R A] : Module R (AddMonoid.End A) :=
  inferInstanceAs <| Module R (A →+ A)

/-- The tautological action by `AddMonoid.End α` on `α`.

This generalizes `AddMonoid.End.applyDistribMulAction`. -/
/-
**AddMonoid.End.applyModule** 是 Mathlib 中的一个实例，位于命名空间 `AddMonoid.End`。
形式化陈述：applyModule [AddCommMonoid A] : Module (AddMonoid.End A) A where add_smul 
_ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tautological action by `AddMonoid.End α` on `α`.

This generalizes `AddMonoid.End.applyDistribMulAction`.
-/
instance applyModule [AddCommMonoid A] : Module (AddMonoid.End A) A where
  add_smul _ _ _ := rfl
  zero_smul _ := rfl

end AddMonoid.End

/-! ### Miscellaneous morphisms -/

namespace AddMonoidHom

/-- Scalar multiplication on the left as an additive monoid homomorphism.

See also the linear map version of this `Module.End.smulLeft`. -/
@[simps! -fullyApplied, deprecated DistribSMul.toAddMonoidHom (since := "2026-01-07")]
/-
**AddMonoidHom.smulLeft** 是 Mathlib 中的一个定义，位于命名空间 `AddMonoidHom`。
形式化陈述：{M : Type u_3} → {A : Type u_4} → [inst : AddMonoid A] → [DistribSMul M A]
 → M → A →+ A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Scalar multiplication on the left as an additive monoid homomorphism.

See also the linear map version of this `Module.End.smulLeft`.
-/
protected def smulLeft [AddMonoid A] [DistribSMul M A] (c : M) : A →+ A :=
  DistribSMul.toAddMonoidHom _ c

/-- Scalar multiplication as a biadditive monoid homomorphism. We need `M` to be commutative
to have addition on `M →+ M`. -/
/-
**AddMonoidHom.smul** 是 Mathlib 中的一个定义，位于命名空间 `AddMonoidHom`。
形式化陈述：{R : Type u_1} → {M : Type u_3} → [inst : Semiring R] → [inst_1 : AddCommM
onoid M] → [_root_.Module R M] → R →+ M →+ M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Scalar multiplication as a biadditive monoid homomorphism. We need `M` to be com
mutative
to have addition on `M →+ M`.
-/
protected def smul [Semiring R] [AddCommMonoid M] [Module R M] : R →+ M →+ M :=
  (Module.toAddMonoidEnd R M).toAddMonoidHom
/-
**AddMonoidHom.coe_smul'** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidHom`。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M],   ⇑AddMonoidHom.smul = DistribSMul.toAddMonoi
dHom M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_smul' [Semiring R] [AddCommMonoid M] [Module R M] :
    ⇑(.smul : R →+ M →+ M) = DistribSMul.toAddMonoidHom _ := rfl

end AddMonoidHom

