/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Algebraic structure on locally constant functions

This file puts algebraic structure (`Group`, `AddGroup`, etc)
on the type of locally constant functions.

-/

@[expose] public section

namespace LocallyConstant

variable {X Y : Type*} [TopologicalSpace X]

@[to_additive]
/-
**LocallyConstant.** 是 Mathlib 中的一个实例，位于命名空间 `LocallyConstant`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [One Y] : One (LocallyConstant X Y) where one := const X 1

@[to_additive (attr := simp)]
/-
**LocallyConstant.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConstant`。
形式化陈述：coe_one [One Y] : ⇑(1 : LocallyConstant X Y) = (1 : X -> Y)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one [One Y] : ⇑(1 : LocallyConstant X Y) = (1 : X → Y) :=
  rfl

@[to_additive]
/-
**LocallyConstant.one_apply** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConstant`。
形式化陈述：one_apply [One Y] (x : X) : (1 : LocallyConstant X Y) x = 1
参数：x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_apply [One Y] (x : X) : (1 : LocallyConstant X Y) x = 1 :=
  rfl

@[to_additive]
/-
**LocallyConstant.** 是 Mathlib 中的一个实例，位于命名空间 `LocallyConstant`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inv Y] : Inv (LocallyConstant X Y) where inv f := ⟨f⁻¹, f.isLocallyConstant.inv⟩

@[to_additive (attr := simp)]
/-
**LocallyConstant.coe_inv** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConstant`。
形式化陈述：coe_inv [Inv Y] (f : LocallyConstant X Y) : ⇑(f⁻¹ : LocallyConstant X Y) =
 (f : X -> Y)⁻¹
参数：f : LocallyConstant X Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inv [Inv Y] (f : LocallyConstant X Y) : ⇑(f⁻¹ : LocallyConstant X Y) = (f : X → Y)⁻¹ :=
  rfl

@[to_additive]
/-
**LocallyConstant.inv_apply** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConstant`。
形式化陈述：inv_apply [Inv Y] (f : LocallyConstant X Y) (x : X) : f⁻¹ x = (f x)⁻¹
参数：f : LocallyConstant X Y；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_apply [Inv Y] (f : LocallyConstant X Y) (x : X) : f⁻¹ x = (f x)⁻¹ :=
  rfl

@[to_additive]
/-
**LocallyConstant.** 是 Mathlib 中的一个实例，位于命名空间 `LocallyConstant`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mul Y] : Mul (LocallyConstant X Y) where
  mul f g := ⟨f * g, f.isLocallyConstant.mul g.isLocallyConstant⟩

@[to_additive (attr := simp)]
/-
**LocallyConstant.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConstant`。
形式化陈述：coe_mul [Mul Y] (f g : LocallyConstant X Y) : ⇑(f * g) = f * g
参数：f g : LocallyConstant X Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul [Mul Y] (f g : LocallyConstant X Y) : ⇑(f * g) = f * g :=
  rfl

@[to_additive]
/-
**LocallyConstant.mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConstant`。
形式化陈述：mul_apply [Mul Y] (f g : LocallyConstant X Y) (x : X) : (f * g) x = f x * 
g x
参数：f g : LocallyConstant X Y；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_apply [Mul Y] (f g : LocallyConstant X Y) (x : X) : (f * g) x = f x * g x :=
  rfl

@[to_additive]
/-
**LocallyConstant.** 是 Mathlib 中的一个实例，位于命名空间 `LocallyConstant`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MulOneClass Y] : MulOneClass (LocallyConstant X Y) :=
  Function.Injective.mulOneClass DFunLike.coe DFunLike.coe_injective rfl fun _ _ => rfl

/-- `DFunLike.coe` as a `MonoidHom`. -/
@[to_additive (attr := simps) /-- `DFunLike.coe` as an `AddMonoidHom`. -/]
/-
**LocallyConstant.coeFnMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant`。
形式化陈述：coeFnMonoidHom [MulOneClass Y] : LocallyConstant X Y ->* X -> Y where toFu
n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`DFunLike.coe` as a `MonoidHom`.
-/
def coeFnMonoidHom [MulOneClass Y] : LocallyConstant X Y →* X → Y where
  toFun := DFunLike.coe
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The constant-function embedding, as a multiplicative monoid hom. -/
@[to_additive (attr := simps) /-- The constant-function embedding, as an additive monoid hom. -/]
/-
**LocallyConstant.constMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant`。
形式化陈述：constMonoidHom [MulOneClass Y] : Y ->* LocallyConstant X Y where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant-function embedding, as a multiplicative monoid hom.
-/
def constMonoidHom [MulOneClass Y] : Y →* LocallyConstant X Y where
  toFun := const X
  map_one' := rfl
  map_mul' _ _ := rfl
/-
**LocallyConstant.** 是 Mathlib 中的一个实例，位于命名空间 `LocallyConstant`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MulZeroClass Y] : MulZeroClass (LocallyConstant X Y) :=
  Function.Injective.mulZeroClass DFunLike.coe DFunLike.coe_injective rfl fun _ _ => rfl
/-
**LocallyConstant.** 是 Mathlib 中的一个实例，位于命名空间 `LocallyConstant`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MulZeroOneClass Y] : MulZeroOneClass (LocallyConstant X Y) :=
  Function.Injective.mulZeroOneClass DFunLike.coe DFunLike.coe_injective rfl rfl fun _ _ => rfl

section CharFn

variable (Y) [MulZeroOneClass Y] {U V : Set X}

/-- Characteristic functions are locally constant functions taking `x : X` to `1` if `x ∈ U`,
  where `U` is a clopen set, and `0` otherwise. -/
/-
**LocallyConstant.charFn** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant`。
形式化陈述：charFn (hU : IsClopen U) : LocallyConstant X Y
参数：hU : IsClopen U。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Characteristic functions are locally constant functions taking `x : X` to `1` if
 `x ∈ U`,
  where `U` is a clopen set, and `0` otherwise.
-/
noncomputable def charFn (hU : IsClopen U) : LocallyConstant X Y :=
  indicator 1 hU
/-
**LocallyConstant.coe_charFn** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConstant`。
形式化陈述：coe_charFn (hU : IsClopen U) : (charFn Y hU : X -> Y) = Set.indicator U 1
参数：hU : IsClopen U。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_charFn (hU : IsClopen U) : (charFn Y hU : X → Y) = Set.indicator U 1 :=
  rfl
/-
**LocallyConstant.charFn_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConstant`。
形式化陈述：charFn_eq_one [Nontrivial Y] (x : X) (hU : IsClopen U) : charFn Y hU x = (
1 : Y) ↔ x in U
参数：x : X；hU : IsClopen U。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.indicator_eq_one_iff_mem`：indicator_eq_one_iff_mem : indicator s 1 i
 = (1 : M₀) ↔ i in s
-/
theorem charFn_eq_one [Nontrivial Y] (x : X) (hU : IsClopen U) : charFn Y hU x = (1 : Y) ↔ x ∈ U :=
  Set.indicator_eq_one_iff_mem _
/-
**LocallyConstant.charFn_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConstant`。
形式化陈述：charFn_eq_zero [Nontrivial Y] (x : X) (hU : IsClopen U) : charFn Y hU x = 
(0 : Y) ↔ x ∉ U
参数：x : X；hU : IsClopen U。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.indicator_eq_zero_iff_notMem`：indicator_eq_zero_iff_notMem : indicat
or s 1 i = (0 : M₀) ↔ i ∉ s
-/
theorem charFn_eq_zero [Nontrivial Y] (x : X) (hU : IsClopen U) : charFn Y hU x = (0 : Y) ↔ x ∉ U :=
  Set.indicator_eq_zero_iff_notMem _
/-
**LocallyConstant.charFn_inj** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConstant`。
形式化陈述：charFn_inj [Nontrivial Y] (hU : IsClopen U) (hV : IsClopen V) (h : charFn 
Y hU = charFn Y hV) : U = V
参数：hU : IsClopen U；hV : IsClopen V；h : charFn Y hU = charFn Y hV。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.indicator_one_inj`：indicator_one_inj (h : indicator s (1 : ι -> M₀) 
= indicator t 1) : s = t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LocallyConstant.coe_inj`：coe_inj {f g : LocallyConstant X Y} : (f : X ->
 Y) = g ↔ f = g
-/
theorem charFn_inj [Nontrivial Y] (hU : IsClopen U) (hV : IsClopen V)
    (h : charFn Y hU = charFn Y hV) : U = V :=
  Set.indicator_one_inj Y <| coe_inj.mpr h

end CharFn

@[to_additive]
/-
**LocallyConstant.** 是 Mathlib 中的一个实例，位于命名空间 `LocallyConstant`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Div Y] : Div (LocallyConstant X Y) where
  div f g := ⟨f / g, f.isLocallyConstant.div g.isLocallyConstant⟩

@[to_additive]
/-
**LocallyConstant.coe_div** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConstant`。
形式化陈述：coe_div [Div Y] (f g : LocallyConstant X Y) : ⇑(f / g) = f / g
参数：f g : LocallyConstant X Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_div [Div Y] (f g : LocallyConstant X Y) : ⇑(f / g) = f / g :=
  rfl

@[to_additive]
/-
**LocallyConstant.div_apply** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConstant`。
形式化陈述：div_apply [Div Y] (f g : LocallyConstant X Y) (x : X) : (f / g) x = f x / 
g x
参数：f g : LocallyConstant X Y；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem div_apply [Div Y] (f g : LocallyConstant X Y) (x : X) : (f / g) x = f x / g x :=
  rfl

@[to_additive]
/-
**LocallyConstant.** 是 Mathlib 中的一个实例，位于命名空间 `LocallyConstant`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semigroup Y] : Semigroup (LocallyConstant X Y) :=
  Function.Injective.semigroup DFunLike.coe DFunLike.coe_injective fun _ _ => rfl
/-
**LocallyConstant.** 是 Mathlib 中的一个实例，位于命名空间 `LocallyConstant`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SemigroupWithZero Y] : SemigroupWithZero (LocallyConstant X Y) :=
  Function.Injective.semigroupWithZero DFunLike.coe DFunLike.coe_injective rfl fun _ _ => rfl

@[to_additive]
/-
**LocallyConstant.** 是 Mathlib 中的一个实例，位于命名空间 `LocallyConstant`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommSemigroup Y] : CommSemigroup (LocallyConstant X Y) :=
  Function.Injective.commSemigroup DFunLike.coe DFunLike.coe_injective fun _ _ => rfl

variable {α R : Type*}

@[to_additive]
/-
**LocallyConstant.smul** 是 Mathlib 中的一个实例，位于命名空间 `LocallyConstant`。
形式化陈述：smul [SMul α Y] : SMul α (LocallyConstant X Y) where smul n f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smul [SMul α Y] : SMul α (LocallyConstant X Y) where
  smul n f := f.map (n • ·)

@[to_additive (attr := simp)]
/-
**LocallyConstant.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConstant`。
形式化陈述：coe_smul [SMul R Y] (r : R) (f : LocallyConstant X Y) : ⇑(r • f) = r • (f 
: X -> Y)
参数：r : R；f : LocallyConstant X Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul [SMul R Y] (r : R) (f : LocallyConstant X Y) : ⇑(r • f) = r • (f : X → Y) :=
  rfl

@[to_additive]
/-
**LocallyConstant.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConstant`。
形式化陈述：smul_apply [SMul R Y] (r : R) (f : LocallyConstant X Y) (x : X) : (r • f) 
x = r • f x
参数：r : R；f : LocallyConstant X Y；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_apply [SMul R Y] (r : R) (f : LocallyConstant X Y) (x : X) : (r • f) x = r • f x :=
  rfl

@[to_additive existing LocallyConstant.smul]
/-
**LocallyConstant.** 是 Mathlib 中的一个实例，位于命名空间 `LocallyConstant`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Pow Y α] : Pow (LocallyConstant X Y) α where
  pow f n := f.map (· ^ n)

@[to_additive]
/-
**LocallyConstant.** 是 Mathlib 中的一个实例，位于命名空间 `LocallyConstant`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid Y] : Monoid (LocallyConstant X Y) :=
  Function.Injective.monoid DFunLike.coe DFunLike.coe_injective rfl (fun _ _ => rfl) fun _ _ => rfl
/-
**LocallyConstant.** 是 Mathlib 中的一个实例，位于命名空间 `LocallyConstant`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NatCast Y] : NatCast (LocallyConstant X Y) where
  natCast n := const X n
/-
**LocallyConstant.** 是 Mathlib 中的一个实例，位于命名空间 `LocallyConstant`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IntCast Y] : IntCast (LocallyConstant X Y) where
  intCast n := const X n
/-
**LocallyConstant.** 是 Mathlib 中的一个实例，位于命名空间 `LocallyConstant`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddMonoidWithOne Y] : AddMonoidWithOne (LocallyConstant X Y) :=
  Function.Injective.addMonoidWithOne DFunLike.coe DFunLike.coe_injective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ => rfl

@[to_additive]
/-
**LocallyConstant.** 是 Mathlib 中的一个实例，位于命名空间 `LocallyConstant`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommMonoid Y] : CommMonoid (LocallyConstant X Y) :=
  Function.Injective.commMonoid DFunLike.coe DFunLike.coe_injective rfl (fun _ _ => rfl)
    fun _ _ => rfl

@[to_additive]
/-
**LocallyConstant.** 是 Mathlib 中的一个实例，位于命名空间 `LocallyConstant`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Group Y] : Group (LocallyConstant X Y) :=
  Function.Injective.group DFunLike.coe DFunLike.coe_injective rfl (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

@[to_additive]
/-
**LocallyConstant.** 是 Mathlib 中的一个实例，位于命名空间 `LocallyConstant`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommGroup Y] : CommGroup (LocallyConstant X Y) :=
  Function.Injective.commGroup DFunLike.coe DFunLike.coe_injective rfl (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
/-
**LocallyConstant.** 是 Mathlib 中的一个实例，位于命名空间 `LocallyConstant`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Distrib Y] : Distrib (LocallyConstant X Y) :=
  Function.Injective.distrib DFunLike.coe DFunLike.coe_injective (fun _ _ => rfl) fun _ _ => rfl
/-
**LocallyConstant.** 是 Mathlib 中的一个实例，位于命名空间 `LocallyConstant`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNonAssocSemiring Y] : NonUnitalNonAssocSemiring (LocallyConstant X Y) :=
  Function.Injective.nonUnitalNonAssocSemiring DFunLike.coe DFunLike.coe_injective rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
/-
**LocallyConstant.** 是 Mathlib 中的一个实例，位于命名空间 `LocallyConstant`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalSemiring Y] : NonUnitalSemiring (LocallyConstant X Y) :=
  Function.Injective.nonUnitalSemiring DFunLike.coe DFunLike.coe_injective rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
/-
**LocallyConstant.** 是 Mathlib 中的一个实例，位于命名空间 `LocallyConstant`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonAssocSemiring Y] : NonAssocSemiring (LocallyConstant X Y) :=
  Function.Injective.nonAssocSemiring DFunLike.coe DFunLike.coe_injective rfl rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

/-- The constant-function embedding, as a ring hom. -/
@[simps]
/-
**LocallyConstant.constRingHom** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant`。
形式化陈述：constRingHom [NonAssocSemiring Y] : Y ->+* LocallyConstant X Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant-function embedding, as a ring hom.
-/
def constRingHom [NonAssocSemiring Y] : Y →+* LocallyConstant X Y :=
  { constMonoidHom, constAddMonoidHom with toFun := const X }
/-
**LocallyConstant.** 是 Mathlib 中的一个实例，位于命名空间 `LocallyConstant`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring Y] : Semiring (LocallyConstant X Y) :=
  Function.Injective.semiring DFunLike.coe DFunLike.coe_injective rfl rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl
/-
**LocallyConstant.** 是 Mathlib 中的一个实例，位于命名空间 `LocallyConstant`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalCommSemiring Y] : NonUnitalCommSemiring (LocallyConstant X Y) :=
  Function.Injective.nonUnitalCommSemiring DFunLike.coe DFunLike.coe_injective rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
/-
**LocallyConstant.** 是 Mathlib 中的一个实例，位于命名空间 `LocallyConstant`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommSemiring Y] : CommSemiring (LocallyConstant X Y) :=
  Function.Injective.commSemiring DFunLike.coe DFunLike.coe_injective rfl rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl
/-
**LocallyConstant.** 是 Mathlib 中的一个实例，位于命名空间 `LocallyConstant`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNonAssocRing Y] : NonUnitalNonAssocRing (LocallyConstant X Y) :=
  Function.Injective.nonUnitalNonAssocRing DFunLike.coe DFunLike.coe_injective rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
/-
**LocallyConstant.** 是 Mathlib 中的一个实例，位于命名空间 `LocallyConstant`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalRing Y] : NonUnitalRing (LocallyConstant X Y) :=
  Function.Injective.nonUnitalRing DFunLike.coe DFunLike.coe_injective rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
/-
**LocallyConstant.** 是 Mathlib 中的一个实例，位于命名空间 `LocallyConstant`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonAssocRing Y] : NonAssocRing (LocallyConstant X Y) :=
  Function.Injective.nonAssocRing DFunLike.coe DFunLike.coe_injective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ => rfl)
/-
**LocallyConstant.** 是 Mathlib 中的一个实例，位于命名空间 `LocallyConstant`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Ring Y] : Ring (LocallyConstant X Y) :=
  Function.Injective.ring DFunLike.coe DFunLike.coe_injective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl
/-
**LocallyConstant.** 是 Mathlib 中的一个实例，位于命名空间 `LocallyConstant`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalCommRing Y] : NonUnitalCommRing (LocallyConstant X Y) :=
  Function.Injective.nonUnitalCommRing DFunLike.coe DFunLike.coe_injective rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
/-
**LocallyConstant.** 是 Mathlib 中的一个实例，位于命名空间 `LocallyConstant`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommRing Y] : CommRing (LocallyConstant X Y) :=
  Function.Injective.commRing DFunLike.coe DFunLike.coe_injective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl

variable {R : Type*}
/-
**LocallyConstant.** 是 Mathlib 中的一个实例，位于命名空间 `LocallyConstant`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid R] [MulAction R Y] : MulAction R (LocallyConstant X Y) :=
  Function.Injective.mulAction _ coe_injective fun _ _ => rfl
/-
**LocallyConstant.** 是 Mathlib 中的一个实例，位于命名空间 `LocallyConstant`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid R] [AddMonoid Y] [DistribMulAction R Y] :
    DistribMulAction R (LocallyConstant X Y) :=
  Function.Injective.distribMulAction coeFnAddMonoidHom coe_injective fun _ _ => rfl
/-
**LocallyConstant.** 是 Mathlib 中的一个实例，位于命名空间 `LocallyConstant`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring R] [AddCommMonoid Y] [Module R Y] : Module R (LocallyConstant X Y) :=
  Function.Injective.module R coeFnAddMonoidHom coe_injective fun _ _ => rfl

section Algebra

variable [CommSemiring R] [Semiring Y] [Algebra R Y]

/-
**LocallyConstant.** 是 Mathlib 中的一个实例，位于命名空间 `LocallyConstant`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra R (LocallyConstant X Y) where
  algebraMap := constRingHom.comp <| algebraMap R Y
  commutes' := by
    intros
    ext
    exact Algebra.commutes' _ _
  smul_def' := by
    intros
    ext
    exact Algebra.smul_def' _ _

@[simp]
/-
**LocallyConstant.coe_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConstant`。
形式化陈述：coe_algebraMap (r : R) : ⇑(algebraMap R (LocallyConstant X Y) r) = algebra
Map R (X -> Y) r
参数：r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_algebraMap (r : R) : ⇑(algebraMap R (LocallyConstant X Y) r) = algebraMap R (X → Y) r :=
  rfl

end Algebra

section coeFn

/-- `DFunLike.coe` as a `RingHom`. -/
/-
**LocallyConstant.coeFnRingHom** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant`。
形式化陈述：{X : Type u_1} → {Y : Type u_2} → [inst : TopologicalSpace X] → [inst_1 : 
Semiring Y] → LocallyConstant X Y →+* X → Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`DFunLike.coe` as a `RingHom`.
-/
@[simps!] def coeFnRingHom [Semiring Y] : LocallyConstant X Y →+* X → Y where
  toMonoidHom := coeFnMonoidHom
  __ := coeFnAddMonoidHom

/-- `DFunLike.coe` as a linear map. -/
/-
**LocallyConstant.coeFn** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`DFunLike.coe` as a linear map.
-/
@[simps!] def coeFnₗ (R : Type*) [Semiring R] [AddCommMonoid Y]
    [Module R Y] : LocallyConstant X Y →ₗ[R] X → Y where
  toAddHom := coeFnAddMonoidHom.toAddHom
  map_smul' _ _ := rfl

/-- `DFunLike.coe` as an `AlgHom`. -/
/-
**LocallyConstant.coeFnAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant`。
形式化陈述：{X : Type u_1} →   {Y : Type u_2} →     [inst : TopologicalSpace X] →     
  (R : Type u_6) →         [inst_1 : CommSemiring R] → [inst_2 : Semiring Y] → [
inst_3 : Algebra R Y] → LocallyConstant X Y →ₐ[R] X → Y
参数：R : Type u_6。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`DFunLike.coe` as an `AlgHom`.
-/
@[simps!] def coeFnAlgHom (R : Type*) [CommSemiring R] [Semiring Y] [Algebra R Y] :
    LocallyConstant X Y →ₐ[R] X → Y where
  toRingHom := coeFnRingHom
  commutes' _ := rfl

end coeFn

section Eval

/-- Evaluation as a `MonoidHom` -/
@[to_additive (attr := simps!) /-- Evaluation as an `AddMonoidHom` -/]
/-
**LocallyConstant.evalMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant`。
形式化陈述：evalMonoidHom [MulOneClass Y] (x : X) : LocallyConstant X Y ->* Y
参数：x : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluation as a `MonoidHom`
-/
def evalMonoidHom [MulOneClass Y] (x : X) : LocallyConstant X Y →* Y :=
  (Pi.evalMonoidHom _ x).comp coeFnMonoidHom

/-- Evaluation as a linear map -/
/-
**LocallyConstant.eval** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant`。
形式化陈述：eval {ι : Type*} {X : ι -> Type*} [forall i, TopologicalSpace (X i)] (i : 
ι) [DiscreteTopology (X i)] : LocallyConstant (Π i, X i) (X i) where toFun
参数：X i；i : ι；X i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluation as a linear map
-/
@[simps!] def evalₗ (R : Type*) [Semiring R] [AddCommMonoid Y]
    [Module R Y] (x : X) : LocallyConstant X Y →ₗ[R] Y :=
  (LinearMap.proj x).comp (coeFnₗ R)

/-- Evaluation as a `RingHom` -/
/-
**LocallyConstant.evalRingHom** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant`。
形式化陈述：{X : Type u_1} → {Y : Type u_2} → [inst : TopologicalSpace X] → [inst_1 : 
Semiring Y] → X → LocallyConstant X Y →+* Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluation as a `RingHom`
-/
@[simps!] def evalRingHom [Semiring Y] (x : X) : LocallyConstant X Y →+* Y :=
  (Pi.evalRingHom _ x).comp coeFnRingHom

/-- Evaluation as an `AlgHom` -/
@[simps!]
/-
**LocallyConstant.eval** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant`。
形式化陈述：eval {ι : Type*} {X : ι -> Type*} [forall i, TopologicalSpace (X i)] (i : 
ι) [DiscreteTopology (X i)] : LocallyConstant (Π i, X i) (X i) where toFun
参数：X i；i : ι；X i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluation as an `AlgHom`
-/
def evalₐ (R : Type*) [CommSemiring R] [Semiring Y] [Algebra R Y] (x : X) :
    LocallyConstant X Y →ₐ[R] Y :=
  (Pi.evalAlgHom _ _ x).comp (coeFnAlgHom R)

end Eval

section Comap

variable [TopologicalSpace Y] {Z : Type*}

/-- `LocallyConstant.comap` as a `MonoidHom`. -/
@[to_additive (attr := simps) /-- `LocallyConstant.comap` as an `AddMonoidHom`. -/]
/-
**LocallyConstant.comapMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant`。
形式化陈述：comapMonoidHom [MulOneClass Z] (f : C(X, Y)) : LocallyConstant Y Z ->* Loc
allyConstant X Z where toFun
参数：f : C(X, Y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LocallyConstant.comap` as a `MonoidHom`.
-/
def comapMonoidHom [MulOneClass Z] (f : C(X, Y)) :
    LocallyConstant Y Z →* LocallyConstant X Z where
  toFun := comap f
  map_one' := rfl
  map_mul' _ _ := rfl

/-- `LocallyConstant.comap` as a linear map. -/
@[simps!]
/-
**LocallyConstant.comap** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant`。
形式化陈述：comap (f : C(X, Y)) (g : LocallyConstant Y Z) : LocallyConstant X Z
参数：f : C(X, Y)；g : LocallyConstant Y Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LocallyConstant.comap` as a linear map.
-/
def comapₗ (R : Type*) [Semiring R] [AddCommMonoid Z] [Module R Z] (f : C(X, Y)) :
    LocallyConstant Y Z →ₗ[R] LocallyConstant X Z where
  toFun := comap f
  map_add' := map_add (comapAddMonoidHom f)
  map_smul' _ _ := rfl

/-- `LocallyConstant.comap` as a `RingHom`. -/
@[simps!]
/-
**LocallyConstant.comapRingHom** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant`。
形式化陈述：comapRingHom [Semiring Z] (f : C(X, Y)) : LocallyConstant Y Z ->+* Locally
Constant X Z where toMonoidHom
参数：f : C(X, Y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LocallyConstant.comap` as a `RingHom`.
-/
def comapRingHom [Semiring Z] (f : C(X, Y)) :
    LocallyConstant Y Z →+* LocallyConstant X Z where
  toMonoidHom := comapMonoidHom f
  __ := (comapAddMonoidHom f)

/-- `LocallyConstant.comap` as an `AlgHom` -/
@[simps!]
/-
**LocallyConstant.comap** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant`。
形式化陈述：comap (f : C(X, Y)) (g : LocallyConstant Y Z) : LocallyConstant X Z
参数：f : C(X, Y)；g : LocallyConstant Y Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LocallyConstant.comap` as an `AlgHom`
-/
def comapₐ (R : Type*) [CommSemiring R] [Semiring Z] [Algebra R Z]
    (f : C(X, Y)) : LocallyConstant Y Z →ₐ[R] LocallyConstant X Z where
  toRingHom := comapRingHom f
  commutes' _ := rfl
/-
**LocallyConstant.ker_comap** 是 Mathlib 中的一个引理，位于命名空间 `LocallyConstant`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ker_comapₗ [Semiring R] [AddCommMonoid Z] [Module R Z] (f : C(X, Y))
    (hfs : Function.Surjective f) :
    LinearMap.ker (comapₗ R f : LocallyConstant Y Z →ₗ[R] LocallyConstant X Z) = ⊥ :=
  LinearMap.ker_eq_bot_of_injective <| comap_injective _ hfs

/-- `LocallyConstant.congrLeft` as a linear equivalence. -/
@[simps!]
/-
**LocallyConstant.congrLeft** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant`。
形式化陈述：congrLeft [TopologicalSpace Y] (e : X ≃ₜ Y) : LocallyConstant X Z ≃ Locall
yConstant Y Z where toFun
参数：e : X ≃ₜ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LocallyConstant.congrLeft` as a linear equivalence.
-/
def congrLeftₗ (R : Type*) [Semiring R] [AddCommMonoid Z] [Module R Z] (e : X ≃ₜ Y) :
    LocallyConstant X Z ≃ₗ[R] LocallyConstant Y Z where
  toLinearMap := comapₗ R ⟨_, e.symm.continuous⟩
  __ := congrLeft e

/-- `LocallyConstant.congrLeft` as a `RingEquiv`. -/
@[simps!]
/-
**LocallyConstant.congrLeftRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant`
。
形式化陈述：congrLeftRingEquiv [Semiring Z] (e : X ≃ₜ Y) : LocallyConstant X Z ≃+* Loc
allyConstant Y Z where toEquiv
参数：e : X ≃ₜ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LocallyConstant.congrLeft` as a `RingEquiv`.
-/
def congrLeftRingEquiv [Semiring Z] (e : X ≃ₜ Y) :
    LocallyConstant X Z ≃+* LocallyConstant Y Z where
  toEquiv := congrLeft e
  __ := comapMonoidHom ⟨_, e.symm.continuous⟩
  __ := comapAddMonoidHom ⟨_, e.symm.continuous⟩

/-- `LocallyConstant.congrLeft` as an `AlgEquiv`. -/
@[simps!]
/-
**LocallyConstant.congrLeft** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant`。
形式化陈述：congrLeft [TopologicalSpace Y] (e : X ≃ₜ Y) : LocallyConstant X Z ≃ Locall
yConstant Y Z where toFun
参数：e : X ≃ₜ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LocallyConstant.congrLeft` as an `AlgEquiv`.
-/
def congrLeftₐ (R : Type*) [CommSemiring R] [Semiring Z] [Algebra R Z] (e : X ≃ₜ Y) :
    LocallyConstant X Z ≃ₐ[R] LocallyConstant Y Z where
  toEquiv := congrLeft e
  __ := comapₐ R ⟨_, e.symm.continuous⟩

end Comap

section Map

variable {Z : Type*}

/-- `LocallyConstant.map` as a `MonoidHom`. -/
@[to_additive (attr := simps) /-- `LocallyConstant.map` as an `AddMonoidHom`. -/]
/-
**LocallyConstant.mapMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant`。
形式化陈述：mapMonoidHom [MulOneClass Y] [MulOneClass Z] (f : Y ->* Z) : LocallyConsta
nt X Y ->* LocallyConstant X Z where toFun
参数：f : Y ->* Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LocallyConstant.map` as a `MonoidHom`.
-/
def mapMonoidHom [MulOneClass Y] [MulOneClass Z] (f : Y →* Z) :
    LocallyConstant X Y →* LocallyConstant X Z where
  toFun := map f
  map_one' := by aesop
  map_mul' := by aesop

/-- `LocallyConstant.map` as a linear map. -/
@[simps!]
/-
**LocallyConstant.map** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant`。
形式化陈述：map (f : Y -> Z) (g : LocallyConstant X Y) : LocallyConstant X Z
参数：f : Y -> Z；g : LocallyConstant X Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LocallyConstant.map` as a linear map.
-/
def mapₗ (R : Type*) [Semiring R] [AddCommMonoid Y] [Module R Y]
    [AddCommMonoid Z] [Module R Z] (f : Y →ₗ[R] Z) :
    LocallyConstant X Y →ₗ[R] LocallyConstant X Z where
  toFun := map f
  map_add' := by aesop
  map_smul' := by aesop

/-- `LocallyConstant.map` as a `RingHom`. -/
@[simps!]
/-
**LocallyConstant.mapRingHom** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant`。
形式化陈述：mapRingHom [Semiring Y] [Semiring Z] (f : Y ->+* Z) : LocallyConstant X Y 
->+* LocallyConstant X Z where toMonoidHom
参数：f : Y ->+* Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LocallyConstant.map` as a `RingHom`.
-/
def mapRingHom [Semiring Y] [Semiring Z] (f : Y →+* Z) :
    LocallyConstant X Y →+* LocallyConstant X Z where
  toMonoidHom := mapMonoidHom f
  __ := (mapAddMonoidHom f.toAddMonoidHom)

/-- `LocallyConstant.map` as an `AlgHom` -/
@[simps!]
/-
**LocallyConstant.map** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant`。
形式化陈述：map (f : Y -> Z) (g : LocallyConstant X Y) : LocallyConstant X Z
参数：f : Y -> Z；g : LocallyConstant X Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LocallyConstant.map` as an `AlgHom`
-/
def mapₐ (R : Type*) [CommSemiring R] [Semiring Y] [Algebra R Y] [Semiring Z] [Algebra R Z]
    (f : Y →ₐ[R] Z) : LocallyConstant X Y →ₐ[R] LocallyConstant X Z where
  toRingHom := mapRingHom f
  commutes' _ := by aesop

/-- `LocallyConstant.congrRight` as a linear equivalence. -/
@[simps!]
/-
**LocallyConstant.congrRight** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant`。
形式化陈述：congrRight (e : Y ≃ Z) : LocallyConstant X Y ≃ LocallyConstant X Z where t
oFun
参数：e : Y ≃ Z。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`LocallyConstant.congrRight` as a linear equivalence.
-/
def congrRightₗ (R : Type*) [Semiring R] [AddCommMonoid Y] [Module R Y]
    [AddCommMonoid Z] [Module R Z] (e : Y ≃ₗ[R] Z) :
    LocallyConstant X Y ≃ₗ[R] LocallyConstant X Z where
  toLinearMap := mapₗ R e
  __ := congrRight e.toEquiv

/-- `LocallyConstant.congrRight` as a `RingEquiv`. -/
@[simps!]
/-
**LocallyConstant.congrRightRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant
`。
形式化陈述：congrRightRingEquiv [Semiring Y] [Semiring Z] (e : Y ≃+* Z) : LocallyConst
ant X Y ≃+* LocallyConstant X Z where toEquiv
参数：e : Y ≃+* Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LocallyConstant.congrRight` as a `RingEquiv`.
-/
def congrRightRingEquiv [Semiring Y] [Semiring Z] (e : Y ≃+* Z) :
    LocallyConstant X Y ≃+* LocallyConstant X Z where
  toEquiv := congrRight e
  __ := mapMonoidHom e.toMonoidHom
  __ := mapAddMonoidHom e.toAddMonoidHom

/-- `LocallyConstant.congrRight` as an `AlgEquiv`. -/
@[simps!]
/-
**LocallyConstant.congrRight** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant`。
形式化陈述：congrRight (e : Y ≃ Z) : LocallyConstant X Y ≃ LocallyConstant X Z where t
oFun
参数：e : Y ≃ Z。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`LocallyConstant.congrRight` as an `AlgEquiv`.
-/
def congrRightₐ (R : Type*) [CommSemiring R] [Semiring Y] [Algebra R Y] [Semiring Z] [Algebra R Z]
    (e : Y ≃ₐ[R] Z) : LocallyConstant X Y ≃ₐ[R] LocallyConstant X Z where
  toEquiv := congrRight e
  __ := mapₐ R e.toAlgHom

end Map

section Const

/-- `LocallyConstant.const` as a linear map. -/
@[simps!]
/-
**LocallyConstant.const** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant`。
形式化陈述：const (X : Type*) {Y : Type*} [TopologicalSpace X] (y : Y) : LocallyConsta
nt X Y
参数：X : Type*；y : Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocallyConstant.const`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] (y : Y), IsLocallyConstant (Function.const X y)

--- 原说明 ---
`LocallyConstant.const` as a linear map.
-/
def constₗ (R : Type*) [Semiring R] [AddCommMonoid Y] [Module R Y] :
    Y →ₗ[R] LocallyConstant X Y where
  toFun := const X
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `LocallyConstant.const` as an `AlgHom` -/
@[simps!]
/-
**LocallyConstant.const** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant`。
形式化陈述：const (X : Type*) {Y : Type*} [TopologicalSpace X] (y : Y) : LocallyConsta
nt X Y
参数：X : Type*；y : Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocallyConstant.const`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] (y : Y), IsLocallyConstant (Function.const X y)

--- 原说明 ---
`LocallyConstant.const` as an `AlgHom`
-/
def constₐ (R : Type*) [CommSemiring R] [Semiring Y] [Algebra R Y] :
    Y →ₐ[R] LocallyConstant X Y where
  toRingHom := constRingHom
  commutes' _ := rfl

end Const

end LocallyConstant

