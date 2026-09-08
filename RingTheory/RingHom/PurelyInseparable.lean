/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.LocalProperties.Basic

/-!
# Purely inseparable ring homomorphisms

In this file we define purely inseparable ring homomorphisms and show their meta properties.

Since purely inseparable is mainly used for fields, we cannot prove many
general ring hom properties. E.g. we can't prove `StableUnderComposition IsPurelyInseparable`,
since `IsPurelyInseparable.trans` requires the involved rings to be fields.

-/

@[expose] public section

universe u v

/-- A ring homomorphism `f : F →+* E` is purely inseparable if `E` is purely inseparable as an
`F`-algebra. -/
@[algebraize IsPurelyInseparable]
/-
**RingHom.IsPurelyInseparable** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：{F : Type u} → {E : Type v} → [inst : CommRing F] → [inst_1 : CommRing E] 
→ (F →+* E) → Prop
参数：F →+* E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring homomorphism `f : F →+* E` is purely inseparable if `E` is purely insepar
able as an
`F`-algebra.
-/
protected def RingHom.IsPurelyInseparable
    {F : Type u} {E : Type v} [CommRing F] [CommRing E] (f : F →+* E) : Prop :=
  letI : Algebra F E := f.toAlgebra
  IsPurelyInseparable F E
/-
**RingHom.isPurelyInseparable_algebraMap_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.isPurelyInseparable_algebraMap_iff {F : Type u} {E : Type v} [Comm
Ring F] [CommRing E] [Algebra F E] : (algebraMap F E).IsPurelyInseparable ↔ IsPu
relyInseparable F E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.IsPurelyInseparable.eq_1`：∀ {F : Type u} {E : Type v} [inst : Co
mmRing F] [inst_1 : CommRing E] (f : F →+* E),   f.IsPurelyInseparable = IsPurel
yInseparable F E
· 使用定理 `toAlgebra_algebraMap`：∀ {R : Type u} {S : Type v} [inst : CommSemiring R
] [inst_1 : CommSemiring S] [inst_2 : Algebra R S],   (algebraMap R S).toAlgebra
 = inst_2
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma RingHom.isPurelyInseparable_algebraMap_iff
    {F : Type u} {E : Type v} [CommRing F] [CommRing E] [Algebra F E] :
    (algebraMap F E).IsPurelyInseparable ↔ IsPurelyInseparable F E := by
  rw [RingHom.IsPurelyInseparable, toAlgebra_algebraMap]

namespace RingHom.IsPurelyInseparable

variable {F E K : Type*}

variable (F) in
/-- The identity of a ring is purely inseparable. -/
/-
**RingHom.IsPurelyInseparable.id** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.IsPurelyInse
parable`。
形式化陈述：id [CommRing F] : RingHom.IsPurelyInseparable (RingHom.id F)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity of a ring is purely inseparable.
-/
lemma id [CommRing F] : RingHom.IsPurelyInseparable (RingHom.id F) :=
  isPurelyInseparable_self F
/-
**RingHom.IsPurelyInseparable.containsIdentities** 是 Mathlib 中的一个引理，位于命名空间 `Ring
Hom.IsPurelyInseparable`。
形式化陈述：containsIdentities : ContainsIdentities RingHom.IsPurelyInseparable
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RingHom.IsPurelyInseparable.id`：id [CommRing F] : RingHom.IsPurelyInsepa
rable (RingHom.id F)
-/
lemma containsIdentities : ContainsIdentities RingHom.IsPurelyInseparable := id

/-- Composition of purely inseparable ring homomorphisms between fields is purely inseparable. -/
/-
**RingHom.IsPurelyInseparable.comp** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.IsPurelyIn
separable`。
形式化陈述：comp [Field F] [Field E] [Field K] {f : F ->+* E} {g : E ->+* K} (hf : f.I
sPurelyInseparable) (hg : g.IsPurelyInseparable) : (g.comp f).IsPurelyInseparabl
e
参数：hf : f.IsPurelyInseparable；hg : g.IsPurelyInseparable。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `IsPurelyInseparable.trans`：IsPurelyInseparable.trans [Algebra E K] [IsSc
alarTower F E K] [h1 : IsPurelyInseparable F E] [h2 : IsPurelyInseparable E K] :
 IsPurelyInsepa…

--- 原说明 ---
Composition of purely inseparable ring homomorphisms between fields is purely in
separable.
-/
lemma comp [Field F] [Field E] [Field K] {f : F →+* E} {g : E →+* K}
    (hf : f.IsPurelyInseparable) (hg : g.IsPurelyInseparable) :
    (g.comp f).IsPurelyInseparable := by
  algebraize [f, g, g.comp f]
  exact IsPurelyInseparable.trans F E K

end RingHom.IsPurelyInseparable

