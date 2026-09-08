/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Ring.Action.End
public import Mathlib.RingTheory.Ideal.Maps

/-! # Pointwise instances on `Ideal`s

This file provides the action `Ideal.pointwiseMulAction` which morally matches the action of
`mulActionSet` (though here an extra `Ideal.span` is inserted).

This action is available in the `Pointwise` locale.

## Implementation notes

This file is similar (but not identical) to `Mathlib/Algebra/Ring/Subsemiring/Pointwise.lean`.
Where possible, try to keep them in sync.

-/

@[expose] public section


open Set

variable {M N R : Type*}

namespace Ideal

section Monoid

variable [Monoid M] [Monoid N] [Semiring R] [MulSemiringAction M R] [MulSemiringAction N R]

/-- The action on an ideal corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale. -/
@[instance_reducible]
/-
**Ideal.pointwiseDistribMulAction** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：{M : Type u_1} →   {R : Type u_3} → [inst : Monoid M] → [inst_1 : Semiring
 R] → [MulSemiringAction M R] → DistribMulAction M (Ideal R)
参数：Ideal R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action on an ideal corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale.
-/
protected def pointwiseDistribMulAction : DistribMulAction M (Ideal R) where
  smul a := Ideal.map (MulSemiringAction.toRingHom _ _ a)
  one_smul I :=
    congr_arg (I.map ·) (RingHom.ext <| one_smul M) |>.trans I.map_id
  mul_smul _ _ I :=
    congr_arg (I.map ·) (RingHom.ext <| mul_smul _ _) |>.trans (I.map_map _ _).symm
  smul_zero _ := Ideal.map_bot
  smul_add _ I J := Ideal.map_sup _ I J

scoped[Pointwise] attribute [instance] Ideal.pointwiseDistribMulAction

open scoped Pointwise

/-- The action on an ideal corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale. -/
@[instance_reducible]
/-
**Ideal.pointwiseMulSemiringAction** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：{M : Type u_1} →   [inst : Monoid M] → {R : Type u_4} → [inst_1 : CommRing
 R] → [MulSemiringAction M R] → MulSemiringAction M (Ideal R)
参数：Ideal R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action on an ideal corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale.
-/
protected def pointwiseMulSemiringAction {R : Type*} [CommRing R] [MulSemiringAction M R] :
    MulSemiringAction M (Ideal R) where
  smul_one a := by simp only [Ideal.one_eq_top]; exact Ideal.map_top _
  smul_mul a I J := Ideal.map_mul (MulSemiringAction.toRingHom _ _ a) I J

scoped[Pointwise] attribute [instance] Ideal.pointwiseMulSemiringAction
/-
**Ideal.pointwise_smul_def** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：pointwise_smul_def {a : M} (S : Ideal R) : a • S = S.map (MulSemiringActio
n.toRingHom _ _ a)
参数：S : Ideal R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pointwise_smul_def {a : M} (S : Ideal R) :
    a • S = S.map (MulSemiringAction.toRingHom _ _ a) :=
  rfl
/-
**Ideal.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul M N] [IsScalarTower M N R] : IsScalarTower M N (Ideal R) where
  smul_assoc x y z := by
    simp_rw [pointwise_smul_def, map_map]
    congr
    ext
    simp

-- note: unlike with `Subring`, `pointwise_smul_toAddSubgroup` wouldn't be true
/-
**Ideal.smul_mem_pointwise_smul** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：smul_mem_pointwise_smul (m : M) (r : R) (S : Ideal R) : r in S -> m • r in
 m • S
参数：m : M；r : R；S : Ideal R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
· 使用定理 `Set.smul_mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β]
 {s : Set β} {a : α} {b : β}, b ∈ s → a • b ∈ a • s
-/
theorem smul_mem_pointwise_smul (m : M) (r : R) (S : Ideal R) : r ∈ S → m • r ∈ m • S :=
  fun h => subset_span <| Set.smul_mem_smul_set h
/-
**Ideal.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CovariantClass M (Ideal R) HSMul.hSMul LE.le :=
  ⟨fun _ _ => map_mono⟩

-- note: unlike with `Subring`, `mem_smul_pointwise_iff_exists` wouldn't be true

@[simp]
/-
**Ideal.smul_bot** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：smul_bot (a : M) : a • (⊥ : Ideal R) = ⊥
参数：a : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.map_bot`：map_bot : (⊥ : Ideal R).map f = ⊥
-/
theorem smul_bot (a : M) : a • (⊥ : Ideal R) = ⊥ :=
  map_bot
/-
**Ideal.smul_sup** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：smul_sup (a : M) (S T : Ideal R) : a • (S ⊔ T) = a • S ⊔ a • T
参数：a : M；S T : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.map_sup`：map_sup : (I ⊔ J).map f = I.map f ⊔ J.map f
-/
theorem smul_sup (a : M) (S T : Ideal R) : a • (S ⊔ T) = a • S ⊔ a • T :=
  map_sup _ _ _
/-
**Ideal.smul_closure** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：smul_closure (a : M) (s : Set R) : a • span s = span (a • s)
参数：a : M；s : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.map_span`：map_span (s : Set R) : map f (span s) = span (f '' s)
-/
theorem smul_closure (a : M) (s : Set R) : a • span s = span (a • s) :=
  Ideal.map_span _ _
/-
**Ideal.pointwise_central_scalar** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
形式化陈述：pointwise_central_scalar [MulSemiringAction Mᵐᵒᵖ R] [IsCentralScalar M R] 
: IsCentralScalar M (Ideal R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
-/
instance pointwise_central_scalar [MulSemiringAction Mᵐᵒᵖ R] [IsCentralScalar M R] :
    IsCentralScalar M (Ideal R) :=
  ⟨fun _ S => (congr_arg fun f => S.map f) <| RingHom.ext <| op_smul_eq_smul _⟩

@[simp]
/-
**Ideal.pointwise_smul_toAddSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：pointwise_smul_toAddSubmonoid (a : M) (S : Ideal R) (ha : Function.Surject
ive fun r : R => a • r) : (a • S).toAddSubmonoid = a • S.toAddSubmonoid
参数：a : M；S : Ideal R；ha : Function.Surjective fun r : R => a • r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoid.ext`：∀ {M : Type u_1} [inst : AddZeroClass M] {S T : AddSub
monoid M}, (∀ (x : M), x ∈ S ↔ x ∈ T) → S = T
· 使用定理 `Ideal.mem_map_iff_of_surjective`：mem_map_iff_of_surjective {I : Ideal R}
 {y} : y in map f I ↔ exists x, x in I ∧ f x = y
-/
theorem pointwise_smul_toAddSubmonoid (a : M) (S : Ideal R)
    (ha : Function.Surjective fun r : R => a • r) :
    (a • S).toAddSubmonoid = a • S.toAddSubmonoid := by
  ext
  exact Ideal.mem_map_iff_of_surjective _ <| by exact ha

@[simp]
/-
**Ideal.pointwise_smul_toAddSubgroup** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：pointwise_smul_toAddSubgroup {R : Type*} [Ring R] [MulSemiringAction M R] 
(a : M) (S : Ideal R) (ha : Function.Surjective fun r : R => a • r) : (a • S).to
AddSubgroup = a • S.toAddSubgroup
参数：a : M；S : Ideal R；ha : Function.Surjective fun r : R => a • r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.ext`：∀ {G : Type u_1} [inst : AddGroup G] {H K : AddSubgroup
 G}, (∀ (x : G), x ∈ H ↔ x ∈ K) → H = K
· 使用定理 `Ideal.mem_map_iff_of_surjective`：mem_map_iff_of_surjective {I : Ideal R}
 {y} : y in map f I ↔ exists x, x in I ∧ f x = y
-/
theorem pointwise_smul_toAddSubgroup {R : Type*} [Ring R] [MulSemiringAction M R]
    (a : M) (S : Ideal R) (ha : Function.Surjective fun r : R => a • r) :
    (a • S).toAddSubgroup = a • S.toAddSubgroup := by
  ext
  exact Ideal.mem_map_iff_of_surjective _ <| by exact ha

end Monoid

section Group

variable [Group M] [Semiring R] [MulSemiringAction M R]

open scoped Pointwise

/-
**Ideal.pointwise_smul_eq_comap** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：pointwise_smul_eq_comap {a : M} (S : Ideal R) : a • S = S.comap (MulSemiri
ngAction.toRingAut _ _ a).symm
参数：S : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.comap.congr_simp`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst
 : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   (f f_1 : F),   f
 = f_1 → ∀ […
· 使用定理 `MulSemiringAction.toRingAut_apply`：∀ (G : Type u_1) (R : Type u_2) [inst
 : Group G] [inst_1 : Semiring R] [inst_2 : MulSemiringAction G R] (a : G),   (M
ulSemiringAction.toRing…
· 使用定理 `Ideal.comap_symm`：comap_symm {I : Ideal R} (f : R ≃+* S) : I.comap f.sym
m = I.map f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem pointwise_smul_eq_comap {a : M} (S : Ideal R) :
    a • S = S.comap (MulSemiringAction.toRingAut _ _ a).symm := by
  ext
  simp [pointwise_smul_def]
  rfl

@[simp]
/-
**Ideal.smul_mem_pointwise_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：smul_mem_pointwise_smul_iff {a : M} {S : Ideal R} {x : R} : a • x in a • S
 ↔ x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用定理 `Ideal.smul_mem_pointwise_smul`：smul_mem_pointwise_smul (m : M) (r : R) (
S : Ideal R) : r in S -> m • r in m • S
-/
theorem smul_mem_pointwise_smul_iff {a : M} {S : Ideal R} {x : R} : a • x ∈ a • S ↔ x ∈ S :=
  ⟨fun h => by simpa using smul_mem_pointwise_smul a⁻¹ _ _ h, smul_mem_pointwise_smul _ _ _⟩
/-
**Ideal.mem_pointwise_smul_iff_inv_smul_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：mem_pointwise_smul_iff_inv_smul_mem {a : M} {S : Ideal R} {x : R} : x in a
 • S ↔ a⁻¹ • x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用定理 `Ideal.smul_mem_pointwise_smul`：smul_mem_pointwise_smul (m : M) (r : R) (
S : Ideal R) : r in S -> m • r in m • S
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
-/
theorem mem_pointwise_smul_iff_inv_smul_mem {a : M} {S : Ideal R} {x : R} :
    x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  ⟨fun h => by simpa using smul_mem_pointwise_smul a⁻¹ _ _ h,
    fun h => by simpa using smul_mem_pointwise_smul a _ _ h⟩
/-
**Ideal.mem_inv_pointwise_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：mem_inv_pointwise_smul_iff {a : M} {S : Ideal R} {x : R} : x in a⁻¹ • S ↔ 
a • x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.mem_pointwise_smul_iff_inv_smul_mem`：mem_pointwise_smul_iff_inv_sm
ul_mem {a : M} {S : Ideal R} {x : R} : x in a • S ↔ a⁻¹ • x in S
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_inv_pointwise_smul_iff {a : M} {S : Ideal R} {x : R} : x ∈ a⁻¹ • S ↔ a • x ∈ S := by
  rw [mem_pointwise_smul_iff_inv_smul_mem, inv_inv]

@[simp]
/-
**Ideal.pointwise_smul_le_pointwise_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：pointwise_smul_le_pointwise_smul_iff {a : M} {S T : Ideal R} : a • S <= a 
• T ↔ S <= T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用定理 `smul_mono_right`：smul_mono_right [SMul M α] [Preorder α] [CovariantClass
 M α HSMul.hSMul LE.le] (m : M) : Monotone (HSMul.hSMul m : α -> α)
· 使用定理 `Ideal.instCovariantClassHSMulLe`：∀ {M : Type u_1} {R : Type u_3} [inst :
 Monoid M] [inst_1 : Semiring R] [inst_2 : MulSemiringAction M R],   CovariantCl
ass M (Ideal R) HSMul…
-/
theorem pointwise_smul_le_pointwise_smul_iff {a : M} {S T : Ideal R} : a • S ≤ a • T ↔ S ≤ T :=
  ⟨fun h => by simpa using smul_mono_right a⁻¹ h, fun h => smul_mono_right a h⟩
/-
**Ideal.pointwise_smul_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：pointwise_smul_subset_iff {a : M} {S T : Ideal R} : a • S <= T ↔ S <= a⁻¹ 
• T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.pointwise_smul_le_pointwise_smul_iff`：pointwise_smul_le_pointwise_
smul_iff {a : M} {S T : Ideal R} : a • S <= a • T ↔ S <= T
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem pointwise_smul_subset_iff {a : M} {S T : Ideal R} : a • S ≤ T ↔ S ≤ a⁻¹ • T := by
  rw [← pointwise_smul_le_pointwise_smul_iff (a := a⁻¹), inv_smul_smul]
/-
**Ideal.subset_pointwise_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：subset_pointwise_smul_iff {a : M} {S T : Ideal R} : S <= a • T ↔ a⁻¹ • S <
= T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.pointwise_smul_le_pointwise_smul_iff`：pointwise_smul_le_pointwise_
smul_iff {a : M} {S T : Ideal R} : a • S <= a • T ↔ S <= T
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem subset_pointwise_smul_iff {a : M} {S T : Ideal R} : S ≤ a • T ↔ a⁻¹ • S ≤ T := by
  rw [← pointwise_smul_le_pointwise_smul_iff (a := a⁻¹), inv_smul_smul]
/-
**Ideal.IsPrime.smul** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsPrime`。
形式化陈述：∀ {M : Type u_1} {R : Type u_3} [inst : Group M] [inst_1 : Semiring R] [in
st_2 : MulSemiringAction M R] {I : Ideal R}   [H : I.IsPrime] (g : M), (g • I).I
sPrime
参数：g : M；g • I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.pointwise_smul_eq_comap`：pointwise_smul_eq_comap {a : M} (S : Idea
l R) : a • S = S.comap (MulSemiringAction.toRingAut _ _ a).symm
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
-/
instance IsPrime.smul {I : Ideal R} [H : I.IsPrime] (g : M) : (g • I).IsPrime := by
  rw [I.pointwise_smul_eq_comap]
  apply H.comap

@[simp]
/-
**Ideal.IsPrime.smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsPrime`。
形式化陈述：∀ {M : Type u_1} {R : Type u_3} [inst : Group M] [inst_1 : Semiring R] [in
st_2 : MulSemiringAction M R] {I : Ideal R}   (g : M), (g • I).IsPrime ↔ I.IsPri
me
参数：g : M；g • I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsPrime.smul`：∀ {M : Type u_1} {R : Type u_3} [inst : Group M] [in
st_1 : Semiring R] [inst_2 : MulSemiringAction M R] {I : Ideal R}   [H : I.IsPri
me] (g :…
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
-/
theorem IsPrime.smul_iff {I : Ideal R} (g : M) : (g • I).IsPrime ↔ I.IsPrime :=
  ⟨fun H ↦ inv_smul_smul g I ▸ H.smul g⁻¹, fun H ↦ H.smul g⟩
/-
**Ideal.inertia_le_stabilizer** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：inertia_le_stabilizer {R : Type*} [Ring R] (P : Ideal R) [MulSemiringActio
n M R] : inertia M P <= MulAction.stabilizer M P
参数：P : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.mem_pointwise_smul_iff_inv_smul_mem`：mem_pointwise_smul_iff_inv_sm
ul_mem {a : M} {S : Ideal R} {x : R} : x in a • S ↔ a⁻¹ • x in S
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.add_mem_iff_left`：∀ {α : Type u} [inst : Ring α] (I : Ideal α) {a 
b : α}, b ∈ I → (a + b ∈ I ↔ a ∈ I)
· 使用定理 `InvMemClass.inv_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Inv G} {inst_1 : SetLike S G} [self : InvMemClass S G] {s : S}   {x : G}, x ∈ s 
→ x⁻¹ ∈ s
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inertia_le_stabilizer {R : Type*} [Ring R] (P : Ideal R) [MulSemiringAction M R] :
    inertia M P ≤ MulAction.stabilizer M P := by
  refine fun σ hσ ↦ SetLike.ext fun x ↦ ?_
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem,
    ← P.add_mem_iff_left (a := x) ((inv_mem hσ) x), add_sub_cancel]
/-
**Ideal.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : Type*} [Ring R] (P : Ideal R) [MulSemiringAction M R] :
  (P.inertia (MulAction.stabilizer M P)).Normal := by
  refine (Subgroup.normal_subgroupOf_iff (inertia_le_stabilizer P)).mpr fun g s hg hs x ↦ ?_
  rw [Submodule.mem_toAddSubgroup, ← Ideal.smul_mem_pointwise_smul_iff (a := s⁻¹), smul_sub,
    smul_smul, ← mul_assoc, inv_mul_cancel_left, mul_smul, Subgroup.inv_mem _ hs]
  exact hg (s⁻¹ • x)

variable {N : Type*} [Group N] [MulSemiringAction N R]

/--
Assume that `M` and `N` are isomorphic and act in a compatible way on `R`, then for any
ideal `I` of `R`, the stabilizer of `I` in `M` is isomorphic to the stabilizer of `I` in `N`.
-/
/-
**Ideal.stabilizerEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：stabilizerEquiv (I : Ideal R) (e : M ≃* N) (he : forall (m : M) (x : R), (
e m) • x = m • x) : MulAction.stabilizer M I ≃* MulAction.stabilizer N I where t
oEquiv
参数：I : Ideal R；e : M ≃* N；he : forall (m : M) (x : R), (e m) • x = m • x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Assume that `M` and `N` are isomorphic and act in a compatible way on `R`, then 
for any
ideal `I` of `R`, the stabilizer of `I` in `M` is isomorphic to the stabilizer o
f `I` in `N`.
-/
def stabilizerEquiv (I : Ideal R) (e : M ≃* N) (he : ∀ (m : M) (x : R), (e m) • x = m • x) :
    MulAction.stabilizer M I ≃* MulAction.stabilizer N I where
  toEquiv := Equiv.subtypeEquiv e fun _ ↦ by
    simp [Ideal.ext_iff, Ideal.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, he]
  map_mul' _ _ := by simp

@[simp]
/-
**Ideal.stabilizerEquiv_apply_smul** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：stabilizerEquiv_apply_smul (I : Ideal R) (e : M ≃* N) (he : forall (m : M)
 (x : R), (e m) • x = m • x) (m : MulAction.stabilizer M I) (x : R) : stabilizer
Equiv I e he m • x = m • x
参数：I : Ideal R；e : M ≃* N；he : forall (m : M) (x : R), (e m) • x = m • x；m : Mul
Action.stabilizer M I；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.subtypeEquiv_apply`：∀ {α : Sort u_1} {β : Sort u_4} {p : α → Prop}
 {q : β → Prop} (e : α ≃ β) (h : ∀ (a : α), p a ↔ q (e a))   (a : { a // p a }),
 (e.subtypeEqu…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem stabilizerEquiv_apply_smul (I : Ideal R) (e : M ≃* N)
    (he : ∀ (m : M) (x : R), (e m) • x = m • x) (m : MulAction.stabilizer M I) (x : R) :
    stabilizerEquiv I e he m • x = m • x := by
  simp [stabilizerEquiv, MulAction.subgroup_smul_def, ← he m x]

@[simp]
/-
**Ideal.stabilizerEquiv_symm_apply_smul** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：stabilizerEquiv_symm_apply_smul (I : Ideal R) (e : M ≃* N) (he : forall (m
 : M) (x : R), (e m) • x = m • x) (n : MulAction.stabilizer N I) (x : R) : (stab
ilizerEquiv I e he).symm n • x = n • x
参数：I : Ideal R；e : M ≃* N；he : forall (m : M) (x : R), (e m) • x = m • x；n : Mul
Action.stabilizer N I；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulEquiv.apply_symm_apply`：apply_symm_apply (e : M ≃* N) (y : N) : e (e.
symm y) = y
· 使用定理 `Ideal.stabilizerEquiv_apply_smul`：stabilizerEquiv_apply_smul (I : Ideal 
R) (e : M ≃* N) (he : forall (m : M) (x : R), (e m) • x = m • x) (m : MulAction.
stabilizer M I) (x : R…
-/
theorem stabilizerEquiv_symm_apply_smul (I : Ideal R) (e : M ≃* N)
    (he : ∀ (m : M) (x : R), (e m) • x = m • x) (n : MulAction.stabilizer N I) (x : R) :
    (stabilizerEquiv I e he).symm n • x = n • x := by
  rw [← (stabilizerEquiv I e he).apply_symm_apply n, stabilizerEquiv_apply_smul,
    (stabilizerEquiv I e he).apply_symm_apply]

/--
Assume that `M` and `N` are isomorphic and act in a compatible way on `R`, then for any
ideal `I` of `R`, the inertia subgroup of `I` in `M` is isomorphic to the inertia subgroup
of `I` in `N`.
-/
/-
**Ideal.inertiaEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：inertiaEquiv {R : Type*} [Ring R] [MulSemiringAction M R] [MulSemiringActi
on N R] (I : Ideal R) (e : M ≃* N) (he : forall (m : M) (x : R), (e m) • x = m •
 x) : inertia M I ≃* inertia N I where toEquiv
参数：I : Ideal R；e : M ≃* N；he : forall (m : M) (x : R), (e m) • x = m • x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Assume that `M` and `N` are isomorphic and act in a compatible way on `R`, then 
for any
ideal `I` of `R`, the inertia subgroup of `I` in `M` is isomorphic to the inerti
a subgroup
of `I` in `N`.
-/
def inertiaEquiv {R : Type*} [Ring R] [MulSemiringAction M R] [MulSemiringAction N R] (I : Ideal R)
    (e : M ≃* N) (he : ∀ (m : M) (x : R), (e m) • x = m • x) :
    inertia M I ≃* inertia N I where
  toEquiv := Equiv.subtypeEquiv e fun _ ↦ by simp [he]
  map_mul' := by simp

@[simp]
/-
**Ideal.inertiaEquiv_apply_smul** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：inertiaEquiv_apply_smul {R : Type*} [Ring R] [MulSemiringAction M R] [MulS
emiringAction N R] (I : Ideal R) (e : M ≃* N) (he : forall (m : M) (x : R), (e m
) • x = m • x) (m : inertia M I) (x : R) : inertiaEquiv I e he m • x = m • x
参数：I : Ideal R；e : M ≃* N；he : forall (m : M) (x : R), (e m) • x = m • x；m : ine
rtia M I；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.subtypeEquiv_apply`：∀ {α : Sort u_1} {β : Sort u_4} {p : α → Prop}
 {q : β → Prop} (e : α ≃ β) (h : ∀ (a : α), p a ↔ q (e a))   (a : { a // p a }),
 (e.subtypeEqu…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inertiaEquiv_apply_smul {R : Type*} [Ring R] [MulSemiringAction M R] [MulSemiringAction N R]
    (I : Ideal R) (e : M ≃* N) (he : ∀ (m : M) (x : R), (e m) • x = m • x) (m : inertia M I)
    (x : R) :
    inertiaEquiv I e he m • x = m • x := by
  simp [inertiaEquiv, MulAction.subgroup_smul_def, ← he m x]

@[simp]
/-
**Ideal.inertiaEquiv_symm_apply_smul** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：inertiaEquiv_symm_apply_smul {R : Type*} [Ring R] [MulSemiringAction M R] 
[MulSemiringAction N R] (I : Ideal R) (e : M ≃* N) (he : forall (m : M) (x : R),
 (e m) • x = m • x) (n : inertia N I) (x : R) : (inertiaEquiv I e he).symm n • x
 = n • x
参数：I : Ideal R；e : M ≃* N；he : forall (m : M) (x : R), (e m) • x = m • x；n : ine
rtia N I；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulEquiv.apply_symm_apply`：apply_symm_apply (e : M ≃* N) (y : N) : e (e.
symm y) = y
· 使用定理 `Ideal.inertiaEquiv_apply_smul`：inertiaEquiv_apply_smul {R : Type*} [Ring
 R] [MulSemiringAction M R] [MulSemiringAction N R] (I : Ideal R) (e : M ≃* N) (
he : forall (m : M)…
-/
theorem inertiaEquiv_symm_apply_smul {R : Type*} [Ring R] [MulSemiringAction M R]
    [MulSemiringAction N R] (I : Ideal R) (e : M ≃* N) (he : ∀ (m : M) (x : R), (e m) • x = m • x)
    (n : inertia N I) (x : R) :
    (inertiaEquiv I e he).symm n • x = n • x := by
  rw [← (inertiaEquiv I e he).apply_symm_apply n, inertiaEquiv_apply_smul,
    (inertiaEquiv I e he).apply_symm_apply]

/-! TODO: add `equivSMul` like we have for subgroup. -/

end Group

end Ideal

