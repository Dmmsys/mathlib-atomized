/-
Copyright (c) 2022 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

/-! # Pointwise instances on `AffineSubspace`s

This file provides the additive action `AffineSubspace.pointwiseAddAction` in the
`Pointwise` locale.

-/

@[expose] public section


open Affine Pointwise

open Set

variable {M k V P V₁ P₁ V₂ P₂ : Type*}

namespace AffineSubspace
section Ring
variable [Ring k]
variable [AddCommGroup V] [Module k V] [AffineSpace V P]
variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]
variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

/-- The additive action on an affine subspace corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale. -/
@[instance_reducible]
/-
**AffineSubspace.pointwiseVAdd** 是 Mathlib 中的一个定义，位于命名空间 `AffineSubspace`。
形式化陈述：{k : Type u_2} →   {V : Type u_3} →     {P : Type u_4} →       [inst : Rin
g k] →         [inst_1 : AddCommGroup V] →           [inst_2 : _root_.Module k V
] → [inst_3 : AddTorsor V P] → VAdd V (AffineSubspace k P)
参数：AffineSubspace k P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The additive action on an affine subspace corresponding to applying the action t
o every element.

This is available as an instance in the `Pointwise` locale.
-/
protected def pointwiseVAdd : VAdd V (AffineSubspace k P) where
  vadd x s := s.map (AffineEquiv.constVAdd k P x)

scoped[Pointwise] attribute [instance] AffineSubspace.pointwiseVAdd
/-
**AffineSubspace.coe_pointwise_vadd** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：∀ {k : Type u_2} {V : Type u_3} {P : Type u_4} [inst : Ring k] [inst_1 : A
ddCommGroup V] [inst_2 : _root_.Module k V]   [inst_3 : AddTorsor V P] (v : V) (
s : AffineSubspace k P), ↑(v +ᵥ s) = v +ᵥ ↑s
参数：v : V；s : AffineSubspace k P；v +ᵥ s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_pointwise_vadd (v : V) (s : AffineSubspace k P) :
    ((v +ᵥ s : AffineSubspace k P) : Set P) = v +ᵥ (s : Set P) := rfl

/-- The additive action on an affine subspace corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale. -/
@[instance_reducible]
/-
**AffineSubspace.pointwiseAddAction** 是 Mathlib 中的一个定义，位于命名空间 `AffineSubspace`。
形式化陈述：{k : Type u_2} →   {V : Type u_3} →     {P : Type u_4} →       [inst : Rin
g k] →         [inst_1 : AddCommGroup V] →           [inst_2 : _root_.Module k V
] → [inst_3 : AddTorsor V P] → AddAction V (AffineSubspace k P)
参数：AffineSubspace k P。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.coe_pointwise_vadd`：∀ {k : Type u_2} {V : Type u_3} {P : 
Type u_4} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]
   [inst_3 : AddTorsor …

--- 原说明 ---
The additive action on an affine subspace corresponding to applying the action t
o every element.

This is available as an instance in the `Pointwise` locale.
-/
protected def pointwiseAddAction : AddAction V (AffineSubspace k P) :=
  SetLike.coe_injective.addAction _ coe_pointwise_vadd

scoped[Pointwise] attribute [instance] AffineSubspace.pointwiseAddAction
/-
**AffineSubspace.pointwise_vadd_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace
`。
形式化陈述：pointwise_vadd_eq_map (v : V) (s : AffineSubspace k P) : v +ᵥ s = s.map (A
ffineEquiv.constVAdd k P v)
参数：v : V；s : AffineSubspace k P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pointwise_vadd_eq_map (v : V) (s : AffineSubspace k P) :
    v +ᵥ s = s.map (AffineEquiv.constVAdd k P v) :=
  rfl
/-
**AffineSubspace.vadd_mem_pointwise_vadd_iff** 是 Mathlib 中的一个定理，位于命名空间 `AffineSu
bspace`。
形式化陈述：vadd_mem_pointwise_vadd_iff {v : V} {s : AffineSubspace k P} {p : P} : v +
ᵥ p in v +ᵥ s ↔ p in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.vadd_mem_vadd_set_iff`：∀ {α : Type u_2} {β : Type u_3} [inst : AddGr
oup α] [inst_1 : AddAction α β] {s : Set β} {a : α} {x : β},   a +ᵥ x ∈ a +ᵥ s ↔
 x ∈ s
-/
theorem vadd_mem_pointwise_vadd_iff {v : V} {s : AffineSubspace k P} {p : P} :
    v +ᵥ p ∈ v +ᵥ s ↔ p ∈ s :=
  vadd_mem_vadd_set_iff
/-
**AffineSubspace.pointwise_vadd_bot** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：∀ {k : Type u_2} {V : Type u_3} {P : Type u_4} [inst : Ring k] [inst_1 : A
ddCommGroup V] [inst_2 : _root_.Module k V]   [inst_3 : AddTorsor V P] (v : V), 
v +ᵥ ⊥ = ⊥
参数：v : V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.ext`：ext {p q : AffineSubspace k P} (h : forall x, x in p
 ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.map_bot`：map_bot : (⊥ : AffineSubspace k P₁).map f = ⊥
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem pointwise_vadd_bot (v : V) : v +ᵥ (⊥ : AffineSubspace k P) = ⊥ := by
  ext; simp [pointwise_vadd_eq_map, map_bot]
/-
**AffineSubspace.pointwise_vadd_top** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：∀ {k : Type u_2} {V : Type u_3} {P : Type u_4} [inst : Ring k] [inst_1 : A
ddCommGroup V] [inst_2 : _root_.Module k V]   [inst_3 : AddTorsor V P] (v : V), 
v +ᵥ ⊤ = ⊤
参数：v : V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.ext`：ext {p q : AffineSubspace k P} (h : forall x, x in p
 ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AffineEquiv.constVAdd_apply`：∀ (k : Type u_1) (P₁ : Type u_2) {V₁ : Type
 u_6} [inst : Ring k] [inst_1 : AddCommGroup V₁]   [inst_2 : _root_.Module k V₁]
 [inst_3 : AddTor…
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma pointwise_vadd_top (v : V) : v +ᵥ (⊤ : AffineSubspace k P) = ⊤ := by
  ext; simp [pointwise_vadd_eq_map, vadd_eq_iff_eq_neg_vadd]
/-
**AffineSubspace.pointwise_vadd_direction** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubsp
ace`。
形式化陈述：pointwise_vadd_direction (v : V) (s : AffineSubspace k P) : (v +ᵥ s).direc
tion = s.direction
参数：v : V；s : AffineSubspace k P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.pointwise_vadd_eq_map`：pointwise_vadd_eq_map (v : V) (s :
 AffineSubspace k P) : v +ᵥ s = s.map (AffineEquiv.constVAdd k P v)
· 使用定理 `AffineSubspace.map_direction`：map_direction (s : AffineSubspace k P₁) : 
(s.map f).direction = s.direction.map f.linear
· 使用定理 `Submodule.map_id`：map_id : map (LinearMap.id : M ->ₗ[R] M) p = p
-/
theorem pointwise_vadd_direction (v : V) (s : AffineSubspace k P) :
    (v +ᵥ s).direction = s.direction := by
  rw [pointwise_vadd_eq_map, map_direction]
  exact Submodule.map_id _
/-
**AffineSubspace.pointwise_vadd_span** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：pointwise_vadd_span (v : V) (s : Set P) : v +ᵥ affineSpan k s = affineSpan
 k (v +ᵥ s)
参数：v : V；s : Set P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.map_span`：map_span (s : Set P₁) : (affineSpan k s).map f 
= affineSpan k (f '' s)
-/
theorem pointwise_vadd_span (v : V) (s : Set P) : v +ᵥ affineSpan k s = affineSpan k (v +ᵥ s) :=
  map_span _ s
/-
**AffineSubspace.map_pointwise_vadd** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：map_pointwise_vadd (f : P₁ ->ᵃ[k] P₂) (v : V₁) (s : AffineSubspace k P₁) :
 (v +ᵥ s).map f = f.linear v +ᵥ s.map f
参数：f : P₁ ->ᵃ[k] P₂；v : V₁；s : AffineSubspace k P₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.pointwise_vadd_eq_map`：pointwise_vadd_eq_map (v : V) (s :
 AffineSubspace k P) : v +ᵥ s = s.map (AffineEquiv.constVAdd k P v)
· 使用定理 `AffineSubspace.map_map`：map_map (s : AffineSubspace k P₁) (f : P₁ ->ᵃ[k]
 P₂) (g : P₂ ->ᵃ[k] P₃) : (s.map f).map g = s.map (g.comp f)
· 使用定理 `AffineMap.ext`：ext {f g : P1 ->ᵃ[k] P2} (h : forall p, f p = g p) : f = 
g
· 使用定理 `AffineMap.map_vadd`：map_vadd (f : P1 ->ᵃ[k] P2) (p : P1) (v : V1) : f (v
 +ᵥ p) = f.linear v +ᵥ f p
-/
theorem map_pointwise_vadd (f : P₁ →ᵃ[k] P₂) (v : V₁) (s : AffineSubspace k P₁) :
    (v +ᵥ s).map f = f.linear v +ᵥ s.map f := by
  rw [pointwise_vadd_eq_map, pointwise_vadd_eq_map, map_map, map_map]
  congr 1
  ext
  exact f.map_vadd _ _

section SMul
variable [DistribSMul M V] [SMulCommClass M k V] {a : M} {s : AffineSubspace k V}
  {p : V}

/-- The multiplicative action on an affine subspace corresponding to applying the action to every
element.

This is available as an instance in the `Pointwise` locale.

TODO: generalize to include `SMul (P ≃ᵃ[k] P) (AffineSubspace k P)`, which acts on `P` with a
`VAdd` version of a `DistribMulAction`. -/
@[instance_reducible]
/-
**AffineSubspace.pointwiseSMul** 是 Mathlib 中的一个定义，位于命名空间 `AffineSubspace`。
形式化陈述：{M : Type u_1} →   {k : Type u_2} →     {V : Type u_3} →       [inst : Rin
g k] →         [inst_1 : AddCommGroup V] →           [inst_2 : _root_.Module k V
] →             [inst_3 : DistribSMul M V] → [SMulCommClass M k V] → SMul M (Aff
ineSubspace k V)
参数：AffineSubspace k V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplicative action on an affine subspace corresponding to applying the ac
tion to every
element.

This is available as an instance in the `Pointwise` locale.

TODO: generalize to include `SMul (P ≃ᵃ[k] P) (AffineSubspace k P)`, which acts 
on `P` with a
`VAdd` version of a `DistribMulAction`.
-/
protected def pointwiseSMul : SMul M (AffineSubspace k V) where
  smul a s := s.map (DistribSMul.toLinearMap k _ a).toAffineMap

scoped[Pointwise] attribute [instance] AffineSubspace.pointwiseSMul

@[simp, norm_cast]
/-
**AffineSubspace.coe_smul** 是 Mathlib 中的一个引理，位于命名空间 `AffineSubspace`。
形式化陈述：coe_smul (a : M) (s : AffineSubspace k V) : ↑(a • s) = a • (s : Set V)
参数：a : M；s : AffineSubspace k V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_smul (a : M) (s : AffineSubspace k V) : ↑(a • s) = a • (s : Set V) := rfl
/-
**AffineSubspace.smul_eq_map** 是 Mathlib 中的一个引理，位于命名空间 `AffineSubspace`。
形式化陈述：smul_eq_map (a : M) (s : AffineSubspace k V) : a • s = s.map (DistribSMul.
toLinearMap k _ a).toAffineMap
参数：a : M；s : AffineSubspace k V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smul_eq_map (a : M) (s : AffineSubspace k V) :
    a • s = s.map (DistribSMul.toLinearMap k _ a).toAffineMap := rfl
/-
**AffineSubspace.smul_mem_smul_iff** 是 Mathlib 中的一个引理，位于命名空间 `AffineSubspace`。
形式化陈述：smul_mem_smul_iff {G : Type*} [Group G] [DistribMulAction G V] [SMulCommCl
ass G k V] {a : G} : a • p in a • s ↔ p in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_mem_smul_set_iff`：smul_mem_smul_set_iff : a • x in a • s ↔ x in
 s
-/
lemma smul_mem_smul_iff {G : Type*} [Group G] [DistribMulAction G V] [SMulCommClass G k V] {a : G} :
    a • p ∈ a • s ↔ p ∈ s := smul_mem_smul_set_iff
/-
**AffineSubspace.smul_bot** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：∀ {M : Type u_1} {k : Type u_2} {V : Type u_3} [inst : Ring k] [inst_1 : A
ddCommGroup V] [inst_2 : _root_.Module k V]   [inst_3 : DistribSMul M V] [inst_4
 : SMulCommClass M k V] (a : M), a • ⊥ = ⊥
参数：a : M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.ext`：ext {p q : AffineSubspace k P} (h : forall x, x in p
 ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.map_bot`：map_bot : (⊥ : AffineSubspace k P₁).map f = ⊥
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma smul_bot (a : M) : a • (⊥ : AffineSubspace k V) = ⊥ := by
  ext; simp [smul_eq_map, map_bot]
/-
**AffineSubspace.smul_span** 是 Mathlib 中的一个引理，位于命名空间 `AffineSubspace`。
形式化陈述：smul_span (a : M) (s : Set V) : a • affineSpan k s = affineSpan k (a • s)
参数：a : M；s : Set V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.map_span`：map_span (s : Set P₁) : (affineSpan k s).map f 
= affineSpan k (f '' s)
-/
lemma smul_span (a : M) (s : Set V) : a • affineSpan k s = affineSpan k (a • s) := map_span _ s

end SMul

section MulAction
variable [Monoid M] [DistribMulAction M V] [SMulCommClass M k V] {a : M} {s : AffineSubspace k V}
  {p : V}

/-- The multiplicative action on an affine subspace corresponding to applying the action to every
element.

This is available as an instance in the `Pointwise` locale.

TODO: generalize to include `SMul (P ≃ᵃ[k] P) (AffineSubspace k P)`, which acts on `P` with a
`VAdd` version of a `DistribMulAction`. -/
@[instance_reducible]
/-
**AffineSubspace.mulAction** 是 Mathlib 中的一个定义，位于命名空间 `AffineSubspace`。
形式化陈述：{M : Type u_1} →   {k : Type u_2} →     {V : Type u_3} →       [inst : Rin
g k] →         [inst_1 : AddCommGroup V] →           [inst_2 : _root_.Module k V
] →             [inst_3 : Monoid M] →               [inst_4 : DistribMulAction M
 V] → [SMulCommClass M k V] → MulAction M (AffineSubspace k V)
参数：AffineSubspace k V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplicative action on an affine subspace corresponding to applying the ac
tion to every
element.

This is available as an instance in the `Pointwise` locale.

TODO: generalize to include `SMul (P ≃ᵃ[k] P) (AffineSubspace k P)`, which acts 
on `P` with a
`VAdd` version of a `DistribMulAction`.
-/
protected def mulAction : MulAction M (AffineSubspace k V) :=
  SetLike.coe_injective.mulAction _ coe_smul

scoped[Pointwise] attribute [instance] AffineSubspace.mulAction
/-
**AffineSubspace.smul_mem_smul_iff_of_isUnit** 是 Mathlib 中的一个引理，位于命名空间 `AffineSu
bspace`。
形式化陈述：smul_mem_smul_iff_of_isUnit (ha : IsUnit a) : a • p in a • s ↔ p in s
参数：ha : IsUnit a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AffineSubspace.smul_mem_smul_iff`：smul_mem_smul_iff {G : Type*} [Group G
] [DistribMulAction G V] [SMulCommClass G k V] {a : G} : a • p in a • s ↔ p in s
-/
lemma smul_mem_smul_iff_of_isUnit (ha : IsUnit a) : a • p ∈ a • s ↔ p ∈ s :=
  smul_mem_smul_iff (a := ha.unit)
/-
**AffineSubspace.smul_mem_smul_iff** 是 Mathlib 中的一个引理，位于命名空间 `AffineSubspace`。
形式化陈述：smul_mem_smul_iff {G : Type*} [Group G] [DistribMulAction G V] [SMulCommCl
ass G k V] {a : G} : a • p in a • s ↔ p in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_mem_smul_set_iff`：smul_mem_smul_set_iff : a • x in a • s ↔ x in
 s
-/
lemma smul_mem_smul_iff₀ {G₀ : Type*} [GroupWithZero G₀] [DistribMulAction G₀ V]
    [SMulCommClass G₀ k V] {a : G₀} (ha : a ≠ 0) : a • p ∈ a • s ↔ p ∈ s :=
  smul_mem_smul_iff_of_isUnit ha.isUnit
/-
**AffineSubspace.smul_top** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：∀ {M : Type u_1} {k : Type u_2} {V : Type u_3} [inst : Ring k] [inst_1 : A
ddCommGroup V] [inst_2 : _root_.Module k V]   [inst_3 : Monoid M] [inst_4 : Dist
ribMulAction M V] [inst_5 : SMulCommClass M k V] {a : M}, IsUnit a → a • ⊤ = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.ext`：ext {p q : AffineSubspace k P} (h : forall x, x in p
 ↔ x in q) : p = q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DistribSMul.toLinearMap_apply`：∀ (R : Type u_1) {S : Type u_3} (M : Type
 u_4) [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R
 M] [inst_3 : Distr…
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
-/
@[simp] lemma smul_top (ha : IsUnit a) : a • (⊤ : AffineSubspace k V) = ⊤ := by
  ext x; simpa [smul_eq_map, map_top] using ⟨ha.unit⁻¹ • x, smul_inv_smul ha.unit _⟩

end MulAction

end Ring

section Field
variable [Field k] [AddCommGroup V] [Module k V] {a : k}

@[simp]
/-
**AffineSubspace.direction_smul** 是 Mathlib 中的一个引理，位于命名空间 `AffineSubspace`。
形式化陈述：direction_smul (ha : a != 0) (s : AffineSubspace k V) : (a • s).direction 
= s.direction
参数：ha : a != 0；s : AffineSubspace k V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DistribSMul.toLinearMap_apply`：∀ (R : Type u_1) {S : Type u_3} (M : Type
 u_4) [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R
 M] [inst_3 : Distr…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AffineSubspace.map_direction`：map_direction (s : AffineSubspace k P₁) : 
(s.map f).direction = s.direction.map f.linear
· 使用定理 `Submodule.map_smul`：∀ {K : Type u_9} {V : Type u_10} {V₂ : Type u_11} [i
nst : Semifield K] [inst_1 : AddCommMonoid V]   [inst_2 : _root_.Module K V] [in
st_3 : A…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Submodule.map_id`：map_id : map (LinearMap.id : M ->ₗ[R] M) p = p
-/
lemma direction_smul (ha : a ≠ 0) (s : AffineSubspace k V) : (a • s).direction = s.direction := by
  have : DistribSMul.toLinearMap k V a = a • LinearMap.id := by
    ext; simp
  simp [smul_eq_map, map_direction, this, Submodule.map_smul, ha]

end Field
end AffineSubspace

