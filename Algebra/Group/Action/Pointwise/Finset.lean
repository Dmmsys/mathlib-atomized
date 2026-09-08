/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# Pointwise actions of finsets
-/

@[expose] public section

-- TODO
-- assert_not_exists MonoidWithZero
assert_not_exists Cardinal

open Function MulOpposite

open scoped Pointwise

variable {F α β γ : Type*}

namespace Finset

/-! ### Instances -/

section Instances

variable [DecidableEq γ]

@[to_additive]
/-
**Finset.smulCommClass_finset** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：smulCommClass_finset [SMul α γ] [SMul β γ] [SMulCommClass α β γ] : SMulCom
mClass α β (Finset γ)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Commute.finset_image`：∀ {α : Type u_1} [inst : DecidableEq α] {
f g : α → α},   Function.Commute f g → Function.Commute (Finset.image f) (Finset
.image g)
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
instance smulCommClass_finset [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass α β (Finset γ) :=
  ⟨fun _ _ => Commute.finset_image <| smul_comm _ _⟩

@[to_additive]
/-
**Finset.smulCommClass_finset'** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：smulCommClass_finset' [SMul α γ] [SMul β γ] [SMulCommClass α β γ] : SMulCo
mmClass α (Finset β) (Finset γ)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.coe_smul_finset`：coe_smul_finset (a : α) (s : Finset β) : ↑(a • s
) = a • (↑s : Set β)
· 使用引理 `Finset.coe_smul`：coe_smul (s : Finset α) (t : Finset β) : ↑(s • t) = (s 
: Set α) • (t : Set β)
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance smulCommClass_finset' [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass α (Finset β) (Finset γ) :=
  ⟨fun a s t => coe_injective <| by simp only [coe_smul_finset, coe_smul, smul_comm]⟩

@[to_additive]
/-
**Finset.smulCommClass_finset''** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：smulCommClass_finset'' [SMul α γ] [SMul β γ] [SMulCommClass α β γ] : SMulC
ommClass (Finset α) β (Finset γ)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
-/
instance smulCommClass_finset'' [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass (Finset α) β (Finset γ) :=
  haveI := SMulCommClass.symm α β γ
  SMulCommClass.symm _ _ _

@[to_additive]
/-
**Finset.smulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：smulCommClass [SMul α γ] [SMul β γ] [SMulCommClass α β γ] : SMulCommClass 
(Finset α) (Finset β) (Finset γ)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.coe_smul`：coe_smul (s : Finset α) (t : Finset β) : ↑(s • t) = (s 
: Set α) • (t : Set β)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance smulCommClass [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass (Finset α) (Finset β) (Finset γ) :=
  ⟨fun s t u => coe_injective <| by simp_rw [coe_smul, smul_comm]⟩

@[to_additive]
/-
**Finset.isScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：isScalarTower [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ] : IsS
calarTower α β (Finset γ)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `Finset.image_image`：image_image [DecidableEq γ] {g : β -> γ} : (s.image 
f).image g = s.image (g ∘ f)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance isScalarTower [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ] :
    IsScalarTower α β (Finset γ) :=
  ⟨fun a b s => by simp only [← image_smul, image_image, smul_assoc, Function.comp_def]⟩

variable [DecidableEq β]

@[to_additive]
/-
**Finset.isScalarTower'** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：isScalarTower' [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ] : Is
ScalarTower α (Finset β) (Finset γ)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.coe_smul`：coe_smul (s : Finset α) (t : Finset β) : ↑(s • t) = (s 
: Set α) • (t : Set β)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.coe_smul_finset`：coe_smul_finset (a : α) (s : Finset β) : ↑(a • s
) = a • (↑s : Set β)
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance isScalarTower' [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ] :
    IsScalarTower α (Finset β) (Finset γ) :=
  ⟨fun a s t => coe_injective <| by simp only [coe_smul_finset, coe_smul, smul_assoc]⟩

@[to_additive]
/-
**Finset.isScalarTower''** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：isScalarTower'' [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ] : I
sScalarTower (Finset α) (Finset β) (Finset γ)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.coe_smul`：coe_smul (s : Finset α) (t : Finset β) : ↑(s • t) = (s 
: Set α) • (t : Set β)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance isScalarTower'' [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ] :
    IsScalarTower (Finset α) (Finset β) (Finset γ) :=
  ⟨fun a s t => coe_injective <| by simp only [coe_smul, smul_assoc]⟩

@[to_additive]
/-
**Finset.isCentralScalar** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：isCentralScalar [SMul α β] [SMul αᵐᵒᵖ β] [IsCentralScalar α β] : IsCentral
Scalar α (Finset β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.coe_smul_finset`：coe_smul_finset (a : α) (s : Finset β) : ↑(a • s
) = a • (↑s : Set β)
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance isCentralScalar [SMul α β] [SMul αᵐᵒᵖ β] [IsCentralScalar α β] :
    IsCentralScalar α (Finset β) :=
  ⟨fun a s => coe_injective <| by simp only [coe_smul_finset, op_smul_eq_smul]⟩

/-- A multiplicative action of a monoid `α` on a type `β` gives a multiplicative action of
`Finset α` on `Finset β`. -/
@[to_additive (attr := instance_reducible)
      /-- An additive action of an additive monoid `α` on a type `β` gives an additive action
      of `Finset α` on `Finset β` -/]
/-
**Finset.mulAction** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} →     [DecidableEq β] → [inst : Decidabl
eEq α] → [inst_1 : Monoid α] → [MulAction α β] → MulAction (Finset α) (Finset β)
参数：Finset α；Finset β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def mulAction [DecidableEq α] [Monoid α] [MulAction α β] :
    MulAction (Finset α) (Finset β) where
  mul_smul _ _ _ := image₂_assoc mul_smul
  one_smul s := image₂_singleton_left.trans <| by simp_rw [one_smul, image_id']

/-- A multiplicative action of a monoid on a type `β` gives a multiplicative action on `Finset β`.
-/
@[to_additive (attr := instance_reducible)
      /-- An additive action of an additive monoid on a type `β` gives an additive action
      on `Finset β`. -/]
/-
**Finset.mulActionFinset** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：{α : Type u_2} → {β : Type u_3} → [DecidableEq β] → [inst : Monoid α] → [M
ulAction α β] → MulAction α (Finset β)
参数：Finset β。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
-/
protected def mulActionFinset [Monoid α] [MulAction α β] : MulAction α (Finset β) :=
  coe_injective.mulAction _ coe_smul_finset

scoped[Pointwise]
  attribute [instance]
    Finset.mulActionFinset Finset.addActionFinset Finset.mulAction Finset.addAction

end Instances

section Mul

variable [Mul α] [DecidableEq α] {s t u : Finset α} {a : α}

open scoped RightActions in
/-
**Finset.mul_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : Mul α] [inst_1 : DecidableEq α] {s : Finset α} (a
 : α), s * {a} = MulOpposite.op a • s
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_singleton_right`：image₂_singleton_right : image₂ f s {b} =
 s.image fun a => f a b
-/
@[to_additive] lemma mul_singleton (a : α) : s * {a} = s <• a := image₂_singleton_right
/-
**Finset.singleton_mul** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : Mul α] [inst_1 : DecidableEq α] {s : Finset α} (a
 : α), {a} * s = a • s
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_singleton_left`：image₂_singleton_left : image₂ f {a} t = t
.image fun b => f a b
-/
@[to_additive] lemma singleton_mul (a : α) : {a} * s = a • s := image₂_singleton_left
/-
**Finset.smul_finset_subset_mul** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : Mul α] [inst_1 : DecidableEq α] {s t : Finset α} 
{a : α}, a ∈ s → a • t ⊆ s * t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_subset_image₂_right`：image_subset_image₂_right (ha : a in s
) : t.image (fun b => f a b) subseteq image₂ f s t
-/
@[to_additive] lemma smul_finset_subset_mul : a ∈ s → a • t ⊆ s * t := image_subset_image₂_right

@[to_additive]
/-
**Finset.op_smul_finset_subset_mul** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：op_smul_finset_subset_mul : a in t -> op a • s subseteq s * t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_subset_image₂_left`：image_subset_image₂_left (hb : b in t) 
: s.image (fun a => f a b) subseteq image₂ f s t
-/
theorem op_smul_finset_subset_mul : a ∈ t → op a • s ⊆ s * t :=
  image_subset_image₂_left

@[to_additive (attr := simp)]
/-
**Finset.biUnion_op_smul_finset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：biUnion_op_smul_finset (s t : Finset α) : (t.biUnion fun a => op a • s) = 
s * t
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.biUnion_image_right`：biUnion_image_right : (t.biUnion fun b => s.
image fun a => f a b) = image₂ f s t
-/
theorem biUnion_op_smul_finset (s t : Finset α) : (t.biUnion fun a => op a • s) = s * t :=
  biUnion_image_right

@[to_additive]
/-
**Finset.mul_subset_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mul_subset_iff_left : s * t subseteq u ↔ forall a in s, a • t subseteq u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_subset_iff_left`：image₂_subset_iff_left : image₂ f s t sub
seteq u ↔ forall a in s, (t.image fun b => f a b) subseteq u
-/
theorem mul_subset_iff_left : s * t ⊆ u ↔ ∀ a ∈ s, a • t ⊆ u :=
  image₂_subset_iff_left

@[to_additive]
/-
**Finset.mul_subset_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mul_subset_iff_right : s * t subseteq u ↔ forall b in t, op b • s subseteq
 u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_subset_iff_right`：image₂_subset_iff_right : image₂ f s t s
ubseteq u ↔ forall b in t, (s.image fun a => f a b) subseteq u
-/
theorem mul_subset_iff_right : s * t ⊆ u ↔ ∀ b ∈ t, op b • s ⊆ u :=
  image₂_subset_iff_right

end Mul

section Semigroup

variable [Semigroup α] [DecidableEq α]

@[to_additive]
/-
**Finset.op_smul_finset_mul_eq_mul_smul_finset** 是 Mathlib 中的一个定理，位于命名空间 `Finset
`。
形式化陈述：op_smul_finset_mul_eq_mul_smul_finset (a : α) (s : Finset α) (t : Finset α
) : op a • s * t = s * a • t
参数：a : α；s : Finset α；t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.op_smul_finset_smul_eq_smul_smul_finset`：op_smul_finset_smul_eq_s
mul_smul_finset (a : α) (s : Finset β) (t : Finset γ) (h : forall (a : α) (b : β
) (c : γ), (op a • b) • c = b • a • …
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem op_smul_finset_mul_eq_mul_smul_finset (a : α) (s : Finset α) (t : Finset α) :
    op a • s * t = s * a • t :=
  op_smul_finset_smul_eq_smul_smul_finset _ _ _ fun _ _ _ => mul_assoc _ _ _

end Semigroup

section IsLeftCancelSMul
variable [SMul α β] [IsLeftCancelSMul α β] [DecidableEq β]

@[to_additive]
/-
**Finset.pairwiseDisjoint_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：pairwiseDisjoint_smul_iff {s : Set α} {t : Finset β} : s.PairwiseDisjoint 
(· • t) ↔ (s ×ˢ t : Set (α × β)).InjOn fun p => p.1 • p.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Finset.coe_smul_finset`：coe_smul_finset (a : α) (s : Finset β) : ↑(a • s
) = a • (↑s : Set β)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem pairwiseDisjoint_smul_iff {s : Set α} {t : Finset β} :
    s.PairwiseDisjoint (· • t) ↔ (s ×ˢ t : Set (α × β)).InjOn fun p => p.1 • p.2 := by
  simp_rw [← pairwiseDisjoint_coe, coe_smul_finset, Set.pairwiseDisjoint_smul_iff]

end IsLeftCancelSMul

@[to_additive]
/-
**Finset.image_smul_distrib** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_smul_distrib [DecidableEq α] [DecidableEq β] [Mul α] [Mul β] [FunLik
e F α β] [MulHomClass F α β] (f : F) (a : α) (s : Finset α) : (a • s).image f = 
f a • s.image f
参数：f : F；a : α；s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_comm`：image_comm {β'} [DecidableEq β'] [DecidableEq γ] {f :
 β -> γ} {g : α -> β} {f' : α -> β'} {g' : β' -> γ} (h_comm : forall a, f (g a) 
= g' (f…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
-/
theorem image_smul_distrib [DecidableEq α] [DecidableEq β] [Mul α] [Mul β] [FunLike F α β]
    [MulHomClass F α β] (f : F) (a : α) (s : Finset α) : (a • s).image f = f a • s.image f :=
  image_comm <| map_mul _ _

section Group

variable [DecidableEq β] [Group α] [MulAction α β] {s t : Finset β} {a : α} {b : β}

@[to_additive (attr := simp)]
/-
**Finset.smul_mem_smul_finset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：smul_mem_smul_finset_iff (a : α) : a • b in a • s ↔ b in s
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.mem_finset_image`：∀ {α : Type u_1} {β : Type u_2} [in
st : DecidableEq β] {f : α → β} {s : Finset α} {a : α},   Function.Injective f →
 (f a ∈ Finset.image f s …
· 使用定理 `MulAction.injective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Injective fun x => g • x
-/
theorem smul_mem_smul_finset_iff (a : α) : a • b ∈ a • s ↔ b ∈ s :=
  (MulAction.injective _).mem_finset_image

@[to_additive (attr := simp)]
/-
**Finset.mul_mem_smul_finset_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mul_mem_smul_finset_iff [DecidableEq α] (a : α) {b : α} {s : Finset α} : a
 * b in a • s ↔ b in s
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.smul_mem_smul_finset_iff`：smul_mem_smul_finset_iff (a : α) : a • 
b in a • s ↔ b in s
-/
lemma mul_mem_smul_finset_iff [DecidableEq α] (a : α) {b : α} {s : Finset α} :
    a * b ∈ a • s ↔ b ∈ s := smul_mem_smul_finset_iff _

@[to_additive]
/-
**Finset.inv_smul_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inv_smul_mem_iff : a⁻¹ • b in s ↔ b in a • s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.smul_mem_smul_finset_iff`：smul_mem_smul_finset_iff (a : α) : a • 
b in a • s ↔ b in s
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inv_smul_mem_iff : a⁻¹ • b ∈ s ↔ b ∈ a • s := by
  rw [← smul_mem_smul_finset_iff a, smul_inv_smul]

@[to_additive]
/-
**Finset.mem_inv_smul_finset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_inv_smul_finset_iff : b in a⁻¹ • s ↔ a • b in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.smul_mem_smul_finset_iff`：smul_mem_smul_finset_iff (a : α) : a • 
b in a • s ↔ b in s
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_inv_smul_finset_iff : b ∈ a⁻¹ • s ↔ a • b ∈ s := by
  rw [← smul_mem_smul_finset_iff a, smul_inv_smul]

@[to_additive (attr := simp)]
/-
**Finset.smul_finset_subset_smul_finset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：smul_finset_subset_smul_finset_iff : a • s subseteq a • t ↔ s subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_subset_image_iff`：image_subset_image_iff {t : Finset α} (hf
 : Injective f) : s.image f subseteq t.image f ↔ s subseteq t
· 使用定理 `MulAction.injective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Injective fun x => g • x
-/
theorem smul_finset_subset_smul_finset_iff : a • s ⊆ a • t ↔ s ⊆ t :=
  image_subset_image_iff <| MulAction.injective _

@[to_additive]
/-
**Finset.smul_finset_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：smul_finset_subset_iff : a • s subseteq t ↔ s subseteq a⁻¹ • t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.coe_smul_finset`：coe_smul_finset (a : α) (s : Finset β) : ↑(a • s
) = a • (↑s : Set β)
· 使用定理 `Set.smul_set_subset_iff_subset_inv_smul_set`：smul_set_subset_iff_subset_
inv_smul_set : a • A subseteq B ↔ A subseteq a⁻¹ • B
-/
theorem smul_finset_subset_iff : a • s ⊆ t ↔ s ⊆ a⁻¹ • t := by
  simp_rw [← coe_subset]
  push_cast
  exact Set.smul_set_subset_iff_subset_inv_smul_set

@[to_additive]
/-
**Finset.subset_smul_finset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：subset_smul_finset_iff : s subseteq a • t ↔ a⁻¹ • s subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.coe_smul_finset`：coe_smul_finset (a : α) (s : Finset β) : ↑(a • s
) = a • (↑s : Set β)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.subset_smul_set_iff`：subset_smul_set_iff : A subseteq a • B ↔ a⁻¹ • 
A subseteq B
-/
theorem subset_smul_finset_iff : s ⊆ a • t ↔ a⁻¹ • s ⊆ t := by
  simp_rw [← coe_subset]
  push_cast
  exact Set.subset_smul_set_iff

@[to_additive]
/-
**Finset.smul_finset_inter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：smul_finset_inter : a • (s inter t) = a • s inter a • t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_inter`：image_inter [DecidableEq α] (s₁ s₂ : Finset α) (hf :
 Injective f) : (s₁ inter s₂).image f = s₁.image f inter s₂.image f
· 使用定理 `MulAction.injective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Injective fun x => g • x
-/
theorem smul_finset_inter : a • (s ∩ t) = a • s ∩ a • t :=
  image_inter _ _ <| MulAction.injective a

@[to_additive]
/-
**Finset.smul_finset_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：smul_finset_sdiff : a • (s \ t) = a • s \ a • t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_sdiff`：image_sdiff [DecidableEq α] {f : α -> β} (s t : Fins
et α) (hf : Injective f) : (s \ t).image f = s.image f \ t.image f
· 使用定理 `MulAction.injective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Injective fun x => g • x
-/
theorem smul_finset_sdiff : a • (s \ t) = a • s \ a • t :=
  image_sdiff _ _ <| MulAction.injective a

open scoped symmDiff in
@[to_additive]
/-
**Finset.smul_finset_symmDiff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：smul_finset_symmDiff : a • s ∆ t = (a • s) ∆ (a • t)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_symmDiff`：image_symmDiff [DecidableEq β] {f : α -> β} (s t 
: Finset α) (hf : Injective f) : (s ∆ t).image f = s.image f ∆ t.image f
· 使用定理 `MulAction.injective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Injective fun x => g • x
-/
theorem smul_finset_symmDiff : a • s ∆ t = (a • s) ∆ (a • t) :=
  image_symmDiff _ _ <| MulAction.injective a

@[to_additive (attr := simp)]
/-
**Finset.smul_finset_univ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：smul_finset_univ [Fintype β] : a • (univ : Finset β) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_univ_of_surjective`：image_univ_of_surjective [Fintype β] {f
 : β -> α} (hf : Surjective f) : univ.image f = univ
· 使用定理 `MulAction.surjective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [
inst_1 : MulAction α β] (g : α), Function.Surjective fun x => g • x
-/
theorem smul_finset_univ [Fintype β] : a • (univ : Finset β) = univ :=
  image_univ_of_surjective <| MulAction.surjective a

@[to_additive (attr := simp)]
/-
**Finset.smul_finset_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：smul_finset_eq_univ [Fintype β] : a • s = univ ↔ s = univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_eq_iff_eq_inv_smul`：smul_eq_iff_eq_inv_smul (g : α) {x y : β} : g •
 x = y ↔ x = g⁻¹ • y
· 使用定理 `Finset.smul_finset_univ`：smul_finset_univ [Fintype β] : a • (univ : Fins
et β) = univ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem smul_finset_eq_univ [Fintype β] : a • s = univ ↔ s = univ := by
  rw [smul_eq_iff_eq_inv_smul, smul_finset_univ]

@[to_additive (attr := simp)]
/-
**Finset.smul_univ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：smul_univ [Fintype β] {s : Finset α} (hs : s.Nonempty) : s • (univ : Finse
t β) = univ
参数：hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.coe_smul`：coe_smul (s : Finset α) (t : Finset β) : ↑(s • t) = (s 
: Set α) • (t : Set β)
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Set.smul_univ`：smul_univ {s : Set α} (hs : s.Nonempty) : s • (univ : Set
 β) = univ
-/
theorem smul_univ [Fintype β] {s : Finset α} (hs : s.Nonempty) : s • (univ : Finset β) = univ :=
  coe_injective <| by
    push_cast
    exact Set.smul_univ hs

@[to_additive (attr := simp)]
/-
**Finset.card_smul_finset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_smul_finset (a : α) (s : Finset β) : (a • s).card = s.card
参数：a : α；s : Finset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_image_of_injective`：card_image_of_injective [DecidableEq β] 
(s : Finset α) (H : Injective f) : #(s.image f) = #s
· 使用定理 `MulAction.injective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Injective fun x => g • x
-/
theorem card_smul_finset (a : α) (s : Finset β) : (a • s).card = s.card :=
  card_image_of_injective _ <| MulAction.injective _

/-- If the left cosets of `t` by elements of `s` are disjoint (but not necessarily distinct!), then
the size of `t` divides the size of `s • t`. -/
@[to_additive /-- If the left cosets of `t` by elements of `s` are disjoint (but not necessarily
distinct!), then the size of `t` divides the size of `s +ᵥ t`. -/]
/-
**Finset.card_dvd_card_smul_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_dvd_card_smul_right {s : Finset α} : ((· • t) '' (s : Set α)).Pairwis
eDisjoint id -> t.card ∣ (s • t).card
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_dvd_card_image₂_right`：card_dvd_card_image₂_right (hf : fora
ll a in s, Injective (f a)) (hs : ((fun a => t.image <| f a) '' s).PairwiseDisjo
int id) : #t ∣ #(image₂…
· 使用定理 `MulAction.injective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Injective fun x => g • x
-/
theorem card_dvd_card_smul_right {s : Finset α} :
    ((· • t) '' (s : Set α)).PairwiseDisjoint id → t.card ∣ (s • t).card :=
  card_dvd_card_image₂_right fun _ _ => MulAction.injective _

variable [DecidableEq α]

/-- If the right cosets of `s` by elements of `t` are disjoint (but not necessarily distinct!), then
the size of `s` divides the size of `s * t`. -/
@[to_additive /-- If the right cosets of `s` by elements of `t` are disjoint (but not necessarily
distinct!), then the size of `s` divides the size of `s + t`. -/]
/-
**Finset.card_dvd_card_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_dvd_card_mul_left {s t : Finset α} : ((fun b => s.image fun a => a * 
b) '' (t : Set α)).PairwiseDisjoint id -> s.card ∣ (s * t).card
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_dvd_card_image₂_left`：card_dvd_card_image₂_left (hf : forall
 b in t, Injective fun a => f a b) (ht : ((fun b => s.image fun a => f a b) '' t
).PairwiseDisjoint id)…
· 使用定理 `mul_left_injective`：mul_left_injective (a : G) : Function.Injective (· *
 a)
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
-/
theorem card_dvd_card_mul_left {s t : Finset α} :
    ((fun b => s.image fun a => a * b) '' (t : Set α)).PairwiseDisjoint id →
      s.card ∣ (s * t).card :=
  card_dvd_card_image₂_left fun _ _ => mul_left_injective _

/-- If the left cosets of `t` by elements of `s` are disjoint (but not necessarily distinct!), then
the size of `t` divides the size of `s * t`. -/
@[to_additive /-- If the left cosets of `t` by elements of `s` are disjoint (but not necessarily
distinct!), then the size of `t` divides the size of `s + t`. -/]
/-
**Finset.card_dvd_card_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_dvd_card_mul_right {s t : Finset α} : ((· • t) '' (s : Set α)).Pairwi
seDisjoint id -> t.card ∣ (s * t).card
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_dvd_card_image₂_right`：card_dvd_card_image₂_right (hf : fora
ll a in s, Injective (f a)) (hs : ((fun a => t.image <| f a) '' s).PairwiseDisjo
int id) : #t ∣ #(image₂…
· 使用定理 `mul_right_injective`：mul_right_injective (a : G) : Injective (a * ·)
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
-/
theorem card_dvd_card_mul_right {s t : Finset α} :
    ((· • t) '' (s : Set α)).PairwiseDisjoint id → t.card ∣ (s * t).card :=
  card_dvd_card_image₂_right fun _ _ => mul_right_injective _

@[to_additive (attr := simp)]
/-
**Finset.inv_smul_finset_distrib** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：inv_smul_finset_distrib (a : α) (s : Finset α) : (a • s)⁻¹ = op a⁻¹ • s⁻¹
参数：a : α；s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma inv_smul_finset_distrib (a : α) (s : Finset α) : (a • s)⁻¹ = op a⁻¹ • s⁻¹ := by
  ext; simp [← inv_smul_mem_iff]

@[to_additive (attr := simp)]
/-
**Finset.inv_op_smul_finset_distrib** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：inv_op_smul_finset_distrib (a : α) (s : Finset α) : (op a • s)⁻¹ = a⁻¹ • s
⁻¹
参数：a : α；s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma inv_op_smul_finset_distrib (a : α) (s : Finset α) : (op a • s)⁻¹ = a⁻¹ • s⁻¹ := by
  ext; simp [← inv_smul_mem_iff]

end Group
end Finset

namespace Fintype
variable {ι : Type*} {α β : ι → Type*} [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (β i)]

@[to_additive]
/-
**Fintype.piFinset_smul** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：piFinset_smul [forall i, SMul (α i) (β i)] (s : forall i, Finset (α i)) (t
 : forall i, Finset (β i)) : piFinset (fun i => s i • t i) = piFinset s • piFins
et t
参数：α i；β i；s : forall i, Finset (α i)；t : forall i, Finset (β i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fintype.piFinset_image₂`：piFinset_image₂ (f : forall i, α i -> β i -> γ 
i) (s : forall i, Finset (α i)) (t : forall i, Finset (β i)) : piFinset (fun i =
> image₂ (f i…
-/
lemma piFinset_smul [∀ i, SMul (α i) (β i)] (s : ∀ i, Finset (α i)) (t : ∀ i, Finset (β i)) :
    piFinset (fun i ↦ s i • t i) = piFinset s • piFinset t := piFinset_image₂ _ _ _

@[to_additive]
/-
**Fintype.piFinset_smul_finset** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：piFinset_smul_finset [forall i, SMul (α i) (β i)] (a : forall i, α i) (s :
 forall i, Finset (β i)) : piFinset (fun i => a i • s i) = a • piFinset s
参数：α i；β i；a : forall i, α i；s : forall i, Finset (β i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fintype.piFinset_image`：piFinset_image [forall a, DecidableEq (δ a)] (f 
: forall a, γ a -> δ a) (s : forall a, Finset (γ a)) : piFinset (fun a => (s a).
image (f a))…
-/
lemma piFinset_smul_finset [∀ i, SMul (α i) (β i)] (a : ∀ i, α i) (s : ∀ i, Finset (β i)) :
    piFinset (fun i ↦ a i • s i) = a • piFinset s := piFinset_image _ _

-- Note: We don't currently state `piFinset_vsub` because there's no
-- `[∀ i, VSub (β i) (α i)] → VSub (∀ i, β i) (∀ i, α i)` instance

end Fintype

/-
**Nat.decidablePred_mem_vadd_set** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Nat.decidablePred_mem_vadd_set {s : Set Nat} [DecidablePred (· in s)] (a :
 Nat) : DecidablePred (· in a +ᵥ s)
参数：· in s；a : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Nat.decidablePred_mem_vadd_set {s : Set ℕ} [DecidablePred (· ∈ s)] (a : ℕ) :
    DecidablePred (· ∈ a +ᵥ s) :=
  fun n ↦ decidable_of_iff' (a ≤ n ∧ n - a ∈ s) <| by
    simp only [Set.mem_vadd_set, vadd_eq_add]; aesop
