/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Algebra.Order.Pi
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Data.DFinsupp.Module

/-!
# Pointwise order on finitely supported dependent functions

This file lifts order structures on the `α i` to `Π₀ i, α i`.

## Main declarations

* `DFinsupp.orderEmbeddingToFun`: The order embedding from finitely supported dependent functions
  to functions.

-/

@[expose] public section

open Finset

variable {ι : Type*} {α : ι → Type*}

namespace DFinsupp

/-! ### Order structures -/


section Zero
variable [∀ i, Zero (α i)]

section LE
variable [∀ i, LE (α i)] {f g : Π₀ i, α i}

/-
**DFinsupp.** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LE (Π₀ i, α i) :=
  ⟨fun f g ↦ ∀ i, f i ≤ g i⟩
/-
**DFinsupp.le_def** 是 Mathlib 中的一个引理，位于命名空间 `DFinsupp`。
形式化陈述：le_def : f <= g ↔ forall i, f i <= g i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma le_def : f ≤ g ↔ ∀ i, f i ≤ g i := Iff.rfl
/-
**DFinsupp.coe_le_coe** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι) → Zero (α i)] [inst_1 
: (i : ι) → LE (α i)] {f g : Π₀ (i : ι), α i},   ⇑f ≤ ⇑g ↔ f ≤ g
参数：i : ι；α i；i : ι；α i；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, norm_cast] lemma coe_le_coe : ⇑f ≤ g ↔ f ≤ g := Iff.rfl

/-- The order on `DFinsupp`s over a partial order embeds into the order on functions -/
/-
**DFinsupp.orderEmbeddingToFun** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：orderEmbeddingToFun : (Π₀ i, α i) ↪o forall i, α i where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The order on `DFinsupp`s over a partial order embeds into the order on functions
-/
def orderEmbeddingToFun : (Π₀ i, α i) ↪o ∀ i, α i where
  toFun := DFunLike.coe
  inj' := DFunLike.coe_injective
  map_rel_iff' := Iff.rfl

@[simp, norm_cast]
/-
**DFinsupp.coe_orderEmbeddingToFun** 是 Mathlib 中的一个引理，位于命名空间 `DFinsupp`。
形式化陈述：coe_orderEmbeddingToFun : ⇑(orderEmbeddingToFun (α
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_orderEmbeddingToFun : ⇑(orderEmbeddingToFun (α := α)) = DFunLike.coe := rfl
/-
**DFinsupp.orderEmbeddingToFun_apply** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：orderEmbeddingToFun_apply {f : Π₀ i, α i} {i : ι} : orderEmbeddingToFun f 
i = f i
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem orderEmbeddingToFun_apply {f : Π₀ i, α i} {i : ι} :
    orderEmbeddingToFun f i = f i :=
  rfl

end LE

section Preorder
variable [∀ i, Preorder (α i)] {f g : Π₀ i, α i} {i : ι} {a b : α i}

/-
**DFinsupp.** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Preorder (Π₀ i, α i) :=
  { (inferInstance : LE (DFinsupp α)) with
    le_refl := fun _ _ ↦ le_rfl
    le_trans := fun _ _ _ hfg hgh i ↦ (hfg i).trans (hgh i) }
/-
**DFinsupp.lt_def** 是 Mathlib 中的一个引理，位于命名空间 `DFinsupp`。
形式化陈述：lt_def : f < g ↔ f <= g ∧ exists i, f i < g i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.lt_def`：Pi.lt_def [forall i, Preorder (π i)] {x y : forall i, π i} : 
x < y ↔ x <= y ∧ exists i, x i < y i
-/
lemma lt_def : f < g ↔ f ≤ g ∧ ∃ i, f i < g i := Pi.lt_def
/-
**DFinsupp.coe_lt_coe** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι) → Zero (α i)] [inst_1 
: (i : ι) → Preorder (α i)]   {f g : Π₀ (i : ι), α i}, ⇑f < ⇑g ↔ f < g
参数：i : ι；α i；i : ι；α i；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, norm_cast] lemma coe_lt_coe : ⇑f < g ↔ f < g := Iff.rfl
/-
**DFinsupp.coe_mono** 是 Mathlib 中的一个引理，位于命名空间 `DFinsupp`。
形式化陈述：coe_mono : Monotone ((⇑) : (Π₀ i, α i) -> forall i, α i)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_mono : Monotone ((⇑) : (Π₀ i, α i) → ∀ i, α i) := fun _ _ ↦ id
/-
**DFinsupp.coe_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `DFinsupp`。
形式化陈述：coe_strictMono : Monotone ((⇑) : (Π₀ i, α i) -> forall i, α i)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_strictMono : Monotone ((⇑) : (Π₀ i, α i) → ∀ i, α i) := fun _ _ ↦ id

variable [DecidableEq ι]
/-
**DFinsupp.single_le_single** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι) → Zero (α i)] [inst_1 
: (i : ι) → Preorder (α i)] {i : ι}   {a b : α i} [inst_2 : DecidableEq ι], ((fu
n₀ | i => a) ≤ fun₀ | i => b) ↔ a ≤ b
参数：i : ι；α i；i : ι；α i；(fun₀ | i => a) ≤ fun₀ | i => b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.single_le_single`：∀ {ι : Type u_6} {α : ι → Type u_7} [inst : Decidab
leEq ι] [inst_1 : (i : ι) → Zero (α i)]   [inst_2 : (i : ι) → Preorder (α i)] {i
 : ι} {a …
-/
@[simp, gcongr] lemma single_le_single : single i a ≤ single i b ↔ a ≤ b :=
  Pi.single_le_single
/-
**DFinsupp.single_mono** 是 Mathlib 中的一个引理，位于命名空间 `DFinsupp`。
形式化陈述：single_mono : Monotone (single i : α i -> Π₀ i, α i)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `DFinsupp.single_le_single`：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (
i : ι) → Zero (α i)] [inst_1 : (i : ι) → Preorder (α i)] {i : ι}   {a b : α i} [
inst_2 : Decida…
-/
lemma single_mono : Monotone (single i : α i → Π₀ i, α i) := fun _ _ ↦ single_le_single.2
/-
**DFinsupp.single_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι) → Zero (α i)] [inst_1 
: (i : ι) → Preorder (α i)] {i : ι} {a : α i}   [inst_2 : DecidableEq ι], (0 ≤ f
un₀ | i => a) ↔ 0 ≤ a
参数：i : ι；α i；i : ι；α i；0 ≤ fun₀ | i => a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.single_nonneg`：∀ {ι : Type u_6} {α : ι → Type u_7} [inst : DecidableE
q ι] [inst_1 : (i : ι) → Zero (α i)]   [inst_2 : (i : ι) → Preorder (α i)] {i : 
ι} {a …
-/
@[simp] lemma single_nonneg : 0 ≤ single i a ↔ 0 ≤ a := Pi.single_nonneg
/-
**DFinsupp.single_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι) → Zero (α i)] [inst_1 
: (i : ι) → Preorder (α i)] {i : ι} {a : α i}   [inst_2 : DecidableEq ι], (fun₀ 
| i => a) ≤ 0 ↔ a ≤ 0
参数：i : ι；α i；i : ι；α i；fun₀ | i => a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.single_nonpos`：∀ {ι : Type u_6} {α : ι → Type u_7} [inst : DecidableE
q ι] [inst_1 : (i : ι) → Zero (α i)]   [inst_2 : (i : ι) → Preorder (α i)] {i : 
ι} {a …
-/
@[simp] lemma single_nonpos : single i a ≤ 0 ↔ a ≤ 0 := Pi.single_nonpos

end Preorder

/-
**DFinsupp.** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, PartialOrder (α i)] : PartialOrder (Π₀ i, α i) :=
  { (inferInstance : Preorder (DFinsupp α)) with
    le_antisymm := fun _ _ hfg hgf ↦ ext fun i ↦ (hfg i).antisymm (hgf i) }
/-
**DFinsupp.** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, SemilatticeInf (α i)] : SemilatticeInf (Π₀ i, α i) :=
  { (inferInstance : PartialOrder (DFinsupp α)) with
    inf := zipWith (fun _ ↦ (· ⊓ ·)) fun _ ↦ inf_idem _
    inf_le_left := fun _ _ _ ↦ inf_le_left
    inf_le_right := fun _ _ _ ↦ inf_le_right
    le_inf := fun _ _ _ hf hg i ↦ le_inf (hf i) (hg i) }

@[simp, norm_cast]
/-
**DFinsupp.coe_inf** 是 Mathlib 中的一个引理，位于命名空间 `DFinsupp`。
形式化陈述：coe_inf [forall i, SemilatticeInf (α i)] (f g : Π₀ i, α i) : f ⊓ g = ⇑f ⊓ 
g
参数：α i；f g : Π₀ i, α i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_inf [∀ i, SemilatticeInf (α i)] (f g : Π₀ i, α i) : f ⊓ g = ⇑f ⊓ g := rfl
/-
**DFinsupp.inf_apply** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：inf_apply [forall i, SemilatticeInf (α i)] (f g : Π₀ i, α i) (i : ι) : (f 
⊓ g) i = f i ⊓ g i
参数：α i；f g : Π₀ i, α i；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.zipWith_apply`：zipWith_apply (f : forall i, β₁ i -> β₂ i -> β i
) (hf : forall i, f i 0 0 = 0) (g₁ : Π₀ i, β₁ i) (g₂ : Π₀ i, β₂ i) (i : ι) : zip
With f hf g₁…
-/
theorem inf_apply [∀ i, SemilatticeInf (α i)] (f g : Π₀ i, α i) (i : ι) : (f ⊓ g) i = f i ⊓ g i :=
  zipWith_apply _ _ _ _ _
/-
**DFinsupp.** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, SemilatticeSup (α i)] : SemilatticeSup (Π₀ i, α i) :=
  { (inferInstance : PartialOrder (DFinsupp α)) with
    sup := zipWith (fun _ ↦ (· ⊔ ·)) fun _ ↦ sup_idem _
    le_sup_left := fun _ _ _ ↦ le_sup_left
    le_sup_right := fun _ _ _ ↦ le_sup_right
    sup_le := fun _ _ _ hf hg i ↦ sup_le (hf i) (hg i) }

@[simp, norm_cast]
/-
**DFinsupp.coe_sup** 是 Mathlib 中的一个引理，位于命名空间 `DFinsupp`。
形式化陈述：coe_sup [forall i, SemilatticeSup (α i)] (f g : Π₀ i, α i) : f ⊔ g = ⇑f ⊔ 
g
参数：α i；f g : Π₀ i, α i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_sup [∀ i, SemilatticeSup (α i)] (f g : Π₀ i, α i) : f ⊔ g = ⇑f ⊔ g := rfl
/-
**DFinsupp.sup_apply** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：sup_apply [forall i, SemilatticeSup (α i)] (f g : Π₀ i, α i) (i : ι) : (f 
⊔ g) i = f i ⊔ g i
参数：α i；f g : Π₀ i, α i；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.zipWith_apply`：zipWith_apply (f : forall i, β₁ i -> β₂ i -> β i
) (hf : forall i, f i 0 0 = 0) (g₁ : Π₀ i, β₁ i) (g₂ : Π₀ i, β₂ i) (i : ι) : zip
With f hf g₁…
-/
theorem sup_apply [∀ i, SemilatticeSup (α i)] (f g : Π₀ i, α i) (i : ι) : (f ⊔ g) i = f i ⊔ g i :=
  zipWith_apply _ _ _ _ _

section Lattice
variable [∀ i, Lattice (α i)] (f g : Π₀ i, α i)

/-
**DFinsupp.lattice** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
形式化陈述：lattice : Lattice (Π₀ i, α i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance lattice : Lattice (Π₀ i, α i) :=
  { (inferInstance : SemilatticeInf (DFinsupp α)),
    (inferInstance : SemilatticeSup (DFinsupp α)) with }

variable [DecidableEq ι] [∀ (i) (x : α i), Decidable (x ≠ 0)]
/-
**DFinsupp.support_inf_union_support_sup** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：support_inf_union_support_sup : (f ⊓ g).support union (f ⊔ g).support = f.
support union g.support
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `compl_injective`：compl_injective : Function.Injective (compl : α -> α)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `Set.compl_union`：compl_union (s t : Set α) : (s union t)ᶜ = sᶜ inter tᶜ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem support_inf_union_support_sup : (f ⊓ g).support ∪ (f ⊔ g).support = f.support ∪ g.support :=
  coe_injective <| compl_injective <| by ext; simp [inf_eq_and_sup_eq_iff]
/-
**DFinsupp.support_sup_union_support_inf** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：support_sup_union_support_inf : (f ⊔ g).support union (f ⊓ g).support = f.
support union g.support
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.union_comm`：union_comm (s₁ s₂ : Finset α) : s₁ union s₂ = s₂ unio
n s₁
· 使用定理 `DFinsupp.support_inf_union_support_sup`：support_inf_union_support_sup : 
(f ⊓ g).support union (f ⊔ g).support = f.support union g.support
-/
theorem support_sup_union_support_inf : (f ⊔ g).support ∪ (f ⊓ g).support = f.support ∪ g.support :=
  (union_comm _ _).trans <| support_inf_union_support_sup _ _

end Lattice
end Zero

/-! ### Algebraic order structures -/

/-
**DFinsupp.** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Algebraic order structures
-/
instance (α : ι → Type*) [∀ i, AddCommMonoid (α i)] [∀ i, PartialOrder (α i)]
    [∀ i, IsOrderedAddMonoid (α i)] : IsOrderedAddMonoid (Π₀ i, α i) :=
  { add_le_add_left := fun _ _ h c i ↦ add_le_add_left (h i) (c i) }
/-
**DFinsupp.** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : ι → Type*) [∀ i, AddCommMonoid (α i)] [∀ i, PartialOrder (α i)]
    [∀ i, IsOrderedCancelAddMonoid (α i)] :
    IsOrderedCancelAddMonoid (Π₀ i, α i) :=
  { le_of_add_le_add_left := fun _ _ _ H i ↦ le_of_add_le_add_left (H i) }
/-
**DFinsupp.** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, AddCommMonoid (α i)] [∀ i, PartialOrder (α i)] [∀ i, AddLeftReflectLE (α i)] :
    AddLeftReflectLE (Π₀ i, α i) where
  le_of_add_le_add_left H i := le_of_add_le_add_left <| H i

section Module
variable {α : Type*} {β : ι → Type*} [Semiring α] [Preorder α] [∀ i, AddCommMonoid (β i)]
  [∀ i, Preorder (β i)] [∀ i, Module α (β i)]

/-
**DFinsupp.instPosSMulMono** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
形式化陈述：instPosSMulMono [forall i, PosSMulMono α (β i)] : PosSMulMono α (Π₀ i, β i
)
参数：β i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `PosSMulMono.lift`：PosSMulMono.lift [PosSMulMono α γ] (hf : forall {b₁ b₂
}, f b₁ <= f b₂ ↔ b₁ <= b₂) (smul : forall (a : α) b, f (a • b) = a • f b) : Pos
SMulMo…
· 使用定理 `DFinsupp.coe_le_coe`：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι)
 → Zero (α i)] [inst_1 : (i : ι) → LE (α i)] {f g : Π₀ (i : ι), α i},   ⇑f ≤ ⇑g 
↔ f ≤ g
· 使用定理 `DFinsupp.coe_smul`：coe_smul [forall i, Zero (β i)] [forall i, SMulZeroCl
ass γ (β i)] (b : γ) (v : Π₀ i, β i) : ⇑(b • v) = b • ⇑v
-/
instance instPosSMulMono [∀ i, PosSMulMono α (β i)] : PosSMulMono α (Π₀ i, β i) :=
  PosSMulMono.lift _ coe_le_coe coe_smul
/-
**DFinsupp.instSMulPosMono** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
形式化陈述：instSMulPosMono [forall i, SMulPosMono α (β i)] : SMulPosMono α (Π₀ i, β i
)
参数：β i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulPosMono.lift`：SMulPosMono.lift [SMulPosMono α γ] (hf : forall {b₁ b₂
}, f b₁ <= f b₂ ↔ b₁ <= b₂) (smul : forall (a : α) b, f (a • b) = a • f b) (zero
 : f 0…
· 使用定理 `DFinsupp.coe_le_coe`：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι)
 → Zero (α i)] [inst_1 : (i : ι) → LE (α i)] {f g : Π₀ (i : ι), α i},   ⇑f ≤ ⇑g 
↔ f ≤ g
· 使用定理 `DFinsupp.coe_smul`：coe_smul [forall i, Zero (β i)] [forall i, SMulZeroCl
ass γ (β i)] (b : γ) (v : Π₀ i, β i) : ⇑(b • v) = b • ⇑v
· 使用定理 `DFinsupp.coe_zero`：∀ {ι : Type u} {β : ι → Type v} [inst : (i : ι) → Zer
o (β i)], ⇑0 = 0
-/
instance instSMulPosMono [∀ i, SMulPosMono α (β i)] : SMulPosMono α (Π₀ i, β i) :=
  SMulPosMono.lift _ coe_le_coe coe_smul coe_zero
/-
**DFinsupp.instPosSMulReflectLE** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
形式化陈述：instPosSMulReflectLE [forall i, PosSMulReflectLE α (β i)] : PosSMulReflect
LE α (Π₀ i, β i)
参数：β i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `PosSMulReflectLE.lift`：PosSMulReflectLE.lift [PosSMulReflectLE α γ] (hf 
: forall {b₁ b₂}, f b₁ <= f b₂ ↔ b₁ <= b₂) (smul : forall (a : α) b, f (a • b) =
 a • f b) :…
· 使用定理 `DFinsupp.coe_le_coe`：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι)
 → Zero (α i)] [inst_1 : (i : ι) → LE (α i)] {f g : Π₀ (i : ι), α i},   ⇑f ≤ ⇑g 
↔ f ≤ g
· 使用定理 `DFinsupp.coe_smul`：coe_smul [forall i, Zero (β i)] [forall i, SMulZeroCl
ass γ (β i)] (b : γ) (v : Π₀ i, β i) : ⇑(b • v) = b • ⇑v
-/
instance instPosSMulReflectLE [∀ i, PosSMulReflectLE α (β i)] : PosSMulReflectLE α (Π₀ i, β i) :=
  PosSMulReflectLE.lift _ coe_le_coe coe_smul
/-
**DFinsupp.instSMulPosReflectLE** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
形式化陈述：instSMulPosReflectLE [forall i, SMulPosReflectLE α (β i)] : SMulPosReflect
LE α (Π₀ i, β i)
参数：β i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulPosReflectLE.lift`：SMulPosReflectLE.lift [SMulPosReflectLE α γ] (hf 
: forall {b₁ b₂}, f b₁ <= f b₂ ↔ b₁ <= b₂) (smul : forall (a : α) b, f (a • b) =
 a • f b) (…
· 使用定理 `DFinsupp.coe_le_coe`：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι)
 → Zero (α i)] [inst_1 : (i : ι) → LE (α i)] {f g : Π₀ (i : ι), α i},   ⇑f ≤ ⇑g 
↔ f ≤ g
· 使用定理 `DFinsupp.coe_smul`：coe_smul [forall i, Zero (β i)] [forall i, SMulZeroCl
ass γ (β i)] (b : γ) (v : Π₀ i, β i) : ⇑(b • v) = b • ⇑v
· 使用定理 `DFinsupp.coe_zero`：∀ {ι : Type u} {β : ι → Type v} [inst : (i : ι) → Zer
o (β i)], ⇑0 = 0
-/
instance instSMulPosReflectLE [∀ i, SMulPosReflectLE α (β i)] : SMulPosReflectLE α (Π₀ i, β i) :=
  SMulPosReflectLE.lift _ coe_le_coe coe_smul coe_zero

end Module

section Module
variable {α : Type*} {β : ι → Type*} [Semiring α] [PartialOrder α] [∀ i, AddCommMonoid (β i)]
  [∀ i, PartialOrder (β i)] [∀ i, Module α (β i)]

/-
**DFinsupp.instPosSMulStrictMono** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
形式化陈述：instPosSMulStrictMono [forall i, PosSMulStrictMono α (β i)] : PosSMulStric
tMono α (Π₀ i, β i)
参数：β i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `PosSMulStrictMono.lift`：PosSMulStrictMono.lift [PosSMulStrictMono α γ] (
hf : forall {b₁ b₂}, f b₁ <= f b₂ ↔ b₁ <= b₂) (smul : forall (a : α) b, f (a • b
) = a • f b)…
· 使用定理 `DFinsupp.coe_le_coe`：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι)
 → Zero (α i)] [inst_1 : (i : ι) → LE (α i)] {f g : Π₀ (i : ι), α i},   ⇑f ≤ ⇑g 
↔ f ≤ g
· 使用定理 `DFinsupp.coe_smul`：coe_smul [forall i, Zero (β i)] [forall i, SMulZeroCl
ass γ (β i)] (b : γ) (v : Π₀ i, β i) : ⇑(b • v) = b • ⇑v
-/
instance instPosSMulStrictMono [∀ i, PosSMulStrictMono α (β i)] : PosSMulStrictMono α (Π₀ i, β i) :=
  PosSMulStrictMono.lift _ coe_le_coe coe_smul
/-
**DFinsupp.instSMulPosStrictMono** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
形式化陈述：instSMulPosStrictMono [forall i, SMulPosStrictMono α (β i)] : SMulPosStric
tMono α (Π₀ i, β i)
参数：β i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulPosStrictMono.lift`：SMulPosStrictMono.lift [SMulPosStrictMono α γ] (
hf : forall {b₁ b₂}, f b₁ <= f b₂ ↔ b₁ <= b₂) (smul : forall (a : α) b, f (a • b
) = a • f b)…
· 使用定理 `DFinsupp.coe_le_coe`：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι)
 → Zero (α i)] [inst_1 : (i : ι) → LE (α i)] {f g : Π₀ (i : ι), α i},   ⇑f ≤ ⇑g 
↔ f ≤ g
· 使用定理 `DFinsupp.coe_smul`：coe_smul [forall i, Zero (β i)] [forall i, SMulZeroCl
ass γ (β i)] (b : γ) (v : Π₀ i, β i) : ⇑(b • v) = b • ⇑v
· 使用定理 `DFinsupp.coe_zero`：∀ {ι : Type u} {β : ι → Type v} [inst : (i : ι) → Zer
o (β i)], ⇑0 = 0
-/
instance instSMulPosStrictMono [∀ i, SMulPosStrictMono α (β i)] : SMulPosStrictMono α (Π₀ i, β i) :=
  SMulPosStrictMono.lift _ coe_le_coe coe_smul coe_zero

-- Note: There is no interesting instance for `PosSMulReflectLT α (Π₀ i, β i)` that's not already
-- implied by the other instances
/-
**DFinsupp.instSMulPosReflectLT** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
形式化陈述：instSMulPosReflectLT [forall i, SMulPosReflectLT α (β i)] : SMulPosReflect
LT α (Π₀ i, β i)
参数：β i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulPosReflectLT.lift`：SMulPosReflectLT.lift [SMulPosReflectLT α γ] (hf 
: forall {b₁ b₂}, f b₁ <= f b₂ ↔ b₁ <= b₂) (smul : forall (a : α) b, f (a • b) =
 a • f b) (…
· 使用定理 `DFinsupp.coe_le_coe`：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι)
 → Zero (α i)] [inst_1 : (i : ι) → LE (α i)] {f g : Π₀ (i : ι), α i},   ⇑f ≤ ⇑g 
↔ f ≤ g
· 使用定理 `DFinsupp.coe_smul`：coe_smul [forall i, Zero (β i)] [forall i, SMulZeroCl
ass γ (β i)] (b : γ) (v : Π₀ i, β i) : ⇑(b • v) = b • ⇑v
· 使用定理 `DFinsupp.coe_zero`：∀ {ι : Type u} {β : ι → Type v} [inst : (i : ι) → Zer
o (β i)], ⇑0 = 0
-/
instance instSMulPosReflectLT [∀ i, SMulPosReflectLT α (β i)] : SMulPosReflectLT α (Π₀ i, β i) :=
  SMulPosReflectLT.lift _ coe_le_coe coe_smul coe_zero

end Module

section PartialOrder

variable (α) [∀ i, AddCommMonoid (α i)] [∀ i, PartialOrder (α i)]

/-
**DFinsupp.** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, IsBotZeroClass (α i)] : OrderBot (Π₀ i, α i) where
  bot := 0
  bot_le := by simp [le_def]
/-
**DFinsupp.** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, IsBotZeroClass (α i)] : IsBotZeroClass (Π₀ i, α i) where
  isBot_zero := isBot_bot

variable {α}

@[deprecated _root_.bot_eq_zero (since := "2026-05-07")]
/-
**DFinsupp.bot_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι) → AddCommMonoid (α i)]
 [inst_1 : (i : ι) → PartialOrder (α i)]   [inst_2 : ∀ (i : ι), IsBotZeroClass (
α i)], ⊥ = 0
参数：i : ι；α i；i : ι；α i；i : ι；α i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem bot_eq_zero [∀ i, IsBotZeroClass (α i)] : (⊥ : Π₀ i, α i) = 0 :=
  rfl

variable [∀ i, CanonicallyOrderedAdd (α i)]

@[simp]
/-
**DFinsupp.add_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：add_eq_zero_iff (f g : Π₀ i, α i) : f + g = 0 ↔ f = 0 ∧ g = 0
参数：f g : Π₀ i, α i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem add_eq_zero_iff (f g : Π₀ i, α i) : f + g = 0 ↔ f = 0 ∧ g = 0 := by
  simp [DFunLike.ext_iff, forall_and]

section LE

variable [DecidableEq ι]

section

variable [∀ (i) (x : α i), Decidable (x ≠ 0)] {f g : Π₀ i, α i} {s : Finset ι}

/-
**DFinsupp.le_iff'** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：le_iff' (hf : f.support subseteq s) : f <= g ↔ forall i in s, f i <= g i
参数：hf : f.support subseteq s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFinsupp.notMem_support_iff`：notMem_support_iff {f : Π₀ i, β i} {i : ι} 
: i ∉ f.support ↔ f i = 0
-/
theorem le_iff' (hf : f.support ⊆ s) : f ≤ g ↔ ∀ i ∈ s, f i ≤ g i :=
  ⟨fun h s _ ↦ h s, fun h s ↦
    if H : s ∈ f.support then h s (hf H) else (notMem_support_iff.1 H).symm ▸ zero_le⟩
/-
**DFinsupp.le_iff** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：le_iff : f <= g ↔ forall i in f.support, f i <= g i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.le_iff'`：le_iff' (hf : f.support subseteq s) : f <= g ↔ forall 
i in s, f i <= g i
· 使用定理 `Finset.Subset.refl`：∀ {α : Type u_1} (s : Finset α), s ⊆ s
-/
theorem le_iff : f ≤ g ↔ ∀ i ∈ f.support, f i ≤ g i :=
  le_iff' <| Subset.refl _
/-
**DFinsupp.support_monotone** 是 Mathlib 中的一个引理，位于命名空间 `DFinsupp`。
形式化陈述：support_monotone : Monotone (support (ι
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.mem_support_iff`：mem_support_iff {f : Π₀ i, β i} {i : ι} : i in
 f.support ↔ f i != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
-/
lemma support_monotone : Monotone (support (ι := ι) (β := α)) :=
  fun f g h a ha ↦ by rw [mem_support_iff, ← pos_iff_ne_zero] at ha ⊢; exact ha.trans_le (h _)
/-
**DFinsupp.support_mono** 是 Mathlib 中的一个引理，位于命名空间 `DFinsupp`。
形式化陈述：support_mono (hfg : f <= g) : f.support subseteq g.support
参数：hfg : f <= g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DFinsupp.support_monotone`：support_monotone : Monotone (support (ι
-/
lemma support_mono (hfg : f ≤ g) : f.support ⊆ g.support := support_monotone hfg

variable (α) in
/-
**DFinsupp.decidableLE** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
形式化陈述：decidableLE [forall i, DecidableLE (α i)] : DecidableLE (Π₀ i, α i)
参数：α i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableLE [∀ i, DecidableLE (α i)] : DecidableLE (Π₀ i, α i) :=
  fun _ _ ↦ decidable_of_iff _ le_iff.symm

end

@[simp]
/-
**DFinsupp.single_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：single_le_iff {f : Π₀ i, α i} {i : ι} {a : α i} : single i a <= f ↔ a <= f
 i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `DFinsupp.le_iff'`：le_iff' (hf : f.support subseteq s) : f <= g ↔ forall 
i in s, f i <= g i
· 使用定理 `DFinsupp.support_single_subset`：support_single_subset {i : ι} {b : β i} 
: (single i b).support subseteq {i}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `DFinsupp.single_apply`：single_apply {i i' b} : (single i b : Π₀ i, β i) 
i' = if h : i = i' then Eq.recOn h b else 0
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem single_le_iff {f : Π₀ i, α i} {i : ι} {a : α i} :
    single i a ≤ f ↔ a ≤ f i := by
  classical exact (le_iff' support_single_subset).trans <| by simp

end LE

variable (α) [∀ i, Sub (α i)] [∀ i, OrderedSub (α i)] {f g : Π₀ i, α i} {i : ι} {a b : α i}

/-- This is called `tsub` for truncated subtraction, to distinguish it with subtraction in an
additive group. -/
/-
**DFinsupp.tsub** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
形式化陈述：tsub : Sub (Π₀ i, α i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is called `tsub` for truncated subtraction, to distinguish it with subtract
ion in an
additive group.
-/
instance tsub : Sub (Π₀ i, α i) :=
  ⟨zipWith (fun _ m n ↦ m - n) fun _ ↦ tsub_self 0⟩

variable {α}
/-
**DFinsupp.tsub_apply** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：tsub_apply (f g : Π₀ i, α i) (i : ι) : (f - g) i = f i - g i
参数：f g : Π₀ i, α i；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.zipWith_apply`：zipWith_apply (f : forall i, β₁ i -> β₂ i -> β i
) (hf : forall i, f i 0 0 = 0) (g₁ : Π₀ i, β₁ i) (g₂ : Π₀ i, β₂ i) (i : ι) : zip
With f hf g₁…
-/
theorem tsub_apply (f g : Π₀ i, α i) (i : ι) : (f - g) i = f i - g i :=
  zipWith_apply _ _ _ _ _

@[simp, norm_cast]
/-
**DFinsupp.coe_tsub** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：coe_tsub (f g : Π₀ i, α i) : ⇑(f - g) = f - g
参数：f g : Π₀ i, α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `DFinsupp.tsub_apply`：tsub_apply (f g : Π₀ i, α i) (i : ι) : (f - g) i = 
f i - g i
-/
theorem coe_tsub (f g : Π₀ i, α i) : ⇑(f - g) = f - g := by
  ext i
  exact tsub_apply f g i

variable (α)
/-
**DFinsupp.** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderedSub (Π₀ i, α i) :=
  ⟨fun _ _ _ ↦ forall_congr' fun _ ↦ tsub_le_iff_right⟩
/-
**DFinsupp.** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, AddLeftMono (α i)] : CanonicallyOrderedAdd (Π₀ i, α i) where
  exists_add_of_le := by
    intro f g h
    exists g - f
    ext i
    exact (add_tsub_cancel_of_le <| h i).symm
  le_add_self := fun _ _ _ ↦ le_add_self
  le_self_add := fun _ _ _ ↦ le_self_add

variable {α} [DecidableEq ι]

@[simp]
/-
**DFinsupp.single_tsub** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：single_tsub : single i (a - b) = single i a - single i b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.tsub_apply`：tsub_apply (f g : Π₀ i, α i) (i : ι) : (f - g) i = 
f i - g i
· 使用定理 `DFinsupp.single_eq_same`：single_eq_same {i b} : (single i b : Π₀ i, β i)
 i = b
· 使用定理 `DFinsupp.single_eq_of_ne`：single_eq_of_ne {i i' b} (h : i' != i) : (sing
le i b : Π₀ i, β i) i' = 0
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
-/
theorem single_tsub : single i (a - b) = single i a - single i b := by
  ext j
  obtain rfl | h := eq_or_ne j i
  · rw [tsub_apply, single_eq_same, single_eq_same, single_eq_same]
  · rw [tsub_apply, single_eq_of_ne h, single_eq_of_ne h, single_eq_of_ne h, tsub_self]

variable [∀ (i) (x : α i), Decidable (x ≠ 0)]
/-
**DFinsupp.support_tsub** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：support_tsub : (f - g).support subseteq f.support
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `DFinsupp.coe_tsub`：coe_tsub (f g : Π₀ i, α i) : ⇑(f - g) = f - g
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem support_tsub : (f - g).support ⊆ f.support := by
  simp +contextual only [subset_iff, tsub_eq_zero_iff_le, mem_support_iff,
    Ne, coe_tsub, Pi.sub_apply, not_imp_not, zero_le, imp_true_iff]
/-
**DFinsupp.subset_support_tsub** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：subset_support_tsub : f.support \ g.support subseteq (f - g).support
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `DFinsupp.coe_tsub`：coe_tsub (f g : Π₀ i, α i) : ⇑(f - g) = f - g
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem subset_support_tsub : f.support \ g.support ⊆ (f - g).support := by
  simp +contextual [subset_iff]

end PartialOrder

section LinearOrder
variable [∀ i, AddCommMonoid (α i)] [∀ i, LinearOrder (α i)] [∀ i, IsBotZeroClass (α i)]
  [DecidableEq ι] {f g : Π₀ i, α i}

@[simp]
/-
**DFinsupp.support_inf** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：support_inf : (f ⊓ g).support = f.support inter g.support
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem support_inf : (f ⊓ g).support = f.support ∩ g.support := by
  ext
  simp

@[simp]
/-
**DFinsupp.support_sup** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：support_sup : (f ⊔ g).support = f.support union g.support
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem support_sup : (f ⊔ g).support = f.support ∪ g.support := by
  ext
  simp [imp_iff_not_or]

nonrec theorem disjoint_iff : Disjoint f g ↔ Disjoint f.support g.support := by
  simp [disjoint_iff, bot_eq_zero, ← DFinsupp.support_eq_empty]

end LinearOrder

end DFinsupp

