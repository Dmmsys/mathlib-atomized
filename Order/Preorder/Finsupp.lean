/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Aaron Anderson
-/
module

public import Mathlib.Data.Finsupp.Defs

/-!
# Pointwise order on finitely supported functions

This file lifts order structures on `M` to `ι →₀ M`.
-/

@[expose] public section

assert_not_exists CompleteLattice

noncomputable section

open Finset

namespace Finsupp
variable {ι M : Type*} [Zero M]

section LE
variable [LE M] {f g : ι →₀ M}

/-
**Finsupp.instLE** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：instLE : LE (ι ->₀ M) where le f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLE : LE (ι →₀ M) where le f g := ∀ i, f i ≤ g i
/-
**Finsupp.le_def** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：le_def : f <= g ↔ forall i, f i <= g i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma le_def : f ≤ g ↔ ∀ i, f i ≤ g i := .rfl
/-
**Finsupp.coe_le_coe** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_2} [inst : Zero M] [inst_1 : LE M] {f g : ι →
₀ M}, ⇑f ≤ ⇑g ↔ f ≤ g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, norm_cast] lemma coe_le_coe : ⇑f ≤ g ↔ f ≤ g := .rfl

/-- The order on `Finsupp`s over a partial order embeds into the order on functions -/
@[simps]
/-
**Finsupp.orderEmbeddingToFun** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：orderEmbeddingToFun : (ι ->₀ M) ↪o (ι -> M) where toFun f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.coe_le_coe`：∀ {ι : Type u_1} {M : Type u_2} [inst : Zero M] [ins
t_1 : LE M] {f g : ι →₀ M}, ⇑f ≤ ⇑g ↔ f ≤ g

--- 原说明 ---
The order on `Finsupp`s over a partial order embeds into the order on functions
-/
def orderEmbeddingToFun : (ι →₀ M) ↪o (ι → M) where
  toFun f := f
  inj' := DFunLike.coe_injective
  map_rel_iff' := coe_le_coe

/-- `equivFunOnFinite` as an order isomorphism. -/
/-
**Finsupp.orderIsoFunOnFinite** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：orderIsoFunOnFinite [Finite ι] : (ι ->₀ M) ≃o (ι -> M) where toEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`equivFunOnFinite` as an order isomorphism.
-/
def orderIsoFunOnFinite [Finite ι] : (ι →₀ M) ≃o (ι → M) where
  toEquiv := equivFunOnFinite
  map_rel_iff' := Iff.rfl

end LE

section Preorder
variable [Preorder M] {f g : ι →₀ M} {i : ι} {a b : M}

/-
**Finsupp.preorder** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：preorder : Preorder (ι ->₀ M) where le_refl _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance preorder : Preorder (ι →₀ M) where
  le_refl _ _ := le_rfl
  le_trans _ _ _ hfg hgh i := (hfg i).trans (hgh i)
/-
**Finsupp.lt_def** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：lt_def : f < g ↔ f <= g ∧ exists i, f i < g i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.lt_def`：Pi.lt_def [forall i, Preorder (π i)] {x y : forall i, π i} : 
x < y ↔ x <= y ∧ exists i, x i < y i
-/
lemma lt_def : f < g ↔ f ≤ g ∧ ∃ i, f i < g i := Pi.lt_def
/-
**Finsupp.coe_lt_coe** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_2} [inst : Zero M] [inst_1 : Preorder M] {f g
 : ι →₀ M}, ⇑f < ⇑g ↔ f < g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, norm_cast] lemma coe_lt_coe : ⇑f < g ↔ f < g := .rfl
/-
**Finsupp.coe_mono** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：coe_mono : Monotone (Finsupp.toFun : (ι ->₀ M) -> ι -> M)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_mono : Monotone (Finsupp.toFun : (ι →₀ M) → ι → M) := fun _ _ ↦ id
/-
**Finsupp.coe_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：coe_strictMono : Monotone (Finsupp.toFun : (ι ->₀ M) -> ι -> M)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_strictMono : Monotone (Finsupp.toFun : (ι →₀ M) → ι → M) := fun _ _ ↦ id

end Preorder

/-
**Finsupp.partialorder** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：partialorder [PartialOrder M] : PartialOrder (ι ->₀ M) where le_antisymm _
f _g hfg hgf
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance partialorder [PartialOrder M] : PartialOrder (ι →₀ M) where
  le_antisymm _f _g hfg hgf := ext fun i ↦ (hfg i).antisymm (hgf i)

section SemilatticeInf
variable [SemilatticeInf M]

/-
**Finsupp.semilatticeInf** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：semilatticeInf : SemilatticeInf (ι ->₀ M) where inf
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance semilatticeInf : SemilatticeInf (ι →₀ M) where
  inf := zipWith (· ⊓ ·) (inf_idem _)
  inf_le_left _f _g _i := inf_le_left
  inf_le_right _f _g _i := inf_le_right
  le_inf _f _g _i h1 h2 s := le_inf (h1 s) (h2 s)
/-
**Finsupp.inf_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_2} [inst : Zero M] [inst_1 : SemilatticeInf M
] (f g : ι →₀ M) (i : ι),   (f ⊓ g) i = f i ⊓ g i
参数：f g : ι →₀ M；i : ι；f ⊓ g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma inf_apply (f g : ι →₀ M) (i : ι) : (f ⊓ g) i = f i ⊓ g i := rfl

end SemilatticeInf

section SemilatticeSup
variable [SemilatticeSup M]

/-
**Finsupp.semilatticeSup** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：semilatticeSup : SemilatticeSup (ι ->₀ M) where sup
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance semilatticeSup : SemilatticeSup (ι →₀ M) where
  sup := zipWith (· ⊔ ·) (sup_idem _)
  le_sup_left _f _g _i := le_sup_left
  le_sup_right _f _g _i := le_sup_right
  sup_le _f _g _h hf hg i := sup_le (hf i) (hg i)

@[simp]
/-
**Finsupp.sup_apply** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：sup_apply (f g : ι ->₀ M) (i : ι) : (f ⊔ g) i = f i ⊔ g i
参数：f g : ι ->₀ M；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sup_apply (f g : ι →₀ M) (i : ι) : (f ⊔ g) i = f i ⊔ g i := rfl

end SemilatticeSup

section Lattice
variable [Lattice M] (f g : ι →₀ M)

/-
**Finsupp.lattice** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：lattice : Lattice (ι ->₀ M) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance lattice : Lattice (ι →₀ M) where
  __ := Finsupp.semilatticeInf
  __ := Finsupp.semilatticeSup

variable [DecidableEq ι]
/-
**Finsupp.support_inf_union_support_sup** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
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
lemma support_inf_union_support_sup : (f ⊓ g).support ∪ (f ⊔ g).support = f.support ∪ g.support :=
  coe_injective <| compl_injective <| by ext; simp [inf_eq_and_sup_eq_iff]
/-
**Finsupp.support_sup_union_support_inf** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：support_sup_union_support_inf : (f ⊔ g).support union (f ⊓ g).support = f.
support union g.support
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.union_comm`：union_comm (s₁ s₂ : Finset α) : s₁ union s₂ = s₂ unio
n s₁
· 使用引理 `Finsupp.support_inf_union_support_sup`：support_inf_union_support_sup : (
f ⊓ g).support union (f ⊔ g).support = f.support union g.support
-/
lemma support_sup_union_support_inf : (f ⊔ g).support ∪ (f ⊓ g).support = f.support ∪ g.support :=
  (union_comm _ _).trans <| support_inf_union_support_sup _ _

end Lattice
end Finsupp

