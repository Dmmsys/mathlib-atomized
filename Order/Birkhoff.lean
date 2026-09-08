/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Filippo A. E. Nuccio, Sam van Gool
-/
module

public import Mathlib.Data.Fintype.Order
public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Order.Irreducible
public import Mathlib.Order.UpperLower.Closure

/-!
# Birkhoff representation

This file proves two facts which together are commonly referred to as "Birkhoff representation":
1. Any nonempty finite partial order is isomorphic to the partial order of sup-irreducible elements
  in its lattice of lower sets.
2. Any nonempty finite distributive lattice is isomorphic to the lattice of lower sets of its
  partial order of sup-irreducible elements.

## Main declarations

For a finite nonempty partial order `α`:
* `OrderEmbedding.supIrredLowerSet`: `α` is isomorphic to the order of its irreducible lower sets.

If `α` is moreover a distributive lattice:
* `OrderIso.lowerSetSupIrred`: `α` is isomorphic to the lattice of lower sets of its irreducible
  elements.
* `OrderEmbedding.birkhoffSet`, `OrderEmbedding.birkhoffFinset`: Order embedding of `α` into the
  powerset lattice of its irreducible elements.
* `LatticeHom.birkhoffSet`, `LatticeHom.birkhoffFinset`: Same as the previous two, but bundled as
  an injective lattice homomorphism.
* `exists_birkhoff_representation`: `α` embeds into some powerset algebra. You should prefer using
  this over the explicit Birkhoff embedding because the Birkhoff embedding is littered with
  decidability footguns that this existential-packaged version can afford to avoid.

## See also

These results form the object part of finite Stone duality: the functorial contravariant
equivalence between the category of finite distributive lattices and the category of finite
partial orders. TODO: extend to morphisms.

## References

* [G. Birkhoff, *Rings of sets*][birkhoff1937]

## Tags

birkhoff, representation, stone duality, lattice embedding
-/

@[expose] public section

open Finset Function OrderDual UpperSet LowerSet

variable {α : Type*}

section PartialOrder
variable [PartialOrder α]

namespace UpperSet
variable {s : UpperSet α}

/-
**UpperSet.infIrred_Ici** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] (a : α), InfIrred (UpperSet.Ici a
)
参数：a : α；UpperSet.Ici a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `UpperSet.Ici_ne_top`：Ici_ne_top : Ici a != ⊤
· 使用定理 `IsMax.eq_top`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderTop 
α] {a : α}, IsMax a → a = ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `UpperSet.mem_Ici_iff`：mem_Ici_iff : b in Ici a ↔ a <= b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `UpperSet.le_Ici`：le_Ici : s <= Ici a ↔ a in s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma infIrred_Ici (a : α) : InfIrred (Ici a) := by
  refine ⟨fun h ↦ Ici_ne_top h.eq_top, fun s t hst ↦ ?_⟩
  have := mem_Ici_iff.2 (le_refl a)
  rw [← hst] at this
  exact this.imp (fun ha ↦ le_antisymm (le_Ici.2 ha) <| hst.ge.trans inf_le_left) fun ha ↦
      le_antisymm (le_Ici.2 ha) <| hst.ge.trans inf_le_right

variable [Finite α]
/-
**UpperSet.infIrred_iff_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] {s : UpperSet α} [Finite α], InfI
rred s ↔ ∃ a, UpperSet.Ici a = s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.exists_minimal`：∀ {α : Type u_2} [inst : LE α] [IsTrans α fun
 a a_1 => a_1 ≤ a] {s : Set α},   s.Finite → s.Nonempty → ∃ i, Minimal (fun x =>
 x ∈ s) i
· 使用定理 `instIsTransGe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x2 ≤ x1
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `UpperSet.coe_nonempty`：coe_nonempty : (s : Set α).Nonempty ↔ s != ⊤
· 使用定理 `InfIrred.ne_top`：InfIrred.ne_top (ha : InfIrred a) : a != ⊤
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `UpperSet.erase_inf_Ici`：erase_inf_Ici (ha : a in s) (has : forall b in s
, b <= a -> b = a) : s.erase a ⊓ Ici a = s
· 使用引理 `le_imp_eq_iff_le_imp_ge`：le_imp_eq_iff_le_imp_ge : (a <= b -> a = b) ↔ (
a <= b -> b <= a) where mp h hab
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `UpperSet.lt_erase`：lt_erase : s < s.erase a ↔ a in s
· 使用定理 `UpperSet.infIrred_Ici`：∀ {α : Type u_1} [inst : PartialOrder α] (a : α),
 InfIrred (UpperSet.Ici a)
-/
@[simp] lemma infIrred_iff_of_finite : InfIrred s ↔ ∃ a, Ici a = s := by
  refine ⟨fun hs ↦ ?_, ?_⟩
  · obtain ⟨a, ha, has⟩ := (s : Set α).toFinite.exists_minimal (coe_nonempty.2 hs.ne_top)
    exact ⟨a, (hs.2 <| erase_inf_Ici ha fun b hb ↦ le_imp_eq_iff_le_imp_ge.2 <| has hb).resolve_left
      (lt_erase.2 ha).ne'⟩
  · rintro ⟨a, rfl⟩
    exact infIrred_Ici _

end UpperSet

namespace LowerSet
variable {s : LowerSet α}

/-
**LowerSet.supIrred_Iic** 是 Mathlib 中的一个定理，位于命名空间 `LowerSet`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] (a : α), SupIrred (LowerSet.Iic a
)
参数：a : α；LowerSet.Iic a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSet.Iic_ne_bot`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, Lower
Set.Iic a ≠ ⊥
· 使用定理 `IsMin.eq_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot 
α] {a : α}, IsMin a → a = ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LowerSet.mem_Iic_iff`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b 
∈ LowerSet.Iic a ↔ b ≤ a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `LowerSet.Iic_le`：∀ {α : Type u_1} [inst : Preorder α] {s : LowerSet α} {
a : α}, LowerSet.Iic a ≤ s ↔ a ∈ s
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma supIrred_Iic (a : α) : SupIrred (Iic a) := by
  refine ⟨fun h ↦ Iic_ne_bot h.eq_bot, fun s t hst ↦ ?_⟩
  have := mem_Iic_iff.2 (le_refl a)
  rw [← hst] at this
  exact this.imp (fun ha ↦ (le_sup_left.trans_eq hst).antisymm <| Iic_le.2 ha) fun ha ↦
    (le_sup_right.trans_eq hst).antisymm <| Iic_le.2 ha

variable [Finite α]
/-
**LowerSet.supIrred_iff_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `LowerSet`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] {s : LowerSet α} [Finite α], SupI
rred s ↔ ∃ a, LowerSet.Iic a = s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.exists_maximal`：∀ {α : Type u_2} [inst : LE α] [IsTrans α LE.
le] {s : Set α}, s.Finite → s.Nonempty → ∃ i, Maximal (fun x => x ∈ s) i
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LowerSet.coe_nonempty`：∀ {α : Type u_1} [inst : LE α] {s : LowerSet α}, 
(↑s).Nonempty ↔ s ≠ ⊥
· 使用定理 `SupIrred.ne_bot`：SupIrred.ne_bot (ha : SupIrred a) : a != ⊥
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LowerSet.erase_sup_Iic`：∀ {α : Type u_1} [inst : Preorder α] {s : LowerS
et α} {a : α},   a ∈ s → (∀ b ∈ s, a ≤ b → b = a) → s.erase a ⊔ LowerSet.Iic a =
 s
· 使用定理 `le_imp_eq_iff_le_imp_ge'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b 
: α}, b ≤ a → a = b ↔ b ≤ a → a ≤ b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LowerSet.erase_lt`：∀ {α : Type u_1} [inst : Preorder α] {s : LowerSet α}
 {a : α}, s.erase a < s ↔ a ∈ s
· 使用定理 `LowerSet.supIrred_Iic`：∀ {α : Type u_1} [inst : PartialOrder α] (a : α),
 SupIrred (LowerSet.Iic a)
-/
@[simp] lemma supIrred_iff_of_finite : SupIrred s ↔ ∃ a, Iic a = s := by
  refine ⟨fun hs ↦ ?_, ?_⟩
  · obtain ⟨a, ha, has⟩ := (s : Set α).toFinite.exists_maximal (coe_nonempty.2 hs.ne_bot)
    exact ⟨a, (hs.2 <| erase_sup_Iic ha fun b hb ↦
      le_imp_eq_iff_le_imp_ge'.2 <| has hb).resolve_left (erase_lt.2 ha).ne⟩
  · rintro ⟨a, rfl⟩
    exact supIrred_Iic _

end LowerSet

namespace OrderEmbedding

set_option backward.isDefEq.respectTransparency false in
/-- The **Birkhoff Embedding** of a finite partial order as sup-irreducible elements in its
lattice of lower sets. -/
/-
**OrderEmbedding.supIrredLowerSet** 是 Mathlib 中的一个定义，位于命名空间 `OrderEmbedding`。
形式化陈述：supIrredLowerSet : α ↪o {s : LowerSet α // SupIrred s} where toFun a
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSet.supIrred_Iic`：∀ {α : Type u_1} [inst : PartialOrder α] (a : α),
 SupIrred (LowerSet.Iic a)

--- 原说明 ---
The **Birkhoff Embedding** of a finite partial order as sup-irreducible elements
 in its
lattice of lower sets.
-/
def supIrredLowerSet : α ↪o {s : LowerSet α // SupIrred s} where
  toFun a := ⟨Iic a, supIrred_Iic _⟩
  inj' _ := by simp
  map_rel_iff' := by simp

set_option backward.isDefEq.respectTransparency false in
/-- The **Birkhoff Embedding** of a finite partial order as inf-irreducible elements in its
lattice of lower sets. -/
/-
**OrderEmbedding.infIrredUpperSet** 是 Mathlib 中的一个定义，位于命名空间 `OrderEmbedding`。
形式化陈述：infIrredUpperSet : α ↪o {s : UpperSet α // InfIrred s} where toFun a
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `UpperSet.infIrred_Ici`：∀ {α : Type u_1} [inst : PartialOrder α] (a : α),
 InfIrred (UpperSet.Ici a)

--- 原说明 ---
The **Birkhoff Embedding** of a finite partial order as inf-irreducible elements
 in its
lattice of lower sets.
-/
def infIrredUpperSet : α ↪o {s : UpperSet α // InfIrred s} where
  toFun a := ⟨Ici a, infIrred_Ici _⟩
  inj' _ := by simp
  map_rel_iff' := by simp
/-
**OrderEmbedding.supIrredLowerSet_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbeddin
g`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] (a : α), OrderEmbedding.supIrredL
owerSet a = ⟨LowerSet.Iic a, ⋯⟩
参数：a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma supIrredLowerSet_apply (a : α) : supIrredLowerSet a = ⟨Iic a, supIrred_Iic _⟩ := rfl
/-
**OrderEmbedding.infIrredUpperSet_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbeddin
g`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] (a : α), OrderEmbedding.infIrredU
pperSet a = ⟨UpperSet.Ici a, ⋯⟩
参数：a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma infIrredUpperSet_apply (a : α) : infIrredUpperSet a = ⟨Ici a, infIrred_Ici _⟩ := rfl

variable [Finite α]
/-
**OrderEmbedding.supIrredLowerSet_surjective** 是 Mathlib 中的一个引理，位于命名空间 `OrderEmb
edding`。
形式化陈述：supIrredLowerSet_surjective : Surjective (supIrredLowerSet (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LowerSet.supIrred_Iic`：∀ {α : Type u_1} [inst : PartialOrder α] (a : α),
 SupIrred (LowerSet.Iic a)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma supIrredLowerSet_surjective : Surjective (supIrredLowerSet (α := α)) := by
  aesop (add simp Surjective)
/-
**OrderEmbedding.infIrredUpperSet_surjective** 是 Mathlib 中的一个引理，位于命名空间 `OrderEmb
edding`。
形式化陈述：infIrredUpperSet_surjective : Surjective (infIrredUpperSet (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `UpperSet.infIrred_Ici`：∀ {α : Type u_1} [inst : PartialOrder α] (a : α),
 InfIrred (UpperSet.Ici a)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma infIrredUpperSet_surjective : Surjective (infIrredUpperSet (α := α)) := by
  aesop (add simp Surjective)

end OrderEmbedding

namespace OrderIso
variable [Finite α]

/-- **Birkhoff Representation for partial orders.** Any partial order is isomorphic
to the partial order of sup-irreducible elements in its lattice of lower sets. -/
/-
**OrderIso.supIrredLowerSet** 是 Mathlib 中的一个定义，位于命名空间 `OrderIso`。
形式化陈述：supIrredLowerSet : α ≃o {s : LowerSet α // SupIrred s}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `OrderEmbedding.supIrredLowerSet_surjective`：supIrredLowerSet_surjective 
: Surjective (supIrredLowerSet (α

--- 原说明 ---
**Birkhoff Representation for partial orders.** Any partial order is isomorphic
to the partial order of sup-irreducible elements in its lattice of lower sets.
-/
noncomputable def supIrredLowerSet : α ≃o {s : LowerSet α // SupIrred s} :=
  RelIso.ofSurjective _ OrderEmbedding.supIrredLowerSet_surjective

/-- **Birkhoff Representation for partial orders.** Any partial order is isomorphic
to the partial order of inf-irreducible elements in its lattice of upper sets. -/
/-
**OrderIso.infIrredUpperSet** 是 Mathlib 中的一个定义，位于命名空间 `OrderIso`。
形式化陈述：infIrredUpperSet : α ≃o {s : UpperSet α // InfIrred s}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `OrderEmbedding.infIrredUpperSet_surjective`：infIrredUpperSet_surjective 
: Surjective (infIrredUpperSet (α

--- 原说明 ---
**Birkhoff Representation for partial orders.** Any partial order is isomorphic
to the partial order of inf-irreducible elements in its lattice of upper sets.
-/
noncomputable def infIrredUpperSet : α ≃o {s : UpperSet α // InfIrred s} :=
  RelIso.ofSurjective _ OrderEmbedding.infIrredUpperSet_surjective
/-
**OrderIso.supIrredLowerSet_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Finite α] (a : α), Orde
rIso.supIrredLowerSet a = ⟨LowerSet.Iic a, ⋯⟩
参数：a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma supIrredLowerSet_apply (a : α) : supIrredLowerSet a = ⟨Iic a, supIrred_Iic _⟩ := rfl
/-
**OrderIso.infIrredUpperSet_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Finite α] (a : α), Orde
rIso.infIrredUpperSet a = ⟨UpperSet.Ici a, ⋯⟩
参数：a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma infIrredUpperSet_apply (a : α) : infIrredUpperSet a = ⟨Ici a, infIrred_Ici _⟩ := rfl

end OrderIso
end PartialOrder

namespace OrderIso
section SemilatticeSup
variable [SemilatticeSup α] [OrderBot α] [Finite α]

set_option backward.isDefEq.respectTransparency false in
/-
**OrderIso.supIrredLowerSet_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBot α] [inst_2 :
 Finite α] (s : { s // SupIrred s })   [inst_3 : Fintype ↥↑s], OrderIso.supIrred
LowerSet.symm s = (↑↑s).toFinset.sup id
参数：s : { s // SupIrred s }；↑↑s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LowerSet.supIrred_iff_of_finite`：∀ {α : Type u_1} [inst : PartialOrder α
] {s : LowerSet α} [Finite α], SupIrred s ↔ ∃ a, LowerSet.Iic a = s
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.toFinset_Iic`：∀ {α : Type u_3} [inst : Preorder α] [inst_1 : Locally
FiniteOrderBot α] (a : α) [inst_2 : Fintype ↑(Set.Iic a)],   (Set.Iic a).toFinse
t = Fi…
· 使用定理 `Finset.sup_Iic`：∀ {α : Type u_2} [inst : SemilatticeSup α] [inst_1 : Loc
allyFiniteOrderBot α] [inst_2 : OrderBot α] (a : α),   (Finset.Iic a).sup id = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma supIrredLowerSet_symm_apply (s : {s : LowerSet α // SupIrred s}) [Fintype s] :
    supIrredLowerSet.symm s = (s.1 : Set α).toFinset.sup id := by
  classical
  obtain ⟨s, hs⟩ := s
  obtain ⟨a, rfl⟩ := supIrred_iff_of_finite.1 hs
  cases nonempty_fintype α
  have : LocallyFiniteOrder α := Fintype.toLocallyFiniteOrder
  simp [symm_apply_eq]

end SemilatticeSup

section SemilatticeInf
variable [SemilatticeInf α] [OrderTop α] [Finite α]

set_option backward.isDefEq.respectTransparency false in
/-
**OrderIso.infIrredUpperSet_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTop α] [inst_2 :
 Finite α] (s : { s // InfIrred s })   [inst_3 : Fintype ↥↑s], OrderIso.infIrred
UpperSet.symm s = (↑↑s).toFinset.inf id
参数：s : { s // InfIrred s }；↑↑s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `UpperSet.infIrred_iff_of_finite`：∀ {α : Type u_1} [inst : PartialOrder α
] {s : UpperSet α} [Finite α], InfIrred s ↔ ∃ a, UpperSet.Ici a = s
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Set.toFinset_Ici`：toFinset_Ici (a : α) [Fintype (Ici a)] : (Ici a).toFin
set = Finset.Ici a
· 使用定理 `Finset.inf_Ici`：∀ {α : Type u_2} [inst : SemilatticeInf α] [inst_1 : Loc
allyFiniteOrderTop α] [inst_2 : OrderTop α] (a : α),   (Finset.Ici a).inf id = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma infIrredUpperSet_symm_apply (s : {s : UpperSet α // InfIrred s}) [Fintype s] :
    infIrredUpperSet.symm s = (s.1 : Set α).toFinset.inf id := by
  classical
  obtain ⟨s, hs⟩ := s
  obtain ⟨a, rfl⟩ := infIrred_iff_of_finite.1 hs
  cases nonempty_fintype α
  have : LocallyFiniteOrder α := Fintype.toLocallyFiniteOrder
  simp [symm_apply_eq]

end SemilatticeInf
end OrderIso

section DistribLattice
variable [DistribLattice α] [Fintype α] [@DecidablePred α SupIrred]

open scoped Classical in
/-- **Birkhoff Representation for finite distributive lattices**. Any nonempty finite distributive
lattice is isomorphic to the lattice of lower sets of its sup-irreducible elements. -/
/-
**OrderIso.lowerSetSupIrred** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderIso.lowerSetSupIrred [OrderBot α] : α ≃o LowerSet {a : α // SupIrred 
a}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Birkhoff Representation for finite distributive lattices**. Any nonempty finit
e distributive
lattice is isomorphic to the lattice of lower sets of its sup-irreducible elemen
ts.
-/
noncomputable def OrderIso.lowerSetSupIrred [OrderBot α] : α ≃o LowerSet {a : α // SupIrred a} :=
  Equiv.toOrderIso
    { toFun := fun a ↦ ⟨{b | ↑b ≤ a}, fun _ _ hcb hba ↦ hba.trans' hcb⟩
      invFun := fun s ↦ (s : Set {a : α // SupIrred a}).toFinset.sup (↑)
      left_inv := fun a ↦ by
        refine le_antisymm (Finset.sup_le fun b ↦ Set.mem_toFinset.1) ?_
        obtain ⟨s, rfl, hs⟩ := exists_supIrred_decomposition a
        exact Finset.sup_le fun i hi ↦
          le_sup_of_le (b := ⟨i, hs hi⟩) (Set.mem_toFinset.2 <| le_sup (f := id) hi) le_rfl
      right_inv := fun s ↦ by
        ext a
        dsimp
        refine ⟨fun ha ↦ ?_, fun ha ↦ ?_⟩
        · obtain ⟨i, hi, ha⟩ := a.2.supPrime.le_finset_sup.1 ha
          exact s.lower ha (Set.mem_toFinset.1 hi)
        · exact le_sup (Set.mem_toFinset.2 ha) }
    (fun _ _ hbc _ ↦ le_trans' hbc) fun _ _ hst ↦ Finset.sup_mono <| Set.toFinset_mono hst

namespace OrderEmbedding

/-- **Birkhoff's Representation Theorem**. Any finite distributive lattice can be embedded in a
powerset lattice. -/
/-
**OrderEmbedding.birkhoffSet** 是 Mathlib 中的一个定义，位于命名空间 `OrderEmbedding`。
形式化陈述：birkhoffSet : α ↪o Set {a : α // SupIrred a}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Birkhoff's Representation Theorem**. Any finite distributive lattice can be em
bedded in a
powerset lattice.
-/
noncomputable def birkhoffSet : α ↪o Set {a : α // SupIrred a} := by
  by_cases! h : IsEmpty α
  · exact OrderEmbedding.ofIsEmpty
  have := Fintype.toOrderBot α
  exact OrderIso.lowerSetSupIrred.toOrderEmbedding.trans ⟨⟨_, SetLike.coe_injective⟩, Iff.rfl⟩

/-- **Birkhoff's Representation Theorem**. Any finite distributive lattice can be embedded in a
powerset lattice. -/
/-
**OrderEmbedding.birkhoffFinset** 是 Mathlib 中的一个定义，位于命名空间 `OrderEmbedding`。
形式化陈述：birkhoffFinset : α ↪o Finset {a : α // SupIrred a}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Birkhoff's Representation Theorem**. Any finite distributive lattice can be em
bedded in a
powerset lattice.
-/
noncomputable def birkhoffFinset : α ↪o Finset {a : α // SupIrred a} := by
  exact birkhoffSet.trans Fintype.finsetOrderIsoSet.symm.toOrderEmbedding
/-
**OrderEmbedding.coe_birkhoffFinset** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：∀ {α : Type u_1} [inst : DistribLattice α] [inst_1 : Fintype α] [inst_2 : 
DecidablePred SupIrred] (a : α),   ↑(OrderEmbedding.birkhoffFinset a) = OrderEmb
edding.birkhoffSet a
参数：a : α；OrderEmbedding.birkhoffFinset a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `OrderIso.coe_toOrderEmbedding`：coe_toOrderEmbedding (e : α ≃o β) : ⇑e.to
OrderEmbedding = e
· 使用定理 `Fintype.finsetEquivSet_symm_apply`：∀ {α : Type u_1} [inst : Fintype α] (
s : Set α) [inst_1 : Fintype ↑s], Fintype.finsetEquivSet.symm s = s.toFinset
· 使用定理 `Set.coe_toFinset`：coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : 
Set α) = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma coe_birkhoffFinset (a : α) : birkhoffFinset a = birkhoffSet a := by
  classical
  -- TODO: This should be a single `simp` call but `simp` refuses to use
  -- `OrderIso.coe_toOrderEmbedding` and `Fintype.coe_finsetOrderIsoSet_symm`
  simp [birkhoffFinset, (OrderIso.coe_toOrderEmbedding)]
/-
**OrderEmbedding.birkhoffSet_sup** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：∀ {α : Type u_1} [inst : DistribLattice α] [inst_1 : Fintype α] [inst_2 : 
DecidablePred SupIrred] (a b : α),   OrderEmbedding.birkhoffSet (a ⊔ b) = OrderE
mbedding.birkhoffSet a ∪ OrderEmbedding.birkhoffSet b
参数：a b : α；a ⊔ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SupHomClass.map_sup`：∀ {F : Type u_6} {α : Type u_7} {β : Type u_8} {ins
t : Max α} {inst_1 : Max β} {inst_2 : FunLike F α β}   [self : SupHomClass F α β
] (f : F)…
· 使用定理 `LatticeHomClass.toSupHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type
 u_8} {inst : Lattice α} {inst_1 : Lattice β} {inst_2 : FunLike F α β}   [self :
 LatticeHomClass F …
· 使用定理 `OrderIsoClass.toLatticeHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Ty
pe u_3} [inst : EquivLike F α β] [inst_1 : Lattice α] [inst_2 : Lattice β]   [Or
derIsoClass F α β], L…
· 使用定理 `OrderIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α
] [inst_1 : LE β], OrderIsoClass (α ≃o β) α β
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `OrderEmbedding.ofIsEmpty_apply`：∀ {α : Type u_2} {β : Type u_3} [inst : 
Preorder α] [inst_1 : Preorder β] [inst_2 : IsEmpty α] (a : α),   OrderEmbedding
.ofIsEmpty a = isEmp…
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `instIsEmptySubtype`：∀ {α : Sort u} [IsEmpty α] (p : α → Prop), IsEmpty (
Subtype p)
-/
@[simp] lemma birkhoffSet_sup (a b : α) : birkhoffSet (a ⊔ b) = birkhoffSet a ∪ birkhoffSet b := by
  unfold OrderEmbedding.birkhoffSet; split <;> simp [eq_iff_true_of_subsingleton]
/-
**OrderEmbedding.birkhoffSet_inf** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：∀ {α : Type u_1} [inst : DistribLattice α] [inst_1 : Fintype α] [inst_2 : 
DecidablePred SupIrred] (a b : α),   OrderEmbedding.birkhoffSet (a ⊓ b) = OrderE
mbedding.birkhoffSet a ∩ OrderEmbedding.birkhoffSet b
参数：a b : α；a ⊓ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `InfHomClass.map_inf`：∀ {F : Type u_6} {α : Type u_7} {β : Type u_8} {ins
t : Min α} {inst_1 : Min β} {inst_2 : FunLike F α β}   [self : InfHomClass F α β
] (f : F)…
· 使用定理 `LatticeHomClass.toInfHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type
 u_8} {inst : Lattice α} {inst_1 : Lattice β} {inst_2 : FunLike F α β}   [self :
 LatticeHomClass F …
· 使用定理 `OrderIsoClass.toLatticeHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Ty
pe u_3} [inst : EquivLike F α β] [inst_1 : Lattice α] [inst_2 : Lattice β]   [Or
derIsoClass F α β], L…
· 使用定理 `OrderIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α
] [inst_1 : LE β], OrderIsoClass (α ≃o β) α β
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `OrderEmbedding.ofIsEmpty_apply`：∀ {α : Type u_2} {β : Type u_3} [inst : 
Preorder α] [inst_1 : Preorder β] [inst_2 : IsEmpty α] (a : α),   OrderEmbedding
.ofIsEmpty a = isEmp…
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `instIsEmptySubtype`：∀ {α : Sort u} [IsEmpty α] (p : α → Prop), IsEmpty (
Subtype p)
-/
@[simp] lemma birkhoffSet_inf (a b : α) : birkhoffSet (a ⊓ b) = birkhoffSet a ∩ birkhoffSet b := by
  unfold OrderEmbedding.birkhoffSet; split <;> simp [eq_iff_true_of_subsingleton]
/-
**OrderEmbedding.birkhoffSet_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：∀ {α : Type u_1} [inst : DistribLattice α] [inst_1 : Fintype α] [inst_2 : 
DecidablePred SupIrred] [inst_3 : OrderBot α]   (a : α), OrderEmbedding.birkhoff
Set a = ↑(OrderIso.lowerSetSupIrred a)
参数：a : α；OrderIso.lowerSetSupIrred a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `bot_nonempty`：∀ (α : Type u_1) [Bot α], Nonempty α
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `Subsingleton.allEq`：∀ {α : Sort u} [self : Subsingleton α] (a b : α), a 
= b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma birkhoffSet_apply [OrderBot α] (a : α) :
    birkhoffSet a = OrderIso.lowerSetSupIrred a := by
  have : Subsingleton (OrderBot α) := inferInstance
  simp +instances [birkhoffSet, this.allEq]

variable [DecidableEq α]
/-
**OrderEmbedding.birkhoffFinset_sup** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：∀ {α : Type u_1} [inst : DistribLattice α] [inst_1 : Fintype α] [inst_2 : 
DecidablePred SupIrred]   [inst_3 : DecidableEq α] (a b : α),   OrderEmbedding.b
irkhoffFinset (a ⊔ b) = OrderEmbedding.birkhoffFinset a ∪ OrderEmbedding.birkhof
fFinset b
参数：a b : α；a ⊔ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderEmbedding.birkhoffSet_sup`：∀ {α : Type u_1} [inst : DistribLattice 
α] [inst_1 : Fintype α] [inst_2 : DecidablePred SupIrred] (a b : α),   OrderEmbe
dding.birkhoffSet (a…
· 使用定理 `Fintype.finsetEquivSet_symm_apply`：∀ {α : Type u_1} [inst : Fintype α] (
s : Set α) [inst_1 : Fintype ↑s], Fintype.finsetEquivSet.symm s = s.toFinset
· 使用定理 `Set.toFinset_union`：toFinset_union [Fintype (s union t : Set _)] : (s un
ion t).toFinset = s.toFinset union t.toFinset
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma birkhoffFinset_sup (a b : α) :
    birkhoffFinset (a ⊔ b) = birkhoffFinset a ∪ birkhoffFinset b := by
  classical
  dsimp [OrderEmbedding.birkhoffFinset]
  simp [birkhoffSet_sup]
/-
**OrderEmbedding.birkhoffFinset_inf** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：∀ {α : Type u_1} [inst : DistribLattice α] [inst_1 : Fintype α] [inst_2 : 
DecidablePred SupIrred]   [inst_3 : DecidableEq α] (a b : α),   OrderEmbedding.b
irkhoffFinset (a ⊓ b) = OrderEmbedding.birkhoffFinset a ∩ OrderEmbedding.birkhof
fFinset b
参数：a b : α；a ⊓ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderEmbedding.birkhoffSet_inf`：∀ {α : Type u_1} [inst : DistribLattice 
α] [inst_1 : Fintype α] [inst_2 : DecidablePred SupIrred] (a b : α),   OrderEmbe
dding.birkhoffSet (a…
· 使用定理 `Fintype.finsetEquivSet_symm_apply`：∀ {α : Type u_1} [inst : Fintype α] (
s : Set α) [inst_1 : Fintype ↑s], Fintype.finsetEquivSet.symm s = s.toFinset
· 使用定理 `Set.toFinset_inter`：toFinset_inter [Fintype (s inter t : Set _)] : (s in
ter t).toFinset = s.toFinset inter t.toFinset
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma birkhoffFinset_inf (a b : α) :
    birkhoffFinset (a ⊓ b) = birkhoffFinset a ∩ birkhoffFinset b := by
  classical
  dsimp [OrderEmbedding.birkhoffFinset]
  simp [birkhoffSet_inf]

end OrderEmbedding

namespace LatticeHom

/-- **Birkhoff's Representation Theorem**. Any finite distributive lattice can be embedded in a
powerset lattice. -/
/-
**LatticeHom.birkhoffSet** 是 Mathlib 中的一个定义，位于命名空间 `LatticeHom`。
形式化陈述：birkhoffSet : LatticeHom α (Set {a : α // SupIrred a}) where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.birkhoffSet_sup`：∀ {α : Type u_1} [inst : DistribLattice 
α] [inst_1 : Fintype α] [inst_2 : DecidablePred SupIrred] (a b : α),   OrderEmbe
dding.birkhoffSet (a…
· 使用定理 `OrderEmbedding.birkhoffSet_inf`：∀ {α : Type u_1} [inst : DistribLattice 
α] [inst_1 : Fintype α] [inst_2 : DecidablePred SupIrred] (a b : α),   OrderEmbe
dding.birkhoffSet (a…

--- 原说明 ---
**Birkhoff's Representation Theorem**. Any finite distributive lattice can be em
bedded in a
powerset lattice.
-/
noncomputable def birkhoffSet : LatticeHom α (Set {a : α // SupIrred a}) where
  toFun := OrderEmbedding.birkhoffSet
  map_sup' := OrderEmbedding.birkhoffSet_sup
  map_inf' := OrderEmbedding.birkhoffSet_inf

open scoped Classical in
/-- **Birkhoff's Representation Theorem**. Any finite distributive lattice can be embedded in a
powerset lattice. -/
/-
**LatticeHom.birkhoffFinset** 是 Mathlib 中的一个定义，位于命名空间 `LatticeHom`。
形式化陈述：birkhoffFinset : LatticeHom α (Finset {a : α // SupIrred a}) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Birkhoff's Representation Theorem**. Any finite distributive lattice can be em
bedded in a
powerset lattice.
-/
noncomputable def birkhoffFinset : LatticeHom α (Finset {a : α // SupIrred a}) where
  toFun := OrderEmbedding.birkhoffFinset
  map_sup' := OrderEmbedding.birkhoffFinset_sup
  map_inf' := OrderEmbedding.birkhoffFinset_inf
/-
**LatticeHom.birkhoffFinset_injective** 是 Mathlib 中的一个引理，位于命名空间 `LatticeHom`。
形式化陈述：birkhoffFinset_injective : Injective (birkhoffFinset (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.injective`：injective (f : r ↪r s) : Injective f
-/
lemma birkhoffFinset_injective : Injective (birkhoffFinset (α := α)) :=
  OrderEmbedding.birkhoffFinset.injective

end LatticeHom

/-
**exists_birkhoff_representation.** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exists_birkhoff_representation.{u} (α : Type u) [Finite α] [DistribLattice α] :
    ∃ (β : Type u) (_ : DecidableEq β) (_ : Fintype β) (f : LatticeHom α (Finset β)),
      Injective f := by
  classical
  cases nonempty_fintype α
  exact ⟨{a : α // SupIrred a}, _, inferInstance, _, LatticeHom.birkhoffFinset_injective⟩

end DistribLattice

