/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Sum.Order
public import Mathlib.Order.Hom.Lattice

/-!
# Lexicographic sum of lattices

This file proves that we can combine two lattices `α` and `β` into a lattice `α ⊕ₗ β` where
everything in `α` is declared smaller than everything in `β`.
-/

@[expose] public section

open OrderDual

namespace Sum.Lex
variable {α β : Type*}

section SemilatticeSup
variable [SemilatticeSup α] [SemilatticeSup β]

-- The linter significantly hinders readability here.
set_option linter.unusedVariables false in
/-
**Sum.Lex.instSemilatticeSup** 是 Mathlib 中的一个定义，位于命名空间 `Sum.Lex`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → [SemilatticeSup α] → [SemilatticeSup β] 
→ SemilatticeSup (α ⊕ₗ β)
参数：α ⊕ₗ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemilatticeSup : SemilatticeSup (α ⊕ₗ β) where
  sup
    | inlₗ a₁, inlₗ a₂ => inl (a₁ ⊔ a₂)
    | inlₗ a₁, inrₗ b₂ => inr b₂
    | inrₗ b₁, inlₗ a₂ => inr b₁
    | inrₗ b₁, inrₗ b₂ => inr (b₁ ⊔ b₂)
  le_sup_left
    | inlₗ a₁, inlₗ a₂ => inl_le_inl_iff.2 le_sup_left
    | inlₗ a₁, inrₗ b₂ => inl_le_inr _ _
    | inrₗ b₁, inlₗ a₂ => le_rfl
    | inrₗ b₁, inrₗ b₂ => inr_le_inr_iff.2 le_sup_left
  le_sup_right
    | inlₗ a₁, inlₗ a₂ => inl_le_inl_iff.2 le_sup_right
    | inlₗ a₁, inrₗ b₂ => le_rfl
    | inrₗ b₁, inlₗ a₂ => inl_le_inr _ _
    | inrₗ b₁, inrₗ b₂ => inr_le_inr_iff.2 le_sup_right
  sup_le
    | inlₗ a₁, inlₗ a₂, inlₗ a₃, Lex.inl h₁₃, Lex.inl h₂₃ => inl_le_inl_iff.2 <| sup_le h₁₃ h₂₃
    | inlₗ a₁, inlₗ a₂, inrₗ b₃, Lex.sep _ _, Lex.sep _ _ => Lex.sep _ _
    | inlₗ a₁, inrₗ b₂, inrₗ b₃, Lex.sep _ _, Lex.inr h₂₃ => inr_le_inr_iff.2 h₂₃
    | inrₗ b₁, inlₗ a₂, inrₗ b₃, Lex.inr h₁₃, Lex.sep _ _ => inr_le_inr_iff.2 h₁₃
    | inrₗ b₁, inrₗ b₂, inrₗ b₃, Lex.inr h₁₃, Lex.inr h₂₃ => inr_le_inr_iff.2 <| sup_le h₁₃ h₂₃
/-
**Sum.Lex.inl_sup** 是 Mathlib 中的一个定理，位于命名空间 `Sum.Lex`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : SemilatticeSup α] [inst_1 : Semila
tticeSup β] (a₁ a₂ : α),   Sum.inlₗ (a₁ ⊔ a₂) = Sum.inlₗ a₁ ⊔ Sum.inlₗ a₂
参数：a₁ a₂ : α；a₁ ⊔ a₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma inl_sup (a₁ a₂ : α) : (inlₗ (a₁ ⊔ a₂) : α ⊕ β) = inlₗ a₁ ⊔ inlₗ a₂ := rfl
/-
**Sum.Lex.inr_sup** 是 Mathlib 中的一个定理，位于命名空间 `Sum.Lex`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : SemilatticeSup α] [inst_1 : Semila
tticeSup β] (b₁ b₂ : β),   Sum.inrₗ (b₁ ⊔ b₂) = Sum.inrₗ b₁ ⊔ Sum.inrₗ b₂
参数：b₁ b₂ : β；b₁ ⊔ b₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma inr_sup (b₁ b₂ : β) : (inrₗ (b₁ ⊔ b₂) : α ⊕ β) = inrₗ b₁ ⊔ inrₗ b₂ := rfl

end SemilatticeSup

section SemilatticeInf
variable [SemilatticeInf α] [SemilatticeInf β]

-- The linter significantly hinders readability here.
set_option linter.unusedVariables false in
/-
**Sum.Lex.instSemilatticeInf** 是 Mathlib 中的一个定义，位于命名空间 `Sum.Lex`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → [SemilatticeInf α] → [SemilatticeInf β] 
→ SemilatticeInf (α ⊕ₗ β)
参数：α ⊕ₗ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemilatticeInf : SemilatticeInf (α ⊕ₗ β) where
  inf
    | inlₗ a₁, inlₗ a₂ => inl (a₁ ⊓ a₂)
    | inlₗ a₁, inrₗ b₂ => inl a₁
    | inrₗ b₁, inlₗ a₂ => inl a₂
    | inrₗ b₁, inrₗ b₂ => inr (b₁ ⊓ b₂)
  inf_le_left
    | inlₗ a₁, inlₗ a₂ => inl_le_inl_iff.2 inf_le_left
    | inlₗ a₁, inrₗ b₂ => le_rfl
    | inrₗ b₁, inlₗ a₂ => inl_le_inr _ _
    | inrₗ b₁, inrₗ b₂ => inr_le_inr_iff.2 inf_le_left
  inf_le_right
    | inlₗ a₁, inlₗ a₂ => inl_le_inl_iff.2 inf_le_right
    | inlₗ a₁, inrₗ b₂ => inl_le_inr _ _
    | inrₗ b₁, inlₗ a₂ => le_rfl
    | inrₗ b₁, inrₗ b₂ => inr_le_inr_iff.2 inf_le_right
  le_inf
    | inlₗ a₁, inlₗ a₂, inlₗ a₃, Lex.inl h₁₃, Lex.inl h₂₃ => inl_le_inl_iff.2 <| le_inf h₁₃ h₂₃
    | inlₗ a₁, inlₗ a₂, inrₗ b₃, Lex.inl h₁₃, Lex.sep _ _ => inl_le_inl_iff.2 h₁₃
    | inlₗ a₁, inrₗ b₂, inlₗ a₃, Lex.sep _ _, Lex.inl h₂₃ => inl_le_inl_iff.2 h₂₃
    | inlₗ a₁, inrₗ b₂, inrₗ b₃, Lex.sep _ _, Lex.sep _ _ => Lex.sep _ _
    | inrₗ b₁, inrₗ b₂, inrₗ b₃, Lex.inr h₁₃, Lex.inr h₂₃ => inr_le_inr_iff.2 <| le_inf h₁₃ h₂₃
/-
**Sum.Lex.inl_inf** 是 Mathlib 中的一个定理，位于命名空间 `Sum.Lex`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : SemilatticeInf α] [inst_1 : Semila
tticeInf β] (a₁ a₂ : α),   Sum.inlₗ (a₁ ⊓ a₂) = Sum.inlₗ a₁ ⊓ Sum.inlₗ a₂
参数：a₁ a₂ : α；a₁ ⊓ a₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma inl_inf (a₁ a₂ : α) : (inlₗ (a₁ ⊓ a₂) : α ⊕ β) = inlₗ a₁ ⊓ inlₗ a₂ := rfl
/-
**Sum.Lex.inr_inf** 是 Mathlib 中的一个定理，位于命名空间 `Sum.Lex`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : SemilatticeInf α] [inst_1 : Semila
tticeInf β] (b₁ b₂ : β),   Sum.inrₗ (b₁ ⊓ b₂) = Sum.inrₗ b₁ ⊓ Sum.inrₗ b₂
参数：b₁ b₂ : β；b₁ ⊓ b₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma inr_inf (b₁ b₂ : β) : (inrₗ (b₁ ⊓ b₂) : α ⊕ β) = inrₗ b₁ ⊓ inrₗ b₂ := rfl

end SemilatticeInf

section Lattice
variable [Lattice α] [Lattice β]

/-
**Sum.Lex.instLattice** 是 Mathlib 中的一个实例，位于命名空间 `Sum.Lex`。
形式化陈述：instLattice : Lattice (α oplusₗ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLattice : Lattice (α ⊕ₗ β) := { instSemilatticeSup, instSemilatticeInf with }

/-- `Sum.Lex.inlₗ` as a lattice homomorphism. -/
/-
**Sum.Lex.inlLatticeHom** 是 Mathlib 中的一个定义，位于命名空间 `Sum.Lex`。
形式化陈述：inlLatticeHom : LatticeHom α (α oplusₗ β) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Sum.Lex.inlₗ` as a lattice homomorphism.
-/
def inlLatticeHom : LatticeHom α (α ⊕ₗ β) where
  toFun := inlₗ
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

/-- `Sum.Lex.inrₗ` as a lattice homomorphism. -/
/-
**Sum.Lex.inrLatticeHom** 是 Mathlib 中的一个定义，位于命名空间 `Sum.Lex`。
形式化陈述：inrLatticeHom : LatticeHom β (α oplusₗ β) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Sum.Lex.inrₗ` as a lattice homomorphism.
-/
def inrLatticeHom : LatticeHom β (α ⊕ₗ β) where
  toFun := inrₗ
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

end Lattice

/-
**Sum.Lex.instDistribLattice** 是 Mathlib 中的一个实例，位于命名空间 `Sum.Lex`。
形式化陈述：instDistribLattice [DistribLattice α] [DistribLattice β] : DistribLattice 
(α oplusₗ β) where le_sup_inf
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDistribLattice [DistribLattice α] [DistribLattice β] : DistribLattice (α ⊕ₗ β) where
  le_sup_inf := by
    simp only [Lex.forall, Sum.forall, inr_le_inr_iff,
      le_sup_left, inl_le_inr, sup_of_le_right, and_self,
      inf_of_le_left, implies_true, inf_of_le_right, sup_of_le_left, ← inl_sup,
      ← inr_sup, ← inl_inf, ← inr_inf, sup_inf_left, le_rfl]

end Sum.Lex

