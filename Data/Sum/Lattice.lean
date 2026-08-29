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
/--
Instance `instSemilatticeSup` / 实例 `instSemilatticeSup`

English:
instance instSemilatticeSup
  signature: : SemilatticeSup (α oplusₗ β) where

中文:
实例 instSemilatticeSup
  签名: : SemilatticeSup (α oplusₗ β) where
-/
instance instSemilatticeSup : SemilatticeSup (α oplusₗ β) where
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
| inlₗ a₁, inlₗ a₂, inlₗ a₃, Lex.inl h₁₃, Lex.inl h₂₃ => inl_le_inl_iff.2 sup_le h₁₃ h₂₃
    | inlₗ a₁, inlₗ a₂, inrₗ b₃, Lex.sep _ _, Lex.sep _ _ => Lex.sep _ _
    | inlₗ a₁, inrₗ b₂, inrₗ b₃, Lex.sep _ _, Lex.inr h₂₃ => inr_le_inr_iff.2 h₂₃
    | inrₗ b₁, inlₗ a₂, inrₗ b₃, Lex.inr h₁₃, Lex.sep _ _ => inr_le_inr_iff.2 h₁₃
| inrₗ b₁, inrₗ b₂, inrₗ b₃, Lex.inr h₁₃, Lex.inr h₂₃ => inr_le_inr_iff.2 sup_le h₁₃ h₂₃

/--
lemma `inl_sup` / 引理 `inl_sup`

English:
lemma inl_sup
  given: (a₁ a₂ : α)
  statement: (inlₗ (a₁ ⊔ a₂) : α oplus β) = inlₗ a₁ ⊔ inlₗ a₂
  proof: rfl

中文:
引理 inl_sup
  条件: (a₁ a₂ : α)
  结论: (inlₗ (a₁ ⊔ a₂) : α oplus β) = inlₗ a₁ ⊔ inlₗ a₂
  证明: rfl
-/
@[simp] lemma inl_sup (a₁ a₂ : α) : (inlₗ (a₁ ⊔ a₂) : α oplus β) = inlₗ a₁ ⊔ inlₗ a₂ := rfl
/--
lemma `inr_sup` / 引理 `inr_sup`

English:
lemma inr_sup
  given: (b₁ b₂ : β)
  statement: (inrₗ (b₁ ⊔ b₂) : α oplus β) = inrₗ b₁ ⊔ inrₗ b₂
  proof: rfl

中文:
引理 inr_sup
  条件: (b₁ b₂ : β)
  结论: (inrₗ (b₁ ⊔ b₂) : α oplus β) = inrₗ b₁ ⊔ inrₗ b₂
  证明: rfl
-/
@[simp] lemma inr_sup (b₁ b₂ : β) : (inrₗ (b₁ ⊔ b₂) : α oplus β) = inrₗ b₁ ⊔ inrₗ b₂ := rfl

end SemilatticeSup

section SemilatticeInf
variable [SemilatticeInf α] [SemilatticeInf β]

-- The linter significantly hinders readability here.
set_option linter.unusedVariables false in
/--
Instance `instSemilatticeInf` / 实例 `instSemilatticeInf`

English:
instance instSemilatticeInf
  signature: : SemilatticeInf (α oplusₗ β) where

中文:
实例 instSemilatticeInf
  签名: : SemilatticeInf (α oplusₗ β) where
-/
instance instSemilatticeInf : SemilatticeInf (α oplusₗ β) where
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
| inlₗ a₁, inlₗ a₂, inlₗ a₃, Lex.inl h₁₃, Lex.inl h₂₃ => inl_le_inl_iff.2 le_inf h₁₃ h₂₃
    | inlₗ a₁, inlₗ a₂, inrₗ b₃, Lex.inl h₁₃, Lex.sep _ _ => inl_le_inl_iff.2 h₁₃
    | inlₗ a₁, inrₗ b₂, inlₗ a₃, Lex.sep _ _, Lex.inl h₂₃ => inl_le_inl_iff.2 h₂₃
    | inlₗ a₁, inrₗ b₂, inrₗ b₃, Lex.sep _ _, Lex.sep _ _ => Lex.sep _ _
| inrₗ b₁, inrₗ b₂, inrₗ b₃, Lex.inr h₁₃, Lex.inr h₂₃ => inr_le_inr_iff.2 le_inf h₁₃ h₂₃

/--
lemma `inl_inf` / 引理 `inl_inf`

English:
lemma inl_inf
  given: (a₁ a₂ : α)
  statement: (inlₗ (a₁ ⊓ a₂) : α oplus β) = inlₗ a₁ ⊓ inlₗ a₂
  proof: rfl

中文:
引理 inl_inf
  条件: (a₁ a₂ : α)
  结论: (inlₗ (a₁ ⊓ a₂) : α oplus β) = inlₗ a₁ ⊓ inlₗ a₂
  证明: rfl
-/
@[simp] lemma inl_inf (a₁ a₂ : α) : (inlₗ (a₁ ⊓ a₂) : α oplus β) = inlₗ a₁ ⊓ inlₗ a₂ := rfl
/--
lemma `inr_inf` / 引理 `inr_inf`

English:
lemma inr_inf
  given: (b₁ b₂ : β)
  statement: (inrₗ (b₁ ⊓ b₂) : α oplus β) = inrₗ b₁ ⊓ inrₗ b₂
  proof: rfl

中文:
引理 inr_inf
  条件: (b₁ b₂ : β)
  结论: (inrₗ (b₁ ⊓ b₂) : α oplus β) = inrₗ b₁ ⊓ inrₗ b₂
  证明: rfl
-/
@[simp] lemma inr_inf (b₁ b₂ : β) : (inrₗ (b₁ ⊓ b₂) : α oplus β) = inrₗ b₁ ⊓ inrₗ b₂ := rfl

end SemilatticeInf

section Lattice
variable [Lattice α] [Lattice β]

/--
Instance `instLattice` / 实例 `instLattice`

English:
instance instLattice
  signature: : Lattice (α oplusₗ β)
  body: { instSemilatticeSup, instSemilatticeInf with }

中文:
实例 instLattice
  签名: : 格 (α oplusₗ β)
  定义体: { instSemilatticeSup, instSemilatticeInf with }

Depends on / 依赖: instSemilatticeInf, instSemilatticeSup
-/
instance instLattice : Lattice (α oplusₗ β) := { instSemilatticeSup, instSemilatticeInf with }

/--
Definition of `inlLatticeHom` / `inlLatticeHom` 的定义

English:
definition inlLatticeHom
  signature: : LatticeHom α (α oplusₗ β) where
  body: inlₗ
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

中文:
定义 inlLatticeHom
  签名: : 格态射 α (α oplusₗ β) where
  定义体: inlₗ
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl
-/
def inlLatticeHom : LatticeHom α (α oplusₗ β) where
  toFun := inlₗ
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

/--
Definition of `inrLatticeHom` / `inrLatticeHom` 的定义

English:
definition inrLatticeHom
  signature: : LatticeHom β (α oplusₗ β) where
  body: inrₗ
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

中文:
定义 inrLatticeHom
  签名: : 格态射 β (α oplusₗ β) where
  定义体: inrₗ
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl
-/
def inrLatticeHom : LatticeHom β (α oplusₗ β) where
  toFun := inrₗ
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

end Lattice

/--
Instance `instDistribLattice` / 实例 `instDistribLattice`

English:
instance instDistribLattice
  signature: [DistribLattice α] [DistribLattice β]
  body: by
    simp only [Lex.forall, Sum.forall, inr_le_inr_iff,
      le_sup_left, inl_le_inr, sup_of_le_right, and_self,
      inf_of_le_left, implies_true, inf_of_le_right, sup_of_le_left, ← inl_sup,
      ← inr_sup, ← inl_inf, ← inr_inf, sup_inf_left, le_rfl]

中文:
实例 instDistribLattice
  签名: [Distrib格 α] [Distrib格 β]
  定义体: by
    simp only [Lex.forall, Sum.forall, inr_le_inr_iff,
      le_sup_left, inl_le_inr, sup_of_le_right, and_self,
      inf_of_le_left, implies_true, inf_of_le_right, sup_of_le_left, ← inl_sup,
      ← inr_sup, ← inl_inf, ← inr_inf, sup_inf_left, le_rfl]

Depends on / 依赖: Lex.forall, Sum.forall, and_self, implies_true, inf_of_le_left, inf_of_le_right, inl_inf, inl_le_inr, inl_sup, inr_inf, inr_le_inr_iff, inr_sup, le_rfl, le_sup_left, sup_inf_left, sup_of_le_left, sup_of_le_right
-/
instance instDistribLattice [DistribLattice α] [DistribLattice β] : DistribLattice (α oplusₗ β) where
  le_sup_inf := by
    simp only [Lex.forall, Sum.forall, inr_le_inr_iff,
      le_sup_left, inl_le_inr, sup_of_le_right, and_self,
      inf_of_le_left, implies_true, inf_of_le_right, sup_of_le_left, ← inl_sup,
      ← inr_sup, ← inl_inf, ← inr_inf, sup_inf_left, le_rfl]

end Sum.Lex
