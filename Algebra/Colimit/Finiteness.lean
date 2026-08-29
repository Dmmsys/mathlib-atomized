/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.Colimit.Module
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Modules as direct limits of finitely generated submodules

We show that every module is the direct limit of its finitely generated submodules.

## Main definitions

* `Module.fgSystem`: the directed system of finitely generated submodules of a module.

* `Module.fgSystem.equiv`: the isomorphism between a module and the direct limit of its
  finitely generated submodules.
-/

@[expose] public section

namespace Module

variable (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]

/--
Definition of `fgSystem` / `fgSystem` 的定义

English:
definition fgSystem
  signature: (N₁ N₂ : {N : Submodule R M // N.FG}) (le : N₁ <= N₂)
  body: Submodule.inclusion le

中文:
定义 fgSystem
  签名: (N₁ N₂ : {N : 子模 R M // N.FG}) (le : N₁ <= N₂)
  定义体: Submodule.inclusion le

Depends on / 依赖: Submodule, Submodule.inclusion, inclusion
-/
def fgSystem (N₁ N₂ : {N : Submodule R M // N.FG}) (le : N₁ <= N₂) : N₁ ->ₗ[R] N₂ :=
  Submodule.inclusion le

open Module.DirectLimit

namespace fgSystem

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsDirectedOrder {N : Submodule R M // N.FG}
  body: ⟨⟨_, N₁.2.sup N₂.2⟩, Subtype.coe_le_coe.mp le_sup_left, Subtype.coe_le_coe.mp le_sup_right⟩

中文:
实例 :
  签名: IsDirectedOrder {N : 子模 R M // N.FG}
  定义体: ⟨⟨_, N₁.2.sup N₂.2⟩, Subtype.coe_le_coe.mp le_sup_left, Subtype.coe_le_coe.mp le_sup_right⟩

Depends on / 依赖: Subtype, Subtype.coe_le_coe.mp, coe_le_coe, le_sup_left, le_sup_right
-/
instance : IsDirectedOrder {N : Submodule R M // N.FG} where
  directed N₁ N₂ :=
    ⟨⟨_, N₁.2.sup N₂.2⟩, Subtype.coe_le_coe.mp le_sup_left, Subtype.coe_le_coe.mp le_sup_right⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DirectedSystem _ (fgSystem R M · · · ·)
  body: rfl
  map_map _ _ _ _ _ _ := rfl

中文:
实例 :
  签名: DirectedSystem _ (fgSystem R M · · · ·)
  定义体: rfl
  map_map _ _ _ _ _ _ := rfl
-/
instance : DirectedSystem _ (fgSystem R M · · · ·) where
  map_self _ _ := rfl
  map_map _ _ _ _ _ _ := rfl

variable [DecidableEq (Submodule R M)]

open Submodule in
/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: : DirectLimit _ (fgSystem R M) ≃ₗ[R] M
  body: .ofBijective (lift _ _ _ _ (fun _ => Submodule.subtype _) fun _ _ _ _ => rfl)
    ⟨lift_injective _ _ fun _ => Subtype.val_injective, fun x =>
⟨of _ _ _ _ ⟨_, fg_span_singleton x⟩ ⟨x, subset_span by rfl⟩, lift_of ..⟩⟩

中文:
定义 equiv
  签名: : DirectLimit _ (fgSystem R M) ≃ₗ[R] M
  定义体: .ofBijective (lift _ _ _ _ (fun _ => Submodule.subtype _) fun _ _ _ _ => rfl)
    ⟨lift_injective _ _ fun _ => Subtype.val_injective, fun x =>
⟨of _ _ _ _ ⟨_, fg_span_singleton x⟩ ⟨x, subset_span by rfl⟩, lift_of ..⟩⟩

Depends on / 依赖: Submodule, Submodule.subtype, Subtype, Subtype.val_injective, fg_span_singleton, lift_injective, lift_of, ofBijective, subset_span, subtype, val_injective
-/
noncomputable def equiv : DirectLimit _ (fgSystem R M) ≃ₗ[R] M :=
  .ofBijective (lift _ _ _ _ (fun _ => Submodule.subtype _) fun _ _ _ _ => rfl)
    ⟨lift_injective _ _ fun _ => Subtype.val_injective, fun x =>
⟨of _ _ _ _ ⟨_, fg_span_singleton x⟩ ⟨x, subset_span by rfl⟩, lift_of ..⟩⟩

variable {R M}

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `equiv_comp_of` / 引理 `equiv_comp_of`

English:
lemma equiv_comp_of
  given: (N : {N : Submodule R M // N.FG})
  proof: by
  ext; simp [equiv]

中文:
引理 equiv_comp_of
  条件: (N : {N : 子模 R M // N.FG})
  证明: by
  ext; simp [equiv]
-/
lemma equiv_comp_of (N : {N : Submodule R M // N.FG}) :
    (equiv R M).toLinearMap ∘ₗ of _ _ _ _ N = N.1.subtype := by
  ext; simp [equiv]

end fgSystem

end Module
