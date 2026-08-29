/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Anne Baanen
-/
module

public import Mathlib.Logic.Function.Iterate
public import Mathlib.Order.GaloisConnection.Basic
public import Mathlib.Order.Hom.Basic

/-!
# Lattice structure on order homomorphisms

This file defines the lattice structure on order homomorphisms, which are bundled
monotone functions.

## Main definitions

* `OrderHom.instCompleteLattice`: if `β` is a complete lattice, so is `α →o β`

## Tags

monotone map, bundled morphism
-/

public section


namespace OrderHom

variable {α β : Type*}

section Preorder

variable [Preorder α]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SemilatticeSup
  signature: β] : Max (α ->o β) where
  body: ⟨fun a => f a ⊔ g a, f.mono.sup g.mono⟩

中文:
实例 [SemilatticeSup
  签名: β] : 最大值 (α ->o β) where
  定义体: ⟨fun a => f a ⊔ g a, f.mono.sup g.mono⟩

Depends on / 依赖: f.mono.sup, g.mono
-/
instance [SemilatticeSup β] : Max (α ->o β) where
  max f g := ⟨fun a => f a ⊔ g a, f.mono.sup g.mono⟩

/--
lemma `coe_sup` / 引理 `coe_sup`

English:
lemma coe_sup
  given: [SemilatticeSup β] (f g : α ->o β)
  proof: rfl

中文:
引理 coe_sup
  条件: [SemilatticeSup β] (f g : α ->o β)
  证明: rfl
-/
@[simp] lemma coe_sup [SemilatticeSup β] (f g : α ->o β) :
    ((f ⊔ g : α ->o β) : α -> β) = (f : α -> β) ⊔ g := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SemilatticeSup
  signature: β] : SemilatticeSup (α ->o β)
  body: { (_ : PartialOrder (α ->o β)) with
    sup := Max.max
    le_sup_left := fun _ _ _ => le_sup_left
    le_sup_right := fun _ _ _ => le_sup_right
    sup_le := fun _ _ _ h₀ h₁ x => sup_le (h₀ x) (h₁ x) }

中文:
实例 [SemilatticeSup
  签名: β] : SemilatticeSup (α ->o β)
  定义体: { (_ : PartialOrder (α ->o β)) with
    sup := Max.max
    le_sup_left := fun _ _ _ => le_sup_left
    le_sup_right := fun _ _ _ => le_sup_right
    sup_le := fun _ _ _ h₀ h₁ x => sup_le (h₀ x) (h₁ x) }

Depends on / 依赖: Max.max, PartialOrder, le_sup_left, le_sup_right, sup_le
-/
instance [SemilatticeSup β] : SemilatticeSup (α ->o β) :=
  { (_ : PartialOrder (α ->o β)) with
    sup := Max.max
    le_sup_left := fun _ _ _ => le_sup_left
    le_sup_right := fun _ _ _ => le_sup_right
    sup_le := fun _ _ _ h₀ h₁ x => sup_le (h₀ x) (h₁ x) }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SemilatticeInf
  signature: β] : Min (α ->o β) where
  body: ⟨fun a => f a ⊓ g a, f.mono.inf g.mono⟩

中文:
实例 [SemilatticeInf
  签名: β] : 最小值 (α ->o β) where
  定义体: ⟨fun a => f a ⊓ g a, f.mono.inf g.mono⟩

Depends on / 依赖: f.mono.inf, g.mono
-/
instance [SemilatticeInf β] : Min (α ->o β) where
  min f g := ⟨fun a => f a ⊓ g a, f.mono.inf g.mono⟩

/--
lemma `coe_inf` / 引理 `coe_inf`

English:
lemma coe_inf
  given: [SemilatticeInf β] (f g : α ->o β)
  proof: rfl

中文:
引理 coe_inf
  条件: [SemilatticeInf β] (f g : α ->o β)
  证明: rfl
-/
@[simp] lemma coe_inf [SemilatticeInf β] (f g : α ->o β) :
    ((f ⊓ g : α ->o β) : α -> β) = (f : α -> β) ⊓ g := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SemilatticeInf
  signature: β] : SemilatticeInf (α ->o β)
  body: { (_ : PartialOrder (α ->o β)), (dualIso α β).symm.toGaloisInsertion.liftSemilatticeInf with
    inf := (· ⊓ ·) }

中文:
实例 [SemilatticeInf
  签名: β] : SemilatticeInf (α ->o β)
  定义体: { (_ : PartialOrder (α ->o β)), (dualIso α β).symm.toGaloisInsertion.liftSemilatticeInf with
    inf := (· ⊓ ·) }

Depends on / 依赖: PartialOrder, dualIso, liftSemilatticeInf, symm.toGaloisInsertion.liftSemilatticeInf, toGaloisInsertion
-/
instance [SemilatticeInf β] : SemilatticeInf (α ->o β) :=
  { (_ : PartialOrder (α ->o β)), (dualIso α β).symm.toGaloisInsertion.liftSemilatticeInf with
    inf := (· ⊓ ·) }

/--
Instance `lattice` / 实例 `lattice`

English:
instance lattice
  signature: [Lattice β]
  body: { (_ : SemilatticeSup (α ->o β)), (_ : SemilatticeInf (α ->o β)) with }

@[simps]

中文:
实例 lattice
  签名: [格 β]
  定义体: { (_ : SemilatticeSup (α ->o β)), (_ : SemilatticeInf (α ->o β)) with }

@[simps]

Depends on / 依赖: SemilatticeInf, SemilatticeSup
-/
instance lattice [Lattice β] : Lattice (α ->o β) :=
  { (_ : SemilatticeSup (α ->o β)), (_ : SemilatticeInf (α ->o β)) with }

@[simps]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: β] [OrderBot β] : Bot (α ->o β) where
  body: const α ⊥

中文:
实例 [预序
  签名: β] [有底序 β] : 底元素 (α ->o β) where
  定义体: const α ⊥
-/
instance [Preorder β] [OrderBot β] : Bot (α ->o β) where
  bot := const α ⊥

/--
Instance `orderBot` / 实例 `orderBot`

English:
instance orderBot
  signature: [Preorder β] [OrderBot β]
  body: bot_le

@[simps]

中文:
实例 orderBot
  签名: [预序 β] [有底序 β]
  定义体: bot_le

@[simps]

Depends on / 依赖: bot_le
-/
instance orderBot [Preorder β] [OrderBot β] : OrderBot (α ->o β) where
  bot_le _ _ := bot_le

@[simps]
/--
Instance `instTopOrderHom` / 实例 `instTopOrderHom`

English:
instance instTopOrderHom
  signature: [Preorder β] [OrderTop β]
  body: const α ⊤

中文:
实例 instTopOrderHom
  签名: [预序 β] [有顶序 β]
  定义体: const α ⊤
-/
instance instTopOrderHom [Preorder β] [OrderTop β] : Top (α ->o β) where
  top := const α ⊤

/--
Instance `orderTop` / 实例 `orderTop`

English:
instance orderTop
  signature: [Preorder β] [OrderTop β]
  body: le_top

中文:
实例 orderTop
  签名: [预序 β] [有顶序 β]
  定义体: le_top

Depends on / 依赖: le_top
-/
instance orderTop [Preorder β] [OrderTop β] : OrderTop (α ->o β) where
  le_top _ _ := le_top

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompleteLattice
  signature: β] : InfSet (α ->o β) where
  body: ⟨fun x => ⨅ f in s, (f :) x, fun _ _ h => iInf₂_mono fun f _ => f.mono h⟩

@[simp]

中文:
实例 [完备格
  签名: β] : 下确界集 (α ->o β) where
  定义体: ⟨fun x => ⨅ f in s, (f :) x, fun _ _ h => iInf₂_mono fun f _ => f.mono h⟩

@[simp]

Depends on / 依赖: f.mono
-/
instance [CompleteLattice β] : InfSet (α ->o β) where
  sInf s := ⟨fun x => ⨅ f in s, (f :) x, fun _ _ h => iInf₂_mono fun f _ => f.mono h⟩

@[simp]
/--
theorem `sInf_apply` / 定理 `sInf_apply`

English:
theorem sInf_apply
  given: [CompleteLattice β] (s : Set (α ->o β)) (x : α)
  proof: rfl

中文:
定理 sInf_apply
  条件: [完备格 β] (s : 集合 (α ->o β)) (x : α)
  证明: rfl
-/
theorem sInf_apply [CompleteLattice β] (s : Set (α ->o β)) (x : α) :
    sInf s x = ⨅ f in s, (f :) x :=
  rfl

/--
theorem `iInf_apply` / 定理 `iInf_apply`

English:
theorem iInf_apply
  given: {ι : Sort*} [CompleteLattice β] (f : ι -> α ->o β) (x : α)
  proof: (sInf_apply _ _).trans iInf_range

@[simp, norm_cast]

中文:
定理 iInf_apply
  条件: {ι : 类型层*} [完备格 β] (f : ι -> α ->o β) (x : α)
  证明: (sInf_apply _ _).trans iInf_range

@[simp, norm_cast]

Depends on / 依赖: iInf_range, sInf_apply
-/
theorem iInf_apply {ι : Sort*} [CompleteLattice β] (f : ι -> α ->o β) (x : α) :
    (⨅ i, f i) x = ⨅ i, f i x :=
  (sInf_apply _ _).trans iInf_range

@[simp, norm_cast]
/--
theorem `coe_iInf` / 定理 `coe_iInf`

English:
theorem coe_iInf
  given: {ι : Sort*} [CompleteLattice β] (f : ι -> α ->o β)
  proof: by
  funext x; simp [iInf_apply]

中文:
定理 coe_iInf
  条件: {ι : 类型层*} [完备格 β] (f : ι -> α ->o β)
  证明: by
  funext x; simp [iInf_apply]

Depends on / 依赖: iInf_apply
-/
theorem coe_iInf {ι : Sort*} [CompleteLattice β] (f : ι -> α ->o β) :
    ((⨅ i, f i : α ->o β) : α -> β) = ⨅ i, (f i : α -> β) := by
  funext x; simp [iInf_apply]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompleteLattice
  signature: β] : SupSet (α ->o β) where
  body: ⟨fun x => ⨆ f in s, (f :) x, fun _ _ h => iSup₂_mono fun f _ => f.mono h⟩

@[simp]

中文:
实例 [完备格
  签名: β] : 上确界集 (α ->o β) where
  定义体: ⟨fun x => ⨆ f in s, (f :) x, fun _ _ h => iSup₂_mono fun f _ => f.mono h⟩

@[simp]

Depends on / 依赖: f.mono
-/
instance [CompleteLattice β] : SupSet (α ->o β) where
  sSup s := ⟨fun x => ⨆ f in s, (f :) x, fun _ _ h => iSup₂_mono fun f _ => f.mono h⟩

@[simp]
/--
theorem `sSup_apply` / 定理 `sSup_apply`

English:
theorem sSup_apply
  given: [CompleteLattice β] (s : Set (α ->o β)) (x : α)
  proof: rfl

中文:
定理 sSup_apply
  条件: [完备格 β] (s : 集合 (α ->o β)) (x : α)
  证明: rfl
-/
theorem sSup_apply [CompleteLattice β] (s : Set (α ->o β)) (x : α) :
    sSup s x = ⨆ f in s, (f :) x :=
  rfl

/--
theorem `iSup_apply` / 定理 `iSup_apply`

English:
theorem iSup_apply
  given: {ι : Sort*} [CompleteLattice β] (f : ι -> α ->o β) (x : α)
  proof: (sSup_apply _ _).trans iSup_range

@[simp, norm_cast]

中文:
定理 iSup_apply
  条件: {ι : 类型层*} [完备格 β] (f : ι -> α ->o β) (x : α)
  证明: (sSup_apply _ _).trans iSup_range

@[simp, norm_cast]

Depends on / 依赖: iSup_range, sSup_apply
-/
theorem iSup_apply {ι : Sort*} [CompleteLattice β] (f : ι -> α ->o β) (x : α) :
    (⨆ i, f i) x = ⨆ i, f i x :=
  (sSup_apply _ _).trans iSup_range

@[simp, norm_cast]
/--
theorem `coe_iSup` / 定理 `coe_iSup`

English:
theorem coe_iSup
  given: {ι : Sort*} [CompleteLattice β] (f : ι -> α ->o β)
  proof: by
  funext x; simp [iSup_apply]

中文:
定理 coe_iSup
  条件: {ι : 类型层*} [完备格 β] (f : ι -> α ->o β)
  证明: by
  funext x; simp [iSup_apply]

Depends on / 依赖: iSup_apply
-/
theorem coe_iSup {ι : Sort*} [CompleteLattice β] (f : ι -> α ->o β) :
    ((⨆ i, f i : α ->o β) : α -> β) = ⨆ i, (f i : α -> β) := by
  funext x; simp [iSup_apply]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompleteLattice
  signature: β] : CompleteLattice (α ->o β)
  body: { (_ : Lattice (α ->o β)), OrderHom.orderTop, OrderHom.orderBot with
    isLUB_sSup _ :=
      .of_image (f := (⇑)) coe_le_coe (by simp [isLUB_pi, Set.image_image, isLUB_biSup])
    isGLB_sInf _ :=
      .of_image (f := (⇑)) coe_le_coe (by simp [isGLB_pi, Set.image_image, isGLB_biInf]) }

中文:
实例 [完备格
  签名: β] : 完备格 (α ->o β)
  定义体: { (_ : Lattice (α ->o β)), OrderHom.orderTop, OrderHom.orderBot with
    isLUB_sSup _ :=
      .of_image (f := (⇑)) coe_le_coe (by simp [isLUB_pi, Set.image_image, isLUB_biSup])
    isGLB_sInf _ :=
      .of_image (f := (⇑)) coe_le_coe (by simp [isGLB_pi, Set.image_image, isGLB_biInf]) }

Depends on / 依赖: Lattice, OrderHom, OrderHom.orderBot, OrderHom.orderTop, Set.image_image, coe_le_coe, image_image, isGLB_biInf, isGLB_pi, isGLB_sInf, isLUB_biSup, isLUB_pi, isLUB_sSup, of_image, orderBot, orderTop
-/
instance [CompleteLattice β] : CompleteLattice (α ->o β) :=
  { (_ : Lattice (α ->o β)), OrderHom.orderTop, OrderHom.orderBot with
    isLUB_sSup _ :=
      .of_image (f := (⇑)) coe_le_coe (by simp [isLUB_pi, Set.image_image, isLUB_biSup])
    isGLB_sInf _ :=
      .of_image (f := (⇑)) coe_le_coe (by simp [isGLB_pi, Set.image_image, isGLB_biInf]) }

/--
theorem `iterate_sup_le_sup_iff` / 定理 `iterate_sup_le_sup_iff`

English:
theorem iterate_sup_le_sup_iff
  given: {α : Type*} [SemilatticeSup α] (f : α ->o α)
  proof: by
  constructor <;> intro h
  · exact h 1 0
  · intro n₁ n₂ a₁ a₂
    have h' : forall n a₁ a₂, f^[n] (a₁ ⊔ a₂) <= f^[n] a₁ ⊔ a₂ := by
      intro n
      induction n with
      | zero => intro a₁ a₂; rfl
      | succ n ih =>
        intro a₁ a₂
        calc
          f^[n + 1] (a₁ ⊔ a₂) = f^[n] (f

中文:
定理 iterate_sup_le_sup_iff
  条件: {α : 类型} [SemilatticeSup α] (f : α ->o α)
  证明: by
  constructor <;> intro h
  · exact h 1 0
  · intro n₁ n₂ a₁ a₂
    have h' : forall n a₁ a₂, f^[n] (a₁ ⊔ a₂) <= f^[n] a₁ ⊔ a₂ := by
      intro n
      induction n with
      | zero => intro a₁ a₂; rfl
      | succ n ih =>
        intro a₁ a₂
        calc
          f^[n + 1] (a₁ ⊔ a₂) = f^[n] (f

Depends on / 依赖: Function, Function.iterate_succ_apply, f.mono.iterate, iterate, iterate_succ_apply
-/
theorem iterate_sup_le_sup_iff {α : Type*} [SemilatticeSup α] (f : α ->o α) :
    (forall n₁ n₂ a₁ a₂, f^[n₁ + n₂] (a₁ ⊔ a₂) <= f^[n₁] a₁ ⊔ f^[n₂] a₂) ↔
      forall a₁ a₂, f (a₁ ⊔ a₂) <= f a₁ ⊔ a₂ := by
  constructor <;> intro h
  · exact h 1 0
  · intro n₁ n₂ a₁ a₂
    have h' : forall n a₁ a₂, f^[n] (a₁ ⊔ a₂) <= f^[n] a₁ ⊔ a₂ := by
      intro n
      induction n with
      | zero => intro a₁ a₂; rfl
      | succ n ih =>
        intro a₁ a₂
        calc
          f^[n + 1] (a₁ ⊔ a₂) = f^[n] (f (a₁ ⊔ a₂)) := Function.iterate_succ_apply f n _
          _ <= f^[n] (f a₁ ⊔ a₂) := f.mono.iterate n (h a₁ a₂)
          _ <= f^[n] (f a₁) ⊔ a₂ := ih _ _
          _ = f^[n + 1] a₁ ⊔ a₂ := by rw [← Function.iterate_succ_apply]
    calc
      f^[n₁ + n₂] (a₁ ⊔ a₂) = f^[n₁] (f^[n₂] (a₁ ⊔ a₂)) :=
        Function.iterate_add_apply f n₁ n₂ _
      _ = f^[n₁] (f^[n₂] (a₂ ⊔ a₁)) := by rw [sup_comm]
      _ <= f^[n₁] (f^[n₂] a₂ ⊔ a₁) := f.mono.iterate n₁ (h' n₂ _ _)
      _ = f^[n₁] (a₁ ⊔ f^[n₂] a₂) := by rw [sup_comm]
      _ <= f^[n₁] a₁ ⊔ f^[n₂] a₂ := h' n₁ a₁ _

end Preorder

end OrderHom
