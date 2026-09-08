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

/-
**OrderHom.** 是 Mathlib 中的一个实例，位于命名空间 `OrderHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SemilatticeSup β] : Max (α →o β) where
  max f g := ⟨fun a => f a ⊔ g a, f.mono.sup g.mono⟩
/-
**OrderHom.coe_sup** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : SemilatticeS
up β] (f g : α →o β), ⇑(f ⊔ g) = ⇑f ⊔ ⇑g
参数：f g : α →o β；f ⊔ g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_sup [SemilatticeSup β] (f g : α →o β) :
    ((f ⊔ g : α →o β) : α → β) = (f : α → β) ⊔ g := rfl
/-
**OrderHom.** 是 Mathlib 中的一个实例，位于命名空间 `OrderHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SemilatticeSup β] : SemilatticeSup (α →o β) :=
  { (_ : PartialOrder (α →o β)) with
    sup := Max.max
    le_sup_left := fun _ _ _ => le_sup_left
    le_sup_right := fun _ _ _ => le_sup_right
    sup_le := fun _ _ _ h₀ h₁ x => sup_le (h₀ x) (h₁ x) }
/-
**OrderHom.** 是 Mathlib 中的一个实例，位于命名空间 `OrderHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SemilatticeInf β] : Min (α →o β) where
  min f g := ⟨fun a => f a ⊓ g a, f.mono.inf g.mono⟩
/-
**OrderHom.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : SemilatticeI
nf β] (f g : α →o β), ⇑(f ⊓ g) = ⇑f ⊓ ⇑g
参数：f g : α →o β；f ⊓ g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_inf [SemilatticeInf β] (f g : α →o β) :
    ((f ⊓ g : α →o β) : α → β) = (f : α → β) ⊓ g := rfl
/-
**OrderHom.** 是 Mathlib 中的一个实例，位于命名空间 `OrderHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SemilatticeInf β] : SemilatticeInf (α →o β) :=
  { (_ : PartialOrder (α →o β)), (dualIso α β).symm.toGaloisInsertion.liftSemilatticeInf with
    inf := (· ⊓ ·) }
/-
**OrderHom.lattice** 是 Mathlib 中的一个实例，位于命名空间 `OrderHom`。
形式化陈述：lattice [Lattice β] : Lattice (α ->o β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance lattice [Lattice β] : Lattice (α →o β) :=
  { (_ : SemilatticeSup (α →o β)), (_ : SemilatticeInf (α →o β)) with }

@[simps]
/-
**OrderHom.** 是 Mathlib 中的一个实例，位于命名空间 `OrderHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preorder β] [OrderBot β] : Bot (α →o β) where
  bot := const α ⊥
/-
**OrderHom.orderBot** 是 Mathlib 中的一个实例，位于命名空间 `OrderHom`。
形式化陈述：orderBot [Preorder β] [OrderBot β] : OrderBot (α ->o β) where bot_le _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance orderBot [Preorder β] [OrderBot β] : OrderBot (α →o β) where
  bot_le _ _ := bot_le

@[simps]
/-
**OrderHom.instTopOrderHom** 是 Mathlib 中的一个实例，位于命名空间 `OrderHom`。
形式化陈述：instTopOrderHom [Preorder β] [OrderTop β] : Top (α ->o β) where top
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instTopOrderHom [Preorder β] [OrderTop β] : Top (α →o β) where
  top := const α ⊤
/-
**OrderHom.orderTop** 是 Mathlib 中的一个实例，位于命名空间 `OrderHom`。
形式化陈述：orderTop [Preorder β] [OrderTop β] : OrderTop (α ->o β) where le_top _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance orderTop [Preorder β] [OrderTop β] : OrderTop (α →o β) where
  le_top _ _ := le_top
/-
**OrderHom.** 是 Mathlib 中的一个实例，位于命名空间 `OrderHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CompleteLattice β] : InfSet (α →o β) where
  sInf s := ⟨fun x => ⨅ f ∈ s, (f :) x, fun _ _ h => iInf₂_mono fun f _ => f.mono h⟩

@[simp]
/-
**OrderHom.sInf_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：sInf_apply [CompleteLattice β] (s : Set (α ->o β)) (x : α) : sInf s x = ⨅ 
f in s, (f :) x
参数：s : Set (α ->o β)；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sInf_apply [CompleteLattice β] (s : Set (α →o β)) (x : α) :
    sInf s x = ⨅ f ∈ s, (f :) x :=
  rfl
/-
**OrderHom.iInf_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：iInf_apply {ι : Sort*} [CompleteLattice β] (f : ι -> α ->o β) (x : α) : (⨅
 i, f i) x = ⨅ i, f i x
参数：f : ι -> α ->o β；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `OrderHom.sInf_apply`：sInf_apply [CompleteLattice β] (s : Set (α ->o β)) 
(x : α) : sInf s x = ⨅ f in s, (f :) x
· 使用定理 `iInf_range`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [inst : Compl
eteLattice α] {g : β → α} {f : ι → β},   ⨅ b ∈ Set.range f, g b = ⨅ i, g (f i)
-/
theorem iInf_apply {ι : Sort*} [CompleteLattice β] (f : ι → α →o β) (x : α) :
    (⨅ i, f i) x = ⨅ i, f i x :=
  (sInf_apply _ _).trans iInf_range

@[simp, norm_cast]
/-
**OrderHom.coe_iInf** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：coe_iInf {ι : Sort*} [CompleteLattice β] (f : ι -> α ->o β) : ((⨅ i, f i :
 α ->o β) : α -> β) = ⨅ i, (f i : α -> β)
参数：f : ι -> α ->o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderHom.iInf_apply`：iInf_apply {ι : Sort*} [CompleteLattice β] (f : ι -
> α ->o β) (x : α) : (⨅ i, f i) x = ⨅ i, f i x
· 使用定理 `iInf_apply`：∀ {α : Type u_8} {β : α → Type u_9} {ι : Sort u_10} [inst : 
(i : α) → InfSet (β i)] {f : ι → (a : α) → β a} {a : α},   (⨅ i, f i) a = ⨅ i, f
…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_iInf {ι : Sort*} [CompleteLattice β] (f : ι → α →o β) :
    ((⨅ i, f i : α →o β) : α → β) = ⨅ i, (f i : α → β) := by
  funext x; simp [iInf_apply]
/-
**OrderHom.** 是 Mathlib 中的一个实例，位于命名空间 `OrderHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CompleteLattice β] : SupSet (α →o β) where
  sSup s := ⟨fun x => ⨆ f ∈ s, (f :) x, fun _ _ h => iSup₂_mono fun f _ => f.mono h⟩

@[simp]
/-
**OrderHom.sSup_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：sSup_apply [CompleteLattice β] (s : Set (α ->o β)) (x : α) : sSup s x = ⨆ 
f in s, (f :) x
参数：s : Set (α ->o β)；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sSup_apply [CompleteLattice β] (s : Set (α →o β)) (x : α) :
    sSup s x = ⨆ f ∈ s, (f :) x :=
  rfl
/-
**OrderHom.iSup_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：iSup_apply {ι : Sort*} [CompleteLattice β] (f : ι -> α ->o β) (x : α) : (⨆
 i, f i) x = ⨆ i, f i x
参数：f : ι -> α ->o β；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `OrderHom.sSup_apply`：sSup_apply [CompleteLattice β] (s : Set (α ->o β)) 
(x : α) : sSup s x = ⨆ f in s, (f :) x
· 使用定理 `iSup_range`：iSup_range {g : β -> α} {f : ι -> β} : ⨆ b in range f, g b =
 ⨆ i, g (f i)
-/
theorem iSup_apply {ι : Sort*} [CompleteLattice β] (f : ι → α →o β) (x : α) :
    (⨆ i, f i) x = ⨆ i, f i x :=
  (sSup_apply _ _).trans iSup_range

@[simp, norm_cast]
/-
**OrderHom.coe_iSup** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：coe_iSup {ι : Sort*} [CompleteLattice β] (f : ι -> α ->o β) : ((⨆ i, f i :
 α ->o β) : α -> β) = ⨆ i, (f i : α -> β)
参数：f : ι -> α ->o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderHom.iSup_apply`：iSup_apply {ι : Sort*} [CompleteLattice β] (f : ι -
> α ->o β) (x : α) : (⨆ i, f i) x = ⨆ i, f i x
· 使用定理 `iSup_apply`：iSup_apply {α : Type*} {β : α -> Type*} {ι : Sort*} [forall 
i, SupSet (β i)] {f : ι -> forall a, β a} {a : α} : (⨆ i, f i) a = ⨆ i, f i a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_iSup {ι : Sort*} [CompleteLattice β] (f : ι → α →o β) :
    ((⨆ i, f i : α →o β) : α → β) = ⨆ i, (f i : α → β) := by
  funext x; simp [iSup_apply]
/-
**OrderHom.** 是 Mathlib 中的一个实例，位于命名空间 `OrderHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CompleteLattice β] : CompleteLattice (α →o β) :=
  { (_ : Lattice (α →o β)), OrderHom.orderTop, OrderHom.orderBot with
    isLUB_sSup _ :=
      .of_image (f := (⇑)) coe_le_coe (by simp [isLUB_pi, Set.image_image, isLUB_biSup])
    isGLB_sInf _ :=
      .of_image (f := (⇑)) coe_le_coe (by simp [isGLB_pi, Set.image_image, isGLB_biInf]) }
/-
**OrderHom.iterate_sup_le_sup_iff** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：iterate_sup_le_sup_iff {α : Type*} [SemilatticeSup α] (f : α ->o α) : (for
all n₁ n₂ a₁ a₂, f^[n₁ + n₂] (a₁ ⊔ a₂) <= f^[n₁] a₁ ⊔ f^[n₂] a₂) ↔ forall a₁ a₂,
 f (a₁ ⊔ a₂) <= f a₁ ⊔ a₂
参数：f : α ->o α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Function.iterate_succ_apply`：iterate_succ_apply (n : Nat) (x : α) : f^[n
.succ] x = f^[n] (f x)
· 使用定理 `Monotone.iterate`：∀ {α : Type u} [inst : Preorder α] {f : α → α}, Monoto
ne f → ∀ (n : ℕ), Monotone f^[n]
· 使用定理 `OrderHom.mono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst
_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.iterate_add_apply`：iterate_add_apply (m n : Nat) (x : α) : f^[m
 + n] x = f^[m] (f^[n] x)
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
-/
theorem iterate_sup_le_sup_iff {α : Type*} [SemilatticeSup α] (f : α →o α) :
    (∀ n₁ n₂ a₁ a₂, f^[n₁ + n₂] (a₁ ⊔ a₂) ≤ f^[n₁] a₁ ⊔ f^[n₂] a₂) ↔
      ∀ a₁ a₂, f (a₁ ⊔ a₂) ≤ f a₁ ⊔ a₂ := by
  constructor <;> intro h
  · exact h 1 0
  · intro n₁ n₂ a₁ a₂
    have h' : ∀ n a₁ a₂, f^[n] (a₁ ⊔ a₂) ≤ f^[n] a₁ ⊔ a₂ := by
      intro n
      induction n with
      | zero => intro a₁ a₂; rfl
      | succ n ih =>
        intro a₁ a₂
        calc
          f^[n + 1] (a₁ ⊔ a₂) = f^[n] (f (a₁ ⊔ a₂)) := Function.iterate_succ_apply f n _
          _ ≤ f^[n] (f a₁ ⊔ a₂) := f.mono.iterate n (h a₁ a₂)
          _ ≤ f^[n] (f a₁) ⊔ a₂ := ih _ _
          _ = f^[n + 1] a₁ ⊔ a₂ := by rw [← Function.iterate_succ_apply]
    calc
      f^[n₁ + n₂] (a₁ ⊔ a₂) = f^[n₁] (f^[n₂] (a₁ ⊔ a₂)) :=
        Function.iterate_add_apply f n₁ n₂ _
      _ = f^[n₁] (f^[n₂] (a₂ ⊔ a₁)) := by rw [sup_comm]
      _ ≤ f^[n₁] (f^[n₂] a₂ ⊔ a₁) := f.mono.iterate n₁ (h' n₂ _ _)
      _ = f^[n₁] (a₁ ⊔ f^[n₂] a₂) := by rw [sup_comm]
      _ ≤ f^[n₁] a₁ ⊔ f^[n₂] a₂ := h' n₁ a₁ _

end Preorder

end OrderHom

