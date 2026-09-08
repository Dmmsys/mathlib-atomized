/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.End
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Tactic.Common

/-!
# Extra lemmas about permutations

This file proves miscellaneous lemmas about `Equiv.Perm`.

## TODO

Most of the content of this file was moved to `Mathlib/Algebra/Group/End.lean` in
https://github.com/leanprover-community/mathlib4/pull/22141.
It would be good to merge the remaining lemmas with other files, e.g.
`GroupTheory.Perm.ViaEmbedding` looks like it could benefit from such a treatment (splitting into
the algebra and non-algebra parts).
-/

public section


universe u v

namespace Equiv

variable {α : Type u} {β : Type v}

section Swap

variable [DecidableEq α]

@[simp]
/-
**Equiv.swap_smul_self_smul** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：swap_smul_self_smul [MulAction (Perm α) β] (i j : α) (x : β) : swap i j • 
swap i j • x = x
参数：Perm α；i j : α；x : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Equiv.swap_mul_self`：∀ {α : Type u_4} [inst : DecidableEq α] (i j : α), 
Equiv.swap i j * Equiv.swap i j = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem swap_smul_self_smul [MulAction (Perm α) β] (i j : α) (x : β) :
    swap i j • swap i j • x = x := by simp [smul_smul]
/-
**Equiv.swap_smul_involutive** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：swap_smul_involutive [MulAction (Perm α) β] (i j : α) : Function.Involutiv
e (swap i j • · : β -> β)
参数：Perm α；i j : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.swap_smul_self_smul`：swap_smul_self_smul [MulAction (Perm α) β] (i
 j : α) (x : β) : swap i j • swap i j • x = x
-/
theorem swap_smul_involutive [MulAction (Perm α) β] (i j : α) :
    Function.Involutive (swap i j • · : β → β) := swap_smul_self_smul i j

end Swap
end Equiv

open Equiv Function

namespace Set
variable {α : Type*} {f : Perm α} {s : Set α}

/-
**Set.BijOn.perm_inv** 是 Mathlib 中的一个定理，位于命名空间 `Set.BijOn`。
形式化陈述：∀ {α : Type u_1} {f : Equiv.Perm α} {s : Set α}, Set.BijOn (⇑f) s s → Set.
BijOn (⇑f⁻¹) s s
参数：⇑f；⇑f⁻¹。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.BijOn.symm`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} 
{f : α → β} {g : β → α},   Set.InvOn f g t s → Set.BijOn f s t → Set.BijOn g t s
· 使用引理 `Equiv.invOn`：invOn : InvOn e e.symm t s
-/
lemma BijOn.perm_inv (hf : BijOn f s s) : BijOn ↑(f⁻¹) s s := hf.symm f.invOn
/-
**Set.MapsTo.perm_pow** 是 Mathlib 中的一个定理，位于命名空间 `Set.MapsTo`。
形式化陈述：∀ {α : Type u_1} {f : Equiv.Perm α} {s : Set α}, Set.MapsTo (⇑f) s s → ∀ (
n : ℕ), Set.MapsTo (⇑(f ^ n)) s s
参数：⇑f；n : ℕ；⇑(f ^ n)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.iterate`：∀ {α : Type u_1} {f : α → α} {s : Set α}, Set.MapsTo
 f s s → ∀ (n : ℕ), Set.MapsTo f^[n] s s
-/
lemma MapsTo.perm_pow : MapsTo f s s → ∀ n : ℕ, MapsTo (f ^ n) s s := by
  simp_rw [Equiv.Perm.coe_pow]; exact MapsTo.iterate
/-
**Set.SurjOn.perm_pow** 是 Mathlib 中的一个定理，位于命名空间 `Set.SurjOn`。
形式化陈述：∀ {α : Type u_1} {f : Equiv.Perm α} {s : Set α}, Set.SurjOn (⇑f) s s → ∀ (
n : ℕ), Set.SurjOn (⇑(f ^ n)) s s
参数：⇑f；n : ℕ；⇑(f ^ n)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.SurjOn.iterate`：∀ {α : Type u_1} {f : α → α} {s : Set α}, Set.SurjOn
 f s s → ∀ (n : ℕ), Set.SurjOn f^[n] s s
-/
lemma SurjOn.perm_pow : SurjOn f s s → ∀ n : ℕ, SurjOn (f ^ n) s s := by
  simp_rw [Equiv.Perm.coe_pow]; exact SurjOn.iterate
/-
**Set.BijOn.perm_pow** 是 Mathlib 中的一个定理，位于命名空间 `Set.BijOn`。
形式化陈述：∀ {α : Type u_1} {f : Equiv.Perm α} {s : Set α}, Set.BijOn (⇑f) s s → ∀ (n
 : ℕ), Set.BijOn (⇑(f ^ n)) s s
参数：⇑f；n : ℕ；⇑(f ^ n)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.BijOn.iterate`：∀ {α : Type u_1} {f : α → α} {s : Set α}, Set.BijOn f
 s s → ∀ (n : ℕ), Set.BijOn f^[n] s s
-/
lemma BijOn.perm_pow : BijOn f s s → ∀ n : ℕ, BijOn (f ^ n) s s := by
  simp_rw [Equiv.Perm.coe_pow]; exact BijOn.iterate
/-
**Set.BijOn.perm_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Set.BijOn`。
形式化陈述：∀ {α : Type u_1} {f : Equiv.Perm α} {s : Set α}, Set.BijOn (⇑f) s s → ∀ (n
 : ℤ), Set.BijOn (⇑(f ^ n)) s s
参数：⇑f；n : ℤ；⇑(f ^ n)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.BijOn.perm_pow`：∀ {α : Type u_1} {f : Equiv.Perm α} {s : Set α}, Set
.BijOn (⇑f) s s → ∀ (n : ℕ), Set.BijOn (⇑(f ^ n)) s s
· 使用定理 `Set.BijOn.perm_inv`：∀ {α : Type u_1} {f : Equiv.Perm α} {s : Set α}, Set
.BijOn (⇑f) s s → Set.BijOn (⇑f⁻¹) s s
-/
lemma BijOn.perm_zpow (hf : BijOn f s s) : ∀ n : ℤ, BijOn (f ^ n) s s
  | Int.ofNat n => hf.perm_pow n
  | Int.negSucc n => (hf.perm_pow (n + 1)).perm_inv

end Set

