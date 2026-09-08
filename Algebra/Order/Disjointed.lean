/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Algebra.Order.SuccPred.PartialSups
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Order.Disjointed

/-!
# `Disjointed` for functions on a `SuccAddOrder`

This file contains material excised from `Mathlib/Order/Disjointed.lean` to avoid import
dependencies from `Mathlib.Algebra.Order` into `Mathlib.Order`.

## TODO

Find a useful statement of `disjointedRec_succ`.
-/

@[expose] public section

open Order

variable {α ι : Type*} [GeneralizedBooleanAlgebra α]

section SuccAddOrder

variable [LinearOrder ι] [LocallyFiniteOrderBot ι] [Add ι] [One ι] [SuccAddOrder ι]

/-
**disjointed_add_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjointed_add_one [NoMaxOrder ι] (f : ι -> α) (i : ι) : disjointed f (i +
 1) = f (i + 1) \ partialSups f i
参数：f : ι -> α；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `disjointed_succ`：disjointed_succ (f : ι -> α) {i : ι} (hi : ¬IsMax i) : 
disjointed f (succ i) = f (succ i) \ partialSups f i
· 使用定理 `not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxOrder α] (a : α), 
¬IsMax a
-/
theorem disjointed_add_one [NoMaxOrder ι] (f : ι → α) (i : ι) :
    disjointed f (i + 1) = f (i + 1) \ partialSups f i := by
  simpa only [succ_eq_add_one] using disjointed_succ f (not_isMax i)
/-
**partialSups_add_one_eq_sup_disjointed** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：partialSups_add_one_eq_sup_disjointed (f : ι -> α) (i : ι) : partialSups f
 (i + 1) = partialSups f i ⊔ disjointed f (i + 1)
参数：f : ι -> α；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_partialSups`：le_partialSups (f : ι -> α) : f <= partialSups f
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用引理 `disjointed_succ`：disjointed_succ (f : ι -> α) {i : ι} (hi : ¬IsMax i) : 
disjointed f (succ i) = f (succ i) \ partialSups f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `partialSups_add_one`：partialSups_add_one [Add ι] [One ι] [LocallyFiniteO
rderBot ι] [SuccAddOrder ι] (f : ι -> α) (i : ι) : partialSups f (i + 1) = parti
alSups f …
· 使用定理 `sup_sdiff_self`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] 
(a b : α), a ⊔ b \ a = a ⊔ b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma partialSups_add_one_eq_sup_disjointed (f : ι → α) (i : ι) :
    partialSups f (i + 1) = partialSups f i ⊔ disjointed f (i + 1) := by
  by_cases hi : IsMax i
  · have : i + 1 = i := by
      have h : i ≤ i + 1 := by
        rw [← Order.succ_eq_add_one]
        apply Order.le_succ
      exact le_antisymm (hi h) h
    simp only [this, left_eq_sup, ge_iff_le, disjointed, sdiff_le_iff]
    apply le_trans (le_partialSups _ _) le_sup_right
  · rw [← Order.succ_eq_add_one, disjointed_succ _ hi]
    simp
/-
**Monotone.disjointed_add_one_sup** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} [inst : GeneralizedBooleanAlgebra α] [inst
_1 : LinearOrder ι]   [inst_2 : LocallyFiniteOrderBot ι] [inst_3 : Add ι] [inst_
4 : One ι] [SuccAddOrder ι] {f : ι → α},   Monotone f → ∀ (i : ι), disjointed f 
(i + 1) ⊔ f i = f (i + 1)
参数：i : ι；i + 1；i + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用引理 `Monotone.disjointed_succ_sup`：Monotone.disjointed_succ_sup {f : ι -> α} 
(hf : Monotone f) (i : ι) : disjointed f (succ i) ⊔ f i = f (succ i)
-/
protected lemma Monotone.disjointed_add_one_sup {f : ι → α} (hf : Monotone f) (i : ι) :
    disjointed f (i + 1) ⊔ f i = f (i + 1) := by
  simpa only [succ_eq_add_one i] using hf.disjointed_succ_sup i
/-
**Monotone.disjointed_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} [inst : GeneralizedBooleanAlgebra α] [inst
_1 : LinearOrder ι]   [inst_2 : LocallyFiniteOrderBot ι] [inst_3 : Add ι] [inst_
4 : One ι] [SuccAddOrder ι] [NoMaxOrder ι] {f : ι → α},   Monotone f → ∀ (i : ι)
, disjointed f (i + 1) = f (i + 1) \ f i
参数：i : ι；i + 1；i + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `Monotone.disjointed_succ`：∀ {α : Type u_1} {ι : Type u_2} [inst : Genera
lizedBooleanAlgebra α] [inst_1 : LinearOrder ι]   [inst_2 : LocallyFiniteOrderBo
t ι] [inst_3 :…
· 使用定理 `not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxOrder α] (a : α), 
¬IsMax a
-/
protected lemma Monotone.disjointed_add_one [NoMaxOrder ι] {f : ι → α} (hf : Monotone f) (i : ι) :
    disjointed f (i + 1) = f (i + 1) \ f i := by
  rw [← succ_eq_add_one, hf.disjointed_succ]
  exact not_isMax i

end SuccAddOrder

section Nat

/-- A recursion principle for `disjointed`. To construct / define something for `disjointed f i`,
it's enough to construct / define it for `f n` and to able to extend through diffs.

Note that this version allows an arbitrary `Sort*`, but requires the domain to be `Nat`, while
the root-level `disjointedRec` allows more general domains but requires `p` to be `Prop`-valued. -/
/-
**Nat.disjointedRec** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：{α : Type u_1} →   [inst : GeneralizedBooleanAlgebra α] →     {f : ℕ → α} 
→ {p : α → Sort u_3} → (⦃t : α⦄ → ⦃i : ℕ⦄ → p t → p (t \ f i)) → ⦃n : ℕ⦄ → p (f 
n) → p (disjointed f n)
参数：⦃t : α⦄ → ⦃i : ℕ⦄ → p t → p (t \ f i)。
该定义给出了一个带前提的构造。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A recursion principle for `disjointed`. To construct / define something for `dis
jointed f i`,
it's enough to construct / define it for `f n` and to able to extend through dif
fs.

Note that this version allows an arbitrary `Sort*`, but requires the domain to b
e `Nat`, while
the root-level `disjointedRec` allows more general domains but requires `p` to b
e `Prop`-valued.
-/
def Nat.disjointedRec {f : ℕ → α} {p : α → Sort*} (hdiff : ∀ ⦃t i⦄, p t → p (t \ f i)) :
    ∀ ⦃n⦄, p (f n) → p (disjointed f n)
  | 0 => fun h₀ ↦ disjointed_zero f ▸ h₀
  | n + 1 => fun h => by
    suffices H : ∀ k, p (f (n + 1) \ partialSups f k) from disjointed_add_one f n ▸ H n
    intro k
    induction k with
    | zero => exact hdiff h
    | succ k ih => simpa only [partialSups_add_one, ← sdiff_sdiff_left] using hdiff ih

@[simp]
/-
**disjointedRec_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjointedRec_zero {f : Nat -> α} {p : α -> Sort*} (hdiff : forall ⦃t i⦄, 
p t -> p (t \ f i)) (h₀ : p (f 0)) : Nat.disjointedRec hdiff h₀ = (disjointed_ze
ro f ▸ h₀)
参数：hdiff : forall ⦃t i⦄, p t -> p (t \ f i)；h₀ : p (f 0)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem disjointedRec_zero {f : ℕ → α} {p : α → Sort*}
    (hdiff : ∀ ⦃t i⦄, p t → p (t \ f i)) (h₀ : p (f 0)) :
    Nat.disjointedRec hdiff h₀ = (disjointed_zero f ▸ h₀) :=
  rfl

-- TODO: Find a useful statement of `disjointedRec_succ`.

end Nat

