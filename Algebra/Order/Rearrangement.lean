/-
Copyright (c) 2022 Mantas Bakšys. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys
-/
module

public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Algebra.Order.Module.Synonym
public import Mathlib.Algebra.Order.Monoid.OrderDual
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Prod.Lex
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.Order.Monotone.Monovary

/-!
# Rearrangement inequality

This file proves the rearrangement inequality and deduces the conditions for equality and strict
inequality.

The rearrangement inequality tells you that for two functions `f g : ι → α`, the sum
`∑ i, f i * g (σ i)` is maximized over all `σ : Perm ι` when `g ∘ σ` monovaries with `f` and
minimized when `g ∘ σ` antivaries with `f`.

The inequality also tells you that `∑ i, f i * g (σ i) = ∑ i, f i * g i` if and only if `g ∘ σ`
monovaries with `f` when `g` monovaries with `f`. The above equality also holds if and only if
`g ∘ σ` antivaries with `f` when `g` antivaries with `f`.

From the above two statements, we deduce that the inequality is strict if and only if `g ∘ σ` does
not monovary with `f` when `g` monovaries with `f`. Analogously, the inequality is strict if and
only if `g ∘ σ` does not antivary with `f` when `g` antivaries with `f`.

## Implementation notes

In fact, we don't need much compatibility between the addition and multiplication of `α`, so we can
actually decouple them by replacing multiplication with scalar multiplication and making `f` and `g`
land in different types.
As a bonus, this makes the dual statement trivial. The multiplication versions are provided for
convenience.

The case for `Monotone`/`Antitone` pairs of functions over a `LinearOrder` is not deduced in this
file because it is easily deducible from the `Monovary` API.

## TODO

Add equality cases for when the permute function is injective. This comes from the following fact:
If `Monovary f g`, `Injective g` and `σ` is a permutation, then `Monovary f (g ∘ σ) ↔ σ = 1`.
-/

public section


open Equiv Equiv.Perm Finset Function OrderDual

variable {ι α β : Type*} [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β] [Module α β]

/-! ### Scalar multiplication versions -/

section SMul

/-! #### Weak rearrangement inequality -/

section weak_inequality
variable [PosSMulMono α β] {s : Finset ι} {σ : Perm ι} {f : ι → α} {g : ι → β}

/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is maximized when
`f` and `g` monovary together on `s`. Stated by permuting the entries of `g`. -/
/-
**MonovaryOn.sum_smul_comp_perm_le_sum_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonovaryOn.sum_smul_comp_perm_le_sum_smul (hfg : MonovaryOn f g s) (hσ : {
x | σ x != x} subseteq s) : ∑ i in s, f i • g (σ i) <= ∑ i in s, f i • g i
参数：hfg : MonovaryOn f g s；hσ : {x | σ x != x} subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on_max_value`：induction_on_max_value [DecidableEq ι] (f
 : ι -> α) {motive : Finset ι -> Prop} (s : Finset ι) (empty : motive ∅) (insert
 : forall a s, a ∉ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.swap_comp_apply`：swap_comp_apply {a b x : α} (π : Perm α) : π.tran
s (swap a b) x = if π x = a then b else if π x = b then a else π x
· 使用定理 `Finset.mem_of_mem_insert_of_ne`：mem_of_mem_insert_of_ne (h : b in insert
 a s) : b != a -> b in s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `MonovaryOn.subset`：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [inst 
: Preorder α] [inst_1 : Preorder β] {f : ι → α} {g : ι → β}   {s t : Set ι}, s ⊆
 t → Mo…
· 使用定理 `Finset.subset_insert`：∀ {α : Type u_1} [inst : DecidableEq α] (a : α) (s
 : Finset α), s ⊆ insert a s
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.swap_self`：swap_self (a : α) : swap a a = Equiv.refl _
· 使用定理 `Equiv.trans_refl`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), e.trans (Equi
v.refl β) = e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.Perm.inv_eq_iff_eq`：inv_eq_iff_eq {f : Perm α} {x y : α} : f⁻¹ x =
 y ↔ x = f y
（共 51 条，此处仅展示前 30 条）

--- 原说明 ---
**Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is 
maximized when
`f` and `g` monovary together on `s`. Stated by permuting the entries of `g`.
-/
theorem MonovaryOn.sum_smul_comp_perm_le_sum_smul (hfg : MonovaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) : ∑ i ∈ s, f i • g (σ i) ≤ ∑ i ∈ s, f i • g i := by
  classical
  induction s using induction_on_max_value fun i ↦ toLex (g i, f i) generalizing σ with
  | empty => simp only [le_rfl, Finset.sum_empty]
  | insert a s has hamax hind => ?_
  set τ : Perm ι := σ.trans (swap a (σ a)) with hτ
  have hτs : {x | τ x ≠ x} ⊆ s := by
    intro x hx
    simp only [τ, Ne, Set.mem_ofPred_eq, Equiv.swap_comp_apply] at hx
    split_ifs at hx with h₁ h₂
    · obtain rfl | hax := eq_or_ne x a
      · contradiction
      · exact mem_of_mem_insert_of_ne (hσ fun h ↦ hax <| h.symm.trans h₁) hax
    · exact (hx <| σ.injective h₂.symm).elim
    · exact mem_of_mem_insert_of_ne (hσ hx) (ne_of_apply_ne _ h₂)
  specialize hind (hfg.subset <| subset_insert _ _) hτs
  simp_rw [sum_insert has]
  grw [← hind]
  obtain hσa | hσa := eq_or_ne a (σ a)
  · rw [hτ, ← hσa, swap_self, trans_refl]
  have h1s : σ.symm a ∈ s := by
    rw [Ne, ← inv_eq_iff_eq] at hσa
    refine mem_of_mem_insert_of_ne (hσ fun h ↦ hσa ?_) hσa
    rwa [apply_symm_apply, eq_comm] at h
  simp only [← s.sum_erase_add _ h1s, add_comm]
  rw [← add_assoc, ← add_assoc]
  simp only [hτ, swap_apply_left, Function.comp_apply, Equiv.coe_trans, apply_symm_apply]
  refine add_le_add (smul_add_smul_le_smul_add_smul' ?_ ?_) (sum_congr rfl fun x hx ↦ ?_).le
  · specialize hamax (σ.symm a) h1s
    rw [Prod.Lex.toLex_le_toLex] at hamax
    rcases hamax with hamax | hamax
    · exact hfg (mem_insert_of_mem h1s) (mem_insert_self _ _) hamax
    · exact hamax.2
  · specialize hamax (σ a) (mem_of_mem_insert_of_ne (hσ <| σ.injective.ne hσa.symm) hσa.symm)
    rw [Prod.Lex.toLex_le_toLex] at hamax
    rcases hamax with hamax | hamax
    · exact hamax.le
    · exact hamax.1.le
  · rw [mem_erase, Ne, eq_symm_apply] at hx
    rw [swap_apply_of_ne_of_ne hx.1 (σ.injective.ne _)]
    rintro rfl
    exact has hx.2

/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is minimized when
`f` and `g` antivary together on `s`. Stated by permuting the entries of `g`. -/
/-
**AntivaryOn.sum_smul_le_sum_smul_comp_perm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntivaryOn.sum_smul_le_sum_smul_comp_perm (hfg : AntivaryOn f g s) (hσ : {
x | σ x != x} subseteq s) : ∑ i in s, f i • g i <= ∑ i in s, f i • g (σ i)
参数：hfg : AntivaryOn f g s；hσ : {x | σ x != x} subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonovaryOn.sum_smul_comp_perm_le_sum_smul`：MonovaryOn.sum_smul_comp_perm
_le_sum_smul (hfg : MonovaryOn f g s) (hσ : {x | σ x != x} subseteq s) : ∑ i in 
s, f i • g (σ i) <= ∑ i in s, f…
· 使用定理 `OrderDual.isOrderedAddCancelMonoid`：∀ {α : Type u} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], IsOrderedCancelAddMonoid
 αᵒᵈ
· 使用定理 `AntivaryOn.dual_right`：AntivaryOn.dual_right : AntivaryOn f g s -> Monov
aryOn f (toDual ∘ g) s

--- 原说明 ---
**Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is 
minimized when
`f` and `g` antivary together on `s`. Stated by permuting the entries of `g`.
-/
theorem AntivaryOn.sum_smul_le_sum_smul_comp_perm (hfg : AntivaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) : ∑ i ∈ s, f i • g i ≤ ∑ i ∈ s, f i • g (σ i) :=
  hfg.dual_right.sum_smul_comp_perm_le_sum_smul hσ

/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is maximized when
`f` and `g` monovary together on `s`. Stated by permuting the entries of `f`. -/
/-
**MonovaryOn.sum_comp_perm_smul_le_sum_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonovaryOn.sum_comp_perm_smul_le_sum_smul (hfg : MonovaryOn f g s) (hσ : {
x | σ x != x} subseteq s) : ∑ i in s, f (σ i) • g i <= ∑ i in s, f i • g i
参数：hfg : MonovaryOn f g s；hσ : {x | σ x != x} subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.sum_comp'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMon
oid M] (σ : Equiv.Perm ι) (s : Finset ι) (f : ι → ι → M),   {a | σ a ≠ a} ⊆ ↑s →
 ∑ x ∈ s, …
· 使用定理 `MonovaryOn.sum_smul_comp_perm_le_sum_smul`：MonovaryOn.sum_smul_comp_perm
_le_sum_smul (hfg : MonovaryOn f g s) (hσ : {x | σ x != x} subseteq s) : ∑ i in 
s, f i • g (σ i) <= ∑ i in s, f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Equiv.Perm.set_support_symm_eq`：set_support_symm_eq : {x | p.symm x != x
} = {x | p x != x}
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True

--- 原说明 ---
**Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is 
maximized when
`f` and `g` monovary together on `s`. Stated by permuting the entries of `f`.
-/
theorem MonovaryOn.sum_comp_perm_smul_le_sum_smul (hfg : MonovaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) : ∑ i ∈ s, f (σ i) • g i ≤ ∑ i ∈ s, f i • g i := by
  convert!
    hfg.sum_smul_comp_perm_le_sum_smul
      (show {x | σ⁻¹ x ≠ x} ⊆ s by simp [set_support_symm_eq, hσ]) using 1
  exact σ.sum_comp' s (fun i j ↦ f i • g j) hσ

/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is minimized when
`f` and `g` antivary together on `s`. Stated by permuting the entries of `f`. -/
/-
**AntivaryOn.sum_smul_le_sum_comp_perm_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntivaryOn.sum_smul_le_sum_comp_perm_smul (hfg : AntivaryOn f g s) (hσ : {
x | σ x != x} subseteq s) : ∑ i in s, f i • g i <= ∑ i in s, f (σ i) • g i
参数：hfg : AntivaryOn f g s；hσ : {x | σ x != x} subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonovaryOn.sum_comp_perm_smul_le_sum_smul`：MonovaryOn.sum_comp_perm_smul
_le_sum_smul (hfg : MonovaryOn f g s) (hσ : {x | σ x != x} subseteq s) : ∑ i in 
s, f (σ i) • g i <= ∑ i in s, f…
· 使用定理 `OrderDual.isOrderedAddCancelMonoid`：∀ {α : Type u} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], IsOrderedCancelAddMonoid
 αᵒᵈ
· 使用定理 `AntivaryOn.dual_right`：AntivaryOn.dual_right : AntivaryOn f g s -> Monov
aryOn f (toDual ∘ g) s

--- 原说明 ---
**Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is 
minimized when
`f` and `g` antivary together on `s`. Stated by permuting the entries of `f`.
-/
theorem AntivaryOn.sum_smul_le_sum_comp_perm_smul (hfg : AntivaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) : ∑ i ∈ s, f i • g i ≤ ∑ i ∈ s, f (σ i) • g i :=
  hfg.dual_right.sum_comp_perm_smul_le_sum_smul hσ

variable [Fintype ι]

/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is maximized when
`f` and `g` monovary together. Stated by permuting the entries of `g`. -/
/-
**Monovary.sum_smul_comp_perm_le_sum_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monovary.sum_smul_comp_perm_le_sum_smul (hfg : Monovary f g) : ∑ i, f i • 
g (σ i) <= ∑ i, f i • g i
参数：hfg : Monovary f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonovaryOn.sum_smul_comp_perm_le_sum_smul`：MonovaryOn.sum_smul_comp_perm
_le_sum_smul (hfg : MonovaryOn f g s) (hσ : {x | σ x != x} subseteq s) : ∑ i in 
s, f i • g (σ i) <= ∑ i in s, f…
· 使用定理 `Monovary.monovaryOn`：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [ins
t : Preorder α] [inst_1 : Preorder β] {f : ι → α} {g : ι → β},   Monovary f g → 
∀ (s : Se…
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)

--- 原说明 ---
**Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is 
maximized when
`f` and `g` monovary together. Stated by permuting the entries of `g`.
-/
theorem Monovary.sum_smul_comp_perm_le_sum_smul (hfg : Monovary f g) :
    ∑ i, f i • g (σ i) ≤ ∑ i, f i • g i :=
  (hfg.monovaryOn _).sum_smul_comp_perm_le_sum_smul fun _ _ ↦ mem_univ _

/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is minimized when
`f` and `g` antivary together. Stated by permuting the entries of `g`. -/
/-
**Antivary.sum_smul_le_sum_smul_comp_perm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antivary.sum_smul_le_sum_smul_comp_perm (hfg : Antivary f g) : ∑ i, f i • 
g i <= ∑ i, f i • g (σ i)
参数：hfg : Antivary f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntivaryOn.sum_smul_le_sum_smul_comp_perm`：AntivaryOn.sum_smul_le_sum_sm
ul_comp_perm (hfg : AntivaryOn f g s) (hσ : {x | σ x != x} subseteq s) : ∑ i in 
s, f i • g i <= ∑ i in s, f i •…
· 使用定理 `Antivary.antivaryOn`：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [ins
t : Preorder α] [inst_1 : Preorder β] {f : ι → α} {g : ι → β},   Antivary f g → 
∀ (s : Se…
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)

--- 原说明 ---
**Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is 
minimized when
`f` and `g` antivary together. Stated by permuting the entries of `g`.
-/
theorem Antivary.sum_smul_le_sum_smul_comp_perm (hfg : Antivary f g) :
    ∑ i, f i • g i ≤ ∑ i, f i • g (σ i) :=
  (hfg.antivaryOn _).sum_smul_le_sum_smul_comp_perm fun _ _ ↦ mem_univ _

/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is maximized when
`f` and `g` monovary together. Stated by permuting the entries of `f`. -/
/-
**Monovary.sum_comp_perm_smul_le_sum_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monovary.sum_comp_perm_smul_le_sum_smul (hfg : Monovary f g) : ∑ i, f (σ i
) • g i <= ∑ i, f i • g i
参数：hfg : Monovary f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonovaryOn.sum_comp_perm_smul_le_sum_smul`：MonovaryOn.sum_comp_perm_smul
_le_sum_smul (hfg : MonovaryOn f g s) (hσ : {x | σ x != x} subseteq s) : ∑ i in 
s, f (σ i) • g i <= ∑ i in s, f…
· 使用定理 `Monovary.monovaryOn`：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [ins
t : Preorder α] [inst_1 : Preorder β] {f : ι → α} {g : ι → β},   Monovary f g → 
∀ (s : Se…
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)

--- 原说明 ---
**Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is 
maximized when
`f` and `g` monovary together. Stated by permuting the entries of `f`.
-/
theorem Monovary.sum_comp_perm_smul_le_sum_smul (hfg : Monovary f g) :
    ∑ i, f (σ i) • g i ≤ ∑ i, f i • g i :=
  (hfg.monovaryOn _).sum_comp_perm_smul_le_sum_smul fun _ _ ↦ mem_univ _

/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is minimized when
`f` and `g` antivary together. Stated by permuting the entries of `f`. -/
/-
**Antivary.sum_smul_le_sum_comp_perm_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antivary.sum_smul_le_sum_comp_perm_smul (hfg : Antivary f g) : ∑ i, f i • 
g i <= ∑ i, f (σ i) • g i
参数：hfg : Antivary f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntivaryOn.sum_smul_le_sum_comp_perm_smul`：AntivaryOn.sum_smul_le_sum_co
mp_perm_smul (hfg : AntivaryOn f g s) (hσ : {x | σ x != x} subseteq s) : ∑ i in 
s, f i • g i <= ∑ i in s, f (σ …
· 使用定理 `Antivary.antivaryOn`：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [ins
t : Preorder α] [inst_1 : Preorder β] {f : ι → α} {g : ι → β},   Antivary f g → 
∀ (s : Se…
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)

--- 原说明 ---
**Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is 
minimized when
`f` and `g` antivary together. Stated by permuting the entries of `f`.
-/
theorem Antivary.sum_smul_le_sum_comp_perm_smul (hfg : Antivary f g) :
    ∑ i, f i • g i ≤ ∑ i, f (σ i) • g i :=
  (hfg.antivaryOn _).sum_smul_le_sum_comp_perm_smul fun _ _ ↦ mem_univ _

end weak_inequality

/-! #### Equality case of the rearrangement inequality -/

section equality_case
variable [PosSMulStrictMono α β] {s : Finset ι} {σ : Perm ι} {f : ι → α} {g : ι → β}

/-- **Equality case of the Rearrangement Inequality**: Pointwise scalar multiplication of `f` and
`g`, which monovary together on `s`, is unchanged by a permutation if and only if `f` and `g ∘ σ`
monovary together on `s`. Stated by permuting the entries of `g`. -/
/-
**MonovaryOn.sum_smul_comp_perm_eq_sum_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonovaryOn.sum_smul_comp_perm_eq_sum_smul_iff (hfg : MonovaryOn f g s) (hσ
 : {x | σ x != x} subseteq s) : ∑ i in s, f i • g (σ i) = ∑ i in s, f i • g i ↔ 
MonovaryOn f (g ∘ σ) s
参数：hfg : MonovaryOn f g s；hσ : {x | σ x != x} subseteq s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MonovaryOn.eq_1`：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [inst : 
Preorder α] [inst_1 : Preorder β] (f : ι → α) (g : ι → β)   (s : Set ι), Monovar
yOn f…
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Equiv.Perm.set_support_mul_subset`：set_support_mul_subset : { x | (p * q
) x != x } subseteq { x | p x != x } union { x | q x != x }
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `Equiv.swap_apply_ne_self_iff`：swap_apply_ne_self_iff {a b x : α} : swap 
a b x != x ↔ a != b ∧ (x = a ∨ x = b)
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a
 → c < b → c < a
· 使用定理 `MonovaryOn.sum_smul_comp_perm_le_sum_smul`：MonovaryOn.sum_smul_comp_perm
_le_sum_smul (hfg : MonovaryOn f g s) (hσ : {x | σ x != x} subseteq s) : ∑ i in 
s, f i • g (σ i) <= ∑ i in s, f…
· 使用定理 `PosSMulStrictMono.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} [inst :
 Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : PartialOrder α]
   [inst_4 : PartialO…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_erase_add`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] [inst_1 : DecidableEq ι] (s : Finset ι) (f : ι → M) {a : ι},   a ∈ s → ∑ 
x ∈ s.eras…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_erase`：mem_erase {a b : α} {s : Finset α} : a in erase s b ↔ 
a != b ∧ a in s
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Equiv.swap_apply_right`：swap_apply_right (a b : α) : swap a b b = a
· 使用定理 `Equiv.swap_apply_left`：swap_apply_left (a b : α) : swap a b a = b
· 使用定理 `add_lt_add_of_le_of_lt`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preord
er α] [AddLeftStrictMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c < d → a 
+ c < b + d
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
**Equality case of the Rearrangement Inequality**: Pointwise scalar multiplicati
on of `f` and
`g`, which monovary together on `s`, is unchanged by a permutation if and only i
f `f` and `g ∘ σ`
monovary together on `s`. Stated by permuting the entries of `g`.
-/
theorem MonovaryOn.sum_smul_comp_perm_eq_sum_smul_iff (hfg : MonovaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) :
    ∑ i ∈ s, f i • g (σ i) = ∑ i ∈ s, f i • g i ↔ MonovaryOn f (g ∘ σ) s := by
  classical
  refine ⟨not_imp_not.1 fun h ↦ ?_, fun h ↦ (hfg.sum_smul_comp_perm_le_sum_smul hσ).antisymm <| by
    simpa using h.sum_smul_comp_perm_le_sum_smul ((set_support_symm_eq _).subset.trans hσ)⟩
  rw [MonovaryOn] at h
  push Not at h
  obtain ⟨x, hx, y, hy, hgxy, hfxy⟩ := h
  set τ : Perm ι := (Equiv.swap x y).trans σ
  have hτs : {x | τ x ≠ x} ⊆ s := by
    refine (set_support_mul_subset σ <| swap x y).trans (Set.union_subset hσ fun z hz ↦ ?_)
    obtain ⟨_, rfl | rfl⟩ := swap_apply_ne_self_iff.1 hz <;> assumption
  refine ((hfg.sum_smul_comp_perm_le_sum_smul hτs).trans_lt' ?_).ne
  obtain rfl | hxy := eq_or_ne x y
  · cases lt_irrefl _ hfxy
  simp only [τ, ← s.sum_erase_add _ hx,
    ← (s.erase x).sum_erase_add _ (mem_erase.2 ⟨hxy.symm, hy⟩),
    add_assoc, Equiv.coe_trans, Function.comp_apply, swap_apply_right, swap_apply_left]
  refine add_lt_add_of_le_of_lt (Finset.sum_congr rfl fun z hz ↦ ?_).le
    (smul_add_smul_lt_smul_add_smul hfxy hgxy)
  simp_rw [mem_erase] at hz
  rw [swap_apply_of_ne_of_ne hz.2.1 hz.1]

/-- **Equality case of the Rearrangement Inequality**: Pointwise scalar multiplication of `f` and
`g`, which antivary together on `s`, is unchanged by a permutation if and only if `f` and `g ∘ σ`
antivary together on `s`. Stated by permuting the entries of `g`. -/
/-
**AntivaryOn.sum_smul_comp_perm_eq_sum_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntivaryOn.sum_smul_comp_perm_eq_sum_smul_iff (hfg : AntivaryOn f g s) (hσ
 : {x | σ x != x} subseteq s) : ∑ i in s, f i • g (σ i) = ∑ i in s, f i • g i ↔ 
AntivaryOn f (g ∘ σ) s
参数：hfg : AntivaryOn f g s；hσ : {x | σ x != x} subseteq s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `MonovaryOn.sum_smul_comp_perm_eq_sum_smul_iff`：MonovaryOn.sum_smul_comp_
perm_eq_sum_smul_iff (hfg : MonovaryOn f g s) (hσ : {x | σ x != x} subseteq s) :
 ∑ i in s, f i • g (σ i) = ∑ i in s…
· 使用定理 `OrderDual.isOrderedAddCancelMonoid`：∀ {α : Type u} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], IsOrderedCancelAddMonoid
 αᵒᵈ
· 使用定理 `AntivaryOn.dual_right`：AntivaryOn.dual_right : AntivaryOn f g s -> Monov
aryOn f (toDual ∘ g) s
· 使用定理 `monovaryOn_toDual_right`：monovaryOn_toDual_right : MonovaryOn f (toDual 
∘ g) s ↔ AntivaryOn f g s

--- 原说明 ---
**Equality case of the Rearrangement Inequality**: Pointwise scalar multiplicati
on of `f` and
`g`, which antivary together on `s`, is unchanged by a permutation if and only i
f `f` and `g ∘ σ`
antivary together on `s`. Stated by permuting the entries of `g`.
-/
theorem AntivaryOn.sum_smul_comp_perm_eq_sum_smul_iff (hfg : AntivaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) :
    ∑ i ∈ s, f i • g (σ i) = ∑ i ∈ s, f i • g i ↔ AntivaryOn f (g ∘ σ) s :=
  (hfg.dual_right.sum_smul_comp_perm_eq_sum_smul_iff hσ).trans monovaryOn_toDual_right

/-- **Equality case of the Rearrangement Inequality**: Pointwise scalar multiplication of `f` and
`g`, which monovary together on `s`, is unchanged by a permutation if and only if `f ∘ σ` and `g`
monovary together on `s`. Stated by permuting the entries of `f`. -/
/-
**MonovaryOn.sum_comp_perm_smul_eq_sum_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonovaryOn.sum_comp_perm_smul_eq_sum_smul_iff (hfg : MonovaryOn f g s) (hσ
 : {x | σ x != x} subseteq s) : ∑ i in s, f (σ i) • g i = ∑ i in s, f i • g i ↔ 
MonovaryOn (f ∘ σ) g s
参数：hfg : MonovaryOn f g s；hσ : {x | σ x != x} subseteq s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用引理 `Equiv.Perm.set_support_symm_eq`：set_support_symm_eq : {x | p.symm x != x
} = {x | p x != x}
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_iff_eq_cancel_right`：∀ {α : Sort u_1} {a b : α}, (∀ {c : α}, a = c ↔ 
b = c) ↔ a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.sum_comp'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMon
oid M] (σ : Equiv.Perm ι) (s : Finset ι) (f : ι → ι → M),   {a | σ a ≠ a} ⊆ ↑s →
 ∑ x ∈ s, …
· 使用定理 `MonovaryOn.sum_smul_comp_perm_eq_sum_smul_iff`：MonovaryOn.sum_smul_comp_
perm_eq_sum_smul_iff (hfg : MonovaryOn f g s) (hσ : {x | σ x != x} subseteq s) :
 ∑ i in s, f i • g (σ i) = ∑ i in s…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_assoc`：comp_assoc (f : φ -> δ) (g : β -> φ) (h : α -> β) :
 (f ∘ g) ∘ h = f ∘ g ∘ h
· 使用定理 `Equiv.Perm.inv_def`：inv_def (f : Perm α) : f⁻¹ = f.symm
· 使用定理 `Equiv.symm_comp_self`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e.symm ∘
 ⇑e = id
· 使用定理 `Function.comp_id`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), f ∘ id = 
f
· 使用定理 `Equiv.eq_preimage_iff_image_eq`：eq_preimage_iff_image_eq {α β} (e : α ≃ 
β) (s t) : s = e ⁻¹' t ↔ e '' s = t
· 使用定理 `Set.image_perm`：image_perm {s : Set α} {σ : Equiv.Perm α} (hs : { a : α 
| σ a != a } subseteq s) : σ '' s = s
· 使用定理 `MonovaryOn.comp_right`：MonovaryOn.comp_right (h : MonovaryOn f g s) (k :
 ι' -> ι) : MonovaryOn (f ∘ k) (g ∘ k) (k ⁻¹' s)
· 使用定理 `Equiv.self_comp_symm`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e ∘ ⇑e.s
ymm = id

--- 原说明 ---
**Equality case of the Rearrangement Inequality**: Pointwise scalar multiplicati
on of `f` and
`g`, which monovary together on `s`, is unchanged by a permutation if and only i
f `f ∘ σ` and `g`
monovary together on `s`. Stated by permuting the entries of `f`.
-/
theorem MonovaryOn.sum_comp_perm_smul_eq_sum_smul_iff (hfg : MonovaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) :
    ∑ i ∈ s, f (σ i) • g i = ∑ i ∈ s, f i • g i ↔ MonovaryOn (f ∘ σ) g s := by
  have hσinv : { x | σ⁻¹ x ≠ x } ⊆ s := (set_support_symm_eq _).subset.trans hσ
  refine (Iff.trans ?_ <| hfg.sum_smul_comp_perm_eq_sum_smul_iff hσinv).trans
    ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · apply eq_iff_eq_cancel_right.2
    rw [σ.sum_comp' s (fun i j ↦ f i • g j) hσ]
    congr
  · convert! h.comp_right σ
    · rw [comp_assoc, inv_def, symm_comp_self, comp_id]
    · rw [σ.eq_preimage_iff_image_eq, Set.image_perm hσ]
  · convert! h.comp_right σ.symm
    · rw [comp_assoc, self_comp_symm, comp_id]
    · rw [σ.symm.eq_preimage_iff_image_eq]
      exact Set.image_perm hσinv

/-- **Equality case of the Rearrangement Inequality**: Pointwise scalar multiplication of `f` and
`g`, which antivary together on `s`, is unchanged by a permutation if and only if `f ∘ σ` and `g`
antivary together on `s`. Stated by permuting the entries of `f`. -/
/-
**AntivaryOn.sum_comp_perm_smul_eq_sum_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntivaryOn.sum_comp_perm_smul_eq_sum_smul_iff (hfg : AntivaryOn f g s) (hσ
 : {x | σ x != x} subseteq s) : ∑ i in s, f (σ i) • g i = ∑ i in s, f i • g i ↔ 
AntivaryOn (f ∘ σ) g s
参数：hfg : AntivaryOn f g s；hσ : {x | σ x != x} subseteq s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `MonovaryOn.sum_comp_perm_smul_eq_sum_smul_iff`：MonovaryOn.sum_comp_perm_
smul_eq_sum_smul_iff (hfg : MonovaryOn f g s) (hσ : {x | σ x != x} subseteq s) :
 ∑ i in s, f (σ i) • g i = ∑ i in s…
· 使用定理 `OrderDual.isOrderedAddCancelMonoid`：∀ {α : Type u} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], IsOrderedCancelAddMonoid
 αᵒᵈ
· 使用定理 `AntivaryOn.dual_right`：AntivaryOn.dual_right : AntivaryOn f g s -> Monov
aryOn f (toDual ∘ g) s
· 使用定理 `monovaryOn_toDual_right`：monovaryOn_toDual_right : MonovaryOn f (toDual 
∘ g) s ↔ AntivaryOn f g s

--- 原说明 ---
**Equality case of the Rearrangement Inequality**: Pointwise scalar multiplicati
on of `f` and
`g`, which antivary together on `s`, is unchanged by a permutation if and only i
f `f ∘ σ` and `g`
antivary together on `s`. Stated by permuting the entries of `f`.
-/
theorem AntivaryOn.sum_comp_perm_smul_eq_sum_smul_iff (hfg : AntivaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) :
    ∑ i ∈ s, f (σ i) • g i = ∑ i ∈ s, f i • g i ↔ AntivaryOn (f ∘ σ) g s :=
  (hfg.dual_right.sum_comp_perm_smul_eq_sum_smul_iff hσ).trans monovaryOn_toDual_right

variable [Fintype ι]

/-- **Equality case of the Rearrangement Inequality**: Pointwise scalar multiplication of `f` and
`g`, which monovary together, is unchanged by a permutation if and only if `f` and `g ∘ σ` monovary
together. Stated by permuting the entries of `g`. -/
/-
**Monovary.sum_smul_comp_perm_eq_sum_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monovary.sum_smul_comp_perm_eq_sum_smul_iff (hfg : Monovary f g) : ∑ i, f 
i • g (σ i) = ∑ i, f i • g i ↔ Monovary f (g ∘ σ)
参数：hfg : Monovary f g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonovaryOn.sum_smul_comp_perm_eq_sum_smul_iff`：MonovaryOn.sum_smul_comp_
perm_eq_sum_smul_iff (hfg : MonovaryOn f g s) (hσ : {x | σ x != x} subseteq s) :
 ∑ i in s, f i • g (σ i) = ∑ i in s…
· 使用定理 `Monovary.monovaryOn`：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [ins
t : Preorder α] [inst_1 : Preorder β] {f : ι → α} {g : ι → β},   Monovary f g → 
∀ (s : Se…
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
**Equality case of the Rearrangement Inequality**: Pointwise scalar multiplicati
on of `f` and
`g`, which monovary together, is unchanged by a permutation if and only if `f` a
nd `g ∘ σ` monovary
together. Stated by permuting the entries of `g`.
-/
theorem Monovary.sum_smul_comp_perm_eq_sum_smul_iff (hfg : Monovary f g) :
    ∑ i, f i • g (σ i) = ∑ i, f i • g i ↔ Monovary f (g ∘ σ) := by
  simp [(hfg.monovaryOn _).sum_smul_comp_perm_eq_sum_smul_iff fun _ _ ↦ mem_univ _]

/-- **Equality case of the Rearrangement Inequality**: Pointwise scalar multiplication of `f` and
`g`, which monovary together, is unchanged by a permutation if and only if `f ∘ σ` and `g` monovary
together. Stated by permuting the entries of `g`. -/
/-
**Monovary.sum_comp_perm_smul_eq_sum_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monovary.sum_comp_perm_smul_eq_sum_smul_iff (hfg : Monovary f g) : ∑ i, f 
(σ i) • g i = ∑ i, f i • g i ↔ Monovary (f ∘ σ) g
参数：hfg : Monovary f g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonovaryOn.sum_comp_perm_smul_eq_sum_smul_iff`：MonovaryOn.sum_comp_perm_
smul_eq_sum_smul_iff (hfg : MonovaryOn f g s) (hσ : {x | σ x != x} subseteq s) :
 ∑ i in s, f (σ i) • g i = ∑ i in s…
· 使用定理 `Monovary.monovaryOn`：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [ins
t : Preorder α] [inst_1 : Preorder β] {f : ι → α} {g : ι → β},   Monovary f g → 
∀ (s : Se…
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
**Equality case of the Rearrangement Inequality**: Pointwise scalar multiplicati
on of `f` and
`g`, which monovary together, is unchanged by a permutation if and only if `f ∘ 
σ` and `g` monovary
together. Stated by permuting the entries of `g`.
-/
theorem Monovary.sum_comp_perm_smul_eq_sum_smul_iff (hfg : Monovary f g) :
    ∑ i, f (σ i) • g i = ∑ i, f i • g i ↔ Monovary (f ∘ σ) g := by
  simp [(hfg.monovaryOn _).sum_comp_perm_smul_eq_sum_smul_iff fun _ _ ↦ mem_univ _]

/-- **Equality case of the Rearrangement Inequality**: Pointwise scalar multiplication of `f` and
`g`, which antivary together, is unchanged by a permutation if and only if `f` and `g ∘ σ` antivary
together. Stated by permuting the entries of `g`. -/
/-
**Antivary.sum_smul_comp_perm_eq_sum_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antivary.sum_smul_comp_perm_eq_sum_smul_iff (hfg : Antivary f g) : ∑ i, f 
i • g (σ i) = ∑ i, f i • g i ↔ Antivary f (g ∘ σ)
参数：hfg : Antivary f g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AntivaryOn.sum_smul_comp_perm_eq_sum_smul_iff`：AntivaryOn.sum_smul_comp_
perm_eq_sum_smul_iff (hfg : AntivaryOn f g s) (hσ : {x | σ x != x} subseteq s) :
 ∑ i in s, f i • g (σ i) = ∑ i in s…
· 使用定理 `Antivary.antivaryOn`：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [ins
t : Preorder α] [inst_1 : Preorder β] {f : ι → α} {g : ι → β},   Antivary f g → 
∀ (s : Se…
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
**Equality case of the Rearrangement Inequality**: Pointwise scalar multiplicati
on of `f` and
`g`, which antivary together, is unchanged by a permutation if and only if `f` a
nd `g ∘ σ` antivary
together. Stated by permuting the entries of `g`.
-/
theorem Antivary.sum_smul_comp_perm_eq_sum_smul_iff (hfg : Antivary f g) :
    ∑ i, f i • g (σ i) = ∑ i, f i • g i ↔ Antivary f (g ∘ σ) := by
  simp [(hfg.antivaryOn _).sum_smul_comp_perm_eq_sum_smul_iff fun _ _ ↦ mem_univ _]

/-- **Equality case of the Rearrangement Inequality**: Pointwise scalar multiplication of `f` and
`g`, which antivary together, is unchanged by a permutation if and only if `f ∘ σ` and `g` antivary
together. Stated by permuting the entries of `f`. -/
/-
**Antivary.sum_comp_perm_smul_eq_sum_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antivary.sum_comp_perm_smul_eq_sum_smul_iff (hfg : Antivary f g) : ∑ i, f 
(σ i) • g i = ∑ i, f i • g i ↔ Antivary (f ∘ σ) g
参数：hfg : Antivary f g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AntivaryOn.sum_comp_perm_smul_eq_sum_smul_iff`：AntivaryOn.sum_comp_perm_
smul_eq_sum_smul_iff (hfg : AntivaryOn f g s) (hσ : {x | σ x != x} subseteq s) :
 ∑ i in s, f (σ i) • g i = ∑ i in s…
· 使用定理 `Antivary.antivaryOn`：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [ins
t : Preorder α] [inst_1 : Preorder β] {f : ι → α} {g : ι → β},   Antivary f g → 
∀ (s : Se…
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
**Equality case of the Rearrangement Inequality**: Pointwise scalar multiplicati
on of `f` and
`g`, which antivary together, is unchanged by a permutation if and only if `f ∘ 
σ` and `g` antivary
together. Stated by permuting the entries of `f`.
-/
theorem Antivary.sum_comp_perm_smul_eq_sum_smul_iff (hfg : Antivary f g) :
    ∑ i, f (σ i) • g i = ∑ i, f i • g i ↔ Antivary (f ∘ σ) g := by
  simp [(hfg.antivaryOn _).sum_comp_perm_smul_eq_sum_smul_iff fun _ _ ↦ mem_univ _]

end equality_case

/-! #### Strict rearrangement inequality -/

section strict_inequality
variable [PosSMulStrictMono α β] {s : Finset ι} {σ : Perm ι} {f : ι → α} {g : ι → β}

/-- **Strict inequality case of the Rearrangement Inequality**: Pointwise scalar multiplication of
`f` and `g`, which monovary together on `s`, is strictly decreased by a permutation if and only if
`f` and `g ∘ σ` do not monovary together on `s`. Stated by permuting the entries of `g`. -/
/-
**MonovaryOn.sum_smul_comp_perm_lt_sum_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonovaryOn.sum_smul_comp_perm_lt_sum_smul_iff (hfg : MonovaryOn f g s) (hσ
 : {x | σ x != x} subseteq s) : ∑ i in s, f i • g (σ i) < ∑ i in s, f i • g i ↔ 
¬MonovaryOn f (g ∘ σ) s
参数：hfg : MonovaryOn f g s；hσ : {x | σ x != x} subseteq s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MonovaryOn.sum_smul_comp_perm_le_sum_smul`：MonovaryOn.sum_smul_comp_perm
_le_sum_smul (hfg : MonovaryOn f g s) (hσ : {x | σ x != x} subseteq s) : ∑ i in 
s, f i • g (σ i) <= ∑ i in s, f…
· 使用定理 `PosSMulStrictMono.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} [inst :
 Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : PartialOrder α]
   [inst_4 : PartialO…
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonovaryOn.sum_smul_comp_perm_eq_sum_smul_iff`：MonovaryOn.sum_smul_comp_
perm_eq_sum_smul_iff (hfg : MonovaryOn f g s) (hσ : {x | σ x != x} subseteq s) :
 ∑ i in s, f i • g (σ i) = ∑ i in s…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
**Strict inequality case of the Rearrangement Inequality**: Pointwise scalar mul
tiplication of
`f` and `g`, which monovary together on `s`, is strictly decreased by a permutat
ion if and only if
`f` and `g ∘ σ` do not monovary together on `s`. Stated by permuting the entries
 of `g`.
-/
theorem MonovaryOn.sum_smul_comp_perm_lt_sum_smul_iff (hfg : MonovaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) :
    ∑ i ∈ s, f i • g (σ i) < ∑ i ∈ s, f i • g i ↔ ¬MonovaryOn f (g ∘ σ) s := by
  simp [← hfg.sum_smul_comp_perm_eq_sum_smul_iff hσ, lt_iff_le_and_ne,
    hfg.sum_smul_comp_perm_le_sum_smul hσ]

/-- **Strict inequality case of the Rearrangement Inequality**: Pointwise scalar multiplication of
`f` and `g`, which antivary together on `s`, is strictly decreased by a permutation if and only if
`f` and `g ∘ σ` do not antivary together on `s`. Stated by permuting the entries of `g`. -/
/-
**AntivaryOn.sum_smul_lt_sum_smul_comp_perm_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntivaryOn.sum_smul_lt_sum_smul_comp_perm_iff (hfg : AntivaryOn f g s) (hσ
 : {x | σ x != x} subseteq s) : ∑ i in s, f i • g i < ∑ i in s, f i • g (σ i) ↔ 
¬AntivaryOn f (g ∘ σ) s
参数：hfg : AntivaryOn f g s；hσ : {x | σ x != x} subseteq s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `AntivaryOn.sum_smul_le_sum_smul_comp_perm`：AntivaryOn.sum_smul_le_sum_sm
ul_comp_perm (hfg : AntivaryOn f g s) (hσ : {x | σ x != x} subseteq s) : ∑ i in 
s, f i • g i <= ∑ i in s, f i •…
· 使用定理 `PosSMulStrictMono.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} [inst :
 Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : PartialOrder α]
   [inst_4 : PartialO…
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AntivaryOn.sum_smul_comp_perm_eq_sum_smul_iff`：AntivaryOn.sum_smul_comp_
perm_eq_sum_smul_iff (hfg : AntivaryOn f g s) (hσ : {x | σ x != x} subseteq s) :
 ∑ i in s, f i • g (σ i) = ∑ i in s…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
**Strict inequality case of the Rearrangement Inequality**: Pointwise scalar mul
tiplication of
`f` and `g`, which antivary together on `s`, is strictly decreased by a permutat
ion if and only if
`f` and `g ∘ σ` do not antivary together on `s`. Stated by permuting the entries
 of `g`.
-/
theorem AntivaryOn.sum_smul_lt_sum_smul_comp_perm_iff (hfg : AntivaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) :
    ∑ i ∈ s, f i • g i < ∑ i ∈ s, f i • g (σ i) ↔ ¬AntivaryOn f (g ∘ σ) s := by
  simp [← hfg.sum_smul_comp_perm_eq_sum_smul_iff hσ, lt_iff_le_and_ne, eq_comm,
    hfg.sum_smul_le_sum_smul_comp_perm hσ]

/-- **Strict inequality case of the Rearrangement Inequality**: Pointwise scalar multiplication of
`f` and `g`, which monovary together on `s`, is strictly decreased by a permutation if and only if
`f ∘ σ` and `g` do not monovary together on `s`. Stated by permuting the entries of `f`. -/
/-
**MonovaryOn.sum_comp_perm_smul_lt_sum_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonovaryOn.sum_comp_perm_smul_lt_sum_smul_iff (hfg : MonovaryOn f g s) (hσ
 : {x | σ x != x} subseteq s) : ∑ i in s, f (σ i) • g i < ∑ i in s, f i • g i ↔ 
¬MonovaryOn (f ∘ σ) g s
参数：hfg : MonovaryOn f g s；hσ : {x | σ x != x} subseteq s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MonovaryOn.sum_comp_perm_smul_le_sum_smul`：MonovaryOn.sum_comp_perm_smul
_le_sum_smul (hfg : MonovaryOn f g s) (hσ : {x | σ x != x} subseteq s) : ∑ i in 
s, f (σ i) • g i <= ∑ i in s, f…
· 使用定理 `PosSMulStrictMono.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} [inst :
 Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : PartialOrder α]
   [inst_4 : PartialO…
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonovaryOn.sum_comp_perm_smul_eq_sum_smul_iff`：MonovaryOn.sum_comp_perm_
smul_eq_sum_smul_iff (hfg : MonovaryOn f g s) (hσ : {x | σ x != x} subseteq s) :
 ∑ i in s, f (σ i) • g i = ∑ i in s…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
**Strict inequality case of the Rearrangement Inequality**: Pointwise scalar mul
tiplication of
`f` and `g`, which monovary together on `s`, is strictly decreased by a permutat
ion if and only if
`f ∘ σ` and `g` do not monovary together on `s`. Stated by permuting the entries
 of `f`.
-/
theorem MonovaryOn.sum_comp_perm_smul_lt_sum_smul_iff (hfg : MonovaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) :
    ∑ i ∈ s, f (σ i) • g i < ∑ i ∈ s, f i • g i ↔ ¬MonovaryOn (f ∘ σ) g s := by
  simp [← hfg.sum_comp_perm_smul_eq_sum_smul_iff hσ, lt_iff_le_and_ne,
    hfg.sum_comp_perm_smul_le_sum_smul hσ]

/-- **Strict inequality case of the Rearrangement Inequality**: Pointwise scalar multiplication of
`f` and `g`, which antivary together on `s`, is strictly decreased by a permutation if and only if
`f ∘ σ` and `g` do not antivary together on `s`. Stated by permuting the entries of `f`. -/
/-
**AntivaryOn.sum_smul_lt_sum_comp_perm_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntivaryOn.sum_smul_lt_sum_comp_perm_smul_iff (hfg : AntivaryOn f g s) (hσ
 : {x | σ x != x} subseteq s) : ∑ i in s, f i • g i < ∑ i in s, f (σ i) • g i ↔ 
¬AntivaryOn (f ∘ σ) g s
参数：hfg : AntivaryOn f g s；hσ : {x | σ x != x} subseteq s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `AntivaryOn.sum_smul_le_sum_comp_perm_smul`：AntivaryOn.sum_smul_le_sum_co
mp_perm_smul (hfg : AntivaryOn f g s) (hσ : {x | σ x != x} subseteq s) : ∑ i in 
s, f i • g i <= ∑ i in s, f (σ …
· 使用定理 `PosSMulStrictMono.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} [inst :
 Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : PartialOrder α]
   [inst_4 : PartialO…
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AntivaryOn.sum_comp_perm_smul_eq_sum_smul_iff`：AntivaryOn.sum_comp_perm_
smul_eq_sum_smul_iff (hfg : AntivaryOn f g s) (hσ : {x | σ x != x} subseteq s) :
 ∑ i in s, f (σ i) • g i = ∑ i in s…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
**Strict inequality case of the Rearrangement Inequality**: Pointwise scalar mul
tiplication of
`f` and `g`, which antivary together on `s`, is strictly decreased by a permutat
ion if and only if
`f ∘ σ` and `g` do not antivary together on `s`. Stated by permuting the entries
 of `f`.
-/
theorem AntivaryOn.sum_smul_lt_sum_comp_perm_smul_iff (hfg : AntivaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) :
    ∑ i ∈ s, f i • g i < ∑ i ∈ s, f (σ i) • g i ↔ ¬AntivaryOn (f ∘ σ) g s := by
  simp [← hfg.sum_comp_perm_smul_eq_sum_smul_iff hσ, eq_comm, lt_iff_le_and_ne,
    hfg.sum_smul_le_sum_comp_perm_smul hσ]

variable [Fintype ι]

/-- **Strict inequality case of the Rearrangement Inequality**: Pointwise scalar multiplication of
`f` and `g`, which monovary together, is strictly decreased by a permutation if and only if
`f` and `g ∘ σ` do not monovary together. Stated by permuting the entries of `g`. -/
/-
**Monovary.sum_smul_comp_perm_lt_sum_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monovary.sum_smul_comp_perm_lt_sum_smul_iff (hfg : Monovary f g) : ∑ i, f 
i • g (σ i) < ∑ i, f i • g i ↔ ¬Monovary f (g ∘ σ)
参数：hfg : Monovary f g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonovaryOn.sum_smul_comp_perm_lt_sum_smul_iff`：MonovaryOn.sum_smul_comp_
perm_lt_sum_smul_iff (hfg : MonovaryOn f g s) (hσ : {x | σ x != x} subseteq s) :
 ∑ i in s, f i • g (σ i) < ∑ i in s…
· 使用定理 `Monovary.monovaryOn`：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [ins
t : Preorder α] [inst_1 : Preorder β] {f : ι → α} {g : ι → β},   Monovary f g → 
∀ (s : Se…
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
**Strict inequality case of the Rearrangement Inequality**: Pointwise scalar mul
tiplication of
`f` and `g`, which monovary together, is strictly decreased by a permutation if 
and only if
`f` and `g ∘ σ` do not monovary together. Stated by permuting the entries of `g`
.
-/
theorem Monovary.sum_smul_comp_perm_lt_sum_smul_iff (hfg : Monovary f g) :
    ∑ i, f i • g (σ i) < ∑ i, f i • g i ↔ ¬Monovary f (g ∘ σ) := by
  simp [(hfg.monovaryOn _).sum_smul_comp_perm_lt_sum_smul_iff fun _ _ ↦ mem_univ _]

/-- **Strict inequality case of the Rearrangement Inequality**: Pointwise scalar multiplication of
`f` and `g`, which monovary together, is strictly decreased by a permutation if and only if
`f` and `g ∘ σ` do not monovary together. Stated by permuting the entries of `g`. -/
/-
**Monovary.sum_comp_perm_smul_lt_sum_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monovary.sum_comp_perm_smul_lt_sum_smul_iff (hfg : Monovary f g) : ∑ i, f 
(σ i) • g i < ∑ i, f i • g i ↔ ¬Monovary (f ∘ σ) g
参数：hfg : Monovary f g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonovaryOn.sum_comp_perm_smul_lt_sum_smul_iff`：MonovaryOn.sum_comp_perm_
smul_lt_sum_smul_iff (hfg : MonovaryOn f g s) (hσ : {x | σ x != x} subseteq s) :
 ∑ i in s, f (σ i) • g i < ∑ i in s…
· 使用定理 `Monovary.monovaryOn`：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [ins
t : Preorder α] [inst_1 : Preorder β] {f : ι → α} {g : ι → β},   Monovary f g → 
∀ (s : Se…
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
**Strict inequality case of the Rearrangement Inequality**: Pointwise scalar mul
tiplication of
`f` and `g`, which monovary together, is strictly decreased by a permutation if 
and only if
`f` and `g ∘ σ` do not monovary together. Stated by permuting the entries of `g`
.
-/
theorem Monovary.sum_comp_perm_smul_lt_sum_smul_iff (hfg : Monovary f g) :
    ∑ i, f (σ i) • g i < ∑ i, f i • g i ↔ ¬Monovary (f ∘ σ) g := by
  simp [(hfg.monovaryOn _).sum_comp_perm_smul_lt_sum_smul_iff fun _ _ ↦ mem_univ _]

/-- **Strict inequality case of the Rearrangement Inequality**: Pointwise scalar multiplication of
`f` and `g`, which antivary together, is strictly decreased by a permutation if and only if
`f` and `g ∘ σ` do not antivary together. Stated by permuting the entries of `g`. -/
/-
**Antivary.sum_smul_lt_sum_smul_comp_perm_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antivary.sum_smul_lt_sum_smul_comp_perm_iff (hfg : Antivary f g) : ∑ i, f 
i • g i < ∑ i, f i • g (σ i) ↔ ¬Antivary f (g ∘ σ)
参数：hfg : Antivary f g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AntivaryOn.sum_smul_lt_sum_smul_comp_perm_iff`：AntivaryOn.sum_smul_lt_su
m_smul_comp_perm_iff (hfg : AntivaryOn f g s) (hσ : {x | σ x != x} subseteq s) :
 ∑ i in s, f i • g i < ∑ i in s, f …
· 使用定理 `Antivary.antivaryOn`：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [ins
t : Preorder α] [inst_1 : Preorder β] {f : ι → α} {g : ι → β},   Antivary f g → 
∀ (s : Se…
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
**Strict inequality case of the Rearrangement Inequality**: Pointwise scalar mul
tiplication of
`f` and `g`, which antivary together, is strictly decreased by a permutation if 
and only if
`f` and `g ∘ σ` do not antivary together. Stated by permuting the entries of `g`
.
-/
theorem Antivary.sum_smul_lt_sum_smul_comp_perm_iff (hfg : Antivary f g) :
    ∑ i, f i • g i < ∑ i, f i • g (σ i) ↔ ¬Antivary f (g ∘ σ) := by
  simp [(hfg.antivaryOn _).sum_smul_lt_sum_smul_comp_perm_iff fun _ _ ↦ mem_univ _]

/-- **Strict inequality case of the Rearrangement Inequality**: Pointwise scalar multiplication of
`f` and `g`, which antivary together, is strictly decreased by a permutation if and only if
`f ∘ σ` and `g` do not antivary together. Stated by permuting the entries of `f`. -/
/-
**Antivary.sum_smul_lt_sum_comp_perm_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antivary.sum_smul_lt_sum_comp_perm_smul_iff (hfg : Antivary f g) : ∑ i, f 
i • g i < ∑ i, f (σ i) • g i ↔ ¬Antivary (f ∘ σ) g
参数：hfg : Antivary f g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AntivaryOn.sum_smul_lt_sum_comp_perm_smul_iff`：AntivaryOn.sum_smul_lt_su
m_comp_perm_smul_iff (hfg : AntivaryOn f g s) (hσ : {x | σ x != x} subseteq s) :
 ∑ i in s, f i • g i < ∑ i in s, f …
· 使用定理 `Antivary.antivaryOn`：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [ins
t : Preorder α] [inst_1 : Preorder β] {f : ι → α} {g : ι → β},   Antivary f g → 
∀ (s : Se…
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
**Strict inequality case of the Rearrangement Inequality**: Pointwise scalar mul
tiplication of
`f` and `g`, which antivary together, is strictly decreased by a permutation if 
and only if
`f ∘ σ` and `g` do not antivary together. Stated by permuting the entries of `f`
.
-/
theorem Antivary.sum_smul_lt_sum_comp_perm_smul_iff (hfg : Antivary f g) :
    ∑ i, f i • g i < ∑ i, f (σ i) • g i ↔ ¬Antivary (f ∘ σ) g := by
  simp [(hfg.antivaryOn _).sum_smul_lt_sum_comp_perm_smul_iff fun _ _ ↦ mem_univ _]

end strict_inequality
end SMul

/-!
### Multiplication versions

Special cases of the above when scalar multiplication is actually multiplication.
-/

section Mul
variable {s : Finset ι} {σ : Perm ι} {f g : ι → α}

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is maximized when `f` and
`g` monovary together on `s`. Stated by permuting the entries of `g`. -/
/-
**MonovaryOn.sum_mul_comp_perm_le_sum_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonovaryOn.sum_mul_comp_perm_le_sum_mul (hfg : MonovaryOn f g s) (hσ : {x 
| σ x != x} subseteq s) : ∑ i in s, f i * g (σ i) <= ∑ i in s, f i * g i
参数：hfg : MonovaryOn f g s；hσ : {x | σ x != x} subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonovaryOn.sum_smul_comp_perm_le_sum_smul`：MonovaryOn.sum_smul_comp_perm
_le_sum_smul (hfg : MonovaryOn f g s) (hσ : {x | σ x != x} subseteq s) : ∑ i in 
s, f i • g (σ i) <= ∑ i in s, f…
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α

--- 原说明 ---
**Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is maximiz
ed when `f` and
`g` monovary together on `s`. Stated by permuting the entries of `g`.
-/
theorem MonovaryOn.sum_mul_comp_perm_le_sum_mul (hfg : MonovaryOn f g s) (hσ : {x | σ x ≠ x} ⊆ s) :
    ∑ i ∈ s, f i * g (σ i) ≤ ∑ i ∈ s, f i * g i :=
  hfg.sum_smul_comp_perm_le_sum_smul hσ

/-- **Equality case of the Rearrangement Inequality**: Pointwise multiplication of `f` and `g`,
which monovary together on `s`, is unchanged by a permutation if and only if `f` and `g ∘ σ`
monovary together on `s`. Stated by permuting the entries of `g`. -/
/-
**MonovaryOn.sum_mul_comp_perm_eq_sum_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonovaryOn.sum_mul_comp_perm_eq_sum_mul_iff (hfg : MonovaryOn f g s) (hσ :
 {x | σ x != x} subseteq s) : ∑ i in s, f i * g (σ i) = ∑ i in s, f i * g i ↔ Mo
novaryOn f (g ∘ σ) s
参数：hfg : MonovaryOn f g s；hσ : {x | σ x != x} subseteq s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonovaryOn.sum_smul_comp_perm_eq_sum_smul_iff`：MonovaryOn.sum_smul_comp_
perm_eq_sum_smul_iff (hfg : MonovaryOn f g s) (hσ : {x | σ x != x} subseteq s) :
 ∑ i in s, f i • g (σ i) = ∑ i in s…
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsStrictOrderedModule.toPosSMulStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α

--- 原说明 ---
**Equality case of the Rearrangement Inequality**: Pointwise multiplication of `
f` and `g`,
which monovary together on `s`, is unchanged by a permutation if and only if `f`
 and `g ∘ σ`
monovary together on `s`. Stated by permuting the entries of `g`.
-/
theorem MonovaryOn.sum_mul_comp_perm_eq_sum_mul_iff (hfg : MonovaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) :
    ∑ i ∈ s, f i * g (σ i) = ∑ i ∈ s, f i * g i ↔ MonovaryOn f (g ∘ σ) s :=
  hfg.sum_smul_comp_perm_eq_sum_smul_iff hσ

/-- **Strict inequality case of the Rearrangement Inequality**: Pointwise scalar multiplication of
`f` and `g`, which monovary together on `s`, is strictly decreased by a permutation if and only if
`f` and `g ∘ σ` do not monovary together on `s`. Stated by permuting the entries of `g`. -/
/-
**MonovaryOn.sum_mul_comp_perm_lt_sum_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonovaryOn.sum_mul_comp_perm_lt_sum_mul_iff (hfg : MonovaryOn f g s) (hσ :
 {x | σ x != x} subseteq s) : ∑ i in s, f i • g (σ i) < ∑ i in s, f i • g i ↔ ¬M
onovaryOn f (g ∘ σ) s
参数：hfg : MonovaryOn f g s；hσ : {x | σ x != x} subseteq s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonovaryOn.sum_smul_comp_perm_lt_sum_smul_iff`：MonovaryOn.sum_smul_comp_
perm_lt_sum_smul_iff (hfg : MonovaryOn f g s) (hσ : {x | σ x != x} subseteq s) :
 ∑ i in s, f i • g (σ i) < ∑ i in s…
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsStrictOrderedModule.toPosSMulStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α

--- 原说明 ---
**Strict inequality case of the Rearrangement Inequality**: Pointwise scalar mul
tiplication of
`f` and `g`, which monovary together on `s`, is strictly decreased by a permutat
ion if and only if
`f` and `g ∘ σ` do not monovary together on `s`. Stated by permuting the entries
 of `g`.
-/
theorem MonovaryOn.sum_mul_comp_perm_lt_sum_mul_iff (hfg : MonovaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) :
    ∑ i ∈ s, f i • g (σ i) < ∑ i ∈ s, f i • g i ↔ ¬MonovaryOn f (g ∘ σ) s :=
  hfg.sum_smul_comp_perm_lt_sum_smul_iff hσ

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is maximized when `f` and
`g` monovary together on `s`. Stated by permuting the entries of `f`. -/
/-
**MonovaryOn.sum_comp_perm_mul_le_sum_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonovaryOn.sum_comp_perm_mul_le_sum_mul (hfg : MonovaryOn f g s) (hσ : {x 
| σ x != x} subseteq s) : ∑ i in s, f (σ i) * g i <= ∑ i in s, f i * g i
参数：hfg : MonovaryOn f g s；hσ : {x | σ x != x} subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonovaryOn.sum_comp_perm_smul_le_sum_smul`：MonovaryOn.sum_comp_perm_smul
_le_sum_smul (hfg : MonovaryOn f g s) (hσ : {x | σ x != x} subseteq s) : ∑ i in 
s, f (σ i) • g i <= ∑ i in s, f…
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α

--- 原说明 ---
**Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is maximiz
ed when `f` and
`g` monovary together on `s`. Stated by permuting the entries of `f`.
-/
theorem MonovaryOn.sum_comp_perm_mul_le_sum_mul (hfg : MonovaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) : ∑ i ∈ s, f (σ i) * g i ≤ ∑ i ∈ s, f i * g i :=
  hfg.sum_comp_perm_smul_le_sum_smul hσ

/-- **Equality case of the Rearrangement Inequality**: Pointwise multiplication of `f` and `g`,
which monovary together on `s`, is unchanged by a permutation if and only if `f ∘ σ` and `g`
monovary together on `s`. Stated by permuting the entries of `f`. -/
/-
**MonovaryOn.sum_comp_perm_mul_eq_sum_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonovaryOn.sum_comp_perm_mul_eq_sum_mul_iff (hfg : MonovaryOn f g s) (hσ :
 {x | σ x != x} subseteq s) : ∑ i in s, f (σ i) * g i = ∑ i in s, f i * g i ↔ Mo
novaryOn (f ∘ σ) g s
参数：hfg : MonovaryOn f g s；hσ : {x | σ x != x} subseteq s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonovaryOn.sum_comp_perm_smul_eq_sum_smul_iff`：MonovaryOn.sum_comp_perm_
smul_eq_sum_smul_iff (hfg : MonovaryOn f g s) (hσ : {x | σ x != x} subseteq s) :
 ∑ i in s, f (σ i) • g i = ∑ i in s…
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsStrictOrderedModule.toPosSMulStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α

--- 原说明 ---
**Equality case of the Rearrangement Inequality**: Pointwise multiplication of `
f` and `g`,
which monovary together on `s`, is unchanged by a permutation if and only if `f 
∘ σ` and `g`
monovary together on `s`. Stated by permuting the entries of `f`.
-/
theorem MonovaryOn.sum_comp_perm_mul_eq_sum_mul_iff (hfg : MonovaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) :
    ∑ i ∈ s, f (σ i) * g i = ∑ i ∈ s, f i * g i ↔ MonovaryOn (f ∘ σ) g s :=
  hfg.sum_comp_perm_smul_eq_sum_smul_iff hσ

/-- **Strict inequality case of the Rearrangement Inequality**: Pointwise multiplication of
`f` and `g`, which monovary together on `s`, is strictly decreased by a permutation if and only if
`f ∘ σ` and `g` do not monovary together on `s`. Stated by permuting the entries of `f`. -/
/-
**MonovaryOn.sum_comp_perm_mul_lt_sum_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonovaryOn.sum_comp_perm_mul_lt_sum_mul_iff (hfg : MonovaryOn f g s) (hσ :
 {x | σ x != x} subseteq s) : ∑ i in s, f (σ i) * g i < ∑ i in s, f i * g i ↔ ¬M
onovaryOn (f ∘ σ) g s
参数：hfg : MonovaryOn f g s；hσ : {x | σ x != x} subseteq s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonovaryOn.sum_comp_perm_smul_lt_sum_smul_iff`：MonovaryOn.sum_comp_perm_
smul_lt_sum_smul_iff (hfg : MonovaryOn f g s) (hσ : {x | σ x != x} subseteq s) :
 ∑ i in s, f (σ i) • g i < ∑ i in s…
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsStrictOrderedModule.toPosSMulStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α

--- 原说明 ---
**Strict inequality case of the Rearrangement Inequality**: Pointwise multiplica
tion of
`f` and `g`, which monovary together on `s`, is strictly decreased by a permutat
ion if and only if
`f ∘ σ` and `g` do not monovary together on `s`. Stated by permuting the entries
 of `f`.
-/
theorem MonovaryOn.sum_comp_perm_mul_lt_sum_mul_iff (hfg : MonovaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) :
    ∑ i ∈ s, f (σ i) * g i < ∑ i ∈ s, f i * g i ↔ ¬MonovaryOn (f ∘ σ) g s :=
  hfg.sum_comp_perm_smul_lt_sum_smul_iff hσ

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is minimized when `f` and
`g` antivary together on `s`. Stated by permuting the entries of `g`. -/
/-
**AntivaryOn.sum_mul_le_sum_mul_comp_perm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntivaryOn.sum_mul_le_sum_mul_comp_perm (hfg : AntivaryOn f g s) (hσ : {x 
| σ x != x} subseteq s) : ∑ i in s, f i * g i <= ∑ i in s, f i * g (σ i)
参数：hfg : AntivaryOn f g s；hσ : {x | σ x != x} subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntivaryOn.sum_smul_le_sum_smul_comp_perm`：AntivaryOn.sum_smul_le_sum_sm
ul_comp_perm (hfg : AntivaryOn f g s) (hσ : {x | σ x != x} subseteq s) : ∑ i in 
s, f i • g i <= ∑ i in s, f i •…
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α

--- 原说明 ---
**Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is minimiz
ed when `f` and
`g` antivary together on `s`. Stated by permuting the entries of `g`.
-/
theorem AntivaryOn.sum_mul_le_sum_mul_comp_perm (hfg : AntivaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) : ∑ i ∈ s, f i * g i ≤ ∑ i ∈ s, f i * g (σ i) :=
  hfg.sum_smul_le_sum_smul_comp_perm hσ

/-- **Equality case of the Rearrangement Inequality**: Pointwise multiplication of `f` and `g`,
which antivary together on `s`, is unchanged by a permutation if and only if `f` and `g ∘ σ`
antivary together on `s`. Stated by permuting the entries of `g`. -/
/-
**AntivaryOn.sum_mul_eq_sum_mul_comp_perm_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntivaryOn.sum_mul_eq_sum_mul_comp_perm_iff (hfg : AntivaryOn f g s) (hσ :
 {x | σ x != x} subseteq s) : ∑ i in s, f i * g (σ i) = ∑ i in s, f i * g i ↔ An
tivaryOn f (g ∘ σ) s
参数：hfg : AntivaryOn f g s；hσ : {x | σ x != x} subseteq s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntivaryOn.sum_smul_comp_perm_eq_sum_smul_iff`：AntivaryOn.sum_smul_comp_
perm_eq_sum_smul_iff (hfg : AntivaryOn f g s) (hσ : {x | σ x != x} subseteq s) :
 ∑ i in s, f i • g (σ i) = ∑ i in s…
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsStrictOrderedModule.toPosSMulStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α

--- 原说明 ---
**Equality case of the Rearrangement Inequality**: Pointwise multiplication of `
f` and `g`,
which antivary together on `s`, is unchanged by a permutation if and only if `f`
 and `g ∘ σ`
antivary together on `s`. Stated by permuting the entries of `g`.
-/
theorem AntivaryOn.sum_mul_eq_sum_mul_comp_perm_iff (hfg : AntivaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) :
    ∑ i ∈ s, f i * g (σ i) = ∑ i ∈ s, f i * g i ↔ AntivaryOn f (g ∘ σ) s :=
  hfg.sum_smul_comp_perm_eq_sum_smul_iff hσ

/-- **Strict inequality case of the Rearrangement Inequality**: Pointwise multiplication of
`f` and `g`, which antivary together on `s`, is strictly decreased by a permutation if and only if
`f` and `g ∘ σ` do not antivary together on `s`. Stated by permuting the entries of `g`. -/
/-
**AntivaryOn.sum_mul_lt_sum_mul_comp_perm_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntivaryOn.sum_mul_lt_sum_mul_comp_perm_iff (hfg : AntivaryOn f g s) (hσ :
 {x | σ x != x} subseteq s) : ∑ i in s, f i * g i < ∑ i in s, f i * g (σ i) ↔ ¬A
ntivaryOn f (g ∘ σ) s
参数：hfg : AntivaryOn f g s；hσ : {x | σ x != x} subseteq s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntivaryOn.sum_smul_lt_sum_smul_comp_perm_iff`：AntivaryOn.sum_smul_lt_su
m_smul_comp_perm_iff (hfg : AntivaryOn f g s) (hσ : {x | σ x != x} subseteq s) :
 ∑ i in s, f i • g i < ∑ i in s, f …
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsStrictOrderedModule.toPosSMulStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α

--- 原说明 ---
**Strict inequality case of the Rearrangement Inequality**: Pointwise multiplica
tion of
`f` and `g`, which antivary together on `s`, is strictly decreased by a permutat
ion if and only if
`f` and `g ∘ σ` do not antivary together on `s`. Stated by permuting the entries
 of `g`.
-/
theorem AntivaryOn.sum_mul_lt_sum_mul_comp_perm_iff (hfg : AntivaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) :
    ∑ i ∈ s, f i * g i < ∑ i ∈ s, f i * g (σ i) ↔ ¬AntivaryOn f (g ∘ σ) s :=
  hfg.sum_smul_lt_sum_smul_comp_perm_iff hσ

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is minimized when `f` and
`g` antivary together on `s`. Stated by permuting the entries of `f`. -/
/-
**AntivaryOn.sum_mul_le_sum_comp_perm_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntivaryOn.sum_mul_le_sum_comp_perm_mul (hfg : AntivaryOn f g s) (hσ : {x 
| σ x != x} subseteq s) : ∑ i in s, f i * g i <= ∑ i in s, f (σ i) * g i
参数：hfg : AntivaryOn f g s；hσ : {x | σ x != x} subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntivaryOn.sum_smul_le_sum_comp_perm_smul`：AntivaryOn.sum_smul_le_sum_co
mp_perm_smul (hfg : AntivaryOn f g s) (hσ : {x | σ x != x} subseteq s) : ∑ i in 
s, f i • g i <= ∑ i in s, f (σ …
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α

--- 原说明 ---
**Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is minimiz
ed when `f` and
`g` antivary together on `s`. Stated by permuting the entries of `f`.
-/
theorem AntivaryOn.sum_mul_le_sum_comp_perm_mul (hfg : AntivaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) : ∑ i ∈ s, f i * g i ≤ ∑ i ∈ s, f (σ i) * g i :=
  hfg.sum_smul_le_sum_comp_perm_smul hσ

/-- **Equality case of the Rearrangement Inequality**: Pointwise multiplication of `f` and `g`,
which antivary together on `s`, is unchanged by a permutation if and only if `f ∘ σ` and `g`
antivary together on `s`. Stated by permuting the entries of `f`. -/
/-
**AntivaryOn.sum_comp_perm_mul_eq_sum_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntivaryOn.sum_comp_perm_mul_eq_sum_mul_iff (hfg : AntivaryOn f g s) (hσ :
 {x | σ x != x} subseteq s) : ∑ i in s, f (σ i) * g i = ∑ i in s, f i * g i ↔ An
tivaryOn (f ∘ σ) g s
参数：hfg : AntivaryOn f g s；hσ : {x | σ x != x} subseteq s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntivaryOn.sum_comp_perm_smul_eq_sum_smul_iff`：AntivaryOn.sum_comp_perm_
smul_eq_sum_smul_iff (hfg : AntivaryOn f g s) (hσ : {x | σ x != x} subseteq s) :
 ∑ i in s, f (σ i) • g i = ∑ i in s…
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsStrictOrderedModule.toPosSMulStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α

--- 原说明 ---
**Equality case of the Rearrangement Inequality**: Pointwise multiplication of `
f` and `g`,
which antivary together on `s`, is unchanged by a permutation if and only if `f 
∘ σ` and `g`
antivary together on `s`. Stated by permuting the entries of `f`.
-/
theorem AntivaryOn.sum_comp_perm_mul_eq_sum_mul_iff (hfg : AntivaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) :
    ∑ i ∈ s, f (σ i) * g i = ∑ i ∈ s, f i * g i ↔ AntivaryOn (f ∘ σ) g s :=
  hfg.sum_comp_perm_smul_eq_sum_smul_iff hσ

/-- **Strict inequality case of the Rearrangement Inequality**: Pointwise multiplication of
`f` and `g`, which antivary together on `s`, is strictly decreased by a permutation if and only if
`f ∘ σ` and `g` do not antivary together on `s`. Stated by permuting the entries of `f`. -/
/-
**AntivaryOn.sum_mul_lt_sum_comp_perm_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntivaryOn.sum_mul_lt_sum_comp_perm_mul_iff (hfg : AntivaryOn f g s) (hσ :
 {x | σ x != x} subseteq s) : ∑ i in s, f i * g i < ∑ i in s, f (σ i) * g i ↔ ¬A
ntivaryOn (f ∘ σ) g s
参数：hfg : AntivaryOn f g s；hσ : {x | σ x != x} subseteq s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntivaryOn.sum_smul_lt_sum_comp_perm_smul_iff`：AntivaryOn.sum_smul_lt_su
m_comp_perm_smul_iff (hfg : AntivaryOn f g s) (hσ : {x | σ x != x} subseteq s) :
 ∑ i in s, f i • g i < ∑ i in s, f …
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsStrictOrderedModule.toPosSMulStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α

--- 原说明 ---
**Strict inequality case of the Rearrangement Inequality**: Pointwise multiplica
tion of
`f` and `g`, which antivary together on `s`, is strictly decreased by a permutat
ion if and only if
`f ∘ σ` and `g` do not antivary together on `s`. Stated by permuting the entries
 of `f`.
-/
theorem AntivaryOn.sum_mul_lt_sum_comp_perm_mul_iff (hfg : AntivaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) :
    ∑ i ∈ s, f i * g i < ∑ i ∈ s, f (σ i) * g i ↔ ¬AntivaryOn (f ∘ σ) g s :=
  hfg.sum_smul_lt_sum_comp_perm_smul_iff hσ

variable [Fintype ι]

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is maximized when `f` and
`g` monovary together. Stated by permuting the entries of `g`. -/
/-
**Monovary.sum_mul_comp_perm_le_sum_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monovary.sum_mul_comp_perm_le_sum_mul (hfg : Monovary f g) : ∑ i, f i * g 
(σ i) <= ∑ i, f i * g i
参数：hfg : Monovary f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monovary.sum_smul_comp_perm_le_sum_smul`：Monovary.sum_smul_comp_perm_le_
sum_smul (hfg : Monovary f g) : ∑ i, f i • g (σ i) <= ∑ i, f i • g i
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α

--- 原说明 ---
**Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is maximiz
ed when `f` and
`g` monovary together. Stated by permuting the entries of `g`.
-/
theorem Monovary.sum_mul_comp_perm_le_sum_mul (hfg : Monovary f g) :
    ∑ i, f i * g (σ i) ≤ ∑ i, f i * g i :=
  hfg.sum_smul_comp_perm_le_sum_smul

/-- **Equality case of the Rearrangement Inequality**: Pointwise multiplication of `f` and `g`,
which monovary together, is unchanged by a permutation if and only if `f` and `g ∘ σ` monovary
together. Stated by permuting the entries of `g`. -/
/-
**Monovary.sum_mul_comp_perm_eq_sum_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monovary.sum_mul_comp_perm_eq_sum_mul_iff (hfg : Monovary f g) : ∑ i, f i 
* g (σ i) = ∑ i, f i * g i ↔ Monovary f (g ∘ σ)
参数：hfg : Monovary f g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monovary.sum_smul_comp_perm_eq_sum_smul_iff`：Monovary.sum_smul_comp_perm
_eq_sum_smul_iff (hfg : Monovary f g) : ∑ i, f i • g (σ i) = ∑ i, f i • g i ↔ Mo
novary f (g ∘ σ)
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsStrictOrderedModule.toPosSMulStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α

--- 原说明 ---
**Equality case of the Rearrangement Inequality**: Pointwise multiplication of `
f` and `g`,
which monovary together, is unchanged by a permutation if and only if `f` and `g
 ∘ σ` monovary
together. Stated by permuting the entries of `g`.
-/
theorem Monovary.sum_mul_comp_perm_eq_sum_mul_iff (hfg : Monovary f g) :
    ∑ i, f i * g (σ i) = ∑ i, f i * g i ↔ Monovary f (g ∘ σ) :=
  hfg.sum_smul_comp_perm_eq_sum_smul_iff

/-- **Strict inequality case of the Rearrangement Inequality**: Pointwise multiplication of
`f` and `g`, which monovary together, is strictly decreased by a permutation if and only if
`f` and `g ∘ σ` do not monovary together. Stated by permuting the entries of `g`. -/
/-
**Monovary.sum_mul_comp_perm_lt_sum_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monovary.sum_mul_comp_perm_lt_sum_mul_iff (hfg : Monovary f g) : ∑ i, f i 
* g (σ i) < ∑ i, f i * g i ↔ ¬Monovary f (g ∘ σ)
参数：hfg : Monovary f g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monovary.sum_smul_comp_perm_lt_sum_smul_iff`：Monovary.sum_smul_comp_perm
_lt_sum_smul_iff (hfg : Monovary f g) : ∑ i, f i • g (σ i) < ∑ i, f i • g i ↔ ¬M
onovary f (g ∘ σ)
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsStrictOrderedModule.toPosSMulStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α

--- 原说明 ---
**Strict inequality case of the Rearrangement Inequality**: Pointwise multiplica
tion of
`f` and `g`, which monovary together, is strictly decreased by a permutation if 
and only if
`f` and `g ∘ σ` do not monovary together. Stated by permuting the entries of `g`
.
-/
theorem Monovary.sum_mul_comp_perm_lt_sum_mul_iff (hfg : Monovary f g) :
    ∑ i, f i * g (σ i) < ∑ i, f i * g i ↔ ¬Monovary f (g ∘ σ) :=
  hfg.sum_smul_comp_perm_lt_sum_smul_iff

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is maximized when `f` and
`g` monovary together. Stated by permuting the entries of `f`. -/
/-
**Monovary.sum_comp_perm_mul_le_sum_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monovary.sum_comp_perm_mul_le_sum_mul (hfg : Monovary f g) : ∑ i, f (σ i) 
* g i <= ∑ i, f i * g i
参数：hfg : Monovary f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monovary.sum_comp_perm_smul_le_sum_smul`：Monovary.sum_comp_perm_smul_le_
sum_smul (hfg : Monovary f g) : ∑ i, f (σ i) • g i <= ∑ i, f i • g i
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α

--- 原说明 ---
**Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is maximiz
ed when `f` and
`g` monovary together. Stated by permuting the entries of `f`.
-/
theorem Monovary.sum_comp_perm_mul_le_sum_mul (hfg : Monovary f g) :
    ∑ i, f (σ i) * g i ≤ ∑ i, f i * g i :=
  hfg.sum_comp_perm_smul_le_sum_smul

/-- **Equality case of the Rearrangement Inequality**: Pointwise multiplication of `f` and `g`,
which monovary together, is unchanged by a permutation if and only if `f ∘ σ` and `g` monovary
together. Stated by permuting the entries of `g`. -/
/-
**Monovary.sum_comp_perm_mul_eq_sum_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monovary.sum_comp_perm_mul_eq_sum_mul_iff (hfg : Monovary f g) : ∑ i, f (σ
 i) * g i = ∑ i, f i * g i ↔ Monovary (f ∘ σ) g
参数：hfg : Monovary f g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monovary.sum_comp_perm_smul_eq_sum_smul_iff`：Monovary.sum_comp_perm_smul
_eq_sum_smul_iff (hfg : Monovary f g) : ∑ i, f (σ i) • g i = ∑ i, f i • g i ↔ Mo
novary (f ∘ σ) g
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsStrictOrderedModule.toPosSMulStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α

--- 原说明 ---
**Equality case of the Rearrangement Inequality**: Pointwise multiplication of `
f` and `g`,
which monovary together, is unchanged by a permutation if and only if `f ∘ σ` an
d `g` monovary
together. Stated by permuting the entries of `g`.
-/
theorem Monovary.sum_comp_perm_mul_eq_sum_mul_iff (hfg : Monovary f g) :
    ∑ i, f (σ i) * g i = ∑ i, f i * g i ↔ Monovary (f ∘ σ) g :=
  hfg.sum_comp_perm_smul_eq_sum_smul_iff

/-- **Strict inequality case of the Rearrangement Inequality**: Pointwise multiplication of
`f` and `g`, which monovary together, is strictly decreased by a permutation if and only if
`f` and `g ∘ σ` do not monovary together. Stated by permuting the entries of `g`. -/
/-
**Monovary.sum_comp_perm_mul_lt_sum_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monovary.sum_comp_perm_mul_lt_sum_mul_iff (hfg : Monovary f g) : ∑ i, f (σ
 i) * g i < ∑ i, f i * g i ↔ ¬Monovary (f ∘ σ) g
参数：hfg : Monovary f g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monovary.sum_comp_perm_smul_lt_sum_smul_iff`：Monovary.sum_comp_perm_smul
_lt_sum_smul_iff (hfg : Monovary f g) : ∑ i, f (σ i) • g i < ∑ i, f i • g i ↔ ¬M
onovary (f ∘ σ) g
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsStrictOrderedModule.toPosSMulStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α

--- 原说明 ---
**Strict inequality case of the Rearrangement Inequality**: Pointwise multiplica
tion of
`f` and `g`, which monovary together, is strictly decreased by a permutation if 
and only if
`f` and `g ∘ σ` do not monovary together. Stated by permuting the entries of `g`
.
-/
theorem Monovary.sum_comp_perm_mul_lt_sum_mul_iff (hfg : Monovary f g) :
    ∑ i, f (σ i) * g i < ∑ i, f i * g i ↔ ¬Monovary (f ∘ σ) g :=
  hfg.sum_comp_perm_smul_lt_sum_smul_iff

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is minimized when `f` and
`g` antivary together. Stated by permuting the entries of `g`. -/
/-
**Antivary.sum_mul_le_sum_mul_comp_perm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antivary.sum_mul_le_sum_mul_comp_perm (hfg : Antivary f g) : ∑ i, f i * g 
i <= ∑ i, f i * g (σ i)
参数：hfg : Antivary f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antivary.sum_smul_le_sum_smul_comp_perm`：Antivary.sum_smul_le_sum_smul_c
omp_perm (hfg : Antivary f g) : ∑ i, f i • g i <= ∑ i, f i • g (σ i)
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α

--- 原说明 ---
**Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is minimiz
ed when `f` and
`g` antivary together. Stated by permuting the entries of `g`.
-/
theorem Antivary.sum_mul_le_sum_mul_comp_perm (hfg : Antivary f g) :
    ∑ i, f i * g i ≤ ∑ i, f i * g (σ i) :=
  hfg.sum_smul_le_sum_smul_comp_perm

/-- **Equality case of the Rearrangement Inequality**: Pointwise multiplication of `f` and `g`,
which antivary together, is unchanged by a permutation if and only if `f` and `g ∘ σ` antivary
together. Stated by permuting the entries of `g`. -/
/-
**Antivary.sum_mul_eq_sum_mul_comp_perm_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antivary.sum_mul_eq_sum_mul_comp_perm_iff (hfg : Antivary f g) : ∑ i, f i 
* g (σ i) = ∑ i, f i * g i ↔ Antivary f (g ∘ σ)
参数：hfg : Antivary f g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antivary.sum_smul_comp_perm_eq_sum_smul_iff`：Antivary.sum_smul_comp_perm
_eq_sum_smul_iff (hfg : Antivary f g) : ∑ i, f i • g (σ i) = ∑ i, f i • g i ↔ An
tivary f (g ∘ σ)
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsStrictOrderedModule.toPosSMulStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α

--- 原说明 ---
**Equality case of the Rearrangement Inequality**: Pointwise multiplication of `
f` and `g`,
which antivary together, is unchanged by a permutation if and only if `f` and `g
 ∘ σ` antivary
together. Stated by permuting the entries of `g`.
-/
theorem Antivary.sum_mul_eq_sum_mul_comp_perm_iff (hfg : Antivary f g) :
    ∑ i, f i * g (σ i) = ∑ i, f i * g i ↔ Antivary f (g ∘ σ) :=
  hfg.sum_smul_comp_perm_eq_sum_smul_iff

/-- **Strict inequality case of the Rearrangement Inequality**: Pointwise multiplication of
`f` and `g`, which antivary together, is strictly decreased by a permutation if and only if
`f` and `g ∘ σ` do not antivary together. Stated by permuting the entries of `g`. -/
/-
**Antivary.sum_mul_lt_sum_mul_comp_perm_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antivary.sum_mul_lt_sum_mul_comp_perm_iff (hfg : Antivary f g) : ∑ i, f i 
• g i < ∑ i, f i • g (σ i) ↔ ¬Antivary f (g ∘ σ)
参数：hfg : Antivary f g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antivary.sum_smul_lt_sum_smul_comp_perm_iff`：Antivary.sum_smul_lt_sum_sm
ul_comp_perm_iff (hfg : Antivary f g) : ∑ i, f i • g i < ∑ i, f i • g (σ i) ↔ ¬A
ntivary f (g ∘ σ)
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsStrictOrderedModule.toPosSMulStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α

--- 原说明 ---
**Strict inequality case of the Rearrangement Inequality**: Pointwise multiplica
tion of
`f` and `g`, which antivary together, is strictly decreased by a permutation if 
and only if
`f` and `g ∘ σ` do not antivary together. Stated by permuting the entries of `g`
.
-/
theorem Antivary.sum_mul_lt_sum_mul_comp_perm_iff (hfg : Antivary f g) :
    ∑ i, f i • g i < ∑ i, f i • g (σ i) ↔ ¬Antivary f (g ∘ σ) :=
  hfg.sum_smul_lt_sum_smul_comp_perm_iff

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is minimized when `f` and
`g` antivary together. Stated by permuting the entries of `f`. -/
/-
**Antivary.sum_mul_le_sum_comp_perm_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antivary.sum_mul_le_sum_comp_perm_mul (hfg : Antivary f g) : ∑ i, f i * g 
i <= ∑ i, f (σ i) * g i
参数：hfg : Antivary f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antivary.sum_smul_le_sum_comp_perm_smul`：Antivary.sum_smul_le_sum_comp_p
erm_smul (hfg : Antivary f g) : ∑ i, f i • g i <= ∑ i, f (σ i) • g i
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α

--- 原说明 ---
**Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is minimiz
ed when `f` and
`g` antivary together. Stated by permuting the entries of `f`.
-/
theorem Antivary.sum_mul_le_sum_comp_perm_mul (hfg : Antivary f g) :
    ∑ i, f i * g i ≤ ∑ i, f (σ i) * g i :=
  hfg.sum_smul_le_sum_comp_perm_smul

/-- **Equality case of the Rearrangement Inequality**: Pointwise multiplication of `f` and `g`,
which antivary together, is unchanged by a permutation if and only if `f ∘ σ` and `g` antivary
together. Stated by permuting the entries of `f`. -/
/-
**Antivary.sum_comp_perm_mul_eq_sum_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antivary.sum_comp_perm_mul_eq_sum_mul_iff (hfg : Antivary f g) : ∑ i, f (σ
 i) * g i = ∑ i, f i * g i ↔ Antivary (f ∘ σ) g
参数：hfg : Antivary f g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antivary.sum_comp_perm_smul_eq_sum_smul_iff`：Antivary.sum_comp_perm_smul
_eq_sum_smul_iff (hfg : Antivary f g) : ∑ i, f (σ i) • g i = ∑ i, f i • g i ↔ An
tivary (f ∘ σ) g
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsStrictOrderedModule.toPosSMulStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α

--- 原说明 ---
**Equality case of the Rearrangement Inequality**: Pointwise multiplication of `
f` and `g`,
which antivary together, is unchanged by a permutation if and only if `f ∘ σ` an
d `g` antivary
together. Stated by permuting the entries of `f`.
-/
theorem Antivary.sum_comp_perm_mul_eq_sum_mul_iff (hfg : Antivary f g) :
    ∑ i, f (σ i) * g i = ∑ i, f i * g i ↔ Antivary (f ∘ σ) g :=
  hfg.sum_comp_perm_smul_eq_sum_smul_iff

/-- **Strict inequality case of the Rearrangement Inequality**: Pointwise multiplication of
`f` and `g`, which antivary together, is strictly decreased by a permutation if and only if
`f ∘ σ` and `g` do not antivary together. Stated by permuting the entries of `f`. -/
/-
**Antivary.sum_mul_lt_sum_comp_perm_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antivary.sum_mul_lt_sum_comp_perm_mul_iff (hfg : Antivary f g) : ∑ i, f i 
* g i < ∑ i, f (σ i) * g i ↔ ¬Antivary (f ∘ σ) g
参数：hfg : Antivary f g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antivary.sum_smul_lt_sum_comp_perm_smul_iff`：Antivary.sum_smul_lt_sum_co
mp_perm_smul_iff (hfg : Antivary f g) : ∑ i, f i • g i < ∑ i, f (σ i) • g i ↔ ¬A
ntivary (f ∘ σ) g
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsStrictOrderedModule.toPosSMulStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α

--- 原说明 ---
**Strict inequality case of the Rearrangement Inequality**: Pointwise multiplica
tion of
`f` and `g`, which antivary together, is strictly decreased by a permutation if 
and only if
`f ∘ σ` and `g` do not antivary together. Stated by permuting the entries of `f`
.
-/
theorem Antivary.sum_mul_lt_sum_comp_perm_mul_iff (hfg : Antivary f g) :
    ∑ i, f i * g i < ∑ i, f (σ i) * g i ↔ ¬Antivary (f ∘ σ) g :=
  hfg.sum_smul_lt_sum_comp_perm_smul_iff

end Mul

