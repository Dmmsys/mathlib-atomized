/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Pi
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.Finset.Sups
public import Mathlib.Order.Birkhoff
public import Mathlib.Order.Booleanisation
public import Mathlib.Order.Sublattice
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.GCongr

/-!
# The four functions theorem and corollaries

This file proves the four functions theorem. The statement is that if
`f₁ a * f₂ b ≤ f₃ (a ⊓ b) * f₄ (a ⊔ b)` for all `a`, `b` in a finite distributive lattice, then
`(∑ x ∈ s, f₁ x) * (∑ x ∈ t, f₂ x) ≤ (∑ x ∈ s ⊼ t, f₃ x) * (∑ x ∈ s ⊻ t, f₄ x)` where
`s ⊼ t = {a ⊓ b | a ∈ s, b ∈ t}`, `s ⊻ t = {a ⊔ b | a ∈ s, b ∈ t}`.

The proof uses Birkhoff's representation theorem to restrict to the case where the finite
distributive lattice is in fact a finite powerset algebra, namely `Finset α` for some finite `α`.
Then it proves this new statement by induction on the size of `α`.

## Main declarations

The two versions of the four functions theorem are
* `Finset.four_functions_theorem` for finite powerset algebras.
* `four_functions_theorem` for any finite distributive lattices.

We deduce a number of corollaries:
* `Finset.le_card_infs_mul_card_sups`: Daykin inequality. `|s| |t| ≤ |s ⊼ t| |s ⊻ t|`
* `holley`: Holley inequality.
* `fkg`: Fortuin-Kasteleyn-Ginibre inequality.
* `Finset.card_le_card_diffs`: Marica-Schönheim inequality. `|s| ≤ |{a \ b | a, b ∈ s}|`

## TODO

Prove that lattices in which `Finset.le_card_infs_mul_card_sups` holds are distributive. See
Daykin, *A lattice is distributive iff |A| |B| <= |A ∨ B| |A ∧ B|*

Prove the Fishburn-Shepp inequality.

Is `collapse` a construct generally useful for set family inductions? If so, we should move it to an
earlier file and give it a proper API.

## References

[*Applications of the FKG Inequality and Its Relatives*, Graham][Graham1983]
-/

public section

open Finset Fintype Function
open scoped FinsetFamily

variable {α β : Type*}

section Finset
variable [DecidableEq α] [CommSemiring β] [LinearOrder β] [IsStrictOrderedRing β]
  {𝒜 : Finset (Finset α)} {a : α} {f f₁ f₂ f₃ f₄ : Finset α → β} {s t u : Finset α}

/-- The `n = 1` case of the Ahlswede-Daykin inequality. Note that we can't just expand everything
out and bound termwise since `c₀ * d₁` appears twice on the RHS of the assumptions while `c₁ * d₀`
does not appear. -/
/-
**ineq** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `n = 1` case of the Ahlswede-Daykin inequality. Note that we can't just expa
nd everything
out and bound termwise since `c₀ * d₁` appears twice on the RHS of the assumptio
ns while `c₁ * d₀`
does not appear.
-/
private lemma ineq [ExistsAddOfLE β] {a₀ a₁ b₀ b₁ c₀ c₁ d₀ d₁ : β}
    (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁) (hb₀ : 0 ≤ b₀) (hb₁ : 0 ≤ b₁)
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (hd₀ : 0 ≤ d₀) (hd₁ : 0 ≤ d₁)
    (h₀₀ : a₀ * b₀ ≤ c₀ * d₀) (h₁₀ : a₁ * b₀ ≤ c₀ * d₁)
    (h₀₁ : a₀ * b₁ ≤ c₀ * d₁) (h₁₁ : a₁ * b₁ ≤ c₁ * d₁) :
    (a₀ + a₁) * (b₀ + b₁) ≤ (c₀ + c₁) * (d₀ + d₁) := by
  calc
    _ = a₀ * b₀ + (a₀ * b₁ + a₁ * b₀) + a₁ * b₁ := by ring
    _ ≤ c₀ * d₀ + (c₀ * d₁ + c₁ * d₀) + c₁ * d₁ := add_le_add_three h₀₀ ?_ h₁₁
    _ = (c₀ + c₁) * (d₀ + d₁) := by ring
  obtain hcd | hcd := (mul_nonneg hc₀ hd₁).eq_or_lt'
  · rw [hcd] at h₀₁ h₁₀
    rw [h₀₁.antisymm, h₁₀.antisymm, add_zero] <;> positivity
  refine le_of_mul_le_mul_right ?_ hcd
  calc (a₀ * b₁ + a₁ * b₀) * (c₀ * d₁)
      = a₀ * b₁ * (c₀ * d₁) + c₀ * d₁ * (a₁ * b₀) := by ring
    _ ≤ a₀ * b₁ * (a₁ * b₀) + c₀ * d₁ * (c₀ * d₁) := mul_add_mul_le_mul_add_mul h₀₁ h₁₀
    _ = a₀ * b₀ * (a₁ * b₁) + c₀ * d₁ * (c₀ * d₁) := by ring
    _ ≤ c₀ * d₀ * (c₁ * d₁) + c₀ * d₁ * (c₀ * d₁) := by gcongr
    _ = (c₀ * d₁ + c₁ * d₀) * (c₀ * d₁) := by ring

set_option backward.privateInPublic true in
/-
**collapse** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def collapse (𝒜 : Finset (Finset α)) (a : α) (f : Finset α → β) (s : Finset α) : β :=
  ∑ t ∈ 𝒜 with t.erase a = s, f t
/-
**erase_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma erase_eq_iff (hs : a ∉ s) : t.erase a = s ↔ t = s ∨ t = insert a s := by
  grind
/-
**filter_collapse_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma filter_collapse_eq (ha : a ∉ s) (𝒜 : Finset (Finset α)) :
    {t ∈ 𝒜 | t.erase a = s} =
      if s ∈ 𝒜 then
        (if insert a s ∈ 𝒜 then {s, insert a s} else {s})
      else
        (if insert a s ∈ 𝒜 then {insert a s} else ∅) := by
  ext t; split_ifs <;> simp [erase_eq_iff ha] <;> aesop

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
omit [LinearOrder β] [IsStrictOrderedRing β] in
/-
**collapse_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：collapse_eq (ha : a ∉ s) (𝒜 : Finset (Finset α)) (f : Finset α -> β) : col
lapse 𝒜 a f s = (if s in 𝒜 then f s else 0) + if insert a s in 𝒜 then f (insert 
a s) else 0
参数：ha : a ∉ s；𝒜 : Finset (Finset α)；f : Finset α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Combinatorics.SetFamily.FourFunctions.0.collapse.eq_1`：
∀ {α : Type u_1} {β : Type u_2} [inst : DecidableEq α] [inst_1 : CommSemiring β]
 (𝒜 : Finset (Finset α)) (a : α)   (f : Finset α → β) (s : F…
· 使用定理 `_private.Mathlib.Combinatorics.SetFamily.FourFunctions.0.filter_collapse
_eq`：∀ {α : Type u_1} [inst : DecidableEq α] {a : α} {s : Finset α},   a ∉ s →  
   ∀ (𝒜 : Finset (Finset α)),       {t ∈ 𝒜 | t.erase a = s} =    …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ne_of_mem_of_not_mem'`：∀ {α : Type u_1} {β : Type u_2} [inst : Membershi
p α β] {s t : β} {a : α}, a ∈ s → a ∉ t → s ≠ t
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
lemma collapse_eq (ha : a ∉ s) (𝒜 : Finset (Finset α)) (f : Finset α → β) :
    collapse 𝒜 a f s = (if s ∈ 𝒜 then f s else 0) +
      if insert a s ∈ 𝒜 then f (insert a s) else 0 := by
  rw [collapse, filter_collapse_eq ha]
  split_ifs <;> simp [(ne_of_mem_of_not_mem' (mem_insert_self a s) ha).symm, *]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
omit [LinearOrder β] [IsStrictOrderedRing β] in
/-
**collapse_of_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：collapse_of_mem (ha : a ∉ s) (ht : t in 𝒜) (hu : u in 𝒜) (hts : t = s) (hu
s : u = insert a s) : collapse 𝒜 a f s = f t + f u
参数：ha : a ∉ s；ht : t in 𝒜；hu : u in 𝒜；hts : t = s；hus : u = insert a s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `collapse_eq`：collapse_eq (ha : a ∉ s) (𝒜 : Finset (Finset α)) (f : Finse
t α -> β) : collapse 𝒜 a f s = (if s in 𝒜 then f s else 0) + if insert a s in 𝒜 
t…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma collapse_of_mem (ha : a ∉ s) (ht : t ∈ 𝒜) (hu : u ∈ 𝒜) (hts : t = s)
    (hus : u = insert a s) : collapse 𝒜 a f s = f t + f u := by
  subst hts; subst hus; simp_rw [collapse_eq ha, if_pos ht, if_pos hu]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**le_collapse_of_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_collapse_of_mem (ha : a ∉ s) (hf : 0 <= f) (hts : t = s) (ht : t in 𝒜) 
: f t <= collapse 𝒜 a f s
参数：ha : a ∉ s；hf : 0 <= f；hts : t = s；ht : t in 𝒜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `collapse_eq`：collapse_eq (ha : a ∉ s) (𝒜 : Finset (Finset α)) (f : Finse
t α -> β) : collapse 𝒜 a f s = (if s in 𝒜 then f s else 0) + if insert a s in 𝒜 
t…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `le_add_of_nonneg_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1
 : LE α] [AddLeftMono α] {a b : α}, 0 ≤ b → a ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma le_collapse_of_mem (ha : a ∉ s) (hf : 0 ≤ f) (hts : t = s) (ht : t ∈ 𝒜) :
    f t ≤ collapse 𝒜 a f s := by
  subst hts
  rw [collapse_eq ha, if_pos ht]
  split_ifs
  · exact le_add_of_nonneg_right <| hf _
  · rw [add_zero]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**le_collapse_of_insert_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_collapse_of_insert_mem (ha : a ∉ s) (hf : 0 <= f) (hts : t = insert a s
) (ht : t in 𝒜) : f t <= collapse 𝒜 a f s
参数：ha : a ∉ s；hf : 0 <= f；hts : t = insert a s；ht : t in 𝒜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `collapse_eq`：collapse_eq (ha : a ∉ s) (𝒜 : Finset (Finset α)) (f : Finse
t α -> β) : collapse 𝒜 a f s = (if s in 𝒜 then f s else 0) + if insert a s in 𝒜 
t…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `le_add_of_nonneg_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 
: LE α] [AddRightMono α] {a b : α}, 0 ≤ b → a ≤ b + a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma le_collapse_of_insert_mem (ha : a ∉ s) (hf : 0 ≤ f) (hts : t = insert a s) (ht : t ∈ 𝒜) :
    f t ≤ collapse 𝒜 a f s := by
  rw [collapse_eq ha, ← hts, if_pos ht]
  split_ifs
  · exact le_add_of_nonneg_left <| hf _
  · rw [zero_add]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**collapse_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：collapse_nonneg (hf : 0 <= f) : 0 <= collapse 𝒜 a f
参数：hf : 0 <= f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
lemma collapse_nonneg (hf : 0 ≤ f) : 0 ≤ collapse 𝒜 a f := fun _s ↦ sum_nonneg fun _t _ ↦ hf _

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**collapse_modular** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：collapse_modular [ExistsAddOfLE β] (hu : a ∉ u) (h₁ : 0 <= f₁) (h₂ : 0 <= 
f₂) (h₃ : 0 <= f₃) (h₄ : 0 <= f₄) (h : forall ⦃s⦄, s subseteq insert a u -> fora
ll ⦃t⦄, t subseteq insert a u -> f₁ s * f₂ t <= f₃ (s inter t) * f₄ (s union t))
 (𝒜 ℬ : Finset (Finset α)) : forall ⦃s⦄, s subseteq u -> forall ⦃t⦄, t subseteq 
u -> collapse 𝒜 a f₁ s * collapse ℬ a f₂ t <= collapse (𝒜 ⊼ ℬ) a f₃ (s inter t) 
* collapse (𝒜 ⊻ ℬ) a f₄ (s union t)
参数：hu : a ∉ u；h₁ : 0 <= f₁；h₂ : 0 <= f₂；h₃ : 0 <= f₃；h₄ : 0 <= f₄；h : forall ⦃s⦄
, s subseteq insert a u -> forall ⦃t⦄, t subseteq insert a u -> f₁ s * f₂ t <= f
₃ (s inter t) * f₄ (s union t)；𝒜 ℬ : Finset (Finset α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.subset_insert`：∀ {α : Type u_1} [inst : DecidableEq α] (a : α) (s
 : Finset α), s ⊆ insert a s
· 使用定理 `Finset.insert_subset_insert`：insert_subset_insert (a : α) {s t : Finset 
α} (h : s subseteq t) : insert a s subseteq insert a t
· 使用定理 `Finset.notMem_mono`：notMem_mono {s t : Finset α} (h : s subseteq t) {a :
 α} : a ∉ t -> a ∉ s
· 使用定理 `Finset.inter_subset_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ∩ s₂ ⊆ s₁
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.notMem_union`：notMem_union : a ∉ s union t ↔ a ∉ s ∧ a ∉ t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `collapse_eq`：collapse_eq (ha : a ∉ s) (𝒜 : Finset (Finset α)) (f : Finse
t α -> β) : collapse 𝒜 a f s = (if s in 𝒜 then f s else 0) + if insert a s in 𝒜 
t…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用引理 `collapse_of_mem`：collapse_of_mem (ha : a ∉ s) (ht : t in 𝒜) (hu : u in 𝒜
) (hts : t = s) (hus : u = insert a s) : collapse 𝒜 a f s = f t + f u
· 使用引理 `Finset.inter_mem_infs`：inter_mem_infs : s in 𝒜 -> t in ℬ -> s inter t in
 𝒜 ⊼ ℬ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.insert_inter_distrib`：insert_inter_distrib (s t : Finset α) (a : 
α) : insert a (s inter t) = insert a s inter insert a t
· 使用引理 `Finset.union_mem_sups`：union_mem_sups : s in 𝒜 -> t in ℬ -> s union t in
 𝒜 ⊻ ℬ
· 使用定理 `Finset.insert_union_distrib`：insert_union_distrib (a : α) (s t : Finset 
α) : insert a (s union t) = insert a s union insert a t
· 使用定理 `_private.Mathlib.Combinatorics.SetFamily.FourFunctions.0.ineq`：∀ {β : Ty
pe u_2} [inst : CommSemiring β] [inst_1 : LinearOrder β] [IsStrictOrderedRing β]
 [ExistsAddOfLE β]   {a₀ a₁ b₀ b₁ c₀ c₁ d₀ d₁ : β},…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.union_insert`：union_insert (a : α) (s t : Finset α) : s union ins
ert a t = insert a (s union t)
· 使用定理 `Finset.insert_union`：insert_union (a : α) (s t : Finset α) : insert a s 
union t = insert a (s union t)
· 使用定理 `Finset.insert_eq_of_mem`：insert_eq_of_mem (h : a in s) : insert a s = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Finset.insert_inter_of_notMem`：insert_inter_of_notMem {s₁ s₂ : Finset α}
 {a : α} (h : a ∉ s₂) : insert a s₁ inter s₂ = s₁ inter s₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.inter_insert_of_notMem`：inter_insert_of_notMem {s₁ s₂ : Finset α}
 {a : α} (h : a ∉ s₁) : s₁ inter insert a s₂ = s₁ inter s₂
（共 55 条，此处仅展示前 30 条）
-/
lemma collapse_modular [ExistsAddOfLE β]
    (hu : a ∉ u) (h₁ : 0 ≤ f₁) (h₂ : 0 ≤ f₂) (h₃ : 0 ≤ f₃) (h₄ : 0 ≤ f₄)
    (h : ∀ ⦃s⦄, s ⊆ insert a u → ∀ ⦃t⦄, t ⊆ insert a u → f₁ s * f₂ t ≤ f₃ (s ∩ t) * f₄ (s ∪ t))
    (𝒜 ℬ : Finset (Finset α)) :
    ∀ ⦃s⦄, s ⊆ u → ∀ ⦃t⦄, t ⊆ u → collapse 𝒜 a f₁ s * collapse ℬ a f₂ t ≤
      collapse (𝒜 ⊼ ℬ) a f₃ (s ∩ t) * collapse (𝒜 ⊻ ℬ) a f₄ (s ∪ t) := by
  rintro s hsu t htu
  -- Gather a bunch of facts we'll need a lot
  have := hsu.trans <| subset_insert a _
  have := htu.trans <| subset_insert a _
  have := insert_subset_insert a hsu
  have := insert_subset_insert a htu
  have has := notMem_mono hsu hu
  have hat := notMem_mono htu hu
  have : a ∉ s ∩ t := notMem_mono (inter_subset_left.trans hsu) hu
  have := notMem_union.2 ⟨has, hat⟩
  rw [collapse_eq has]
  split_ifs
  · rw [collapse_eq hat]
    split_ifs
    · rw [collapse_of_mem ‹_› (inter_mem_infs ‹_› ‹_›) (inter_mem_infs ‹_› ‹_›) rfl
        (insert_inter_distrib _ _ _).symm, collapse_of_mem ‹_› (union_mem_sups ‹_› ‹_›)
        (union_mem_sups ‹_› ‹_›) rfl (insert_union_distrib _ _ _).symm]
      refine ineq (h₁ _) (h₁ _) (h₂ _) (h₂ _) (h₃ _) (h₃ _) (h₄ _) (h₄ _) (h ‹_› ‹_›) ?_ ?_ ?_
      · simpa [*] using h ‹insert a s ⊆ _› ‹t ⊆ _›
      · simpa [*] using h ‹s ⊆ _› ‹insert a t ⊆ _›
      · simpa [*] using h ‹insert a s ⊆ _› ‹insert a t ⊆ _›
    · rw [add_zero, add_mul]
      refine (add_le_add (h ‹_› ‹_›) <| h ‹_› ‹_›).trans ?_
      rw [collapse_of_mem ‹_› (union_mem_sups ‹_› ‹_›) (union_mem_sups ‹_› ‹_›) rfl
        (insert_union _ _ _), insert_inter_of_notMem ‹_›, ← mul_add]
      gcongr
      exacts [add_nonneg (h₄ _) <| h₄ _, le_collapse_of_mem ‹_› h₃ rfl <| inter_mem_infs ‹_› ‹_›]
    · rw [zero_add, add_mul]
      refine (add_le_add (h ‹_› ‹_›) <| h ‹_› ‹_›).trans ?_
      rw [collapse_of_mem ‹_› (inter_mem_infs ‹_› ‹_›) (inter_mem_infs ‹_› ‹_›)
        (inter_insert_of_notMem ‹_›) (insert_inter_distrib _ _ _).symm, union_insert,
        insert_union_distrib, ← add_mul]
      gcongr
      exacts [add_nonneg (h₃ _) <| h₃ _,
        le_collapse_of_insert_mem ‹_› h₄ (insert_union_distrib _ _ _).symm (union_mem_sups ‹_› ‹_›)]
    · rw [add_zero, mul_zero]
      exact mul_nonneg (collapse_nonneg h₃ _) <| collapse_nonneg h₄ _
  · rw [add_zero, collapse_eq hat, mul_add]
    split_ifs
    · refine (add_le_add (h ‹_› ‹_›) <| h ‹_› ‹_›).trans ?_
      rw [collapse_of_mem ‹_› (union_mem_sups ‹_› ‹_›) (union_mem_sups ‹_› ‹_›) rfl
        (union_insert _ _ _), inter_insert_of_notMem ‹_›, ← mul_add]
      gcongr
      · exact add_nonneg (h₄ _) (h₄ _)
      · exact le_collapse_of_mem ‹_› h₃ rfl <| inter_mem_infs ‹_› ‹_›
    · rw [mul_zero, add_zero]
      exact (h ‹_› ‹_›).trans <| mul_le_mul (le_collapse_of_mem ‹_› h₃ rfl <|
        inter_mem_infs ‹_› ‹_›) (le_collapse_of_mem ‹_› h₄ rfl <| union_mem_sups ‹_› ‹_›)
        (h₄ _) <| collapse_nonneg h₃ _
    · rw [mul_zero, zero_add]
      refine (h ‹_› ‹_›).trans <| mul_le_mul ?_ (le_collapse_of_insert_mem ‹_› h₄
        (union_insert _ _ _) <| union_mem_sups ‹_› ‹_›) (h₄ _) <| collapse_nonneg h₃ _
      exact le_collapse_of_mem (notMem_mono inter_subset_left ‹_›) h₃
        (inter_insert_of_notMem ‹_›) <| inter_mem_infs ‹_› ‹_›
    · simp_rw [mul_zero, add_zero]
      exact mul_nonneg (collapse_nonneg h₃ _) <| collapse_nonneg h₄ _
  · rw [zero_add, collapse_eq hat, mul_add]
    split_ifs
    · refine (add_le_add (h ‹_› ‹_›) <| h ‹_› ‹_›).trans ?_
      rw [collapse_of_mem ‹_› (inter_mem_infs ‹_› ‹_›) (inter_mem_infs ‹_› ‹_›)
        (insert_inter_of_notMem ‹_›) (insert_inter_distrib _ _ _).symm,
        insert_inter_of_notMem ‹_›, ← insert_inter_distrib, insert_union, insert_union_distrib,
        ← add_mul]
      gcongr
      · exact add_nonneg (h₃ _) (h₃ _)
      · exact le_collapse_of_insert_mem ‹_› h₄
          (insert_union_distrib _ _ _).symm <| union_mem_sups ‹_› ‹_›
    · rw [mul_zero, add_zero]
      refine (h ‹_› ‹_›).trans <| mul_le_mul (le_collapse_of_mem ‹_› h₃
        (insert_inter_of_notMem ‹_›) <| inter_mem_infs ‹_› ‹_›) (le_collapse_of_insert_mem ‹_› h₄
        (insert_union _ _ _) <| union_mem_sups ‹_› ‹_›) (h₄ _) <| collapse_nonneg h₃ _
    · rw [mul_zero, zero_add]
      exact (h ‹_› ‹_›).trans <| mul_le_mul (le_collapse_of_insert_mem ‹_› h₃
        (insert_inter_distrib _ _ _).symm <| inter_mem_infs ‹_› ‹_›) (le_collapse_of_insert_mem ‹_›
        h₄ (insert_union_distrib _ _ _).symm <| union_mem_sups ‹_› ‹_›) (h₄ _) <|
        collapse_nonneg h₃ _
    · simp_rw [mul_zero, add_zero]
      exact mul_nonneg (collapse_nonneg h₃ _) <| collapse_nonneg h₄ _
  · simp_rw [add_zero, zero_mul]
    exact mul_nonneg (collapse_nonneg h₃ _) <| collapse_nonneg h₄ _

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
omit [LinearOrder β] [IsStrictOrderedRing β] in
/-
**sum_collapse** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sum_collapse (h𝒜 : 𝒜 subseteq (insert a u).powerset) (hu : a ∉ u) : ∑ s in
 u.powerset, collapse 𝒜 a f s = ∑ s in 𝒜, f s
参数：h𝒜 : 𝒜 subseteq (insert a u).powerset；hu : a ∉ u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_ite_mem`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s t : Finset ι) (f : ι → M),   (∑ i ∈ s, if i ∈ t
 then f …
· 使用定理 `Finset.sum_image`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} [inst :
 AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι]   {s : Finset κ} {g : κ →
 ι}, S…
· 使用定理 `Set.InjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α →
 β}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁
· 使用定理 `Finset.notMem_mono`：notMem_mono {s t : Finset α} (h : s subseteq t) {a :
 α} : a ∉ t -> a ∉ s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_powerset`：mem_powerset {s t : Finset α} : s in powerset t ↔ s
 subseteq t
· 使用定理 `Set.LeftInvOn.injOn`：injOn (h : LeftInvOn f₁' f s) : InjOn f s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Finset.insert_erase_invOn`：insert_erase_invOn : Set.InvOn (insert a) (fu
n s => s.erase a) {s : Finset α | a in s} {s : Finset α | a ∉ s}
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `collapse_eq`：collapse_eq (ha : a ∉ s) (𝒜 : Finset (Finset α)) (f : Finse
t α -> β) : collapse 𝒜 a f s = (if s in 𝒜 then f s else 0) + if insert a s in 𝒜 
t…
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.subset_insert_iff`：subset_insert_iff {a : α} {s t : Finset α} : s
 subseteq insert a t ↔ s.erase a subseteq t
· 使用定理 `Finset.insert_subset_insert`：insert_subset_insert (a : α) {s t : Finset 
α} (h : s subseteq t) : insert a s subseteq insert a t
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `Finset.erase_ne_self`：erase_ne_self : s.erase a != s ↔ a in s
· 使用定理 `Finset.sum_union`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   Disjoint s₁ s₂ → ∑
 x ∈ s…
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `disjoint_sdiff_self_right`：disjoint_sdiff_self_right : Disjoint x (y \ x
)
· 使用定理 `Finset.union_inter_distrib_right`：union_inter_distrib_right (s t u : Fin
set α) : (s union t) inter u = s inter u union t inter u
（共 35 条，此处仅展示前 30 条）
-/
lemma sum_collapse (h𝒜 : 𝒜 ⊆ (insert a u).powerset) (hu : a ∉ u) :
    ∑ s ∈ u.powerset, collapse 𝒜 a f s = ∑ s ∈ 𝒜, f s := by
  calc
    _ = ∑ s ∈ u.powerset ∩ 𝒜, f s + ∑ s ∈ u.powerset.image (insert a) ∩ 𝒜, f s := ?_
    _ = ∑ s ∈ u.powerset ∩ 𝒜, f s + ∑ s ∈ ((insert a u).powerset \ u.powerset) ∩ 𝒜, f s := ?_
    _ = ∑ s ∈ 𝒜, f s := ?_
  · rw [← Finset.sum_ite_mem, ← Finset.sum_ite_mem, sum_image, ← sum_add_distrib]
    · exact sum_congr rfl fun s hs ↦ collapse_eq (notMem_mono (mem_powerset.1 hs) hu) _ _
    · exact (insert_erase_invOn.2.injOn).mono fun s hs ↦ notMem_mono (mem_powerset.1 hs) hu
  · congr with s
    simp only [mem_image, mem_powerset, mem_sdiff, subset_insert_iff]
    refine ⟨?_, fun h ↦ ⟨_, h.1, ?_⟩⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨subset_insert_iff.1 <| insert_subset_insert _ hs, fun h ↦
        hu <| h <| mem_insert_self _ _⟩
    · rw [insert_erase (erase_ne_self.1 fun hs ↦ ?_)]
      rw [hs] at h
      exact h.2 h.1
  · rw [← sum_union (disjoint_sdiff_self_right.mono inf_le_left inf_le_left),
      ← union_inter_distrib_right, union_sdiff_of_subset (powerset_mono.2 <| subset_insert _ _),
      inter_eq_right.2 h𝒜]

variable [ExistsAddOfLE β]

/-- The **Four Functions Theorem** on a powerset algebra. See `four_functions_theorem` for the
finite distributive lattice generalisation. -/
/-
**Finset.four_functions_theorem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : DecidableEq α] [inst_1 : CommSemir
ing β] [inst_2 : LinearOrder β]   [IsStrictOrderedRing β] {f₁ f₂ f₃ f₄ : Finset 
α → β} [ExistsAddOfLE β] (u : Finset α),   0 ≤ f₁ →     0 ≤ f₂ →       0 ≤ f₃ → 
        0 ≤ f₄ →           (∀ ⦃s : Finset α⦄, s ⊆ u → ∀ ⦃t : Finset α⦄, t ⊆ u → 
f₁ s * f₂ t ≤ f₃ (s ∩ t) * f₄ (s ∪ t)) →             ∀ {𝒜 ℬ : Finset (Finset α)}
,               𝒜 ⊆ u.powerset →                 ℬ ⊆ u.powerset → (∑ s ∈ 𝒜, f₁ s
) * ∑ s ∈ ℬ, f₂ s ≤ (∑ s ∈ 𝒜 ⊼ ℬ, f₃ s) * ∑ s ∈ 𝒜 ⊻ ℬ, f₄ s
参数：u : Finset α；∀ ⦃s : Finset α⦄, s ⊆ u → ∀ ⦃t : Finset α⦄, t ⊆ u → f₁ s * f₂ t 
≤ f₃ (s ∩ t) * f₄ (s ∪ t)；Finset α；∑ s ∈ 𝒜, f₁ s；∑ s ∈ 𝒜 ⊼ ℬ, f₃ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.empty_infs`：empty_infs : ∅ ⊼ t = ∅
· 使用定理 `Finset.empty_sups`：empty_sups : ∅ ⊻ t = ∅
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Finset.infs_empty`：infs_empty : s ⊼ ∅ = ∅
· 使用定理 `Finset.sups_empty`：sups_empty : s ⊻ ∅ = ∅
· 使用定理 `Finset.infs_singleton`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 :
 SemilatticeInf α] {s : Finset α} {b : α},   s ⊼ {b} = Finset.image (fun x => x 
⊓ b) s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `Finset.image_singleton`：image_singleton (f : α -> β) (a : α) : image f {
a} = {f a}
· 使用定理 `Finset.sups_singleton`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 :
 SemilatticeSup α] {s : Finset α} {b : α},   s ⊻ {b} = Finset.image (fun x => x 
⊔ b) s
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `Finset.inter_self`：inter_self (s : Finset α) : s inter s = s
· 使用定理 `Finset.union_idempotent`：union_idempotent (s : Finset α) : s union s = s
· 使用定理 `subset_refl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preord
er α] (a : α), a ⊆ a
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.powerset_infs_powerset_self`：∀ {α : Type u_2} [inst : DecidableEq
 α] (s : Finset α), s.powerset ⊼ s.powerset = s.powerset
· 使用定理 `Finset.infs_subset`：infs_subset : s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁
 ⊼ t₁ subseteq s₂ ⊼ t₂
· 使用定理 `Finset.powerset_sups_powerset_self`：∀ {α : Type u_2} [inst : DecidableEq
 α] (s : Finset α), s.powerset ⊻ s.powerset = s.powerset
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
The **Four Functions Theorem** on a powerset algebra. See `four_functions_theore
m` for the
finite distributive lattice generalisation.
-/
protected lemma Finset.four_functions_theorem (u : Finset α)
    (h₁ : 0 ≤ f₁) (h₂ : 0 ≤ f₂) (h₃ : 0 ≤ f₃) (h₄ : 0 ≤ f₄)
    (h : ∀ ⦃s⦄, s ⊆ u → ∀ ⦃t⦄, t ⊆ u → f₁ s * f₂ t ≤ f₃ (s ∩ t) * f₄ (s ∪ t))
    {𝒜 ℬ : Finset (Finset α)} (h𝒜 : 𝒜 ⊆ u.powerset) (hℬ : ℬ ⊆ u.powerset) :
    (∑ s ∈ 𝒜, f₁ s) * ∑ s ∈ ℬ, f₂ s ≤ (∑ s ∈ 𝒜 ⊼ ℬ, f₃ s) * ∑ s ∈ 𝒜 ⊻ ℬ, f₄ s := by
  induction u using Finset.induction generalizing f₁ f₂ f₃ f₄ 𝒜 ℬ with
  | empty =>
    simp only [Finset.powerset_empty, Finset.subset_singleton_iff] at h𝒜 hℬ
    obtain rfl | rfl := h𝒜
    · simp
    obtain rfl | rfl := hℬ
    · simp
    simpa using h (subset_refl ∅) subset_rfl
  | insert a u hu ih =>
    specialize ih (collapse_nonneg h₁) (collapse_nonneg h₂) (collapse_nonneg h₃)
      (collapse_nonneg h₄) (collapse_modular hu h₁ h₂ h₃ h₄ h 𝒜 ℬ) Subset.rfl Subset.rfl
    have : 𝒜 ⊼ ℬ ⊆ powerset (insert a u) := by simpa using infs_subset h𝒜 hℬ
    have : 𝒜 ⊻ ℬ ⊆ powerset (insert a u) := by simpa using sups_subset h𝒜 hℬ
    simpa only [powerset_sups_powerset_self, powerset_infs_powerset_self, sum_collapse,
      not_false_eq_true, *] using ih

variable (f₁ f₂ f₃ f₄) [Finite α]
/-
**four_functions_theorem_aux** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma four_functions_theorem_aux (h₁ : 0 ≤ f₁) (h₂ : 0 ≤ f₂) (h₃ : 0 ≤ f₃) (h₄ : 0 ≤ f₄)
    (h : ∀ s t, f₁ s * f₂ t ≤ f₃ (s ∩ t) * f₄ (s ∪ t)) (𝒜 ℬ : Finset (Finset α)) :
    (∑ s ∈ 𝒜, f₁ s) * ∑ s ∈ ℬ, f₂ s ≤ (∑ s ∈ 𝒜 ⊼ ℬ, f₃ s) * ∑ s ∈ 𝒜 ⊻ ℬ, f₄ s := by
  have := Fintype.ofFinite α
  refine univ.four_functions_theorem h₁ h₂ h₃ h₄ ?_ ?_ ?_ <;> simp [h]

end Finset

section DistribLattice
variable [DistribLattice α] [CommSemiring β] [LinearOrder β] [IsStrictOrderedRing β]
  [ExistsAddOfLE β] (f f₁ f₂ f₃ f₄ g μ : α → β)

set_option backward.isDefEq.respectTransparency false in
/-- The **Four Functions Theorem**, aka **Ahlswede-Daykin Inequality**. -/
/-
**four_functions_theorem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：four_functions_theorem [DecidableEq α] (h₁ : 0 <= f₁) (h₂ : 0 <= f₂) (h₃ :
 0 <= f₃) (h₄ : 0 <= f₄) (h : forall a b, f₁ a * f₂ b <= f₃ (a ⊓ b) * f₄ (a ⊔ b)
) (s t : Finset α) : (∑ a in s, f₁ a) * ∑ a in t, f₂ a <= (∑ a in s ⊼ t, f₃ a) *
 ∑ a in s ⊻ t, f₄ a
参数：h₁ : 0 <= f₁；h₂ : 0 <= f₂；h₃ : 0 <= f₃；h₄ : 0 <= f₄；h : forall a b, f₁ a * f₂
 b <= f₃ (a ⊓ b) * f₄ (a ⊔ b)；s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSublattice.supClosed`：∀ {α : Type u_3} [inst : Lattice α] {s : Set α},
 IsSublattice s → SupClosed s
· 使用定理 `isSublattice_latticeClosure`：∀ {α : Type u_3} [inst : Lattice α] {s : Se
t α}, IsSublattice (latticeClosure s)
· 使用定理 `IsSublattice.infClosed`：∀ {α : Type u_3} [inst : Lattice α] {s : Set α},
 IsSublattice s → InfClosed s
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
· 使用引理 `Set.Finite.latticeClosure`：Set.Finite.latticeClosure (hs : s.Finite) : (
latticeClosure s).Finite
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用定理 `Finset.image_preimage`：image_preimage [DecidableEq β] (f : α -> β) (s : 
Finset β) [forall x, Decidable (x in Set.range f)] (hf : Set.InjOn f (f ⁻¹' ↑s))
 : image f …
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `subset_latticeClosure`：∀ {α : Type u_3} [inst : Lattice α] {s : Set α}, 
s ⊆ latticeClosure s
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用引理 `exists_birkhoff_representation`：exists_birkhoff_representation.{u} (α : 
Type u) [Finite α] [DistribLattice α] : exists (β : Type u) (_ : DecidableEq β) 
(_ : Fintype β) (f :…
· 使用定理 `_private.Mathlib.Combinatorics.SetFamily.FourFunctions.0.four_functions_
theorem_aux`：∀ {α : Type u_1} {β : Type u_2} [inst : DecidableEq α] [inst_1 : Co
mmSemiring β] [inst_2 : LinearOrder β]   [IsStrictOrderedRing β] (f₁ f₂ f…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Function.extend_nonneg`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [
inst : Zero γ] [inst_1 : LE γ] {f : α → β} {g : α → γ} {e : β → γ},   0 ≤ g → 0 
≤ e → 0 ≤ Fu…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `LatticeHomClass.toSupHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type
 u_8} {inst : Lattice α} {inst_1 : Lattice β} {inst_2 : FunLike F α β}   [self :
 LatticeHomClass F …
· 使用定理 `LatticeHom.instLatticeHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : 
Lattice α] [inst_1 : Lattice β], LatticeHomClass (LatticeHom α β) α β
· 使用定理 `LatticeHomClass.toInfHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type
 u_8} {inst : Lattice α} {inst_1 : Lattice β} {inst_2 : FunLike F α β}   [self :
 LatticeHomClass F …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
The **Four Functions Theorem**, aka **Ahlswede-Daykin Inequality**.
-/
lemma four_functions_theorem [DecidableEq α] (h₁ : 0 ≤ f₁) (h₂ : 0 ≤ f₂) (h₃ : 0 ≤ f₃) (h₄ : 0 ≤ f₄)
    (h : ∀ a b, f₁ a * f₂ b ≤ f₃ (a ⊓ b) * f₄ (a ⊔ b)) (s t : Finset α) :
    (∑ a ∈ s, f₁ a) * ∑ a ∈ t, f₂ a ≤ (∑ a ∈ s ⊼ t, f₃ a) * ∑ a ∈ s ⊻ t, f₄ a := by
  classical
  set L : Sublattice α := ⟨latticeClosure (s ∪ t), isSublattice_latticeClosure.1,
    isSublattice_latticeClosure.2⟩
  have : Finite L := (s.finite_toSet.union t.finite_toSet).latticeClosure.to_subtype
  set s' : Finset L := s.preimage (↑) Subtype.coe_injective.injOn
  set t' : Finset L := t.preimage (↑) Subtype.coe_injective.injOn
  have hs' : s'.map ⟨L.subtype, Subtype.coe_injective⟩ = s := by
    simpa [s', map_eq_image, image_preimage, filter_eq_self] using!
      fun a ha ↦ subset_latticeClosure <| Set.subset_union_left ha
  have ht' : t'.map ⟨L.subtype, Subtype.coe_injective⟩ = t := by
    simpa [t', map_eq_image, image_preimage, filter_eq_self] using!
      fun a ha ↦ subset_latticeClosure <| Set.subset_union_right ha
  clear_value s' t'
  obtain ⟨β, _, _, g, hg⟩ := exists_birkhoff_representation L
  have := four_functions_theorem_aux (extend g (f₁ ∘ (↑)) 0) (extend g (f₂ ∘ (↑)) 0)
    (extend g (f₃ ∘ (↑)) 0) (extend g (f₄ ∘ (↑)) 0) (extend_nonneg (fun _ ↦ h₁ _) le_rfl)
    (extend_nonneg (fun _ ↦ h₂ _) le_rfl) (extend_nonneg (fun _ ↦ h₃ _) le_rfl)
    (extend_nonneg (fun _ ↦ h₄ _) le_rfl) ?_ (s'.map ⟨g, hg⟩) (t'.map ⟨g, hg⟩)
  · simpa only [← hs', ← ht', ← map_sups, ← map_infs, sum_map, Embedding.coeFn_mk, hg.extend_apply]
      using! this
  rintro s t
  obtain ⟨a, rfl⟩ | hs := em (∃ a, g a = s)
  · obtain ⟨b, rfl⟩ | ht := em (∃ b, g b = t)
    · simp_rw [← sup_eq_union, ← inf_eq_inter, ← map_sup, ← map_inf, hg.extend_apply]
      exact h _ _
    · simpa [extend_apply' _ _ _ ht] using! mul_nonneg
        (extend_nonneg (fun a : L ↦ h₃ a) le_rfl _) (extend_nonneg (fun a : L ↦ h₄ a) le_rfl _)
  · simpa [extend_apply' _ _ _ hs] using! mul_nonneg
      (extend_nonneg (fun a : L ↦ h₃ a) le_rfl _) (extend_nonneg (fun a : L ↦ h₄ a) le_rfl _)

/-- An inequality of Daykin. Interestingly, any lattice in which this inequality holds is
distributive. -/
/-
**Finset.le_card_infs_mul_card_sups** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Finset.le_card_infs_mul_card_sups [DecidableEq α] (s t : Finset α) : #s * 
#t <= #(s ⊼ t) * #(s ⊻ t)
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `four_functions_theorem`：four_functions_theorem [DecidableEq α] (h₁ : 0 <
= f₁) (h₂ : 0 <= f₂) (h₃ : 0 <= f₃) (h₄ : 0 <= f₄) (h : forall a b, f₁ a * f₂ b 
<= f₃ (a ⊓ b…
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
An inequality of Daykin. Interestingly, any lattice in which this inequality hol
ds is
distributive.
-/
lemma Finset.le_card_infs_mul_card_sups [DecidableEq α] (s t : Finset α) :
    #s * #t ≤ #(s ⊼ t) * #(s ⊻ t) := by
  simpa using four_functions_theorem (1 : α → ℕ) 1 1 1 zero_le_one zero_le_one zero_le_one
    zero_le_one (fun _ _ ↦ le_rfl) s t

variable [Fintype α]

/-- Special case of the **Four Functions Theorem** when `s = t = univ`. -/
/-
**four_functions_theorem_univ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：four_functions_theorem_univ (h₁ : 0 <= f₁) (h₂ : 0 <= f₂) (h₃ : 0 <= f₃) (
h₄ : 0 <= f₄) (h : forall a b, f₁ a * f₂ b <= f₃ (a ⊓ b) * f₄ (a ⊔ b)) : (∑ a, f
₁ a) * ∑ a, f₂ a <= (∑ a, f₃ a) * ∑ a, f₄ a
参数：h₁ : 0 <= f₁；h₂ : 0 <= f₂；h₃ : 0 <= f₃；h₄ : 0 <= f₄；h : forall a b, f₁ a * f₂
 b <= f₃ (a ⊓ b) * f₄ (a ⊔ b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_infs_univ`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 :
 SemilatticeInf α] [inst_2 : Fintype α],   Finset.univ ⊼ Finset.univ = Finset.un
iv
· 使用定理 `Finset.univ_sups_univ`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 :
 SemilatticeSup α] [inst_2 : Fintype α],   Finset.univ ⊻ Finset.univ = Finset.un
iv
· 使用引理 `four_functions_theorem`：four_functions_theorem [DecidableEq α] (h₁ : 0 <
= f₁) (h₂ : 0 <= f₂) (h₃ : 0 <= f₃) (h₄ : 0 <= f₄) (h : forall a b, f₁ a * f₂ b 
<= f₃ (a ⊓ b…

--- 原说明 ---
Special case of the **Four Functions Theorem** when `s = t = univ`.
-/
lemma four_functions_theorem_univ (h₁ : 0 ≤ f₁) (h₂ : 0 ≤ f₂) (h₃ : 0 ≤ f₃) (h₄ : 0 ≤ f₄)
    (h : ∀ a b, f₁ a * f₂ b ≤ f₃ (a ⊓ b) * f₄ (a ⊔ b)) :
    (∑ a, f₁ a) * ∑ a, f₂ a ≤ (∑ a, f₃ a) * ∑ a, f₄ a := by
  classical simpa using four_functions_theorem f₁ f₂ f₃ f₄ h₁ h₂ h₃ h₄ h univ univ

/-- The **Holley Inequality**. -/
/-
**holley** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：holley (hμ₀ : 0 <= μ) (hf : 0 <= f) (hg : 0 <= g) (hμ : Monotone μ) (hfg :
 ∑ a, f a = ∑ a, g a) (h : forall a b, f a * g b <= f (a ⊓ b) * g (a ⊔ b)) : ∑ a
, μ a * f a <= ∑ a, μ a * g a
参数：hμ₀ : 0 <= μ；hf : 0 <= f；hg : 0 <= g；hμ : Monotone μ；hfg : ∑ a, f a = ∑ a, g 
a；h : forall a b, f a * g b <= f (a ⊓ b) * g (a ⊔ b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fintype.sum_eq_zero_iff_of_nonneg`：∀ {ι : Type u_9} {M : Type u_10} [ins
t : Fintype ι] [inst_1 : AddCommMonoid M] [inst_2 : PartialOrder M] [AddLeftMono
 M]   {f : ι → M}, 0 ≤ …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `four_functions_theorem`：four_functions_theorem [DecidableEq α] (h₁ : 0 <
= f₁) (h₂ : 0 <= f₂) (h₃ : 0 <= f₃) (h₄ : 0 <= f₄) (h : forall a b, f₁ a * f₂ b 
<= f₃ (a ⊓ b…
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `Finset.univ_infs_univ`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 :
 SemilatticeInf α] [inst_2 : Fintype α],   Finset.univ ⊼ Finset.univ = Finset.un
iv
· 使用定理 `Finset.univ_sups_univ`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 :
 SemilatticeSup α] [inst_2 : Fintype α],   Finset.univ ⊻ Finset.univ = Finset.un
iv
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Fintype.sum_pos`：∀ {ι : Type u_1} {M : Type u_4} [inst : Fintype ι] [ins
t_1 : AddCommMonoid M] [inst_2 : PartialOrder M]   [IsOrderedCancelAddMonoid M] 
{f : …
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R

--- 原说明 ---
The **Holley Inequality**.
-/
lemma holley (hμ₀ : 0 ≤ μ) (hf : 0 ≤ f) (hg : 0 ≤ g) (hμ : Monotone μ)
    (hfg : ∑ a, f a = ∑ a, g a) (h : ∀ a b, f a * g b ≤ f (a ⊓ b) * g (a ⊔ b)) :
    ∑ a, μ a * f a ≤ ∑ a, μ a * g a := by
  classical
  obtain rfl | hf := hf.eq_or_lt
  · simp only [Pi.zero_apply, sum_const_zero, eq_comm, Fintype.sum_eq_zero_iff_of_nonneg hg] at hfg
    simp [hfg]
  obtain rfl | hg := hg.eq_or_lt
  · simp only [Pi.zero_apply, sum_const_zero, Fintype.sum_eq_zero_iff_of_nonneg hf.le] at hfg
    simp [hfg]
  have := four_functions_theorem g (μ * f) f (μ * g) hg.le (mul_nonneg hμ₀ hf.le) hf.le
    (mul_nonneg hμ₀ hg.le) (fun a b ↦ ?_) univ univ
  · simpa [hfg, sum_pos hg] using this
  · simp_rw [Pi.mul_apply, mul_left_comm _ (μ _), mul_comm (g _)]
    rw [sup_comm, inf_comm]
    exact mul_le_mul (hμ le_sup_left) (h _ _) (mul_nonneg (hf.le _) <| hg.le _) <| hμ₀ _

/-- The **Fortuin-Kasteleyn-Ginibre Inequality**. -/
/-
**fkg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：fkg (hμ₀ : 0 <= μ) (hf₀ : 0 <= f) (hg₀ : 0 <= g) (hf : Monotone f) (hg : M
onotone g) (hμ : forall a b, μ a * μ b <= μ (a ⊓ b) * μ (a ⊔ b)) : (∑ a, μ a * f
 a) * ∑ a, μ a * g a <= (∑ a, μ a) * ∑ a, μ a * (f a * g a)
参数：hμ₀ : 0 <= μ；hf₀ : 0 <= f；hg₀ : 0 <= g；hf : Monotone f；hg : Monotone g；hμ : f
orall a b, μ a * μ b <= μ (a ⊓ b) * μ (a ⊔ b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `four_functions_theorem_univ`：four_functions_theorem_univ (h₁ : 0 <= f₁) 
(h₂ : 0 <= f₂) (h₃ : 0 <= f₃) (h₄ : 0 <= f₄) (h : forall a b, f₁ a * f₂ b <= f₃ 
(a ⊓ b) * f₄ (a ⊔…
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b

--- 原说明 ---
The **Fortuin-Kasteleyn-Ginibre Inequality**.
-/
lemma fkg (hμ₀ : 0 ≤ μ) (hf₀ : 0 ≤ f) (hg₀ : 0 ≤ g) (hf : Monotone f) (hg : Monotone g)
    (hμ : ∀ a b, μ a * μ b ≤ μ (a ⊓ b) * μ (a ⊔ b)) :
    (∑ a, μ a * f a) * ∑ a, μ a * g a ≤ (∑ a, μ a) * ∑ a, μ a * (f a * g a) := by
  refine four_functions_theorem_univ (μ * f) (μ * g) μ _ (mul_nonneg hμ₀ hf₀) (mul_nonneg hμ₀ hg₀)
    hμ₀ (mul_nonneg hμ₀ <| mul_nonneg hf₀ hg₀) (fun a b ↦ ?_)
  dsimp
  rw [mul_mul_mul_comm, ← mul_assoc (μ (a ⊓ b))]
  exact mul_le_mul (hμ _ _) (mul_le_mul (hf le_sup_left) (hg le_sup_right) (hg₀ _) <| hf₀ _)
    (mul_nonneg (hf₀ _) <| hg₀ _) <| mul_nonneg (hμ₀ _) <| hμ₀ _

end DistribLattice

open Booleanisation

variable [DecidableEq α] [GeneralizedBooleanAlgebra α]

/-- A slight generalisation of the **Marica-Schönheim Inequality**. -/
/-
**Finset.le_card_diffs_mul_card_diffs** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Finset.le_card_diffs_mul_card_diffs (s t : Finset α) : #s * #t <= #(s \\ t
) * #(t \\ s)
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Booleanisation.liftLatticeHom_injective`：liftLatticeHom_injective : Inje
ctive (liftLatticeHom (α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用定理 `Finset.image_image₂_distrib`：image_image₂_distrib {g : γ -> δ} {f' : α' 
-> β' -> δ} {g₁ : α -> α'} {g₂ : β -> β'} (h_distrib : forall a b, g (f a b) = f
' (g₁ a) (g₂ b)) …
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.card_compls`：∀ {α : Type u_2} [inst : BooleanAlgebra α] (s : Fins
et α), s.compls.card = s.card
· 使用定理 `Finset.infs_compls_eq_diffs`：∀ {α : Type u_2} [inst : BooleanAlgebra α] 
[inst_1 : DecidableEq α] (s t : Finset α), s ⊼ t.compls = s.diffs t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.compls_sups`：∀ {α : Type u_2} [inst : BooleanAlgebra α] [inst_1 :
 DecidableEq α] (s t : Finset α),   (s ⊻ t).compls = s.compls ⊼ t.compls
· 使用定理 `Finset.compls_compls`：∀ {α : Type u_2} [inst : BooleanAlgebra α] (s : Fi
nset α), s.compls.compls = s
· 使用定理 `Finset.compls_infs_eq_diffs`：∀ {α : Type u_2} [inst : BooleanAlgebra α] 
[inst_1 : DecidableEq α] (s t : Finset α), s.compls ⊼ t = t.diffs s
· 使用引理 `Finset.le_card_infs_mul_card_sups`：Finset.le_card_infs_mul_card_sups [De
cidableEq α] (s t : Finset α) : #s * #t <= #(s ⊼ t) * #(s ⊻ t)

--- 原说明 ---
A slight generalisation of the **Marica-Schönheim Inequality**.
-/
lemma Finset.le_card_diffs_mul_card_diffs (s t : Finset α) :
    #s * #t ≤ #(s \\ t) * #(t \\ s) := by
  have : ∀ s t : Finset α, (s \\ t).map ⟨_, liftLatticeHom_injective⟩ =
      s.map ⟨_, liftLatticeHom_injective⟩ \\ t.map ⟨_, liftLatticeHom_injective⟩ := by
    rintro s t
    simp_rw [map_eq_image]
    exact image_image₂_distrib fun a b ↦ rfl
  simpa [← card_compls (_ ⊻ _), ← map_sup, ← map_inf, ← this] using
    (s.map ⟨_, liftLatticeHom_injective⟩).le_card_infs_mul_card_sups
      (t.map ⟨_, liftLatticeHom_injective⟩)ᶜˢ

/-- The **Marica-Schönheim Inequality**. -/
/-
**Finset.card_le_card_diffs** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Finset.card_le_card_diffs (s : Finset α) : #s <= #(s \\ s)
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_pow_le_pow_left₀`：le_of_pow_le_pow_left₀ (hn : n != 0) (hb : 0 <= 
b) (h : a ^ n <= b ^ n) : a <= b
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.le_card_diffs_mul_card_diffs`：Finset.le_card_diffs_mul_card_diffs
 (s t : Finset α) : #s * #t <= #(s \\ t) * #(t \\ s)

--- 原说明 ---
The **Marica-Schönheim Inequality**.
-/
lemma Finset.card_le_card_diffs (s : Finset α) : #s ≤ #(s \\ s) :=
  le_of_pow_le_pow_left₀ two_ne_zero zero_le <| by
    simpa [← sq] using s.le_card_diffs_mul_card_diffs s
