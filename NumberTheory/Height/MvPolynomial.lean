/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Polynomial.Homogenize
public import Mathlib.NumberTheory.Height.Basic

import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Data.Fintype.Order
import all Mathlib.NumberTheory.Height.Basic

/-!
# Height bounds for linear and polynomial maps

We prove an upper bound for the height of the image of a tuple under a linear map.

We also prove upper and lower bounds for the height of `fun i ↦ eval P i x`, where `P` is a family
of homogeneous polynomials over the field `K` of the same degree `N` and `x : ι → K`
with `ι` finite.
-/

public section

section aux

/-
**Height.iSup_fun_eq_max** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma Height.iSup_fun_eq_max (f : Fin 2 → ℝ) : iSup f = max (f 0) (f 1) := by
  rw [show f = ![f 0, f 1] from List.ofFn_inj.mp rfl]
  exact (max_eq_iSup ..).symm

namespace IsNonarchimedean

variable {R α β F : Type*} [CommRing R] [AddCommMonoid β] [FunLike F β ℝ] [NonnegHomClass F β ℝ]
    [ZeroHomClass F β ℝ] {v : F} {l : α → β}

-- NOTE: The following cannot be moved to Mathlib.Algebra.Order.Ring.IsNonarchimedean,
--       because it needs the target to be the reals (to have the default value zero
--       for empty iSups), which are not known there.
/-- The ultrametric triangle inequality for finite sums. -/
/-
**IsNonarchimedean.apply_sum_le** 是 Mathlib 中的一个引理，位于命名空间 `IsNonarchimedean`。
形式化陈述：apply_sum_le (hv : IsNonarchimedean v) {s : Finset α} : v (∑ i in s, l i) 
<= ⨆ i : s, v (l i)
参数：hv : IsNonarchimedean v。
该定理/引理给出了一组等式。
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
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `Real.iSup_of_isEmpty`：∀ {ι : Sort u_1} [IsEmpty ι] (f : ι → ℝ), ⨆ i, f i
 = 0
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用引理 `Finite.le_ciSup_of_le`：le_ciSup_of_le {a : α} {f : ι -> α} (c : ι) (h : 
a <= f c) : a <= iSup f
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Real.iSup_nonneg_of_nonnegHomClass`：iSup_nonneg_of_nonnegHomClass {ι F α
 : Type*} [FunLike F α Real] [NonnegHomClass F α Real] (f : F) (g : ι -> α) : 0 
<= ⨆ i, f (g i)
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x

--- 原说明 ---
The ultrametric triangle inequality for finite sums.
-/
lemma apply_sum_le (hv : IsNonarchimedean v) {s : Finset α} :
    v (∑ i ∈ s, l i) ≤ ⨆ i : s, v (l i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    grw [hv .., ih]
    refine max_le ?_ ?_
    · exact Finite.le_ciSup_of_le ⟨_, s.mem_insert_self a⟩ le_rfl
    · rcases isEmpty_or_nonempty s with hs | hs
      · simpa using Real.iSup_nonneg_of_nonnegHomClass v _
      exact ciSup_le fun i ↦ Finite.le_ciSup_of_le (⟨i.val, Finset.mem_insert_of_mem i.prop⟩) le_rfl

/-- The ultrametric triangle inequality for finite sums. -/
/-
**IsNonarchimedean.apply_sum_univ_le** 是 Mathlib 中的一个引理，位于命名空间 `IsNonarchimedean
`。
形式化陈述：apply_sum_univ_le [Fintype α] (hv : IsNonarchimedean v) : v (∑ i, l i) <= 
⨆ i, v (l i)
参数：hv : IsNonarchimedean v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用引理 `IsNonarchimedean.apply_sum_le`：apply_sum_le (hv : IsNonarchimedean v) {s
 : Finset α} : v (∑ i in s, l i) <= ⨆ i : s, v (l i)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `cbiSup_eq_of_forall`：cbiSup_eq_of_forall {p : ι -> Prop} {f : Subtype p 
-> α} (hp : forall i, p i) : ⨆ (i) (h : p i), f ⟨i, h⟩ = iSup f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `ciSup_unique`：ciSup_unique [Unique ι] {s : ι -> α} : ⨆ i, s i = s defaul
t

--- 原说明 ---
The ultrametric triangle inequality for finite sums.
-/
lemma apply_sum_univ_le [Fintype α] (hv : IsNonarchimedean v) :
    v (∑ i, l i) ≤ ⨆ i, v (l i) := by
  grw [hv.apply_sum_le, ← cbiSup_eq_of_forall (by grind)]
  simp

end IsNonarchimedean

end aux

/-!
### Upper bound for the height of the image under a linear map
-/

variable {K : Type*} [Field K] {ι ι' : Type*} [Fintype ι] [Finite ι']

-- The "local" version of the bound for (archimedean) absolute values.
/-
**AbsoluteValue.iSup_abv_linearMap_apply_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AbsoluteValue.iSup_abv_linearMap_apply_le (v : AbsoluteValue K Real) (A : 
ι' × ι -> K) (x : ι -> K) : ⨆ j, v (∑ i, A (j, i) * x i) <= Nat.card ι * (⨆ ji, 
v (A ji)) * ⨆ i, v (x i)
参数：v : AbsoluteValue K Real；A : ι' × ι -> K；x : ι -> K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.iSup_of_isEmpty`：∀ {ι : Sort u_1} [IsEmpty ι] (f : ι → ℝ), ⨆ i, f i
 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用引理 `AbsoluteValue.sum_le`：AbsoluteValue.sum_le [Semiring R] [Semiring S] [Pa
rtialOrder S] [IsOrderedRing S] (abv : AbsoluteValue R S) (s : Finset ι) (f : ι 
-> R) : ab…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用引理 `Finite.le_ciSup_of_le`：le_ciSup_of_le {a : α} {f : ι -> α} (c : ι) (h : 
a <= f c) : a <= iSup f
· 使用定理 `Finite.instProd`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], 
Finite (α × β)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用引理 `Real.iSup_nonneg_of_nonnegHomClass`：iSup_nonneg_of_nonnegHomClass {ι F α
 : Type*} [FunLike F α Real] [NonnegHomClass F α Real] (f : F) (g : ι -> α) : 0 
<= ⨆ i, f (g i)
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
（共 31 条，此处仅展示前 30 条）
-/
lemma AbsoluteValue.iSup_abv_linearMap_apply_le (v : AbsoluteValue K ℝ) (A : ι' × ι → K)
    (x : ι → K) :
    ⨆ j, v (∑ i, A (j, i) * x i) ≤ Nat.card ι * (⨆ ji, v (A ji)) * ⨆ i, v (x i) := by
  rcases isEmpty_or_nonempty ι'
  · simp
  refine ciSup_le fun j ↦ ?_
  grw [v.sum_le]
  simp only [map_mul]
  grw [Finset.sum_le_sum (g := fun _ ↦ (⨆ ji, v (A ji)) * ⨆ i, v (x i)) fun i _ ↦ ?h]
  case h =>
    gcongr
    · exact Real.iSup_nonneg_of_nonnegHomClass v _
    · exact Finite.le_ciSup_of_le (j, i) le_rfl
    · exact Finite.le_ciSup_of_le i le_rfl
  rw [Finset.sum_const, nsmul_eq_mul, mul_assoc, Finset.card_univ, Nat.card_eq_fintype_card]

-- The "local" version of the bound for nonarchimedean absolute values.
/-
**IsNonarchimedean.iSup_abv_linearMap_apply_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsNonarchimedean.iSup_abv_linearMap_apply_le {v : AbsoluteValue K Real} (h
v : IsNonarchimedean v) (A : ι' × ι -> K) (x : ι -> K) : ⨆ j, v (∑ i, A (j, i) *
 x i) <= (⨆ ji, v (A ji)) * ⨆ i, v (x i)
参数：hv : IsNonarchimedean v；A : ι' × ι -> K；x : ι -> K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `AbsoluteValue.map_zero`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring
 R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S),
 abv 0 = 0
· 使用定理 `Real.iSup_const_zero`：iSup_const_zero : ⨆ _ : ι, (0 : Real) = 0
· 使用定理 `Real.iSup_of_isEmpty`：∀ {ι : Sort u_1} [IsEmpty ι] (f : ι → ℝ), ⨆ i, f i
 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用引理 `IsNonarchimedean.apply_sum_le`：apply_sum_le (hv : IsNonarchimedean v) {s
 : Finset α} : v (∑ i in s, l i) <= ⨆ i : s, v (l i)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `Function.Surjective.iSup_comp`：Function.Surjective.iSup_comp {f : ι -> ι
'} (hf : Surjective f) (g : ι' -> α) : ⨆ x, g (f x) = ⨆ y, g y
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用引理 `Finite.le_ciSup_of_le`：le_ciSup_of_le {a : α} {f : ι -> α} (c : ι) (h : 
a <= f c) : a <= iSup f
· 使用定理 `Finite.instProd`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], 
Finite (α × β)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用引理 `Real.iSup_nonneg_of_nonnegHomClass`：iSup_nonneg_of_nonnegHomClass {ι F α
 : Type*} [FunLike F α Real] [NonnegHomClass F α Real] (f : F) (g : ι -> α) : 0 
<= ⨆ i, f (g i)
-/
lemma IsNonarchimedean.iSup_abv_linearMap_apply_le {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v)
    (A : ι' × ι → K) (x : ι → K) :
    ⨆ j, v (∑ i, A (j, i) * x i) ≤ (⨆ ji, v (A ji)) * ⨆ i, v (x i) := by
  rcases isEmpty_or_nonempty ι
  · simp
  rcases isEmpty_or_nonempty ι'
  · simp
  refine ciSup_le fun j ↦ ?_
  grw [hv.apply_sum_le]
  simp only [map_mul]
  have (f : ι → ℝ) : ⨆ i : ↥Finset.univ, f i.val = ⨆ i, f i :=
    Function.Surjective.iSup_comp (fun i ↦ ⟨⟨i, Finset.mem_univ i⟩, rfl⟩) f
  rw [this fun i ↦ v (A (j, i)) * v (x i)]
  refine ciSup_le fun i ↦ ?_
  gcongr
  · exact Real.iSup_nonneg_of_nonnegHomClass v _
  · exact Finite.le_ciSup_of_le (j, i) le_rfl
  · exact Finite.le_ciSup_of_le i le_rfl

namespace Height

variable [AdmissibleAbsValues K]

open AdmissibleAbsValues

open Multiset in
/-- Let `A : ι' × ι → K`, which we can interpret as a linear map from `ι → K` to `ι' → K`.
Let `x : ι → K` be a tuple. Then the multiplicative height of `A x` is bounded by
`#ι ^ totalWeight K * mulHeight A * mulHeight x` (if `ι` is nonempty).

Note: We use the uncurried form of `A` so that we can write `mulHeight A`. -/
/-
**Height.mulHeight_linearMap_apply_le** 是 Mathlib 中的一个定理，位于命名空间 `Height`。
形式化陈述：mulHeight_linearMap_apply_le [Nonempty ι] (A : ι' × ι -> K) (x : ι -> K) :
 mulHeight (fun j => ∑ i, A (j, i) * x i) <= Nat.card ι ^ totalWeight K * mulHei
ght A * mulHeight x
参数：A : ι' × ι -> K；x : ι -> K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.one_le_pow`：∀ (n m : ℕ), 0 < m → 1 ≤ m ^ n
· 使用定理 `Nat.card_pos`：∀ {α : Type u_1} [Nonempty α] [Finite α], 0 < Nat.card α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `Height.one_le_mulHeight`：one_le_mulHeight (x : ι -> K) : 1 <= mulHeight 
x
· 使用定理 `Finite.instProd`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], 
Finite (α × β)
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
（共 69 条，此处仅展示前 30 条）

--- 原说明 ---
Let `A : ι' × ι → K`, which we can interpret as a linear map from `ι → K` to `ι'
 → K`.
Let `x : ι → K` be a tuple. Then the multiplicative height of `A x` is bounded b
y
`#ι ^ totalWeight K * mulHeight A * mulHeight x` (if `ι` is nonempty).

Note: We use the uncurried form of `A` so that we can write `mulHeight A`.
-/
theorem mulHeight_linearMap_apply_le [Nonempty ι] (A : ι' × ι → K) (x : ι → K) :
    mulHeight (fun j ↦ ∑ i, A (j, i) * x i) ≤
      Nat.card ι ^ totalWeight K * mulHeight A * mulHeight x := by
  have H₀ : 1 ≤ Nat.card ι ^ totalWeight K * mulHeight A * mulHeight x := by
    rw [show (1 : ℝ) = 1 * 1 * 1 by ring]
    gcongr
    · exact_mod_cast Nat.one_le_pow _ _ Nat.card_pos
    · exact one_le_mulHeight _
    · exact one_le_mulHeight _
  rcases isEmpty_or_nonempty ι' with hι' | hι'
  · simpa only [mulHeight_eq_one_of_subsingleton, mul_one] using H₀
  rcases eq_or_ne (fun j ↦ ∑ i, A (j, i) * x i) 0 with h | h
  · simpa only [h, mulHeight_zero] using H₀
  rcases eq_or_ne A 0 with rfl | hA
  · simpa using H₀
  rcases eq_or_ne x 0 with rfl | hx
  · simpa using H₀
  rw [mulHeight_eq h, mulHeight_eq hA, mulHeight_eq hx, mul_mul_mul_comm, ← mul_assoc, ← mul_assoc,
    mul_assoc (_ * _ * _)]
  gcongr
  · exact finprod_nonneg fun v ↦ Real.iSup_nonneg_of_nonnegHomClass v.val _
  · refine mul_nonneg (mul_nonneg (by simp) ?_) ?_ <;>
      exact prod_map_nonneg fun v _ ↦ Real.iSup_nonneg_of_nonnegHomClass v _
  · -- archimedean part: reduce to "local" statement `linearMap_apply_bound`
    rw [mul_assoc, ← prod_map_mul, ← prod_replicate, totalWeight, ← map_const', ← prod_map_mul]
    refine prod_map_le_prod_map₀ _ _ (fun v _ ↦ Real.iSup_nonneg_of_nonnegHomClass v _) fun v _ ↦ ?_
    rw [mul_comm (iSup _), ← mul_assoc]
    exact v.iSup_abv_linearMap_apply_le A x
  · -- nonarchimedean part: reduce to "local" statement `linearMap_apply_bound_of_isNonarchimedean`
    rw [← finprod_mul_distrib (by fun_prop) (by fun_prop)]
    refine finprod_le_finprod (by fun_prop)
      (fun v ↦ Real.iSup_nonneg_of_nonnegHomClass v.val _) (by fun_prop) fun v ↦ ?_
    exact (isNonarchimedean _ v.prop).iSup_abv_linearMap_apply_le A x

open Real in
/-- Let `A : ι' × ι → K`, which we can interpret as a linear map from `ι → K` to `ι' → K`.
Let `x : ι → K` be a tuple. Then the logarithmic height of `A x` is bounded by
`totalWeight K * log #ι + logHeight A + logHeight x`.

(Note that here we do not need to assume that `ι` is nonempty, due to the convenient
junk value `log 0 = 0`.) -/
/-
**Height.logHeight_linearMap_apply_le** 是 Mathlib 中的一个定理，位于命名空间 `Height`。
形式化陈述：logHeight_linearMap_apply_le (A : ι' × ι -> K) (x : ι -> K) : logHeight (f
un j => ∑ i, A (j, i) * x i) <= totalWeight K * log (Nat.card ι) + logHeight A +
 logHeight x
参数：A : ι' × ι -> K；x : ι -> K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `Height.logHeight_nonneg`：logHeight_nonneg (x : ι -> K) : 0 <= logHeight 
x
· 使用定理 `Finite.instProd`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], 
Finite (α × β)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `Height.fun_logHeight_zero`：∀ {K : Type u_1} [inst : Field K] [inst_1 : H
eight.AdmissibleAbsValues K] {ι : Type u_2},   (Height.logHeight fun x => 0) = 0
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_eq_zero`：∀ {α : Type u_1} [inst : Fintype α] [IsEmpty α], F
intype.card α = 0
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `Height.logHeight_eq_zero_of_subsingleton`：logHeight_eq_zero_of_subsingle
ton {ι : Type*} [Subsingleton ι] (x : ι -> K) : logHeight x = 0
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `Height.mulHeight_pos`：mulHeight_pos (x : ι -> K) : 0 < mulHeight x
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
Let `A : ι' × ι → K`, which we can interpret as a linear map from `ι → K` to `ι'
 → K`.
Let `x : ι → K` be a tuple. Then the logarithmic height of `A x` is bounded by
`totalWeight K * log #ι + logHeight A + logHeight x`.

(Note that here we do not need to assume that `ι` is nonempty, due to the conven
ient
junk value `log 0 = 0`.)
-/
theorem logHeight_linearMap_apply_le (A : ι' × ι → K) (x : ι → K) :
    logHeight (fun j ↦ ∑ i, A (j, i) * x i) ≤
      totalWeight K * log (Nat.card ι) + logHeight A + logHeight x := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · suffices 0 ≤ logHeight A + logHeight x by simp
    positivity
  simp only [logHeight_eq_log_mulHeight]
  have : (Nat.card ι : ℝ) ^ totalWeight K ≠ 0 := by simp
  pull (disch := first | assumption | positivity) log
  exact (log_le_log <| by positivity) <| mulHeight_linearMap_apply_le ..

end Height

/-!
### Upper bound for the height of the image under a polynomial map

If `p : ι' → MvPolynomial ι K` is a family of homogeneous polynomials of the same degree `N`
and `x : ι → K`, then the multiplicative height of `fun j ↦ (p j).eval x` is bounded above by
an (explicit) constant depending only on `p` times the `N`th power of the multiplicative
height of `x`. A similar statement holds for the logarithmic height.
-/

open MvPolynomial

variable {K : Type*} [Field K] {ι : Type*}

-- The "local" version of the height bound for (archimedean) absolute values.
/-
**AbsoluteValue.eval_mvPolynomial_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AbsoluteValue.eval_mvPolynomial_le [Finite ι] (v : AbsoluteValue K Real) {
p : MvPolynomial ι K} {N : Nat} (hp : p.IsHomogeneous N) (x : ι -> K) : v (p.eva
l x) <= (AddMonoidAlgebra.coeff p).sum (fun _ c => v c) * (⨆ i, v (x i)) ^ N
参数：v : AbsoluteValue K Real；hp : p.IsHomogeneous N；x : ι -> K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.eval_eq`：eval_eq (X : σ -> R) (f : MvPolynomial σ R) : eval
 X f = ∑ d in f.support, f.coeff d * ∏ i in d.support, X i ^ d i
· 使用定理 `MvPolynomial.sum_def`：sum_def {A} [AddCommMonoid A] {p : MvPolynomial σ 
R} {b : (σ ->₀ Nat) -> R -> A} : (AddMonoidAlgebra.coeff p).sum b = ∑ m in p.sup
port, b m …
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用引理 `AbsoluteValue.sum_le`：AbsoluteValue.sum_le [Semiring R] [Semiring S] [Pa
rtialOrder S] [IsOrderedRing S] (abv : AbsoluteValue R S) (s : Finset ι) (f : ι 
-> R) : ab…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `AbsoluteValue.map_mul`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring 
R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) (
x y : R), a…
· 使用定理 `AbsoluteValue.map_prod`：∀ {ι : Type u_1} {R : Type u_2} {S : Type u_3} [
inst : CommSemiring R] [Nontrivial R] [inst_2 : CommRing S]   [inst_3 : LinearOr
der S] [IsSt…
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `AbsoluteValue.map_pow`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring 
R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) [
IsDomain S]…
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用引理 `MvPolynomial.IsHomogeneous.degree_eq_sum_deg_support`：degree_eq_sum_deg_
support (hφ : φ.IsHomogeneous n) {s : σ ->₀ Nat} (hs : s in φ.support) : n = ∑ i
 in s.support, s i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.prod_pow_eq_pow_sum`：prod_pow_eq_pow_sum (s : Finset ι) (f : ι ->
 Nat) (a : M) : ∏ i in s, a ^ f i = a ^ ∑ i in s, f i
· 使用引理 `Finset.prod_le_prod`：prod_le_prod (h0 : forall i in s, 0 <= f i) (h1 : f
orall i in s, f i <= g i) : ∏ i in s, f i <= ∏ i in s, g i
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `pow_le_pow_left₀`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 :
 Preorder M₀] {a b : M₀} [PosMulMono M₀] [MulPosMono M₀],   0 ≤ a → a ≤ b → ∀ (n
 : ℕ),…
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用引理 `Finite.le_ciSup`：le_ciSup (f : ι -> α) (i : ι) : f i <= ⨆ j, f j
-/
lemma AbsoluteValue.eval_mvPolynomial_le [Finite ι] (v : AbsoluteValue K ℝ)
    {p : MvPolynomial ι K} {N : ℕ} (hp : p.IsHomogeneous N) (x : ι → K) :
    v (p.eval x) ≤ (AddMonoidAlgebra.coeff p).sum (fun _ c ↦ v c) * (⨆ i, v (x i)) ^ N := by
  rw [eval_eq, sum_def, Finset.sum_mul]
  grw [AbsoluteValue.sum_le]
  simp_rw [v.map_mul, v.map_prod, v.map_pow]
  refine Finset.sum_le_sum fun s hs ↦ ?_
  gcongr
  rw [hp.degree_eq_sum_deg_support hs, ← Finset.prod_pow_eq_pow_sum]
  gcongr with i
  exact Finite.le_ciSup (fun j ↦ v (x j)) i

-- The "local" version of the height bound for nonarchimedean absolute values.
/-
**IsNonarchimedean.eval_mvPolynomial_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsNonarchimedean.eval_mvPolynomial_le [Finite ι] {v : AbsoluteValue K Real
} (hv : IsNonarchimedean v) {p : MvPolynomial ι K} {N : Nat} (hp : p.IsHomogeneo
us N) (x : ι -> K) : v (p.eval x) <= (⨆ s : p.support, v (coeff s p)) * (⨆ i, v 
(x i)) ^ N
参数：hv : IsNonarchimedean v；hp : p.IsHomogeneous N；x : ι -> K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AbsoluteValue.map_zero`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring
 R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S),
 abv 0 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.iSup_of_isEmpty`：∀ {ι : Sort u_1} [IsEmpty ι] (f : ι → ℝ), ⨆ i, f i
 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.eval_eq`：eval_eq (X : σ -> R) (f : MvPolynomial σ R) : eval
 X f = ∑ d in f.support, f.coeff d * ∏ i in d.support, X i ^ d i
· 使用定理 `IsNonarchimedean.finset_image_add_of_nonempty`：finset_image_add_of_nonem
pty {α β : Type*} [AddCommMonoid α] {f : α -> R} (hna : IsNonarchimedean f) (g :
 β -> α) {t : Finset β} (ht : t.Non…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `MvPolynomial.support_nonempty`：support_nonempty {p : MvPolynomial σ R} :
 p.support.Nonempty ↔ p != 0
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `AbsoluteValue.map_mul`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring 
R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) (
x y : R), a…
· 使用定理 `AbsoluteValue.map_prod`：∀ {ι : Type u_1} {R : Type u_2} {S : Type u_3} [
inst : CommSemiring R] [Nontrivial R] [inst_2 : CommRing S]   [inst_3 : LinearOr
der S] [IsSt…
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `AbsoluteValue.map_pow`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring 
R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) [
IsDomain S]…
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用引理 `Finite.le_ciSup_of_le`：le_ciSup_of_le {a : α} {f : ι -> α} (c : ι) (h : 
a <= f c) : a <= iSup f
（共 42 条，此处仅展示前 30 条）
-/
lemma IsNonarchimedean.eval_mvPolynomial_le [Finite ι] {v : AbsoluteValue K ℝ}
    (hv : IsNonarchimedean v) {p : MvPolynomial ι K} {N : ℕ} (hp : p.IsHomogeneous N) (x : ι → K) :
    v (p.eval x) ≤ (⨆ s : p.support, v (coeff s p)) * (⨆ i, v (x i)) ^ N := by
  rcases eq_or_ne p 0 with rfl | hp₀
  · simp_all
  rw [eval_eq]
  obtain ⟨s, hs₁, hs₂⟩ :=
    hv.finset_image_add_of_nonempty (fun d ↦ coeff d p * ∏ i ∈ d.support, x i ^ d i)
      (support_nonempty.mpr hp₀)
  grw [hs₂]
  simp_rw [v.map_mul, v.map_prod, v.map_pow]
  gcongr
  · exact Real.iSup_nonneg_of_nonnegHomClass v _
  · exact Finite.le_ciSup_of_le (⟨s, hs₁⟩ : p.support) le_rfl
  · rw [hp.degree_eq_sum_deg_support hs₁, ← Finset.prod_pow_eq_pow_sum]
    gcongr with i
    exact Finite.le_ciSup (fun j ↦ v (x j)) i

namespace Height

variable {ι' : Type*}

variable [AdmissibleAbsValues K]

open AdmissibleAbsValues

/-- The constant in the (upper) height bound on values of `p`. -/
@[expose] noncomputable
/-
**Height.mulHeightBound** 是 Mathlib 中的一个定义，位于命名空间 `Height`。
形式化陈述：mulHeightBound (p : ι' -> MvPolynomial ι K) : Real
参数：p : ι' -> MvPolynomial ι K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant in the (upper) height bound on values of `p`.
-/
def mulHeightBound (p : ι' → MvPolynomial ι K) : ℝ :=
  (archAbsVal.map fun v ↦ ⨆ j, (AddMonoidAlgebra.coeff <| p j).sum (fun _ c ↦ v c)).prod *
    ∏ᶠ v : nonarchAbsVal, ⨆ j, max (⨆ s : (p j).support, v.val (coeff s (p j))) 1
/-
**Height.mulHeightBound_eq** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：mulHeightBound_eq (p : ι' -> MvPolynomial ι K) : mulHeightBound p = (archA
bsVal.map fun v => ⨆ j, (AddMonoidAlgebra.coeff <| p j).sum (fun _ c => v c)).pr
od * ∏ᶠ v : nonarchAbsVal, ⨆ j, max (⨆ s : (p j).support, v.val (coeff s (p j)))
 1
参数：p : ι' -> MvPolynomial ι K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mulHeightBound_eq (p : ι' → MvPolynomial ι K) :
    mulHeightBound p =
     (archAbsVal.map fun v ↦ ⨆ j, (AddMonoidAlgebra.coeff <| p j).sum (fun _ c ↦ v c)).prod *
        ∏ᶠ v : nonarchAbsVal, ⨆ j, max (⨆ s : (p j).support, v.val (coeff s (p j))) 1 :=
  rfl

variable (K ι ι') in
/-
**Height.max_mulHeightBound_zero_one_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：max_mulHeightBound_zero_one_eq_one : max (mulHeightBound (0 : ι' -> MvPoly
nomial ι K)) 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.iSup_const_zero`：iSup_const_zero : ⨆ _ : ι, (0 : Real) = 0
· 使用定理 `Multiset.map_const'`：∀ {α : Type u_1} {β : Type v} (s : Multiset α) (b :
 β), Multiset.map (fun x => b) s = Multiset.replicate s.card b
· 使用定理 `Multiset.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n
 a).prod = a ^ n
· 使用引理 `zero_pow_eq`：zero_pow_eq (n : Nat) : (0 : M₀) ^ n = if n = 0 then 1 else
 0
· 使用定理 `AbsoluteValue.map_zero`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring
 R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S),
 abv 0 = 0
· 使用定理 `Real.iSup_of_isEmpty`：∀ {ι : Sort u_1} [IsEmpty ι] (f : ι → ℝ), ⨆ i, f i
 = 0
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `finprod_zero_le_one`：finprod_zero_le_one {M α : Type*} [CommMonoidWithZe
ro M] [PartialOrder M] [ZeroLEOneClass M] [PosMulMono M] : ∏ᶠ _ : α, (0 : M) <= 
1
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `ciSup_const`：ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a
· 使用定理 `finprod_one`：finprod_one : (∏ᶠ _ : α, (1 : M)) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma max_mulHeightBound_zero_one_eq_one :
    max (mulHeightBound (0 : ι' → MvPolynomial ι K)) 1 = 1 := by
  simp only [mulHeightBound_eq, Pi.zero_apply, support_zero, coeff_zero, AbsoluteValue.map_zero,
    Real.iSup_of_isEmpty, zero_le_one, sup_of_le_right, AddMonoidAlgebra.coeff_zero,
    Finsupp.sum_zero_index, Real.iSup_const_zero, Multiset.map_const', Multiset.prod_replicate,
    sup_eq_right, zero_pow_eq]
  rcases isEmpty_or_nonempty ι'
  · split_ifs
    · simpa using finprod_zero_le_one
    · simp
  · simp
    grind

variable [Finite ι']

open Function in
@[fun_prop]
/-
**Height.hasFiniteMulSupport_iSup_max_iSup_one** 是 Mathlib 中的一个引理，位于命名空间 `Height
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma hasFiniteMulSupport_iSup_max_iSup_one (h : Nonempty ι') (p : ι' → MvPolynomial ι K) :
    (fun v : nonarchAbsVal ↦
      ⨆ j, max (⨆ s : (p j).support, v.val (coeff s.val (p j))) 1).HasFiniteMulSupport := by
  refine HasFiniteMulSupport.iSup fun j ↦ ?_
  rcases isEmpty_or_nonempty (p j).support with hs₀ | hs₀
  · simp [hasFiniteMulSupport_one]
  have H (s : (p j).support) : coeff s.val (p j) ≠ 0 := mem_support_iff.mp s.prop
  fun_prop (disch := simp [H])

open Real Multiset Finsupp in
/-
**Height.mulHeight_constantCoeff_le_mulHeightBound** 是 Mathlib 中的一个引理，位于命名空间 `He
ight`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma mulHeight_constantCoeff_le_mulHeightBound {p : ι' → MvPolynomial ι K}
    (h : (fun j ↦ constantCoeff (p j)) ≠ 0) :
    mulHeight (fun j ↦ constantCoeff (p j)) ≤ mulHeightBound p := by
  simp only [mulHeight_eq h, mulHeightBound_eq]
  gcongr
  · exact finprod_nonneg fun v ↦ Real.iSup_nonneg_of_nonnegHomClass ..
  · exact prod_map_nonneg fun v _ ↦ iSup_nonneg fun _ ↦ sum_nonneg fun _ _ ↦ by positivity
  · have H (v : AbsoluteValue K ℝ) (j : ι') :
        v (constantCoeff (p j)) ≤ (AddMonoidAlgebra.coeff <| p j).sum fun _ c ↦ v c :=
      single_eval_le_sum _ v.map_zero (fun _ ↦ by positivity) _
    exact prod_map_le_prod_map₀ _ _ (fun v _ ↦ Real.iSup_nonneg_of_nonnegHomClass ..)
      fun v _ ↦ Finite.ciSup_mono (H v)
  · have := (Function.ne_iff.mp h).nonempty
    refine finprod_le_finprod (by fun_prop)
      (fun v ↦ Real.iSup_nonneg_of_nonnegHomClass ..) (by fun_prop) ?_
    refine fun v ↦ Finite.ciSup_mono fun j ↦ ?_
    rw [show constantCoeff (p j) = coeff 0 (p j) from rfl]
    rcases eq_or_ne (coeff 0 (p j)) 0 with h₀ | h₀
    · simp [h₀]
    · exact le_sup_of_le_left <| Finite.le_ciSup_of_le ⟨0, by simp [h₀]⟩ le_rfl

variable [Finite ι]

open Real Finsupp Multiset in
/-- Let `K` be a field with an admissible family of absolute values (giving rise
to a multiplicative height).
Let `p` be a family (indexed by `ι'`) of homogeneous polynomials in variables indexed by
the finite type `ι` and of the same degree `N`. Then for any `x : ι →  K`,
the multiplicative height of `fun j : ι' ↦ eval x (p j)` is bounded by a positive constant
(which is made explicit) times `mulHeight x ^ N`. -/
/-
**Height.mulHeight_eval_le** 是 Mathlib 中的一个定理，位于命名空间 `Height`。
形式化陈述：mulHeight_eval_le {N : Nat} {p : ι' -> MvPolynomial ι K} (hp : forall i, (
p i).IsHomogeneous N) (x : ι -> K) : mulHeight (fun j => (p j).eval x) <= max (m
ulHeightBound p) 1 * mulHeight x ^ N
参数：hp : forall i, (p i).IsHomogeneous N；x : ι -> K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.eval_zero`：eval_zero : eval (0 : σ -> R) = constantCoeff
· 使用引理 `Height.mulHeight_zero`：mulHeight_zero : mulHeight (0 : ι -> K) = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `le_max_of_le_left`：le_max_of_le_left : a <= b -> a <= max b c
· 使用定理 `_private.Mathlib.NumberTheory.Height.MvPolynomial.0.Height.mulHeight_con
stantCoeff_le_mulHeightBound`：∀ {K : Type u_4} [inst : Field K] {ι : Type u_5} {
ι' : Type u_6} [inst_1 : Height.AdmissibleAbsValues K] [Finite ι']   {p : ι' → M
vPolynomia…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用引理 `Height.mulHeight_pos`：mulHeight_pos (x : ι -> K) : 0 < mulHeight x
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `one_le_pow₀`：one_le_pow₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 <= 
a) {n : Nat} : 1 <= a ^ n
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用引理 `Height.one_le_mulHeight`：one_le_mulHeight (x : ι -> K) : 1 <= mulHeight 
x
· 使用引理 `Real.iSup_nonneg`：iSup_nonneg (hf : forall i, 0 <= f i) : 0 <= ⨆ i, f i
· 使用定理 `Finsupp.sum_nonneg'`：sum_nonneg' (h : forall i, 0 <= h₁ i (f i)) : 0 <= 
f.sum h₁
（共 66 条，此处仅展示前 30 条）

--- 原说明 ---
Let `K` be a field with an admissible family of absolute values (giving rise
to a multiplicative height).
Let `p` be a family (indexed by `ι'`) of homogeneous polynomials in variables in
dexed by
the finite type `ι` and of the same degree `N`. Then for any `x : ι →  K`,
the multiplicative height of `fun j : ι' ↦ eval x (p j)` is bounded by a positiv
e constant
(which is made explicit) times `mulHeight x ^ N`.
-/
theorem mulHeight_eval_le {N : ℕ} {p : ι' → MvPolynomial ι K} (hp : ∀ i, (p i).IsHomogeneous N)
    (x : ι → K) :
    mulHeight (fun j ↦ (p j).eval x) ≤ max (mulHeightBound p) 1 * mulHeight x ^ N := by
  rcases eq_or_ne x 0 with rfl | hx
  · rcases eq_or_ne (fun j ↦ constantCoeff (p j)) 0 with h | h
    · simp [h]
    · simpa using le_max_of_le_left <| mulHeight_constantCoeff_le_mulHeightBound h
  rcases eq_or_ne (fun j ↦ eval x (p j)) 0 with h₀ | h₀
  · grw [← le_max_right]
    simpa [h₀, mulHeight_zero] using one_le_pow₀ <| one_le_mulHeight x
  have H₀ (v : AbsoluteValue K ℝ) : 0 ≤ ⨆ j, (AddMonoidAlgebra.coeff <| p j).sum fun _ c ↦ v c :=
    iSup_nonneg (fun j ↦ sum_nonneg' <| fun s ↦ by positivity)
  -- The following four statements are used in the `gcongr`s below.
  have H₁ :
     0 ≤ (archAbsVal.map (fun v ↦ ⨆ j, (AddMonoidAlgebra.coeff <| p j).sum fun _ c ↦ v c)).prod :=
    prod_map_nonneg fun v _ ↦ H₀ v
  have H₂ : 0 ≤ (archAbsVal.map (fun v ↦ ⨆ i, v (x i))).prod :=
    prod_map_nonneg fun _ _ ↦ Real.iSup_nonneg_of_nonnegHomClass ..
  have H₃ : 0 ≤ ∏ᶠ v : nonarchAbsVal, ⨆ i, v.val ((eval x) (p i)) :=
    finprod_nonneg fun _ ↦ Real.iSup_nonneg_of_nonnegHomClass ..
  have H₄ : 0 ≤ ∏ᶠ v : nonarchAbsVal, ⨆ i, v.val (x i) :=
    finprod_nonneg fun _ ↦ Real.iSup_nonneg_of_nonnegHomClass ..
  -- The following two statements are helpful for discharging the goals left by `gcongr`.
  have HH₁ (v : AbsoluteValue K ℝ) : 0 ≤ (⨆ i, v (x i)) ^ N :=
    pow_nonneg (Real.iSup_nonneg_of_nonnegHomClass v _) N
  have HH₂ (f : ι' → ℝ) (j : ι') : f j ≤ ⨆ j, f j := Finite.le_ciSup ..
  simp only [mulHeight_eq hx, mulHeight_eq h₀, mulHeightBound_eq]
  grw [← le_max_left]
  rw [mul_pow, mul_mul_mul_comm]
  gcongr
  · -- archimedean part: reduce to "local" statement `eval_mvPolynomial_le`
    rw [← prod_map_pow, ← prod_map_mul]
    refine prod_map_le_prod_map₀ _ _ (fun _ _ ↦ Real.iSup_nonneg_of_nonnegHomClass ..)
      fun v _ ↦ Real.iSup_le (fun j ↦ ?_) <| mul_nonneg (H₀ v) (HH₁ v)
    grw [v.eval_mvPolynomial_le (hp j) x]
    gcongr
    · exact HH₁ v
    · exact HH₂ (fun j ↦ (AddMonoidAlgebra.coeff <| p j).sum fun _ c ↦ v c) j
  · -- nonarchimedean part: reduce to "local" statement `eval_mvPolynomial_le`
    have := (Function.ne_iff.mp h₀).nonempty
    have F := hasFiniteMulSupport_iSup_nonarchAbsVal hx
    rw [finprod_pow F, ← finprod_mul_distrib (by fun_prop) (by fun_prop)]
    refine finprod_le_finprod (by fun_prop)
      (fun _ ↦ Real.iSup_nonneg_of_nonnegHomClass ..) (by fun_prop) fun v ↦ Real.iSup_le
      (fun j ↦ ?_) ?_
    · grw [(isNonarchimedean _ v.prop).eval_mvPolynomial_le (hp j) x]
      gcongr
      · exact HH₁ v.val
      · grw [← HH₂, ← le_max_left]
    · exact mul_nonneg (iSup_nonneg fun _ ↦ by positivity) <| by simp only [HH₁]

/-- Let `K` be a field with an admissible family of absolute values (giving rise
to a multiplicative height).
Let `p` be a family (indexed by `ι'`) of homogeneous polynomials in variables indexed by
the finite type `ι` and of the same degree `N`. Then for any `x : ι →  K`,
the multiplicative height of `fun j : ι' ↦ eval x (p j)` is bounded by a positive constant
times `mulHeight x ^ N`.

The difference to `mulHeight_eval_le` is that the constant is not made explicit. -/
/-
**Height.mulHeight_eval_le'** 是 Mathlib 中的一个定理，位于命名空间 `Height`。
形式化陈述：mulHeight_eval_le' {N : Nat} {p : ι' -> MvPolynomial ι K} (hp : forall i, 
(p i).IsHomogeneous N) : exists C > 0, forall (x : ι -> K), mulHeight (fun j => 
(p j).eval x) <= C * mulHeight x ^ N
参数：hp : forall i, (p i).IsHomogeneous N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_max_of_lt_right`：lt_max_of_lt_right (h : a < c) : a < max b c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Height.mulHeight_eval_le`：mulHeight_eval_le {N : Nat} {p : ι' -> MvPolyn
omial ι K} (hp : forall i, (p i).IsHomogeneous N) (x : ι -> K) : mulHeight (fun 
j => (p j).eva…

--- 原说明 ---
Let `K` be a field with an admissible family of absolute values (giving rise
to a multiplicative height).
Let `p` be a family (indexed by `ι'`) of homogeneous polynomials in variables in
dexed by
the finite type `ι` and of the same degree `N`. Then for any `x : ι →  K`,
the multiplicative height of `fun j : ι' ↦ eval x (p j)` is bounded by a positiv
e constant
times `mulHeight x ^ N`.

The difference to `mulHeight_eval_le` is that the constant is not made explicit.
-/
theorem mulHeight_eval_le' {N : ℕ} {p : ι' → MvPolynomial ι K} (hp : ∀ i, (p i).IsHomogeneous N) :
    ∃ C > 0, ∀ (x : ι → K), mulHeight (fun j ↦ (p j).eval x) ≤ C * mulHeight x ^ N :=
  ⟨_, by positivity, mulHeight_eval_le hp⟩

open Real in
/-- Let `K` be a field with an admissible family of absolute values (giving rise
to a logarithmic height).
Let `p` be a family (indexed by `ι'`) of homogeneous polynomials in variables indexed by
the finite type `ι` and of the same degree `N`. Then for any `x : ι →  K`,
the logarithmic height of `fun j : ι' ↦ eval x (p j)` is bounded by a constant
(which is made explicit) plus `N * logHeight x`. -/
/-
**Height.logHeight_eval_le** 是 Mathlib 中的一个定理，位于命名空间 `Height`。
形式化陈述：logHeight_eval_le {N : Nat} {p : ι' -> MvPolynomial ι K} (hp : forall i, (
p i).IsHomogeneous N) (x : ι -> K) : logHeight (fun j => (p j).eval x) <= log (m
ax (mulHeightBound p) 1) + N * logHeight x
参数：hp : forall i, (p i).IsHomogeneous N；x : ι -> K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `lt_max_of_lt_right`：lt_max_of_lt_right (h : a < c) : a < max b c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用引理 `Height.mulHeight_pos`：mulHeight_pos (x : ι -> K) : 0 < mulHeight x
· 使用引理 `Real.log_le_log`：log_le_log (hx : 0 < x) (hxy : x <= y) : log x <= log y
· 使用定理 `Height.mulHeight_eval_le`：mulHeight_eval_le {N : Nat} {p : ι' -> MvPolyn
omial ι K} (hp : forall i, (p i).IsHomogeneous N) (x : ι -> K) : mulHeight (fun 
j => (p j).eva…

--- 原说明 ---
Let `K` be a field with an admissible family of absolute values (giving rise
to a logarithmic height).
Let `p` be a family (indexed by `ι'`) of homogeneous polynomials in variables in
dexed by
the finite type `ι` and of the same degree `N`. Then for any `x : ι →  K`,
the logarithmic height of `fun j : ι' ↦ eval x (p j)` is bounded by a constant
(which is made explicit) plus `N * logHeight x`.
-/
theorem logHeight_eval_le {N : ℕ} {p : ι' → MvPolynomial ι K} (hp : ∀ i, (p i).IsHomogeneous N)
    (x : ι → K) :
    logHeight (fun j ↦ (p j).eval x) ≤ log (max (mulHeightBound p) 1) + N * logHeight x := by
  simp_rw [logHeight_eq_log_mulHeight]
  pull (disch := positivity) log
  exact (log_le_log <| by positivity) <| mulHeight_eval_le hp x

/-- Let `K` be a field with an admissible family of absolute values (giving rise
to a logarithmic height).
Let `p` be a family (indexed by `ι'`) of homogeneous polynomials in variables indexed by
the finite type `ι` and of the same degree `N`. Then for any `x : ι →  K`,
the logarithmic height of `fun j : ι' ↦ eval x (p j)` is bounded by a constant
plus `N * logHeight x`.

The difference to `logHeight_eval_le` is that the constant is not made explicit. -/
/-
**Height.logHeight_eval_le'** 是 Mathlib 中的一个定理，位于命名空间 `Height`。
形式化陈述：logHeight_eval_le' {N : Nat} {p : ι' -> MvPolynomial ι K} (hp : forall i, 
(p i).IsHomogeneous N) : exists C, forall (x : ι -> K), logHeight (fun j => (p j
).eval x) <= C + N * logHeight x
参数：hp : forall i, (p i).IsHomogeneous N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Height.logHeight_eval_le`：logHeight_eval_le {N : Nat} {p : ι' -> MvPolyn
omial ι K} (hp : forall i, (p i).IsHomogeneous N) (x : ι -> K) : logHeight (fun 
j => (p j).eva…

--- 原说明 ---
Let `K` be a field with an admissible family of absolute values (giving rise
to a logarithmic height).
Let `p` be a family (indexed by `ι'`) of homogeneous polynomials in variables in
dexed by
the finite type `ι` and of the same degree `N`. Then for any `x : ι →  K`,
the logarithmic height of `fun j : ι' ↦ eval x (p j)` is bounded by a constant
plus `N * logHeight x`.

The difference to `logHeight_eval_le` is that the constant is not made explicit.
-/
theorem logHeight_eval_le' {N : ℕ} {p : ι' → MvPolynomial ι K} (hp : ∀ i, (p i).IsHomogeneous N) :
    ∃ C, ∀ (x : ι → K), logHeight (fun j ↦ (p j).eval x) ≤ C + N * logHeight x :=
  ⟨_, logHeight_eval_le hp⟩

end Height

/-!
### Lower bound for the height of the image under a polynomial map

If
* `p : ι' → MvPolynomial ι K` is a family of homogeneous polynomials of the same degree `N`,
* `q : ι × ι' → MvPolynomial ι K` is a family of homogeneous polynomials of the same degree `M`,
* `x : ι → K` is such that for all `k : ι`,
  `∑ j, (q (k, j)).eval x * (p j).eval x = (x k) ^ (M + N)`,

then the multiplicative height of `fun j ↦ (p j).eval x` is bounded below by an (explicit) positive
constant depending only on `q` times the `N`th power of the multiplicative height of `x`.
A similar statement holds for the logarithmic height.

Note that we only require the polynomial relations `∑ j, q (k, j) * p j = X k ^ (M + N)`
to hold after evaluating at `x`. In this way, we can apply the result to points on some
subvariety of projective space when the map given by `p` is a morphism on that subvariety,
but not necessarily on all of the ambient space. In fact, the proof does not even need that
`p j` is homogeneous (of fixed degree). In applications, this will be the case, however,
and if the third condition above holds on the level of polynomials, then it follows.

The main idea is to reduce this to a combination of `mulHeight_linearMap_apply_le`
and `mulHeight_eval_le`.
-/

namespace Height

variable {K : Type*} [Field K] {ι ι' : Type*} [Fintype ι']

/-
**Height.mulHeight_eval_ge_aux** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma mulHeight_eval_ge_aux {M N : ℕ} {q : ι × ι' → MvPolynomial ι K} [IsEmpty ι']
    (p : ι' → MvPolynomial ι K) {x : ι → K}
    (h : ∀ k, ∑ j, (q (k, j)).eval x * (p j).eval x = (x k) ^ (M + N)) :
    x = 0 := by
  ext i
  simp only [Finset.univ_eq_empty, Finset.sum_empty] at h
  exact eq_zero_of_pow_eq_zero <| (h i).symm

variable [AdmissibleAbsValues K] [Finite ι]

open AdmissibleAbsValues

/-- If
* `p : ι' → MvPolynomial ι K` is a family of polynomials (which in practice will be homogeneous
  of the same degree `N`),
* `q : ι × ι' → MvPolynomial ι K` is a family of homogeneous polynomials of the same degree `M`,
* `x : ι → K` is such that for all `k : ι`,
  `∑ j, (q (k, j)).eval x * (p j).eval x = (x k) ^ (M + N)`,

then the multiplicative height of `fun j ↦ (p j).eval x` is bounded below by an (explicit) positive
constant depending only on `q` times the `N`th power of the multiplicative height of `x`. -/
/-
**Height.mulHeight_eval_ge** 是 Mathlib 中的一个定理，位于命名空间 `Height`。
形式化陈述：mulHeight_eval_ge {M N : Nat} {q : ι × ι' -> MvPolynomial ι K} (hq : foral
l a, (q a).IsHomogeneous M) (p : ι' -> MvPolynomial ι K) {x : ι -> K} (h : foral
l k, ∑ j, (q (k, j)).eval x * (p j).eval x = (x k) ^ (M + N)) : (Nat.card ι' ^ t
otalWeight K * max (mulHeightBound q) 1)⁻¹ * mulHeight x ^ N <= mulHeight (fun j
 => (p j).eval x)
参数：hq : forall a, (q a).IsHomogeneous M；p : ι' -> MvPolynomial ι K；h : forall k,
 ∑ j, (q (k, j)).eval x * (p j).eval x = (x k) ^ (M + N)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_eq_zero`：∀ {α : Type u_1} [inst : Fintype α] [IsEmpty α], F
intype.card α = 0
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用引理 `Height.max_mulHeightBound_zero_one_eq_one`：max_mulHeightBound_zero_one_e
q_one : max (mulHeightBound (0 : ι' -> MvPolynomial ι K)) 1 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `_private.Mathlib.NumberTheory.Height.MvPolynomial.0.Height.mulHeight_eva
l_ge_aux`：∀ {K : Type u_6} [inst : Field K] {ι : Type u_7} {ι' : Type u_8} [inst
_1 : Fintype ι'] {M N : ℕ}   {q : ι × ι' → MvPolynomial ι K} [IsEmpty …
· 使用引理 `Height.mulHeight_zero`：mulHeight_zero : mulHeight (0 : ι -> K) = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MvPolynomial.eval_zero`：eval_zero : eval (0 : σ -> R) = constantCoeff
· 使用引理 `Height.mulHeight_eq_one_of_subsingleton`：mulHeight_eq_one_of_subsingleto
n {ι : Type*} [Subsingleton ι] (x : ι -> K) : mulHeight x = 1
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Height.mulHeight_pow`：mulHeight_pow (x : ι -> K) (n : Nat) : mulHeight (
x ^ n) = mulHeight x ^ n
· 使用定理 `Height.mulHeight_linearMap_apply_le`：mulHeight_linearMap_apply_le [Nonem
pty ι] (A : ι' × ι -> K) (x : ι -> K) : mulHeight (fun j => ∑ i, A (j, i) * x i)
 <= Nat.card ι ^ totalWei…
· 使用引理 `inv_mul_le_iff₀`：inv_mul_le_iff₀ (hc : 0 < c) : c⁻¹ * b <= a ↔ b <= c * 
a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
（共 77 条，此处仅展示前 30 条）

--- 原说明 ---
If
* `p : ι' → MvPolynomial ι K` is a family of polynomials (which in practice will
 be homogeneous
  of the same degree `N`),
* `q : ι × ι' → MvPolynomial ι K` is a family of homogeneous polynomials of the 
same degree `M`,
* `x : ι → K` is such that for all `k : ι`,
  `∑ j, (q (k, j)).eval x * (p j).eval x = (x k) ^ (M + N)`,

then the multiplicative height of `fun j ↦ (p j).eval x` is bounded below by an 
(explicit) positive
constant depending only on `q` times the `N`th power of the multiplicative heigh
t of `x`.
-/
theorem mulHeight_eval_ge {M N : ℕ} {q : ι × ι' → MvPolynomial ι K}
    (hq : ∀ a, (q a).IsHomogeneous M) (p : ι' → MvPolynomial ι K) {x : ι → K}
    (h : ∀ k, ∑ j, (q (k, j)).eval x * (p j).eval x = (x k) ^ (M + N)) :
    (Nat.card ι' ^ totalWeight K * max (mulHeightBound q) 1)⁻¹ * mulHeight x ^ N ≤
      mulHeight (fun j ↦ (p j).eval x) := by
  rcases isEmpty_or_nonempty ι'
  · simp [show q = 0 from Subsingleton.elim .., max_mulHeightBound_zero_one_eq_one K ι (ι × ι'),
      mulHeight_eval_ge_aux p h]
    grind [zero_pow_eq]
  -- case `ι'` nonempty
  let q' : ι × ι' → K := fun a ↦ (q a).eval x
  have H : mulHeight x ^ (M + N) ≤
      Nat.card ι' ^ totalWeight K * mulHeight q' * mulHeight fun j ↦ (p j).eval x := by
    rw [← mulHeight_pow x (M + N)]
    have : x ^ (M + N) = fun k ↦ ∑ j, (q (k, j)).eval x * (p j).eval x := funext fun k ↦ (h k).symm
    simpa [this] using mulHeight_linearMap_apply_le q' _
  rw [inv_mul_le_iff₀ ?hC, ← mul_le_mul_iff_left₀ (by positivity : 0 < mulHeight x ^ M)]
  case hC => exact mul_pos (mod_cast Nat.one_le_pow _ _ Nat.card_pos) <| by positivity
  rw [← pow_add, add_comm]
  grw [H, mulHeight_eval_le hq x]
  exact Eq.le (by ring)

/-- If
* `p : ι' → MvPolynomial ι K` is a family of polynomials (which in practice will be homogeneous
  of the same degree `N`),
* `q : ι × ι' → MvPolynomial ι K` is a family of homogeneous polynomials of the same degree `M`,
* `x : ι → K` is such that for all `k : ι`,
  `∑ j, (q (k, j)).eval x * (p j).eval x = (x k) ^ (M + N)`,

then the multiplicative height of `fun j ↦ (p j).eval x` is bounded below by a positive
constant depending only on `q` times the `N`th power of the multiplicative height of `x`.

The difference to `mulHeight_eval_ge` is that the constant is not made explicit. -/
/-
**Height.mulHeight_eval_ge'** 是 Mathlib 中的一个定理，位于命名空间 `Height`。
形式化陈述：mulHeight_eval_ge' {M N : Nat} {q : ι × ι' -> MvPolynomial ι K} (hq : fora
ll a, (q a).IsHomogeneous M) : exists C > 0, forall (p : ι' -> MvPolynomial ι K)
 {x : ι -> K} (_h : forall k, ∑ j, (q (k, j)).eval x * (p j).eval x = (x k) ^ (M
 + N)), C * mulHeight x ^ N <= mulHeight (fun j => (p j).eval x)
参数：hq : forall a, (q a).IsHomogeneous M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `_private.Mathlib.NumberTheory.Height.MvPolynomial.0.Height.mulHeight_eva
l_ge_aux`：∀ {K : Type u_6} [inst : Field K] {ι : Type u_7} {ι' : Type u_8} [inst
_1 : Fintype ι'] {M N : ℕ}   {q : ι × ι' → MvPolynomial ι K} [IsEmpty …
· 使用引理 `Height.mulHeight_zero`：mulHeight_zero : mulHeight (0 : ι -> K) = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MvPolynomial.eval_zero`：eval_zero : eval (0 : σ -> R) = constantCoeff
· 使用引理 `Height.mulHeight_eq_one_of_subsingleton`：mulHeight_eq_one_of_subsingleto
n {ι : Type*} [Subsingleton ι] (x : ι -> K) : mulHeight x = 1
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `Nat.card_pos`：∀ {α : Type u_1} [Nonempty α] [Finite α], 0 < Nat.card α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `lt_max_of_lt_right`：lt_max_of_lt_right (h : a < c) : a < max b c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
If
* `p : ι' → MvPolynomial ι K` is a family of polynomials (which in practice will
 be homogeneous
  of the same degree `N`),
* `q : ι × ι' → MvPolynomial ι K` is a family of homogeneous polynomials of the 
same degree `M`,
* `x : ι → K` is such that for all `k : ι`,
  `∑ j, (q (k, j)).eval x * (p j).eval x = (x k) ^ (M + N)`,

then the multiplicative height of `fun j ↦ (p j).eval x` is bounded below by a p
ositive
constant depending only on `q` times the `N`th power of the multiplicative heigh
t of `x`.

The difference to `mulHeight_eval_ge` is that the constant is not made explicit.
-/
theorem mulHeight_eval_ge' {M N : ℕ} {q : ι × ι' → MvPolynomial ι K}
    (hq : ∀ a, (q a).IsHomogeneous M) :
    ∃ C > 0, ∀ (p : ι' → MvPolynomial ι K) {x : ι → K}
      (_h : ∀ k, ∑ j, (q (k, j)).eval x * (p j).eval x = (x k) ^ (M + N)),
      C * mulHeight x ^ N ≤ mulHeight (fun j ↦ (p j).eval x) := by
  rcases isEmpty_or_nonempty ι'
  · exact ⟨1, zero_lt_one, fun p _ h ↦ by simp [mulHeight_eval_ge_aux p h]⟩
  have : 0 < Nat.card ι' := Nat.card_pos
  exact ⟨_, by positivity, mulHeight_eval_ge hq⟩

open Real in
/-- If
* `p : ι' → MvPolynomial ι K` is a family of polynomials (which in practice will be homogeneous
  of the same degree `N`),
* `q : ι × ι' → MvPolynomial ι K` is a family of homogeneous polynomials of the same degree `M`,
* `x : ι → K` is such that for all `k : ι`,
  `∑ j, (q (k, j)).eval x * (p j).eval x = (x k) ^ (M + N)`,

then the logarithmic height of `fun j ↦ (p j).eval x` is bounded below by an (explicit)
constant depending only on `q` plus `N` times the logarithmic height of `x`. -/
/-
**Height.logHeight_eval_ge** 是 Mathlib 中的一个定理，位于命名空间 `Height`。
形式化陈述：logHeight_eval_ge {M N : Nat} {q : ι × ι' -> MvPolynomial ι K} (hq : foral
l a, (q a).IsHomogeneous M) (p : ι' -> MvPolynomial ι K) {x : ι -> K} (h : foral
l k, ∑ j, (q (k, j)).eval x * (p j).eval x = (x k) ^ (M + N)) : -log (Nat.card ι
' ^ totalWeight K * max (mulHeightBound q) 1) + N * logHeight x <= logHeight (fu
n j => (p j).eval x)
参数：hq : forall a, (q a).IsHomogeneous M；p : ι' -> MvPolynomial ι K；h : forall k,
 ∑ j, (q (k, j)).eval x * (p j).eval x = (x k) ^ (M + N)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_eq_zero`：∀ {α : Type u_1} [inst : Fintype α] [IsEmpty α], F
intype.card α = 0
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用引理 `Height.max_mulHeightBound_zero_one_eq_one`：max_mulHeightBound_zero_one_e
q_one : max (mulHeightBound (0 : ι' -> MvPolynomial ι K)) 1 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Real.log_pow`：log_pow (x : Real) (n : Nat) : log (x ^ n) = n * log x
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `_private.Mathlib.NumberTheory.Height.MvPolynomial.0.Height.mulHeight_eva
l_ge_aux`：∀ {K : Type u_6} [inst : Field K] {ι : Type u_7} {ι' : Type u_8} [inst
_1 : Fintype ι'] {M N : ℕ}   {q : ι × ι' → MvPolynomial ι K} [IsEmpty …
· 使用引理 `Height.mulHeight_zero`：mulHeight_zero : mulHeight (0 : ι -> K) = 1
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MvPolynomial.eval_zero`：eval_zero : eval (0 : σ -> R) = constantCoeff
· 使用引理 `Height.mulHeight_eq_one_of_subsingleton`：mulHeight_eq_one_of_subsingleto
n {ι : Type*} [Subsingleton ι] (x : ι -> K) : mulHeight x = 1
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
（共 51 条，此处仅展示前 30 条）

--- 原说明 ---
If
* `p : ι' → MvPolynomial ι K` is a family of polynomials (which in practice will
 be homogeneous
  of the same degree `N`),
* `q : ι × ι' → MvPolynomial ι K` is a family of homogeneous polynomials of the 
same degree `M`,
* `x : ι → K` is such that for all `k : ι`,
  `∑ j, (q (k, j)).eval x * (p j).eval x = (x k) ^ (M + N)`,

then the logarithmic height of `fun j ↦ (p j).eval x` is bounded below by an (ex
plicit)
constant depending only on `q` plus `N` times the logarithmic height of `x`.
-/
theorem logHeight_eval_ge {M N : ℕ} {q : ι × ι' → MvPolynomial ι K}
    (hq : ∀ a, (q a).IsHomogeneous M) (p : ι' → MvPolynomial ι K) {x : ι → K}
    (h : ∀ k, ∑ j, (q (k, j)).eval x * (p j).eval x = (x k) ^ (M + N)) :
    -log (Nat.card ι' ^ totalWeight K * max (mulHeightBound q) 1) + N * logHeight x ≤
      logHeight (fun j ↦ (p j).eval x) := by
  simp only [logHeight_eq_log_mulHeight]
  rcases isEmpty_or_nonempty ι'
  · simp [show q = 0 from Subsingleton.elim .., mulHeight_eval_ge_aux p h,
      max_mulHeightBound_zero_one_eq_one K ι (ι × ι')]
  have : (Nat.card ι' : ℝ) ^ totalWeight K ≠ 0 := by simp
  pull (disch := first | assumption | positivity) log
  exact (log_le_log <| by positivity) <| mulHeight_eval_ge hq p h

/-- If
* `p : ι' → MvPolynomial ι K` is a family of polynomials (which in practice will be homogeneous
  of the same degree `N`),
* `q : ι × ι' → MvPolynomial ι K` is a family of homogeneous polynomials of the same degree `M`,
* `x : ι → K` is such that for all `k : ι`,
  `∑ j, (q (k, j)).eval x * (p j).eval x = (x k) ^ (M + N)`,

then the logarithmic height of `fun j ↦ (p j).eval x` is bounded below by a
constant plus `N` times the logarithmic height of `x`.

The difference to `logHeight_eval_ge` is that the constant is not made explicit. -/
/-
**Height.logHeight_eval_ge'** 是 Mathlib 中的一个定理，位于命名空间 `Height`。
形式化陈述：logHeight_eval_ge' {M N : Nat} {q : ι × ι' -> MvPolynomial ι K} (hq : fora
ll a, (q a).IsHomogeneous M) : exists C, forall (p : ι' -> MvPolynomial ι K) {x 
: ι -> K} (_h : forall k, ∑ j, (q (k, j)).eval x * (p j).eval x = (x k) ^ (M + N
)), C + N * logHeight x <= logHeight (fun j => (p j).eval x)
参数：hq : forall a, (q a).IsHomogeneous M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Height.logHeight_eval_ge`：logHeight_eval_ge {M N : Nat} {q : ι × ι' -> M
vPolynomial ι K} (hq : forall a, (q a).IsHomogeneous M) (p : ι' -> MvPolynomial 
ι K) {x : ι ->…

--- 原说明 ---
If
* `p : ι' → MvPolynomial ι K` is a family of polynomials (which in practice will
 be homogeneous
  of the same degree `N`),
* `q : ι × ι' → MvPolynomial ι K` is a family of homogeneous polynomials of the 
same degree `M`,
* `x : ι → K` is such that for all `k : ι`,
  `∑ j, (q (k, j)).eval x * (p j).eval x = (x k) ^ (M + N)`,

then the logarithmic height of `fun j ↦ (p j).eval x` is bounded below by a
constant plus `N` times the logarithmic height of `x`.

The difference to `logHeight_eval_ge` is that the constant is not made explicit.
-/
theorem logHeight_eval_ge' {M N : ℕ} {q : ι × ι' → MvPolynomial ι K}
    (hq : ∀ a, (q a).IsHomogeneous M) :
    ∃ C, ∀ (p : ι' → MvPolynomial ι K) {x : ι → K}
      (_h : ∀ k, ∑ j, (q (k, j)).eval x * (p j).eval x = (x k) ^ (M + N)),
      C + N * logHeight x ≤ logHeight (fun j ↦ (p j).eval x) :=
  ⟨_, logHeight_eval_ge hq⟩

end Height

/-!
### Bounds for the height of ![x*y, x+y, 1]

We show that the multiplicative height of `![a*c, a*d + b*c, b*d]` is bounded from above and from
below by a positive constant times the product of the multiplicative heights of `![a, b]` and
`![c, d]` (and the analogous statements for the logarithmic heights).

The constants are unspecified here; with (likely considerably, but trivial) more work,
we could make them explicit.
-/

section sym2

namespace Height

variable [AdmissibleAbsValues K]

/-
**Height.mulHeight_mul_mulHeight** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：mulHeight_mul_mulHeight {a b c d : K} (hab : ![a, b] != 0) (hcd : ![c, d] 
!= 0) : mulHeight ![a, b] * mulHeight ![c, d] = mulHeight ![a * c, a * d, b * c,
 b * d]
参数：hab : ![a, b] != 0；hcd : ![c, d] != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Height.mulHeight_fun_mul_eq`：mulHeight_fun_mul_eq {x : ι -> K} (hx : x !
= 0) {y : ι' -> K} (hy : y != 0) : mulHeight (fun a : ι × ι' => x a.1 * y a.2) =
 mulHeight x * mu…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Fin.mk.congr_simp`：∀ {n : ℕ} (val val_1 : ℕ) (e_val : val = val_1) (isLt
 : val < n), ⟨val, isLt⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Equiv.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun toFun_1 : α 
→ β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : invFun 
= invFun_…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Nat.mod_succ`：∀ (n : ℕ), n % n.succ = n
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用引理 `Height.mulHeight_comp_equiv`：mulHeight_comp_equiv (e : ι ≃ ι') (x : ι' -
> K) : mulHeight (x ∘ e) = mulHeight x
-/
lemma mulHeight_mul_mulHeight {a b c d : K} (hab : ![a, b] ≠ 0) (hcd : ![c, d] ≠ 0) :
    mulHeight ![a, b] * mulHeight ![c, d] = mulHeight ![a * c, a * d, b * c, b * d] := by
  simp only [← mulHeight_fun_mul_eq hab hcd]
  convert! mulHeight_comp_equiv finProdFinEquiv _ with i
  fin_cases i <;> simp [finProdFinEquiv]

open MvPolynomial

variable (K)
/-
**Height.mulHeight_sym2_le** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：mulHeight_sym2_le : exists C > 0, forall (a b c d : K), mulHeight ![a * c,
 a * d + b * c, b * d] <= C * mulHeight ![a, b] * mulHeight ![c, d]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Height.mulHeight_eval_le'`：mulHeight_eval_le' {N : Nat} {p : ι' -> MvPol
ynomial ι K} (hp : forall i, (p i).IsHomogeneous N) : exists C > 0, forall (x : 
ι -> K), mulHei…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Height.mulHeight_zero`：mulHeight_zero : mulHeight (0 : ι -> K) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用引理 `Height.one_le_mulHeight`：one_le_mulHeight (x : ι -> K) : 1 <= mulHeight 
x
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `lt_max_of_lt_left`：lt_max_of_lt_left (h : a < b) : a < max b c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
（共 42 条，此处仅展示前 30 条）
-/
lemma mulHeight_sym2_le :
    ∃ C > 0, ∀ (a b c d : K),
      mulHeight ![a * c, a * d + b * c, b * d] ≤ C * mulHeight ![a, b] * mulHeight ![c, d] := by
  let p : Fin 3 → MvPolynomial (Fin 4) K := ![X 0, X 1 + X 2, X 3]
  have hom i : (p i).IsHomogeneous 1 := by
    fin_cases i <;> simp [p, isHomogeneous_X, IsHomogeneous.add]
  obtain ⟨C, hC₀, hC⟩ := mulHeight_eval_le' hom
  simp only [pow_one] at hC
  refine ⟨max C 1, by grind, fun a b c d ↦ ?_⟩
  by_cases hab : ![a, b] = 0
  · rw [hab, mulHeight_zero, mul_one, show a = 0 from congrFun hab 0,
      show b = 0 from congrFun hab 1,
      show ![0 * c, 0 * d + 0 * c, 0 * d] = 0 by ext i; fin_cases i <;> simp, mulHeight_zero]
    grw [← one_le_mulHeight]
    grind
  by_cases hcd : ![c, d] = 0
  · rw [hcd, mulHeight_zero, mul_one, show c = 0 from congrFun hcd 0,
      show d = 0 from congrFun hcd 1,
      show ![a * 0, a * 0 + b * 0, b * 0] = 0 by ext i; fin_cases i <;> simp, mulHeight_zero]
    grw [← one_le_mulHeight]
    grind
  rw [mul_assoc, mulHeight_mul_mulHeight hab hcd]
  grw [← le_max_left C 1]
  convert! hC _ with i
  fin_cases i <;> simp [p]
/-
**Height.mulHeight_sym2_ge** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：mulHeight_sym2_ge : exists C > 0, forall {a b c d : K}, ![a, b] != 0 -> ![
c, d] != 0 -> C * mulHeight ![a, b] * mulHeight ![c, d] <= mulHeight ![a * c, a 
* d + b * c, b * d]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Height.mulHeight_eval_ge'`：mulHeight_eval_ge' {M N : Nat} {q : ι × ι' ->
 MvPolynomial ι K} (hq : forall a, (q a).IsHomogeneous M) : exists C > 0, forall
 (p : ι' -> MvP…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `Height.mulHeight_mul_mulHeight`：mulHeight_mul_mulHeight {a b c d : K} (h
ab : ![a, b] != 0) (hcd : ![c, d] != 0) : mulHeight ![a, b] * mulHeight ![c, d] 
= mulHeight ![a * c,…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MvPolynomial.eval_X`：eval_X : forall n, eval f (X n) = f n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Fin.sum_univ_three`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : Fin 3
 → M), ∑ i, f i = f 0 + f 1 + f 2
（共 77 条，此处仅展示前 30 条）
-/
lemma mulHeight_sym2_ge :
    ∃ C > 0, ∀ {a b c d : K}, ![a, b] ≠ 0 → ![c, d] ≠ 0 →
      C * mulHeight ![a, b] * mulHeight ![c, d] ≤ mulHeight ![a * c, a * d + b * c, b * d] := by
  let p : Fin 3 → MvPolynomial (Fin 4) K := ![X 0, X 1 + X 2, X 3]
  let q : Fin 4 × Fin 3 → MvPolynomial (Fin 4) K :=
    ![![X 0, 0, 0], ![0, X 1, -X 0], ![0, X 2, -X 0], ![0, 0, X 3]].uncurry
  have hom a : (q a).IsHomogeneous 1 := by
    fin_cases a <;> simp [q] <;> grind [!isHomogeneous_X, isHomogeneous_zero, IsHomogeneous.neg]
  obtain ⟨C, hC₀, hC⟩ := mulHeight_eval_ge' (M := 1) (N := 1) hom
  simp only [pow_one] at hC
  refine ⟨C, hC₀, fun hab hcd ↦ ?_⟩
  rw [mul_assoc, mulHeight_mul_mulHeight hab hcd]
  convert! hC p fun j ↦ ?H with i
  case H => fin_cases j <;> simp [p, q, Fin.sum_univ_three] <;> ring
  fin_cases i <;> simp [p]

open Real in
/-
**Height.logHeight_sym2_le** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：logHeight_sym2_le : exists C, forall (a b c d : K), logHeight ![a * c, a *
 d + b * c, b * d] <= C + logHeight ![a, b] + logHeight ![c, d]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Height.mulHeight_sym2_le`：mulHeight_sym2_le : exists C > 0, forall (a b 
c d : K), mulHeight ![a * c, a * d + b * c, b * d] <= C * mulHeight ![a, b] * mu
lHeight ![c, d…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `Height.mulHeight_pos`：mulHeight_pos (x : ι -> K) : 0 < mulHeight x
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Real.log_le_log`：log_le_log (hx : 0 < x) (hxy : x <= y) : log x <= log y
-/
lemma logHeight_sym2_le :
    ∃ C, ∀ (a b c d : K), logHeight ![a * c, a * d + b * c, b * d] ≤
      C + logHeight ![a, b] + logHeight ![c, d] := by
  obtain ⟨C', hC₀, hC⟩ := mulHeight_sym2_le K
  refine ⟨log C', fun a b c d ↦ ?_⟩
  simp only [logHeight_eq_log_mulHeight]
  pull (disch := positivity) log
  exact log_le_log (by positivity) (hC ..)

open Real in
/-
**Height.logHeight_sym2_ge** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：logHeight_sym2_ge : exists C, forall {a b c d : K}, ![a, b] != 0 -> ![c, d
] != 0 -> C + logHeight ![a, b] + logHeight ![c, d] <= logHeight ![a * c, a * d 
+ b * c, b * d]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Height.mulHeight_sym2_ge`：mulHeight_sym2_ge : exists C > 0, forall {a b 
c d : K}, ![a, b] != 0 -> ![c, d] != 0 -> C * mulHeight ![a, b] * mulHeight ![c,
 d] <= mulHeig…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `Height.mulHeight_pos`：mulHeight_pos (x : ι -> K) : 0 < mulHeight x
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Real.log_le_log`：log_le_log (hx : 0 < x) (hxy : x <= y) : log x <= log y
-/
lemma logHeight_sym2_ge :
    ∃ C, ∀ {a b c d : K}, ![a, b] ≠ 0 → ![c, d] ≠ 0 →
      C + logHeight ![a, b] + logHeight ![c, d] ≤ logHeight ![a * c, a * d + b * c, b * d] := by
  obtain ⟨C', hC₀, hC⟩ := mulHeight_sym2_ge K
  refine ⟨log C', fun hab hcd ↦ ?_⟩
  simp only [logHeight_eq_log_mulHeight]
  pull (disch := positivity) log
  exact log_le_log (by positivity) (hC hab hcd)

-- see below comment regarding performance
set_option linter.tacticAnalysis.mergeWithGrind false in
/-
**Height.abs_logHeight_sym2_sub_le** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：abs_logHeight_sym2_sub_le : exists C, forall {a b c d : K}, ![a, b] != 0 -
> ![c, d] != 0 -> |logHeight ![a * c, a * d + b * c, b * d] - (logHeight ![a, b]
 + logHeight ![c, d])| <= C
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Height.logHeight_sym2_le`：logHeight_sym2_le : exists C, forall (a b c d 
: K), logHeight ![a * c, a * d + b * c, b * d] <= C + logHeight ![a, b] + logHei
ght ![c, d]
· 使用引理 `Height.logHeight_sym2_ge`：logHeight_sym2_ge : exists C, forall {a b c d 
: K}, ![a, b] != 0 -> ![c, d] != 0 -> C + logHeight ![a, b] + logHeight ![c, d] 
<= logHeight !…
-/
lemma abs_logHeight_sym2_sub_le :
    ∃ C, ∀ {a b c d : K}, ![a, b] ≠ 0 → ![c, d] ≠ 0 →
      |logHeight ![a * c, a * d + b * c, b * d] - (logHeight ![a, b] + logHeight ![c, d])| ≤ C := by
  obtain ⟨C₁, hC₁⟩ := logHeight_sym2_le K
  obtain ⟨C₂, hC₂⟩ := logHeight_sym2_ge K
  -- `grind` does it without the `specialize`, but is slow
  exact ⟨max C₁ (-C₂), fun hab hcd ↦ by specialize hC₂ hab hcd; grind⟩

end Height

end sym2

end

