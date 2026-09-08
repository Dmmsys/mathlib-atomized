/-
Copyright (c) 2025 Michael Stoll, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Floris van Doorn
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Tactic.Ring

/-!
# Big operators on a finset in groups with zero involving order

This file contains the results concerning the interaction of finset big operators with groups with
zero, where order is involved.
-/

public section

variable {ι R S : Type*}

namespace Finset

section CommMonoidWithZero
variable [CommMonoidWithZero R]

section PosMulMono
variable [Preorder R] [ZeroLEOneClass R] [PosMulMono R] {f g : ι → R} {s t : Finset ι}

/-
**Finset.prod_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_nonneg (h0 : forall i in s, 0 <= f i) : 0 <= ∏ i in s, f i
参数：h0 : forall i in s, 0 <= f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_induction`：prod_induction {M : Type*} [CommMonoid M] (f : ι 
-> M) (p : M -> Prop) (hom : forall a b, p a -> p b -> p (a * b)) (unit : p 1) (
base : fora…
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
-/
lemma prod_nonneg (h0 : ∀ i ∈ s, 0 ≤ f i) : 0 ≤ ∏ i ∈ s, f i :=
  prod_induction f (fun i ↦ 0 ≤ i) (fun _ _ ha hb ↦ mul_nonneg ha hb) zero_le_one h0

/-- If all `f i`, `i ∈ s`, are nonnegative and each `f i` is less than or equal to `g i`, then the
product of `f i` is less than or equal to the product of `g i`. See also `Finset.prod_le_prod'` for
the case of an ordered commutative multiplicative monoid. -/
@[gcongr]
/-
**Finset.prod_le_prod** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_le_prod (h0 : forall i in s, 0 <= f i) (h1 : forall i in s, f i <= g 
i) : ∏ i in s, f i <= ∏ i in s, g i
参数：h0 : forall i in s, 0 <= f i；h1 : forall i in s, f i <= g i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `posMulMono_iff_mulPosMono`：posMulMono_iff_mulPosMono : PosMulMono α ↔ Mu
lPosMono α
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Finset.prod_nonneg`：prod_nonneg (h0 : forall i in s, 0 <= f i) : 0 <= ∏ 
i in s, f i
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c

--- 原说明 ---
If all `f i`, `i ∈ s`, are nonnegative and each `f i` is less than or equal to `
g i`, then the
product of `f i` is less than or equal to the product of `g i`. See also `Finset
.prod_le_prod'` for
the case of an ordered commutative multiplicative monoid.
-/
lemma prod_le_prod (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s has ih =>
    simp only [prod_cons, forall_mem_cons] at h0 h1 ⊢
    have := posMulMono_iff_mulPosMono.1 ‹PosMulMono R›
    gcongr
    exacts [prod_nonneg h0.2, h0.1.trans h1.1, h1.1, ih h0.2 h1.2]

/-- A finite product of nonnegative monotone functions is monotone. See also
`Monotone.finsetProd'` for the case of an ordered commutative multiplicative monoid. -/
/-
**Finset._root_.Monotone.finsetProd** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finite product of nonnegative monotone functions is monotone. See also
`Monotone.finsetProd'` for the case of an ordered commutative multiplicative mon
oid.
-/
theorem _root_.Monotone.finsetProd {γ : Type*} [Preorder γ] {f : ι → γ → R}
    (hf : ∀ i ∈ s, Monotone (f i)) (hf₀ : ∀ i ∈ s, ∀ x, 0 ≤ f i x) :
    Monotone fun x ↦ ∏ i ∈ s, f i x :=
  fun _ _ hab ↦ prod_le_prod (fun i hi ↦ hf₀ i hi _) fun i hi ↦ hf i hi hab

/-- A finite product of functions nonnegative and monotone on `u` is monotone on `u`. See also
`MonotoneOn.finsetProd'` for the case of an ordered commutative multiplicative monoid. -/
/-
**Finset._root_.MonotoneOn.finsetProd** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finite product of functions nonnegative and monotone on `u` is monotone on `u`
. See also
`MonotoneOn.finsetProd'` for the case of an ordered commutative multiplicative m
onoid.
-/
theorem _root_.MonotoneOn.finsetProd {γ : Type*} [Preorder γ] {u : Set γ} {f : ι → γ → R}
    (hf : ∀ i ∈ s, MonotoneOn (f i) u) (hf₀ : ∀ i ∈ s, ∀ x ∈ u, 0 ≤ f i x) :
    MonotoneOn (fun x ↦ ∏ i ∈ s, f i x) u :=
  fun _ ha _ hb hab ↦ prod_le_prod (fun i hi ↦ hf₀ i hi _ ha) fun i hi ↦ hf i hi ha hb hab

/-- A finite product of nonnegative antitone functions is antitone. See also
`Antitone.finsetProd'` for the case of an ordered commutative multiplicative monoid. -/
/-
**Finset._root_.Antitone.finsetProd** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finite product of nonnegative antitone functions is antitone. See also
`Antitone.finsetProd'` for the case of an ordered commutative multiplicative mon
oid.
-/
theorem _root_.Antitone.finsetProd {γ : Type*} [Preorder γ] {f : ι → γ → R}
    (hf : ∀ i ∈ s, Antitone (f i)) (hf₀ : ∀ i ∈ s, ∀ x, 0 ≤ f i x) :
    Antitone fun x ↦ ∏ i ∈ s, f i x :=
  fun _ _ hab ↦ prod_le_prod (fun i hi ↦ hf₀ i hi _) fun i hi ↦ hf i hi hab

/-- A finite product of functions nonnegative and antitone on `u` is antitone on `u`. See also
`AntitoneOn.finsetProd'` for the case of an ordered commutative multiplicative monoid. -/
/-
**Finset._root_.AntitoneOn.finsetProd** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finite product of functions nonnegative and antitone on `u` is antitone on `u`
. See also
`AntitoneOn.finsetProd'` for the case of an ordered commutative multiplicative m
onoid.
-/
theorem _root_.AntitoneOn.finsetProd {γ : Type*} [Preorder γ] {u : Set γ} {f : ι → γ → R}
    (hf : ∀ i ∈ s, AntitoneOn (f i) u) (hf₀ : ∀ i ∈ s, ∀ x ∈ u, 0 ≤ f i x) :
    AntitoneOn (fun x ↦ ∏ i ∈ s, f i x) u :=
  fun _ ha _ hb hab ↦ prod_le_prod (fun i hi ↦ hf₀ i hi _ hb) fun i hi ↦ hf i hi ha hb hab

/-- If each `f i`, `i ∈ s` belongs to `[0, 1]`, then their product is less than or equal to one.
See also `Finset.prod_le_one'` for the case of an ordered commutative multiplicative monoid. -/
/-
**Finset.prod_le_one** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_le_one (h0 : forall i in s, 0 <= f i) (h1 : forall i in s, f i <= 1) 
: ∏ i in s, f i <= 1
参数：h0 : forall i in s, 0 <= f i；h1 : forall i in s, f i <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用引理 `Finset.prod_le_prod`：prod_le_prod (h0 : forall i in s, 0 <= f i) (h1 : f
orall i in s, f i <= g i) : ∏ i in s, f i <= ∏ i in s, g i

--- 原说明 ---
If each `f i`, `i ∈ s` belongs to `[0, 1]`, then their product is less than or e
qual to one.
See also `Finset.prod_le_one'` for the case of an ordered commutative multiplica
tive monoid.
-/
lemma prod_le_one (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) : ∏ i ∈ s, f i ≤ 1 := by
  convert! ← prod_le_prod h0 h1
  exact Finset.prod_const_one

/-- A version of `Finset.one_le_prod'` for `PosMulMono` in place of `MulLeftMono`. -/
/-
**Finset.one_le_prod** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：one_le_prod (hf : forall i in s, 1 <= f i) : 1 <= ∏ i in s, f i
参数：hf : forall i in s, 1 <= f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用引理 `Finset.prod_le_prod`：prod_le_prod (h0 : forall i in s, 0 <= f i) (h1 : f
orall i in s, f i <= g i) : ∏ i in s, f i <= ∏ i in s, g i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
A version of `Finset.one_le_prod'` for `PosMulMono` in place of `MulLeftMono`.
-/
lemma one_le_prod (hf : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i := by
  simpa using prod_le_prod (by simp) hf
/-
**Finset.le_prod_max_one** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：le_prod_max_one {M : Type*} [CommMonoidWithZero M] [LinearOrder M] [ZeroLE
OneClass M] [PosMulMono M] {i : ι} (hi : i in s) (f : ι -> M) : f i <= ∏ i in s,
 max (f i) 1
参数：hi : i in s；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用引理 `Finset.prod_nonneg`：prod_nonneg (h0 : forall i in s, 0 <= f i) : 0 <= ∏ 
i in s, f i
· 使用定理 `le_sup_of_le_right`：le_sup_of_le_right (h : c <= b) : c <= a ⊔ b
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_eq_single_of_mem`：prod_eq_single_of_mem {s : Finset ι} {f : 
ι -> M} (a : ι) (h : a in s) (h₀ : forall b in s, b != a -> f b = 1) : ∏ x in s,
 f x = f a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Finset.prod_le_prod`：prod_le_prod (h0 : forall i in s, 0 <= f i) (h1 : f
orall i in s, f i <= g i) : ∏ i in s, f i <= ∏ i in s, g i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma le_prod_max_one {M : Type*} [CommMonoidWithZero M] [LinearOrder M] [ZeroLEOneClass M]
    [PosMulMono M] {i : ι} (hi : i ∈ s) (f : ι → M) :
    f i ≤ ∏ i ∈ s, max (f i) 1 := by
  classical
  rcases lt_or_ge (f i) 0 with hf | hf
  · exact (hf.trans_le <| prod_nonneg fun _ _ ↦ le_sup_of_le_right zero_le_one).le
  have : f i = ∏ j ∈ s, if i = j then f i else 1 := by
    rw [prod_eq_single_of_mem i hi fun _ _ _ ↦ by grind]
    simp
  exact this ▸ prod_le_prod (fun _ _ ↦ by grind [zero_le_one]) fun _ _ ↦ by grind

@[gcongr]
/-
**Finset.prod_le_prod_of_subset_of_one_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_le_prod_of_subset_of_one_le (h : s subseteq t) (hf0 : forall i in s, 
0 <= f i) (hf : forall i in t, i ∉ s -> 1 <= f i) : ∏ i in s, f i <= ∏ i in t, f
 i
参数：h : s subseteq t；hf0 : forall i in s, 0 <= f i；hf : forall i in t, i ∉ s -> 1
 <= f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `posMulMono_iff_mulPosMono`：posMulMono_iff_mulPosMono : PosMulMono α ↔ Mu
lPosMono α
· 使用定理 `le_mul_of_one_le_left`：le_mul_of_one_le_left [MulPosMono α] (hb : 0 <= b
) (h : 1 <= a) : b <= a * b
· 使用引理 `Finset.prod_nonneg`：prod_nonneg (h0 : forall i in s, 0 <= f i) : 0 <= ∏ 
i in s, f i
· 使用引理 `Finset.one_le_prod`：one_le_prod (hf : forall i in s, 1 <= f i) : 1 <= ∏ 
i in s, f i
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_union`：prod_union [DecidableEq ι] (h : Disjoint s₁ s₂) : ∏ x
 in s₁ union s₂, f x = (∏ x in s₁, f x) * ∏ x in s₂, f x
· 使用定理 `Finset.sdiff_disjoint`：sdiff_disjoint : Disjoint (t \ s) s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sdiff_union_of_subset`：sdiff_union_of_subset {s₁ s₂ : Finset α} (
h : s₁ subseteq s₂) : s₂ \ s₁ union s₁ = s₂
-/
theorem prod_le_prod_of_subset_of_one_le (h : s ⊆ t)
    (hf0 : ∀ i ∈ s, 0 ≤ f i)
    (hf : ∀ i ∈ t, i ∉ s → 1 ≤ f i) : ∏ i ∈ s, f i ≤ ∏ i ∈ t, f i := by
  have := posMulMono_iff_mulPosMono.1 ‹PosMulMono R›
  classical
  calc
      ∏ i ∈ s, f i ≤ (∏ i ∈ t \ s, f i) * ∏ i ∈ s, f i :=
        le_mul_of_one_le_left (prod_nonneg hf0) <| one_le_prod <| by simpa only [mem_sdiff, and_imp]
      _ = ∏ i ∈ t \ s ∪ s, f i := (prod_union sdiff_disjoint).symm
      _ = ∏ i ∈ t, f i := by rw [sdiff_union_of_subset h]
/-
**Finset.prod_le_prod_of_subset_of_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_le_prod_of_subset_of_le_one (h : s subseteq t) (hf0 : forall i in t, 
0 <= f i) (hf : forall i in t, i ∉ s -> f i <= 1) : ∏ i in t, f i <= ∏ i in s, f
 i
参数：h : s subseteq t；hf0 : forall i in t, 0 <= f i；hf : forall i in t, i ∉ s -> f
 i <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `posMulMono_iff_mulPosMono`：posMulMono_iff_mulPosMono : PosMulMono α ↔ Mu
lPosMono α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sdiff_union_of_subset`：sdiff_union_of_subset {s₁ s₂ : Finset α} (
h : s₁ subseteq s₂) : s₂ \ s₁ union s₁ = s₂
· 使用定理 `Finset.prod_union`：prod_union [DecidableEq ι] (h : Disjoint s₁ s₂) : ∏ x
 in s₁ union s₂, f x = (∏ x in s₁, f x) * ∏ x in s₂, f x
· 使用定理 `Finset.sdiff_disjoint`：sdiff_disjoint : Disjoint (t \ s) s
· 使用定理 `mul_le_of_le_one_left`：mul_le_of_le_one_left [MulPosMono α] (hb : 0 <= b
) (h : a <= 1) : a * b <= b
· 使用引理 `Finset.prod_nonneg`：prod_nonneg (h0 : forall i in s, 0 <= f i) : 0 <= ∏ 
i in s, f i
· 使用引理 `Finset.prod_le_one`：prod_le_one (h0 : forall i in s, 0 <= f i) (h1 : for
all i in s, f i <= 1) : ∏ i in s, f i <= 1
-/
theorem prod_le_prod_of_subset_of_le_one (h : s ⊆ t) (hf0 : ∀ i ∈ t, 0 ≤ f i)
    (hf : ∀ i ∈ t, i ∉ s → f i ≤ 1) :
    ∏ i ∈ t, f i ≤ ∏ i ∈ s, f i := by
  have := posMulMono_iff_mulPosMono.1 ‹PosMulMono R›
  classical
  calc
    ∏ i ∈ t, f i = ∏ i ∈ t \ s ∪ s, f i := by rw [sdiff_union_of_subset h]
    _ = (∏ i ∈ t \ s, f i) * ∏ i ∈ s, f i := prod_union sdiff_disjoint
    _ ≤ ∏ i ∈ s, f i :=
      mul_le_of_le_one_left (prod_nonneg (by grind)) (prod_le_one (by grind) (by grind))
/-
**Finset.prod_mono_set_of_one_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_mono_set_of_one_le (hf : forall x, 1 <= f x) : Monotone fun s => ∏ x 
in s, f x
参数：hf : forall x, 1 <= f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_le_prod_of_subset_of_one_le`：prod_le_prod_of_subset_of_one_l
e (h : s subseteq t) (hf0 : forall i in s, 0 <= f i) (hf : forall i in t, i ∉ s 
-> 1 <= f i) : ∏ i in s, f i …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
-/
theorem prod_mono_set_of_one_le (hf : ∀ x, 1 ≤ f x) :
    Monotone fun s ↦ ∏ x ∈ s, f x :=
  fun _ _ hst ↦ prod_le_prod_of_subset_of_one_le hst
    (fun i _ ↦ zero_le_one.trans (hf i)) (fun x _ _ ↦ hf x)
/-
**Finset.prod_anti_set_of_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_anti_set_of_le_one (hf0 : forall (x : ι), 0 <= f x) (hf : forall (x :
 ι), f x <= 1) : Antitone fun (s : Finset ι) => ∏ x in s, f x
参数：hf0 : forall (x : ι), 0 <= f x；hf : forall (x : ι), f x <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_le_prod_of_subset_of_le_one`：prod_le_prod_of_subset_of_le_on
e (h : s subseteq t) (hf0 : forall i in t, 0 <= f i) (hf : forall i in t, i ∉ s 
-> f i <= 1) : ∏ i in t, f i …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem prod_anti_set_of_le_one (hf0 : ∀ (x : ι), 0 ≤ f x) (hf : ∀ (x : ι), f x ≤ 1) :
    Antitone fun (s : Finset ι) => ∏ x ∈ s, f x :=
  fun _ _ hst ↦ prod_le_prod_of_subset_of_le_one hst (by grind) (by simp [hf])

end PosMulMono

section PosMulStrictMono
variable [PartialOrder R] [ZeroLEOneClass R] [PosMulStrictMono R] [Nontrivial R] {f g : ι → R}
  {s t : Finset ι}

/-
**Finset.prod_pos** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_pos (h0 : forall i in s, 0 < f i) : 0 < ∏ i in s, f i
参数：h0 : forall i in s, 0 < f i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_induction`：prod_induction {M : Type*} [CommMonoid M] (f : ι 
-> M) (p : M -> Prop) (hom : forall a b, p a -> p b -> p (a * b)) (unit : p 1) (
base : fora…
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
-/
lemma prod_pos (h0 : ∀ i ∈ s, 0 < f i) : 0 < ∏ i ∈ s, f i :=
  prod_induction f (fun x ↦ 0 < x) (fun _ _ ha hb ↦ mul_pos ha hb) zero_lt_one h0
/-
**Finset.prod_lt_prod** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_lt_prod (hf : forall i in s, 0 < f i) (hfg : forall i in s, f i <= g 
i) (hlt : exists i in s, f i < g i) : ∏ i in s, f i < ∏ i in s, g i
参数：hf : forall i in s, 0 < f i；hfg : forall i in s, f i <= g i；hlt : exists i in
 s, f i < g i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `posMulStrictMono_iff_mulPosStrictMono`：posMulStrictMono_iff_mulPosStrict
Mono : PosMulStrictMono α ↔ MulPosStrictMono α
· 使用定理 `mul_lt_mul_of_pos_of_nonneg'`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : 
Zero α] [inst_2 : Preorder α] {a b c d : α} [PosMulMono α]   [MulPosStrictMono α
], a < b → c ≤ d →…
· 使用定理 `PosMulStrictMono.toPosMulMono`：∀ {α : Type u_1} [inst : MulZeroClass α] 
[inst_1 : PartialOrder α] [PosMulStrictMono α], PosMulMono α
· 使用引理 `Finset.prod_le_prod`：prod_le_prod (h0 : forall i in s, 0 <= f i) (h1 : f
orall i in s, f i <= g i) : ∏ i in s, f i <= ∏ i in s, g i
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Finset.mem_of_mem_erase`：mem_of_mem_erase : b in erase s a -> b in s
· 使用引理 `Finset.prod_pos`：prod_pos (h0 : forall i in s, 0 < f i) : 0 < ∏ i in s, 
f i
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma prod_lt_prod (hf : ∀ i ∈ s, 0 < f i) (hfg : ∀ i ∈ s, f i ≤ g i)
    (hlt : ∃ i ∈ s, f i < g i) :
    ∏ i ∈ s, f i < ∏ i ∈ s, g i := by
  classical
  obtain ⟨i, hi, hilt⟩ := hlt
  rw [← insert_erase hi, prod_insert (notMem_erase _ _), prod_insert (notMem_erase _ _)]
  have := posMulStrictMono_iff_mulPosStrictMono.1 ‹PosMulStrictMono R›
  refine mul_lt_mul_of_pos_of_nonneg' hilt ?_ ?_ ?_
  · exact prod_le_prod (fun j hj => le_of_lt (hf j (mem_of_mem_erase hj)))
      (fun _ hj ↦ hfg _ <| mem_of_mem_erase hj)
  · exact prod_pos fun j hj => hf j (mem_of_mem_erase hj)
  · exact (hf i hi).le.trans hilt.le
/-
**Finset.prod_lt_prod_of_nonempty** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_lt_prod_of_nonempty (hf : forall i in s, 0 < f i) (hfg : forall i in 
s, f i < g i) (h_ne : s.Nonempty) : ∏ i in s, f i < ∏ i in s, g i
参数：hf : forall i in s, 0 < f i；hfg : forall i in s, f i < g i；h_ne : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.prod_lt_prod`：prod_lt_prod (hf : forall i in s, 0 < f i) (hfg : f
orall i in s, f i <= g i) (hlt : exists i in s, f i < g i) : ∏ i in s, f i < ∏ i
 in s, g …
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma prod_lt_prod_of_nonempty (hf : ∀ i ∈ s, 0 < f i) (hfg : ∀ i ∈ s, f i < g i)
    (h_ne : s.Nonempty) :
    ∏ i ∈ s, f i < ∏ i ∈ s, g i := by
  apply prod_lt_prod hf fun i hi => le_of_lt (hfg i hi)
  obtain ⟨i, hi⟩ := h_ne
  exact ⟨i, hi, hfg i hi⟩

end PosMulStrictMono
end CommMonoidWithZero

end Finset

