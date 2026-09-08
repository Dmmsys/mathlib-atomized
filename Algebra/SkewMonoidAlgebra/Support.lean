/-
Copyright (c) 2025 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, María Inés de Frutos Fernández
-/
module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Algebra.SkewMonoidAlgebra.Basic

/-!
# Lemmas about the support of an element of a skew monoid algebra

For `f : SkewMonoidAlgebra k G`, `f.support` is the set of all `a ∈ G` such that `f.coeff a ≠ 0`.
-/

public section

open scoped Pointwise

namespace SkewMonoidAlgebra

open Finset Finsupp

variable {k G : Type*}

section AddCommMonoid

variable [AddCommMonoid k] {a : G} {b : k}

/-
**SkewMonoidAlgebra.support_single** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`
。
形式化陈述：∀ {k : Type u_1} {G : Type u_2} [inst : AddCommMonoid k] {b : k} (a : G), 
  b ≠ 0 → (SkewMonoidAlgebra.single a b).support = {a}
参数：a : G；SkewMonoidAlgebra.single a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.support_single`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] 
{b : M} (a : α), b ≠ 0 → (fun₀ | a => b).support = {a}
-/
@[simp] lemma support_single (a : G) (h : b ≠ 0) : (single a b).support = {a} :=
  Finsupp.support_single _ h

@[deprecated (since := "2026-05-05")] alias support_single_ne_zero := support_single
/-
**SkewMonoidAlgebra.support_single_subset** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidA
lgebra`。
形式化陈述：support_single_subset : (single a b).support subseteq {a}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.support_single_subset`：support_single_subset : (single a b).supp
ort subseteq {a}
-/
theorem support_single_subset : (single a b).support ⊆ {a} := Finsupp.support_single_subset
/-
**SkewMonoidAlgebra.support_sum** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：support_sum {k' G' : Type*} [DecidableEq G'] [AddCommMonoid k'] {f : SkewM
onoidAlgebra k G} {g : G -> k -> SkewMonoidAlgebra k' G'} : (f.sum g).support su
bseteq f.support.biUnion fun a => (g a (f.coeff a)).support
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.coeff_sum'`：coeff_sum' {k' G' : Type*} [AddCommMonoid 
k'] (f : SkewMonoidAlgebra k G) (g : G -> k -> SkewMonoidAlgebra k' G') : (sum f
 g).coeff = Finsup…
· 使用定理 `Finsupp.support_sum`：support_sum [DecidableEq β] [Zero M] [AddCommMonoid
 N] {f : α ->₀ M} {g : α -> M -> β ->₀ N} : (f.sum g).support subseteq f.support
.biUnion …
-/
theorem support_sum {k' G' : Type*} [DecidableEq G'] [AddCommMonoid k'] {f : SkewMonoidAlgebra k G}
    {g : G → k → SkewMonoidAlgebra k' G'} :
    (f.sum g).support ⊆ f.support.biUnion fun a ↦ (g a (f.coeff a)).support := by
  simp_rw [support, coeff_sum']
  apply Finsupp.support_sum

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup k]

/-
**SkewMonoidAlgebra.support_neg** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：support_neg (p : SkewMonoidAlgebra k G) : (-p).support = p.support
参数：p : SkewMonoidAlgebra k G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.support.eq_1`：∀ {k : Type u_1} {G : Type u_2} [inst : 
AddMonoid k] (p : SkewMonoidAlgebra k G), p.support = p.coeff.support
· 使用定理 `SkewMonoidAlgebra.coeff_neg`：coeff_neg (a : SkewMonoidAlgebra k G) : (-a
).coeff = -a.coeff
· 使用引理 `Finsupp.support_neg`：support_neg (f : ι ->₀ G) : support (-f) = support 
f
· 使用定理 `SkewMonoidAlgebra.support_coeff`：support_coeff (p : SkewMonoidAlgebra k 
G) : p.coeff.support = p.support
-/
theorem support_neg (p : SkewMonoidAlgebra k G) : (-p).support = p.support := by
  rw [support, coeff_neg, Finsupp.support_neg, support_coeff]

end AddCommGroup

section AddCommMonoidWithOne

variable [One G] [AddCommMonoidWithOne k]

/-
**SkewMonoidAlgebra.support_one_subset** 是 Mathlib 中的一个引理，位于命名空间 `SkewMonoidAlge
bra`。
形式化陈述：support_one_subset : (1 : SkewMonoidAlgebra k G).support subseteq 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.support_single_subset`：support_single_subset : (single a b).supp
ort subseteq {a}
-/
lemma support_one_subset : (1 : SkewMonoidAlgebra k G).support ⊆ 1 :=
  Finsupp.support_single_subset

@[simp]
/-
**SkewMonoidAlgebra.support_one** 是 Mathlib 中的一个引理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：support_one [NeZero (1 : k)] : (1 : SkewMonoidAlgebra k G).support = 1
参数：1 : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.support_single`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] 
{b : M} (a : α), b ≠ 0 → (fun₀ | a => b).support = {a}
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
lemma support_one [NeZero (1 : k)] : (1 : SkewMonoidAlgebra k G).support = 1 :=
  Finsupp.support_single _ one_ne_zero

end AddCommMonoidWithOne

section Semiring

variable [Monoid G] [Semiring k] [MulSemiringAction G k]
variable (f g : SkewMonoidAlgebra k G)

section DecidableEq

variable [DecidableEq G]

/-
**SkewMonoidAlgebra.support_mul** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：support_mul : (f * g).support subseteq f.support * g.support
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `SkewMonoidAlgebra.support_sum`：support_sum {k' G' : Type*} [DecidableEq 
G'] [AddCommMonoid k'] {f : SkewMonoidAlgebra k G} {g : G -> k -> SkewMonoidAlge
bra k' G'} : (f.sum…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.biUnion_subset`：biUnion_subset {s' : Finset β} : s.biUnion t subs
eteq s' ↔ forall x in s, t x subseteq s'
· 使用定理 `SkewMonoidAlgebra.support_single_subset`：support_single_subset : (single
 a b).support subseteq {a}
· 使用定理 `Finset.singleton_subset_iff`：singleton_subset_iff {s : Finset α} {a : α}
 : {a} subseteq s ↔ a in s
· 使用定理 `Finset.mem_image₂_of_mem`：mem_image₂_of_mem (ha : a in s) (hb : b in t) 
: f a b in image₂ f s t
-/
theorem support_mul : (f * g).support ⊆ f.support * g.support :=
  support_sum.trans <| biUnion_subset.2 fun _x hx ↦
    support_sum.trans <| biUnion_subset.2 fun _y hy ↦
      support_single_subset.trans <| singleton_subset_iff.2 <| mem_image₂_of_mem hx hy
/-
**SkewMonoidAlgebra.support_single_mul_subset** 是 Mathlib 中的一个定理，位于命名空间 `SkewMon
oidAlgebra`。
形式化陈述：support_single_mul_subset (r : k) (a : G) : (single a r * f : SkewMonoidAl
gebra k G).support subseteq Finset.image (a * ·) f.support
参数：r : k；a : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `SkewMonoidAlgebra.support_mul`：support_mul : (f * g).support subseteq f.
support * g.support
· 使用定理 `Finset.image₂_subset_right`：image₂_subset_right (hs : s subseteq s') : i
mage₂ f s t subseteq image₂ f s' t
· 使用定理 `SkewMonoidAlgebra.support_single_subset`：support_single_subset : (single
 a b).support subseteq {a}
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.image₂_singleton_left`：image₂_singleton_left : image₂ f {a} t = t
.image fun b => f a b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem support_single_mul_subset (r : k) (a : G) :
    (single a r * f : SkewMonoidAlgebra k G).support ⊆ Finset.image (a * ·) f.support :=
  (support_mul _ _).trans <| (Finset.image₂_subset_right support_single_subset).trans <| by
    rw [Finset.image₂_singleton_left]
/-
**SkewMonoidAlgebra.support_mul_single_subset** 是 Mathlib 中的一个定理，位于命名空间 `SkewMon
oidAlgebra`。
形式化陈述：support_mul_single_subset (r : k) (a : G) : (f * single a r).support subse
teq Finset.image (· * a) f.support
参数：r : k；a : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `SkewMonoidAlgebra.support_mul`：support_mul : (f * g).support subseteq f.
support * g.support
· 使用定理 `Finset.image₂_subset_left`：image₂_subset_left (ht : t subseteq t') : ima
ge₂ f s t subseteq image₂ f s t'
· 使用定理 `SkewMonoidAlgebra.support_single_subset`：support_single_subset : (single
 a b).support subseteq {a}
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.image₂_singleton_right`：image₂_singleton_right : image₂ f s {b} =
 s.image fun a => f a b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem support_mul_single_subset (r : k) (a : G) :
    (f * single a r).support ⊆ Finset.image (· * a) f.support :=
  (support_mul _ _).trans <| (Finset.image₂_subset_left support_single_subset).trans <| by
    rw [Finset.image₂_singleton_right]
/-
**SkewMonoidAlgebra.support_single_mul_eq_image** 是 Mathlib 中的一个定理，位于命名空间 `SkewM
onoidAlgebra`。
形式化陈述：support_single_mul_eq_image {r : k} {x : G} (lx : IsLeftRegular x) (hrx : 
forall y, r * x • y = 0 ↔ y = 0) : (single x r * f : SkewMonoidAlgebra k G).supp
ort = Finset.image (x * ·) f.support
参数：lx : IsLeftRegular x；hrx : forall y, r * x • y = 0 ↔ y = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `SkewMonoidAlgebra.support_single_mul_subset`：support_single_mul_subset (
r : k) (a : G) : (single a r * f : SkewMonoidAlgebra k G).support subseteq Finse
t.image (a * ·) f.support
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SkewMonoidAlgebra.coeff_mul`：coeff_mul [DecidableEq G] (f g : SkewMonoid
Algebra k G) (x : G) : (f * g).coeff x = f.sum fun a₁ b₁ => g.sum fun a₂ b₂ => i
f a₁ * a₂ = x the…
· 使用定理 `SkewMonoidAlgebra.sum_single_index`：sum_single_index {N} [AddCommMonoid 
N] {a : G} {b : k} {h : G -> k -> N} (h_zero : h a 0 = 0) : (SkewMonoidAlgebra.s
ingle a b).sum h = h a b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `SkewMonoidAlgebra.sum_zero`：sum_zero {N : Type*} [AddCommMonoid N] {f : 
SkewMonoidAlgebra k G} : (f.sum fun _ _ => (0 : N)) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SkewMonoidAlgebra.sum_ite_eq'`：sum_ite_eq' {N : Type*} [AddCommMonoid N]
 [DecidableEq G] (f : SkewMonoidAlgebra k G) (a : G) (b : G -> k -> N) : (f.sum 
fun (x : G) (v : k)…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SkewMonoidAlgebra.mem_support_iff`：mem_support_iff {f : SkewMonoidAlgebr
a k G} {a : G} : a in f.support ↔ f.coeff a != 0
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem support_single_mul_eq_image {r : k} {x : G} (lx : IsLeftRegular x)
    (hrx : ∀ y, r * x • y = 0 ↔ y = 0) :
    (single x r * f : SkewMonoidAlgebra k G).support = Finset.image (x * ·) f.support := by
  refine subset_antisymm (support_single_mul_subset f _ _) fun y hy ↦ ?_
  obtain ⟨y, yf, rfl⟩ : ∃ a : G, a ∈ f.support ∧ x * a = y := by
    simpa only [Finset.mem_image, exists_prop] using hy
  simp [coeff_mul, mem_support_iff.mp yf, hrx, mem_support_iff, sum_single_index, Ne,
    zero_mul, ite_self, sum_zero, lx.eq_iff]
/-
**SkewMonoidAlgebra.support_mul_single_eq_image** 是 Mathlib 中的一个定理，位于命名空间 `SkewM
onoidAlgebra`。
形式化陈述：support_mul_single_eq_image {r : k} {x : G} (rx : IsRightRegular x) (hrx :
 forall g : G, forall y, y * g • r = 0 ↔ y = 0) : (f * single x r).support = Fin
set.image (· * x) f.support
参数：rx : IsRightRegular x；hrx : forall g : G, forall y, y * g • r = 0 ↔ y = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `SkewMonoidAlgebra.support_mul_single_subset`：support_mul_single_subset (
r : k) (a : G) : (f * single a r).support subseteq Finset.image (· * a) f.suppor
t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.coeff_mul`：coeff_mul [DecidableEq G] (f g : SkewMonoid
Algebra k G) (x : G) : (f * g).coeff x = f.sum fun a₁ b₁ => g.sum fun a₂ b₂ => i
f a₁ * a₂ = x the…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SkewMonoidAlgebra.sum_single_index`：sum_single_index {N} [AddCommMonoid 
N] {a : G} {b : k} {h : G -> k -> N} (h_zero : h a 0 = 0) : (SkewMonoidAlgebra.s
ingle a b).sum h = h a b
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SkewMonoidAlgebra.sum_ite_eq'`：sum_ite_eq' {N : Type*} [AddCommMonoid N]
 [DecidableEq G] (f : SkewMonoidAlgebra k G) (a : G) (b : G -> k -> N) : (f.sum 
fun (x : G) (v : k)…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SkewMonoidAlgebra.mem_support_iff`：mem_support_iff {f : SkewMonoidAlgebr
a k G} {a : G} : a in f.support ↔ f.coeff a != 0
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem support_mul_single_eq_image {r : k} {x : G} (rx : IsRightRegular x)
    (hrx : ∀ g : G, ∀ y, y * g • r = 0 ↔ y = 0) :
    (f * single x r).support = Finset.image (· * x) f.support := by
  refine subset_antisymm (support_mul_single_subset f _ _) fun y hy ↦ ?_
  obtain ⟨y, yf, rfl⟩ : ∃ a : G, a ∈ f.support ∧ a * x = y := by
    simpa only [Finset.mem_image, exists_prop] using hy
  simp [coeff_mul, mem_support_iff.mp yf, hrx, mem_support_iff, sum_single_index, mul_zero,
    ite_self, rx.eq_iff]

end DecidableEq

/-
**SkewMonoidAlgebra.support_mul_single** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlge
bra`。
形式化陈述：support_mul_single [IsRightCancelMul G] (r : k) (x : G) (hrx : forall g : 
G, forall y, y * g • r = 0 ↔ y = 0) : (f * single x r).support = f.support.map (
mulRightEmbedding x)
参数：r : k；x : G；hrx : forall g : G, forall y, y * g • r = 0 ↔ y = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SkewMonoidAlgebra.support_mul_single_eq_image`：support_mul_single_eq_ima
ge {r : k} {x : G} (rx : IsRightRegular x) (hrx : forall g : G, forall y, y * g 
• r = 0 ↔ y = 0) : (f * single x r)…
· 使用定理 `IsRightRegular.all`：IsRightRegular.all [Mul R] [IsRightCancelMul R] (g :
 R) : IsRightRegular g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mulRightEmbedding_apply`：∀ {G : Type u_1} [inst : Mul G] [inst_1 : IsRig
htCancelMul G] (g h : G), (mulRightEmbedding g) h = h * g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem support_mul_single [IsRightCancelMul G] (r : k) (x : G)
    (hrx : ∀ g : G, ∀ y, y * g • r = 0 ↔ y = 0) :
    (f * single x r).support = f.support.map (mulRightEmbedding x) := by
  classical
  ext a
  simp [support_mul_single_eq_image f (IsRightRegular.all x) hrx]
/-
**SkewMonoidAlgebra.support_single_mul** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlge
bra`。
形式化陈述：support_single_mul [IsLeftCancelMul G] (r : k) (x : G) (hrx : forall y, r 
* x • y = 0 ↔ y = 0) : (single x r * f : SkewMonoidAlgebra k G).support = f.supp
ort.map (mulLeftEmbedding x)
参数：r : k；x : G；hrx : forall y, r * x • y = 0 ↔ y = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SkewMonoidAlgebra.support_single_mul_eq_image`：support_single_mul_eq_ima
ge {r : k} {x : G} (lx : IsLeftRegular x) (hrx : forall y, r * x • y = 0 ↔ y = 0
) : (single x r * f : SkewMonoidAlg…
· 使用定理 `IsLeftRegular.all`：IsLeftRegular.all [Mul R] [IsLeftCancelMul R] (g : R)
 : IsLeftRegular g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mulLeftEmbedding_apply`：∀ {G : Type u_1} [inst : Mul G] [inst_1 : IsLeft
CancelMul G] (g h : G), (mulLeftEmbedding g) h = g * h
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem support_single_mul [IsLeftCancelMul G] (r : k) (x : G)
    (hrx : ∀ y, r * x • y = 0 ↔ y = 0) :
    (single x r * f : SkewMonoidAlgebra k G).support = f.support.map (mulLeftEmbedding x) := by
  classical
  ext a
  simp [support_single_mul_eq_image f (IsLeftRegular.all x) hrx]

section Span

/-- An element of `SkewMonoidAlgebra k G` is in the subalgebra generated by its support. -/
/-
**SkewMonoidAlgebra.mem_span_support** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebr
a`。
形式化陈述：mem_span_support (f : SkewMonoidAlgebra k G) : f in Submodule.span k (of k
 G '' (f.support : Set G))
参数：f : SkewMonoidAlgebra k G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.mem_span_image_iff_exists_fun`：Fintype.mem_span_image_iff_exists
_fun {s : Set α} [Fintype s] : x in span R (v '' s) ↔ exists c : s -> R, ∑ i, c 
i • v i = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `SkewMonoidAlgebra.of_apply`：of_apply (a : G) : (of k G) a = single a 1
· 使用定理 `SkewMonoidAlgebra.smul_single`：smul_single {S} [SMulZeroClass S k] (s : 
S) (a : G) (b : k) : s • single a b = single a (s • b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finsupp.sum_attach_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : AddCommMonoid N] {s : Finset α} (f : α → M) {h : α → M → N},   ∑ x ∈ s
.attach, h (↑x…
· 使用定理 `SkewMonoidAlgebra.sum_single`：sum_single (f : SkewMonoidAlgebra k G) : f
.sum single = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
An element of `SkewMonoidAlgebra k G` is in the subalgebra generated by its supp
ort.
-/
theorem mem_span_support (f : SkewMonoidAlgebra k G) :
    f ∈ Submodule.span k (of k G '' (f.support : Set G)) := by
  rw [Fintype.mem_span_image_iff_exists_fun k]
  use Finset.restrict f.support f.coeff
  simp [smul_single, ← sum_def', sum_single]

end Span

end Semiring

end SkewMonoidAlgebra

