/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Group.Embedding
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic

import Mathlib.LinearAlgebra.Span.Basic

/-!
# Lemmas about the support of a finitely supported function
-/

public section

open scoped Pointwise

universe u₁ u₂ u₃

namespace MonoidAlgebra

open Finset Finsupp

variable {k : Type u₁} {G : Type u₂} [Semiring k]

section Mul
variable [Mul G]

@[to_additive (dont_translate := k) support_coeff_mul_subset]
/-
**MonoidAlgebra.support_coeff_mul_subset** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebr
a`。
形式化陈述：support_coeff_mul_subset [DecidableEq G] (x y : k[G]) : (x * y).coeff.supp
ort subseteq x.coeff.support * y.coeff.support
参数：x y : k[G]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `MonoidAlgebra.mul_def`：mul_def (x y : R[M]) : x * y = x.coeff.sum fun m₁
 r₁ => y.coeff.sum fun m₂ r₂ => single (m₁ * m₂) (r₁ * r₂)
· 使用引理 `MonoidAlgebra.coeff_finsuppSum`：coeff_finsuppSum [AddCommMonoid N] (f : 
ι ->₀ N) (g : ι -> N -> R[M]) : coeff (f.sum g) = f.sum (fun i n => coeff (g i n
))
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Finsupp.support_sum`：support_sum [DecidableEq β] [Zero M] [AddCommMonoid
 N] {f : α ->₀ M} {g : α -> M -> β ->₀ N} : (f.sum g).support subseteq f.support
.biUnion …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `Finset.biUnion_subset`：biUnion_subset {s' : Finset β} : s.biUnion t subs
eteq s' ↔ forall x in s, t x subseteq s'
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finsupp.support_single_subset`：support_single_subset : (single a b).supp
ort subseteq {a}
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.singleton_subset_iff`：singleton_subset_iff {s : Finset α} {a : α}
 : {a} subseteq s ↔ a in s
· 使用定理 `Finset.mem_image₂_of_mem`：mem_image₂_of_mem (ha : a in s) (hb : b in t) 
: f a b in image₂ f s t
-/
theorem support_coeff_mul_subset [DecidableEq G] (x y : k[G]) :
    (x * y).coeff.support ⊆ x.coeff.support * y.coeff.support := by
  simp only [MonoidAlgebra.mul_def, coeff_finsuppSum]
  grw [Finsupp.support_sum, biUnion_subset]
  rintro x hx
  grw [Finsupp.support_sum, biUnion_subset]
  exact fun y hy ↦ support_single_subset.trans <| singleton_subset_iff.2 <| mem_image₂_of_mem hx hy

@[deprecated (since := "2026-06-18")] alias support_single_mul_eq_image := support_coeff_mul_subset

@[to_additive (dont_translate := k) support_coeff_single_mul_subset]
/-
**MonoidAlgebra.support_coeff_single_mul_subset** 是 Mathlib 中的一个引理，位于命名空间 `Monoi
dAlgebra`。
形式化陈述：support_coeff_single_mul_subset [DecidableEq G] (x : k[G]) (r : k) (a : G)
 : (single a r * x).coeff.support subseteq x.coeff.support.image (a * ·)
参数：x : k[G]；r : k；a : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `MonoidAlgebra.support_coeff_mul_subset`：support_coeff_mul_subset [Decida
bleEq G] (x y : k[G]) : (x * y).coeff.support subseteq x.coeff.support * y.coeff
.support
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonoidAlgebra.coeff_single`：coeff_single (m : M) (r : R) : (single m r).
coeff = .single m r
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `Finset.instMulLeftMono`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 
: Mul α], MulLeftMono (Finset α)
· 使用定理 `Finset.instMulRightMono`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1
 : Mul α], MulRightMono (Finset α)
· 使用定理 `Finsupp.support_single_subset`：support_single_subset : (single a b).supp
ort subseteq {a}
· 使用定理 `Finset.image₂_singleton_left`：image₂_singleton_left : image₂ f {a} t = t
.image fun b => f a b
-/
lemma support_coeff_single_mul_subset [DecidableEq G] (x : k[G]) (r : k) (a : G) :
    (single a r * x).coeff.support ⊆ x.coeff.support.image (a * ·) := by
  grw [support_coeff_mul_subset, coeff_single, support_single_subset]
  change image₂ _ _ _ ⊆ _
  rw [image₂_singleton_left]

@[to_additive (dont_translate := k) support_coeff_mul_single_subset]
/-
**MonoidAlgebra.support_coeff_mul_single_subset** 是 Mathlib 中的一个定理，位于命名空间 `Monoi
dAlgebra`。
形式化陈述：support_coeff_mul_single_subset [DecidableEq G] (x : k[G]) (r : k) (a : G)
 : (x * single a r).coeff.support subseteq x.coeff.support.image (· * a)
参数：x : k[G]；r : k；a : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `MonoidAlgebra.support_coeff_mul_subset`：support_coeff_mul_subset [Decida
bleEq G] (x y : k[G]) : (x * y).coeff.support subseteq x.coeff.support * y.coeff
.support
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonoidAlgebra.coeff_single`：coeff_single (m : M) (r : R) : (single m r).
coeff = .single m r
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `Finset.instMulLeftMono`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 
: Mul α], MulLeftMono (Finset α)
· 使用定理 `Finset.instMulRightMono`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1
 : Mul α], MulRightMono (Finset α)
· 使用定理 `Finsupp.support_single_subset`：support_single_subset : (single a b).supp
ort subseteq {a}
· 使用定理 `Finset.image₂_singleton_right`：image₂_singleton_right : image₂ f s {b} =
 s.image fun a => f a b
-/
theorem support_coeff_mul_single_subset [DecidableEq G] (x : k[G]) (r : k) (a : G) :
    (x * single a r).coeff.support ⊆ x.coeff.support.image (· * a) := by
  grw [support_coeff_mul_subset, coeff_single, support_single_subset]
  change image₂ _ _ _ ⊆ _
  rw [image₂_singleton_right]

set_option backward.isDefEq.respectTransparency false in
@[to_additive (dont_translate := k) support_coeff_single_mul_eq_image]
/-
**MonoidAlgebra.support_coeff_single_mul_eq_image** 是 Mathlib 中的一个定理，位于命名空间 `Mon
oidAlgebra`。
形式化陈述：support_coeff_single_mul_eq_image [DecidableEq G] (f : k[G]) {r : k} (hr :
 forall y, r * y = 0 ↔ y = 0) {x : G} (lx : IsLeftRegular x) : (single x r * f).
coeff.support = f.coeff.support.image (x * ·)
参数：f : k[G]；hr : forall y, r * y = 0 ↔ y = 0；lx : IsLeftRegular x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用引理 `MonoidAlgebra.support_coeff_single_mul_subset`：support_coeff_single_mul_
subset [DecidableEq G] (x : k[G]) (r : k) (a : G) : (single a r * x).coeff.suppo
rt subseteq x.coeff.support.image (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonoidAlgebra.coeff_mul`：coeff_mul [DecidableEq M] (x y : R[M]) (m : M) 
: (x * y).coeff m = x.coeff.sum fun m₁ r₁ => y.coeff.sum fun m₂ r₂ => if m₁ * m₂
 = m then r₁ …
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
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
· 使用定理 `Finsupp.sum_fun_zero`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [i
nst : Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M),   (f.sum fun x x_1 => 0) 
= 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finsupp.sum_ite_eq'`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [in
st : Zero M] [inst_1 : AddCommMonoid N] [inst_2 : DecidableEq α]   (f : α →₀ M) 
(a : α) (…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem support_coeff_single_mul_eq_image [DecidableEq G] (f : k[G]) {r : k}
    (hr : ∀ y, r * y = 0 ↔ y = 0) {x : G} (lx : IsLeftRegular x) :
    (single x r * f).coeff.support = f.coeff.support.image (x * ·) := by
  refine subset_antisymm (support_coeff_single_mul_subset f _ _) fun y hy => ?_
  obtain ⟨y, yf, rfl⟩ : ∃ a ∈ f.coeff.support, x * a = y := by grind
  simp [coeff_mul, mem_support_iff.mp yf, hr, lx.eq_iff]

set_option backward.isDefEq.respectTransparency false in
@[to_additive (dont_translate := k) support_coeff_mul_single_eq_image]
/-
**MonoidAlgebra.support_coeff_mul_single_eq_image** 是 Mathlib 中的一个定理，位于命名空间 `Mon
oidAlgebra`。
形式化陈述：support_coeff_mul_single_eq_image [DecidableEq G] (f : k[G]) {r : k} (hr :
 forall y, y * r = 0 ↔ y = 0) {x : G} (rx : IsRightRegular x) : (f * single x r)
.coeff.support = Finset.image (· * x) f.coeff.support
参数：f : k[G]；hr : forall y, y * r = 0 ↔ y = 0；rx : IsRightRegular x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `MonoidAlgebra.support_coeff_mul_single_subset`：support_coeff_mul_single_
subset [DecidableEq G] (x : k[G]) (r : k) (a : G) : (x * single a r).coeff.suppo
rt subseteq x.coeff.support.image (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonoidAlgebra.coeff_mul`：coeff_mul [DecidableEq M] (x y : R[M]) (m : M) 
: (x * y).coeff m = x.coeff.sum fun m₁ r₁ => y.coeff.sum fun m₂ r₂ => if m₁ * m₂
 = m then r₁ …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finsupp.sum_ite_eq'`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [in
st : Zero M] [inst_1 : AddCommMonoid N] [inst_2 : DecidableEq α]   (f : α →₀ M) 
(a : α) (…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem support_coeff_mul_single_eq_image [DecidableEq G] (f : k[G]) {r : k}
    (hr : ∀ y, y * r = 0 ↔ y = 0) {x : G} (rx : IsRightRegular x) :
    (f * single x r).coeff.support = Finset.image (· * x) f.coeff.support := by
  refine subset_antisymm (support_coeff_mul_single_subset f _ _) fun y hy => ?_
  obtain ⟨y, yf, rfl⟩ : ∃ a : G, a ∈ f.coeff.support ∧ a * x = y := by grind
  simp [coeff_mul, mem_support_iff.mp yf, hr, rx.eq_iff]

@[deprecated (since := "2026-06-18")]
alias support_mul_single_eq_image := support_coeff_mul_single_eq_image

@[to_additive (dont_translate := k) support_coeff_mul_single]
/-
**MonoidAlgebra.support_coeff_mul_single** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebr
a`。
形式化陈述：support_coeff_mul_single [IsRightCancelMul G] (f : k[G]) (r : k) (hr : for
all y, y * r = 0 ↔ y = 0) (x : G) : (f * single x r).coeff.support = f.coeff.sup
port.map (mulRightEmbedding x)
参数：f : k[G]；r : k；hr : forall y, y * r = 0 ↔ y = 0；x : G。
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
· 使用定理 `MonoidAlgebra.support_coeff_mul_single_eq_image`：support_coeff_mul_singl
e_eq_image [DecidableEq G] (f : k[G]) {r : k} (hr : forall y, y * r = 0 ↔ y = 0)
 {x : G} (rx : IsRightRegular x) : (f…
· 使用定理 `IsRightRegular.all`：IsRightRegular.all [Mul R] [IsRightCancelMul R] (g :
 R) : IsRightRegular g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mulRightEmbedding_apply`：∀ {G : Type u_1} [inst : Mul G] [inst_1 : IsRig
htCancelMul G] (g h : G), (mulRightEmbedding g) h = h * g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem support_coeff_mul_single [IsRightCancelMul G] (f : k[G]) (r : k)
    (hr : ∀ y, y * r = 0 ↔ y = 0) (x : G) :
    (f * single x r).coeff.support = f.coeff.support.map (mulRightEmbedding x) := by
  classical ext; simp [support_coeff_mul_single_eq_image f hr (.all x)]

@[deprecated (since := "2026-06-18")] alias support_mul_single := support_coeff_mul_single

@[to_additive (dont_translate := k) support_coeff_single_mul]
/-
**MonoidAlgebra.support_coeff_single_mul** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebr
a`。
形式化陈述：support_coeff_single_mul [IsLeftCancelMul G] (f : k[G]) (r : k) (hr : fora
ll y, r * y = 0 ↔ y = 0) (x : G) : (single x r * f : k[G]).coeff.support = f.coe
ff.support.map (mulLeftEmbedding x)
参数：f : k[G]；r : k；hr : forall y, r * y = 0 ↔ y = 0；x : G。
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
· 使用定理 `MonoidAlgebra.support_coeff_single_mul_eq_image`：support_coeff_single_mu
l_eq_image [DecidableEq G] (f : k[G]) {r : k} (hr : forall y, r * y = 0 ↔ y = 0)
 {x : G} (lx : IsLeftRegular x) : (si…
· 使用定理 `IsLeftRegular.all`：IsLeftRegular.all [Mul R] [IsLeftCancelMul R] (g : R)
 : IsLeftRegular g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mulLeftEmbedding_apply`：∀ {G : Type u_1} [inst : Mul G] [inst_1 : IsLeft
CancelMul G] (g h : G), (mulLeftEmbedding g) h = g * h
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem support_coeff_single_mul [IsLeftCancelMul G] (f : k[G]) (r : k)
    (hr : ∀ y, r * y = 0 ↔ y = 0) (x : G) :
    (single x r * f : k[G]).coeff.support =
      f.coeff.support.map (mulLeftEmbedding x) := by
  classical ext; simp [support_coeff_single_mul_eq_image f hr (.all x)]

@[deprecated (since := "2026-06-18")] alias support_single_mul := support_coeff_single_mul

end Mul

@[to_additive (dont_translate := k) support_coeff_one_subset]
/-
**MonoidAlgebra.support_coeff_one_subset** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebr
a`。
形式化陈述：support_coeff_one_subset [One G] : (1 : k[G]).coeff.support subseteq 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.support_single_subset`：support_single_subset : (single a b).supp
ort subseteq {a}
-/
lemma support_coeff_one_subset [One G] : (1 : k[G]).coeff.support ⊆ 1 :=
  Finsupp.support_single_subset

@[deprecated (since := "2026-06-18")] alias support_one_subset := support_coeff_one_subset

@[to_additive (dont_translate := k) (attr := simp) support_coeff_one]
/-
**MonoidAlgebra.support_coeff_one** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：support_coeff_one [One G] [NeZero (1 : k)] : (1 : k[G]).coeff.support = 1
参数：1 : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.support_single`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] 
{b : M} (a : α), b ≠ 0 → (fun₀ | a => b).support = {a}
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
lemma support_coeff_one [One G] [NeZero (1 : k)] : (1 : k[G]).coeff.support = 1 :=
  Finsupp.support_single _ one_ne_zero

@[deprecated (since := "2026-06-18")] alias support_one := support_coeff_one

section Span

/-- An element of `k[G]` is in the subalgebra generated by its support. -/
/-
**MonoidAlgebra.mem_span_support_coeff** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebra`
。
形式化陈述：mem_span_support_coeff [MulOneClass G] (f : k[G]) : f in Submodule.span k 
(of k G '' f.coeff.support)
参数：f : k[G]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `MonoidAlgebra.ofMagma_apply`：∀ (R : Type u_8) (M : Type u_9) [inst : Sem
iring R] [inst_1 : Mul M] (a : M),   (MonoidAlgebra.ofMagma R M) a = MonoidAlgeb
ra.single a 1

--- 原说明 ---
An element of `k[G]` is in the subalgebra generated by its support.
-/
theorem mem_span_support_coeff [MulOneClass G] (f : k[G]) :
    f ∈ Submodule.span k (of k G '' f.coeff.support) := by
  simp [of, ← supported_eq_span_single, mem_supported]

@[deprecated (since := "2026-06-18")] alias mem_span_support := mem_span_support_coeff

end Span

end MonoidAlgebra

namespace AddMonoidAlgebra

open Finset Finsupp MulOpposite

variable {k : Type u₁} {G : Type u₂} [Semiring k]

section Span

set_option backward.isDefEq.respectTransparency.types false in
/-- An element of `k[G]` is in the submodule generated by its support. -/
/-
**AddMonoidAlgebra.mem_span_support_coeff** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAl
gebra`。
形式化陈述：mem_span_support_coeff (f : k[G]) : f in Submodule.span k (of' k G '' f.co
eff.support)
参数：f : k[G]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s

--- 原说明 ---
An element of `k[G]` is in the submodule generated by its support.
-/
theorem mem_span_support_coeff (f : k[G]) : f ∈ Submodule.span k (of' k G '' f.coeff.support) := by
  simp [of', ← supported_eq_span_single, mem_supported]

@[deprecated (since := "2026-06-18")] alias mem_span_support := mem_span_support_coeff

end Span

end AddMonoidAlgebra

