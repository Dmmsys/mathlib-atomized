/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Order.Filter.AtTopBot.Group

/-!
# Convergence to ±infinity in ordered rings
-/

public section

variable {α β : Type*}

namespace Filter

section OrderedSemiring

variable [Semiring α] [PartialOrder α] [IsOrderedRing α] {l : Filter β} {f g : β → α}

/-
**Filter.Tendsto.atTop_mul_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : CommMonoid M] [inst_1 : Preorder M
] [IsOrderedMonoid M] {l : Filter α}   {f g : α → M},   Filter.Tendsto f l Filte
r.atTop → Filter.Tendsto g l Filter.atTop → Filter.Tendsto (fun x => f x * g x) 
l Filter.atTop
参数：fun x => f x * g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.atTop_mul_one_eventuallyLE`：∀ {α : Type u_1} {M : Type u_
2} [inst : CommMonoid M] [inst_1 : Preorder M] [IsOrderedMonoid M] {l : Filter α
}   {f g : α → M}, Filter.Tends…
· 使用定理 `Filter.Tendsto.eventually_ge_atTop`：∀ {α : Type u_3} {β : Type u_4} [ins
t : Preorder β] {f : α → β} {l : Filter α},   Filter.Tendsto f l Filter.atTop → 
∀ (c : β), ∀ᶠ (x : α) in…
-/
theorem Tendsto.atTop_mul_atTop₀ (hf : Tendsto f l atTop) (hg : Tendsto g l atTop) :
    Tendsto (fun x => f x * g x) l atTop := by
  refine tendsto_atTop_mono' _ ?_ hg
  filter_upwards [hg.eventually (eventually_ge_atTop 0),
    hf.eventually (eventually_ge_atTop 1)] with _ using le_mul_of_one_le_left
/-
**Filter.tendsto_mul_self_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_mul_self_atTop : Tendsto (fun x : α => x * x) atTop atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.atTop_mul_atTop₀`：∀ {α : Type u_1} {β : Type u_2} [inst :
 Semiring α] [inst_1 : PartialOrder α] [IsOrderedRing α] {l : Filter β}   {f g :
 β → α},   Filter.Ten…
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
-/
theorem tendsto_mul_self_atTop : Tendsto (fun x : α => x * x) atTop atTop :=
  tendsto_id.atTop_mul_atTop₀ tendsto_id

/-- The monomial function `x^n` tends to `+∞` at `+∞` for any positive natural `n`.
A version for positive real powers exists as `tendsto_rpow_atTop`. -/
/-
**Filter.tendsto_pow_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_pow_atTop {n : Nat} (hn : n != 0) : Tendsto (fun x : α => x ^ n) a
tTop atTop
参数：hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_atTop_mono'`：tendsto_atTop_mono' [Preorder β] (l : Filter
 α) ⦃f₁ f₂ : α -> β⦄ (h : f₁ <=ᶠ[l] f₂) (h₁ : Tendsto f₁ l atTop) : Tendsto f₂ l
 atTop
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用引理 `le_self_pow₀`：le_self_pow₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 <
= a) (hn : n != 0) : a <= a ^ n
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x

--- 原说明 ---
The monomial function `x^n` tends to `+∞` at `+∞` for any positive natural `n`.
A version for positive real powers exists as `tendsto_rpow_atTop`.
-/
theorem tendsto_pow_atTop {n : ℕ} (hn : n ≠ 0) : Tendsto (fun x : α => x ^ n) atTop atTop :=
  tendsto_atTop_mono' _ ((eventually_ge_atTop 1).mono fun _x hx => le_self_pow₀ hx hn) tendsto_id

end OrderedSemiring

/-
**Filter.zero_pow_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：zero_pow_eventuallyEq [MonoidWithZero α] : (fun n : Nat => (0 : α) ^ n) =ᶠ
[atTop] fun _ => 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
-/
theorem zero_pow_eventuallyEq [MonoidWithZero α] :
    (fun n : ℕ => (0 : α) ^ n) =ᶠ[atTop] fun _ => 0 :=
  eventually_atTop.2 ⟨1, fun _n hn ↦ zero_pow <| Nat.one_le_iff_ne_zero.1 hn⟩

section OrderedRing

variable [Ring α] [PartialOrder α] [IsOrderedRing α] {l : Filter β} {f g : β → α}

/-
**Filter.Tendsto.atTop_mul_atBot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Tendsto.atTop_mul_atBot₀ (hf : Tendsto f l atTop) (hg : Tendsto g l atBot) :
    Tendsto (fun x => f x * g x) l atBot := by
  have := hf.atTop_mul_atTop₀ <| tendsto_neg_atBot_atTop.comp hg
  simpa only [Function.comp_def, neg_mul_eq_mul_neg, neg_neg] using
    tendsto_neg_atTop_atBot.comp this
/-
**Filter.Tendsto.atBot_mul_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Tendsto.atBot_mul_atTop₀ (hf : Tendsto f l atBot) (hg : Tendsto g l atTop) :
    Tendsto (fun x => f x * g x) l atBot := by
  have : Tendsto (fun x => -f x * g x) l atTop :=
    (tendsto_neg_atBot_atTop.comp hf).atTop_mul_atTop₀ hg
  simpa only [Function.comp_def, neg_mul_eq_neg_mul, neg_neg] using
    tendsto_neg_atTop_atBot.comp this
/-
**Filter.Tendsto.atBot_mul_atBot** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : CommMonoid M] [inst_1 : Preorder M
] [IsOrderedMonoid M] {l : Filter α}   {f g : α → M},   Filter.Tendsto f l Filte
r.atBot → Filter.Tendsto g l Filter.atBot → Filter.Tendsto (fun x => f x * g x) 
l Filter.atBot
参数：fun x => f x * g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.atTop_mul_atTop`：∀ {α : Type u_1} {M : Type u_2} [inst : 
CommMonoid M] [inst_1 : Preorder M] [IsOrderedMonoid M] {l : Filter α}   {f g : 
α → M},   Filter.Ten…
-/
theorem Tendsto.atBot_mul_atBot₀ (hf : Tendsto f l atBot) (hg : Tendsto g l atBot) :
    Tendsto (fun x => f x * g x) l atTop := by
  have : Tendsto (fun x => -f x * -g x) l atTop :=
    (tendsto_neg_atBot_atTop.comp hf).atTop_mul_atTop₀ (tendsto_neg_atBot_atTop.comp hg)
  simpa only [neg_mul_neg] using this

end OrderedRing

section LinearOrderedSemiring

variable [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] {l : Filter β} {f : β → α}

/-
**Filter.Tendsto.atTop_of_const_mul** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : CommMonoid M] [inst_1 : Preorder M
] [IsOrderedCancelMonoid M] {l : Filter α}   {f : α → M} (C : M), Filter.Tendsto
 (fun x => C * f x) l Filter.atTop → Filter.Tendsto f l Filter.atTop
参数：C : M；fun x => C * f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_atTop`：tendsto_atTop [Preorder β] {m : α -> β} {f : Filte
r α} : Tendsto m f atTop ↔ forall b, forallᶠ a in f, b <= m a
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_of_mul_le_mul_left'`：le_of_mul_le_mul_left' [MulLeftReflectLE α] {a b
 c : α} (bc : a * b <= a * c) : b <= c
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLE`：∀ {α : Type u_2} [inst : CommM
onoid α] [inst_1 : Preorder α] [IsOrderedCancelMonoid α], MulLeftReflectLE α
-/
theorem Tendsto.atTop_of_const_mul₀ {c : α} (hc : 0 < c) (hf : Tendsto (fun x => c * f x) l atTop) :
    Tendsto f l atTop :=
  tendsto_atTop.2 fun b => (tendsto_atTop.1 hf (c * b)).mono
    fun _x hx => le_of_mul_le_mul_left hx hc
/-
**Filter.Tendsto.atTop_of_mul_const** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : CommMonoid M] [inst_1 : Preorder M
] [IsOrderedCancelMonoid M] {l : Filter α}   {f : α → M} (C : M), Filter.Tendsto
 (fun x => f x * C) l Filter.atTop → Filter.Tendsto f l Filter.atTop
参数：C : M；fun x => f x * C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_atTop`：tendsto_atTop [Preorder β] {m : α -> β} {f : Filte
r α} : Tendsto m f atTop ↔ forall b, forallᶠ a in f, b <= m a
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_of_mul_le_mul_right'`：le_of_mul_le_mul_right' [MulRightReflectLE α] {
a b c : α} (bc : b * a <= c * a) : b <= c
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLE`：∀ {α : Type u_2} [inst : CommM
onoid α] [inst_1 : Preorder α] [IsOrderedCancelMonoid α], MulLeftReflectLE α
-/
theorem Tendsto.atTop_of_mul_const₀ {c : α} (hc : 0 < c) (hf : Tendsto (fun x => f x * c) l atTop) :
    Tendsto f l atTop :=
  tendsto_atTop.2 fun b => (tendsto_atTop.1 hf (b * c)).mono
    fun _x hx => le_of_mul_le_mul_right hx hc

@[simp]
/-
**Filter.tendsto_pow_atTop_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_pow_atTop_iff {n : Nat} : Tendsto (fun x : α => x ^ n) atTop atTop
 ↔ n != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `IsStrictOrderedRing.toNoMaxOrder`：∀ {R : Type u} [inst : Semiring R] [in
st_1 : PartialOrder R] [IsStrictOrderedRing R], NoMaxOrder R
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `IsStrictOrderedRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} {
inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], Nontrivial R
· 使用定理 `Filter.tendsto_pow_atTop`：tendsto_pow_atTop {n : Nat} (hn : n != 0) : Te
ndsto (fun x : α => x ^ n) atTop atTop
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
theorem tendsto_pow_atTop_iff {n : ℕ} : Tendsto (fun x : α => x ^ n) atTop atTop ↔ n ≠ 0 :=
  ⟨fun h hn => by simp only [hn, pow_zero, not_tendsto_const_atTop] at h, tendsto_pow_atTop⟩

end LinearOrderedSemiring

/-
**Filter.not_tendsto_pow_atTop_atBot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsStrictOrdered
Ring α] {n : ℕ},   ¬Filter.Tendsto (fun x => x ^ n) Filter.atTop Filter.atBot
参数：fun x => x ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `instNoBotOrderOfNoMinOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMinO
rder α], NoBotOrder α
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.isDomain`：∀ {R : Type u} [inst : Semiring R] [inst_1
 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], IsDomain R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Filter.Tendsto.not_tendsto`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} 
{a : Filter α} {b₁ b₂ : Filter β},   Filter.Tendsto f a b₁ → ∀ [a.NeBot], Disjoi
nt b₁ b₂ → ¬Filt…
· 使用定理 `Filter.tendsto_pow_atTop`：tendsto_pow_atTop {n : Nat} (hn : n != 0) : Te
ndsto (fun x : α => x ^ n) atTop atTop
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `Filter.disjoint_atTop_atBot`：∀ {α : Type u_3} [inst : PartialOrder α] [N
ontrivial α], Disjoint Filter.atTop Filter.atBot
-/
theorem not_tendsto_pow_atTop_atBot [Ring α] [LinearOrder α] [IsStrictOrderedRing α] :
    ∀ {n : ℕ}, ¬Tendsto (fun x : α => x ^ n) atTop atBot
  | 0 => by simp [not_tendsto_const_atBot]
  | n + 1 => (tendsto_pow_atTop n.succ_ne_zero).not_tendsto disjoint_atTop_atBot

end Filter

open Filter

variable {R : Type*} [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]

/-
**exists_lt_mul_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_lt_mul_self (a : R) : exists x >= 0, a < x * x
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `IsStrictOrderedRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} {
inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], Nontrivial R
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.tendsto_mul_self_atTop`：tendsto_mul_self_atTop : Tendsto (fun x :
 α => x * x) atTop atTop
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `IsStrictOrderedRing.toNoMaxOrder`：∀ {R : Type u} [inst : Semiring R] [in
st_1 : PartialOrder R] [IsStrictOrderedRing R], NoMaxOrder R
-/
theorem exists_lt_mul_self (a : R) : ∃ x ≥ 0, a < x * x :=
  ((eventually_ge_atTop 0).and (tendsto_mul_self_atTop.eventually (eventually_gt_atTop a))).exists
/-
**exists_le_mul_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_le_mul_self (a : R) : exists x >= 0, a <= x * x
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_lt_mul_self`：exists_lt_mul_self (a : R) : exists x >= 0, a < x * 
x
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem exists_le_mul_self (a : R) : ∃ x ≥ 0, a ≤ x * x :=
  let ⟨x, hx0, hxa⟩ := exists_lt_mul_self a
  ⟨x, hx0, hxa.le⟩
