/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.Monoid.OrderDual
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Order.Filter.AtTopBot.Tendsto

/-!
# Convergence to ±infinity in ordered commutative monoids
-/

public section

variable {α M : Type*}

namespace Filter

section OrderedCommMonoid

variable [CommMonoid M] [Preorder M] [IsOrderedMonoid M] {l : Filter α} {f g : α → M}

@[to_additive]
/-
**Filter.Tendsto.one_eventuallyLE_mul_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Te
ndsto`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : CommMonoid M] [inst_1 : Preorder M
] [IsOrderedMonoid M] {l : Filter α}   {f g : α → M}, 1 ≤ᶠ[l] f → Filter.Tendsto
 g l Filter.atTop → Filter.Tendsto (fun x => f x * g x) l Filter.atTop
参数：fun x => f x * g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_atTop_mono'`：tendsto_atTop_mono' [Preorder β] (l : Filter
 α) ⦃f₁ f₂ : α -> β⦄ (h : f₁ <=ᶠ[l] f₂) (h₁ : Tendsto f₁ l atTop) : Tendsto f₂ l
 atTop
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `le_mul_of_one_le_left'`：le_mul_of_one_le_left' [MulRightMono α] {a b : α
} (h : 1 <= b) : a <= b * a
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem Tendsto.one_eventuallyLE_mul_atTop (hf : 1 ≤ᶠ[l] f) (hg : Tendsto g l atTop) :
    Tendsto (fun x => f x * g x) l atTop :=
  tendsto_atTop_mono' l (hf.mono fun _ ↦ le_mul_of_one_le_left') hg

@[to_additive]
/-
**Filter.Tendsto.eventuallyLE_one_mul_atBot** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Te
ndsto`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : CommMonoid M] [inst_1 : Preorder M
] [IsOrderedMonoid M] {l : Filter α}   {f g : α → M}, f ≤ᶠ[l] 1 → Filter.Tendsto
 g l Filter.atBot → Filter.Tendsto (fun x => f x * g x) l Filter.atBot
参数：fun x => f x * g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.one_eventuallyLE_mul_atTop`：∀ {α : Type u_1} {M : Type u_
2} [inst : CommMonoid M] [inst_1 : Preorder M] [IsOrderedMonoid M] {l : Filter α
}   {f g : α → M}, 1 ≤ᶠ[l] f → …
-/
theorem Tendsto.eventuallyLE_one_mul_atBot (hf : f ≤ᶠ[l] 1) (hg : Tendsto g l atBot) :
    Tendsto (fun x => f x * g x) l atBot :=
  hg.one_eventuallyLE_mul_atTop (M := Mᵒᵈ) hf

@[to_additive]
/-
**Filter.Tendsto.one_le_mul_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : CommMonoid M] [inst_1 : Preorder M
] [IsOrderedMonoid M] {l : Filter α}   {f g : α → M},   (∀ (x : α), 1 ≤ f x) → F
ilter.Tendsto g l Filter.atTop → Filter.Tendsto (fun x => f x * g x) l Filter.at
Top
参数：∀ (x : α), 1 ≤ f x；fun x => f x * g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.one_eventuallyLE_mul_atTop`：∀ {α : Type u_1} {M : Type u_
2} [inst : CommMonoid M] [inst_1 : Preorder M] [IsOrderedMonoid M] {l : Filter α
}   {f g : α → M}, 1 ≤ᶠ[l] f → …
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
theorem Tendsto.one_le_mul_atTop (hf : ∀ x, 1 ≤ f x) (hg : Tendsto g l atTop) :
    Tendsto (fun x => f x * g x) l atTop :=
  hg.one_eventuallyLE_mul_atTop (.of_forall hf)

@[to_additive]
/-
**Filter.Tendsto.le_one_mul_atBot** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : CommMonoid M] [inst_1 : Preorder M
] [IsOrderedMonoid M] {l : Filter α}   {f g : α → M},   (∀ (x : α), f x ≤ 1) → F
ilter.Tendsto g l Filter.atBot → Filter.Tendsto (fun x => f x * g x) l Filter.at
Bot
参数：∀ (x : α), f x ≤ 1；fun x => f x * g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.eventuallyLE_one_mul_atBot`：∀ {α : Type u_1} {M : Type u_
2} [inst : CommMonoid M] [inst_1 : Preorder M] [IsOrderedMonoid M] {l : Filter α
}   {f g : α → M}, f ≤ᶠ[l] 1 → …
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
theorem Tendsto.le_one_mul_atBot (hf : ∀ x, f x ≤ 1) (hg : Tendsto g l atBot) :
    Tendsto (fun x => f x * g x) l atBot :=
  hg.eventuallyLE_one_mul_atBot (.of_forall hf)

@[to_additive]
/-
**Filter.Tendsto.atTop_mul_one_eventuallyLE** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Te
ndsto`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : CommMonoid M] [inst_1 : Preorder M
] [IsOrderedMonoid M] {l : Filter α}   {f g : α → M}, Filter.Tendsto f l Filter.
atTop → 1 ≤ᶠ[l] g → Filter.Tendsto (fun x => f x * g x) l Filter.atTop
参数：fun x => f x * g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_atTop_mono'`：tendsto_atTop_mono' [Preorder β] (l : Filter
 α) ⦃f₁ f₂ : α -> β⦄ (h : f₁ <=ᶠ[l] f₂) (h₁ : Tendsto f₁ l atTop) : Tendsto f₂ l
 atTop
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `le_mul_of_one_le_right'`：le_mul_of_one_le_right' [MulLeftMono α] {a b : 
α} (h : 1 <= b) : a <= a * b
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem Tendsto.atTop_mul_one_eventuallyLE (hf : Tendsto f l atTop) (hg : 1 ≤ᶠ[l] g) :
    Tendsto (fun x => f x * g x) l atTop :=
  tendsto_atTop_mono' l (hg.mono fun _ => le_mul_of_one_le_right') hf

@[to_additive]
/-
**Filter.Tendsto.atBot_mul_eventuallyLE_one** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Te
ndsto`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : CommMonoid M] [inst_1 : Preorder M
] [IsOrderedMonoid M] {l : Filter α}   {f g : α → M}, Filter.Tendsto f l Filter.
atBot → g ≤ᶠ[l] 1 → Filter.Tendsto (fun x => f x * g x) l Filter.atBot
参数：fun x => f x * g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.atTop_mul_one_eventuallyLE`：∀ {α : Type u_1} {M : Type u_
2} [inst : CommMonoid M] [inst_1 : Preorder M] [IsOrderedMonoid M] {l : Filter α
}   {f g : α → M}, Filter.Tends…
-/
theorem Tendsto.atBot_mul_eventuallyLE_one (hf : Tendsto f l atBot) (hg : g ≤ᶠ[l] 1) :
    Tendsto (fun x => f x * g x) l atBot :=
  hf.atTop_mul_one_eventuallyLE (M := Mᵒᵈ) hg

@[to_additive]
/-
**Filter.Tendsto.atTop_mul_one_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : CommMonoid M] [inst_1 : Preorder M
] [IsOrderedMonoid M] {l : Filter α}   {f g : α → M},   Filter.Tendsto f l Filte
r.atTop → (∀ (x : α), 1 ≤ g x) → Filter.Tendsto (fun x => f x * g x) l Filter.at
Top
参数：∀ (x : α), 1 ≤ g x；fun x => f x * g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.atTop_mul_one_eventuallyLE`：∀ {α : Type u_1} {M : Type u_
2} [inst : CommMonoid M] [inst_1 : Preorder M] [IsOrderedMonoid M] {l : Filter α
}   {f g : α → M}, Filter.Tends…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
theorem Tendsto.atTop_mul_one_le (hf : Tendsto f l atTop) (hg : ∀ x, 1 ≤ g x) :
    Tendsto (fun x => f x * g x) l atTop :=
  hf.atTop_mul_one_eventuallyLE <| .of_forall hg

@[to_additive]
/-
**Filter.Tendsto.atBot_mul_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : CommMonoid M] [inst_1 : Preorder M
] [IsOrderedMonoid M] {l : Filter α}   {f g : α → M},   Filter.Tendsto f l Filte
r.atBot → (∀ (x : α), g x ≤ 1) → Filter.Tendsto (fun x => f x * g x) l Filter.at
Bot
参数：∀ (x : α), g x ≤ 1；fun x => f x * g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.atBot_mul_eventuallyLE_one`：∀ {α : Type u_1} {M : Type u_
2} [inst : CommMonoid M] [inst_1 : Preorder M] [IsOrderedMonoid M] {l : Filter α
}   {f g : α → M}, Filter.Tends…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
theorem Tendsto.atBot_mul_le_one (hf : Tendsto f l atBot) (hg : ∀ x, g x ≤ 1) :
    Tendsto (fun x => f x * g x) l atBot :=
  hf.atBot_mul_eventuallyLE_one (.of_forall hg)

/-- In an ordered multiplicative monoid, if `f` and `g` tend to `+∞`, then so does `f * g`.

Earlier, this name was used for a similar lemma about semirings,
which is now called `Filter.Tendsto.atTop_mul_atTop₀`. -/
@[to_additive]
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

--- 原说明 ---
In an ordered multiplicative monoid, if `f` and `g` tend to `+∞`, then so does `
f * g`.

Earlier, this name was used for a similar lemma about semirings,
which is now called `Filter.Tendsto.atTop_mul_atTop₀`.
-/
theorem Tendsto.atTop_mul_atTop (hf : Tendsto f l atTop) (hg : Tendsto g l atTop) :
    Tendsto (fun x => f x * g x) l atTop :=
  hf.atTop_mul_one_eventuallyLE <| hg.eventually_ge_atTop 1

/-- In an ordered multiplicative monoid, if `f` and `g` tend to `-∞`, then so does `f * g`.

Earlier, this name was used for a similar lemma about rings (with conclusion `f * g → +∞`),
which is now called `Filter.Tendsto.atBot_mul_atBot₀`. -/
@[to_additive]
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

--- 原说明 ---
In an ordered multiplicative monoid, if `f` and `g` tend to `-∞`, then so does `
f * g`.

Earlier, this name was used for a similar lemma about rings (with conclusion `f 
* g → +∞`),
which is now called `Filter.Tendsto.atBot_mul_atBot₀`.
-/
theorem Tendsto.atBot_mul_atBot (hf : Tendsto f l atBot) (hg : Tendsto g l atBot) :
    Tendsto (fun x => f x * g x) l atBot :=
  hf.atTop_mul_atTop (M := Mᵒᵈ) hg

@[to_additive nsmul_atTop]
/-
**Filter.Tendsto.atTop_pow** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : CommMonoid M] [inst_1 : Preorder M
] [IsOrderedMonoid M] {l : Filter α}   {f : α → M}, Filter.Tendsto f l Filter.at
Top → ∀ {n : ℕ}, 0 < n → Filter.Tendsto (fun x => f x ^ n) l Filter.atTop
参数：fun x => f x ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_atTop_mono'`：tendsto_atTop_mono' [Preorder β] (l : Filter
 α) ⦃f₁ f₂ : α -> β⦄ (h : f₁ <=ᶠ[l] f₂) (h₁ : Tendsto f₁ l atTop) : Tendsto f₂ l
 atTop
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Tendsto.eventually_ge_atTop`：∀ {α : Type u_3} {β : Type u_4} [ins
t : Preorder β] {f : α → β} {l : Filter α},   Filter.Tendsto f l Filter.atTop → 
∀ (c : β), ∀ᶠ (x : α) in…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `pow_le_pow_right'`：pow_le_pow_right' {n m : Nat} (ha : 1 <= a) (h : n <=
 m) : a ^ n <= a ^ m
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem Tendsto.atTop_pow (hf : Tendsto f l atTop) {n : ℕ} (hn : 0 < n) :
    Tendsto (fun x => f x ^ n) l atTop := by
  refine tendsto_atTop_mono' _ ((hf.eventually_ge_atTop 1).mono fun x hx ↦ ?_) hf
  simpa only [pow_one] using pow_le_pow_right' hx hn

@[to_additive nsmul_atBot]
/-
**Filter.Tendsto.atBot_pow** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : CommMonoid M] [inst_1 : Preorder M
] [IsOrderedMonoid M] {l : Filter α}   {f : α → M}, Filter.Tendsto f l Filter.at
Bot → ∀ {n : ℕ}, 0 < n → Filter.Tendsto (fun x => f x ^ n) l Filter.atBot
参数：fun x => f x ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.atTop_pow`：∀ {α : Type u_1} {M : Type u_2} [inst : CommMo
noid M] [inst_1 : Preorder M] [IsOrderedMonoid M] {l : Filter α}   {f : α → M}, 
Filter.Tendsto…
-/
theorem Tendsto.atBot_pow (hf : Tendsto f l atBot) {n : ℕ} (hn : 0 < n) :
    Tendsto (fun x => f x ^ n) l atBot :=
  Tendsto.atTop_pow (M := Mᵒᵈ) hf hn

end OrderedCommMonoid

section OrderedCancelCommMonoid

variable [CommMonoid M] [Preorder M] [IsOrderedCancelMonoid M] {l : Filter α} {f g : α → M}

/-- In an ordered cancellative multiplicative monoid, if `C * f x → +∞`, then `f x → +∞`.

Earlier, this name was used for a similar lemma about ordered rings,
which is now called `Filter.Tendsto.atTop_of_const_mul₀`. -/
@[to_additive]
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

--- 原说明 ---
In an ordered cancellative multiplicative monoid, if `C * f x → +∞`, then `f x →
 +∞`.

Earlier, this name was used for a similar lemma about ordered rings,
which is now called `Filter.Tendsto.atTop_of_const_mul₀`.
-/
theorem Tendsto.atTop_of_const_mul (C : M) (hf : Tendsto (C * f ·) l atTop) : Tendsto f l atTop :=
  tendsto_atTop.2 fun b ↦ (tendsto_atTop.1 hf (C * b)).mono fun _ ↦ le_of_mul_le_mul_left'

@[to_additive]
/-
**Filter.Tendsto.atBot_of_const_mul** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : CommMonoid M] [inst_1 : Preorder M
] [IsOrderedCancelMonoid M] {l : Filter α}   {f : α → M} (C : M), Filter.Tendsto
 (fun x => C * f x) l Filter.atBot → Filter.Tendsto f l Filter.atBot
参数：C : M；fun x => C * f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.atTop_of_const_mul`：∀ {α : Type u_1} {M : Type u_2} [inst
 : CommMonoid M] [inst_1 : Preorder M] [IsOrderedCancelMonoid M] {l : Filter α} 
  {f : α → M} (C : M), …
-/
theorem Tendsto.atBot_of_const_mul (C : M) (hf : Tendsto (C * f ·) l atBot) : Tendsto f l atBot :=
  hf.atTop_of_const_mul (M := Mᵒᵈ)

/-- In an ordered cancellative multiplicative monoid, if `f x * C → +∞`, then `f x → +∞`.

Earlier, this name was used for a similar lemma about ordered rings,
which is now called `Filter.Tendsto.atTop_of_mul_const₀`. -/
@[to_additive]
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

--- 原说明 ---
In an ordered cancellative multiplicative monoid, if `f x * C → +∞`, then `f x →
 +∞`.

Earlier, this name was used for a similar lemma about ordered rings,
which is now called `Filter.Tendsto.atTop_of_mul_const₀`.
-/
theorem Tendsto.atTop_of_mul_const (C : M) (hf : Tendsto (f · * C) l atTop) : Tendsto f l atTop :=
  tendsto_atTop.2 fun b => (tendsto_atTop.1 hf (b * C)).mono fun _ => le_of_mul_le_mul_right'

@[to_additive]
/-
**Filter.Tendsto.atBot_of_mul_const** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : CommMonoid M] [inst_1 : Preorder M
] [IsOrderedCancelMonoid M] {l : Filter α}   {f : α → M} (C : M), Filter.Tendsto
 (fun x => f x * C) l Filter.atBot → Filter.Tendsto f l Filter.atBot
参数：C : M；fun x => f x * C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.atTop_of_mul_const`：∀ {α : Type u_1} {M : Type u_2} [inst
 : CommMonoid M] [inst_1 : Preorder M] [IsOrderedCancelMonoid M] {l : Filter α} 
  {f : α → M} (C : M), …
-/
theorem Tendsto.atBot_of_mul_const (C : M) (hf : Tendsto (f · * C) l atBot) : Tendsto f l atBot :=
  hf.atTop_of_mul_const (M := Mᵒᵈ)

/-- If `f` is eventually bounded from above along `l` and `f * g` tends to `+∞`,
then `g` tends to `+∞`. -/
@[to_additive /-- If `f` is eventually bounded from above along `l` and `f + g` tends to `+∞`,
then `g` tends to `+∞`. -/]
/-
**Filter.Tendsto.atTop_of_isBoundedUnder_le_mul** 是 Mathlib 中的一个定理，位于命名空间 `Filte
r.Tendsto`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : CommMonoid M] [inst_1 : Preorder M
] [IsOrderedCancelMonoid M] {l : Filter α}   {f g : α → M},   Filter.IsBoundedUn
der (fun x1 x2 => x1 ≤ x2) l f →     Filter.Tendsto (fun x => f x * g x) l Filte
r.atTop → Filter.Tendsto g l Filter.atTop
参数：fun x1 x2 => x1 ≤ x2；fun x => f x * g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.atTop_of_const_mul`：∀ {α : Type u_1} {M : Type u_2} [inst
 : CommMonoid M] [inst_1 : Preorder M] [IsOrderedCancelMonoid M] {l : Filter α} 
  {f : α → M} (C : M), …
· 使用定理 `Filter.tendsto_atTop_mono'`：tendsto_atTop_mono' [Preorder β] (l : Filter
 α) ⦃f₁ f₂ : α -> β⦄ (h : f₁ <=ᶠ[l] f₂) (h₁ : Tendsto f₁ l atTop) : Tendsto f₂ l
 atTop
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `IsOrderedCancelMonoid.toIsOrderedMonoid`：∀ {α : Type u_2} {inst : CommMo
noid α} {inst_1 : Preorder α} [self : IsOrderedCancelMonoid α], IsOrderedMonoid 
α
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem Tendsto.atTop_of_isBoundedUnder_le_mul (hf : IsBoundedUnder (· ≤ ·) l f)
    (hfg : Tendsto (fun x => f x * g x) l atTop) : Tendsto g l atTop := by
  obtain ⟨C, hC⟩ := hf
  refine .atTop_of_const_mul C <| tendsto_atTop_mono' l ?_ hfg
  exact (eventually_map.mp hC).mono fun _ _ ↦ by dsimp; gcongr

@[to_additive]
/-
**Filter.Tendsto.atBot_of_isBoundedUnder_ge_mul** 是 Mathlib 中的一个定理，位于命名空间 `Filte
r.Tendsto`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : CommMonoid M] [inst_1 : Preorder M
] [IsOrderedCancelMonoid M] {l : Filter α}   {f g : α → M},   Filter.IsBoundedUn
der (fun x1 x2 => x1 ≥ x2) l f →     Filter.Tendsto (fun x => f x * g x) l Filte
r.atBot → Filter.Tendsto g l Filter.atBot
参数：fun x1 x2 => x1 ≥ x2；fun x => f x * g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.atTop_of_isBoundedUnder_le_mul`：∀ {α : Type u_1} {M : Typ
e u_2} [inst : CommMonoid M] [inst_1 : Preorder M] [IsOrderedCancelMonoid M] {l 
: Filter α}   {f g : α → M},   Filt…
-/
theorem Tendsto.atBot_of_isBoundedUnder_ge_mul (hf : IsBoundedUnder (· ≥ ·) l f)
    (h : Tendsto (fun x => f x * g x) l atBot) : Tendsto g l atBot :=
  h.atTop_of_isBoundedUnder_le_mul (M := Mᵒᵈ) hf

@[to_additive]
/-
**Filter.Tendsto.atTop_of_le_const_mul** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto
`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : CommMonoid M] [inst_1 : Preorder M
] [IsOrderedCancelMonoid M] {l : Filter α}   {f g : α → M},   (∃ C, ∀ (x : α), f
 x ≤ C) → Filter.Tendsto (fun x => f x * g x) l Filter.atTop → Filter.Tendsto g 
l Filter.atTop
参数：∃ C, ∀ (x : α), f x ≤ C；fun x => f x * g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.atTop_of_isBoundedUnder_le_mul`：∀ {α : Type u_1} {M : Typ
e u_2} [inst : CommMonoid M] [inst_1 : Preorder M] [IsOrderedCancelMonoid M] {l 
: Filter α}   {f g : α → M},   Filt…
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
theorem Tendsto.atTop_of_le_const_mul (hf : ∃ C, ∀ x, f x ≤ C)
    (hfg : Tendsto (fun x ↦ f x * g x) l atTop) : Tendsto g l atTop :=
  hfg.atTop_of_isBoundedUnder_le_mul <| hf.imp fun _C hC ↦ eventually_map.mpr <| .of_forall hC

@[to_additive]
/-
**Filter.Tendsto.atBot_of_const_le_mul** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto
`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : CommMonoid M] [inst_1 : Preorder M
] [IsOrderedCancelMonoid M] {l : Filter α}   {f g : α → M},   (∃ C, ∀ (x : α), C
 ≤ f x) → Filter.Tendsto (fun x => f x * g x) l Filter.atBot → Filter.Tendsto g 
l Filter.atBot
参数：∃ C, ∀ (x : α), C ≤ f x；fun x => f x * g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.atTop_of_le_const_mul`：∀ {α : Type u_1} {M : Type u_2} [i
nst : CommMonoid M] [inst_1 : Preorder M] [IsOrderedCancelMonoid M] {l : Filter 
α}   {f g : α → M},   (∃ C…
-/
theorem Tendsto.atBot_of_const_le_mul (hf : ∃ C, ∀ x, C ≤ f x)
    (hfg : Tendsto (fun x ↦ f x * g x) l atBot) : Tendsto g l atBot :=
  Tendsto.atTop_of_le_const_mul (M := Mᵒᵈ) hf hfg

@[to_additive]
/-
**Filter.Tendsto.atTop_of_mul_isBoundedUnder_le** 是 Mathlib 中的一个定理，位于命名空间 `Filte
r.Tendsto`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : CommMonoid M] [inst_1 : Preorder M
] [IsOrderedCancelMonoid M] {l : Filter α}   {f g : α → M},   Filter.IsBoundedUn
der (fun x1 x2 => x1 ≤ x2) l g →     Filter.Tendsto (fun x => f x * g x) l Filte
r.atTop → Filter.Tendsto f l Filter.atTop
参数：fun x1 x2 => x1 ≤ x2；fun x => f x * g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.atTop_of_mul_const`：∀ {α : Type u_1} {M : Type u_2} [inst
 : CommMonoid M] [inst_1 : Preorder M] [IsOrderedCancelMonoid M] {l : Filter α} 
  {f : α → M} (C : M), …
· 使用定理 `Filter.tendsto_atTop_mono'`：tendsto_atTop_mono' [Preorder β] (l : Filter
 α) ⦃f₁ f₂ : α -> β⦄ (h : f₁ <=ᶠ[l] f₂) (h₁ : Tendsto f₁ l atTop) : Tendsto f₂ l
 atTop
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `IsOrderedCancelMonoid.toIsOrderedMonoid`：∀ {α : Type u_2} {inst : CommMo
noid α} {inst_1 : Preorder α} [self : IsOrderedCancelMonoid α], IsOrderedMonoid 
α
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem Tendsto.atTop_of_mul_isBoundedUnder_le (hg : IsBoundedUnder (· ≤ ·) l g)
    (h : Tendsto (fun x => f x * g x) l atTop) : Tendsto f l atTop := by
  obtain ⟨C, hC⟩ := hg
  refine .atTop_of_mul_const C <| tendsto_atTop_mono' l ?_ h
  exact (eventually_map.mp hC).mono fun _ _ ↦ by dsimp; gcongr

@[to_additive]
/-
**Filter.Tendsto.atBot_of_mul_isBoundedUnder_ge** 是 Mathlib 中的一个定理，位于命名空间 `Filte
r.Tendsto`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : CommMonoid M] [inst_1 : Preorder M
] [IsOrderedCancelMonoid M] {l : Filter α}   {f g : α → M},   Filter.IsBoundedUn
der (fun x1 x2 => x1 ≥ x2) l g →     Filter.Tendsto (fun x => f x * g x) l Filte
r.atBot → Filter.Tendsto f l Filter.atBot
参数：fun x1 x2 => x1 ≥ x2；fun x => f x * g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.atTop_of_mul_isBoundedUnder_le`：∀ {α : Type u_1} {M : Typ
e u_2} [inst : CommMonoid M] [inst_1 : Preorder M] [IsOrderedCancelMonoid M] {l 
: Filter α}   {f g : α → M},   Filt…
-/
theorem Tendsto.atBot_of_mul_isBoundedUnder_ge (hg : IsBoundedUnder (· ≥ ·) l g)
    (h : Tendsto (fun x => f x * g x) l atBot) : Tendsto f l atBot :=
  h.atTop_of_mul_isBoundedUnder_le (M := Mᵒᵈ) hg

@[to_additive]
/-
**Filter.Tendsto.atTop_of_mul_le_const** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto
`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : CommMonoid M] [inst_1 : Preorder M
] [IsOrderedCancelMonoid M] {l : Filter α}   {f g : α → M},   (∃ C, ∀ (x : α), g
 x ≤ C) → Filter.Tendsto (fun x => f x * g x) l Filter.atTop → Filter.Tendsto f 
l Filter.atTop
参数：∃ C, ∀ (x : α), g x ≤ C；fun x => f x * g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.atTop_of_mul_isBoundedUnder_le`：∀ {α : Type u_1} {M : Typ
e u_2} [inst : CommMonoid M] [inst_1 : Preorder M] [IsOrderedCancelMonoid M] {l 
: Filter α}   {f g : α → M},   Filt…
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
theorem Tendsto.atTop_of_mul_le_const (hg : ∃ C, ∀ x, g x ≤ C)
    (hfg : Tendsto (fun x ↦ f x * g x) l atTop) : Tendsto f l atTop :=
  hfg.atTop_of_mul_isBoundedUnder_le <| hg.imp fun _C hC ↦ eventually_map.mpr <| .of_forall hC

@[to_additive]
/-
**Filter.Tendsto.atBot_of_mul_const_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto
`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : CommMonoid M] [inst_1 : Preorder M
] [IsOrderedCancelMonoid M] {l : Filter α}   {f g : α → M},   (∃ C, ∀ (x : α), C
 ≤ g x) → Filter.Tendsto (fun x => f x * g x) l Filter.atBot → Filter.Tendsto f 
l Filter.atBot
参数：∃ C, ∀ (x : α), C ≤ g x；fun x => f x * g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.atTop_of_mul_le_const`：∀ {α : Type u_1} {M : Type u_2} [i
nst : CommMonoid M] [inst_1 : Preorder M] [IsOrderedCancelMonoid M] {l : Filter 
α}   {f g : α → M},   (∃ C…
-/
theorem Tendsto.atBot_of_mul_const_le (hg : ∃ C, ∀ x, C ≤ g x)
    (hfg : Tendsto (fun x ↦ f x * g x) l atBot) : Tendsto f l atBot :=
  Tendsto.atTop_of_mul_le_const (M := Mᵒᵈ) hg hfg

end OrderedCancelCommMonoid

end Filter

