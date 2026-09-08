/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Normed.Field.Basic

/-!
# Asymptotics

We introduce these relations:

* `IsBigOWith c l f g` : "f is big O of g along l with constant c";
* `f =O[l] g` : "f is big O of g along l";
* `f =Θ[l] g` : "f is big O of g along l and vice versa";
* `f =o[l] g` : "f is little o of g along l";
* `f ~[l] g` : `f` and `g` are equivalent, i.e., `f - g =o[l] g`.

Here `l` is any filter on the domain of `f` and `g`, which are assumed to be the same. The codomains
of `f` and `g` do not need to be the same; all that is needed is that there is a norm associated
with these types, and it is the norm that is compared asymptotically.

The relation `IsBigOWith c` is introduced to factor out common algebraic arguments in the proofs of
similar properties of `IsBigO` and `IsLittleO`. Usually proofs outside of this file should use
`IsBigO` instead.

Often the ranges of `f` and `g` will be the real numbers, in which case the norm is the absolute
value. In general, we have

  `f =O[l] g ↔ (fun x ↦ ‖f x‖) =O[l] (fun x ↦ ‖g x‖)`,

and similarly for `IsLittleO`. But our setup allows us to use the notions e.g. with functions
to the integers, rationals, complex numbers, or any normed vector space without mentioning the
norm explicitly.

If `f` and `g` are functions to a normed field like the reals or complex numbers and `g` is always
nonzero, we have

  `f =o[l] g ↔ Tendsto (fun x ↦ f x / (g x)) l (𝓝 0)`.

In fact, the right-to-left direction holds without the hypothesis on `g`, and in the other direction
it suffices to assume that `f` is zero wherever `g` is. (This generalization is useful in defining
the Fréchet derivative.)

Sometimes Landau notation may be embedded in more complex expressions, such as
$f(n) = n ^ {1 + O(g(n))}$. This can be expressed using the existential pattern, for example:

  `∃ (e : ℕ → ℝ) (he : e =O[l] g), f =ᶠ[l] fun n ↦ n ^ (1 + e n)`.

-/

set_option linter.style.longFile 1600

@[expose] public section

assert_not_exists IsBoundedSMul Summable OpenPartialHomeomorph BoundedLENhdsClass

open Set Topology Filter NNReal

namespace Asymptotics


variable {α : Type*} {β : Type*} {E : Type*} {F : Type*} {G : Type*} {E' : Type*}
  {F' : Type*} {G' : Type*} {E'' : Type*} {F'' : Type*} {G'' : Type*} {E''' : Type*}
  {R : Type*} {R' : Type*} {𝕜 : Type*} {𝕜' : Type*}

variable [Norm E] [Norm F] [Norm G]
variable [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F'] [SeminormedAddCommGroup G']
  [NormedAddCommGroup E''] [NormedAddCommGroup F''] [NormedAddCommGroup G''] [SeminormedRing R]
  [SeminormedAddGroup E''']
  [SeminormedRing R']

variable {S : Type*} [NormedRing S] [NormMulClass S]
variable [NormedDivisionRing 𝕜] [NormedDivisionRing 𝕜']
variable {c c' c₁ c₂ : ℝ} {f : α → E} {g : α → F} {k : α → G}
variable {f' : α → E'} {g' : α → F'} {k' : α → G'}
variable {f'' : α → E''} {g'' : α → F''} {k'' : α → G''}
variable {l l' : Filter α}

section Defs

/-! ### Definitions -/


/-- This version of the Landau notation `IsBigOWith C l f g` where `f` and `g` are two functions on
a type `α` and `l` is a filter on `α`, means that eventually for `l`, `‖f‖` is bounded by `C * ‖g‖`.
In other words, `‖f‖ / ‖g‖` is eventually bounded by `C`, modulo division by zero issues that are
avoided by this definition. Probably you want to use `IsBigO` instead of this relation. -/
irreducible_def IsBigOWith (c : ℝ) (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖

/-- Definition of `IsBigOWith`. We record it in a lemma as `IsBigOWith` is irreducible. -/
/-
**Asymptotics.isBigOWith_iff** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOWith_iff : IsBigOWith c l f g ↔ forallᶠ x in l, ‖f x‖ <= c * ‖g x‖
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.IsBigOWith_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type 
u_20} [inst : Norm E] [inst_1 : Norm F] (c : ℝ) (l : Filter α) (f : α → E)   (g 
: α → F), Asympt…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Definition of `IsBigOWith`. We record it in a lemma as `IsBigOWith` is irreducib
le.
-/
theorem isBigOWith_iff : IsBigOWith c l f g ↔ ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ := by rw [IsBigOWith_def]

alias ⟨IsBigOWith.bound, IsBigOWith.of_bound⟩ := isBigOWith_iff

/-- The Landau notation `f =O[l] g` where `f` and `g` are two functions on a type `α` and `l` is
a filter on `α`, means that eventually for `l`, `‖f‖` is bounded by a constant multiple of `‖g‖`.
In other words, `‖f‖ / ‖g‖` is eventually bounded, modulo division by zero issues that are avoided
by this definition. -/
irreducible_def IsBigO (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  ∃ c : ℝ, IsBigOWith c l f g

@[inherit_doc]
notation:100 f " =O[" l "] " g:100 => IsBigO l f g

/-- Definition of `IsBigO` in terms of `IsBigOWith`. We record it in a lemma as `IsBigO` is
irreducible. -/
/-
**Asymptotics.isBigO_iff_isBigOWith** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_iff_isBigOWith : f =O[l] g ↔ exists c : Real, IsBigOWith c l f g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.IsBigO_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type u_20
} [inst : Norm E] [inst_1 : Norm F] (l : Filter α) (f : α → E)   (g : α → F), f 
=O[l] g = ∃ …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Definition of `IsBigO` in terms of `IsBigOWith`. We record it in a lemma as `IsB
igO` is
irreducible.
-/
theorem isBigO_iff_isBigOWith : f =O[l] g ↔ ∃ c : ℝ, IsBigOWith c l f g := by rw [IsBigO_def]

/-- Definition of `IsBigO` in terms of filters. -/
/-
**Asymptotics.isBigO_iff** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_iff : f =O[l] g ↔ exists c : Real, forallᶠ x in l, ‖f x‖ <= c * ‖g 
x‖
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.IsBigO_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type u_20
} [inst : Norm E] [inst_1 : Norm F] (l : Filter α) (f : α → E)   (g : α → F), f 
=O[l] g = ∃ …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Asymptotics.IsBigOWith_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type 
u_20} [inst : Norm E] [inst_1 : Norm F] (c : ℝ) (l : Filter α) (f : α → E)   (g 
: α → F), Asympt…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Definition of `IsBigO` in terms of filters.
-/
theorem isBigO_iff : f =O[l] g ↔ ∃ c : ℝ, ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ := by
  simp only [IsBigO_def, IsBigOWith_def]

/-- Definition of `IsBigO` in terms of filters, with a positive constant. -/
/-
**Asymptotics.isBigO_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_iff' {g : α -> E'''} : f =O[l] g ↔ exists c > 0, forallᶠ x in l, ‖f
 x‖ <= c * ‖g x‖
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.isBigO_iff`：isBigO_iff : f =O[l] g ↔ exists c : Real, forall
ᶠ x in l, ‖f x‖ <= c * ‖g x‖
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖

--- 原说明 ---
Definition of `IsBigO` in terms of filters, with a positive constant.
-/
theorem isBigO_iff' {g : α → E'''} :
    f =O[l] g ↔ ∃ c > 0, ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ := by
  refine ⟨fun h => ?mp, fun h => ?mpr⟩
  case mp =>
    rw [isBigO_iff] at h
    obtain ⟨c, hc⟩ := h
    refine ⟨max c 1, zero_lt_one.trans_le (le_max_right _ _), ?_⟩
    filter_upwards [hc] with x hx
    apply hx.trans
    gcongr
    exact le_max_left _ _
  case mpr =>
    rw [isBigO_iff]
    obtain ⟨c, ⟨_, hc⟩⟩ := h
    exact ⟨c, hc⟩

/-- Definition of `IsBigO` in terms of filters, with the constant in the lower bound. -/
/-
**Asymptotics.isBigO_iff''** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_iff'' {g : α -> E'''} : f =O[l] g ↔ exists c > 0, forallᶠ x in l, c
 * ‖f x‖ <= ‖g x‖
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.isBigO_iff'`：isBigO_iff' {g : α -> E'''} : f =O[l] g ↔ exist
s c > 0, forallᶠ x in l, ‖f x‖ <= c * ‖g x‖
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `inv_mul_le_iff₀`：inv_mul_le_iff₀ (hc : 0 < c) : c⁻¹ * b <= a ↔ b <= c * 
a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a

--- 原说明 ---
Definition of `IsBigO` in terms of filters, with the constant in the lower bound
.
-/
theorem isBigO_iff'' {g : α → E'''} :
    f =O[l] g ↔ ∃ c > 0, ∀ᶠ x in l, c * ‖f x‖ ≤ ‖g x‖ := by
  refine ⟨fun h => ?mp, fun h => ?mpr⟩
  case mp =>
    rw [isBigO_iff'] at h
    obtain ⟨c, ⟨hc_pos, hc⟩⟩ := h
    refine ⟨c⁻¹, ⟨by positivity, ?_⟩⟩
    filter_upwards [hc] with x hx
    rwa [inv_mul_le_iff₀ (by positivity)]
  case mpr =>
    rw [isBigO_iff']
    obtain ⟨c, ⟨hc_pos, hc⟩⟩ := h
    refine ⟨c⁻¹, ⟨by positivity, ?_⟩⟩
    filter_upwards [hc] with x hx
    rwa [← inv_inv c, inv_mul_le_iff₀ (by positivity)] at hx
/-
**Asymptotics.IsBigO.of_bound** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : N
orm F] {f : α → E} {g : α → F} {l : Filter α}   (c : ℝ), (∀ᶠ (x : α) in l, ‖f x‖
 ≤ c * ‖g x‖) → f =O[l] g
参数：c : ℝ；∀ᶠ (x : α) in l, ‖f x‖ ≤ c * ‖g x‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Asymptotics.isBigO_iff`：isBigO_iff : f =O[l] g ↔ exists c : Real, forall
ᶠ x in l, ‖f x‖ <= c * ‖g x‖
-/
theorem IsBigO.of_bound (c : ℝ) (h : ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖) : f =O[l] g :=
  isBigO_iff.2 ⟨c, h⟩
/-
**Asymptotics.IsBigO.of_bound'** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : N
orm F] {f : α → E} {g : α → F} {l : Filter α},   (∀ᶠ (x : α) in l, ‖f x‖ ≤ ‖g x‖
) → f =O[l] g
参数：∀ᶠ (x : α) in l, ‖f x‖ ≤ ‖g x‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.of_bound`：∀ {α : Type u_1} {E : Type u_3} {F : Type u
_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α}   (
c : ℝ), (∀ᶠ (x : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem IsBigO.of_bound' (h : ∀ᶠ x in l, ‖f x‖ ≤ ‖g x‖) : f =O[l] g :=
  .of_bound 1 <| by simpa only [one_mul] using h
/-
**Asymptotics.IsBigO.bound** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : N
orm F] {f : α → E} {g : α → F} {l : Filter α},   f =O[l] g → ∃ c, ∀ᶠ (x : α) in 
l, ‖f x‖ ≤ c * ‖g x‖
参数：x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Asymptotics.isBigO_iff`：isBigO_iff : f =O[l] g ↔ exists c : Real, forall
ᶠ x in l, ‖f x‖ <= c * ‖g x‖
-/
theorem IsBigO.bound : f =O[l] g → ∃ c : ℝ, ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ :=
  isBigO_iff.1

/-- See also `Filter.Eventually.isBigO`, which is the same lemma
stated using `Filter.Eventually` instead of `Filter.EventuallyLE`. -/
/-
**Asymptotics.IsBigO.of_norm_eventuallyLE** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics
.IsBigO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} [inst : Norm E] {f : α → E} {l : Filter α}
 {g : α → ℝ},   (fun x => ‖f x‖) ≤ᶠ[l] g → f =O[l] g
参数：fun x => ‖f x‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.of_bound'`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},  
 (∀ᶠ (x : α) in l,…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|

--- 原说明 ---
See also `Filter.Eventually.isBigO`, which is the same lemma
stated using `Filter.Eventually` instead of `Filter.EventuallyLE`.
-/
theorem IsBigO.of_norm_eventuallyLE {g : α → ℝ} (h : (‖f ·‖) ≤ᶠ[l] g) : f =O[l] g :=
  .of_bound' <| h.mono fun _ h ↦ h.trans <| le_abs_self _
/-
**Asymptotics.IsBigO.of_norm_le** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} [inst : Norm E] {f : α → E} {l : Filter α}
 {g : α → ℝ},   (∀ (x : α), ‖f x‖ ≤ g x) → f =O[l] g
参数：∀ (x : α), ‖f x‖ ≤ g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.of_norm_eventuallyLE`：∀ {α : Type u_1} {E : Type u_3}
 [inst : Norm E] {f : α → E} {l : Filter α} {g : α → ℝ},   (fun x => ‖f x‖) ≤ᶠ[l
] g → f =O[l] g
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
theorem IsBigO.of_norm_le {g : α → ℝ} (h : ∀ x, ‖f x‖ ≤ g x) : f =O[l] g :=
  .of_norm_eventuallyLE <| .of_forall h

/-- We say that `f` is `Θ(g)` along a filter `l` (notation: `f =Θ[l] g`) if `f =O[l] g` and
`g =O[l] f`. -/
/-
**Asymptotics.IsTheta** 是 Mathlib 中的一个定义，位于命名空间 `Asymptotics`。
形式化陈述：IsTheta (l : Filter α) (f : α -> E) (g : α -> F) : Prop
参数：l : Filter α；f : α -> E；g : α -> F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that `f` is `Θ(g)` along a filter `l` (notation: `f =Θ[l] g`) if `f =O[l]
 g` and
`g =O[l] f`.
-/
def IsTheta (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  IsBigO l f g ∧ IsBigO l g f

@[inherit_doc]
notation:100 f " =Θ[" l "] " g:100 => IsTheta l f g
/-
**Asymptotics.IsBigO.antisymm** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : N
orm F] {f : α → E} {g : α → F} {l : Filter α},   f =O[l] g → g =O[l] f → f =Θ[l]
 g
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsBigO.antisymm (h₁ : f =O[l] g) (h₂ : g =O[l] f) : f =Θ[l] g :=
  ⟨h₁, h₂⟩
/-
**Asymptotics.IsTheta.isBigO** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsTheta`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : N
orm F] {f : α → E} {g : α → F} {l : Filter α},   f =Θ[l] g → f =O[l] g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma IsTheta.isBigO (h : f =Θ[l] g) : f =O[l] g := h.1
/-
**Asymptotics.IsTheta.isBigO_symm** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsTheta
`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : N
orm F] {f : α → E} {g : α → F} {l : Filter α},   f =Θ[l] g → g =O[l] f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma IsTheta.isBigO_symm (h : f =Θ[l] g) : g =O[l] f := h.2

/-- The Landau notation `f =o[l] g` where `f` and `g` are two functions on a type `α` and `l` is
a filter on `α`, means that eventually for `l`, `‖f‖` is bounded by an arbitrarily small constant
multiple of `‖g‖`. In other words, `‖f‖ / ‖g‖` tends to `0` along `l`, modulo division by zero
issues that are avoided by this definition. -/
irreducible_def IsLittleO (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  ∀ ⦃c : ℝ⦄, 0 < c → IsBigOWith c l f g

@[inherit_doc]
notation:100 f " =o[" l "] " g:100 => IsLittleO l f g

/-- Definition of `IsLittleO` in terms of `IsBigOWith`. -/
/-
**Asymptotics.isLittleO_iff_forall_isBigOWith** 是 Mathlib 中的一个定理，位于命名空间 `Asympto
tics`。
形式化陈述：isLittleO_iff_forall_isBigOWith : f =o[l] g ↔ forall ⦃c : Real⦄, 0 < c -> 
IsBigOWith c l f g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.IsLittleO_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type u
_20} [inst : Norm E] [inst_1 : Norm F] (l : Filter α) (f : α → E)   (g : α → F),
 f =o[l] g = ∀ …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Definition of `IsLittleO` in terms of `IsBigOWith`.
-/
theorem isLittleO_iff_forall_isBigOWith : f =o[l] g ↔ ∀ ⦃c : ℝ⦄, 0 < c → IsBigOWith c l f g := by
  rw [IsLittleO_def]

alias ⟨IsLittleO.forall_isBigOWith, IsLittleO.of_isBigOWith⟩ := isLittleO_iff_forall_isBigOWith

/-- Definition of `IsLittleO` in terms of filters. -/
/-
**Asymptotics.isLittleO_iff** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_iff : f =o[l] g ↔ forall ⦃c : Real⦄, 0 < c -> forallᶠ x in l, ‖f
 x‖ <= c * ‖g x‖
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.IsLittleO_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type u
_20} [inst : Norm E] [inst_1 : Norm F] (l : Filter α) (f : α → E)   (g : α → F),
 f =o[l] g = ∀ …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Asymptotics.IsBigOWith_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type 
u_20} [inst : Norm E] [inst_1 : Norm F] (c : ℝ) (l : Filter α) (f : α → E)   (g 
: α → F), Asympt…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Definition of `IsLittleO` in terms of filters.
-/
theorem isLittleO_iff : f =o[l] g ↔ ∀ ⦃c : ℝ⦄, 0 < c → ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ := by
  simp only [IsLittleO_def, IsBigOWith_def]

alias ⟨IsLittleO.bound, IsLittleO.of_bound⟩ := isLittleO_iff
/-
**Asymptotics.IsLittleO.def** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLittleO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : N
orm F] {c : ℝ} {f : α → E} {g : α → F}   {l : Filter α}, f =o[l] g → 0 < c → ∀ᶠ 
(x : α) in l, ‖f x‖ ≤ c * ‖g x‖
参数：x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Asymptotics.isLittleO_iff`：isLittleO_iff : f =o[l] g ↔ forall ⦃c : Real⦄
, 0 < c -> forallᶠ x in l, ‖f x‖ <= c * ‖g x‖
-/
theorem IsLittleO.def (h : f =o[l] g) (hc : 0 < c) : ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ :=
  isLittleO_iff.1 h hc
/-
**Asymptotics.IsLittleO.def'** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLittleO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : N
orm F] {c : ℝ} {f : α → E} {g : α → F}   {l : Filter α}, f =o[l] g → 0 < c → Asy
mptotics.IsBigOWith c l f g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Asymptotics.isBigOWith_iff`：isBigOWith_iff : IsBigOWith c l f g ↔ forall
ᶠ x in l, ‖f x‖ <= c * ‖g x‖
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Asymptotics.isLittleO_iff`：isLittleO_iff : f =o[l] g ↔ forall ⦃c : Real⦄
, 0 < c -> forallᶠ x in l, ‖f x‖ <= c * ‖g x‖
-/
theorem IsLittleO.def' (h : f =o[l] g) (hc : 0 < c) : IsBigOWith c l f g :=
  isBigOWith_iff.2 <| isLittleO_iff.1 h hc
/-
**Asymptotics.IsLittleO.eventuallyLE** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLi
ttleO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : N
orm F] {f : α → E} {g : α → F} {l : Filter α},   f =o[l] g → ∀ᶠ (x : α) in l, ‖f
 x‖ ≤ ‖g x‖
参数：x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Asymptotics.IsLittleO.def`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4
} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : Filte
r α}, f =o[l] g…
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem IsLittleO.eventuallyLE (h : f =o[l] g) : ∀ᶠ x in l, ‖f x‖ ≤ ‖g x‖ := by
  simpa using h.def zero_lt_one
/-
**Asymptotics.IsLittleO.eventuallyLT_norm_of_eventually_pos** 是 Mathlib 中的一个定理，位
于命名空间 `Asymptotics.IsLittleO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : N
orm F] {f : α → E} {g : α → F} {l : Filter α},   f =o[l] g → (∀ᶠ (x : α) in l, 0
 < ‖g x‖) → ∀ᶠ (x : α) in l, ‖f x‖ < ‖g x‖
参数：∀ᶠ (x : α) in l, 0 < ‖g x‖；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Asymptotics.IsLittleO.def`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4
} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : Filte
r α}, f =o[l] g…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_lt_iff_lt_one_left`：mul_lt_iff_lt_one_left [MulPosStrictMono α] [Mul
PosReflectLT α] (b0 : 0 < b) : a * b < b ↔ a < 1
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_lt_true`：isNNRat_lt_true [Semiring α] [Line
arOrder α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Nat} -> {da db : Nat}
 -> IsNNRat a na da -> IsN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
theorem IsLittleO.eventuallyLT_norm_of_eventually_pos (h : f =o[l] g) (hg : ∀ᶠ x in l, 0 < ‖g x‖) :
    ∀ᶠ x in l, ‖f x‖ < ‖g x‖ := by
  refine ((h.def (show 0 < 2⁻¹ by simp)).and hg).mono fun x ⟨hx₁, hx₂⟩ ↦ hx₁.trans_lt ?_
  rw [mul_lt_iff_lt_one_left hx₂]
  norm_num

/-- Two functions `u` and `v` are said to be asymptotically equivalent along a filter `l`
  (denoted as `u ~[l] v` in the `Asymptotics` namespace)
  when `u x - v x = o(v x)` as `x` converges along `l`. -/
/-
**Asymptotics.IsEquivalent** 是 Mathlib 中的一个定义，位于命名空间 `Asymptotics`。
形式化陈述：IsEquivalent (l : Filter α) (u v : α -> E')
参数：l : Filter α；u v : α -> E'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two functions `u` and `v` are said to be asymptotically equivalent along a filte
r `l`
  (denoted as `u ~[l] v` in the `Asymptotics` namespace)
  when `u x - v x = o(v x)` as `x` converges along `l`.
-/
def IsEquivalent (l : Filter α) (u v : α → E') :=
  (u - v) =o[l] v

@[inherit_doc] scoped notation:50 u " ~[" l:50 "] " v:50 => Asymptotics.IsEquivalent l u v

end Defs

/-! ### Conversions -/


/-
**Asymptotics.IsBigOWith.isBigO** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigOWit
h`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : N
orm F] {c : ℝ} {f : α → E} {g : α → F}   {l : Filter α}, Asymptotics.IsBigOWith 
c l f g → f =O[l] g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.IsBigO_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type u_20
} [inst : Norm E] [inst_1 : Norm F] (l : Filter α) (f : α → E)   (g : α → F), f 
=O[l] g = ∃ …

--- 原说明 ---
### Conversions
-/
theorem IsBigOWith.isBigO (h : IsBigOWith c l f g) : f =O[l] g := by rw [IsBigO_def]; exact ⟨c, h⟩
/-
**Asymptotics.IsLittleO.isBigOWith** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLitt
leO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : N
orm F] {f : α → E} {g : α → F} {l : Filter α},   f =o[l] g → Asymptotics.IsBigOW
ith 1 l f g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.def'`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_
4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : Filt
er α}, f =o[l] g…
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem IsLittleO.isBigOWith (hgf : f =o[l] g) : IsBigOWith 1 l f g :=
  hgf.def' zero_lt_one
/-
**Asymptotics.IsLittleO.isBigO** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLittleO`
。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : N
orm F] {f : α → E} {g : α → F} {l : Filter α},   f =o[l] g → f =O[l] g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : F
ilter α}, Asymptoti…
· 使用定理 `Asymptotics.IsLittleO.isBigOWith`：∀ {α : Type u_1} {E : Type u_3} {F : T
ype u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α
},   f =o[l] g → Asymp…
-/
theorem IsLittleO.isBigO (hgf : f =o[l] g) : f =O[l] g :=
  hgf.isBigOWith.isBigO
/-
**Asymptotics.IsBigO.isBigOWith** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : N
orm F] {f : α → E} {g : α → F} {l : Filter α},   f =O[l] g → ∃ c, Asymptotics.Is
BigOWith c l f g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Asymptotics.isBigO_iff_isBigOWith`：isBigO_iff_isBigOWith : f =O[l] g ↔ e
xists c : Real, IsBigOWith c l f g
-/
theorem IsBigO.isBigOWith : f =O[l] g → ∃ c : ℝ, IsBigOWith c l f g :=
  isBigO_iff_isBigOWith.1
/-
**Asymptotics.IsBigOWith.weaken** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigOWit
h`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F' : Type u_7} [inst : Norm E] [inst_1 : 
SeminormedAddCommGroup F'] {c c' : ℝ}   {f : α → E} {g' : α → F'} {l : Filter α}
, Asymptotics.IsBigOWith c l f g' → c ≤ c' → Asymptotics.IsBigOWith c' l f g'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.of_bound`：∀ {α : Type u_1} {E : Type u_3} {F : Ty
pe u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l :
 Filter α}, (∀ᶠ (x : …
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Asymptotics.IsBigOWith.bound`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : Fi
lter α}, Asymptoti…
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem IsBigOWith.weaken (h : IsBigOWith c l f g') (hc : c ≤ c') : IsBigOWith c' l f g' :=
  IsBigOWith.of_bound <|
    mem_of_superset h.bound fun x hx =>
      calc
        ‖f x‖ ≤ c * ‖g' x‖ := hx
        _ ≤ _ := by gcongr
/-
**Asymptotics.IsBigOWith.exists_pos** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBig
OWith`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F' : Type u_7} [inst : Norm E] [inst_1 : 
SeminormedAddCommGroup F'] {c : ℝ} {f : α → E}   {g' : α → F'} {l : Filter α}, A
symptotics.IsBigOWith c l f g' → ∃ c' > 0, Asymptotics.IsBigOWith c' l f g'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `Asymptotics.IsBigOWith.weaken`：∀ {α : Type u_1} {E : Type u_3} {F' : Typ
e u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {c c' : ℝ}   {f : α 
→ E} {g' : α → F'} …
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
-/
theorem IsBigOWith.exists_pos (h : IsBigOWith c l f g') :
    ∃ c' > 0, IsBigOWith c' l f g' :=
  ⟨max c 1, lt_of_lt_of_le zero_lt_one (le_max_right c 1), h.weaken <| le_max_left c 1⟩
/-
**Asymptotics.IsBigO.exists_pos** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F' : Type u_7} [inst : Norm E] [inst_1 : 
SeminormedAddCommGroup F'] {f : α → E}   {g' : α → F'} {l : Filter α}, f =O[l] g
' → ∃ c > 0, Asymptotics.IsBigOWith c l f g'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.isBigOWith`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α}, 
  f =O[l] g → ∃ c, …
· 使用定理 `Asymptotics.IsBigOWith.exists_pos`：∀ {α : Type u_1} {E : Type u_3} {F' :
 Type u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {c : ℝ} {f : α →
 E}   {g' : α → F'} {l …
-/
theorem IsBigO.exists_pos (h : f =O[l] g') : ∃ c > 0, IsBigOWith c l f g' :=
  let ⟨_c, hc⟩ := h.isBigOWith
  hc.exists_pos
/-
**Asymptotics.IsBigOWith.exists_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.Is
BigOWith`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F' : Type u_7} [inst : Norm E] [inst_1 : 
SeminormedAddCommGroup F'] {c : ℝ} {f : α → E}   {g' : α → F'} {l : Filter α}, A
symptotics.IsBigOWith c l f g' → ∃ c' ≥ 0, Asymptotics.IsBigOWith c' l f g'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.exists_pos`：∀ {α : Type u_1} {E : Type u_3} {F' :
 Type u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {c : ℝ} {f : α →
 E}   {g' : α → F'} {l …
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem IsBigOWith.exists_nonneg (h : IsBigOWith c l f g') :
    ∃ c' ≥ 0, IsBigOWith c' l f g' :=
  let ⟨c, cpos, hc⟩ := h.exists_pos
  ⟨c, le_of_lt cpos, hc⟩
/-
**Asymptotics.IsBigO.exists_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO
`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F' : Type u_7} [inst : Norm E] [inst_1 : 
SeminormedAddCommGroup F'] {f : α → E}   {g' : α → F'} {l : Filter α}, f =O[l] g
' → ∃ c ≥ 0, Asymptotics.IsBigOWith c l f g'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.isBigOWith`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α}, 
  f =O[l] g → ∃ c, …
· 使用定理 `Asymptotics.IsBigOWith.exists_nonneg`：∀ {α : Type u_1} {E : Type u_3} {F
' : Type u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {c : ℝ} {f : 
α → E}   {g' : α → F'} {l …
-/
theorem IsBigO.exists_nonneg (h : f =O[l] g') : ∃ c ≥ 0, IsBigOWith c l f g' :=
  let ⟨_c, hc⟩ := h.isBigOWith
  hc.exists_nonneg

/-- `f = O(g)` if and only if `IsBigOWith c f g` for all sufficiently large `c`. -/
/-
**Asymptotics.isBigO_iff_eventually_isBigOWith** 是 Mathlib 中的一个定理，位于命名空间 `Asympt
otics`。
形式化陈述：isBigO_iff_eventually_isBigOWith : f =O[l] g' ↔ forallᶠ c in atTop, IsBigO
With c l f g'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Asymptotics.isBigO_iff_isBigOWith`：isBigO_iff_isBigOWith : f =O[l] g ↔ e
xists c : Real, IsBigOWith c l f g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.mem_atTop_sets`：mem_atTop_sets {s : Set α} : s in (atTop : Filter
 α) ↔ exists a : α, forall b, a <= b -> b in s
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Asymptotics.IsBigOWith.weaken`：∀ {α : Type u_1} {E : Type u_3} {F' : Typ
e u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {c c' : ℝ}   {f : α 
→ E} {g' : α → F'} …
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x

--- 原说明 ---
`f = O(g)` if and only if `IsBigOWith c f g` for all sufficiently large `c`.
-/
theorem isBigO_iff_eventually_isBigOWith : f =O[l] g' ↔ ∀ᶠ c in atTop, IsBigOWith c l f g' :=
  isBigO_iff_isBigOWith.trans
    ⟨fun ⟨c, hc⟩ => mem_atTop_sets.2 ⟨c, fun _c' hc' => hc.weaken hc'⟩, fun h => h.exists⟩

/-- `f = O(g)` if and only if `∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖` for all sufficiently large `c`. -/
/-
**Asymptotics.isBigO_iff_eventually** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_iff_eventually : f =O[l] g' ↔ forallᶠ c in atTop, forallᶠ x in l, ‖
f x‖ <= c * ‖g' x‖
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Asymptotics.isBigO_iff_eventually_isBigOWith`：isBigO_iff_eventually_isBi
gOWith : f =O[l] g' ↔ forallᶠ c in atTop, IsBigOWith c l f g'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Asymptotics.IsBigOWith_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type 
u_20} [inst : Norm E] [inst_1 : Norm F] (c : ℝ) (l : Filter α) (f : α → E)   (g 
: α → F), Asympt…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`f = O(g)` if and only if `∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖` for all sufficiently la
rge `c`.
-/
theorem isBigO_iff_eventually : f =O[l] g' ↔ ∀ᶠ c in atTop, ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g' x‖ :=
  isBigO_iff_eventually_isBigOWith.trans <| by simp only [IsBigOWith_def]
/-
**Asymptotics.IsBigO.exists_mem_basis** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsB
igO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F' : Type u_7} [inst : Norm E] [inst_1 : 
SeminormedAddCommGroup F'] {f : α → E}   {g' : α → F'} {l : Filter α} {ι : Sort 
u_18} {p : ι → Prop} {s : ι → Set α},   f =O[l] g' → l.HasBasis p s → ∃ c > 0, ∃
 i, p i ∧ ∀ x ∈ s i, ‖f x‖ ≤ c * ‖g' x‖
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Asymptotics.IsBigO.exists_pos`：∀ {α : Type u_1} {E : Type u_3} {F' : Typ
e u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {f : α → E}   {g' : 
α → F'} {l : Filter…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.HasBasis.eventually_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : α → Prop}, (∀ᶠ 
(x : α) in l, q x) ↔…
-/
theorem IsBigO.exists_mem_basis {ι} {p : ι → Prop} {s : ι → Set α} (h : f =O[l] g')
    (hb : l.HasBasis p s) :
    ∃ c > 0, ∃ i : ι, p i ∧ ∀ x ∈ s i, ‖f x‖ ≤ c * ‖g' x‖ :=
  flip Exists.imp h.exists_pos fun c h => by
    simpa only [isBigOWith_iff, hb.eventually_iff, exists_prop] using h
/-
**Asymptotics.isBigOWith_inv** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOWith_inv (hc : 0 < c) : IsBigOWith c⁻¹ l f g ↔ forallᶠ x in l, c * ‖
f x‖ <= ‖g x‖
参数：hc : 0 < c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.IsBigOWith_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type 
u_20} [inst : Norm E] [inst_1 : Norm F] (c : ℝ) (l : Filter α) (f : α → E)   (g 
: α → F), Asympt…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `le_div_iff₀'`：le_div_iff₀' (hc : 0 < c) : a <= b / c ↔ c * a <= b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isBigOWith_inv (hc : 0 < c) : IsBigOWith c⁻¹ l f g ↔ ∀ᶠ x in l, c * ‖f x‖ ≤ ‖g x‖ := by
  simp only [IsBigOWith_def, ← div_eq_inv_mul, le_div_iff₀' hc]

-- We prove this lemma with strange assumptions to get two lemmas below automatically
/-
**Asymptotics.isLittleO_iff_nat_mul_le_aux** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotic
s`。
形式化陈述：isLittleO_iff_nat_mul_le_aux (h₀ : (forall x, 0 <= ‖f x‖) ∨ forall x, 0 <=
 ‖g x‖) : f =o[l] g ↔ forall n : Nat, forallᶠ x in l, ↑n * ‖f x‖ <= ‖g x‖
参数：h₀ : (forall x, 0 <= ‖f x‖) ∨ forall x, 0 <= ‖g x‖。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Asymptotics.IsLittleO.def`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4
} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : Filte
r α}, f =o[l] g…
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Asymptotics.isBigOWith_inv`：isBigOWith_inv (hc : 0 < c) : IsBigOWith c⁻¹
 l f g ↔ forallᶠ x in l, c * ‖f x‖ <= ‖g x‖
· 使用定理 `Asymptotics.IsLittleO.def'`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_
4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : Filt
er α}, f =o[l] g…
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Asymptotics.isLittleO_iff`：isLittleO_iff : f =o[l] g ↔ forall ⦃c : Real⦄
, 0 < c -> forallᶠ x in l, ‖f x‖ <= c * ‖g x‖
· 使用定理 `exists_nat_gt`：exists_nat_gt (x : R) : exists n : Nat, x < n
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Asymptotics.IsBigOWith.bound`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : Fi
lter α}, Asymptoti…
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用引理 `inv_le_of_inv_le₀`：inv_le_of_inv_le₀ (ha : 0 < a) (h : a⁻¹ <= b) : b⁻¹ <
= a
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
（共 32 条，此处仅展示前 30 条）
-/
theorem isLittleO_iff_nat_mul_le_aux (h₀ : (∀ x, 0 ≤ ‖f x‖) ∨ ∀ x, 0 ≤ ‖g x‖) :
    f =o[l] g ↔ ∀ n : ℕ, ∀ᶠ x in l, ↑n * ‖f x‖ ≤ ‖g x‖ := by
  constructor
  · rintro H (_ | n)
    · refine (H.def one_pos).mono fun x h₀' => ?_
      rw [Nat.cast_zero, zero_mul]
      refine h₀.elim (fun hf => (hf x).trans ?_) fun hg => hg x
      rwa [one_mul] at h₀'
    · have : (0 : ℝ) < n.succ := Nat.cast_pos.2 n.succ_pos
      exact (isBigOWith_inv this).1 (H.def' <| inv_pos.2 this)
  · refine fun H => isLittleO_iff.2 fun ε ε0 => ?_
    rcases exists_nat_gt ε⁻¹ with ⟨n, hn⟩
    have hn₀ : (0 : ℝ) < n := (inv_pos.2 ε0).trans hn
    refine ((isBigOWith_inv hn₀).2 (H n)).bound.mono fun x hfg => ?_
    refine hfg.trans (mul_le_mul_of_nonneg_right (inv_le_of_inv_le₀ ε0 hn.le) ?_)
    refine h₀.elim (fun hf => nonneg_of_mul_nonneg_right ((hf x).trans hfg) ?_) fun h => h x
    exact inv_pos.2 hn₀
/-
**Asymptotics.isLittleO_iff_nat_mul_le** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_iff_nat_mul_le : f =o[l] g' ↔ forall n : Nat, forallᶠ x in l, ↑n
 * ‖f x‖ <= ‖g' x‖
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isLittleO_iff_nat_mul_le_aux`：isLittleO_iff_nat_mul_le_aux (
h₀ : (forall x, 0 <= ‖f x‖) ∨ forall x, 0 <= ‖g x‖) : f =o[l] g ↔ forall n : Nat
, forallᶠ x in l, ↑n * ‖f x‖ <…
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem isLittleO_iff_nat_mul_le : f =o[l] g' ↔ ∀ n : ℕ, ∀ᶠ x in l, ↑n * ‖f x‖ ≤ ‖g' x‖ :=
  isLittleO_iff_nat_mul_le_aux (Or.inr fun _x => norm_nonneg _)
/-
**Asymptotics.isLittleO_iff_nat_mul_le'** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_iff_nat_mul_le' : f' =o[l] g ↔ forall n : Nat, forallᶠ x in l, ↑
n * ‖f' x‖ <= ‖g x‖
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isLittleO_iff_nat_mul_le_aux`：isLittleO_iff_nat_mul_le_aux (
h₀ : (forall x, 0 <= ‖f x‖) ∨ forall x, 0 <= ‖g x‖) : f =o[l] g ↔ forall n : Nat
, forallᶠ x in l, ↑n * ‖f x‖ <…
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem isLittleO_iff_nat_mul_le' : f' =o[l] g ↔ ∀ n : ℕ, ∀ᶠ x in l, ↑n * ‖f' x‖ ≤ ‖g x‖ :=
  isLittleO_iff_nat_mul_le_aux (Or.inl fun _x => norm_nonneg _)

/-! ### Subsingleton -/


@[nontriviality]
/-
**Asymptotics.isLittleO_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_of_subsingleton [Subsingleton E'] : f' =o[l] g'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.of_bound`：∀ {α : Type u_1} {E : Type u_3} {F : Typ
e u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},
   (∀ ⦃c : ℝ⦄, 0 < c…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
### Subsingleton
-/
theorem isLittleO_of_subsingleton [Subsingleton E'] : f' =o[l] g' :=
  IsLittleO.of_bound fun c hc => by simp [Subsingleton.elim (f' _) 0, mul_nonneg hc.le]

@[nontriviality]
/-
**Asymptotics.isBigO_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_of_subsingleton [Subsingleton E'] : f' =O[l] g'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},  
 f =o[l] g → f =O[…
· 使用定理 `Asymptotics.isLittleO_of_subsingleton`：isLittleO_of_subsingleton [Subsin
gleton E'] : f' =o[l] g'
-/
theorem isBigO_of_subsingleton [Subsingleton E'] : f' =O[l] g' :=
  isLittleO_of_subsingleton.isBigO

section congr

variable {f₁ f₂ : α → E} {g₁ g₂ : α → F}

/-! ### Congruence -/


/-
**Asymptotics.isBigOWith_congr** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOWith_congr (hc : c₁ = c₂) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : Is
BigOWith c₁ l f₁ g₁ ↔ IsBigOWith c₂ l f₂ g₂
参数：hc : c₁ = c₂；hf : f₁ =ᶠ[l] f₂；hg : g₁ =ᶠ[l] g₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.IsBigOWith_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type 
u_20} [inst : Norm E] [inst_1 : Norm F] (c : ℝ) (l : Filter α) (f : α → E)   (g 
: α → F), Asympt…
· 使用定理 `Filter.eventually_congr`：eventually_congr {f : Filter α} {p q : α -> Pro
p} (h : forallᶠ x in f, p x ↔ q x) : (forallᶠ x in f, p x) ↔ forallᶠ x in f, q x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
### Congruence
-/
theorem isBigOWith_congr (hc : c₁ = c₂) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) :
    IsBigOWith c₁ l f₁ g₁ ↔ IsBigOWith c₂ l f₂ g₂ := by
  simp only [IsBigOWith_def]
  subst c₂
  apply Filter.eventually_congr
  filter_upwards [hf, hg] with _ e₁ e₂
  rw [e₁, e₂]
/-
**Asymptotics.IsBigOWith.congr'** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigOWit
h`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : N
orm F] {c₁ c₂ : ℝ} {l : Filter α}   {f₁ f₂ : α → E} {g₁ g₂ : α → F},   Asymptoti
cs.IsBigOWith c₁ l f₁ g₁ → c₁ = c₂ → f₁ =ᶠ[l] f₂ → g₁ =ᶠ[l] g₂ → Asymptotics.IsB
igOWith c₂ l f₂ g₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Asymptotics.isBigOWith_congr`：isBigOWith_congr (hc : c₁ = c₂) (hf : f₁ =
ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : IsBigOWith c₁ l f₁ g₁ ↔ IsBigOWith c₂ l f₂ g₂
-/
theorem IsBigOWith.congr' (h : IsBigOWith c₁ l f₁ g₁) (hc : c₁ = c₂) (hf : f₁ =ᶠ[l] f₂)
    (hg : g₁ =ᶠ[l] g₂) : IsBigOWith c₂ l f₂ g₂ :=
  (isBigOWith_congr hc hf hg).mp h
/-
**Asymptotics.IsBigOWith.congr** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigOWith
`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : N
orm F] {c₁ c₂ : ℝ} {l : Filter α}   {f₁ f₂ : α → E} {g₁ g₂ : α → F},   Asymptoti
cs.IsBigOWith c₁ l f₁ g₁ →     c₁ = c₂ → (∀ (x : α), f₁ x = f₂ x) → (∀ (x : α), 
g₁ x = g₂ x) → Asymptotics.IsBigOWith c₂ l f₂ g₂
参数：∀ (x : α), f₁ x = f₂ x；∀ (x : α), g₁ x = g₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.congr'`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {c₁ c₂ : ℝ} {l : Filter α}   {f₁ f₂ : α 
→ E} {g₁ g₂ : α → F…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
theorem IsBigOWith.congr (h : IsBigOWith c₁ l f₁ g₁) (hc : c₁ = c₂) (hf : ∀ x, f₁ x = f₂ x)
    (hg : ∀ x, g₁ x = g₂ x) : IsBigOWith c₂ l f₂ g₂ :=
  h.congr' hc (univ_mem' hf) (univ_mem' hg)
/-
**Asymptotics.IsBigOWith.congr_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBig
OWith`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : N
orm F] {c : ℝ} {g : α → F} {l : Filter α}   {f₁ f₂ : α → E}, Asymptotics.IsBigOW
ith c l f₁ g → (∀ (x : α), f₁ x = f₂ x) → Asymptotics.IsBigOWith c l f₂ g
参数：∀ (x : α), f₁ x = f₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.congr`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {c₁ c₂ : ℝ} {l : Filter α}   {f₁ f₂ : α →
 E} {g₁ g₂ : α → F…
-/
theorem IsBigOWith.congr_left (h : IsBigOWith c l f₁ g) (hf : ∀ x, f₁ x = f₂ x) :
    IsBigOWith c l f₂ g :=
  h.congr rfl hf fun _ => rfl
/-
**Asymptotics.IsBigOWith.congr_right** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBi
gOWith`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : N
orm F] {c : ℝ} {f : α → E} {l : Filter α}   {g₁ g₂ : α → F}, Asymptotics.IsBigOW
ith c l f g₁ → (∀ (x : α), g₁ x = g₂ x) → Asymptotics.IsBigOWith c l f g₂
参数：∀ (x : α), g₁ x = g₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.congr`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {c₁ c₂ : ℝ} {l : Filter α}   {f₁ f₂ : α →
 E} {g₁ g₂ : α → F…
-/
theorem IsBigOWith.congr_right (h : IsBigOWith c l f g₁) (hg : ∀ x, g₁ x = g₂ x) :
    IsBigOWith c l f g₂ :=
  h.congr rfl (fun _ => rfl) hg
/-
**Asymptotics.IsBigOWith.congr_const** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBi
gOWith`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : N
orm F] {c₁ c₂ : ℝ} {f : α → E} {g : α → F}   {l : Filter α}, Asymptotics.IsBigOW
ith c₁ l f g → c₁ = c₂ → Asymptotics.IsBigOWith c₂ l f g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.congr`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {c₁ c₂ : ℝ} {l : Filter α}   {f₁ f₂ : α →
 E} {g₁ g₂ : α → F…
-/
theorem IsBigOWith.congr_const (h : IsBigOWith c₁ l f g) (hc : c₁ = c₂) : IsBigOWith c₂ l f g :=
  h.congr hc (fun _ => rfl) fun _ => rfl
/-
**Asymptotics.isBigO_congr** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_congr (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₁ =O[l] g₁ ↔ f₂ =O[l
] g₂
参数：hf : f₁ =ᶠ[l] f₂；hg : g₁ =ᶠ[l] g₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.IsBigO_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type u_20
} [inst : Norm E] [inst_1 : Norm F] (l : Filter α) (f : α → E)   (g : α → F), f 
=O[l] g = ∃ …
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `Asymptotics.isBigOWith_congr`：isBigOWith_congr (hc : c₁ = c₂) (hf : f₁ =
ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : IsBigOWith c₁ l f₁ g₁ ↔ IsBigOWith c₂ l f₂ g₂
-/
theorem isBigO_congr (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₁ =O[l] g₁ ↔ f₂ =O[l] g₂ := by
  simp only [IsBigO_def]
  exact exists_congr fun c => isBigOWith_congr rfl hf hg
/-
**Asymptotics.IsBigO.congr'** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : N
orm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ : α → F}, f₁ =O[l] g₁ → f₁ =ᶠ[l] 
f₂ → g₁ =ᶠ[l] g₂ → f₂ =O[l] g₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Asymptotics.isBigO_congr`：isBigO_congr (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l]
 g₂) : f₁ =O[l] g₁ ↔ f₂ =O[l] g₂
-/
theorem IsBigO.congr' (h : f₁ =O[l] g₁) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₂ =O[l] g₂ :=
  (isBigO_congr hf hg).mp h
/-
**Asymptotics.IsBigO.congr** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : N
orm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ : α → F}, f₁ =O[l] g₁ → (∀ (x : α
), f₁ x = f₂ x) → (∀ (x : α), g₁ x = g₂ x) → f₂ =O[l] g₂
参数：∀ (x : α), f₁ x = f₂ x；∀ (x : α), g₁ x = g₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.congr'`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4
} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ : α 
→ F}, f₁ =O[l] …
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
theorem IsBigO.congr (h : f₁ =O[l] g₁) (hf : ∀ x, f₁ x = f₂ x) (hg : ∀ x, g₁ x = g₂ x) :
    f₂ =O[l] g₂ :=
  h.congr' (univ_mem' hf) (univ_mem' hg)
/-
**Asymptotics.IsBigO.congr_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : N
orm F] {g : α → F} {l : Filter α}   {f₁ f₂ : α → E}, f₁ =O[l] g → (∀ (x : α), f₁
 x = f₂ x) → f₂ =O[l] g
参数：∀ (x : α), f₁ x = f₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.congr`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4}
 [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ : α →
 F}, f₁ =O[l] …
-/
theorem IsBigO.congr_left (h : f₁ =O[l] g) (hf : ∀ x, f₁ x = f₂ x) : f₂ =O[l] g :=
  h.congr hf fun _ => rfl
/-
**Asymptotics.IsBigO.congr_right** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : N
orm F] {f : α → E} {l : Filter α}   {g₁ g₂ : α → F}, f =O[l] g₁ → (∀ (x : α), g₁
 x = g₂ x) → f =O[l] g₂
参数：∀ (x : α), g₁ x = g₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.congr`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4}
 [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ : α →
 F}, f₁ =O[l] …
-/
theorem IsBigO.congr_right (h : f =O[l] g₁) (hg : ∀ x, g₁ x = g₂ x) : f =O[l] g₂ :=
  h.congr (fun _ => rfl) hg
/-
**Asymptotics.isLittleO_congr** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_congr (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₁ =o[l] g₁ ↔ f₂ =
o[l] g₂
参数：hf : f₁ =ᶠ[l] f₂；hg : g₁ =ᶠ[l] g₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.IsLittleO_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type u
_20} [inst : Norm E] [inst_1 : Norm F] (l : Filter α) (f : α → E)   (g : α → F),
 f =o[l] g = ∀ …
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `Asymptotics.isBigOWith_congr`：isBigOWith_congr (hc : c₁ = c₂) (hf : f₁ =
ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : IsBigOWith c₁ l f₁ g₁ ↔ IsBigOWith c₂ l f₂ g₂
-/
theorem isLittleO_congr (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₁ =o[l] g₁ ↔ f₂ =o[l] g₂ := by
  simp only [IsLittleO_def]
  exact forall₂_congr fun c _hc => isBigOWith_congr (Eq.refl c) hf hg
/-
**Asymptotics.IsLittleO.congr'** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLittleO`
。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : N
orm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ : α → F}, f₁ =o[l] g₁ → f₁ =ᶠ[l] 
f₂ → g₁ =ᶠ[l] g₂ → f₂ =o[l] g₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Asymptotics.isLittleO_congr`：isLittleO_congr (hf : f₁ =ᶠ[l] f₂) (hg : g₁
 =ᶠ[l] g₂) : f₁ =o[l] g₁ ↔ f₂ =o[l] g₂
-/
theorem IsLittleO.congr' (h : f₁ =o[l] g₁) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₂ =o[l] g₂ :=
  (isLittleO_congr hf hg).mp h
/-
**Asymptotics.IsLittleO.congr** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLittleO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : N
orm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ : α → F}, f₁ =o[l] g₁ → (∀ (x : α
), f₁ x = f₂ x) → (∀ (x : α), g₁ x = g₂ x) → f₂ =o[l] g₂
参数：∀ (x : α), f₁ x = f₂ x；∀ (x : α), g₁ x = g₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.congr'`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ :
 α → F}, f₁ =o[l] …
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
theorem IsLittleO.congr (h : f₁ =o[l] g₁) (hf : ∀ x, f₁ x = f₂ x) (hg : ∀ x, g₁ x = g₂ x) :
    f₂ =o[l] g₂ :=
  h.congr' (univ_mem' hf) (univ_mem' hg)
/-
**Asymptotics.IsLittleO.congr_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLitt
leO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : N
orm F] {g : α → F} {l : Filter α}   {f₁ f₂ : α → E}, f₁ =o[l] g → (∀ (x : α), f₁
 x = f₂ x) → f₂ =o[l] g
参数：∀ (x : α), f₁ x = f₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.congr`：∀ {α : Type u_1} {E : Type u_3} {F : Type u
_4} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ : 
α → F}, f₁ =o[l] …
-/
theorem IsLittleO.congr_left (h : f₁ =o[l] g) (hf : ∀ x, f₁ x = f₂ x) : f₂ =o[l] g :=
  h.congr hf fun _ => rfl
/-
**Asymptotics.IsLittleO.congr_right** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLit
tleO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : N
orm F] {f : α → E} {l : Filter α}   {g₁ g₂ : α → F}, f =o[l] g₁ → (∀ (x : α), g₁
 x = g₂ x) → f =o[l] g₂
参数：∀ (x : α), g₁ x = g₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.congr`：∀ {α : Type u_1} {E : Type u_3} {F : Type u
_4} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ : 
α → F}, f₁ =o[l] …
-/
theorem IsLittleO.congr_right (h : f =o[l] g₁) (hg : ∀ x, g₁ x = g₂ x) : f =o[l] g₂ :=
  h.congr (fun _ => rfl) hg

@[trans]
/-
**Asymptotics._root_.Filter.EventuallyEq.trans_isBigO** 是 Mathlib 中的一个定理，位于命名空间 
`Asymptotics`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Filter.EventuallyEq.trans_isBigO {f₁ f₂ : α → E} {g : α → F} (hf : f₁ =ᶠ[l] f₂)
    (h : f₂ =O[l] g) : f₁ =O[l] g :=
  h.congr' hf.symm EventuallyEq.rfl
/-
**Asymptotics.transEventuallyEqIsBigO** 是 Mathlib 中的一个实例，位于命名空间 `Asymptotics`。
形式化陈述：transEventuallyEqIsBigO : @Trans (α -> E) (α -> E) (α -> F) (· =ᶠ[l] ·) (·
 =O[l] ·) (· =O[l] ·) where trans
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.trans_isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : T
ype u_4} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g :
 α → F}, f₁ =ᶠ[l] f₂ →…
-/
instance transEventuallyEqIsBigO :
    @Trans (α → E) (α → E) (α → F) (· =ᶠ[l] ·) (· =O[l] ·) (· =O[l] ·) where
  trans := Filter.EventuallyEq.trans_isBigO

@[trans]
/-
**Asymptotics._root_.Filter.EventuallyEq.trans_isLittleO** 是 Mathlib 中的一个定理，位于命名
空间 `Asymptotics`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Filter.EventuallyEq.trans_isLittleO {f₁ f₂ : α → E} {g : α → F} (hf : f₁ =ᶠ[l] f₂)
    (h : f₂ =o[l] g) : f₁ =o[l] g :=
  h.congr' hf.symm EventuallyEq.rfl
/-
**Asymptotics.transEventuallyEqIsLittleO** 是 Mathlib 中的一个实例，位于命名空间 `Asymptotics`
。
形式化陈述：transEventuallyEqIsLittleO : @Trans (α -> E) (α -> E) (α -> F) (· =ᶠ[l] ·)
 (· =o[l] ·) (· =o[l] ·) where trans
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.trans_isLittleO`：∀ {α : Type u_1} {E : Type u_3} {F 
: Type u_4} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {
g : α → F}, f₁ =ᶠ[l] f₂ →…
-/
instance transEventuallyEqIsLittleO :
    @Trans (α → E) (α → E) (α → F) (· =ᶠ[l] ·) (· =o[l] ·) (· =o[l] ·) where
  trans := Filter.EventuallyEq.trans_isLittleO

@[trans]
/-
**Asymptotics.IsBigO.trans_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.I
sBigO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : N
orm F] {l : Filter α} {f : α → E}   {g₁ g₂ : α → F}, f =O[l] g₁ → g₁ =ᶠ[l] g₂ → 
f =O[l] g₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.congr'`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4
} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ : α 
→ F}, f₁ =O[l] …
· 使用定理 `Filter.EventuallyEq.rfl`：∀ {α : Type u} {β : Type v} {l : Filter α} {f :
 α → β}, f =ᶠ[l] f
-/
theorem IsBigO.trans_eventuallyEq {f : α → E} {g₁ g₂ : α → F} (h : f =O[l] g₁) (hg : g₁ =ᶠ[l] g₂) :
    f =O[l] g₂ :=
  h.congr' EventuallyEq.rfl hg
/-
**Asymptotics.transIsBigOEventuallyEq** 是 Mathlib 中的一个实例，位于命名空间 `Asymptotics`。
形式化陈述：transIsBigOEventuallyEq : @Trans (α -> E) (α -> F) (α -> F) (· =O[l] ·) (·
 =ᶠ[l] ·) (· =O[l] ·) where trans
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans_eventuallyEq`：∀ {α : Type u_1} {E : Type u_3} {
F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f : α → E}   {g₁
 g₂ : α → F}, f =O[l] g₁ → …
-/
instance transIsBigOEventuallyEq :
    @Trans (α → E) (α → F) (α → F) (· =O[l] ·) (· =ᶠ[l] ·) (· =O[l] ·) where
  trans := IsBigO.trans_eventuallyEq

@[trans]
/-
**Asymptotics.IsLittleO.trans_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotic
s.IsLittleO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : N
orm F] {l : Filter α} {f : α → E}   {g₁ g₂ : α → F}, f =o[l] g₁ → g₁ =ᶠ[l] g₂ → 
f =o[l] g₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.congr'`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ :
 α → F}, f₁ =o[l] …
· 使用定理 `Filter.EventuallyEq.rfl`：∀ {α : Type u} {β : Type v} {l : Filter α} {f :
 α → β}, f =ᶠ[l] f
-/
theorem IsLittleO.trans_eventuallyEq {f : α → E} {g₁ g₂ : α → F} (h : f =o[l] g₁)
    (hg : g₁ =ᶠ[l] g₂) : f =o[l] g₂ :=
  h.congr' EventuallyEq.rfl hg
/-
**Asymptotics.transIsLittleOEventuallyEq** 是 Mathlib 中的一个实例，位于命名空间 `Asymptotics`
。
形式化陈述：transIsLittleOEventuallyEq : @Trans (α -> E) (α -> F) (α -> F) (· =o[l] ·)
 (· =ᶠ[l] ·) (· =o[l] ·) where trans
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.trans_eventuallyEq`：∀ {α : Type u_1} {E : Type u_3
} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f : α → E}   
{g₁ g₂ : α → F}, f =o[l] g₁ → …
-/
instance transIsLittleOEventuallyEq :
    @Trans (α → E) (α → F) (α → F) (· =o[l] ·) (· =ᶠ[l] ·) (· =o[l] ·) where
  trans := IsLittleO.trans_eventuallyEq

end congr

/-! ### Filter operations and transitivity -/


/-
**Asymptotics.IsBigOWith.comp_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsB
igOWith`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {E : Type u_3} {F : Type u_4} [inst : Norm
 E] [inst_1 : Norm F] {c : ℝ} {f : α → E}   {g : α → F} {l : Filter α},   Asympt
otics.IsBigOWith c l f g →     ∀ {k : β → α} {l' : Filter β}, Filter.Tendsto k l
' l → Asymptotics.IsBigOWith c l' (f ∘ k) (g ∘ k)
参数：f ∘ k；g ∘ k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.of_bound`：∀ {α : Type u_1} {E : Type u_3} {F : Ty
pe u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l :
 Filter α}, (∀ᶠ (x : …
· 使用定理 `Asymptotics.IsBigOWith.bound`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : Fi
lter α}, Asymptoti…

--- 原说明 ---
### Filter operations and transitivity
-/
theorem IsBigOWith.comp_tendsto (hcfg : IsBigOWith c l f g) {k : β → α} {l' : Filter β}
    (hk : Tendsto k l' l) : IsBigOWith c l' (f ∘ k) (g ∘ k) :=
  IsBigOWith.of_bound <| hk hcfg.bound
/-
**Asymptotics.IsBigO.comp_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`
。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {E : Type u_3} {F : Type u_4} [inst : Norm
 E] [inst_1 : Norm F] {f : α → E} {g : α → F}   {l : Filter α}, f =O[l] g → ∀ {k
 : β → α} {l' : Filter β}, Filter.Tendsto k l' l → (f ∘ k) =O[l'] (g ∘ k)
参数：f ∘ k；g ∘ k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Asymptotics.isBigO_iff_isBigOWith`：isBigO_iff_isBigOWith : f =O[l] g ↔ e
xists c : Real, IsBigOWith c l f g
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Asymptotics.IsBigOWith.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E 
: Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E}
   {g : α → F} {l : Filte…
· 使用定理 `Asymptotics.IsBigO.isBigOWith`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α}, 
  f =O[l] g → ∃ c, …
-/
theorem IsBigO.comp_tendsto (hfg : f =O[l] g) {k : β → α} {l' : Filter β} (hk : Tendsto k l' l) :
    (f ∘ k) =O[l'] (g ∘ k) :=
  isBigO_iff_isBigOWith.2 <| hfg.isBigOWith.imp fun _c h => h.comp_tendsto hk
/-
**Asymptotics.IsBigO.comp_neg_int** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`
。
形式化陈述：∀ {E : Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : ℤ →
 E} {g : ℤ → F},   f =O[Filter.cofinite] g → (fun n => f (-n)) =O[Filter.cofinit
e] fun n => g (-n)
参数：fun n => f (-n)；-n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.neg_apply`：∀ (G : Type u_14) [inst : InvolutiveNeg G], ⇑(Equiv.neg
 G) = Neg.neg
· 使用定理 `Asymptotics.IsBigO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E : Ty
pe u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}
   {l : Filter α}, f …
· 使用定理 `Function.Injective.tendsto_cofinite`：Function.Injective.tendsto_cofinite
 {f : α -> β} (hf : Injective f) : Tendsto f cofinite cofinite
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
lemma IsBigO.comp_neg_int {f : ℤ → E} {g : ℤ → F} (hf : f =O[cofinite] g) :
    (fun n => f (-n)) =O[cofinite] fun n => g (-n) := by
  rw [← Equiv.neg_apply]
  exact hf.comp_tendsto (Equiv.neg ℤ).injective.tendsto_cofinite
/-
**Asymptotics.IsLittleO.comp_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLi
ttleO`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {E : Type u_3} {F : Type u_4} [inst : Norm
 E] [inst_1 : Norm F] {f : α → E} {g : α → F}   {l : Filter α}, f =o[l] g → ∀ {k
 : β → α} {l' : Filter β}, Filter.Tendsto k l' l → (f ∘ k) =o[l'] (g ∘ k)
参数：f ∘ k；g ∘ k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.of_isBigOWith`：∀ {α : Type u_1} {E : Type u_3} {F 
: Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filte
r α},   (∀ ⦃c : ℝ⦄, 0 < c…
· 使用定理 `Asymptotics.IsBigOWith.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E 
: Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E}
   {g : α → F} {l : Filte…
· 使用定理 `Asymptotics.IsLittleO.forall_isBigOWith`：∀ {α : Type u_1} {E : Type u_3}
 {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : F
ilter α},   f =o[l] g → ∀ ⦃c …
-/
theorem IsLittleO.comp_tendsto (hfg : f =o[l] g) {k : β → α} {l' : Filter β} (hk : Tendsto k l' l) :
    (f ∘ k) =o[l'] (g ∘ k) :=
  IsLittleO.of_isBigOWith fun _c cpos => (hfg.forall_isBigOWith cpos).comp_tendsto hk

@[simp]
/-
**Asymptotics.isBigOWith_map** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOWith_map {k : β -> α} {l : Filter β} : IsBigOWith c (map k l) f g ↔ 
IsBigOWith c l (f ∘ k) (g ∘ k)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.IsBigOWith_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type 
u_20} [inst : Norm E] [inst_1 : Norm F] (c : ℝ) (l : Filter α) (f : α → E)   (g 
: α → F), Asympt…
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
-/
theorem isBigOWith_map {k : β → α} {l : Filter β} :
    IsBigOWith c (map k l) f g ↔ IsBigOWith c l (f ∘ k) (g ∘ k) := by
  simp only [IsBigOWith_def]
  exact eventually_map

@[simp]
/-
**Asymptotics.isBigO_map** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_map {k : β -> α} {l : Filter β} : f =O[map k l] g ↔ (f ∘ k) =O[l] (
g ∘ k)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.IsBigO_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type u_20
} [inst : Norm E] [inst_1 : Norm F] (l : Filter α) (f : α → E)   (g : α → F), f 
=O[l] g = ∃ …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isBigO_map {k : β → α} {l : Filter β} : f =O[map k l] g ↔ (f ∘ k) =O[l] (g ∘ k) := by
  simp only [IsBigO_def, isBigOWith_map]

@[simp]
/-
**Asymptotics.isLittleO_map** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_map {k : β -> α} {l : Filter β} : f =o[map k l] g ↔ (f ∘ k) =o[l
] (g ∘ k)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.IsLittleO_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type u
_20} [inst : Norm E] [inst_1 : Norm F] (l : Filter α) (f : α → E)   (g : α → F),
 f =o[l] g = ∀ …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isLittleO_map {k : β → α} {l : Filter β} : f =o[map k l] g ↔ (f ∘ k) =o[l] (g ∘ k) := by
  simp only [IsLittleO_def, isBigOWith_map]
/-
**Asymptotics.IsBigOWith.mono** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigOWith`
。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : N
orm F] {c : ℝ} {f : α → E} {g : α → F}   {l l' : Filter α}, Asymptotics.IsBigOWi
th c l' f g → l ≤ l' → Asymptotics.IsBigOWith c l f g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.of_bound`：∀ {α : Type u_1} {E : Type u_3} {F : Ty
pe u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l :
 Filter α}, (∀ᶠ (x : …
· 使用定理 `Asymptotics.IsBigOWith.bound`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : Fi
lter α}, Asymptoti…
-/
theorem IsBigOWith.mono (h : IsBigOWith c l' f g) (hl : l ≤ l') : IsBigOWith c l f g :=
  IsBigOWith.of_bound <| hl h.bound
/-
**Asymptotics.IsBigO.mono** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : N
orm F] {f : α → E} {g : α → F}   {l l' : Filter α}, f =O[l'] g → l ≤ l' → f =O[l
] g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Asymptotics.isBigO_iff_isBigOWith`：isBigO_iff_isBigOWith : f =O[l] g ↔ e
xists c : Real, IsBigOWith c l f g
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Asymptotics.IsBigOWith.mono`：∀ {α : Type u_1} {E : Type u_3} {F : Type u
_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l l' : 
Filter α}, Asympt…
· 使用定理 `Asymptotics.IsBigO.isBigOWith`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α}, 
  f =O[l] g → ∃ c, …
-/
theorem IsBigO.mono (h : f =O[l'] g) (hl : l ≤ l') : f =O[l] g :=
  isBigO_iff_isBigOWith.2 <| h.isBigOWith.imp fun _c h => h.mono hl
/-
**Asymptotics.IsLittleO.mono** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLittleO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : N
orm F] {f : α → E} {g : α → F}   {l l' : Filter α}, f =o[l'] g → l ≤ l' → f =o[l
] g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.of_isBigOWith`：∀ {α : Type u_1} {E : Type u_3} {F 
: Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filte
r α},   (∀ ⦃c : ℝ⦄, 0 < c…
· 使用定理 `Asymptotics.IsBigOWith.mono`：∀ {α : Type u_1} {E : Type u_3} {F : Type u
_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l l' : 
Filter α}, Asympt…
· 使用定理 `Asymptotics.IsLittleO.forall_isBigOWith`：∀ {α : Type u_1} {E : Type u_3}
 {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : F
ilter α},   f =o[l] g → ∀ ⦃c …
-/
theorem IsLittleO.mono (h : f =o[l'] g) (hl : l ≤ l') : f =o[l] g :=
  IsLittleO.of_isBigOWith fun _c cpos => (h.forall_isBigOWith cpos).mono hl
/-
**Asymptotics.IsBigOWith.trans** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigOWith
`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} {G : Type u_5} [inst : Norm
 E] [inst_1 : Norm F] [inst_2 : Norm G]   {c c' : ℝ} {f : α → E} {g : α → F} {k 
: α → G} {l : Filter α},   Asymptotics.IsBigOWith c l f g → Asymptotics.IsBigOWi
th c' l g k → 0 ≤ c → Asymptotics.IsBigOWith (c * c') l f k
参数：c * c'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type 
u_20} [inst : Norm E] [inst_1 : Norm F] (c : ℝ) (l : Filter α) (f : α → E)   (g 
: α → F), Asympt…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem IsBigOWith.trans (hfg : IsBigOWith c l f g) (hgk : IsBigOWith c' l g k) (hc : 0 ≤ c) :
    IsBigOWith (c * c') l f k := by
  simp only [IsBigOWith_def] at *
  filter_upwards [hfg, hgk] with x hx hx'
  calc
    ‖f x‖ ≤ c * ‖g x‖ := hx
    _ ≤ c * (c' * ‖k x‖) := by gcongr
    _ = c * c' * ‖k x‖ := (mul_assoc _ _ _).symm

@[trans]
/-
**Asymptotics.IsBigO.trans** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5} {F' : Type u_7} [inst : Nor
m E] [inst_1 : Norm G]   [inst_2 : SeminormedAddCommGroup F'] {l : Filter α} {f 
: α → E} {g : α → F'} {k : α → G},   f =O[l] g → g =O[l] k → f =O[l] k
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.exists_nonneg`：∀ {α : Type u_1} {E : Type u_3} {F' : 
Type u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {f : α → E}   {g'
 : α → F'} {l : Filter…
· 使用定理 `Asymptotics.IsBigO.isBigOWith`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α}, 
  f =O[l] g → ∃ c, …
· 使用定理 `Asymptotics.IsBigOWith.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : F
ilter α}, Asymptoti…
· 使用定理 `Asymptotics.IsBigOWith.trans`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} {G : Type u_5} [inst : Norm E] [inst_1 : Norm F] [inst_2 : Norm G]   {c c' 
: ℝ} {f : α → E} {…
-/
theorem IsBigO.trans {f : α → E} {g : α → F'} {k : α → G} (hfg : f =O[l] g) (hgk : g =O[l] k) :
    f =O[l] k :=
  let ⟨_c, cnonneg, hc⟩ := hfg.exists_nonneg
  let ⟨_c', hc'⟩ := hgk.isBigOWith
  (hc.trans hc' cnonneg).isBigO
/-
**Asymptotics.transIsBigOIsBigO** 是 Mathlib 中的一个实例，位于命名空间 `Asymptotics`。
形式化陈述：transIsBigOIsBigO : @Trans (α -> E) (α -> F') (α -> G) (· =O[l] ·) (· =O[l
] ·) (· =O[l] ·) where trans
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5}
 {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddComm
Group F'] {l :…
-/
instance transIsBigOIsBigO :
    @Trans (α → E) (α → F') (α → G) (· =O[l] ·) (· =O[l] ·) (· =O[l] ·) where
  trans := IsBigO.trans
/-
**Asymptotics.IsLittleO.trans_isBigOWith** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.
IsLittleO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} {G : Type u_5} [inst : Norm
 E] [inst_1 : Norm F] [inst_2 : Norm G]   {c : ℝ} {f : α → E} {g : α → F} {k : α
 → G} {l : Filter α},   f =o[l] g → Asymptotics.IsBigOWith c l g k → 0 < c → f =
o[l] k
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type u
_20} [inst : Norm E] [inst_1 : Norm F] (l : Filter α) (f : α → E)   (g : α → F),
 f =o[l] g = ∀ …
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Asymptotics.IsBigOWith.congr_const`：∀ {α : Type u_1} {E : Type u_3} {F :
 Type u_4} [inst : Norm E] [inst_1 : Norm F] {c₁ c₂ : ℝ} {f : α → E} {g : α → F}
   {l : Filter α}, Asymp…
· 使用定理 `Asymptotics.IsBigOWith.trans`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} {G : Type u_5} [inst : Norm E] [inst_1 : Norm F] [inst_2 : Norm G]   {c c' 
: ℝ} {f : α → E} {…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem IsLittleO.trans_isBigOWith (hfg : f =o[l] g) (hgk : IsBigOWith c l g k) (hc : 0 < c) :
    f =o[l] k := by
  simp only [IsLittleO_def] at *
  intro c' c'pos
  have : 0 < c' / c := div_pos c'pos hc
  exact ((hfg this).trans hgk this.le).congr_const (div_mul_cancel₀ _ hc.ne')

@[trans]
/-
**Asymptotics.IsLittleO.trans_isBigO** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLi
ttleO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} {G' : Type u_8} [inst : Nor
m E] [inst_1 : Norm F]   [inst_2 : SeminormedAddCommGroup G'] {l : Filter α} {f 
: α → E} {g : α → F} {k : α → G'},   f =o[l] g → g =O[l] k → f =o[l] k
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.exists_pos`：∀ {α : Type u_1} {E : Type u_3} {F' : Typ
e u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {f : α → E}   {g' : 
α → F'} {l : Filter…
· 使用定理 `Asymptotics.IsLittleO.trans_isBigOWith`：∀ {α : Type u_1} {E : Type u_3} 
{F : Type u_4} {G : Type u_5} [inst : Norm E] [inst_1 : Norm F] [inst_2 : Norm G
]   {c : ℝ} {f : α → E} {g :…
-/
theorem IsLittleO.trans_isBigO {f : α → E} {g : α → F} {k : α → G'} (hfg : f =o[l] g)
    (hgk : g =O[l] k) : f =o[l] k :=
  let ⟨_c, cpos, hc⟩ := hgk.exists_pos
  hfg.trans_isBigOWith hc cpos
/-
**Asymptotics.transIsLittleOIsBigO** 是 Mathlib 中的一个实例，位于命名空间 `Asymptotics`。
形式化陈述：transIsLittleOIsBigO : @Trans (α -> E) (α -> F) (α -> G') (· =o[l] ·) (· =
O[l] ·) (· =o[l] ·) where trans
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.trans_isBigO`：∀ {α : Type u_1} {E : Type u_3} {F :
 Type u_4} {G' : Type u_8} [inst : Norm E] [inst_1 : Norm F]   [inst_2 : Seminor
medAddCommGroup G'] {l :…
-/
instance transIsLittleOIsBigO :
    @Trans (α → E) (α → F) (α → G') (· =o[l] ·) (· =O[l] ·) (· =o[l] ·) where
  trans := IsLittleO.trans_isBigO
/-
**Asymptotics.IsBigOWith.trans_isLittleO** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.
IsBigOWith`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} {G : Type u_5} [inst : Norm
 E] [inst_1 : Norm F] [inst_2 : Norm G]   {c : ℝ} {f : α → E} {g : α → F} {k : α
 → G} {l : Filter α},   Asymptotics.IsBigOWith c l f g → g =o[l] k → 0 < c → f =
o[l] k
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type u
_20} [inst : Norm E] [inst_1 : Norm F] (l : Filter α) (f : α → E)   (g : α → F),
 f =o[l] g = ∀ …
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Asymptotics.IsBigOWith.congr_const`：∀ {α : Type u_1} {E : Type u_3} {F :
 Type u_4} [inst : Norm E] [inst_1 : Norm F] {c₁ c₂ : ℝ} {f : α → E} {g : α → F}
   {l : Filter α}, Asymp…
· 使用定理 `Asymptotics.IsBigOWith.trans`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} {G : Type u_5} [inst : Norm E] [inst_1 : Norm F] [inst_2 : Norm G]   {c c' 
: ℝ} {f : α → E} {…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `mul_div_cancel₀`：mul_div_cancel₀ (a : G₀) (hb : b != 0) : b * (a / b) = 
a
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem IsBigOWith.trans_isLittleO (hfg : IsBigOWith c l f g) (hgk : g =o[l] k) (hc : 0 < c) :
    f =o[l] k := by
  simp only [IsLittleO_def] at *
  intro c' c'pos
  have : 0 < c' / c := div_pos c'pos hc
  exact (hfg.trans (hgk this) hc.le).congr_const (mul_div_cancel₀ _ hc.ne')

@[trans]
/-
**Asymptotics.IsBigO.trans_isLittleO** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBi
gO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5} {F' : Type u_7} [inst : Nor
m E] [inst_1 : Norm G]   [inst_2 : SeminormedAddCommGroup F'] {l : Filter α} {f 
: α → E} {g : α → F'} {k : α → G},   f =O[l] g → g =o[l] k → f =o[l] k
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.exists_pos`：∀ {α : Type u_1} {E : Type u_3} {F' : Typ
e u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {f : α → E}   {g' : 
α → F'} {l : Filter…
· 使用定理 `Asymptotics.IsBigOWith.trans_isLittleO`：∀ {α : Type u_1} {E : Type u_3} 
{F : Type u_4} {G : Type u_5} [inst : Norm E] [inst_1 : Norm F] [inst_2 : Norm G
]   {c : ℝ} {f : α → E} {g :…
-/
theorem IsBigO.trans_isLittleO {f : α → E} {g : α → F'} {k : α → G} (hfg : f =O[l] g)
    (hgk : g =o[l] k) : f =o[l] k :=
  let ⟨_c, cpos, hc⟩ := hfg.exists_pos
  hc.trans_isLittleO hgk cpos
/-
**Asymptotics.transIsBigOIsLittleO** 是 Mathlib 中的一个实例，位于命名空间 `Asymptotics`。
形式化陈述：transIsBigOIsLittleO : @Trans (α -> E) (α -> F') (α -> G) (· =O[l] ·) (· =
o[l] ·) (· =o[l] ·) where trans
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans_isLittleO`：∀ {α : Type u_1} {E : Type u_3} {G :
 Type u_5} {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : Seminor
medAddCommGroup F'] {l :…
-/
instance transIsBigOIsLittleO :
    @Trans (α → E) (α → F') (α → G) (· =O[l] ·) (· =o[l] ·) (· =o[l] ·) where
  trans := IsBigO.trans_isLittleO

@[trans]
/-
**Asymptotics.IsLittleO.trans** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLittleO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} {G : Type u_5} [inst : Norm
 E] [inst_1 : Norm F] [inst_2 : Norm G]   {l : Filter α} {f : α → E} {g : α → F}
 {k : α → G}, f =o[l] g → g =o[l] k → f =o[l] k
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.trans_isBigOWith`：∀ {α : Type u_1} {E : Type u_3} 
{F : Type u_4} {G : Type u_5} [inst : Norm E] [inst_1 : Norm F] [inst_2 : Norm G
]   {c : ℝ} {f : α → E} {g :…
· 使用定理 `Asymptotics.IsLittleO.isBigOWith`：∀ {α : Type u_1} {E : Type u_3} {F : T
ype u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α
},   f =o[l] g → Asymp…
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem IsLittleO.trans {f : α → E} {g : α → F} {k : α → G} (hfg : f =o[l] g) (hgk : g =o[l] k) :
    f =o[l] k :=
  hfg.trans_isBigOWith hgk.isBigOWith one_pos
/-
**Asymptotics.transIsLittleOIsLittleO** 是 Mathlib 中的一个实例，位于命名空间 `Asymptotics`。
形式化陈述：transIsLittleOIsLittleO : @Trans (α -> E) (α -> F) (α -> G) (· =o[l] ·) (·
 =o[l] ·) (· =o[l] ·) where trans
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.trans`：∀ {α : Type u_1} {E : Type u_3} {F : Type u
_4} {G : Type u_5} [inst : Norm E] [inst_1 : Norm F] [inst_2 : Norm G]   {l : Fi
lter α} {f : α → …
-/
instance transIsLittleOIsLittleO :
    @Trans (α → E) (α → F) (α → G) (· =o[l] ·) (· =o[l] ·) (· =o[l] ·) where
  trans := IsLittleO.trans
/-
**Asymptotics._root_.Filter.Eventually.trans_isBigO** 是 Mathlib 中的一个定理，位于命名空间 `A
symptotics`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Filter.Eventually.trans_isBigO {f : α → E} {g : α → F'} {k : α → G}
    (hfg : ∀ᶠ x in l, ‖f x‖ ≤ ‖g x‖) (hgk : g =O[l] k) : f =O[l] k :=
  (IsBigO.of_bound' hfg).trans hgk

/-- See also `Asymptotics.IsBigO.of_norm_eventuallyLE`, which is the same lemma
stated using `Filter.EventuallyLE` instead of `Filter.Eventually`. -/
/-
**Asymptotics._root_.Filter.Eventually.isBigO** 是 Mathlib 中的一个定理，位于命名空间 `Asympto
tics`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See also `Asymptotics.IsBigO.of_norm_eventuallyLE`, which is the same lemma
stated using `Filter.EventuallyLE` instead of `Filter.Eventually`.
-/
theorem _root_.Filter.Eventually.isBigO {f : α → E} {g : α → ℝ} {l : Filter α}
    (hfg : ∀ᶠ x in l, ‖f x‖ ≤ g x) : f =O[l] g :=
  .of_norm_eventuallyLE hfg

section

variable (l)

/-
**Asymptotics.isBigOWith_of_le'** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOWith_of_le' (hfg : forall x, ‖f x‖ <= c * ‖g x‖) : IsBigOWith c l f 
g
参数：hfg : forall x, ‖f x‖ <= c * ‖g x‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.of_bound`：∀ {α : Type u_1} {E : Type u_3} {F : Ty
pe u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l :
 Filter α}, (∀ᶠ (x : …
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
theorem isBigOWith_of_le' (hfg : ∀ x, ‖f x‖ ≤ c * ‖g x‖) : IsBigOWith c l f g :=
  IsBigOWith.of_bound <| univ_mem' hfg
/-
**Asymptotics.isBigOWith_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOWith_of_le (hfg : forall x, ‖f x‖ <= ‖g x‖) : IsBigOWith 1 l f g
参数：hfg : forall x, ‖f x‖ <= ‖g x‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isBigOWith_of_le'`：isBigOWith_of_le' (hfg : forall x, ‖f x‖ 
<= c * ‖g x‖) : IsBigOWith c l f g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem isBigOWith_of_le (hfg : ∀ x, ‖f x‖ ≤ ‖g x‖) : IsBigOWith 1 l f g :=
  isBigOWith_of_le' l fun x => by
    rw [one_mul]
    exact hfg x
/-
**Asymptotics.isBigO_of_le'** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_of_le' (hfg : forall x, ‖f x‖ <= c * ‖g x‖) : f =O[l] g
参数：hfg : forall x, ‖f x‖ <= c * ‖g x‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : F
ilter α}, Asymptoti…
· 使用定理 `Asymptotics.isBigOWith_of_le'`：isBigOWith_of_le' (hfg : forall x, ‖f x‖ 
<= c * ‖g x‖) : IsBigOWith c l f g
-/
theorem isBigO_of_le' (hfg : ∀ x, ‖f x‖ ≤ c * ‖g x‖) : f =O[l] g :=
  (isBigOWith_of_le' l hfg).isBigO
/-
**Asymptotics.isBigO_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_of_le (hfg : forall x, ‖f x‖ <= ‖g x‖) : f =O[l] g
参数：hfg : forall x, ‖f x‖ <= ‖g x‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : F
ilter α}, Asymptoti…
· 使用定理 `Asymptotics.isBigOWith_of_le`：isBigOWith_of_le (hfg : forall x, ‖f x‖ <=
 ‖g x‖) : IsBigOWith 1 l f g
-/
theorem isBigO_of_le (hfg : ∀ x, ‖f x‖ ≤ ‖g x‖) : f =O[l] g :=
  (isBigOWith_of_le l hfg).isBigO

end

@[refl]
/-
**Asymptotics.isBigOWith_refl** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOWith_refl (f : α -> E) (l : Filter α) : IsBigOWith 1 l f f
参数：f : α -> E；l : Filter α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isBigOWith_of_le`：isBigOWith_of_le (hfg : forall x, ‖f x‖ <=
 ‖g x‖) : IsBigOWith 1 l f g
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem isBigOWith_refl (f : α → E) (l : Filter α) : IsBigOWith 1 l f f :=
  isBigOWith_of_le l fun _ => le_rfl

@[refl]
/-
**Asymptotics.isBigO_refl** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_refl (f : α -> E) (l : Filter α) : f =O[l] f
参数：f : α -> E；l : Filter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : F
ilter α}, Asymptoti…
· 使用定理 `Asymptotics.isBigOWith_refl`：isBigOWith_refl (f : α -> E) (l : Filter α)
 : IsBigOWith 1 l f f
-/
theorem isBigO_refl (f : α → E) (l : Filter α) : f =O[l] f :=
  (isBigOWith_refl f l).isBigO
/-
**Asymptotics._root_.Filter.EventuallyEq.isBigO** 是 Mathlib 中的一个定理，位于命名空间 `Asymp
totics`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Filter.EventuallyEq.isBigO {f₁ f₂ : α → E} (hf : f₁ =ᶠ[l] f₂) : f₁ =O[l] f₂ :=
  hf.trans_isBigO (isBigO_refl _ _)
/-
**Asymptotics.IsBigOWith.trans_le** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigOW
ith`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} {G : Type u_5} [inst : Norm
 E] [inst_1 : Norm F] [inst_2 : Norm G]   {c : ℝ} {f : α → E} {g : α → F} {k : α
 → G} {l : Filter α},   Asymptotics.IsBigOWith c l f g → (∀ (x : α), ‖g x‖ ≤ ‖k 
x‖) → 0 ≤ c → Asymptotics.IsBigOWith c l f k
参数：∀ (x : α), ‖g x‖ ≤ ‖k x‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.congr_const`：∀ {α : Type u_1} {E : Type u_3} {F :
 Type u_4} [inst : Norm E] [inst_1 : Norm F] {c₁ c₂ : ℝ} {f : α → E} {g : α → F}
   {l : Filter α}, Asymp…
· 使用定理 `Asymptotics.IsBigOWith.trans`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} {G : Type u_5} [inst : Norm E] [inst_1 : Norm F] [inst_2 : Norm G]   {c c' 
: ℝ} {f : α → E} {…
· 使用定理 `Asymptotics.isBigOWith_of_le`：isBigOWith_of_le (hfg : forall x, ‖f x‖ <=
 ‖g x‖) : IsBigOWith 1 l f g
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem IsBigOWith.trans_le (hfg : IsBigOWith c l f g) (hgk : ∀ x, ‖g x‖ ≤ ‖k x‖) (hc : 0 ≤ c) :
    IsBigOWith c l f k :=
  (hfg.trans (isBigOWith_of_le l hgk) hc).congr_const <| mul_one c
/-
**Asymptotics.IsBigO.trans_le** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5} {F' : Type u_7} [inst : Nor
m E] [inst_1 : Norm G]   [inst_2 : SeminormedAddCommGroup F'] {f : α → E} {k : α
 → G} {g' : α → F'} {l : Filter α},   f =O[l] g' → (∀ (x : α), ‖g' x‖ ≤ ‖k x‖) →
 f =O[l] k
参数：∀ (x : α), ‖g' x‖ ≤ ‖k x‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5}
 {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddComm
Group F'] {l :…
· 使用定理 `Asymptotics.isBigO_of_le`：isBigO_of_le (hfg : forall x, ‖f x‖ <= ‖g x‖) 
: f =O[l] g
-/
theorem IsBigO.trans_le (hfg : f =O[l] g') (hgk : ∀ x, ‖g' x‖ ≤ ‖k x‖) : f =O[l] k :=
  hfg.trans (isBigO_of_le l hgk)
/-
**Asymptotics.IsLittleO.trans_le** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLittle
O`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} {G : Type u_5} [inst : Norm
 E] [inst_1 : Norm F] [inst_2 : Norm G]   {f : α → E} {g : α → F} {k : α → G} {l
 : Filter α}, f =o[l] g → (∀ (x : α), ‖g x‖ ≤ ‖k x‖) → f =o[l] k
参数：∀ (x : α), ‖g x‖ ≤ ‖k x‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.trans_isBigOWith`：∀ {α : Type u_1} {E : Type u_3} 
{F : Type u_4} {G : Type u_5} [inst : Norm E] [inst_1 : Norm F] [inst_2 : Norm G
]   {c : ℝ} {f : α → E} {g :…
· 使用定理 `Asymptotics.isBigOWith_of_le`：isBigOWith_of_le (hfg : forall x, ‖f x‖ <=
 ‖g x‖) : IsBigOWith 1 l f g
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem IsLittleO.trans_le (hfg : f =o[l] g) (hgk : ∀ x, ‖g x‖ ≤ ‖k x‖) : f =o[l] k :=
  hfg.trans_isBigOWith (isBigOWith_of_le _ hgk) zero_lt_one
/-
**Asymptotics.isLittleO_irrefl'** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_irrefl' (h : existsᶠ x in l, ‖f' x‖ != 0) : ¬f' =o[l] f'
参数：h : existsᶠ x in l, ‖f' x‖ != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Filter.Frequently.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Filter.Eventually.and_frequently`：∀ {α : Type u} {p q : α → Prop} {f : F
ilter α},   (∀ᶠ (x : α) in f, p x) → (∃ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p
 x ∧ q x
· 使用定理 `Asymptotics.IsLittleO.bound`：∀ {α : Type u_1} {E : Type u_3} {F : Type u
_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},   
f =o[l] g → ∀ ⦃c …
· 使用定理 `one_half_pos`：one_half_pos : (0 : α) < 1 / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `half_lt_self`：∀ {α : Type u_2} [inst : Semifield α] [inst_1 : PartialOrd
er α] [PosMulReflectLT α] {a : α} [IsStrictOrderedRing α],   0 < a → a / 2 < a
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
-/
theorem isLittleO_irrefl' (h : ∃ᶠ x in l, ‖f' x‖ ≠ 0) : ¬f' =o[l] f' := by
  intro ho
  rcases ((ho.bound one_half_pos).and_frequently h).exists with ⟨x, hle, hne⟩
  rw [one_div, ← div_eq_inv_mul] at hle
  exact (half_lt_self (lt_of_le_of_ne (norm_nonneg _) hne.symm)).not_ge hle
/-
**Asymptotics.isLittleO_irrefl** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_irrefl (h : existsᶠ x in l, f'' x != 0) : ¬f'' =o[l] f''
参数：h : existsᶠ x in l, f'' x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isLittleO_irrefl'`：isLittleO_irrefl' (h : existsᶠ x in l, ‖f
' x‖ != 0) : ¬f' =o[l] f'
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0
-/
theorem isLittleO_irrefl (h : ∃ᶠ x in l, f'' x ≠ 0) : ¬f'' =o[l] f'' :=
  isLittleO_irrefl' <| h.mono fun _x => norm_ne_zero_iff.mpr
/-
**Asymptotics.IsBigO.not_isLittleO** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO
`。
形式化陈述：∀ {α : Type u_1} {F' : Type u_7} {E'' : Type u_9} [inst : SeminormedAddCom
mGroup F'] [inst_1 : NormedAddCommGroup E'']   {g' : α → F'} {f'' : α → E''} {l 
: Filter α}, f'' =O[l] g' → (∃ᶠ (x : α) in l, f'' x ≠ 0) → ¬g' =o[l] f''
参数：∃ᶠ (x : α) in l, f'' x ≠ 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isLittleO_irrefl`：isLittleO_irrefl (h : existsᶠ x in l, f'' 
x != 0) : ¬f'' =o[l] f''
· 使用定理 `Asymptotics.IsBigO.trans_isLittleO`：∀ {α : Type u_1} {E : Type u_3} {G :
 Type u_5} {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : Seminor
medAddCommGroup F'] {l :…
-/
theorem IsBigO.not_isLittleO (h : f'' =O[l] g') (hf : ∃ᶠ x in l, f'' x ≠ 0) :
    ¬g' =o[l] f'' := fun h' =>
  isLittleO_irrefl hf (h.trans_isLittleO h')
/-
**Asymptotics.IsLittleO.not_isBigO** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLitt
leO`。
形式化陈述：∀ {α : Type u_1} {F' : Type u_7} {E'' : Type u_9} [inst : SeminormedAddCom
mGroup F'] [inst_1 : NormedAddCommGroup E'']   {g' : α → F'} {f'' : α → E''} {l 
: Filter α}, f'' =o[l] g' → (∃ᶠ (x : α) in l, f'' x ≠ 0) → ¬g' =O[l] f''
参数：∃ᶠ (x : α) in l, f'' x ≠ 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isLittleO_irrefl`：isLittleO_irrefl (h : existsᶠ x in l, f'' 
x != 0) : ¬f'' =o[l] f''
· 使用定理 `Asymptotics.IsLittleO.trans_isBigO`：∀ {α : Type u_1} {E : Type u_3} {F :
 Type u_4} {G' : Type u_8} [inst : Norm E] [inst_1 : Norm F]   [inst_2 : Seminor
medAddCommGroup G'] {l :…
-/
theorem IsLittleO.not_isBigO (h : f'' =o[l] g') (hf : ∃ᶠ x in l, f'' x ≠ 0) :
    ¬g' =O[l] f'' := fun h' =>
  isLittleO_irrefl hf (h.trans_isBigO h')

section Bot

variable (c f g)

@[simp]
/-
**Asymptotics.isBigOWith_bot** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOWith_bot : IsBigOWith c ⊥ f g
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.of_bound`：∀ {α : Type u_1} {E : Type u_3} {F : Ty
pe u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l :
 Filter α}, (∀ᶠ (x : …
· 使用定理 `trivial`：True
-/
theorem isBigOWith_bot : IsBigOWith c ⊥ f g :=
  IsBigOWith.of_bound <| trivial

@[simp]
/-
**Asymptotics.isBigO_bot** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_bot : f =O[⊥] g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : F
ilter α}, Asymptoti…
· 使用定理 `Asymptotics.isBigOWith_bot`：isBigOWith_bot : IsBigOWith c ⊥ f g
-/
theorem isBigO_bot : f =O[⊥] g :=
  (isBigOWith_bot 1 f g).isBigO

@[simp]
/-
**Asymptotics.isLittleO_bot** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_bot : f =o[⊥] g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.of_isBigOWith`：∀ {α : Type u_1} {E : Type u_3} {F 
: Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filte
r α},   (∀ ⦃c : ℝ⦄, 0 < c…
· 使用定理 `Asymptotics.isBigOWith_bot`：isBigOWith_bot : IsBigOWith c ⊥ f g
-/
theorem isLittleO_bot : f =o[⊥] g :=
  IsLittleO.of_isBigOWith fun c _ => isBigOWith_bot c f g

end Bot

@[simp]
/-
**Asymptotics.isBigOWith_pure** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOWith_pure {x} : IsBigOWith c (pure x) f g ↔ ‖f x‖ <= c * ‖g x‖
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isBigOWith_iff`：isBigOWith_iff : IsBigOWith c l f g ↔ forall
ᶠ x in l, ‖f x‖ <= c * ‖g x‖
-/
theorem isBigOWith_pure {x} : IsBigOWith c (pure x) f g ↔ ‖f x‖ ≤ c * ‖g x‖ :=
  isBigOWith_iff
/-
**Asymptotics.IsBigOWith.sup** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigOWith`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : N
orm F] {c : ℝ} {f : α → E} {g : α → F}   {l l' : Filter α},   Asymptotics.IsBigO
With c l f g → Asymptotics.IsBigOWith c l' f g → Asymptotics.IsBigOWith c (l ⊔ l
') f g
参数：l ⊔ l'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.of_bound`：∀ {α : Type u_1} {E : Type u_3} {F : Ty
pe u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l :
 Filter α}, (∀ᶠ (x : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.mem_sup`：mem_sup {f g : Filter α} {s : Set α} : s in f ⊔ g ↔ s in
 f ∧ s in g
· 使用定理 `Asymptotics.IsBigOWith.bound`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : Fi
lter α}, Asymptoti…
-/
theorem IsBigOWith.sup (h : IsBigOWith c l f g) (h' : IsBigOWith c l' f g) :
    IsBigOWith c (l ⊔ l') f g :=
  IsBigOWith.of_bound <| mem_sup.2 ⟨h.bound, h'.bound⟩
/-
**Asymptotics.IsBigOWith.sup'** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigOWith`
。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F' : Type u_7} [inst : Norm E] [inst_1 : 
SeminormedAddCommGroup F'] {c c' : ℝ}   {f : α → E} {g' : α → F'} {l l' : Filter
 α},   Asymptotics.IsBigOWith c l f g' → Asymptotics.IsBigOWith c' l' f g' → Asy
mptotics.IsBigOWith (max c c') (l ⊔ l') f g'
参数：max c c'；l ⊔ l'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.of_bound`：∀ {α : Type u_1} {E : Type u_3} {F : Ty
pe u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l :
 Filter α}, (∀ᶠ (x : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.mem_sup`：mem_sup {f g : Filter α} {s : Set α} : s in f ⊔ g ↔ s in
 f ∧ s in g
· 使用定理 `Asymptotics.IsBigOWith.bound`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : Fi
lter α}, Asymptoti…
· 使用定理 `Asymptotics.IsBigOWith.weaken`：∀ {α : Type u_1} {E : Type u_3} {F' : Typ
e u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {c c' : ℝ}   {f : α 
→ E} {g' : α → F'} …
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
-/
theorem IsBigOWith.sup' (h : IsBigOWith c l f g') (h' : IsBigOWith c' l' f g') :
    IsBigOWith (max c c') (l ⊔ l') f g' :=
  IsBigOWith.of_bound <|
    mem_sup.2 ⟨(h.weaken <| le_max_left c c').bound, (h'.weaken <| le_max_right c c').bound⟩
/-
**Asymptotics.IsBigO.sup** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F' : Type u_7} [inst : Norm E] [inst_1 : 
SeminormedAddCommGroup F'] {f : α → E}   {g' : α → F'} {l l' : Filter α}, f =O[l
] g' → f =O[l'] g' → f =O[l ⊔ l'] g'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.isBigOWith`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α}, 
  f =O[l] g → ∃ c, …
· 使用定理 `Asymptotics.IsBigOWith.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : F
ilter α}, Asymptoti…
· 使用定理 `Asymptotics.IsBigOWith.sup'`：∀ {α : Type u_1} {E : Type u_3} {F' : Type 
u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {c c' : ℝ}   {f : α → 
E} {g' : α → F'} …
-/
theorem IsBigO.sup (h : f =O[l] g') (h' : f =O[l'] g') : f =O[l ⊔ l'] g' :=
  let ⟨_c, hc⟩ := h.isBigOWith
  let ⟨_c', hc'⟩ := h'.isBigOWith
  (hc.sup' hc').isBigO
/-
**Asymptotics.IsLittleO.sup** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLittleO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : N
orm F] {f : α → E} {g : α → F}   {l l' : Filter α}, f =o[l] g → f =o[l'] g → f =
o[l ⊔ l'] g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.of_isBigOWith`：∀ {α : Type u_1} {E : Type u_3} {F 
: Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filte
r α},   (∀ ⦃c : ℝ⦄, 0 < c…
· 使用定理 `Asymptotics.IsBigOWith.sup`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_
4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l l' : F
ilter α},   Asym…
· 使用定理 `Asymptotics.IsLittleO.forall_isBigOWith`：∀ {α : Type u_1} {E : Type u_3}
 {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : F
ilter α},   f =o[l] g → ∀ ⦃c …
-/
theorem IsLittleO.sup (h : f =o[l] g) (h' : f =o[l'] g) : f =o[l ⊔ l'] g :=
  IsLittleO.of_isBigOWith fun _c cpos => (h.forall_isBigOWith cpos).sup (h'.forall_isBigOWith cpos)

@[simp]
/-
**Asymptotics.isBigO_sup** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_sup : f =O[l ⊔ l'] g' ↔ f =O[l] g' ∧ f =O[l'] g'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.mono`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} 
[inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}   {l l' : Filter α}, f
 =O[l'] g → l…
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `Asymptotics.IsBigO.sup`：∀ {α : Type u_1} {E : Type u_3} {F' : Type u_7} 
[inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {f : α → E}   {g' : α → F'}
 {l l' : Fil…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem isBigO_sup : f =O[l ⊔ l'] g' ↔ f =O[l] g' ∧ f =O[l'] g' :=
  ⟨fun h => ⟨h.mono le_sup_left, h.mono le_sup_right⟩, fun h => h.1.sup h.2⟩

@[simp]
/-
**Asymptotics.isLittleO_sup** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_sup : f =o[l ⊔ l'] g ↔ f =o[l] g ∧ f =o[l'] g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.mono`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_
4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}   {l l' : Filter α}
, f =o[l'] g → l…
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `Asymptotics.IsLittleO.sup`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4
} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}   {l l' : Filter α},
 f =o[l] g → f …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem isLittleO_sup : f =o[l ⊔ l'] g ↔ f =o[l] g ∧ f =o[l'] g :=
  ⟨fun h => ⟨h.mono le_sup_left, h.mono le_sup_right⟩, fun h => h.1.sup h.2⟩
/-
**Asymptotics.isBigOWith_insert** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOWith_insert [TopologicalSpace α] {x : α} {s : Set α} {C : Real} {g :
 α -> E} {g' : α -> F} (h : ‖g x‖ <= C * ‖g' x‖) : IsBigOWith C (𝓝[insert x s] x
) g g' ↔ IsBigOWith C (𝓝[s] x) g g'
参数：h : ‖g x‖ <= C * ‖g' x‖。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.IsBigOWith_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type 
u_20} [inst : Norm E] [inst_1 : Norm F] (c : ℝ) (l : Filter α) (f : α → E)   (g 
: α → F), Asympt…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nhdsWithin_insert`：nhdsWithin_insert (a : α) (s : Set α) : 𝓝[insert a s]
 a = pure a ⊔ 𝓝[s] a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isBigOWith_insert [TopologicalSpace α] {x : α} {s : Set α} {C : ℝ} {g : α → E} {g' : α → F}
    (h : ‖g x‖ ≤ C * ‖g' x‖) : IsBigOWith C (𝓝[insert x s] x) g g' ↔
    IsBigOWith C (𝓝[s] x) g g' := by
  simp_rw [IsBigOWith_def, nhdsWithin_insert, eventually_sup, eventually_pure, h, true_and]
/-
**Asymptotics.IsBigOWith.insert** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigOWit
h`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : N
orm F] [inst_2 : TopologicalSpace α] {x : α}   {s : Set α} {C : ℝ} {g : α → E} {
g' : α → F},   Asymptotics.IsBigOWith C (nhdsWithin x s) g g' →     ‖g x‖ ≤ C * 
‖g' x‖ → Asymptotics.IsBigOWith C (nhdsWithin x (insert x s)) g g'
参数：nhdsWithin x s；nhdsWithin x (insert x s)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Asymptotics.isBigOWith_insert`：isBigOWith_insert [TopologicalSpace α] {x
 : α} {s : Set α} {C : Real} {g : α -> E} {g' : α -> F} (h : ‖g x‖ <= C * ‖g' x‖
) : IsBigOWith C (𝓝…
-/
protected theorem IsBigOWith.insert [TopologicalSpace α] {x : α} {s : Set α} {C : ℝ} {g : α → E}
    {g' : α → F} (h1 : IsBigOWith C (𝓝[s] x) g g') (h2 : ‖g x‖ ≤ C * ‖g' x‖) :
    IsBigOWith C (𝓝[insert x s] x) g g' :=
  (isBigOWith_insert h2).mpr h1
/-
**Asymptotics.isLittleO_insert** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_insert [TopologicalSpace α] {x : α} {s : Set α} {g : α -> E'} {g
' : α -> F'} (h : g x = 0) : g =o[𝓝[insert x s] x] g' ↔ g =o[𝓝[s] x] g'
参数：h : g x = 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.IsLittleO_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type u
_20} [inst : Norm E] [inst_1 : Norm F] (l : Filter α) (f : α → E)   (g : α → F),
 f =o[l] g = ∀ …
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Asymptotics.isBigOWith_insert`：isBigOWith_insert [TopologicalSpace α] {x
 : α} {s : Set α} {C : Real} {g : α -> E} {g' : α -> F} (h : ‖g x‖ <= C * ‖g' x‖
) : IsBigOWith C (𝓝…
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isLittleO_insert [TopologicalSpace α] {x : α} {s : Set α} {g : α → E'} {g' : α → F'}
    (h : g x = 0) : g =o[𝓝[insert x s] x] g' ↔ g =o[𝓝[s] x] g' := by
  simp_rw [IsLittleO_def]
  refine forall_congr' fun c => forall_congr' fun hc => ?_
  rw [isBigOWith_insert]
  rw [h, norm_zero]
  positivity
/-
**Asymptotics.IsLittleO.insert** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLittleO`
。
形式化陈述：∀ {α : Type u_1} {E' : Type u_6} {F' : Type u_7} [inst : SeminormedAddComm
Group E'] [inst_1 : SeminormedAddCommGroup F']   [inst_2 : TopologicalSpace α] {
x : α} {s : Set α} {g : α → E'} {g' : α → F'},   g =o[nhdsWithin x s] g' → g x =
 0 → g =o[nhdsWithin x (insert x s)] g'
参数：insert x s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Asymptotics.isLittleO_insert`：isLittleO_insert [TopologicalSpace α] {x :
 α} {s : Set α} {g : α -> E'} {g' : α -> F'} (h : g x = 0) : g =o[𝓝[insert x s] 
x] g' ↔ g =o[𝓝[s] …
-/
protected theorem IsLittleO.insert [TopologicalSpace α] {x : α} {s : Set α} {g : α → E'}
    {g' : α → F'} (h1 : g =o[𝓝[s] x] g') (h2 : g x = 0) : g =o[𝓝[insert x s] x] g' :=
  (isLittleO_insert h2).mpr h1

/-! ### Simplification: norm, abs -/


section NormAbs

variable {u v : α → ℝ}

@[simp]
/-
**Asymptotics.isBigOWith_norm_right** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOWith_norm_right : (IsBigOWith c l f fun x => ‖g' x‖) ↔ IsBigOWith c 
l f g'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.IsBigOWith_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type 
u_20} [inst : Norm E] [inst_1 : Norm F] (c : ℝ) (l : Filter α) (f : α → E)   (g 
: α → F), Asympt…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isBigOWith_norm_right : (IsBigOWith c l f fun x => ‖g' x‖) ↔ IsBigOWith c l f g' := by
  simp only [IsBigOWith_def, norm_norm]

@[simp]
/-
**Asymptotics.isBigOWith_abs_right** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOWith_abs_right : (IsBigOWith c l f fun x => |u x|) ↔ IsBigOWith c l 
f u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isBigOWith_norm_right`：isBigOWith_norm_right : (IsBigOWith c
 l f fun x => ‖g' x‖) ↔ IsBigOWith c l f g'
-/
theorem isBigOWith_abs_right : (IsBigOWith c l f fun x => |u x|) ↔ IsBigOWith c l f u :=
  @isBigOWith_norm_right _ _ _ _ _ _ f u l

alias ⟨IsBigOWith.of_norm_right, IsBigOWith.norm_right⟩ := isBigOWith_norm_right

alias ⟨IsBigOWith.of_abs_right, IsBigOWith.abs_right⟩ := isBigOWith_abs_right

@[simp]
/-
**Asymptotics.isBigO_norm_right** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_norm_right : (f =O[l] fun x => ‖g' x‖) ↔ f =O[l] g'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.IsBigO_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type u_20
} [inst : Norm E] [inst_1 : Norm F] (l : Filter α) (f : α → E)   (g : α → F), f 
=O[l] g = ∃ …
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `Asymptotics.isBigOWith_norm_right`：isBigOWith_norm_right : (IsBigOWith c
 l f fun x => ‖g' x‖) ↔ IsBigOWith c l f g'
-/
theorem isBigO_norm_right : (f =O[l] fun x => ‖g' x‖) ↔ f =O[l] g' := by
  simp only [IsBigO_def]
  exact exists_congr fun _ => isBigOWith_norm_right

@[simp]
/-
**Asymptotics.isBigO_abs_right** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_abs_right : (f =O[l] fun x => |u x|) ↔ f =O[l] u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isBigO_norm_right`：isBigO_norm_right : (f =O[l] fun x => ‖g'
 x‖) ↔ f =O[l] g'
-/
theorem isBigO_abs_right : (f =O[l] fun x => |u x|) ↔ f =O[l] u :=
  @isBigO_norm_right _ _ ℝ _ _ _ _ _

alias ⟨IsBigO.of_norm_right, IsBigO.norm_right⟩ := isBigO_norm_right

alias ⟨IsBigO.of_abs_right, IsBigO.abs_right⟩ := isBigO_abs_right

@[simp]
/-
**Asymptotics.isLittleO_norm_right** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_norm_right : (f =o[l] fun x => ‖g' x‖) ↔ f =o[l] g'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.IsLittleO_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type u
_20} [inst : Norm E] [inst_1 : Norm F] (l : Filter α) (f : α → E)   (g : α → F),
 f =o[l] g = ∀ …
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `Asymptotics.isBigOWith_norm_right`：isBigOWith_norm_right : (IsBigOWith c
 l f fun x => ‖g' x‖) ↔ IsBigOWith c l f g'
-/
theorem isLittleO_norm_right : (f =o[l] fun x => ‖g' x‖) ↔ f =o[l] g' := by
  simp only [IsLittleO_def]
  exact forall₂_congr fun _ _ => isBigOWith_norm_right

@[simp]
/-
**Asymptotics.isLittleO_abs_right** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_abs_right : (f =o[l] fun x => |u x|) ↔ f =o[l] u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isLittleO_norm_right`：isLittleO_norm_right : (f =o[l] fun x 
=> ‖g' x‖) ↔ f =o[l] g'
-/
theorem isLittleO_abs_right : (f =o[l] fun x => |u x|) ↔ f =o[l] u :=
  @isLittleO_norm_right _ _ ℝ _ _ _ _ _

alias ⟨IsLittleO.of_norm_right, IsLittleO.norm_right⟩ := isLittleO_norm_right

alias ⟨IsLittleO.of_abs_right, IsLittleO.abs_right⟩ := isLittleO_abs_right

@[simp]
/-
**Asymptotics.isBigOWith_norm_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOWith_norm_left : IsBigOWith c l (fun x => ‖f' x‖) g ↔ IsBigOWith c l
 f' g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.IsBigOWith_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type 
u_20} [inst : Norm E] [inst_1 : Norm F] (c : ℝ) (l : Filter α) (f : α → E)   (g 
: α → F), Asympt…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isBigOWith_norm_left : IsBigOWith c l (fun x => ‖f' x‖) g ↔ IsBigOWith c l f' g := by
  simp only [IsBigOWith_def, norm_norm]

@[simp]
/-
**Asymptotics.isBigOWith_abs_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOWith_abs_left : IsBigOWith c l (fun x => |u x|) g ↔ IsBigOWith c l u
 g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isBigOWith_norm_left`：isBigOWith_norm_left : IsBigOWith c l 
(fun x => ‖f' x‖) g ↔ IsBigOWith c l f' g
-/
theorem isBigOWith_abs_left : IsBigOWith c l (fun x => |u x|) g ↔ IsBigOWith c l u g :=
  @isBigOWith_norm_left _ _ _ _ _ _ g u l

alias ⟨IsBigOWith.of_norm_left, IsBigOWith.norm_left⟩ := isBigOWith_norm_left

alias ⟨IsBigOWith.of_abs_left, IsBigOWith.abs_left⟩ := isBigOWith_abs_left

@[simp]
/-
**Asymptotics.isBigO_norm_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_norm_left : (fun x => ‖f' x‖) =O[l] g ↔ f' =O[l] g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.IsBigO_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type u_20
} [inst : Norm E] [inst_1 : Norm F] (l : Filter α) (f : α → E)   (g : α → F), f 
=O[l] g = ∃ …
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `Asymptotics.isBigOWith_norm_left`：isBigOWith_norm_left : IsBigOWith c l 
(fun x => ‖f' x‖) g ↔ IsBigOWith c l f' g
-/
theorem isBigO_norm_left : (fun x => ‖f' x‖) =O[l] g ↔ f' =O[l] g := by
  simp only [IsBigO_def]
  exact exists_congr fun _ => isBigOWith_norm_left

@[simp]
/-
**Asymptotics.isBigO_abs_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_abs_left : (fun x => |u x|) =O[l] g ↔ u =O[l] g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isBigO_norm_left`：isBigO_norm_left : (fun x => ‖f' x‖) =O[l]
 g ↔ f' =O[l] g
-/
theorem isBigO_abs_left : (fun x => |u x|) =O[l] g ↔ u =O[l] g :=
  @isBigO_norm_left _ _ _ _ _ g u l

alias ⟨IsBigO.of_norm_left, IsBigO.norm_left⟩ := isBigO_norm_left

alias ⟨IsBigO.of_abs_left, IsBigO.abs_left⟩ := isBigO_abs_left

@[simp]
/-
**Asymptotics.isLittleO_norm_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_norm_left : (fun x => ‖f' x‖) =o[l] g ↔ f' =o[l] g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.IsLittleO_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type u
_20} [inst : Norm E] [inst_1 : Norm F] (l : Filter α) (f : α → E)   (g : α → F),
 f =o[l] g = ∀ …
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `Asymptotics.isBigOWith_norm_left`：isBigOWith_norm_left : IsBigOWith c l 
(fun x => ‖f' x‖) g ↔ IsBigOWith c l f' g
-/
theorem isLittleO_norm_left : (fun x => ‖f' x‖) =o[l] g ↔ f' =o[l] g := by
  simp only [IsLittleO_def]
  exact forall₂_congr fun _ _ => isBigOWith_norm_left

@[simp]
/-
**Asymptotics.isLittleO_abs_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_abs_left : (fun x => |u x|) =o[l] g ↔ u =o[l] g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isLittleO_norm_left`：isLittleO_norm_left : (fun x => ‖f' x‖)
 =o[l] g ↔ f' =o[l] g
-/
theorem isLittleO_abs_left : (fun x => |u x|) =o[l] g ↔ u =o[l] g :=
  @isLittleO_norm_left _ _ _ _ _ g u l

alias ⟨IsLittleO.of_norm_left, IsLittleO.norm_left⟩ := isLittleO_norm_left

alias ⟨IsLittleO.of_abs_left, IsLittleO.abs_left⟩ := isLittleO_abs_left
/-
**Asymptotics.isBigOWith_norm_norm** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOWith_norm_norm : (IsBigOWith c l (fun x => ‖f' x‖) fun x => ‖g' x‖) 
↔ IsBigOWith c l f' g'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Asymptotics.isBigOWith_norm_left`：isBigOWith_norm_left : IsBigOWith c l 
(fun x => ‖f' x‖) g ↔ IsBigOWith c l f' g
· 使用定理 `Asymptotics.isBigOWith_norm_right`：isBigOWith_norm_right : (IsBigOWith c
 l f fun x => ‖g' x‖) ↔ IsBigOWith c l f g'
-/
theorem isBigOWith_norm_norm :
    (IsBigOWith c l (fun x => ‖f' x‖) fun x => ‖g' x‖) ↔ IsBigOWith c l f' g' :=
  isBigOWith_norm_left.trans isBigOWith_norm_right
/-
**Asymptotics.isBigOWith_abs_abs** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOWith_abs_abs : (IsBigOWith c l (fun x => |u x|) fun x => |v x|) ↔ Is
BigOWith c l u v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Asymptotics.isBigOWith_abs_left`：isBigOWith_abs_left : IsBigOWith c l (f
un x => |u x|) g ↔ IsBigOWith c l u g
· 使用定理 `Asymptotics.isBigOWith_abs_right`：isBigOWith_abs_right : (IsBigOWith c l
 f fun x => |u x|) ↔ IsBigOWith c l f u
-/
theorem isBigOWith_abs_abs :
    (IsBigOWith c l (fun x => |u x|) fun x => |v x|) ↔ IsBigOWith c l u v :=
  isBigOWith_abs_left.trans isBigOWith_abs_right

alias ⟨IsBigOWith.of_norm_norm, IsBigOWith.norm_norm⟩ := isBigOWith_norm_norm

alias ⟨IsBigOWith.of_abs_abs, IsBigOWith.abs_abs⟩ := isBigOWith_abs_abs
/-
**Asymptotics.isBigO_norm_norm** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_norm_norm : ((fun x => ‖f' x‖) =O[l] fun x => ‖g' x‖) ↔ f' =O[l] g'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Asymptotics.isBigO_norm_left`：isBigO_norm_left : (fun x => ‖f' x‖) =O[l]
 g ↔ f' =O[l] g
· 使用定理 `Asymptotics.isBigO_norm_right`：isBigO_norm_right : (f =O[l] fun x => ‖g'
 x‖) ↔ f =O[l] g'
-/
theorem isBigO_norm_norm : ((fun x => ‖f' x‖) =O[l] fun x => ‖g' x‖) ↔ f' =O[l] g' :=
  isBigO_norm_left.trans isBigO_norm_right
/-
**Asymptotics.isBigO_abs_abs** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_abs_abs : ((fun x => |u x|) =O[l] fun x => |v x|) ↔ u =O[l] v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Asymptotics.isBigO_abs_left`：isBigO_abs_left : (fun x => |u x|) =O[l] g 
↔ u =O[l] g
· 使用定理 `Asymptotics.isBigO_abs_right`：isBigO_abs_right : (f =O[l] fun x => |u x|
) ↔ f =O[l] u
-/
theorem isBigO_abs_abs : ((fun x => |u x|) =O[l] fun x => |v x|) ↔ u =O[l] v :=
  isBigO_abs_left.trans isBigO_abs_right

alias ⟨IsBigO.of_norm_norm, IsBigO.norm_norm⟩ := isBigO_norm_norm

alias ⟨IsBigO.of_abs_abs, IsBigO.abs_abs⟩ := isBigO_abs_abs
/-
**Asymptotics.isLittleO_norm_norm** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_norm_norm : ((fun x => ‖f' x‖) =o[l] fun x => ‖g' x‖) ↔ f' =o[l]
 g'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Asymptotics.isLittleO_norm_left`：isLittleO_norm_left : (fun x => ‖f' x‖)
 =o[l] g ↔ f' =o[l] g
· 使用定理 `Asymptotics.isLittleO_norm_right`：isLittleO_norm_right : (f =o[l] fun x 
=> ‖g' x‖) ↔ f =o[l] g'
-/
theorem isLittleO_norm_norm : ((fun x => ‖f' x‖) =o[l] fun x => ‖g' x‖) ↔ f' =o[l] g' :=
  isLittleO_norm_left.trans isLittleO_norm_right
/-
**Asymptotics.isLittleO_abs_abs** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_abs_abs : ((fun x => |u x|) =o[l] fun x => |v x|) ↔ u =o[l] v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Asymptotics.isLittleO_abs_left`：isLittleO_abs_left : (fun x => |u x|) =o
[l] g ↔ u =o[l] g
· 使用定理 `Asymptotics.isLittleO_abs_right`：isLittleO_abs_right : (f =o[l] fun x =>
 |u x|) ↔ f =o[l] u
-/
theorem isLittleO_abs_abs : ((fun x => |u x|) =o[l] fun x => |v x|) ↔ u =o[l] v :=
  isLittleO_abs_left.trans isLittleO_abs_right

alias ⟨IsLittleO.of_norm_norm, IsLittleO.norm_norm⟩ := isLittleO_norm_norm

alias ⟨IsLittleO.of_abs_abs, IsLittleO.abs_abs⟩ := isLittleO_abs_abs

end NormAbs

/-! ### Simplification: negate -/


@[simp]
/-
**Asymptotics.isBigOWith_neg_right** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOWith_neg_right : (IsBigOWith c l f fun x => -g' x) ↔ IsBigOWith c l 
f g'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.IsBigOWith_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type 
u_20} [inst : Norm E] [inst_1 : Norm F] (c : ℝ) (l : Filter α) (f : α → E)   (g 
: α → F), Asympt…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
### Simplification: negate
-/
theorem isBigOWith_neg_right : (IsBigOWith c l f fun x => -g' x) ↔ IsBigOWith c l f g' := by
  simp only [IsBigOWith_def, norm_neg]

alias ⟨IsBigOWith.of_neg_right, IsBigOWith.neg_right⟩ := isBigOWith_neg_right

@[simp]
/-
**Asymptotics.isBigO_neg_right** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_neg_right : (f =O[l] fun x => -g' x) ↔ f =O[l] g'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.IsBigO_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type u_20
} [inst : Norm E] [inst_1 : Norm F] (l : Filter α) (f : α → E)   (g : α → F), f 
=O[l] g = ∃ …
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `Asymptotics.isBigOWith_neg_right`：isBigOWith_neg_right : (IsBigOWith c l
 f fun x => -g' x) ↔ IsBigOWith c l f g'
-/
theorem isBigO_neg_right : (f =O[l] fun x => -g' x) ↔ f =O[l] g' := by
  simp only [IsBigO_def]
  exact exists_congr fun _ => isBigOWith_neg_right

alias ⟨IsBigO.of_neg_right, IsBigO.neg_right⟩ := isBigO_neg_right

@[simp]
/-
**Asymptotics.isLittleO_neg_right** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_neg_right : (f =o[l] fun x => -g' x) ↔ f =o[l] g'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.IsLittleO_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type u
_20} [inst : Norm E] [inst_1 : Norm F] (l : Filter α) (f : α → E)   (g : α → F),
 f =o[l] g = ∀ …
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `Asymptotics.isBigOWith_neg_right`：isBigOWith_neg_right : (IsBigOWith c l
 f fun x => -g' x) ↔ IsBigOWith c l f g'
-/
theorem isLittleO_neg_right : (f =o[l] fun x => -g' x) ↔ f =o[l] g' := by
  simp only [IsLittleO_def]
  exact forall₂_congr fun _ _ => isBigOWith_neg_right

alias ⟨IsLittleO.of_neg_right, IsLittleO.neg_right⟩ := isLittleO_neg_right

@[simp]
/-
**Asymptotics.isBigOWith_neg_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOWith_neg_left : IsBigOWith c l (fun x => -f' x) g ↔ IsBigOWith c l f
' g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.IsBigOWith_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type 
u_20} [inst : Norm E] [inst_1 : Norm F] (c : ℝ) (l : Filter α) (f : α → E)   (g 
: α → F), Asympt…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isBigOWith_neg_left : IsBigOWith c l (fun x => -f' x) g ↔ IsBigOWith c l f' g := by
  simp only [IsBigOWith_def, norm_neg]

alias ⟨IsBigOWith.of_neg_left, IsBigOWith.neg_left⟩ := isBigOWith_neg_left

@[simp]
/-
**Asymptotics.isBigO_neg_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_neg_left : (fun x => -f' x) =O[l] g ↔ f' =O[l] g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.IsBigO_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type u_20
} [inst : Norm E] [inst_1 : Norm F] (l : Filter α) (f : α → E)   (g : α → F), f 
=O[l] g = ∃ …
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `Asymptotics.isBigOWith_neg_left`：isBigOWith_neg_left : IsBigOWith c l (f
un x => -f' x) g ↔ IsBigOWith c l f' g
-/
theorem isBigO_neg_left : (fun x => -f' x) =O[l] g ↔ f' =O[l] g := by
  simp only [IsBigO_def]
  exact exists_congr fun _ => isBigOWith_neg_left

alias ⟨IsBigO.of_neg_left, IsBigO.neg_left⟩ := isBigO_neg_left

@[simp]
/-
**Asymptotics.isLittleO_neg_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_neg_left : (fun x => -f' x) =o[l] g ↔ f' =o[l] g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.IsLittleO_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type u
_20} [inst : Norm E] [inst_1 : Norm F] (l : Filter α) (f : α → E)   (g : α → F),
 f =o[l] g = ∀ …
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `Asymptotics.isBigOWith_neg_left`：isBigOWith_neg_left : IsBigOWith c l (f
un x => -f' x) g ↔ IsBigOWith c l f' g
-/
theorem isLittleO_neg_left : (fun x => -f' x) =o[l] g ↔ f' =o[l] g := by
  simp only [IsLittleO_def]
  exact forall₂_congr fun _ _ => isBigOWith_neg_left

alias ⟨IsLittleO.of_neg_left, IsLittleO.neg_left⟩ := isLittleO_neg_left

/-! ### Product of functions (right) -/


/-
**Asymptotics.isBigOWith_fst_prod** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOWith_fst_prod : IsBigOWith 1 l f' fun x => (f' x, g' x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isBigOWith_of_le`：isBigOWith_of_le (hfg : forall x, ‖f x‖ <=
 ‖g x‖) : IsBigOWith 1 l f g
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b

--- 原说明 ---
### Product of functions (right)
-/
theorem isBigOWith_fst_prod : IsBigOWith 1 l f' fun x => (f' x, g' x) :=
  isBigOWith_of_le l fun _x => le_max_left _ _
/-
**Asymptotics.isBigOWith_snd_prod** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOWith_snd_prod : IsBigOWith 1 l g' fun x => (f' x, g' x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isBigOWith_of_le`：isBigOWith_of_le (hfg : forall x, ‖f x‖ <=
 ‖g x‖) : IsBigOWith 1 l f g
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
-/
theorem isBigOWith_snd_prod : IsBigOWith 1 l g' fun x => (f' x, g' x) :=
  isBigOWith_of_le l fun _x => le_max_right _ _
/-
**Asymptotics.isBigO_fst_prod** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_fst_prod : f' =O[l] fun x => (f' x, g' x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : F
ilter α}, Asymptoti…
· 使用定理 `Asymptotics.isBigOWith_fst_prod`：isBigOWith_fst_prod : IsBigOWith 1 l f'
 fun x => (f' x, g' x)
-/
theorem isBigO_fst_prod : f' =O[l] fun x => (f' x, g' x) :=
  isBigOWith_fst_prod.isBigO
/-
**Asymptotics.isBigO_snd_prod** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_snd_prod : g' =O[l] fun x => (f' x, g' x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : F
ilter α}, Asymptoti…
· 使用定理 `Asymptotics.isBigOWith_snd_prod`：isBigOWith_snd_prod : IsBigOWith 1 l g'
 fun x => (f' x, g' x)
-/
theorem isBigO_snd_prod : g' =O[l] fun x => (f' x, g' x) :=
  isBigOWith_snd_prod.isBigO
/-
**Asymptotics.isBigO_fst_prod'** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_fst_prod' {f' : α -> E' × F'} : (fun x => (f' x).1) =O[l] f'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Asymptotics.IsBigO_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type u_20
} [inst : Norm E] [inst_1 : Norm F] (l : Filter α) (f : α → E)   (g : α → F), f 
=O[l] g = ∃ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Asymptotics.IsBigOWith_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type 
u_20} [inst : Norm E] [inst_1 : Norm F] (c : ℝ) (l : Filter α) (f : α → E)   (g 
: α → F), Asympt…
· 使用定理 `Asymptotics.isBigO_fst_prod`：isBigO_fst_prod : f' =O[l] fun x => (f' x, 
g' x)
-/
theorem isBigO_fst_prod' {f' : α → E' × F'} : (fun x => (f' x).1) =O[l] f' := by
  simpa [IsBigO_def, IsBigOWith_def] using! isBigO_fst_prod (E' := E') (F' := F')
/-
**Asymptotics.isBigO_snd_prod'** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_snd_prod' {f' : α -> E' × F'} : (fun x => (f' x).2) =O[l] f'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Asymptotics.IsBigO_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type u_20
} [inst : Norm E] [inst_1 : Norm F] (l : Filter α) (f : α → E)   (g : α → F), f 
=O[l] g = ∃ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Asymptotics.IsBigOWith_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type 
u_20} [inst : Norm E] [inst_1 : Norm F] (c : ℝ) (l : Filter α) (f : α → E)   (g 
: α → F), Asympt…
· 使用定理 `Asymptotics.isBigO_snd_prod`：isBigO_snd_prod : g' =O[l] fun x => (f' x, 
g' x)
-/
theorem isBigO_snd_prod' {f' : α → E' × F'} : (fun x => (f' x).2) =O[l] f' := by
  simpa [IsBigO_def, IsBigOWith_def] using! isBigO_snd_prod (E' := E') (F' := F')

section

variable (f' k')

/-
**Asymptotics.IsBigOWith.prod_rightl** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBi
gOWith`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F' : Type u_7} {G' : Type u_8} [inst : No
rm E] [inst_1 : SeminormedAddCommGroup F']   [inst_2 : SeminormedAddCommGroup G'
] {c : ℝ} {f : α → E} {g' : α → F'} (k' : α → G') {l : Filter α},   Asymptotics.
IsBigOWith c l f g' → 0 ≤ c → Asymptotics.IsBigOWith c l f fun x => (g' x, k' x)
参数：k' : α → G'；g' x, k' x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.congr_const`：∀ {α : Type u_1} {E : Type u_3} {F :
 Type u_4} [inst : Norm E] [inst_1 : Norm F] {c₁ c₂ : ℝ} {f : α → E} {g : α → F}
   {l : Filter α}, Asymp…
· 使用定理 `Asymptotics.IsBigOWith.trans`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} {G : Type u_5} [inst : Norm E] [inst_1 : Norm F] [inst_2 : Norm G]   {c c' 
: ℝ} {f : α → E} {…
· 使用定理 `Asymptotics.isBigOWith_fst_prod`：isBigOWith_fst_prod : IsBigOWith 1 l f'
 fun x => (f' x, g' x)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem IsBigOWith.prod_rightl (h : IsBigOWith c l f g') (hc : 0 ≤ c) :
    IsBigOWith c l f fun x => (g' x, k' x) :=
  (h.trans isBigOWith_fst_prod hc).congr_const (mul_one c)
/-
**Asymptotics.IsBigO.prod_rightl** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F' : Type u_7} {G' : Type u_8} [inst : No
rm E] [inst_1 : SeminormedAddCommGroup F']   [inst_2 : SeminormedAddCommGroup G'
] {f : α → E} {g' : α → F'} (k' : α → G') {l : Filter α},   f =O[l] g' → f =O[l]
 fun x => (g' x, k' x)
参数：k' : α → G'；g' x, k' x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.exists_nonneg`：∀ {α : Type u_1} {E : Type u_3} {F' : 
Type u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {f : α → E}   {g'
 : α → F'} {l : Filter…
· 使用定理 `Asymptotics.IsBigOWith.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : F
ilter α}, Asymptoti…
· 使用定理 `Asymptotics.IsBigOWith.prod_rightl`：∀ {α : Type u_1} {E : Type u_3} {F' 
: Type u_7} {G' : Type u_8} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F']
   [inst_2 : SeminormedA…
-/
theorem IsBigO.prod_rightl (h : f =O[l] g') : f =O[l] fun x => (g' x, k' x) :=
  let ⟨_c, cnonneg, hc⟩ := h.exists_nonneg
  (hc.prod_rightl k' cnonneg).isBigO
/-
**Asymptotics.IsLittleO.prod_rightl** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLit
tleO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F' : Type u_7} {G' : Type u_8} [inst : No
rm E] [inst_1 : SeminormedAddCommGroup F']   [inst_2 : SeminormedAddCommGroup G'
] {f : α → E} {g' : α → F'} (k' : α → G') {l : Filter α},   f =o[l] g' → f =o[l]
 fun x => (g' x, k' x)
参数：k' : α → G'；g' x, k' x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.of_isBigOWith`：∀ {α : Type u_1} {E : Type u_3} {F 
: Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filte
r α},   (∀ ⦃c : ℝ⦄, 0 < c…
· 使用定理 `Asymptotics.IsBigOWith.prod_rightl`：∀ {α : Type u_1} {E : Type u_3} {F' 
: Type u_7} {G' : Type u_8} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F']
   [inst_2 : SeminormedA…
· 使用定理 `Asymptotics.IsLittleO.forall_isBigOWith`：∀ {α : Type u_1} {E : Type u_3}
 {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : F
ilter α},   f =o[l] g → ∀ ⦃c …
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem IsLittleO.prod_rightl (h : f =o[l] g') : f =o[l] fun x => (g' x, k' x) :=
  IsLittleO.of_isBigOWith fun _c cpos => (h.forall_isBigOWith cpos).prod_rightl k' cpos.le
/-
**Asymptotics.IsBigOWith.prod_rightr** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBi
gOWith`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {E' : Type u_6} {F' : Type u_7} [inst : No
rm E] [inst_1 : SeminormedAddCommGroup E']   [inst_2 : SeminormedAddCommGroup F'
] {c : ℝ} {f : α → E} (f' : α → E') {g' : α → F'} {l : Filter α},   Asymptotics.
IsBigOWith c l f g' → 0 ≤ c → Asymptotics.IsBigOWith c l f fun x => (f' x, g' x)
参数：f' : α → E'；f' x, g' x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.congr_const`：∀ {α : Type u_1} {E : Type u_3} {F :
 Type u_4} [inst : Norm E] [inst_1 : Norm F] {c₁ c₂ : ℝ} {f : α → E} {g : α → F}
   {l : Filter α}, Asymp…
· 使用定理 `Asymptotics.IsBigOWith.trans`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} {G : Type u_5} [inst : Norm E] [inst_1 : Norm F] [inst_2 : Norm G]   {c c' 
: ℝ} {f : α → E} {…
· 使用定理 `Asymptotics.isBigOWith_snd_prod`：isBigOWith_snd_prod : IsBigOWith 1 l g'
 fun x => (f' x, g' x)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem IsBigOWith.prod_rightr (h : IsBigOWith c l f g') (hc : 0 ≤ c) :
    IsBigOWith c l f fun x => (f' x, g' x) :=
  (h.trans isBigOWith_snd_prod hc).congr_const (mul_one c)
/-
**Asymptotics.IsBigO.prod_rightr** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {E' : Type u_6} {F' : Type u_7} [inst : No
rm E] [inst_1 : SeminormedAddCommGroup E']   [inst_2 : SeminormedAddCommGroup F'
] {f : α → E} (f' : α → E') {g' : α → F'} {l : Filter α},   f =O[l] g' → f =O[l]
 fun x => (f' x, g' x)
参数：f' : α → E'；f' x, g' x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.exists_nonneg`：∀ {α : Type u_1} {E : Type u_3} {F' : 
Type u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {f : α → E}   {g'
 : α → F'} {l : Filter…
· 使用定理 `Asymptotics.IsBigOWith.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : F
ilter α}, Asymptoti…
· 使用定理 `Asymptotics.IsBigOWith.prod_rightr`：∀ {α : Type u_1} {E : Type u_3} {E' 
: Type u_6} {F' : Type u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup E']
   [inst_2 : SeminormedA…
-/
theorem IsBigO.prod_rightr (h : f =O[l] g') : f =O[l] fun x => (f' x, g' x) :=
  let ⟨_c, cnonneg, hc⟩ := h.exists_nonneg
  (hc.prod_rightr f' cnonneg).isBigO
/-
**Asymptotics.IsLittleO.prod_rightr** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLit
tleO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {E' : Type u_6} {F' : Type u_7} [inst : No
rm E] [inst_1 : SeminormedAddCommGroup E']   [inst_2 : SeminormedAddCommGroup F'
] {f : α → E} (f' : α → E') {g' : α → F'} {l : Filter α},   f =o[l] g' → f =o[l]
 fun x => (f' x, g' x)
参数：f' : α → E'；f' x, g' x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.of_isBigOWith`：∀ {α : Type u_1} {E : Type u_3} {F 
: Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filte
r α},   (∀ ⦃c : ℝ⦄, 0 < c…
· 使用定理 `Asymptotics.IsBigOWith.prod_rightr`：∀ {α : Type u_1} {E : Type u_3} {E' 
: Type u_6} {F' : Type u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup E']
   [inst_2 : SeminormedA…
· 使用定理 `Asymptotics.IsLittleO.forall_isBigOWith`：∀ {α : Type u_1} {E : Type u_3}
 {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : F
ilter α},   f =o[l] g → ∀ ⦃c …
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem IsLittleO.prod_rightr (h : f =o[l] g') : f =o[l] fun x => (f' x, g' x) :=
  IsLittleO.of_isBigOWith fun _c cpos => (h.forall_isBigOWith cpos).prod_rightr f' cpos.le

end

section

variable {f : α × β → E} {g : α × β → F} {l' : Filter β}

/-
**Asymptotics.IsBigO.fiberwise_right** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBi
gO`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {E : Type u_3} {F : Type u_4} [inst : Norm
 E] [inst_1 : Norm F] {l : Filter α}   {f : α × β → E} {g : α × β → F} {l' : Fil
ter β},   f =O[l ×ˢ l'] g → ∀ᶠ (a : α) in l, (fun x => f (a, x)) =O[l'] fun x =>
 g (a, x)
参数：a : α；fun x => f (a, x)；a, x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
-/
protected theorem IsBigO.fiberwise_right :
    f =O[l ×ˢ l'] g → ∀ᶠ a in l, (f ⟨a, ·⟩) =O[l'] (g ⟨a, ·⟩) := by
  simp only [isBigO_iff, eventually_iff, mem_prod_iff]
  rintro ⟨c, t₁, ht₁, t₂, ht₂, ht⟩
  exact mem_of_superset ht₁ fun _ ha ↦ ⟨c, mem_of_superset ht₂ fun _ hb ↦ ht ⟨ha, hb⟩⟩
/-
**Asymptotics.IsBigO.fiberwise_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBig
O`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {E : Type u_3} {F : Type u_4} [inst : Norm
 E] [inst_1 : Norm F] {l : Filter α}   {f : α × β → E} {g : α × β → F} {l' : Fil
ter β},   f =O[l ×ˢ l'] g → ∀ᶠ (b : β) in l', (fun x => f (x, b)) =O[l] fun x =>
 g (x, b)
参数：b : β；fun x => f (x, b)；x, b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
-/
protected theorem IsBigO.fiberwise_left :
    f =O[l ×ˢ l'] g → ∀ᶠ b in l', (f ⟨·, b⟩) =O[l] (g ⟨·, b⟩) := by
  simp only [isBigO_iff, eventually_iff, mem_prod_iff]
  rintro ⟨c, t₁, ht₁, t₂, ht₂, ht⟩
  exact mem_of_superset ht₂ fun _ hb ↦ ⟨c, mem_of_superset ht₁ fun _ ha ↦ ht ⟨ha, hb⟩⟩

end

section

variable (l' : Filter β)

/-
**Asymptotics.IsBigO.comp_fst** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {E : Type u_3} {F : Type u_4} [inst : Norm
 E] [inst_1 : Norm F] {f : α → E} {g : α → F}   {l : Filter α} (l' : Filter β), 
f =O[l] g → (f ∘ Prod.fst) =O[l ×ˢ l'] (g ∘ Prod.fst)
参数：l' : Filter β；f ∘ Prod.fst；g ∘ Prod.fst。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.eventually_true`：∀ {α : Type u} (f : Filter α), ∀ᶠ (x : α) in f, 
True
-/
protected theorem IsBigO.comp_fst : f =O[l] g → (f ∘ Prod.fst) =O[l ×ˢ l'] (g ∘ Prod.fst) := by
  simp only [isBigO_iff, eventually_prod_iff]
  exact fun ⟨c, hc⟩ ↦ ⟨c, _, hc, fun _ ↦ True, eventually_true l', fun {_} h {_} _ ↦ h⟩
/-
**Asymptotics.IsBigO.comp_snd** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {E : Type u_3} {F : Type u_4} [inst : Norm
 E] [inst_1 : Norm F] {f : α → E} {g : α → F}   {l : Filter α} (l' : Filter β), 
f =O[l] g → (f ∘ Prod.snd) =O[l' ×ˢ l] (g ∘ Prod.snd)
参数：l' : Filter β；f ∘ Prod.snd；g ∘ Prod.snd。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.eventually_true`：∀ {α : Type u} (f : Filter α), ∀ᶠ (x : α) in f, 
True
-/
protected theorem IsBigO.comp_snd : f =O[l] g → (f ∘ Prod.snd) =O[l' ×ˢ l] (g ∘ Prod.snd) := by
  simp only [isBigO_iff, eventually_prod_iff]
  exact fun ⟨c, hc⟩ ↦ ⟨c, fun _ ↦ True, eventually_true l', _, hc, fun _ ↦ id⟩
/-
**Asymptotics.IsLittleO.comp_fst** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLittle
O`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {E : Type u_3} {F : Type u_4} [inst : Norm
 E] [inst_1 : Norm F] {f : α → E} {g : α → F}   {l : Filter α} (l' : Filter β), 
f =o[l] g → (f ∘ Prod.fst) =o[l ×ˢ l'] (g ∘ Prod.fst)
参数：l' : Filter β；f ∘ Prod.fst；g ∘ Prod.fst。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Filter.eventually_true`：∀ {α : Type u} (f : Filter α), ∀ᶠ (x : α) in f, 
True
-/
protected theorem IsLittleO.comp_fst : f =o[l] g → (f ∘ Prod.fst) =o[l ×ˢ l'] (g ∘ Prod.fst) := by
  simp only [isLittleO_iff, eventually_prod_iff]
  exact fun h _ hc ↦ ⟨_, h hc, fun _ ↦ True, eventually_true l', fun {_} h {_} _ ↦ h⟩
/-
**Asymptotics.IsLittleO.comp_snd** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLittle
O`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {E : Type u_3} {F : Type u_4} [inst : Norm
 E] [inst_1 : Norm F] {f : α → E} {g : α → F}   {l : Filter α} (l' : Filter β), 
f =o[l] g → (f ∘ Prod.snd) =o[l' ×ˢ l] (g ∘ Prod.snd)
参数：l' : Filter β；f ∘ Prod.snd；g ∘ Prod.snd。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Filter.eventually_true`：∀ {α : Type u} (f : Filter α), ∀ᶠ (x : α) in f, 
True
-/
protected theorem IsLittleO.comp_snd : f =o[l] g → (f ∘ Prod.snd) =o[l' ×ˢ l] (g ∘ Prod.snd) := by
  simp only [isLittleO_iff, eventually_prod_iff]
  exact fun h _ hc ↦ ⟨fun _ ↦ True, eventually_true l', _, h hc, fun _ ↦ id⟩

end

/-
**Asymptotics.IsBigOWith.prod_left_same** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.I
sBigOWith`。
形式化陈述：∀ {α : Type u_1} {E' : Type u_6} {F' : Type u_7} {G' : Type u_8} [inst : S
eminormedAddCommGroup E']   [inst_1 : SeminormedAddCommGroup F'] [inst_2 : Semin
ormedAddCommGroup G'] {c : ℝ} {f' : α → E'} {g' : α → F'}   {k' : α → G'} {l : F
ilter α},   Asymptotics.IsBigOWith c l f' k' →     Asymptotics.IsBigOWith c l g'
 k' → Asymptotics.IsBigOWith c l (fun x => (f' x, g' x)) k'
参数：fun x => (f' x, g' x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.isBigOWith_iff`：isBigOWith_iff : IsBigOWith c l f g ↔ forall
ᶠ x in l, ‖f x‖ <= c * ‖g x‖
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
-/
theorem IsBigOWith.prod_left_same (hf : IsBigOWith c l f' k') (hg : IsBigOWith c l g' k') :
    IsBigOWith c l (fun x => (f' x, g' x)) k' := by
  rw [isBigOWith_iff] at *; filter_upwards [hf, hg] with x using max_le
/-
**Asymptotics.IsBigOWith.prod_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO
With`。
形式化陈述：∀ {α : Type u_1} {E' : Type u_6} {F' : Type u_7} {G' : Type u_8} [inst : S
eminormedAddCommGroup E']   [inst_1 : SeminormedAddCommGroup F'] [inst_2 : Semin
ormedAddCommGroup G'] {c c' : ℝ} {f' : α → E'} {g' : α → F'}   {k' : α → G'} {l 
: Filter α},   Asymptotics.IsBigOWith c l f' k' →     Asymptotics.IsBigOWith c' 
l g' k' → Asymptotics.IsBigOWith (max c c') l (fun x => (f' x, g' x)) k'
参数：max c c'；fun x => (f' x, g' x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.prod_left_same`：∀ {α : Type u_1} {E' : Type u_6} 
{F' : Type u_7} {G' : Type u_8} [inst : SeminormedAddCommGroup E']   [inst_1 : S
eminormedAddCommGroup F'] […
· 使用定理 `Asymptotics.IsBigOWith.weaken`：∀ {α : Type u_1} {E : Type u_3} {F' : Typ
e u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {c c' : ℝ}   {f : α 
→ E} {g' : α → F'} …
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
-/
theorem IsBigOWith.prod_left (hf : IsBigOWith c l f' k') (hg : IsBigOWith c' l g' k') :
    IsBigOWith (max c c') l (fun x => (f' x, g' x)) k' :=
  (hf.weaken <| le_max_left c c').prod_left_same (hg.weaken <| le_max_right c c')
/-
**Asymptotics.IsBigOWith.prod_left_fst** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.Is
BigOWith`。
形式化陈述：∀ {α : Type u_1} {E' : Type u_6} {F' : Type u_7} {G' : Type u_8} [inst : S
eminormedAddCommGroup E']   [inst_1 : SeminormedAddCommGroup F'] [inst_2 : Semin
ormedAddCommGroup G'] {c : ℝ} {f' : α → E'} {g' : α → F'}   {k' : α → G'} {l : F
ilter α}, Asymptotics.IsBigOWith c l (fun x => (f' x, g' x)) k' → Asymptotics.Is
BigOWith c l f' k'
参数：fun x => (f' x, g' x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.congr_const`：∀ {α : Type u_1} {E : Type u_3} {F :
 Type u_4} [inst : Norm E] [inst_1 : Norm F] {c₁ c₂ : ℝ} {f : α → E} {g : α → F}
   {l : Filter α}, Asymp…
· 使用定理 `Asymptotics.IsBigOWith.trans`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} {G : Type u_5} [inst : Norm E] [inst_1 : Norm F] [inst_2 : Norm G]   {c c' 
: ℝ} {f : α → E} {…
· 使用定理 `Asymptotics.isBigOWith_fst_prod`：isBigOWith_fst_prod : IsBigOWith 1 l f'
 fun x => (f' x, g' x)
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem IsBigOWith.prod_left_fst (h : IsBigOWith c l (fun x => (f' x, g' x)) k') :
    IsBigOWith c l f' k' :=
  (isBigOWith_fst_prod.trans h zero_le_one).congr_const <| one_mul c
/-
**Asymptotics.IsBigOWith.prod_left_snd** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.Is
BigOWith`。
形式化陈述：∀ {α : Type u_1} {E' : Type u_6} {F' : Type u_7} {G' : Type u_8} [inst : S
eminormedAddCommGroup E']   [inst_1 : SeminormedAddCommGroup F'] [inst_2 : Semin
ormedAddCommGroup G'] {c : ℝ} {f' : α → E'} {g' : α → F'}   {k' : α → G'} {l : F
ilter α}, Asymptotics.IsBigOWith c l (fun x => (f' x, g' x)) k' → Asymptotics.Is
BigOWith c l g' k'
参数：fun x => (f' x, g' x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.congr_const`：∀ {α : Type u_1} {E : Type u_3} {F :
 Type u_4} [inst : Norm E] [inst_1 : Norm F] {c₁ c₂ : ℝ} {f : α → E} {g : α → F}
   {l : Filter α}, Asymp…
· 使用定理 `Asymptotics.IsBigOWith.trans`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} {G : Type u_5} [inst : Norm E] [inst_1 : Norm F] [inst_2 : Norm G]   {c c' 
: ℝ} {f : α → E} {…
· 使用定理 `Asymptotics.isBigOWith_snd_prod`：isBigOWith_snd_prod : IsBigOWith 1 l g'
 fun x => (f' x, g' x)
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem IsBigOWith.prod_left_snd (h : IsBigOWith c l (fun x => (f' x, g' x)) k') :
    IsBigOWith c l g' k' :=
  (isBigOWith_snd_prod.trans h zero_le_one).congr_const <| one_mul c
/-
**Asymptotics.isBigOWith_prod_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOWith_prod_left : IsBigOWith c l (fun x => (f' x, g' x)) k' ↔ IsBigOW
ith c l f' k' ∧ IsBigOWith c l g' k'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.prod_left_fst`：∀ {α : Type u_1} {E' : Type u_6} {
F' : Type u_7} {G' : Type u_8} [inst : SeminormedAddCommGroup E']   [inst_1 : Se
minormedAddCommGroup F'] […
· 使用定理 `Asymptotics.IsBigOWith.prod_left_snd`：∀ {α : Type u_1} {E' : Type u_6} {
F' : Type u_7} {G' : Type u_8} [inst : SeminormedAddCommGroup E']   [inst_1 : Se
minormedAddCommGroup F'] […
· 使用定理 `Asymptotics.IsBigOWith.prod_left_same`：∀ {α : Type u_1} {E' : Type u_6} 
{F' : Type u_7} {G' : Type u_8} [inst : SeminormedAddCommGroup E']   [inst_1 : S
eminormedAddCommGroup F'] […
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem isBigOWith_prod_left :
    IsBigOWith c l (fun x => (f' x, g' x)) k' ↔ IsBigOWith c l f' k' ∧ IsBigOWith c l g' k' :=
  ⟨fun h => ⟨h.prod_left_fst, h.prod_left_snd⟩, fun h => h.1.prod_left_same h.2⟩
/-
**Asymptotics.IsBigO.prod_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`。
形式化陈述：∀ {α : Type u_1} {E' : Type u_6} {F' : Type u_7} {G' : Type u_8} [inst : S
eminormedAddCommGroup E']   [inst_1 : SeminormedAddCommGroup F'] [inst_2 : Semin
ormedAddCommGroup G'] {f' : α → E'} {g' : α → F'} {k' : α → G'}   {l : Filter α}
, f' =O[l] k' → g' =O[l] k' → (fun x => (f' x, g' x)) =O[l] k'
参数：fun x => (f' x, g' x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.isBigOWith`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α}, 
  f =O[l] g → ∃ c, …
· 使用定理 `Asymptotics.IsBigOWith.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : F
ilter α}, Asymptoti…
· 使用定理 `Asymptotics.IsBigOWith.prod_left`：∀ {α : Type u_1} {E' : Type u_6} {F' :
 Type u_7} {G' : Type u_8} [inst : SeminormedAddCommGroup E']   [inst_1 : Semino
rmedAddCommGroup F'] […
-/
theorem IsBigO.prod_left (hf : f' =O[l] k') (hg : g' =O[l] k') : (fun x => (f' x, g' x)) =O[l] k' :=
  let ⟨_c, hf⟩ := hf.isBigOWith
  let ⟨_c', hg⟩ := hg.isBigOWith
  (hf.prod_left hg).isBigO
/-
**Asymptotics.IsBigO.prod_left_fst** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO
`。
形式化陈述：∀ {α : Type u_1} {E' : Type u_6} {F' : Type u_7} {G' : Type u_8} [inst : S
eminormedAddCommGroup E']   [inst_1 : SeminormedAddCommGroup F'] [inst_2 : Semin
ormedAddCommGroup G'] {f' : α → E'} {g' : α → F'} {k' : α → G'}   {l : Filter α}
, (fun x => (f' x, g' x)) =O[l] k' → f' =O[l] k'
参数：fun x => (f' x, g' x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5}
 {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddComm
Group F'] {l :…
· 使用定理 `Asymptotics.isBigO_fst_prod`：isBigO_fst_prod : f' =O[l] fun x => (f' x, 
g' x)
-/
theorem IsBigO.prod_left_fst : (fun x => (f' x, g' x)) =O[l] k' → f' =O[l] k' :=
  IsBigO.trans isBigO_fst_prod
/-
**Asymptotics.IsBigO.prod_left_snd** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO
`。
形式化陈述：∀ {α : Type u_1} {E' : Type u_6} {F' : Type u_7} {G' : Type u_8} [inst : S
eminormedAddCommGroup E']   [inst_1 : SeminormedAddCommGroup F'] [inst_2 : Semin
ormedAddCommGroup G'] {f' : α → E'} {g' : α → F'} {k' : α → G'}   {l : Filter α}
, (fun x => (f' x, g' x)) =O[l] k' → g' =O[l] k'
参数：fun x => (f' x, g' x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5}
 {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddComm
Group F'] {l :…
· 使用定理 `Asymptotics.isBigO_snd_prod`：isBigO_snd_prod : g' =O[l] fun x => (f' x, 
g' x)
-/
theorem IsBigO.prod_left_snd : (fun x => (f' x, g' x)) =O[l] k' → g' =O[l] k' :=
  IsBigO.trans isBigO_snd_prod

@[simp]
/-
**Asymptotics.isBigO_prod_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_prod_left : (fun x => (f' x, g' x)) =O[l] k' ↔ f' =O[l] k' ∧ g' =O[
l] k'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.prod_left_fst`：∀ {α : Type u_1} {E' : Type u_6} {F' :
 Type u_7} {G' : Type u_8} [inst : SeminormedAddCommGroup E']   [inst_1 : Semino
rmedAddCommGroup F'] […
· 使用定理 `Asymptotics.IsBigO.prod_left_snd`：∀ {α : Type u_1} {E' : Type u_6} {F' :
 Type u_7} {G' : Type u_8} [inst : SeminormedAddCommGroup E']   [inst_1 : Semino
rmedAddCommGroup F'] […
· 使用定理 `Asymptotics.IsBigO.prod_left`：∀ {α : Type u_1} {E' : Type u_6} {F' : Typ
e u_7} {G' : Type u_8} [inst : SeminormedAddCommGroup E']   [inst_1 : Seminormed
AddCommGroup F'] […
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem isBigO_prod_left : (fun x => (f' x, g' x)) =O[l] k' ↔ f' =O[l] k' ∧ g' =O[l] k' :=
  ⟨fun h => ⟨h.prod_left_fst, h.prod_left_snd⟩, fun h => h.1.prod_left h.2⟩
/-
**Asymptotics.IsLittleO.prod_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLittl
eO`。
形式化陈述：∀ {α : Type u_1} {E' : Type u_6} {F' : Type u_7} {G' : Type u_8} [inst : S
eminormedAddCommGroup E']   [inst_1 : SeminormedAddCommGroup F'] [inst_2 : Semin
ormedAddCommGroup G'] {f' : α → E'} {g' : α → F'} {k' : α → G'}   {l : Filter α}
, f' =o[l] k' → g' =o[l] k' → (fun x => (f' x, g' x)) =o[l] k'
参数：fun x => (f' x, g' x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.of_isBigOWith`：∀ {α : Type u_1} {E : Type u_3} {F 
: Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filte
r α},   (∀ ⦃c : ℝ⦄, 0 < c…
· 使用定理 `Asymptotics.IsBigOWith.prod_left_same`：∀ {α : Type u_1} {E' : Type u_6} 
{F' : Type u_7} {G' : Type u_8} [inst : SeminormedAddCommGroup E']   [inst_1 : S
eminormedAddCommGroup F'] […
· 使用定理 `Asymptotics.IsLittleO.forall_isBigOWith`：∀ {α : Type u_1} {E : Type u_3}
 {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : F
ilter α},   f =o[l] g → ∀ ⦃c …
-/
theorem IsLittleO.prod_left (hf : f' =o[l] k') (hg : g' =o[l] k') :
    (fun x => (f' x, g' x)) =o[l] k' :=
  IsLittleO.of_isBigOWith fun _c hc =>
    (hf.forall_isBigOWith hc).prod_left_same (hg.forall_isBigOWith hc)
/-
**Asymptotics.IsLittleO.prod_left_fst** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsL
ittleO`。
形式化陈述：∀ {α : Type u_1} {E' : Type u_6} {F' : Type u_7} {G' : Type u_8} [inst : S
eminormedAddCommGroup E']   [inst_1 : SeminormedAddCommGroup F'] [inst_2 : Semin
ormedAddCommGroup G'] {f' : α → E'} {g' : α → F'} {k' : α → G'}   {l : Filter α}
, (fun x => (f' x, g' x)) =o[l] k' → f' =o[l] k'
参数：fun x => (f' x, g' x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans_isLittleO`：∀ {α : Type u_1} {E : Type u_3} {G :
 Type u_5} {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : Seminor
medAddCommGroup F'] {l :…
· 使用定理 `Asymptotics.isBigO_fst_prod`：isBigO_fst_prod : f' =O[l] fun x => (f' x, 
g' x)
-/
theorem IsLittleO.prod_left_fst : (fun x => (f' x, g' x)) =o[l] k' → f' =o[l] k' :=
  IsBigO.trans_isLittleO isBigO_fst_prod
/-
**Asymptotics.IsLittleO.prod_left_snd** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsL
ittleO`。
形式化陈述：∀ {α : Type u_1} {E' : Type u_6} {F' : Type u_7} {G' : Type u_8} [inst : S
eminormedAddCommGroup E']   [inst_1 : SeminormedAddCommGroup F'] [inst_2 : Semin
ormedAddCommGroup G'] {f' : α → E'} {g' : α → F'} {k' : α → G'}   {l : Filter α}
, (fun x => (f' x, g' x)) =o[l] k' → g' =o[l] k'
参数：fun x => (f' x, g' x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans_isLittleO`：∀ {α : Type u_1} {E : Type u_3} {G :
 Type u_5} {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : Seminor
medAddCommGroup F'] {l :…
· 使用定理 `Asymptotics.isBigO_snd_prod`：isBigO_snd_prod : g' =O[l] fun x => (f' x, 
g' x)
-/
theorem IsLittleO.prod_left_snd : (fun x => (f' x, g' x)) =o[l] k' → g' =o[l] k' :=
  IsBigO.trans_isLittleO isBigO_snd_prod

@[simp]
/-
**Asymptotics.isLittleO_prod_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_prod_left : (fun x => (f' x, g' x)) =o[l] k' ↔ f' =o[l] k' ∧ g' 
=o[l] k'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.prod_left_fst`：∀ {α : Type u_1} {E' : Type u_6} {F
' : Type u_7} {G' : Type u_8} [inst : SeminormedAddCommGroup E']   [inst_1 : Sem
inormedAddCommGroup F'] […
· 使用定理 `Asymptotics.IsLittleO.prod_left_snd`：∀ {α : Type u_1} {E' : Type u_6} {F
' : Type u_7} {G' : Type u_8} [inst : SeminormedAddCommGroup E']   [inst_1 : Sem
inormedAddCommGroup F'] […
· 使用定理 `Asymptotics.IsLittleO.prod_left`：∀ {α : Type u_1} {E' : Type u_6} {F' : 
Type u_7} {G' : Type u_8} [inst : SeminormedAddCommGroup E']   [inst_1 : Seminor
medAddCommGroup F'] […
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem isLittleO_prod_left : (fun x => (f' x, g' x)) =o[l] k' ↔ f' =o[l] k' ∧ g' =o[l] k' :=
  ⟨fun h => ⟨h.prod_left_fst, h.prod_left_snd⟩, fun h => h.1.prod_left h.2⟩
/-
**Asymptotics.IsBigOWith.eq_zero_imp** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBi
gOWith`。
形式化陈述：∀ {α : Type u_1} {E'' : Type u_9} {F'' : Type u_10} [inst : NormedAddCommG
roup E''] [inst_1 : NormedAddCommGroup F'']   {c : ℝ} {f'' : α → E''} {g'' : α →
 F''} {l : Filter α},   Asymptotics.IsBigOWith c l f'' g'' → ∀ᶠ (x : α) in l, g'
' x = 0 → f'' x = 0
参数：x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Asymptotics.IsBigOWith.bound`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : Fi
lter α}, Asymptoti…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `norm_le_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≤ 0 ↔ a = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem IsBigOWith.eq_zero_imp (h : IsBigOWith c l f'' g'') : ∀ᶠ x in l, g'' x = 0 → f'' x = 0 :=
  Eventually.mono h.bound fun x hx hg => norm_le_zero_iff.1 <| by simpa [hg] using hx
/-
**Asymptotics.IsBigO.eq_zero_imp** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`。
形式化陈述：∀ {α : Type u_1} {E'' : Type u_9} {F'' : Type u_10} [inst : NormedAddCommG
roup E''] [inst_1 : NormedAddCommGroup F'']   {f'' : α → E''} {g'' : α → F''} {l
 : Filter α}, f'' =O[l] g'' → ∀ᶠ (x : α) in l, g'' x = 0 → f'' x = 0
参数：x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.isBigOWith`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α}, 
  f =O[l] g → ∃ c, …
· 使用定理 `Asymptotics.IsBigOWith.eq_zero_imp`：∀ {α : Type u_1} {E'' : Type u_9} {F
'' : Type u_10} [inst : NormedAddCommGroup E''] [inst_1 : NormedAddCommGroup F''
]   {c : ℝ} {f'' : α → E…
-/
theorem IsBigO.eq_zero_imp (h : f'' =O[l] g'') : ∀ᶠ x in l, g'' x = 0 → f'' x = 0 :=
  let ⟨_C, hC⟩ := h.isBigOWith
  hC.eq_zero_imp

/-! ### Addition and subtraction -/


section add_sub

variable {f₁ f₂ : α → E'} {g₁ g₂ : α → F'}

/-
**Asymptotics.IsBigOWith.add** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigOWith`。
形式化陈述：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} [inst : Norm F] [inst_1 : 
SeminormedAddCommGroup E'] {c₁ c₂ : ℝ}   {g : α → F} {l : Filter α} {f₁ f₂ : α →
 E'},   Asymptotics.IsBigOWith c₁ l f₁ g →     Asymptotics.IsBigOWith c₂ l f₂ g 
→ Asymptotics.IsBigOWith (c₁ + c₂) l (fun x => f₁ x + f₂ x) g
参数：c₁ + c₂；fun x => f₁ x + f₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.IsBigOWith_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type 
u_20} [inst : Norm E] [inst_1 : Norm F] (c : ℝ) (l : Filter α) (f : α → E)   (g 
: α → F), Asympt…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `norm_add_le_of_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {a₁ a₂
 : E} {r₁ r₂ : ℝ}, ‖a₁‖ ≤ r₁ → ‖a₂‖ ≤ r₂ → ‖a₁ + a₂‖ ≤ r₁ + r₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
-/
theorem IsBigOWith.add (h₁ : IsBigOWith c₁ l f₁ g) (h₂ : IsBigOWith c₂ l f₂ g) :
    IsBigOWith (c₁ + c₂) l (fun x => f₁ x + f₂ x) g := by
  rw [IsBigOWith_def] at *
  filter_upwards [h₁, h₂] with x hx₁ hx₂ using
    calc
      ‖f₁ x + f₂ x‖ ≤ c₁ * ‖g x‖ + c₂ * ‖g x‖ := norm_add_le_of_le hx₁ hx₂
      _ = (c₁ + c₂) * ‖g x‖ := (add_mul _ _ _).symm
/-
**Asymptotics.IsBigO.add** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`。
形式化陈述：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} [inst : Norm F] [inst_1 : 
SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α} {f₁ f₂ : α → E'}, f₁ =O[
l] g → f₂ =O[l] g → (fun x => f₁ x + f₂ x) =O[l] g
参数：fun x => f₁ x + f₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.isBigOWith`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α}, 
  f =O[l] g → ∃ c, …
· 使用定理 `Asymptotics.IsBigOWith.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : F
ilter α}, Asymptoti…
· 使用定理 `Asymptotics.IsBigOWith.add`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u
_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {c₁ c₂ : ℝ}   {g : α → 
F} {l : Filter α…
-/
theorem IsBigO.add (h₁ : f₁ =O[l] g) (h₂ : f₂ =O[l] g) : (fun x => f₁ x + f₂ x) =O[l] g :=
  let ⟨_c₁, hc₁⟩ := h₁.isBigOWith
  let ⟨_c₂, hc₂⟩ := h₂.isBigOWith
  (hc₁.add hc₂).isBigO
/-
**Asymptotics.IsLittleO.add** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLittleO`。
形式化陈述：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} [inst : Norm F] [inst_1 : 
SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α} {f₁ f₂ : α → E'}, f₁ =o[
l] g → f₂ =o[l] g → (fun x => f₁ x + f₂ x) =o[l] g
参数：fun x => f₁ x + f₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.of_isBigOWith`：∀ {α : Type u_1} {E : Type u_3} {F 
: Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filte
r α},   (∀ ⦃c : ℝ⦄, 0 < c…
· 使用定理 `Asymptotics.IsBigOWith.congr_const`：∀ {α : Type u_1} {E : Type u_3} {F :
 Type u_4} [inst : Norm E] [inst_1 : Norm F] {c₁ c₂ : ℝ} {f : α → E} {g : α → F}
   {l : Filter α}, Asymp…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Asymptotics.IsBigOWith.add`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u
_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {c₁ c₂ : ℝ}   {g : α → 
F} {l : Filter α…
· 使用定理 `Asymptotics.IsLittleO.forall_isBigOWith`：∀ {α : Type u_1} {E : Type u_3}
 {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : F
ilter α},   f =o[l] g → ∀ ⦃c …
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `add_halves`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2] (a :
 K), a / 2 + a / 2 = a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem IsLittleO.add (h₁ : f₁ =o[l] g) (h₂ : f₂ =o[l] g) : (fun x => f₁ x + f₂ x) =o[l] g :=
  IsLittleO.of_isBigOWith fun c cpos =>
    ((h₁.forall_isBigOWith <| half_pos cpos).add (h₂.forall_isBigOWith <|
      half_pos cpos)).congr_const (add_halves c)
/-
**Asymptotics.IsBigOWith.add_add** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigOWi
th`。
形式化陈述：∀ {α : Type u_1} {E' : Type u_6} [inst : SeminormedAddCommGroup E'] {c₁ c₂
 : ℝ} {l : Filter α} {f₁ f₂ : α → E'}   {g₁ g₂ : α → ℝ},   Asymptotics.IsBigOWit
h c₁ l f₁ g₁ →     Asymptotics.IsBigOWith c₂ l f₂ g₂ →       Asymptotics.IsBigOW
ith (max c₁ c₂) l (fun x => f₁ x + f₂ x) fun x => ‖g₁ x‖ + ‖g₂ x‖
参数：max c₁ c₂；fun x => f₁ x + f₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.IsBigOWith_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type 
u_20} [inst : Norm E] [inst_1 : Norm F] (c : ℝ) (l : Filter α) (f : α → E)   (g 
: α → F), Asympt…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `norm_add_le_of_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {a₁ a₂
 : E} {r₁ r₂ : ℝ}, ‖a₁‖ ≤ r₁ → ‖a₂‖ ≤ r₂ → ‖a₁ + a₂‖ ≤ r₁ + r₂
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
-/
theorem IsBigOWith.add_add {g₁ g₂ : α → ℝ} (h₁ : IsBigOWith c₁ l f₁ g₁)
    (h₂ : IsBigOWith c₂ l f₂ g₂) :
    IsBigOWith (max c₁ c₂) l (fun x ↦ f₁ x + f₂ x) (fun x ↦ ‖g₁ x‖ + ‖g₂ x‖) := by
  rw [IsBigOWith_def] at *
  filter_upwards [h₁, h₂] with x hx₁ hx₂
  calc
    ‖f₁ x + f₂ x‖ ≤ c₁ * ‖g₁ x‖ + c₂ * ‖g₂ x‖ := norm_add_le_of_le hx₁ hx₂
    _ ≤ (max c₁ c₂) * ‖g₁ x‖ + (max c₁ c₂) * ‖g₂ x‖ := by
        gcongr <;> simp [le_max_left _ _, le_max_right _ _]
    _ = (max c₁ c₂) * ‖‖g₁ x‖ + ‖g₂ x‖‖ := by
        rw [Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)), mul_add]
/-
**Asymptotics.IsBigO.add_add** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`。
形式化陈述：∀ {α : Type u_1} {E' : Type u_6} [inst : SeminormedAddCommGroup E'] {l : F
ilter α} {f₁ f₂ : α → E'} {g₁ g₂ : α → ℝ},   f₁ =O[l] g₁ → f₂ =O[l] g₂ → (fun x 
=> f₁ x + f₂ x) =O[l] fun x => ‖g₁ x‖ + ‖g₂ x‖
参数：fun x => f₁ x + f₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.isBigOWith`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α}, 
  f =O[l] g → ∃ c, …
· 使用定理 `Asymptotics.IsBigOWith.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : F
ilter α}, Asymptoti…
· 使用定理 `Asymptotics.IsBigOWith.add_add`：∀ {α : Type u_1} {E' : Type u_6} [inst :
 SeminormedAddCommGroup E'] {c₁ c₂ : ℝ} {l : Filter α} {f₁ f₂ : α → E'}   {g₁ g₂
 : α → ℝ},   Asympto…
-/
theorem IsBigO.add_add {g₁ g₂ : α → ℝ} (h₁ : f₁ =O[l] g₁) (h₂ : f₂ =O[l] g₂) :
    (fun x ↦ f₁ x + f₂ x) =O[l] fun x ↦ ‖g₁ x‖ + ‖g₂ x‖ := by
  obtain ⟨c₁, hc₁⟩ := h₁.isBigOWith
  obtain ⟨c₂, hc₂⟩ := h₂.isBigOWith
  exact (hc₁.add_add hc₂).isBigO
/-
**Asymptotics.IsLittleO.add_add** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLittleO
`。
形式化陈述：∀ {α : Type u_1} {E' : Type u_6} {F' : Type u_7} [inst : SeminormedAddComm
Group E'] [inst_1 : SeminormedAddCommGroup F']   {l : Filter α} {f₁ f₂ : α → E'}
 {g₁ g₂ : α → F'},   f₁ =o[l] g₁ → f₂ =o[l] g₂ → (fun x => f₁ x + f₂ x) =o[l] fu
n x => ‖g₁ x‖ + ‖g₂ x‖
参数：fun x => f₁ x + f₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.add`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_
6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filte
r α} {f₁ f₂ : α…
· 使用定理 `Asymptotics.IsLittleO.trans_le`：∀ {α : Type u_1} {E : Type u_3} {F : Typ
e u_4} {G : Type u_5} [inst : Norm E] [inst_1 : Norm F] [inst_2 : Norm G]   {f :
 α → E} {g : α → F} …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem IsLittleO.add_add (h₁ : f₁ =o[l] g₁) (h₂ : f₂ =o[l] g₂) :
    (fun x => f₁ x + f₂ x) =o[l] fun x => ‖g₁ x‖ + ‖g₂ x‖ := by
  refine (h₁.trans_le fun x => ?_).add (h₂.trans_le ?_) <;> simp [abs_of_nonneg, add_nonneg]
/-
**Asymptotics.IsBigO.add_isLittleO** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO
`。
形式化陈述：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} [inst : Norm F] [inst_1 : 
SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α} {f₁ f₂ : α → E'}, f₁ =O[
l] g → f₂ =o[l] g → (fun x => f₁ x + f₂ x) =O[l] g
参数：fun x => f₁ x + f₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.add`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} 
[inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α
} {f₁ f₂ : α…
· 使用定理 `Asymptotics.IsLittleO.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},  
 f =o[l] g → f =O[…
-/
theorem IsBigO.add_isLittleO (h₁ : f₁ =O[l] g) (h₂ : f₂ =o[l] g) : (fun x => f₁ x + f₂ x) =O[l] g :=
  h₁.add h₂.isBigO
/-
**Asymptotics.IsLittleO.add_isBigO** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLitt
leO`。
形式化陈述：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} [inst : Norm F] [inst_1 : 
SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α} {f₁ f₂ : α → E'}, f₁ =o[
l] g → f₂ =O[l] g → (fun x => f₁ x + f₂ x) =O[l] g
参数：fun x => f₁ x + f₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.add`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} 
[inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α
} {f₁ f₂ : α…
· 使用定理 `Asymptotics.IsLittleO.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},  
 f =o[l] g → f =O[…
-/
theorem IsLittleO.add_isBigO (h₁ : f₁ =o[l] g) (h₂ : f₂ =O[l] g) : (fun x => f₁ x + f₂ x) =O[l] g :=
  h₁.isBigO.add h₂
/-
**Asymptotics.IsBigOWith.add_isLittleO** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.Is
BigOWith`。
形式化陈述：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} [inst : Norm F] [inst_1 : 
SeminormedAddCommGroup E'] {c₁ c₂ : ℝ}   {g : α → F} {l : Filter α} {f₁ f₂ : α →
 E'},   Asymptotics.IsBigOWith c₁ l f₁ g → f₂ =o[l] g → c₁ < c₂ → Asymptotics.Is
BigOWith c₂ l (fun x => f₁ x + f₂ x) g
参数：fun x => f₁ x + f₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.congr_const`：∀ {α : Type u_1} {E : Type u_3} {F :
 Type u_4} [inst : Norm E] [inst_1 : Norm F] {c₁ c₂ : ℝ} {f : α → E} {g : α → F}
   {l : Filter α}, Asymp…
· 使用定理 `Asymptotics.IsBigOWith.add`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u
_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {c₁ c₂ : ℝ}   {g : α → 
F} {l : Filter α…
· 使用定理 `Asymptotics.IsLittleO.forall_isBigOWith`：∀ {α : Type u_1} {E : Type u_3}
 {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : F
ilter α},   f =o[l] g → ∀ ⦃c …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
-/
theorem IsBigOWith.add_isLittleO (h₁ : IsBigOWith c₁ l f₁ g) (h₂ : f₂ =o[l] g) (hc : c₁ < c₂) :
    IsBigOWith c₂ l (fun x => f₁ x + f₂ x) g :=
  (h₁.add (h₂.forall_isBigOWith (sub_pos.2 hc))).congr_const (add_sub_cancel _ _)
/-
**Asymptotics.IsLittleO.add_isBigOWith** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.Is
LittleO`。
形式化陈述：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} [inst : Norm F] [inst_1 : 
SeminormedAddCommGroup E'] {c₁ c₂ : ℝ}   {g : α → F} {l : Filter α} {f₁ f₂ : α →
 E'},   f₁ =o[l] g → Asymptotics.IsBigOWith c₁ l f₂ g → c₁ < c₂ → Asymptotics.Is
BigOWith c₂ l (fun x => f₁ x + f₂ x) g
参数：fun x => f₁ x + f₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.congr_left`：∀ {α : Type u_1} {E : Type u_3} {F : 
Type u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {g : α → F} {l : Filter α}  
 {f₁ f₂ : α → E}, Asymp…
· 使用定理 `Asymptotics.IsBigOWith.add_isLittleO`：∀ {α : Type u_1} {F : Type u_4} {E
' : Type u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {c₁ c₂ : ℝ}  
 {g : α → F} {l : Filter α…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem IsLittleO.add_isBigOWith (h₁ : f₁ =o[l] g) (h₂ : IsBigOWith c₁ l f₂ g) (hc : c₁ < c₂) :
    IsBigOWith c₂ l (fun x => f₁ x + f₂ x) g :=
  (h₂.add_isLittleO h₁ hc).congr_left fun _ => add_comm _ _
/-
**Asymptotics.IsBigOWith.sub** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigOWith`。
形式化陈述：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} [inst : Norm F] [inst_1 : 
SeminormedAddCommGroup E'] {c₁ c₂ : ℝ}   {g : α → F} {l : Filter α} {f₁ f₂ : α →
 E'},   Asymptotics.IsBigOWith c₁ l f₁ g →     Asymptotics.IsBigOWith c₂ l f₂ g 
→ Asymptotics.IsBigOWith (c₁ + c₂) l (fun x => f₁ x - f₂ x) g
参数：c₁ + c₂；fun x => f₁ x - f₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Asymptotics.IsBigOWith.add`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u
_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {c₁ c₂ : ℝ}   {g : α → 
F} {l : Filter α…
· 使用定理 `Asymptotics.IsBigOWith.neg_left`：∀ {α : Type u_1} {F : Type u_4} {E' : T
ype u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {c : ℝ} {g : α → F
}   {f' : α → E'} {l …
-/
theorem IsBigOWith.sub (h₁ : IsBigOWith c₁ l f₁ g) (h₂ : IsBigOWith c₂ l f₂ g) :
    IsBigOWith (c₁ + c₂) l (fun x => f₁ x - f₂ x) g := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg_left
/-
**Asymptotics.IsBigOWith.sub_isLittleO** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.Is
BigOWith`。
形式化陈述：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} [inst : Norm F] [inst_1 : 
SeminormedAddCommGroup E'] {c₁ c₂ : ℝ}   {g : α → F} {l : Filter α} {f₁ f₂ : α →
 E'},   Asymptotics.IsBigOWith c₁ l f₁ g → f₂ =o[l] g → c₁ < c₂ → Asymptotics.Is
BigOWith c₂ l (fun x => f₁ x - f₂ x) g
参数：fun x => f₁ x - f₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Asymptotics.IsBigOWith.add_isLittleO`：∀ {α : Type u_1} {F : Type u_4} {E
' : Type u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {c₁ c₂ : ℝ}  
 {g : α → F} {l : Filter α…
· 使用定理 `Asymptotics.IsLittleO.neg_left`：∀ {α : Type u_1} {F : Type u_4} {E' : Ty
pe u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {f' :
 α → E'} {l : Filter…
-/
theorem IsBigOWith.sub_isLittleO (h₁ : IsBigOWith c₁ l f₁ g) (h₂ : f₂ =o[l] g) (hc : c₁ < c₂) :
    IsBigOWith c₂ l (fun x => f₁ x - f₂ x) g := by
  simpa only [sub_eq_add_neg] using h₁.add_isLittleO h₂.neg_left hc
/-
**Asymptotics.IsBigO.sub** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`。
形式化陈述：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} [inst : Norm F] [inst_1 : 
SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α} {f₁ f₂ : α → E'}, f₁ =O[
l] g → f₂ =O[l] g → (fun x => f₁ x - f₂ x) =O[l] g
参数：fun x => f₁ x - f₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Asymptotics.IsBigO.add`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} 
[inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α
} {f₁ f₂ : α…
· 使用定理 `Asymptotics.IsBigO.neg_left`：∀ {α : Type u_1} {F : Type u_4} {E' : Type 
u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {f' : α 
→ E'} {l : Filter…
-/
theorem IsBigO.sub (h₁ : f₁ =O[l] g) (h₂ : f₂ =O[l] g) : (fun x => f₁ x - f₂ x) =O[l] g := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg_left
/-
**Asymptotics.IsLittleO.sub** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLittleO`。
形式化陈述：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} [inst : Norm F] [inst_1 : 
SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α} {f₁ f₂ : α → E'}, f₁ =o[
l] g → f₂ =o[l] g → (fun x => f₁ x - f₂ x) =o[l] g
参数：fun x => f₁ x - f₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Asymptotics.IsLittleO.add`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_
6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filte
r α} {f₁ f₂ : α…
· 使用定理 `Asymptotics.IsLittleO.neg_left`：∀ {α : Type u_1} {F : Type u_4} {E' : Ty
pe u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {f' :
 α → E'} {l : Filter…
-/
theorem IsLittleO.sub (h₁ : f₁ =o[l] g) (h₂ : f₂ =o[l] g) : (fun x => f₁ x - f₂ x) =o[l] g := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg_left
/-
**Asymptotics.IsBigO.add_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`
。
形式化陈述：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} [inst : Norm F] [inst_1 : 
SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α} {f₁ f₂ : α → E'}, f₂ =O[
l] g → ((fun x => f₁ x + f₂ x) =O[l] g ↔ f₁ =O[l] g)
参数：(fun x => f₁ x + f₂ x) =O[l] g ↔ f₁ =O[l] g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.congr`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4}
 [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ : α →
 F}, f₁ =O[l] …
· 使用定理 `Asymptotics.IsBigO.sub`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} 
[inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α
} {f₁ f₂ : α…
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `Asymptotics.IsBigO.add`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} 
[inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α
} {f₁ f₂ : α…
-/
theorem IsBigO.add_iff_left (h₂ : f₂ =O[l] g) : (fun x => f₁ x + f₂ x) =O[l] g ↔ (f₁ =O[l] g) :=
  ⟨fun h ↦ h.sub h₂ |>.congr (fun _ ↦ add_sub_cancel_right _ _) (fun _ ↦ rfl), fun h ↦ h.add h₂⟩
/-
**Asymptotics.IsBigO.add_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO
`。
形式化陈述：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} [inst : Norm F] [inst_1 : 
SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α} {f₁ f₂ : α → E'}, f₁ =O[
l] g → ((fun x => f₁ x + f₂ x) =O[l] g ↔ f₂ =O[l] g)
参数：(fun x => f₁ x + f₂ x) =O[l] g ↔ f₂ =O[l] g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.congr`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4}
 [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ : α →
 F}, f₁ =O[l] …
· 使用定理 `Asymptotics.IsBigO.sub`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} 
[inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α
} {f₁ f₂ : α…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_sub_of_add_eq'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G},
 c + a = b → a = b - c
· 使用定理 `Asymptotics.IsBigO.add`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} 
[inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α
} {f₁ f₂ : α…
-/
theorem IsBigO.add_iff_right (h₁ : f₁ =O[l] g) : (fun x => f₁ x + f₂ x) =O[l] g ↔ (f₂ =O[l] g) :=
  ⟨fun h ↦ h.sub h₁ |>.congr (fun _ ↦ (eq_sub_of_add_eq' rfl).symm) (fun _ ↦ rfl), fun h ↦ h₁.add h⟩
/-
**Asymptotics.IsLittleO.add_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLi
ttleO`。
形式化陈述：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} [inst : Norm F] [inst_1 : 
SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α} {f₁ f₂ : α → E'}, f₂ =o[
l] g → ((fun x => f₁ x + f₂ x) =o[l] g ↔ f₁ =o[l] g)
参数：(fun x => f₁ x + f₂ x) =o[l] g ↔ f₁ =o[l] g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.congr`：∀ {α : Type u_1} {E : Type u_3} {F : Type u
_4} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ : 
α → F}, f₁ =o[l] …
· 使用定理 `Asymptotics.IsLittleO.sub`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_
6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filte
r α} {f₁ f₂ : α…
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `Asymptotics.IsLittleO.add`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_
6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filte
r α} {f₁ f₂ : α…
-/
theorem IsLittleO.add_iff_left (h₂ : f₂ =o[l] g) : (fun x => f₁ x + f₂ x) =o[l] g ↔ (f₁ =o[l] g) :=
  ⟨fun h ↦ h.sub h₂ |>.congr (fun _ ↦ add_sub_cancel_right _ _) (fun _ ↦ rfl), fun h ↦ h.add h₂⟩
/-
**Asymptotics.IsLittleO.add_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsL
ittleO`。
形式化陈述：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} [inst : Norm F] [inst_1 : 
SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α} {f₁ f₂ : α → E'}, f₁ =o[
l] g → ((fun x => f₁ x + f₂ x) =o[l] g ↔ f₂ =o[l] g)
参数：(fun x => f₁ x + f₂ x) =o[l] g ↔ f₂ =o[l] g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.congr`：∀ {α : Type u_1} {E : Type u_3} {F : Type u
_4} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ : 
α → F}, f₁ =o[l] …
· 使用定理 `Asymptotics.IsLittleO.sub`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_
6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filte
r α} {f₁ f₂ : α…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_sub_of_add_eq'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G},
 c + a = b → a = b - c
· 使用定理 `Asymptotics.IsLittleO.add`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_
6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filte
r α} {f₁ f₂ : α…
-/
theorem IsLittleO.add_iff_right (h₁ : f₁ =o[l] g) : (fun x => f₁ x + f₂ x) =o[l] g ↔ (f₂ =o[l] g) :=
  ⟨fun h ↦ h.sub h₁ |>.congr (fun _ ↦ (eq_sub_of_add_eq' rfl).symm) (fun _ ↦ rfl), fun h ↦ h₁.add h⟩
/-
**Asymptotics.IsBigO.sub_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`
。
形式化陈述：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} [inst : Norm F] [inst_1 : 
SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α} {f₁ f₂ : α → E'}, f₂ =O[
l] g → ((fun x => f₁ x - f₂ x) =O[l] g ↔ f₁ =O[l] g)
参数：(fun x => f₁ x - f₂ x) =O[l] g ↔ f₁ =O[l] g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.congr`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4}
 [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ : α →
 F}, f₁ =O[l] …
· 使用定理 `Asymptotics.IsBigO.add`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} 
[inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α
} {f₁ f₂ : α…
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `Asymptotics.IsBigO.sub`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} 
[inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α
} {f₁ f₂ : α…
-/
theorem IsBigO.sub_iff_left (h₂ : f₂ =O[l] g) : (fun x => f₁ x - f₂ x) =O[l] g ↔ (f₁ =O[l] g) :=
  ⟨fun h ↦ h.add h₂ |>.congr (fun _ ↦ sub_add_cancel ..) (fun _ ↦ rfl), fun h ↦ h.sub h₂⟩
/-
**Asymptotics.IsBigO.sub_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO
`。
形式化陈述：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} [inst : Norm F] [inst_1 : 
SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α} {f₁ f₂ : α → E'}, f₁ =O[
l] g → ((fun x => f₁ x - f₂ x) =O[l] g ↔ f₂ =O[l] g)
参数：(fun x => f₁ x - f₂ x) =O[l] g ↔ f₂ =O[l] g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.congr`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4}
 [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ : α →
 F}, f₁ =O[l] …
· 使用定理 `Asymptotics.IsBigO.sub`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} 
[inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α
} {f₁ f₂ : α…
· 使用定理 `sub_sub_self`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - (a
 - b) = b
-/
theorem IsBigO.sub_iff_right (h₁ : f₁ =O[l] g) : (fun x => f₁ x - f₂ x) =O[l] g ↔ (f₂ =O[l] g) :=
  ⟨fun h ↦ h₁.sub h |>.congr (fun _ ↦ sub_sub_self ..) (fun _ ↦ rfl), fun h ↦ h₁.sub h⟩
/-
**Asymptotics.IsLittleO.sub_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLi
ttleO`。
形式化陈述：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} [inst : Norm F] [inst_1 : 
SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α} {f₁ f₂ : α → E'}, f₂ =o[
l] g → ((fun x => f₁ x - f₂ x) =o[l] g ↔ f₁ =o[l] g)
参数：(fun x => f₁ x - f₂ x) =o[l] g ↔ f₁ =o[l] g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.congr`：∀ {α : Type u_1} {E : Type u_3} {F : Type u
_4} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ : 
α → F}, f₁ =o[l] …
· 使用定理 `Asymptotics.IsLittleO.add`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_
6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filte
r α} {f₁ f₂ : α…
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `Asymptotics.IsLittleO.sub`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_
6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filte
r α} {f₁ f₂ : α…
-/
theorem IsLittleO.sub_iff_left (h₂ : f₂ =o[l] g) : (fun x => f₁ x - f₂ x) =o[l] g ↔ (f₁ =o[l] g) :=
  ⟨fun h ↦ h.add h₂ |>.congr (fun _ ↦ sub_add_cancel ..) (fun _ ↦ rfl), fun h ↦ h.sub h₂⟩
/-
**Asymptotics.IsLittleO.sub_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsL
ittleO`。
形式化陈述：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} [inst : Norm F] [inst_1 : 
SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α} {f₁ f₂ : α → E'}, f₁ =o[
l] g → ((fun x => f₁ x - f₂ x) =o[l] g ↔ f₂ =o[l] g)
参数：(fun x => f₁ x - f₂ x) =o[l] g ↔ f₂ =o[l] g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.congr`：∀ {α : Type u_1} {E : Type u_3} {F : Type u
_4} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ : 
α → F}, f₁ =o[l] …
· 使用定理 `Asymptotics.IsLittleO.sub`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_
6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filte
r α} {f₁ f₂ : α…
· 使用定理 `sub_sub_self`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - (a
 - b) = b
-/
theorem IsLittleO.sub_iff_right (h₁ : f₁ =o[l] g) : (fun x => f₁ x - f₂ x) =o[l] g ↔ (f₂ =o[l] g) :=
  ⟨fun h ↦ h₁.sub h |>.congr (fun _ ↦ sub_sub_self ..) (fun _ ↦ rfl), fun h ↦ h₁.sub h⟩

end add_sub

/-!
### Lemmas about `IsBigO (f₁ - f₂) g l` / `IsLittleO (f₁ - f₂) g l` treated as a binary relation
-/


section IsBigOOAsRel

variable {f₁ f₂ f₃ : α → E'}

/-
**Asymptotics.IsBigOWith.symm** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigOWith`
。
形式化陈述：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} [inst : Norm F] [inst_1 : 
SeminormedAddCommGroup E'] {c : ℝ} {g : α → F}   {l : Filter α} {f₁ f₂ : α → E'}
,   Asymptotics.IsBigOWith c l (fun x => f₁ x - f₂ x) g → Asymptotics.IsBigOWith
 c l (fun x => f₂ x - f₁ x) g
参数：fun x => f₁ x - f₂ x；fun x => f₂ x - f₁ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.congr_left`：∀ {α : Type u_1} {E : Type u_3} {F : 
Type u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {g : α → F} {l : Filter α}  
 {f₁ f₂ : α → E}, Asymp…
· 使用定理 `Asymptotics.IsBigOWith.neg_left`：∀ {α : Type u_1} {F : Type u_4} {E' : T
ype u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {c : ℝ} {g : α → F
}   {f' : α → E'} {l …
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
-/
theorem IsBigOWith.symm (h : IsBigOWith c l (fun x => f₁ x - f₂ x) g) :
    IsBigOWith c l (fun x => f₂ x - f₁ x) g :=
  h.neg_left.congr_left fun _x => neg_sub _ _
/-
**Asymptotics.isBigOWith_comm** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOWith_comm : IsBigOWith c l (fun x => f₁ x - f₂ x) g ↔ IsBigOWith c l
 (fun x => f₂ x - f₁ x) g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.symm`：∀ {α : Type u_1} {F : Type u_4} {E' : Type 
u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {c : ℝ} {g : α → F}   
{l : Filter α} {f…
-/
theorem isBigOWith_comm :
    IsBigOWith c l (fun x => f₁ x - f₂ x) g ↔ IsBigOWith c l (fun x => f₂ x - f₁ x) g :=
  ⟨IsBigOWith.symm, IsBigOWith.symm⟩
/-
**Asymptotics.IsBigO.symm** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`。
形式化陈述：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} [inst : Norm F] [inst_1 : 
SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α} {f₁ f₂ : α → E'}, (fun x
 => f₁ x - f₂ x) =O[l] g → (fun x => f₂ x - f₁ x) =O[l] g
参数：fun x => f₁ x - f₂ x；fun x => f₂ x - f₁ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.congr_left`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {g : α → F} {l : Filter α}   {f₁ f₂ : α 
→ E}, f₁ =O[l] g → …
· 使用定理 `Asymptotics.IsBigO.neg_left`：∀ {α : Type u_1} {F : Type u_4} {E' : Type 
u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {f' : α 
→ E'} {l : Filter…
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
-/
theorem IsBigO.symm (h : (fun x => f₁ x - f₂ x) =O[l] g) : (fun x => f₂ x - f₁ x) =O[l] g :=
  h.neg_left.congr_left fun _x => neg_sub _ _
/-
**Asymptotics.isBigO_comm** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_comm : (fun x => f₁ x - f₂ x) =O[l] g ↔ (fun x => f₂ x - f₁ x) =O[l
] g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.symm`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6}
 [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filter 
α} {f₁ f₂ : α…
-/
theorem isBigO_comm : (fun x => f₁ x - f₂ x) =O[l] g ↔ (fun x => f₂ x - f₁ x) =O[l] g :=
  ⟨IsBigO.symm, IsBigO.symm⟩
/-
**Asymptotics.IsLittleO.symm** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLittleO`。
形式化陈述：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} [inst : Norm F] [inst_1 : 
SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α} {f₁ f₂ : α → E'}, (fun x
 => f₁ x - f₂ x) =o[l] g → (fun x => f₂ x - f₁ x) =o[l] g
参数：fun x => f₁ x - f₂ x；fun x => f₂ x - f₁ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `Asymptotics.IsLittleO.neg_left`：∀ {α : Type u_1} {F : Type u_4} {E' : Ty
pe u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {f' :
 α → E'} {l : Filter…
-/
theorem IsLittleO.symm (h : (fun x => f₁ x - f₂ x) =o[l] g) : (fun x => f₂ x - f₁ x) =o[l] g := by
  simpa only [neg_sub] using h.neg_left
/-
**Asymptotics.isLittleO_comm** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_comm : (fun x => f₁ x - f₂ x) =o[l] g ↔ (fun x => f₂ x - f₁ x) =
o[l] g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.symm`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u
_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filt
er α} {f₁ f₂ : α…
-/
theorem isLittleO_comm : (fun x => f₁ x - f₂ x) =o[l] g ↔ (fun x => f₂ x - f₁ x) =o[l] g :=
  ⟨IsLittleO.symm, IsLittleO.symm⟩
/-
**Asymptotics.IsBigOWith.triangle** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigOW
ith`。
形式化陈述：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} [inst : Norm F] [inst_1 : 
SeminormedAddCommGroup E'] {c c' : ℝ}   {g : α → F} {l : Filter α} {f₁ f₂ f₃ : α
 → E'},   Asymptotics.IsBigOWith c l (fun x => f₁ x - f₂ x) g →     Asymptotics.
IsBigOWith c' l (fun x => f₂ x - f₃ x) g → Asymptotics.IsBigOWith (c + c') l (fu
n x => f₁ x - f₃ x) g
参数：fun x => f₁ x - f₂ x；fun x => f₂ x - f₃ x；c + c'；fun x => f₁ x - f₃ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.congr_left`：∀ {α : Type u_1} {E : Type u_3} {F : 
Type u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {g : α → F} {l : Filter α}  
 {f₁ f₂ : α → E}, Asymp…
· 使用定理 `Asymptotics.IsBigOWith.add`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u
_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {c₁ c₂ : ℝ}   {g : α → 
F} {l : Filter α…
· 使用定理 `sub_add_sub_cancel`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : G), a 
- b + (b - c) = a - c
-/
theorem IsBigOWith.triangle (h₁ : IsBigOWith c l (fun x => f₁ x - f₂ x) g)
    (h₂ : IsBigOWith c' l (fun x => f₂ x - f₃ x) g) :
    IsBigOWith (c + c') l (fun x => f₁ x - f₃ x) g :=
  (h₁.add h₂).congr_left fun _x => sub_add_sub_cancel _ _ _
/-
**Asymptotics.IsBigO.triangle** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`。
形式化陈述：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} [inst : Norm F] [inst_1 : 
SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α} {f₁ f₂ f₃ : α → E'},   (
fun x => f₁ x - f₂ x) =O[l] g → (fun x => f₂ x - f₃ x) =O[l] g → (fun x => f₁ x 
- f₃ x) =O[l] g
参数：fun x => f₁ x - f₂ x；fun x => f₂ x - f₃ x；fun x => f₁ x - f₃ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.congr_left`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {g : α → F} {l : Filter α}   {f₁ f₂ : α 
→ E}, f₁ =O[l] g → …
· 使用定理 `Asymptotics.IsBigO.add`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} 
[inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α
} {f₁ f₂ : α…
· 使用定理 `sub_add_sub_cancel`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : G), a 
- b + (b - c) = a - c
-/
theorem IsBigO.triangle (h₁ : (fun x => f₁ x - f₂ x) =O[l] g)
    (h₂ : (fun x => f₂ x - f₃ x) =O[l] g) : (fun x => f₁ x - f₃ x) =O[l] g :=
  (h₁.add h₂).congr_left fun _x => sub_add_sub_cancel _ _ _
/-
**Asymptotics.IsLittleO.triangle** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLittle
O`。
形式化陈述：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} [inst : Norm F] [inst_1 : 
SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α} {f₁ f₂ f₃ : α → E'},   (
fun x => f₁ x - f₂ x) =o[l] g → (fun x => f₂ x - f₃ x) =o[l] g → (fun x => f₁ x 
- f₃ x) =o[l] g
参数：fun x => f₁ x - f₂ x；fun x => f₂ x - f₃ x；fun x => f₁ x - f₃ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.congr_left`：∀ {α : Type u_1} {E : Type u_3} {F : T
ype u_4} [inst : Norm E] [inst_1 : Norm F] {g : α → F} {l : Filter α}   {f₁ f₂ :
 α → E}, f₁ =o[l] g → …
· 使用定理 `Asymptotics.IsLittleO.add`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_
6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filte
r α} {f₁ f₂ : α…
· 使用定理 `sub_add_sub_cancel`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : G), a 
- b + (b - c) = a - c
-/
theorem IsLittleO.triangle (h₁ : (fun x => f₁ x - f₂ x) =o[l] g)
    (h₂ : (fun x => f₂ x - f₃ x) =o[l] g) : (fun x => f₁ x - f₃ x) =o[l] g :=
  (h₁.add h₂).congr_left fun _x => sub_add_sub_cancel _ _ _
/-
**Asymptotics.IsBigO.congr_of_sub** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`
。
形式化陈述：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} [inst : Norm F] [inst_1 : 
SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α} {f₁ f₂ : α → E'}, (fun x
 => f₁ x - f₂ x) =O[l] g → (f₁ =O[l] g ↔ f₂ =O[l] g)
参数：fun x => f₁ x - f₂ x；f₁ =O[l] g ↔ f₂ =O[l] g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.congr_left`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {g : α → F} {l : Filter α}   {f₁ f₂ : α 
→ E}, f₁ =O[l] g → …
· 使用定理 `Asymptotics.IsBigO.sub`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} 
[inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α
} {f₁ f₂ : α…
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `Asymptotics.IsBigO.add`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} 
[inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α
} {f₁ f₂ : α…
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
-/
theorem IsBigO.congr_of_sub (h : (fun x => f₁ x - f₂ x) =O[l] g) : f₁ =O[l] g ↔ f₂ =O[l] g :=
  ⟨fun h' => (h'.sub h).congr_left fun _x => sub_sub_cancel _ _, fun h' =>
    (h.add h').congr_left fun _x => sub_add_cancel _ _⟩
/-
**Asymptotics.IsLittleO.congr_of_sub** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLi
ttleO`。
形式化陈述：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} [inst : Norm F] [inst_1 : 
SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α} {f₁ f₂ : α → E'}, (fun x
 => f₁ x - f₂ x) =o[l] g → (f₁ =o[l] g ↔ f₂ =o[l] g)
参数：fun x => f₁ x - f₂ x；f₁ =o[l] g ↔ f₂ =o[l] g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.congr_left`：∀ {α : Type u_1} {E : Type u_3} {F : T
ype u_4} [inst : Norm E] [inst_1 : Norm F] {g : α → F} {l : Filter α}   {f₁ f₂ :
 α → E}, f₁ =o[l] g → …
· 使用定理 `Asymptotics.IsLittleO.sub`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_
6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filte
r α} {f₁ f₂ : α…
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `Asymptotics.IsLittleO.add`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_
6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filte
r α} {f₁ f₂ : α…
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
-/
theorem IsLittleO.congr_of_sub (h : (fun x => f₁ x - f₂ x) =o[l] g) : f₁ =o[l] g ↔ f₂ =o[l] g :=
  ⟨fun h' => (h'.sub h).congr_left fun _x => sub_sub_cancel _ _, fun h' =>
    (h.add h').congr_left fun _x => sub_add_cancel _ _⟩

end IsBigOOAsRel

/-! ### Zero, one, and other constants -/


section ZeroConst

variable (g g' l)

/-
**Asymptotics.isLittleO_zero** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_zero : (fun _x => (0 : E')) =o[l] g'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.of_bound`：∀ {α : Type u_1} {E : Type u_3} {F : Typ
e u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},
   (∀ ⦃c : ℝ⦄, 0 < c…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem isLittleO_zero : (fun _x => (0 : E')) =o[l] g' :=
  IsLittleO.of_bound fun c hc =>
    univ_mem' fun x => by simpa using mul_nonneg hc.le (norm_nonneg <| g' x)
/-
**Asymptotics.isBigOWith_zero** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOWith_zero (hc : 0 <= c) : IsBigOWith c l (fun _x => (0 : E')) g'
参数：hc : 0 <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.of_bound`：∀ {α : Type u_1} {E : Type u_3} {F : Ty
pe u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l :
 Filter α}, (∀ᶠ (x : …
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem isBigOWith_zero (hc : 0 ≤ c) : IsBigOWith c l (fun _x => (0 : E')) g' :=
  IsBigOWith.of_bound <| univ_mem' fun x => by simpa using mul_nonneg hc (norm_nonneg <| g' x)
/-
**Asymptotics.isBigOWith_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOWith_zero' : IsBigOWith 0 l (fun _x => (0 : E')) g
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.of_bound`：∀ {α : Type u_1} {E : Type u_3} {F : Ty
pe u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l :
 Filter α}, (∀ᶠ (x : …
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem isBigOWith_zero' : IsBigOWith 0 l (fun _x => (0 : E')) g :=
  IsBigOWith.of_bound <| univ_mem' fun x => by simp
/-
**Asymptotics.isBigO_zero** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_zero : (fun _x => (0 : E')) =O[l] g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Asymptotics.isBigO_iff_isBigOWith`：isBigO_iff_isBigOWith : f =O[l] g ↔ e
xists c : Real, IsBigOWith c l f g
· 使用定理 `Asymptotics.isBigOWith_zero'`：isBigOWith_zero' : IsBigOWith 0 l (fun _x 
=> (0 : E')) g
-/
theorem isBigO_zero : (fun _x => (0 : E')) =O[l] g :=
  isBigO_iff_isBigOWith.2 ⟨0, isBigOWith_zero' _ _⟩
/-
**Asymptotics.isBigO_refl_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_refl_left : (fun x => f' x - f' x) =O[l] g'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.congr_left`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {g : α → F} {l : Filter α}   {f₁ f₂ : α 
→ E}, f₁ =O[l] g → …
· 使用定理 `Asymptotics.isBigO_zero`：isBigO_zero : (fun _x => (0 : E')) =O[l] g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
theorem isBigO_refl_left : (fun x => f' x - f' x) =O[l] g' :=
  (isBigO_zero g' l).congr_left fun _x => (sub_self _).symm
/-
**Asymptotics.isLittleO_refl_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_refl_left : (fun x => f' x - f' x) =o[l] g'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.congr_left`：∀ {α : Type u_1} {E : Type u_3} {F : T
ype u_4} [inst : Norm E] [inst_1 : Norm F] {g : α → F} {l : Filter α}   {f₁ f₂ :
 α → E}, f₁ =o[l] g → …
· 使用定理 `Asymptotics.isLittleO_zero`：isLittleO_zero : (fun _x => (0 : E')) =o[l] 
g'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
theorem isLittleO_refl_left : (fun x => f' x - f' x) =o[l] g' :=
  (isLittleO_zero g' l).congr_left fun _x => (sub_self _).symm

variable {g g' l}

@[simp]
/-
**Asymptotics.isBigOWith_zero_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOWith_zero_right_iff : (IsBigOWith c l f'' fun _x => (0 : F')) ↔ f'' 
=ᶠ[l] 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.IsBigOWith_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type 
u_20} [inst : Norm E] [inst_1 : Norm F] (c : ℝ) (l : Filter α) (f : α → E)   (g 
: α → F), Asympt…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isBigOWith_zero_right_iff : (IsBigOWith c l f'' fun _x => (0 : F')) ↔ f'' =ᶠ[l] 0 := by
  simp only [IsBigOWith_def, norm_zero, mul_zero, norm_le_zero_iff, EventuallyEq, Pi.zero_apply]

@[simp]
/-
**Asymptotics.isBigO_zero_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_zero_right_iff : (f'' =O[l] fun _x => (0 : F')) ↔ f'' =ᶠ[l] 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.isBigOWith`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α}, 
  f =O[l] g → ∃ c, …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Asymptotics.isBigOWith_zero_right_iff`：isBigOWith_zero_right_iff : (IsBi
gOWith c l f'' fun _x => (0 : F')) ↔ f'' =ᶠ[l] 0
· 使用定理 `Asymptotics.IsBigOWith.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : F
ilter α}, Asymptoti…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem isBigO_zero_right_iff : (f'' =O[l] fun _x => (0 : F')) ↔ f'' =ᶠ[l] 0 :=
  ⟨fun h =>
    let ⟨_c, hc⟩ := h.isBigOWith
    isBigOWith_zero_right_iff.1 hc,
    fun h => (isBigOWith_zero_right_iff.2 h : IsBigOWith 1 _ _ _).isBigO⟩

@[simp]
/-
**Asymptotics.isLittleO_zero_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_zero_right_iff : (f'' =o[l] fun _x => (0 : F')) ↔ f'' =ᶠ[l] 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Asymptotics.isBigO_zero_right_iff`：isBigO_zero_right_iff : (f'' =O[l] fu
n _x => (0 : F')) ↔ f'' =ᶠ[l] 0
· 使用定理 `Asymptotics.IsLittleO.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},  
 f =o[l] g → f =O[…
· 使用定理 `Asymptotics.IsLittleO.of_isBigOWith`：∀ {α : Type u_1} {E : Type u_3} {F 
: Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filte
r α},   (∀ ⦃c : ℝ⦄, 0 < c…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Asymptotics.isBigOWith_zero_right_iff`：isBigOWith_zero_right_iff : (IsBi
gOWith c l f'' fun _x => (0 : F')) ↔ f'' =ᶠ[l] 0
-/
theorem isLittleO_zero_right_iff : (f'' =o[l] fun _x => (0 : F')) ↔ f'' =ᶠ[l] 0 :=
  ⟨fun h => isBigO_zero_right_iff.1 h.isBigO,
   fun h => IsLittleO.of_isBigOWith fun _c _hc => isBigOWith_zero_right_iff.2 h⟩
/-
**Asymptotics.isBigOWith_const_const** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOWith_const_const (c : E) {c' : F''} (hc' : c' != 0) (l : Filter α) :
 IsBigOWith (‖c‖ / ‖c'‖) l (fun _x : α => c) fun _x => c'
参数：c : E；hc' : c' != 0；l : Filter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type 
u_20} [inst : Norm E] [inst_1 : Norm F] (c : ℝ) (l : Filter α) (f : α → E)   (g 
: α → F), Asympt…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem isBigOWith_const_const (c : E) {c' : F''} (hc' : c' ≠ 0) (l : Filter α) :
    IsBigOWith (‖c‖ / ‖c'‖) l (fun _x : α => c) fun _x => c' := by
  simp only [IsBigOWith_def]
  apply univ_mem'
  intro x
  rw [mem_ofPred, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hc')]
/-
**Asymptotics.isBigO_const_const** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_const_const (c : E) {c' : F''} (hc' : c' != 0) (l : Filter α) : (fu
n _x : α => c) =O[l] fun _x => c'
参数：c : E；hc' : c' != 0；l : Filter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : F
ilter α}, Asymptoti…
· 使用定理 `Asymptotics.isBigOWith_const_const`：isBigOWith_const_const (c : E) {c' :
 F''} (hc' : c' != 0) (l : Filter α) : IsBigOWith (‖c‖ / ‖c'‖) l (fun _x : α => 
c) fun _x => c'
-/
theorem isBigO_const_const (c : E) {c' : F''} (hc' : c' ≠ 0) (l : Filter α) :
    (fun _x : α => c) =O[l] fun _x => c' :=
  (isBigOWith_const_const c hc' l).isBigO

@[simp]
/-
**Asymptotics.isBigO_const_const_iff** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_const_const_iff {c : E''} {c' : F''} (l : Filter α) [l.NeBot] : ((f
un _x : α => c) =O[l] fun _x => c') ↔ c' = 0 -> c = 0
参数：l : Filter α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Asymptotics.isBigO_const_const`：isBigO_const_const (c : E) {c' : F''} (h
c' : c' != 0) (l : Filter α) : (fun _x : α => c) =O[l] fun _x => c'
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
-/
theorem isBigO_const_const_iff {c : E''} {c' : F''} (l : Filter α) [l.NeBot] :
    ((fun _x : α => c) =O[l] fun _x => c') ↔ c' = 0 → c = 0 := by
  rcases eq_or_ne c' 0 with (rfl | hc')
  · simp [EventuallyEq]
  · simp [hc', isBigO_const_const _ hc']

@[simp]
/-
**Asymptotics.isBigO_pure** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_pure {x} : f'' =O[pure x] g'' ↔ g'' x = 0 -> f'' x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isBigO_congr`：isBigO_congr (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l]
 g₂) : f₁ =O[l] g₁ ↔ f₂ =O[l] g₂
· 使用定理 `Asymptotics.isBigO_const_const_iff`：isBigO_const_const_iff {c : E''} {c'
 : F''} (l : Filter α) [l.NeBot] : ((fun _x : α => c) =O[l] fun _x => c') ↔ c' =
 0 -> c = 0
-/
theorem isBigO_pure {x} : f'' =O[pure x] g'' ↔ g'' x = 0 → f'' x = 0 :=
  calc
    f'' =O[pure x] g'' ↔ (fun _y : α => f'' x) =O[pure x] fun _ => g'' x := isBigO_congr rfl rfl
    _ ↔ g'' x = 0 → f'' x = 0 := isBigO_const_const_iff _

end ZeroConst

/-! ### Multiplication by a constant -/

/-
**Asymptotics.isBigOWith_const_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOWith_const_mul_self (c : R) (f : α -> R) (l : Filter α) : IsBigOWith
 ‖c‖ l (fun x => c * f x) f
参数：c : R；f : α -> R；l : Filter α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isBigOWith_of_le'`：isBigOWith_of_le' (hfg : forall x, ‖f x‖ 
<= c * ‖g x‖) : IsBigOWith c l f g
· 使用定理 `norm_mul_le`：norm_mul_le (a b : α) : ‖a * b‖ <= ‖a‖ * ‖b‖

--- 原说明 ---
### Multiplication by a constant
-/
theorem isBigOWith_const_mul_self (c : R) (f : α → R) (l : Filter α) :
    IsBigOWith ‖c‖ l (fun x => c * f x) f :=
  isBigOWith_of_le' _ fun _x => norm_mul_le _ _
/-
**Asymptotics.isBigO_const_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_const_mul_self (c : R) (f : α -> R) (l : Filter α) : (fun x => c * 
f x) =O[l] f
参数：c : R；f : α -> R；l : Filter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : F
ilter α}, Asymptoti…
· 使用定理 `Asymptotics.isBigOWith_const_mul_self`：isBigOWith_const_mul_self (c : R)
 (f : α -> R) (l : Filter α) : IsBigOWith ‖c‖ l (fun x => c * f x) f
-/
theorem isBigO_const_mul_self (c : R) (f : α → R) (l : Filter α) : (fun x => c * f x) =O[l] f :=
  (isBigOWith_const_mul_self c f l).isBigO
/-
**Asymptotics.IsBigOWith.const_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.I
sBigOWith`。
形式化陈述：∀ {α : Type u_1} {F : Type u_4} {R : Type u_13} [inst : Norm F] [inst_1 : 
SeminormedRing R] {c : ℝ} {g : α → F}   {l : Filter α} {f : α → R},   Asymptotic
s.IsBigOWith c l f g → ∀ (c' : R), Asymptotics.IsBigOWith (‖c'‖ * c) l (fun x =>
 c' * f x) g
参数：c' : R；‖c'‖ * c；fun x => c' * f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.trans`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} {G : Type u_5} [inst : Norm E] [inst_1 : Norm F] [inst_2 : Norm G]   {c c' 
: ℝ} {f : α → E} {…
· 使用定理 `Asymptotics.isBigOWith_const_mul_self`：isBigOWith_const_mul_self (c : R)
 (f : α -> R) (l : Filter α) : IsBigOWith ‖c‖ l (fun x => c * f x) f
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem IsBigOWith.const_mul_left {f : α → R} (h : IsBigOWith c l f g) (c' : R) :
    IsBigOWith (‖c'‖ * c) l (fun x => c' * f x) g :=
  (isBigOWith_const_mul_self c' f l).trans h (norm_nonneg c')
/-
**Asymptotics.IsBigO.const_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBig
O`。
形式化陈述：∀ {α : Type u_1} {F : Type u_4} {R : Type u_13} [inst : Norm F] [inst_1 : 
SeminormedRing R] {g : α → F} {l : Filter α}   {f : α → R}, f =O[l] g → ∀ (c' : 
R), (fun x => c' * f x) =O[l] g
参数：c' : R；fun x => c' * f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.isBigOWith`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α}, 
  f =O[l] g → ∃ c, …
· 使用定理 `Asymptotics.IsBigOWith.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : F
ilter α}, Asymptoti…
· 使用定理 `Asymptotics.IsBigOWith.const_mul_left`：∀ {α : Type u_1} {F : Type u_4} {
R : Type u_13} [inst : Norm F] [inst_1 : SeminormedRing R] {c : ℝ} {g : α → F}  
 {l : Filter α} {f : α → R}…
-/
theorem IsBigO.const_mul_left {f : α → R} (h : f =O[l] g) (c' : R) : (fun x => c' * f x) =O[l] g :=
  let ⟨_c, hc⟩ := h.isBigOWith
  (hc.const_mul_left c').isBigO
/-
**Asymptotics.isBigOWith_self_const_mul'** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`
。
形式化陈述：isBigOWith_self_const_mul' (u : Rˣ) (f : α -> R) (l : Filter α) : IsBigOWi
th ‖(↑u⁻¹ : R)‖ l f fun x => ↑u * f x
参数：u : Rˣ；f : α -> R；l : Filter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.congr_left`：∀ {α : Type u_1} {E : Type u_3} {F : 
Type u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {g : α → F} {l : Filter α}  
 {f₁ f₂ : α → E}, Asymp…
· 使用定理 `Asymptotics.isBigOWith_const_mul_self`：isBigOWith_const_mul_self (c : R)
 (f : α -> R) (l : Filter α) : IsBigOWith ‖c‖ l (fun x => c * f x) f
· 使用定理 `Units.inv_mul_cancel_left`：inv_mul_cancel_left (a : αˣ) (b : α) : (↑a⁻¹ 
: α) * (a * b) = b
-/
theorem isBigOWith_self_const_mul' (u : Rˣ) (f : α → R) (l : Filter α) :
    IsBigOWith ‖(↑u⁻¹ : R)‖ l f fun x => ↑u * f x :=
  (isBigOWith_const_mul_self ↑u⁻¹ (fun x ↦ ↑u * f x) l).congr_left
    fun x ↦ u.inv_mul_cancel_left (f x)
/-
**Asymptotics.isBigOWith_self_const_mul** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOWith_self_const_mul {c : S} (hc : c != 0) (f : α -> S) (l : Filter α
) : IsBigOWith ‖c‖⁻¹ l f fun x => c * f x
参数：hc : c != 0；f : α -> S；l : Filter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Asymptotics.IsBigOWith_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type 
u_20} [inst : Norm E] [inst_1 : Norm F] (c : ℝ) (l : Filter α) (f : α → E)   (g 
: α → F), Asympt…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `inv_mul_cancel_left₀`：inv_mul_cancel_left₀ (h : a != 0) (b : G₀) : a⁻¹ *
 (a * b) = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0
-/
theorem isBigOWith_self_const_mul {c : S} (hc : c ≠ 0) (f : α → S) (l : Filter α) :
    IsBigOWith ‖c‖⁻¹ l f fun x ↦ c * f x := by
  simp [IsBigOWith, inv_mul_cancel_left₀ (norm_ne_zero_iff.mpr hc)]
/-
**Asymptotics.isBigO_self_const_mul'** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_self_const_mul' {c : R} (hc : IsUnit c) (f : α -> R) (l : Filter α)
 : f =O[l] fun x => c * f x
参数：hc : IsUnit c；f : α -> R；l : Filter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : F
ilter α}, Asymptoti…
· 使用定理 `Asymptotics.isBigOWith_self_const_mul'`：isBigOWith_self_const_mul' (u : 
Rˣ) (f : α -> R) (l : Filter α) : IsBigOWith ‖(↑u⁻¹ : R)‖ l f fun x => ↑u * f x
-/
theorem isBigO_self_const_mul' {c : R} (hc : IsUnit c) (f : α → R) (l : Filter α) :
    f =O[l] fun x => c * f x :=
  let ⟨u, hu⟩ := hc
  hu ▸ (isBigOWith_self_const_mul' u f l).isBigO
/-
**Asymptotics.isBigO_self_const_mul** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_self_const_mul {c : S} (hc : c != 0) (f : α -> S) (l : Filter α) : 
f =O[l] fun x => c * f x
参数：hc : c != 0；f : α -> S；l : Filter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : F
ilter α}, Asymptoti…
· 使用定理 `Asymptotics.isBigOWith_self_const_mul`：isBigOWith_self_const_mul {c : S}
 (hc : c != 0) (f : α -> S) (l : Filter α) : IsBigOWith ‖c‖⁻¹ l f fun x => c * f
 x
-/
theorem isBigO_self_const_mul {c : S} (hc : c ≠ 0) (f : α → S) (l : Filter α) :
    f =O[l] fun x ↦ c * f x :=
  (isBigOWith_self_const_mul hc f l).isBigO
/-
**Asymptotics.isBigO_const_mul_left_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`
。
形式化陈述：isBigO_const_mul_left_iff' {f : α -> R} {c : R} (hc : IsUnit c) : (fun x =
> c * f x) =O[l] g ↔ f =O[l] g
参数：hc : IsUnit c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5}
 {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddComm
Group F'] {l :…
· 使用定理 `Asymptotics.isBigO_self_const_mul'`：isBigO_self_const_mul' {c : R} (hc :
 IsUnit c) (f : α -> R) (l : Filter α) : f =O[l] fun x => c * f x
· 使用定理 `Asymptotics.IsBigO.const_mul_left`：∀ {α : Type u_1} {F : Type u_4} {R : 
Type u_13} [inst : Norm F] [inst_1 : SeminormedRing R] {g : α → F} {l : Filter α
}   {f : α → R}, f =O[l…
-/
theorem isBigO_const_mul_left_iff' {f : α → R} {c : R} (hc : IsUnit c) :
    (fun x => c * f x) =O[l] g ↔ f =O[l] g :=
  ⟨(isBigO_self_const_mul' hc f l).trans, fun h => h.const_mul_left c⟩
/-
**Asymptotics.isBigO_const_mul_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_const_mul_left_iff {f : α -> S} {c : S} (hc : c != 0) : (fun x => c
 * f x) =O[l] g ↔ f =O[l] g
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5}
 {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddComm
Group F'] {l :…
· 使用定理 `Asymptotics.isBigO_self_const_mul`：isBigO_self_const_mul {c : S} (hc : c
 != 0) (f : α -> S) (l : Filter α) : f =O[l] fun x => c * f x
· 使用定理 `Asymptotics.isBigO_const_mul_self`：isBigO_const_mul_self (c : R) (f : α 
-> R) (l : Filter α) : (fun x => c * f x) =O[l] f
-/
theorem isBigO_const_mul_left_iff {f : α → S} {c : S} (hc : c ≠ 0) :
    (fun x => c * f x) =O[l] g ↔ f =O[l] g :=
  ⟨(isBigO_self_const_mul hc f l).trans, (isBigO_const_mul_self c f l).trans⟩
/-
**Asymptotics.IsLittleO.const_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.Is
LittleO`。
形式化陈述：∀ {α : Type u_1} {F : Type u_4} {R : Type u_13} [inst : Norm F] [inst_1 : 
SeminormedRing R] {g : α → F} {l : Filter α}   {f : α → R}, f =o[l] g → ∀ (c : R
), (fun x => c * f x) =o[l] g
参数：c : R；fun x => c * f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans_isLittleO`：∀ {α : Type u_1} {E : Type u_3} {G :
 Type u_5} {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : Seminor
medAddCommGroup F'] {l :…
· 使用定理 `Asymptotics.isBigO_const_mul_self`：isBigO_const_mul_self (c : R) (f : α 
-> R) (l : Filter α) : (fun x => c * f x) =O[l] f
-/
theorem IsLittleO.const_mul_left {f : α → R} (h : f =o[l] g) (c : R) : (fun x => c * f x) =o[l] g :=
  (isBigO_const_mul_self c f l).trans_isLittleO h
/-
**Asymptotics.isLittleO_const_mul_left_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Asymptoti
cs`。
形式化陈述：isLittleO_const_mul_left_iff' {f : α -> R} {c : R} (hc : IsUnit c) : (fun 
x => c * f x) =o[l] g ↔ f =o[l] g
参数：hc : IsUnit c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans_isLittleO`：∀ {α : Type u_1} {E : Type u_3} {G :
 Type u_5} {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : Seminor
medAddCommGroup F'] {l :…
· 使用定理 `Asymptotics.isBigO_self_const_mul'`：isBigO_self_const_mul' {c : R} (hc :
 IsUnit c) (f : α -> R) (l : Filter α) : f =O[l] fun x => c * f x
· 使用定理 `Asymptotics.IsLittleO.const_mul_left`：∀ {α : Type u_1} {F : Type u_4} {R
 : Type u_13} [inst : Norm F] [inst_1 : SeminormedRing R] {g : α → F} {l : Filte
r α}   {f : α → R}, f =o[l…
-/
theorem isLittleO_const_mul_left_iff' {f : α → R} {c : R} (hc : IsUnit c) :
    (fun x => c * f x) =o[l] g ↔ f =o[l] g :=
  ⟨(isBigO_self_const_mul' hc f l).trans_isLittleO, fun h => h.const_mul_left c⟩
/-
**Asymptotics.isLittleO_const_mul_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotic
s`。
形式化陈述：isLittleO_const_mul_left_iff {f : α -> S} {c : S} (hc : c != 0) : (fun x =
> c * f x) =o[l] g ↔ f =o[l] g
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans_isLittleO`：∀ {α : Type u_1} {E : Type u_3} {G :
 Type u_5} {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : Seminor
medAddCommGroup F'] {l :…
· 使用定理 `Asymptotics.isBigO_self_const_mul`：isBigO_self_const_mul {c : S} (hc : c
 != 0) (f : α -> S) (l : Filter α) : f =O[l] fun x => c * f x
· 使用定理 `Asymptotics.isBigO_const_mul_self`：isBigO_const_mul_self (c : R) (f : α 
-> R) (l : Filter α) : (fun x => c * f x) =O[l] f
-/
theorem isLittleO_const_mul_left_iff {f : α → S} {c : S} (hc : c ≠ 0) :
    (fun x => c * f x) =o[l] g ↔ f =o[l] g :=
  ⟨(isBigO_self_const_mul hc f l).trans_isLittleO, (isBigO_const_mul_self c f l).trans_isLittleO⟩
/-
**Asymptotics.IsBigOWith.of_const_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Asymptoti
cs.IsBigOWith`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {R : Type u_13} [inst : Norm E] [inst_1 : 
SeminormedRing R] {c' : ℝ} {f : α → E}   {l : Filter α} {g : α → R} {c : R},   0
 ≤ c' → (Asymptotics.IsBigOWith c' l f fun x => c * g x) → Asymptotics.IsBigOWit
h (c' * ‖c‖) l f g
参数：Asymptotics.IsBigOWith c' l f fun x => c * g x；c' * ‖c‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.trans`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} {G : Type u_5} [inst : Norm E] [inst_1 : Norm F] [inst_2 : Norm G]   {c c' 
: ℝ} {f : α → E} {…
· 使用定理 `Asymptotics.isBigOWith_const_mul_self`：isBigOWith_const_mul_self (c : R)
 (f : α -> R) (l : Filter α) : IsBigOWith ‖c‖ l (fun x => c * f x) f
-/
theorem IsBigOWith.of_const_mul_right {g : α → R} {c : R} (hc' : 0 ≤ c')
    (h : IsBigOWith c' l f fun x => c * g x) : IsBigOWith (c' * ‖c‖) l f g :=
  h.trans (isBigOWith_const_mul_self c g l) hc'
/-
**Asymptotics.IsBigO.of_const_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.I
sBigO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {R : Type u_13} [inst : Norm E] [inst_1 : 
SeminormedRing R] {f : α → E} {l : Filter α}   {g : α → R} {c : R}, (f =O[l] fun
 x => c * g x) → f =O[l] g
参数：f =O[l] fun x => c * g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.exists_nonneg`：∀ {α : Type u_1} {E : Type u_3} {F' : 
Type u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {f : α → E}   {g'
 : α → F'} {l : Filter…
· 使用定理 `Asymptotics.IsBigOWith.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : F
ilter α}, Asymptoti…
· 使用定理 `Asymptotics.IsBigOWith.of_const_mul_right`：∀ {α : Type u_1} {E : Type u_
3} {R : Type u_13} [inst : Norm E] [inst_1 : SeminormedRing R] {c' : ℝ} {f : α →
 E}   {l : Filter α} {g : α → R…
-/
theorem IsBigO.of_const_mul_right {g : α → R} {c : R} (h : f =O[l] fun x => c * g x) : f =O[l] g :=
  let ⟨_c, cnonneg, hc⟩ := h.exists_nonneg
  (hc.of_const_mul_right cnonneg).isBigO
/-
**Asymptotics.IsBigOWith.const_mul_right'** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics
.IsBigOWith`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {R : Type u_13} [inst : Norm E] [inst_1 : 
SeminormedRing R] {f : α → E} {l : Filter α}   {g : α → R} {u : Rˣ} {c' : ℝ},   
0 ≤ c' → Asymptotics.IsBigOWith c' l f g → Asymptotics.IsBigOWith (c' * ‖↑u⁻¹‖) 
l f fun x => ↑u * g x
参数：c' * ‖↑u⁻¹‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.trans`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} {G : Type u_5} [inst : Norm E] [inst_1 : Norm F] [inst_2 : Norm G]   {c c' 
: ℝ} {f : α → E} {…
· 使用定理 `Asymptotics.isBigOWith_self_const_mul'`：isBigOWith_self_const_mul' (u : 
Rˣ) (f : α -> R) (l : Filter α) : IsBigOWith ‖(↑u⁻¹ : R)‖ l f fun x => ↑u * f x
-/
theorem IsBigOWith.const_mul_right' {g : α → R} {u : Rˣ} {c' : ℝ} (hc' : 0 ≤ c')
    (h : IsBigOWith c' l f g) : IsBigOWith (c' * ‖(↑u⁻¹ : R)‖) l f fun x => ↑u * g x :=
  h.trans (isBigOWith_self_const_mul' _ _ _) hc'
/-
**Asymptotics.IsBigOWith.const_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.
IsBigOWith`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} [inst : Norm E] {S : Type u_17} [inst_1 : 
NormedRing S] [NormMulClass S] {f : α → E}   {l : Filter α} {g : α → S} {c : S},
   c ≠ 0 →     ∀ {c' : ℝ}, 0 ≤ c' → Asymptotics.IsBigOWith c' l f g → Asymptotic
s.IsBigOWith (c' * ‖c‖⁻¹) l f fun x => c * g x
参数：c' * ‖c‖⁻¹。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.trans`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} {G : Type u_5} [inst : Norm E] [inst_1 : Norm F] [inst_2 : Norm G]   {c c' 
: ℝ} {f : α → E} {…
· 使用定理 `Asymptotics.isBigOWith_self_const_mul`：isBigOWith_self_const_mul {c : S}
 (hc : c != 0) (f : α -> S) (l : Filter α) : IsBigOWith ‖c‖⁻¹ l f fun x => c * f
 x
-/
theorem IsBigOWith.const_mul_right {g : α → S} {c : S} (hc : c ≠ 0) {c' : ℝ} (hc' : 0 ≤ c')
    (h : IsBigOWith c' l f g) : IsBigOWith (c' * ‖c‖⁻¹) l f fun x => c * g x :=
  h.trans (isBigOWith_self_const_mul hc g l) hc'
/-
**Asymptotics.IsBigO.const_mul_right'** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsB
igO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {R : Type u_13} [inst : Norm E] [inst_1 : 
SeminormedRing R] {f : α → E} {l : Filter α}   {g : α → R} {c : R}, IsUnit c → f
 =O[l] g → f =O[l] fun x => c * g x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5}
 {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddComm
Group F'] {l :…
· 使用定理 `Asymptotics.isBigO_self_const_mul'`：isBigO_self_const_mul' {c : R} (hc :
 IsUnit c) (f : α -> R) (l : Filter α) : f =O[l] fun x => c * f x
-/
theorem IsBigO.const_mul_right' {g : α → R} {c : R} (hc : IsUnit c) (h : f =O[l] g) :
    f =O[l] fun x => c * g x :=
  h.trans (isBigO_self_const_mul' hc g l)
/-
**Asymptotics.IsBigO.const_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBi
gO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} [inst : Norm E] {S : Type u_17} [inst_1 : 
NormedRing S] [NormMulClass S] {f : α → E}   {l : Filter α} {g : α → S} {c : S},
 c ≠ 0 → f =O[l] g → f =O[l] fun x => c * g x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.exists_nonneg`：∀ {α : Type u_1} {E : Type u_3} {F' : 
Type u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {f : α → E}   {g'
 : α → F'} {l : Filter…
· 使用定理 `Asymptotics.IsBigOWith.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : F
ilter α}, Asymptoti…
· 使用定理 `Asymptotics.IsBigOWith.const_mul_right`：∀ {α : Type u_1} {E : Type u_3} 
[inst : Norm E] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S] {f : α 
→ E}   {l : Filter α} {g : α…
-/
theorem IsBigO.const_mul_right {g : α → S} {c : S} (hc : c ≠ 0) (h : f =O[l] g) :
    f =O[l] fun x => c * g x :=
  match h.exists_nonneg with
  | ⟨_, hd, hd'⟩ => (hd'.const_mul_right hc hd).isBigO
/-
**Asymptotics.isBigO_const_mul_right_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics
`。
形式化陈述：isBigO_const_mul_right_iff' {g : α -> R} {c : R} (hc : IsUnit c) : (f =O[l
] fun x => c * g x) ↔ f =O[l] g
参数：hc : IsUnit c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.of_const_mul_right`：∀ {α : Type u_1} {E : Type u_3} {
R : Type u_13} [inst : Norm E] [inst_1 : SeminormedRing R] {f : α → E} {l : Filt
er α}   {g : α → R} {c : R}…
· 使用定理 `Asymptotics.IsBigO.const_mul_right'`：∀ {α : Type u_1} {E : Type u_3} {R 
: Type u_13} [inst : Norm E] [inst_1 : SeminormedRing R] {f : α → E} {l : Filter
 α}   {g : α → R} {c : R}…
-/
theorem isBigO_const_mul_right_iff' {g : α → R} {c : R} (hc : IsUnit c) :
    (f =O[l] fun x => c * g x) ↔ f =O[l] g :=
  ⟨fun h => h.of_const_mul_right, fun h => h.const_mul_right' hc⟩
/-
**Asymptotics.isBigO_const_mul_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`
。
形式化陈述：isBigO_const_mul_right_iff {g : α -> S} {c : S} (hc : c != 0) : (f =O[l] f
un x => c * g x) ↔ f =O[l] g
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.of_const_mul_right`：∀ {α : Type u_1} {E : Type u_3} {
R : Type u_13} [inst : Norm E] [inst_1 : SeminormedRing R] {f : α → E} {l : Filt
er α}   {g : α → R} {c : R}…
· 使用定理 `Asymptotics.IsBigO.const_mul_right`：∀ {α : Type u_1} {E : Type u_3} [ins
t : Norm E] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S] {f : α → E}
   {l : Filter α} {g : α…
-/
theorem isBigO_const_mul_right_iff {g : α → S} {c : S} (hc : c ≠ 0) :
    (f =O[l] fun x => c * g x) ↔ f =O[l] g :=
  ⟨fun h ↦ h.of_const_mul_right, fun h ↦ h.const_mul_right hc⟩
/-
**Asymptotics.IsLittleO.of_const_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotic
s.IsLittleO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {R : Type u_13} [inst : Norm E] [inst_1 : 
SeminormedRing R] {f : α → E} {l : Filter α}   {g : α → R} {c : R}, (f =o[l] fun
 x => c * g x) → f =o[l] g
参数：f =o[l] fun x => c * g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.trans_isBigO`：∀ {α : Type u_1} {E : Type u_3} {F :
 Type u_4} {G' : Type u_8} [inst : Norm E] [inst_1 : Norm F]   [inst_2 : Seminor
medAddCommGroup G'] {l :…
· 使用定理 `Asymptotics.isBigO_const_mul_self`：isBigO_const_mul_self (c : R) (f : α 
-> R) (l : Filter α) : (fun x => c * f x) =O[l] f
-/
theorem IsLittleO.of_const_mul_right {g : α → R} {c : R} (h : f =o[l] fun x => c * g x) :
    f =o[l] g :=
  h.trans_isBigO (isBigO_const_mul_self c g l)
/-
**Asymptotics.IsLittleO.const_mul_right'** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.
IsLittleO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {R : Type u_13} [inst : Norm E] [inst_1 : 
SeminormedRing R] {f : α → E} {l : Filter α}   {g : α → R} {c : R}, IsUnit c → f
 =o[l] g → f =o[l] fun x => c * g x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.trans_isBigO`：∀ {α : Type u_1} {E : Type u_3} {F :
 Type u_4} {G' : Type u_8} [inst : Norm E] [inst_1 : Norm F]   [inst_2 : Seminor
medAddCommGroup G'] {l :…
· 使用定理 `Asymptotics.isBigO_self_const_mul'`：isBigO_self_const_mul' {c : R} (hc :
 IsUnit c) (f : α -> R) (l : Filter α) : f =O[l] fun x => c * f x
-/
theorem IsLittleO.const_mul_right' {g : α → R} {c : R} (hc : IsUnit c) (h : f =o[l] g) :
    f =o[l] fun x => c * g x :=
  h.trans_isBigO (isBigO_self_const_mul' hc g l)
/-
**Asymptotics.IsLittleO.const_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.I
sLittleO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} [inst : Norm E] {S : Type u_17} [inst_1 : 
NormedRing S] [NormMulClass S] {f : α → E}   {l : Filter α} {g : α → S} {c : S},
 c ≠ 0 → f =o[l] g → f =o[l] fun x => c * g x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.trans_isBigO`：∀ {α : Type u_1} {E : Type u_3} {F :
 Type u_4} {G' : Type u_8} [inst : Norm E] [inst_1 : Norm F]   [inst_2 : Seminor
medAddCommGroup G'] {l :…
· 使用定理 `Asymptotics.isBigO_self_const_mul`：isBigO_self_const_mul {c : S} (hc : c
 != 0) (f : α -> S) (l : Filter α) : f =O[l] fun x => c * f x
-/
theorem IsLittleO.const_mul_right {g : α → S} {c : S} (hc : c ≠ 0) (h : f =o[l] g) :
    f =o[l] fun x => c * g x :=
  h.trans_isBigO <| isBigO_self_const_mul hc g l
/-
**Asymptotics.isLittleO_const_mul_right_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Asymptot
ics`。
形式化陈述：isLittleO_const_mul_right_iff' {g : α -> R} {c : R} (hc : IsUnit c) : (f =
o[l] fun x => c * g x) ↔ f =o[l] g
参数：hc : IsUnit c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.of_const_mul_right`：∀ {α : Type u_1} {E : Type u_3
} {R : Type u_13} [inst : Norm E] [inst_1 : SeminormedRing R] {f : α → E} {l : F
ilter α}   {g : α → R} {c : R}…
· 使用定理 `Asymptotics.IsLittleO.const_mul_right'`：∀ {α : Type u_1} {E : Type u_3} 
{R : Type u_13} [inst : Norm E] [inst_1 : SeminormedRing R] {f : α → E} {l : Fil
ter α}   {g : α → R} {c : R}…
-/
theorem isLittleO_const_mul_right_iff' {g : α → R} {c : R} (hc : IsUnit c) :
    (f =o[l] fun x => c * g x) ↔ f =o[l] g :=
  ⟨fun h => h.of_const_mul_right, fun h => h.const_mul_right' hc⟩
/-
**Asymptotics.isLittleO_const_mul_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `Asymptoti
cs`。
形式化陈述：isLittleO_const_mul_right_iff {g : α -> S} {c : S} (hc : c != 0) : (f =o[l
] fun x => c * g x) ↔ f =o[l] g
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.of_const_mul_right`：∀ {α : Type u_1} {E : Type u_3
} {R : Type u_13} [inst : Norm E] [inst_1 : SeminormedRing R] {f : α → E} {l : F
ilter α}   {g : α → R} {c : R}…
· 使用定理 `Asymptotics.IsLittleO.trans_isBigO`：∀ {α : Type u_1} {E : Type u_3} {F :
 Type u_4} {G' : Type u_8} [inst : Norm E] [inst_1 : Norm F]   [inst_2 : Seminor
medAddCommGroup G'] {l :…
· 使用定理 `Asymptotics.isBigO_self_const_mul`：isBigO_self_const_mul {c : S} (hc : c
 != 0) (f : α -> S) (l : Filter α) : f =O[l] fun x => c * f x
-/
theorem isLittleO_const_mul_right_iff {g : α → S} {c : S} (hc : c ≠ 0) :
    (f =o[l] fun x => c * g x) ↔ f =o[l] g :=
  ⟨fun h ↦ h.of_const_mul_right, fun h ↦ h.trans_isBigO (isBigO_self_const_mul hc g l)⟩

/-! ### Multiplication -/

/-
**Asymptotics.IsBigOWith.mul** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigOWith`。
形式化陈述：∀ {α : Type u_1} {R : Type u_13} [inst : SeminormedRing R] {S : Type u_17}
 [inst_1 : NormedRing S] [NormMulClass S]   {l : Filter α} {f₁ f₂ : α → R} {g₁ g
₂ : α → S} {c₁ c₂ : ℝ},   Asymptotics.IsBigOWith c₁ l f₁ g₁ →     Asymptotics.Is
BigOWith c₂ l f₂ g₂ → Asymptotics.IsBigOWith (c₁ * c₂) l (fun x => f₁ x * f₂ x) 
fun x => g₁ x * g₂ x
参数：c₁ * c₂；fun x => f₁ x * f₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type 
u_20} [inst : Norm E] [inst_1 : Norm F] (c : ℝ) (l : Filter α) (f : α → E)   (g 
: α → F), Asympt…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `norm_mul_le`：norm_mul_le (a b : α) : ‖a * b‖ <= ‖a‖ * ‖b‖
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖

--- 原说明 ---
### Multiplication
-/
theorem IsBigOWith.mul {f₁ f₂ : α → R} {g₁ g₂ : α → S} {c₁ c₂ : ℝ} (h₁ : IsBigOWith c₁ l f₁ g₁)
    (h₂ : IsBigOWith c₂ l f₂ g₂) :
    IsBigOWith (c₁ * c₂) l (fun x => f₁ x * f₂ x) fun x => g₁ x * g₂ x := by
  simp only [IsBigOWith_def] at *
  filter_upwards [h₁, h₂] with _ hx₁ hx₂
  apply le_trans (norm_mul_le _ _)
  convert! mul_le_mul hx₁ hx₂ (norm_nonneg _) (le_trans (norm_nonneg _) hx₁) using 1
  rw [norm_mul, mul_mul_mul_comm]
/-
**Asymptotics.IsBigO.mul** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`。
形式化陈述：∀ {α : Type u_1} {R : Type u_13} [inst : SeminormedRing R] {S : Type u_17}
 [inst_1 : NormedRing S] [NormMulClass S]   {l : Filter α} {f₁ f₂ : α → R} {g₁ g
₂ : α → S},   f₁ =O[l] g₁ → f₂ =O[l] g₂ → (fun x => f₁ x * f₂ x) =O[l] fun x => 
g₁ x * g₂ x
参数：fun x => f₁ x * f₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.isBigOWith`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α}, 
  f =O[l] g → ∃ c, …
· 使用定理 `Asymptotics.IsBigOWith.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : F
ilter α}, Asymptoti…
· 使用定理 `Asymptotics.IsBigOWith.mul`：∀ {α : Type u_1} {R : Type u_13} [inst : Sem
inormedRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   {l : F
ilter α} {f₁ f₂ …
-/
theorem IsBigO.mul {f₁ f₂ : α → R} {g₁ g₂ : α → S} (h₁ : f₁ =O[l] g₁) (h₂ : f₂ =O[l] g₂) :
    (fun x => f₁ x * f₂ x) =O[l] fun x => g₁ x * g₂ x :=
  let ⟨_c, hc⟩ := h₁.isBigOWith
  let ⟨_c', hc'⟩ := h₂.isBigOWith
  (hc.mul hc').isBigO
/-
**Asymptotics.IsBigO.mul_isLittleO** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO
`。
形式化陈述：∀ {α : Type u_1} {R : Type u_13} [inst : SeminormedRing R] {S : Type u_17}
 [inst_1 : NormedRing S] [NormMulClass S]   {l : Filter α} {f₁ f₂ : α → R} {g₁ g
₂ : α → S},   f₁ =O[l] g₁ → f₂ =o[l] g₂ → (fun x => f₁ x * f₂ x) =o[l] fun x => 
g₁ x * g₂ x
参数：fun x => f₁ x * f₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type u
_20} [inst : Norm E] [inst_1 : Norm F] (l : Filter α) (f : α → E)   (g : α → F),
 f =o[l] g = ∀ …
· 使用定理 `Asymptotics.IsBigO.exists_pos`：∀ {α : Type u_1} {E : Type u_3} {F' : Typ
e u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {f : α → E}   {g' : 
α → F'} {l : Filter…
· 使用定理 `Asymptotics.IsBigOWith.congr_const`：∀ {α : Type u_1} {E : Type u_3} {F :
 Type u_4} [inst : Norm E] [inst_1 : Norm F] {c₁ c₂ : ℝ} {f : α → E} {g : α → F}
   {l : Filter α}, Asymp…
· 使用定理 `Asymptotics.IsBigOWith.mul`：∀ {α : Type u_1} {R : Type u_13} [inst : Sem
inormedRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   {l : F
ilter α} {f₁ f₂ …
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `mul_div_cancel₀`：mul_div_cancel₀ (a : G₀) (hb : b != 0) : b * (a / b) = 
a
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem IsBigO.mul_isLittleO {f₁ f₂ : α → R} {g₁ g₂ : α → S} (h₁ : f₁ =O[l] g₁) (h₂ : f₂ =o[l] g₂) :
    (fun x => f₁ x * f₂ x) =o[l] fun x => g₁ x * g₂ x := by
  simp only [IsLittleO_def] at *
  intro c cpos
  rcases h₁.exists_pos with ⟨c', c'pos, hc'⟩
  exact (hc'.mul (h₂ (div_pos cpos c'pos))).congr_const (mul_div_cancel₀ _ (ne_of_gt c'pos))
/-
**Asymptotics.IsLittleO.mul_isBigO** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLitt
leO`。
形式化陈述：∀ {α : Type u_1} {R : Type u_13} [inst : SeminormedRing R] {S : Type u_17}
 [inst_1 : NormedRing S] [NormMulClass S]   {l : Filter α} {f₁ f₂ : α → R} {g₁ g
₂ : α → S},   f₁ =o[l] g₁ → f₂ =O[l] g₂ → (fun x => f₁ x * f₂ x) =o[l] fun x => 
g₁ x * g₂ x
参数：fun x => f₁ x * f₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type u
_20} [inst : Norm E] [inst_1 : Norm F] (l : Filter α) (f : α → E)   (g : α → F),
 f =o[l] g = ∀ …
· 使用定理 `Asymptotics.IsBigO.exists_pos`：∀ {α : Type u_1} {E : Type u_3} {F' : Typ
e u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {f : α → E}   {g' : 
α → F'} {l : Filter…
· 使用定理 `Asymptotics.IsBigOWith.congr_const`：∀ {α : Type u_1} {E : Type u_3} {F :
 Type u_4} [inst : Norm E] [inst_1 : Norm F] {c₁ c₂ : ℝ} {f : α → E} {g : α → F}
   {l : Filter α}, Asymp…
· 使用定理 `Asymptotics.IsBigOWith.mul`：∀ {α : Type u_1} {R : Type u_13} [inst : Sem
inormedRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   {l : F
ilter α} {f₁ f₂ …
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem IsLittleO.mul_isBigO {f₁ f₂ : α → R} {g₁ g₂ : α → S} (h₁ : f₁ =o[l] g₁) (h₂ : f₂ =O[l] g₂) :
    (fun x ↦ f₁ x * f₂ x) =o[l] fun x ↦ g₁ x * g₂ x := by
  simp only [IsLittleO_def] at *
  intro c cpos
  rcases h₂.exists_pos with ⟨c', c'pos, hc'⟩
  exact ((h₁ (div_pos cpos c'pos)).mul hc').congr_const (div_mul_cancel₀ _ (ne_of_gt c'pos))
/-
**Asymptotics.IsLittleO.mul** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLittleO`。
形式化陈述：∀ {α : Type u_1} {R : Type u_13} [inst : SeminormedRing R] {S : Type u_17}
 [inst_1 : NormedRing S] [NormMulClass S]   {l : Filter α} {f₁ f₂ : α → R} {g₁ g
₂ : α → S},   f₁ =o[l] g₁ → f₂ =o[l] g₂ → (fun x => f₁ x * f₂ x) =o[l] fun x => 
g₁ x * g₂ x
参数：fun x => f₁ x * f₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.mul_isBigO`：∀ {α : Type u_1} {R : Type u_13} [inst
 : SeminormedRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   
{l : Filter α} {f₁ f₂ …
· 使用定理 `Asymptotics.IsLittleO.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},  
 f =o[l] g → f =O[…
-/
theorem IsLittleO.mul {f₁ f₂ : α → R} {g₁ g₂ : α → S} (h₁ : f₁ =o[l] g₁) (h₂ : f₂ =o[l] g₂) :
    (fun x ↦ f₁ x * f₂ x) =o[l] fun x ↦ g₁ x * g₂ x :=
  h₁.mul_isBigO h₂.isBigO
/-
**Asymptotics.IsBigOWith.pow'** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigOWith`
。
形式化陈述：∀ {α : Type u_1} {R : Type u_13} [inst : SeminormedRing R] {S : Type u_17}
 [inst_1 : NormedRing S] [NormMulClass S]   {c : ℝ} {l : Filter α} [NormOneClass
 S] {f : α → R} {g : α → S},   Asymptotics.IsBigOWith c l f g →     ∀ (n : ℕ), A
symptotics.IsBigOWith (Nat.casesOn n ‖1‖ fun n => c ^ (n + 1)) l (fun x => f x ^
 n) fun x => g x ^ n
参数：n : ℕ；Nat.casesOn n ‖1‖ fun n => c ^ (n + 1)；fun x => f x ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsBigOWith.pow' [NormOneClass S] {f : α → R} {g : α → S} (h : IsBigOWith c l f g) :
    ∀ n : ℕ, IsBigOWith (Nat.casesOn n ‖(1 : R)‖ fun n ↦ c ^ (n + 1))
      l (fun x => f x ^ n) fun x => g x ^ n
  | 0 => by
    have : Nontrivial S := NormOneClass.nontrivial
    simpa using isBigOWith_const_const (1 : R) (one_ne_zero' S) l
  | 1 => by simpa
  | n + 2 => by simpa [pow_succ] using (IsBigOWith.pow' h (n + 1)).mul h
/-
**Asymptotics.IsBigOWith.pow** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigOWith`。
形式化陈述：∀ {α : Type u_1} {R : Type u_13} [inst : SeminormedRing R] {S : Type u_17}
 [inst_1 : NormedRing S] [NormMulClass S]   {c : ℝ} {l : Filter α} [NormOneClass
 R] [NormOneClass S] {f : α → R} {g : α → S},   Asymptotics.IsBigOWith c l f g →
 ∀ (n : ℕ), Asymptotics.IsBigOWith (c ^ n) l (fun x => f x ^ n) fun x => g x ^ n
参数：n : ℕ；c ^ n；fun x => f x ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `Asymptotics.IsBigOWith.pow'`：∀ {α : Type u_1} {R : Type u_13} [inst : Se
minormedRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   {c : 
ℝ} {l : Filter α}…
-/
theorem IsBigOWith.pow [NormOneClass R] [NormOneClass S]
    {f : α → R} {g : α → S} (h : IsBigOWith c l f g) :
    ∀ n : ℕ, IsBigOWith (c ^ n) l (fun x => f x ^ n) fun x => g x ^ n
  | 0 => by simpa using h.pow' 0
  | n + 1 => h.pow' (n + 1)
/-
**Asymptotics.IsBigOWith.of_pow** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigOWit
h`。
形式化陈述：∀ {α : Type u_1} {R : Type u_13} [inst : SeminormedRing R] {S : Type u_17}
 [inst_1 : NormedRing S] [NormMulClass S]   {c c' : ℝ} {l : Filter α} [NormOneCl
ass S] {n : ℕ} {f : α → S} {g : α → R},   Asymptotics.IsBigOWith c l (f ^ n) (g 
^ n) → n ≠ 0 → c ≤ c' ^ n → 0 ≤ c' → Asymptotics.IsBigOWith c' l f g
参数：f ^ n；g ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.of_bound`：∀ {α : Type u_1} {E : Type u_3} {F : Ty
pe u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l :
 Filter α}, (∀ᶠ (x : …
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Asymptotics.IsBigOWith.bound`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : Fi
lter α}, Asymptoti…
· 使用定理 `Asymptotics.IsBigOWith.weaken`：∀ {α : Type u_1} {E : Type u_3} {F' : Typ
e u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {c c' : ℝ}   {f : α 
→ E} {g' : α → F'} …
· 使用引理 `le_of_pow_le_pow_left₀`：le_of_pow_le_pow_left₀ (hn : n != 0) (hb : 0 <= 
b) (h : a ^ n <= b ^ n) : a <= b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `norm_pow_le'`：norm_pow_le' (a : α) {n : Nat} (h : 0 < n) : ‖a ^ n‖ <= ‖a
‖ ^ n
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
-/
theorem IsBigOWith.of_pow [NormOneClass S] {n : ℕ} {f : α → S} {g : α → R}
    (h : IsBigOWith c l (f ^ n) (g ^ n)) (hn : n ≠ 0) (hc : c ≤ c' ^ n) (hc' : 0 ≤ c') :
    IsBigOWith c' l f g :=
  IsBigOWith.of_bound <| (h.weaken hc).bound.mono fun x hx ↦
    le_of_pow_le_pow_left₀ hn (by positivity) <|
      calc
        ‖f x‖ ^ n = ‖f x ^ n‖ := (norm_pow _ _).symm
        _ ≤ c' ^ n * ‖g x ^ n‖ := hx
        _ ≤ c' ^ n * ‖g x‖ ^ n := by gcongr; exact norm_pow_le' _ hn.bot_lt
        _ = (c' * ‖g x‖) ^ n := (mul_pow _ _ _).symm
/-
**Asymptotics.IsBigO.pow** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`。
形式化陈述：∀ {α : Type u_1} {R : Type u_13} [inst : SeminormedRing R] {S : Type u_17}
 [inst_1 : NormedRing S] [NormMulClass S]   {l : Filter α} [NormOneClass S] {f :
 α → R} {g : α → S},   f =O[l] g → ∀ (n : ℕ), (fun x => f x ^ n) =O[l] fun x => 
g x ^ n
参数：n : ℕ；fun x => f x ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.isBigOWith`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α}, 
  f =O[l] g → ∃ c, …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Asymptotics.isBigO_iff_isBigOWith`：isBigO_iff_isBigOWith : f =O[l] g ↔ e
xists c : Real, IsBigOWith c l f g
· 使用定理 `Asymptotics.IsBigOWith.pow'`：∀ {α : Type u_1} {R : Type u_13} [inst : Se
minormedRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   {c : 
ℝ} {l : Filter α}…
-/
theorem IsBigO.pow [NormOneClass S] {f : α → R} {g : α → S} (h : f =O[l] g) (n : ℕ) :
    (fun x => f x ^ n) =O[l] fun x => g x ^ n :=
  let ⟨_C, hC⟩ := h.isBigOWith
  isBigO_iff_isBigOWith.2 ⟨_, hC.pow' n⟩
/-
**Asymptotics.IsLittleO.pow** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLittleO`。
形式化陈述：∀ {α : Type u_1} {R : Type u_13} [inst : SeminormedRing R] {S : Type u_17}
 [inst_1 : NormedRing S] [NormMulClass S]   {l : Filter α} {f : α → R} {g : α → 
S}, f =o[l] g → ∀ {n : ℕ}, 0 < n → (fun x => f x ^ n) =o[l] fun x => g x ^ n
参数：fun x => f x ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_succ_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k.succ
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Asymptotics.IsLittleO.mul`：∀ {α : Type u_1} {R : Type u_13} [inst : Semi
normedRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   {l : Fi
lter α} {f₁ f₂ …
-/
theorem IsLittleO.pow {f : α → R} {g : α → S} (h : f =o[l] g) {n : ℕ} (hn : 0 < n) :
    (fun x => f x ^ n) =o[l] fun x => g x ^ n := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'; clear hn
  induction n with
  | zero => simpa only [pow_one]
  | succ n ihn => convert! ihn.mul h <;> simp [pow_succ]
/-
**Asymptotics.IsLittleO.of_pow** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLittleO`
。
形式化陈述：∀ {α : Type u_1} {R : Type u_13} [inst : SeminormedRing R] {S : Type u_17}
 [inst_1 : NormedRing S] [NormMulClass S]   {l : Filter α} [NormOneClass S] {f :
 α → S} {g : α → R} {n : ℕ}, (f ^ n) =o[l] (g ^ n) → n ≠ 0 → f =o[l] g
参数：f ^ n；g ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.of_isBigOWith`：∀ {α : Type u_1} {E : Type u_3} {F 
: Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filte
r α},   (∀ ⦃c : ℝ⦄, 0 < c…
· 使用定理 `Asymptotics.IsBigOWith.of_pow`：∀ {α : Type u_1} {R : Type u_13} [inst : 
SeminormedRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   {c 
c' : ℝ} {l : Filter…
· 使用定理 `Asymptotics.IsLittleO.def'`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_
4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : Filt
er α}, f =o[l] g…
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem IsLittleO.of_pow [NormOneClass S] {f : α → S} {g : α → R} {n : ℕ}
    (h : (f ^ n) =o[l] (g ^ n)) (hn : n ≠ 0) : f =o[l] g :=
  IsLittleO.of_isBigOWith fun _c hc => (h.def' <| pow_pos hc _).of_pow hn le_rfl hc.le

/-! ### Inverse -/

/-
**Asymptotics.IsBigOWith.inv_rev** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigOWi
th`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_15} {𝕜' : Type u_16} [inst : NormedDivisionRi
ng 𝕜] [inst_1 : NormedDivisionRing 𝕜'] {c : ℝ}   {l : Filter α} {f : α → 𝕜} {g :
 α → 𝕜'},   Asymptotics.IsBigOWith c l f g →     (∀ᶠ (x : α) in l, f x = 0 → g x
 = 0) → Asymptotics.IsBigOWith c l (fun x => (g x)⁻¹) fun x => (f x)⁻¹
参数：∀ᶠ (x : α) in l, f x = 0 → g x = 0；fun x => (g x)⁻¹；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.of_bound`：∀ {α : Type u_1} {E : Type u_3} {F : Ty
pe u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l :
 Filter α}, (∀ᶠ (x : …
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Asymptotics.IsBigOWith.bound`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : Fi
lter α}, Asymptoti…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `pos_of_mul_pos_left`：pos_of_mul_pos_left [MulPosReflectLT α] (h : 0 < a 
* b) (hb : 0 <= b) : 0 < a
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `inv_anti₀`：inv_anti₀ (hb : 0 < b) (hba : b <= a) : a⁻¹ <= b⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_inv`：mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹
· 使用引理 `div_le_iff₀`：div_le_iff₀ (hc : 0 < c) : b / c <= a ↔ b <= a * c

--- 原说明 ---
### Inverse
-/
theorem IsBigOWith.inv_rev {f : α → 𝕜} {g : α → 𝕜'} (h : IsBigOWith c l f g)
    (h₀ : ∀ᶠ x in l, f x = 0 → g x = 0) : IsBigOWith c l (fun x => (g x)⁻¹) fun x => (f x)⁻¹ := by
  refine IsBigOWith.of_bound (h.bound.mp (h₀.mono fun x h₀ hle => ?_))
  rcases eq_or_ne (f x) 0 with hx | hx
  · simp only [hx, h₀ hx, inv_zero, norm_zero, mul_zero, le_rfl]
  · have hc : 0 < c := pos_of_mul_pos_left ((norm_pos_iff.2 hx).trans_le hle) (norm_nonneg _)
    replace hle := inv_anti₀ (norm_pos_iff.2 hx) hle
    simpa only [norm_inv, mul_inv, ← div_eq_inv_mul, div_le_iff₀ hc] using! hle
/-
**Asymptotics.IsBigO.inv_rev** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_15} {𝕜' : Type u_16} [inst : NormedDivisionRi
ng 𝕜] [inst_1 : NormedDivisionRing 𝕜']   {l : Filter α} {f : α → 𝕜} {g : α → 𝕜'}
,   f =O[l] g → (∀ᶠ (x : α) in l, f x = 0 → g x = 0) → (fun x => (g x)⁻¹) =O[l] 
fun x => (f x)⁻¹
参数：∀ᶠ (x : α) in l, f x = 0 → g x = 0；fun x => (g x)⁻¹；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.isBigOWith`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α}, 
  f =O[l] g → ∃ c, …
· 使用定理 `Asymptotics.IsBigOWith.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : F
ilter α}, Asymptoti…
· 使用定理 `Asymptotics.IsBigOWith.inv_rev`：∀ {α : Type u_1} {𝕜 : Type u_15} {𝕜' : T
ype u_16} [inst : NormedDivisionRing 𝕜] [inst_1 : NormedDivisionRing 𝕜'] {c : ℝ}
   {l : Filter α} {f…
-/
theorem IsBigO.inv_rev {f : α → 𝕜} {g : α → 𝕜'} (h : f =O[l] g)
    (h₀ : ∀ᶠ x in l, f x = 0 → g x = 0) : (fun x => (g x)⁻¹) =O[l] fun x => (f x)⁻¹ :=
  let ⟨_c, hc⟩ := h.isBigOWith
  (hc.inv_rev h₀).isBigO
/-
**Asymptotics.IsLittleO.inv_rev** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLittleO
`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_15} {𝕜' : Type u_16} [inst : NormedDivisionRi
ng 𝕜] [inst_1 : NormedDivisionRing 𝕜']   {l : Filter α} {f : α → 𝕜} {g : α → 𝕜'}
,   f =o[l] g → (∀ᶠ (x : α) in l, f x = 0 → g x = 0) → (fun x => (g x)⁻¹) =o[l] 
fun x => (f x)⁻¹
参数：∀ᶠ (x : α) in l, f x = 0 → g x = 0；fun x => (g x)⁻¹；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.of_isBigOWith`：∀ {α : Type u_1} {E : Type u_3} {F 
: Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filte
r α},   (∀ ⦃c : ℝ⦄, 0 < c…
· 使用定理 `Asymptotics.IsBigOWith.inv_rev`：∀ {α : Type u_1} {𝕜 : Type u_15} {𝕜' : T
ype u_16} [inst : NormedDivisionRing 𝕜] [inst_1 : NormedDivisionRing 𝕜'] {c : ℝ}
   {l : Filter α} {f…
· 使用定理 `Asymptotics.IsLittleO.def'`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_
4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : Filt
er α}, f =o[l] g…
-/
theorem IsLittleO.inv_rev {f : α → 𝕜} {g : α → 𝕜'} (h : f =o[l] g)
    (h₀ : ∀ᶠ x in l, f x = 0 → g x = 0) : (fun x => (g x)⁻¹) =o[l] fun x => (f x)⁻¹ :=
  IsLittleO.of_isBigOWith fun _c hc => (h.def' hc).inv_rev h₀

/-! ### Sum -/

section Sum

variable {ι : Type*} {A : ι → α → E'} {C : ι → ℝ} {s : Finset ι}

/-
**Asymptotics.IsBigOWith.sum** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigOWith`。
形式化陈述：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} [inst : Norm F] [inst_1 : 
SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α} {ι : Type u_18} {A : ι →
 α → E'} {C : ι → ℝ} {s : Finset ι},   (∀ i ∈ s, Asymptotics.IsBigOWith (C i) l 
(A i) g) → Asymptotics.IsBigOWith (∑ i ∈ s, C i) l (∑ i ∈ s, A i) g
参数：∀ i ∈ s, Asymptotics.IsBigOWith (C i) l (A i) g；∑ i ∈ s, C i；∑ i ∈ s, A i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_empty`：∀ {ι : Type u_1} {M : Type u_3} {f : ι → M} [inst : Ad
dCommMonoid M], ∑ x ∈ ∅, f x = 0
· 使用定理 `Asymptotics.isBigOWith_zero'`：isBigOWith_zero' : IsBigOWith 0 l (fun _x 
=> (0 : E')) g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `Asymptotics.IsBigOWith.add`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u
_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {c₁ c₂ : ℝ}   {g : α → 
F} {l : Filter α…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
@[to_fun] theorem IsBigOWith.sum (h : ∀ i ∈ s, IsBigOWith (C i) l (A i) g) :
    IsBigOWith (∑ i ∈ s, C i) l (∑ i ∈ s, A i) g := by
  induction s using Finset.cons_induction with
  | empty =>
      rw [Finset.sum_empty]
      apply isBigOWith_zero'
  | cons i s is IH =>
    simp only [Finset.sum_cons, Finset.forall_mem_cons] at h ⊢
    exact h.1.add (IH h.2)
/-
**Asymptotics.IsBigO.sum** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`。
形式化陈述：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} [inst : Norm F] [inst_1 : 
SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α} {ι : Type u_18} {A : ι →
 α → E'} {s : Finset ι}, (∀ i ∈ s, A i =O[l] g) → (∑ i ∈ s, A i) =O[l] g
参数：∀ i ∈ s, A i =O[l] g；∑ i ∈ s, A i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type u_20
} [inst : Norm E] [inst_1 : Norm F] (l : Filter α) (f : α → E)   (g : α → F), f 
=O[l] g = ∃ …
· 使用定理 `Asymptotics.IsBigOWith.sum`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u
_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filt
er α} {ι : Type …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Function.sometimes_spec`：sometimes_spec {p : Prop} {α} [Nonempty α] (P :
 α -> Prop) (f : p -> α) (a : p) (h : P (f a)) : P (sometimes f)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
@[to_fun] theorem IsBigO.sum (h : ∀ i ∈ s, A i =O[l] g) : (∑ i ∈ s, A i) =O[l] g := by
  simp only [IsBigO_def] at *
  choose! C hC using h
  exact ⟨_, IsBigOWith.sum hC⟩
/-
**Asymptotics.IsLittleO.sum** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLittleO`。
形式化陈述：∀ {α : Type u_1} {E' : Type u_6} {F' : Type u_7} [inst : SeminormedAddComm
Group E'] [inst_1 : SeminormedAddCommGroup F']   {g' : α → F'} {l : Filter α} {ι
 : Type u_18} {A : ι → α → E'} {s : Finset ι},   (∀ i ∈ s, A i =o[l] g') → (∑ i 
∈ s, A i) =o[l] g'
参数：∀ i ∈ s, A i =o[l] g'；∑ i ∈ s, A i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_induction`：∀ {ι : Type u_1} {s : Finset ι} {M : Type u_7} [in
st : AddCommMonoid M] (f : ι → M) (p : M → Prop),   (∀ (a b : M), p a → p b → p 
(a + b)) →…
· 使用定理 `Asymptotics.IsLittleO.add`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_
6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filte
r α} {f₁ f₂ : α…
· 使用定理 `Asymptotics.isLittleO_zero`：isLittleO_zero : (fun _x => (0 : E')) =o[l] 
g'
-/
@[to_fun] theorem IsLittleO.sum (h : ∀ i ∈ s, A i =o[l] g') : (∑ i ∈ s, A i) =o[l] g' := by
  exact Finset.sum_induction A (· =o[l] g') (fun _ _ ↦ .add) (isLittleO_zero ..) h

variable {B : ι → α → ℝ}

/-- If each term `A i` of a sum `IsBigO` of `B i`, then the sum of the `A i` `IsBigO` of the sum
of the norms of the `B i`. -/
/-
**Asymptotics.IsBigOWith.sum_congr** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO
With`。
形式化陈述：∀ {α : Type u_1} {E' : Type u_6} [inst : SeminormedAddCommGroup E'] {l : F
ilter α} {ι : Type u_18} {A : ι → α → E'}   {C : ι → ℝ} {s : Finset ι} {B : ι → 
α → ℝ},   (∀ i ∈ s, Asymptotics.IsBigOWith (C i) l (A i) (B i)) →     Asymptotic
s.IsBigOWith (sSup (C '' ↑s)) l (fun H => ∑ i ∈ s, A i H) fun H => ∑ i ∈ s, ‖B i
 H‖
参数：∀ i ∈ s, Asymptotics.IsBigOWith (C i) l (A i) (B i)；sSup (C '' ↑s)；fun H => ∑
 i ∈ s, A i H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `Real.sSup_empty`：sSup_empty : sSup (∅ : Set Real) = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Asymptotics.IsBigOWith_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type 
u_20} [inst : Norm E] [inst_1 : Norm F] (c : ℝ) (l : Filter α) (f : α → E)   (g 
: α → F), Asympt…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_all_finset`：∀ {α : Type u} {ι : Type u_2} (I : Finset 
ι) {l : Filter α} {p : ι → α → Prop},   (∀ᶠ (x : α) in l, ∀ i ∈ I, p i x) ↔ ∀ i 
∈ I, ∀ᶠ (x : α) in…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `norm_sum_le`：norm_sum_le {E} [SeminormedAddCommGroup E] (s : Finset ι) (
f : ι -> E) : ‖∑ i in s, f i‖ <= ∑ i in s, ‖f i‖
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.sup'_eq_csSup_image`：∀ {ι : Type u_1} {α : Type u_2} [inst : Cond
itionallyCompleteLattice α] (s : Finset ι) (H : s.Nonempty) (f : ι → α),   s.sup
' H f = sSup (f …
· 使用定理 `Finset.le_sup'_iff`：∀ {α : Type u_2} {ι : Type u_5} [inst : LinearOrder 
α] {s : Finset ι} (H : s.Nonempty) {f : ι → α} {a : α},   a ≤ s.sup' H f ↔ ∃ b ∈
 s, a ≤ …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
If each term `A i` of a sum `IsBigO` of `B i`, then the sum of the `A i` `IsBigO
` of the sum
of the norms of the `B i`.
-/
theorem IsBigOWith.sum_congr
    (hAB : ∀ i ∈ s, IsBigOWith (C i) l (A i) (B i)) :
    IsBigOWith (sSup (C '' s)) l (fun H ↦ ∑ i ∈ s, A i H) (fun H ↦ ∑ i ∈ s, ‖B i H‖) := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp [isBigOWith_zero]
  simp only [IsBigOWith_def] at *
  filter_upwards [(eventually_all_finset s).mpr hAB]
    with x hx
  calc
    ‖∑ i ∈ s, A i x‖ ≤ ∑ i ∈ s, ‖A i x‖ := norm_sum_le ..
    _ ≤ ∑ i ∈ s, C i * ‖B i x‖ := Finset.sum_le_sum (fun j hj ↦ hx j hj)
    _ ≤ ∑ i ∈ s, sSup (C '' s) * ‖B i x‖ := by
        refine Finset.sum_le_sum ?_
        intro j hj; gcongr
        rw [← s.sup'_eq_csSup_image hs, Finset.le_sup'_iff]; use j
    _ = sSup (C '' s) * ∑ i ∈ s, ‖B i x‖ := (Finset.mul_sum ..).symm
    _ = sSup (C '' s) * ‖∑ i ∈ s, ‖B i x‖‖ := by
      congr; rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))]
/-
**Asymptotics.IsBigO.sum_congr** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`。
形式化陈述：∀ {α : Type u_1} {E' : Type u_6} [inst : SeminormedAddCommGroup E'] {l : F
ilter α} {ι : Type u_18} {A : ι → α → E'}   {s : Finset ι} {B : ι → α → ℝ}, (∀ i
 ∈ s, A i =O[l] B i) → (fun H => ∑ i ∈ s, A i H) =O[l] fun H => ∑ i ∈ s, ‖B i H‖
参数：∀ i ∈ s, A i =O[l] B i；fun H => ∑ i ∈ s, A i H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type u_20
} [inst : Norm E] [inst_1 : Norm F] (l : Filter α) (f : α → E)   (g : α → F), f 
=O[l] g = ∃ …
· 使用定理 `Asymptotics.IsBigOWith.sum_congr`：∀ {α : Type u_1} {E' : Type u_6} [inst
 : SeminormedAddCommGroup E'] {l : Filter α} {ι : Type u_18} {A : ι → α → E'}   
{C : ι → ℝ} {s : Finse…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Function.sometimes_spec`：sometimes_spec {p : Prop} {α} [Nonempty α] (P :
 α -> Prop) (f : p -> α) (a : p) (h : P (f a)) : P (sometimes f)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem IsBigO.sum_congr (hAB : ∀ i ∈ s, A i =O[l] B i) :
    (fun H => ∑ i ∈ s, A i H) =O[l] fun H => ∑ i ∈ s, ‖B i H‖ := by
  simp only [IsBigO_def] at *
  choose! C hC using hAB
  exact ⟨_, IsBigOWith.sum_congr hC⟩
/-
**Asymptotics.IsLittleO.sum_congr** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLittl
eO`。
形式化陈述：∀ {α : Type u_1} {E' : Type u_6} [inst : SeminormedAddCommGroup E'] {l : F
ilter α} {ι : Type u_18} {A : ι → α → E'}   {s : Finset ι} {B : ι → α → ℝ}, (∀ i
 ∈ s, A i =o[l] B i) → (fun H => ∑ i ∈ s, A i H) =o[l] fun H => ∑ i ∈ s, ‖B i H‖
参数：∀ i ∈ s, A i =o[l] B i；fun H => ∑ i ∈ s, A i H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `Asymptotics.IsLittleO.add_add`：∀ {α : Type u_1} {E' : Type u_6} {F' : Ty
pe u_7} [inst : SeminormedAddCommGroup E'] [inst_1 : SeminormedAddCommGroup F'] 
  {l : Filter α} {f…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem IsLittleO.sum_congr (hAB : ∀ i ∈ s, A i =o[l] B i) :
    (fun H => ∑ i ∈ s, A i H) =o[l] fun H => ∑ i ∈ s, ‖B i H‖ := by
  induction s using Finset.cons_induction with
  | empty => simp [isLittleO_zero]
  | cons i s his h =>
  simp_rw [Finset.sum_cons]
  calc (fun H => A i H + ∑ j ∈ s, A j H)
      =o[l] fun H => ‖B i H‖ + ‖∑ j ∈ s, ‖B j H‖‖ :=
          (hAB i (by simp)).add_add (h (fun j hj => hAB j (by simp [hj])))
    _ =ᶠ[l] fun H => ‖B i H‖ + ∑ j ∈ s, ‖B j H‖ := by
        refine Eventually.of_forall fun H ↦ congr_arg (‖B i H‖ + ·) ?_
        exact Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)

/-- Similar to `IsBigOWith.sum_congr` except the index set can change in the sum. This requires the
constant in `hAB` to be independent of the index `i` and also the big-O relationship to "kick in"
at the same point along the running variable. Hence the `⊤` in `⊤ ×ˢ l`. -/
/-
**Asymptotics.IsBigOWith.sum_congr'** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBig
OWith`。
形式化陈述：∀ {α : Type u_1} {E' : Type u_6} [inst : SeminormedAddCommGroup E'] {l : F
ilter α} {ι : Type u_18} {A : ι → α → E'}   {B : ι → α → ℝ} {C : ℝ} {i : α → Fin
set ι},   Asymptotics.IsBigOWith C (⊤ ×ˢ l) (Function.uncurry A) (Function.uncur
ry B) →     Asymptotics.IsBigOWith C l (fun H => ∑ j ∈ i H, A j H) fun H => ∑ j 
∈ i H, ‖B j H‖
参数：⊤ ×ˢ l；Function.uncurry A；Function.uncurry B；fun H => ∑ j ∈ i H, A j H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type 
u_20} [inst : Norm E] [inst_1 : Norm F] (c : ℝ) (l : Filter α) (f : α → E)   (g 
: α → F), Asympt…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.eventually_prod_iff`：eventually_prod_iff {p : α × β -> Prop} : (f
orallᶠ x in f ×ˢ g, p x) ↔ exists pa : α -> Prop, (forallᶠ x in f, pa x) ∧ exist
s pb : β -> Prop…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `norm_sum_le`：norm_sum_le {E} [SeminormedAddCommGroup E] (s : Finset ι) (
f : ι -> E) : ‖∑ i in s, f i‖ <= ∑ i in s, ‖f i‖
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Filter.eventually_top`：eventually_top {p : α -> Prop} : (forallᶠ x in ⊤,
 p x) ↔ forall x, p x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖

--- 原说明 ---
Similar to `IsBigOWith.sum_congr` except the index set can change in the sum. Th
is requires the
constant in `hAB` to be independent of the index `i` and also the big-O relation
ship to "kick in"
at the same point along the running variable. Hence the `⊤` in `⊤ ×ˢ l`.
-/
theorem IsBigOWith.sum_congr' {C : ℝ} {i : α → Finset ι}
    (hAB : IsBigOWith C (⊤ ×ˢ l) A.uncurry B.uncurry) :
    IsBigOWith C l (fun H => ∑ j ∈ i H, A j H) (fun H => ∑ j ∈ i H, ‖B j H‖) := by
  simp only [IsBigOWith_def] at *
  obtain ⟨s₁, hs₁, s₂, hs₂, hbound⟩ := Filter.eventually_prod_iff.mp hAB
  filter_upwards [hs₂] with H hH
  calc
    ‖∑ j ∈ i H, A j H‖ ≤ ∑ j ∈ i H, ‖A j H‖ := norm_sum_le ..
    _ ≤ ∑ j ∈ i H, C * ‖B j H‖ :=
        Finset.sum_le_sum fun j _ => hbound (Filter.eventually_top.mp hs₁ j) hH
    _ = C * ∑ j ∈ i H, ‖B j H‖ := (Finset.mul_sum ..).symm
    _ = C * ‖∑ j ∈ i H, ‖B j H‖‖ := by
        congr; rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))]
/-
**Asymptotics.IsBigO.sum_congr'** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`。
形式化陈述：∀ {α : Type u_1} {E' : Type u_6} [inst : SeminormedAddCommGroup E'] {l : F
ilter α} {ι : Type u_18} {A : ι → α → E'}   {B : ι → α → ℝ} {i : α → Finset ι}, 
  Function.uncurry A =O[⊤ ×ˢ l] Function.uncurry B → (fun H => ∑ j ∈ i H, A j H)
 =O[l] fun H => ∑ j ∈ i H, ‖B j H‖
参数：fun H => ∑ j ∈ i H, A j H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type u_20
} [inst : Norm E] [inst_1 : Norm F] (l : Filter α) (f : α → E)   (g : α → F), f 
=O[l] g = ∃ …
· 使用定理 `Asymptotics.IsBigO.isBigOWith`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α}, 
  f =O[l] g → ∃ c, …
· 使用定理 `Asymptotics.IsBigOWith.sum_congr'`：∀ {α : Type u_1} {E' : Type u_6} [ins
t : SeminormedAddCommGroup E'] {l : Filter α} {ι : Type u_18} {A : ι → α → E'}  
 {B : ι → α → ℝ} {C : ℝ…
-/
theorem IsBigO.sum_congr' {i : α → Finset ι} (hAB : A.uncurry =O[⊤ ×ˢ l] B.uncurry) :
    (fun H => ∑ j ∈ i H, A j H) =O[l] (fun H => ∑ j ∈ i H, ‖B j H‖) := by
  simp only [IsBigO_def]
  obtain ⟨C, hC⟩ := hAB.isBigOWith
  exact ⟨C, hC.sum_congr'⟩
/-
**Asymptotics.IsLittleO.sum_congr'** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLitt
leO`。
形式化陈述：∀ {α : Type u_1} {E' : Type u_6} [inst : SeminormedAddCommGroup E'] {l : F
ilter α} {ι : Type u_18} {A : ι → α → E'}   {B : ι → α → ℝ} {i : α → Finset ι}, 
  Function.uncurry A =o[⊤ ×ˢ l] Function.uncurry B → (fun H => ∑ j ∈ i H, A j H)
 =o[l] fun H => ∑ j ∈ i H, ‖B j H‖
参数：fun H => ∑ j ∈ i H, A j H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.isLittleO_iff_forall_isBigOWith`：isLittleO_iff_forall_isBigO
With : f =o[l] g ↔ forall ⦃c : Real⦄, 0 < c -> IsBigOWith c l f g
· 使用定理 `Asymptotics.IsBigOWith.sum_congr'`：∀ {α : Type u_1} {E' : Type u_6} [ins
t : SeminormedAddCommGroup E'] {l : Filter α} {ι : Type u_18} {A : ι → α → E'}  
 {B : ι → α → ℝ} {C : ℝ…
-/
theorem IsLittleO.sum_congr' {i : α → Finset ι} (hAB : A.uncurry =o[⊤ ×ˢ l] B.uncurry) :
    (fun H => ∑ j ∈ i H, A j H) =o[l] (fun H => ∑ j ∈ i H, ‖B j H‖) := by
  rw [isLittleO_iff_forall_isBigOWith] at *
  intro c hc
  exact (hAB hc).sum_congr'

end Sum

/-!
### Eventually (u / v) * v = u

If `u` and `v` are linked by an `IsBigOWith` relation, then we
eventually have `(u / v) * v = u`, even if `v` vanishes.
-/

section EventuallyMulDivCancel

variable {u v : α → 𝕜}

/-
**Asymptotics.IsBigOWith.eventually_mul_div_cancel** 是 Mathlib 中的一个定理，位于命名空间 `As
ymptotics.IsBigOWith`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_15} [inst : NormedDivisionRing 𝕜] {c : ℝ} {l 
: Filter α} {u v : α → 𝕜},   Asymptotics.IsBigOWith c l u v → u / v * v =ᶠ[l] u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Asymptotics.IsBigOWith.bound`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : Fi
lter α}, Asymptoti…
· 使用引理 `div_mul_cancel_of_imp`：div_mul_cancel_of_imp (h : b = 0 -> a = 0) : a / 
b * b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem IsBigOWith.eventually_mul_div_cancel (h : IsBigOWith c l u v) : u / v * v =ᶠ[l] u :=
  Eventually.mono h.bound fun y hy => div_mul_cancel_of_imp fun hv => by simpa [hv] using hy

/-- If `u = O(v)` along `l`, then `(u / v) * v = u` eventually at `l`. -/
/-
**Asymptotics.IsBigO.eventually_mul_div_cancel** 是 Mathlib 中的一个定理，位于命名空间 `Asympt
otics.IsBigO`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_15} [inst : NormedDivisionRing 𝕜] {l : Filter
 α} {u v : α → 𝕜},   u =O[l] v → u / v * v =ᶠ[l] u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.isBigOWith`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α}, 
  f =O[l] g → ∃ c, …
· 使用定理 `Asymptotics.IsBigOWith.eventually_mul_div_cancel`：∀ {α : Type u_1} {𝕜 : 
Type u_15} [inst : NormedDivisionRing 𝕜] {c : ℝ} {l : Filter α} {u v : α → 𝕜},  
 Asymptotics.IsBigOWith c l u v → u / …

--- 原说明 ---
If `u = O(v)` along `l`, then `(u / v) * v = u` eventually at `l`.
-/
theorem IsBigO.eventually_mul_div_cancel (h : u =O[l] v) : u / v * v =ᶠ[l] u :=
  let ⟨_c, hc⟩ := h.isBigOWith
  hc.eventually_mul_div_cancel

/-- If `u = o(v)` along `l`, then `(u / v) * v = u` eventually at `l`. -/
/-
**Asymptotics.IsLittleO.eventually_mul_div_cancel** 是 Mathlib 中的一个定理，位于命名空间 `Asy
mptotics.IsLittleO`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_15} [inst : NormedDivisionRing 𝕜] {l : Filter
 α} {u v : α → 𝕜},   u =o[l] v → u / v * v =ᶠ[l] u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.eventually_mul_div_cancel`：∀ {α : Type u_1} {𝕜 : 
Type u_15} [inst : NormedDivisionRing 𝕜] {c : ℝ} {l : Filter α} {u v : α → 𝕜},  
 Asymptotics.IsBigOWith c l u v → u / …
· 使用定理 `Asymptotics.IsLittleO.forall_isBigOWith`：∀ {α : Type u_1} {E : Type u_3}
 {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : F
ilter α},   f =o[l] g → ∀ ⦃c …
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α

--- 原说明 ---
If `u = o(v)` along `l`, then `(u / v) * v = u` eventually at `l`.
-/
theorem IsLittleO.eventually_mul_div_cancel (h : u =o[l] v) : u / v * v =ᶠ[l] u :=
  (h.forall_isBigOWith zero_lt_one).eventually_mul_div_cancel

end EventuallyMulDivCancel

end Asymptotics

