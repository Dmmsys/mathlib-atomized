/-
Copyright (c) 2020 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Eval.Subring
public import Mathlib.Algebra.Polynomial.Monic

/-!
# Polynomials that lift

Given semirings `R` and `S` with a morphism `f : R →+* S`, we define a subsemiring `lifts` of
`S[X]` by the image of `RingHom.of (map f)`.
Then, we prove that a polynomial that lifts can always be lifted to a polynomial of the same degree
and that a monic polynomial that lifts can be lifted to a monic polynomial (of the same degree).

## Main definition

* `lifts (f : R →+* S)` : the subsemiring of polynomials that lift.

## Main results

* `lifts_and_degree_eq` : A polynomial lifts if and only if it can be lifted to a polynomial
  of the same degree.
* `lifts_and_degree_eq_and_monic` : A monic polynomial lifts if and only if it can be lifted to a
  monic polynomial of the same degree.
* `lifts_iff_alg` : if `R` is commutative, a polynomial lifts if and only if it is in the image of
  `mapAlg`, where `mapAlg : R[X] →ₐ[R] S[X]` is the only `R`-algebra map
  that sends `X` to `X`.

## Implementation details

In general `R` and `S` are semirings, so `lifts` is a semiring. In the case of rings, see
`lifts_iff_liftsRing`.

Since we do not assume `R` to be commutative, we cannot say in general that the set of polynomials
that lift is a subalgebra. (By `lift_iff` this is true if `R` is commutative.)

-/

@[expose] public section


open Polynomial

noncomputable section

namespace Polynomial

universe u v w

section Semiring

variable {R : Type u} [Semiring R] {S : Type v} [Semiring S] {f : R →+* S}

/-- We define the subsemiring of polynomials that lifts as the image of `RingHom.of (map f)`. -/
/-
**Polynomial.lifts** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：lifts (f : R ->+* S) : Subsemiring S[X]
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We define the subsemiring of polynomials that lifts as the image of `RingHom.of 
(map f)`.
-/
def lifts (f : R →+* S) : Subsemiring S[X] :=
  RingHom.rangeS (mapRingHom f)
/-
**Polynomial.mem_lifts** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mem_lifts (p : S[X]) : p in lifts f ↔ exists q : R[X], map f q = p
参数：p : S[X]。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_lifts (p : S[X]) : p ∈ lifts f ↔ ∃ q : R[X], map f q = p := by
  simp only [coe_mapRingHom, lifts, RingHom.mem_rangeS]
/-
**Polynomial.lifts_iff_set_range** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：lifts_iff_set_range (p : S[X]) : p in lifts f ↔ p in Set.range (map f)
参数：p : S[X]。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lifts_iff_set_range (p : S[X]) : p ∈ lifts f ↔ p ∈ Set.range (map f) := by
  simp only [coe_mapRingHom, lifts, Set.mem_range, RingHom.mem_rangeS]
/-
**Polynomial.lifts_iff_ringHom_rangeS** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：lifts_iff_ringHom_rangeS (p : S[X]) : p in lifts f ↔ p in (mapRingHom f).r
angeS
参数：p : S[X]。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lifts_iff_ringHom_rangeS (p : S[X]) : p ∈ lifts f ↔ p ∈ (mapRingHom f).rangeS := by
  simp only [coe_mapRingHom, lifts, RingHom.mem_rangeS]
/-
**Polynomial.lifts_iff_coeff_lifts** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：lifts_iff_coeff_lifts (p : S[X]) : p in lifts f ↔ forall n : Nat, p.coeff 
n in Set.range f
参数：p : S[X]。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.lifts_iff_ringHom_rangeS`：lifts_iff_ringHom_rangeS (p : S[X])
 : p in lifts f ↔ p in (mapRingHom f).rangeS
· 使用定理 `Polynomial.mem_map_rangeS`：mem_map_rangeS {p : S[X]} : p in (mapRingHom 
f).rangeS ↔ forall n, p.coeff n in f.rangeS
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lifts_iff_coeff_lifts (p : S[X]) : p ∈ lifts f ↔ ∀ n : ℕ, p.coeff n ∈ Set.range f := by
  rw [lifts_iff_ringHom_rangeS, mem_map_rangeS f]
  rfl
/-
**Polynomial.lifts_iff_coeffs_subset_range** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
`。
形式化陈述：lifts_iff_coeffs_subset_range (p : S[X]) : p in lifts f ↔ (p.coeffs : Set 
S) subseteq Set.range f
参数：p : S[X]。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.lifts_iff_coeff_lifts`：lifts_iff_coeff_lifts (p : S[X]) : p i
n lifts f ↔ forall n : Nat, p.coeff n in Set.range f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.mem_coeffs_iff`：mem_coeffs_iff {p : R[X]} {c : R} : c in p.co
effs ↔ exists n in p.support, c = p.coeff n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.coeff_mem_coeffs`：coeff_mem_coeffs {p : R[X]} {n : Nat} (h : 
p.coeff n != 0) : p.coeff n in p.coeffs
-/
theorem lifts_iff_coeffs_subset_range (p : S[X]) :
    p ∈ lifts f ↔ (p.coeffs : Set S) ⊆ Set.range f := by
  rw [lifts_iff_coeff_lifts]
  constructor
  · intro h _ hc
    obtain ⟨n, ⟨-, hn⟩⟩ := mem_coeffs_iff.mp hc
    exact hn ▸ h n
  · intro h n
    by_cases hn : p.coeff n = 0
    · exact ⟨0, by simp [hn]⟩
    · exact h <| coeff_mem_coeffs hn
/-
**Polynomial.mem_lifts_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mem_lifts_of_surjective (hf : Function.Surjective f) (p : S[X]) : p in lif
ts f
参数：hf : Function.Surjective f；p : S[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.lifts_iff_coeff_lifts`：lifts_iff_coeff_lifts (p : S[X]) : p i
n lifts f ↔ forall n : Nat, p.coeff n in Set.range f
-/
theorem mem_lifts_of_surjective (hf : Function.Surjective f) (p : S[X]) : p ∈ lifts f :=
  (lifts_iff_coeff_lifts p).mpr fun n ↦ hf (p.coeff n)

/-- If `(r : R)`, then `C (f r)` lifts. -/
/-
**Polynomial.C_mem_lifts** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：C_mem_lifts (f : R ->+* S) (r : R) : C (f r) in lifts f
参数：f : R ->+* S；r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `(r : R)`, then `C (f r)` lifts.
-/
theorem C_mem_lifts (f : R →+* S) (r : R) : C (f r) ∈ lifts f :=
  ⟨C r, by
    simp only [coe_mapRingHom, map_C]⟩

/-- If `(s : S)` is in the image of `f`, then `C s` lifts. -/
/-
**Polynomial.C'_mem_lifts** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {S : Type v} [inst_1 : Semiring S] {f :
 R →+* S} {s : S},   s ∈ Set.range ⇑f → Polynomial.C s ∈ Polynomial.lifts f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `(s : S)` is in the image of `f`, then `C s` lifts.
-/
theorem C'_mem_lifts {f : R →+* S} {s : S} (h : s ∈ Set.range f) : C s ∈ lifts f := by
  obtain ⟨r, rfl⟩ := Set.mem_range.1 h
  use C r
  simp only [coe_mapRingHom, map_C]

/-- The polynomial `X` lifts. -/
/-
**Polynomial.X_mem_lifts** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：X_mem_lifts (f : R ->+* S) : (X : S[X]) in lifts f
参数：f : R ->+* S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The polynomial `X` lifts.
-/
theorem X_mem_lifts (f : R →+* S) : (X : S[X]) ∈ lifts f :=
  ⟨X, by
    simp only [coe_mapRingHom, map_X]⟩

/-- The polynomial `X ^ n` lifts. -/
/-
**Polynomial.X_pow_mem_lifts** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：X_pow_mem_lifts (f : R ->+* S) (n : Nat) : (X ^ n : S[X]) in lifts f
参数：f : R ->+* S；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The polynomial `X ^ n` lifts.
-/
theorem X_pow_mem_lifts (f : R →+* S) (n : ℕ) : (X ^ n : S[X]) ∈ lifts f :=
  ⟨X ^ n, by
    simp only [coe_mapRingHom, map_pow, map_X]⟩

/-- If `p` lifts and `(r : R)` then `r * p` lifts. -/
/-
**Polynomial.base_mul_mem_lifts** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：base_mul_mem_lifts {p : S[X]} (r : R) (hp : p in lifts f) : C (f r) * p in
 lifts f
参数：r : R；hp : p in lifts f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `p` lifts and `(r : R)` then `r * p` lifts.
-/
theorem base_mul_mem_lifts {p : S[X]} (r : R) (hp : p ∈ lifts f) : C (f r) * p ∈ lifts f := by
  simp only [lifts, RingHom.mem_rangeS] at hp ⊢
  obtain ⟨p₁, rfl⟩ := hp
  use C r * p₁
  simp only [coe_mapRingHom, map_C, map_mul]

/-- If `(s : S)` is in the image of `f`, then `monomial n s` lifts. -/
/-
**Polynomial.monomial_mem_lifts** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monomial_mem_lifts {s : S} (n : Nat) (h : s in Set.range f) : monomial n s
 in lifts f
参数：n : Nat；h : s in Set.range f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_monomial`：map_monomial {n a} : (monomial n a).map f = mon
omial n (f a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `(s : S)` is in the image of `f`, then `monomial n s` lifts.
-/
theorem monomial_mem_lifts {s : S} (n : ℕ) (h : s ∈ Set.range f) : monomial n s ∈ lifts f := by
  obtain ⟨r, rfl⟩ := Set.mem_range.1 h
  use monomial n r
  simp only [coe_mapRingHom, map_monomial]

/-- If `p` lifts then `p.erase n` lifts. -/
/-
**Polynomial.erase_mem_lifts** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：erase_mem_lifts {p : S[X]} (n : Nat) (h : p in lifts f) : p.erase n in lif
ts f
参数：n : Nat；h : p in lifts f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.lifts_iff_ringHom_rangeS`：lifts_iff_ringHom_rangeS (p : S[X])
 : p in lifts f ↔ p in (mapRingHom f).rangeS
· 使用定理 `Polynomial.mem_map_rangeS`：mem_map_rangeS {p : S[X]} : p in (mapRingHom 
f).rangeS ↔ forall n, p.coeff n in f.rangeS
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Polynomial.erase_same`：erase_same (p : R[X]) (n : Nat) : coeff (p.erase 
n) n = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.erase_ne`：erase_ne (p : R[X]) {n i : Nat} (h : i != n) : coef
f (p.erase n) i = coeff p i
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False

--- 原说明 ---
If `p` lifts then `p.erase n` lifts.
-/
theorem erase_mem_lifts {p : S[X]} (n : ℕ) (h : p ∈ lifts f) : p.erase n ∈ lifts f := by
  rw [lifts_iff_ringHom_rangeS, mem_map_rangeS] at h ⊢
  intro k
  by_cases hk : k = n
  · use 0
    simp only [hk, map_zero, erase_same]
  obtain ⟨i, hi⟩ := h k
  use i
  simp only [hi, hk, erase_ne, Ne, not_false_iff]

section LiftDeg

/-
**Polynomial.monomial_mem_lifts_and_degree_eq** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial`。
形式化陈述：monomial_mem_lifts_and_degree_eq {s : S} {n : Nat} (hl : monomial n s in l
ifts f) : exists q : R[X], map f q = monomial n s ∧ q.degree = (monomial n s).de
gree
参数：hl : monomial n s in lifts f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_zero`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [in
st_1 : Semiring S] (f : R →+* S), Polynomial.map f 0 = 0
· 使用定理 `Polynomial.monomial_zero_right`：monomial_zero_right (n : Nat) : monomial
 n (0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.lifts_iff_coeff_lifts`：lifts_iff_coeff_lifts (p : S[X]) : p i
n lifts f ↔ forall n : Nat, p.coeff n in Set.range f
· 使用定理 `Polynomial.coeff_monomial_same`：coeff_monomial_same (n : Nat) (c : R) : 
(monomial n c).coeff n = c
· 使用定理 `Polynomial.map_monomial`：map_monomial {n a} : (monomial n a).map f = mon
omial n (f a)
· 使用定理 `Polynomial.degree_monomial`：degree_monomial (n : Nat) (ha : a != 0) : de
gree (monomial n a) = n
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem monomial_mem_lifts_and_degree_eq {s : S} {n : ℕ} (hl : monomial n s ∈ lifts f) :
    ∃ q : R[X], map f q = monomial n s ∧ q.degree = (monomial n s).degree := by
  rcases eq_or_ne s 0 with rfl | h
  · exact ⟨0, by simp⟩
  obtain ⟨a, rfl⟩ := coeff_monomial_same n s ▸ (monomial n s).lifts_iff_coeff_lifts.mp hl n
  refine ⟨monomial n a, map_monomial f, ?_⟩
  rw [degree_monomial, degree_monomial n h]
  exact mt (fun ha ↦ ha ▸ map_zero f) h

/-- A polynomial that lifts can be lifted to a polynomial of the same support. -/
/-
**Polynomial.exists_support_eq_of_mem_lifts** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：exists_support_eq_of_mem_lifts {p : S[X]} (hlifts : p in lifts f) : exists
 q : R[X], map f q = p ∧ q.support = p.support
参数：hlifts : p in lifts f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.lifts_iff_coeff_lifts`：lifts_iff_coeff_lifts (p : S[X]) : p i
n lifts f ↔ forall n : Nat, p.coeff n in Set.range f
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.map_sum`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [ins
t_1 : Semiring S] (f : R →+* S) {ι : Type u_1}   (g : ι → Polynomial R) (s : Fin
set ι), …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.map_monomial`：map_monomial {n a} : (monomial n a).map f = mon
omial n (f a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.finsetSum_coeff`：finsetSum_coeff {ι : Type*} (s : Finset ι) (
f : ι -> R[X]) (n : Nat) : coeff (∑ b in s, f b) n = ∑ b in s, coeff (f b) n
· 使用定理 `Polynomial.coeff_monomial`：coeff_monomial : coeff (monomial n a) m = if 
n = m then a else 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…

--- 原说明 ---
A polynomial that lifts can be lifted to a polynomial of the same support.
-/
theorem exists_support_eq_of_mem_lifts {p : S[X]} (hlifts : p ∈ lifts f) :
    ∃ q : R[X], map f q = p ∧ q.support = p.support := by
  rw [lifts_iff_coeff_lifts] at hlifts
  let g : ℕ → R := fun k ↦ (hlifts k).choose
  have hg : ∀ k, f (g k) = p.coeff k := fun k ↦ (hlifts k).choose_spec
  let q : R[X] := ∑ k ∈ p.support, monomial k (g k)
  have hq : map f q = p := by simp_rw [q, Polynomial.map_sum, map_monomial, hg, ← as_sum_support]
  have hq' : q.support = p.support := by
    simp_rw [Finset.ext_iff, mem_support_iff, q, finsetSum_coeff, coeff_monomial,
      Finset.sum_ite_eq', ite_ne_right_iff, mem_support_iff, and_iff_left_iff_imp, not_imp_not]
    exact fun k h ↦ by rw [← hg, h, map_zero]
  exact ⟨q, hq, hq'⟩

/-- A polynomial lifts if and only if it can be lifted to a polynomial of the same degree. -/
/-
**Polynomial.exists_degree_eq_of_mem_lifts** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
`。
形式化陈述：exists_degree_eq_of_mem_lifts {p : S[X]} (hlifts : p in lifts f) : exists 
q : R[X], map f q = p ∧ q.degree = p.degree
参数：hlifts : p in lifts f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.exists_support_eq_of_mem_lifts`：exists_support_eq_of_mem_lift
s {p : S[X]} (hlifts : p in lifts f) : exists q : R[X], map f q = p ∧ q.support 
= p.support
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
A polynomial lifts if and only if it can be lifted to a polynomial of the same d
egree.
-/
theorem exists_degree_eq_of_mem_lifts {p : S[X]} (hlifts : p ∈ lifts f) :
    ∃ q : R[X], map f q = p ∧ q.degree = p.degree := by
  obtain ⟨q, hq, hq'⟩ := exists_support_eq_of_mem_lifts hlifts
  exact ⟨q, hq, congrArg Finset.max hq'⟩
/-
**Polynomial.exists_natDegree_eq_of_mem_lifts** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial`。
形式化陈述：exists_natDegree_eq_of_mem_lifts {p : S[X]} (hlifts : p in lifts f) : exis
ts q, map f q = p ∧ q.natDegree = p.natDegree
参数：hlifts : p in lifts f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.imp_right`：∀ {a b c : Prop}, (a → b) → c ∧ a → c ∧ b
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq`：natDegree_eq_of_degree_eq [Semirin
g S] {q : S[X]} (h : degree p = degree q) : natDegree p = natDegree q
· 使用定理 `Polynomial.exists_degree_eq_of_mem_lifts`：exists_degree_eq_of_mem_lifts 
{p : S[X]} (hlifts : p in lifts f) : exists q : R[X], map f q = p ∧ q.degree = p
.degree
-/
theorem exists_natDegree_eq_of_mem_lifts {p : S[X]} (hlifts : p ∈ lifts f) :
    ∃ q, map f q = p ∧ q.natDegree = p.natDegree :=
  (exists_degree_eq_of_mem_lifts hlifts).imp fun _ ↦ And.imp_right natDegree_eq_of_degree_eq

@[deprecated (since := "2026-02-11")]
alias mem_lifts_and_degree_eq := exists_degree_eq_of_mem_lifts

end LiftDeg

section Monic

/-- A monic polynomial lifts if and only if it can be lifted to a monic polynomial
of the same degree. -/
/-
**Polynomial.lifts_and_degree_eq_and_monic** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
`。
形式化陈述：lifts_and_degree_eq_and_monic [Nontrivial S] {p : S[X]} (hlifts : p in lif
ts f) (hp : p.Monic) : exists q : R[X], map f q = p ∧ q.degree = p.degree ∧ q.Mo
nic
参数：hlifts : p in lifts f；hp : p.Monic。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.lifts_iff_coeff_lifts`：lifts_iff_coeff_lifts (p : S[X]) : p i
n lifts f ↔ forall n : Nat, p.coeff n in Set.range f
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.map_add`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p + q)
 = Polyn…
· 使用定理 `Polynomial.map_sum`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [ins
t_1 : Semiring S] (f : R →+* S) {ι : Type u_1}   (g : ι → Polynomial R) (s : Fin
set ι), …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.map_pow`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p :
 Polynomial R} [inst_1 : Semiring S] (f : R →+* S) (n : ℕ),   Polynomial.map f (
p ^ n) =…
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.Monic.as_sum`：∀ {R : Type u} [inst : Semiring R] {p : Polynom
ial R},   p.Monic → p = Polynomial.X ^ p.natDegree + ∑ i ∈ Finset.range p.natDeg
ree, Polynomi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.monic_X_pow_add`：monic_X_pow_add {n : Nat} (H : degree p < n)
 : Monic (X ^ n + p)
· 使用定理 `Polynomial.Monic.degree_map`：∀ {R : Type u} {S : Type v} [inst : Semirin
g R] [inst_1 : Semiring S] [Nontrivial S] {P : Polynomial R},   P.Monic → ∀ (f :
 R →+* S), (Polyn…

--- 原说明 ---
A monic polynomial lifts if and only if it can be lifted to a monic polynomial
of the same degree.
-/
theorem lifts_and_degree_eq_and_monic [Nontrivial S] {p : S[X]} (hlifts : p ∈ lifts f)
    (hp : p.Monic) : ∃ q : R[X], map f q = p ∧ q.degree = p.degree ∧ q.Monic := by
  rw [lifts_iff_coeff_lifts] at hlifts
  let g : ℕ → R := fun k ↦ (hlifts k).choose
  have hg k : f (g k) = p.coeff k := (hlifts k).choose_spec
  let q : R[X] := X ^ p.natDegree + ∑ k ∈ Finset.range p.natDegree, C (g k) * X ^ k
  have hq : map f q = p := by
    simp_rw [q, Polynomial.map_add, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow,
      map_X, map_C, hg, ← hp.as_sum]
  have h : q.Monic := monic_X_pow_add (by simp_rw [← Fin.sum_univ_eq_sum_range, degree_sum_fin_lt])
  exact ⟨q, hq, hq ▸ (h.degree_map f).symm, h⟩
/-
**Polynomial.lifts_and_natDegree_eq_and_monic** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial`。
形式化陈述：lifts_and_natDegree_eq_and_monic {p : S[X]} (hlifts : p in lifts f) (hp : 
p.Monic) : exists q : R[X], map f q = p ∧ q.natDegree = p.natDegree ∧ q.Monic
参数：hlifts : p in lifts f；hp : p.Monic。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_one`：natDegree_one : natDegree (1 : R[X]) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.lifts_and_degree_eq_and_monic`：lifts_and_degree_eq_and_monic 
[Nontrivial S] {p : S[X]} (hlifts : p in lifts f) (hp : p.Monic) : exists q : R[
X], map f q = p ∧ q.degree = p…
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq`：natDegree_eq_of_degree_eq [Semirin
g S] {q : S[X]} (h : degree p = degree q) : natDegree p = natDegree q
-/
theorem lifts_and_natDegree_eq_and_monic {p : S[X]} (hlifts : p ∈ lifts f) (hp : p.Monic) :
    ∃ q : R[X], map f q = p ∧ q.natDegree = p.natDegree ∧ q.Monic := by
  rcases subsingleton_or_nontrivial S with hR | hR
  · obtain rfl : p = 1 := Subsingleton.elim _ _
    exact ⟨1, Subsingleton.elim _ _, by simp, by simp⟩
  obtain ⟨p', h₁, h₂, h₃⟩ := lifts_and_degree_eq_and_monic hlifts hp
  exact ⟨p', h₁, natDegree_eq_of_degree_eq h₂, h₃⟩

end Monic

end Semiring

section Ring

variable {R : Type u} [Ring R] {S : Type v} [Ring S] (f : R →+* S)

/-- The subring of polynomials that lift. -/
/-
**Polynomial.liftsRing** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：liftsRing (f : R ->+* S) : Subring S[X]
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subring of polynomials that lift.
-/
def liftsRing (f : R →+* S) : Subring S[X] :=
  RingHom.range (mapRingHom f)

/-- If `R` and `S` are rings, `p` is in the subring of polynomials that lift if and only if it is in
the subsemiring of polynomials that lift. -/
/-
**Polynomial.lifts_iff_liftsRing** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：lifts_iff_liftsRing (p : S[X]) : p in lifts f ↔ p in liftsRing f
参数：p : S[X]。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
If `R` and `S` are rings, `p` is in the subring of polynomials that lift if and 
only if it is in
the subsemiring of polynomials that lift.
-/
theorem lifts_iff_liftsRing (p : S[X]) : p ∈ lifts f ↔ p ∈ liftsRing f := by
  simp only [lifts, liftsRing, RingHom.mem_range, RingHom.mem_rangeS]

end Ring

section Algebra

variable {R : Type u} [CommSemiring R] {S : Type v} [Semiring S] [Algebra R S]

/-- A polynomial `p` lifts if and only if it is in the image of `mapAlg`. -/
/-
**Polynomial.mem_lifts_iff_mem_alg** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mem_lifts_iff_mem_alg (R : Type u) [CommSemiring R] {S : Type v} [Semiring
 S] [Algebra R S] (p : S[X]) : p in lifts (algebraMap R S) ↔ p in AlgHom.range (
@mapAlg R _ S _ _)
参数：R : Type u；p : S[X]。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `Polynomial.mapAlg_eq_map`：mapAlg_eq_map (S : Type v) [Semiring S] [Algeb
ra R S] (p : R[X]) : mapAlg R S p = map (algebraMap R S) p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A polynomial `p` lifts if and only if it is in the image of `mapAlg`.
-/
theorem mem_lifts_iff_mem_alg (R : Type u) [CommSemiring R] {S : Type v} [Semiring S] [Algebra R S]
    (p : S[X]) : p ∈ lifts (algebraMap R S) ↔ p ∈ AlgHom.range (@mapAlg R _ S _ _) := by
  simp only [coe_mapRingHom, lifts, mapAlg_eq_map, AlgHom.mem_range, RingHom.mem_rangeS]

/-- If `p` lifts and `(r : R)` then `r • p` lifts. -/
/-
**Polynomial.smul_mem_lifts** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：smul_mem_lifts {p : S[X]} (r : R) (hp : p in lifts (algebraMap R S)) : r •
 p in lifts (algebraMap R S)
参数：r : R；hp : p in lifts (algebraMap R S)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.mem_lifts_iff_mem_alg`：mem_lifts_iff_mem_alg (R : Type u) [Co
mmSemiring R] {S : Type v} [Semiring S] [Algebra R S] (p : S[X]) : p in lifts (a
lgebraMap R S) ↔ p in …
· 使用定理 `Subalgebra.smul_mem`：smul_mem {x : A} (hx : x in S) (r : R) : r • x in S

--- 原说明 ---
If `p` lifts and `(r : R)` then `r • p` lifts.
-/
theorem smul_mem_lifts {p : S[X]} (r : R) (hp : p ∈ lifts (algebraMap R S)) :
    r • p ∈ lifts (algebraMap R S) := by
  rw [mem_lifts_iff_mem_alg] at hp ⊢
  exact Subalgebra.smul_mem (mapAlg R S).range hp r
/-
**Polynomial.monic_of_monic_mapAlg** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monic_of_monic_mapAlg [FaithfulSMul R S] {p : Polynomial R} (hp : (mapAlg 
R S p).Monic) : p.Monic
参数：hp : (mapAlg R S p).Monic。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.monic_of_injective`：monic_of_injective (hf : Injective f) {p 
: R[X]} (hp : (p.map f).Monic) : p.Monic
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
-/
theorem monic_of_monic_mapAlg [FaithfulSMul R S] {p : Polynomial R} (hp : (mapAlg R S p).Monic) :
    p.Monic :=
  monic_of_injective (FaithfulSMul.algebraMap_injective R S) hp

end Algebra

end Polynomial

