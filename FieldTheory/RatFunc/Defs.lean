/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# The field of rational functions

Files in this folder define the field `K⟮X⟯` of rational functions over a field `K`, show it
is the field of fractions of `K[X]` and provide the main results concerning it. This file contains
the basic definition.

For connections with Laurent Series, see `Mathlib/RingTheory/LaurentSeries.lean`.

## Main definitions
We provide a set of recursion and induction principles:
- `RatFunc.liftOn`: define a function by mapping a fraction of polynomials `p/q` to `f p q`,
  if `f` is well-defined in the sense that `p/q = p'/q' → f p q = f p' q'`.
- `RatFunc.liftOn'`: define a function by mapping a fraction of polynomials `p/q` to `f p q`,
  if `f` is well-defined in the sense that `f (a * p) (a * q) = f p' q'`.
- `RatFunc.induction_on`: if `P` holds on `p / q` for all polynomials `p q`, then `P` holds on all
  rational functions

## Implementation notes

To provide good API encapsulation and speed up unification problems,
`RatFunc` is defined as a structure, and all operations are `@[irreducible] def`s

We need a couple of maps to set up the `Field` and `IsFractionRing` structure,
namely `RatFunc.ofFractionRing`, `RatFunc.toFractionRing`, `RatFunc.mk` and
`RatFunc.toFractionRingRingEquiv`.
All these maps get `simp`ed to bundled morphisms like `algebraMap K[X] K⟮X⟯`
and `IsLocalization.algEquiv`.

There are separate lifts and maps of homomorphisms, to provide routes of lifting even when
the codomain is not a field or even an integral domain.

## References

* [Kleiman, *Misconceptions about $K_X$*][kleiman1979]
* https://freedommathdance.blogspot.com/2012/11/misconceptions-about-kx.html
* https://stacks.math.columbia.edu/tag/01X1

-/

@[expose] public section

noncomputable section

open scoped nonZeroDivisors Polynomial

universe u v

variable (K : Type u)

/-- `RatFunc K` is `K(X)`, the field of rational functions over `K`.

The inclusion of polynomials into `RatFunc` is `algebraMap K[X] K⟮X⟯`,
the maps between `K⟮X⟯` and another field of fractions of `K[X]`,
especially `FractionRing K[X]`, are given by `IsLocalization.algEquiv`.
-/
/-
**RatFunc** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(K : Type u) → [CommRing K] → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`RatFunc K` is `K(X)`, the field of rational functions over `K`.

The inclusion of polynomials into `RatFunc` is `algebraMap K[X] K⟮X⟯`,
the maps between `K⟮X⟯` and another field of fractions of `K[X]`,
especially `FractionRing K[X]`, are given by `IsLocalization.algEquiv`.
-/
structure RatFunc [CommRing K] : Type u where ofFractionRing ::
/-- the coercion to the fraction ring of the polynomial ring -/
  toFractionRing : FractionRing K[X]

@[inherit_doc] scoped[RatFunc] notation:9000 R "⟮X⟯" => RatFunc R

namespace RatFunc

section CommRing

variable {K}
variable [CommRing K]

section Rec

/-! ### Constructing `RatFunc`s and their induction principles -/

/-
**RatFunc.ofFractionRing_injective** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：ofFractionRing_injective : Function.Injective (ofFractionRing : _ -> K⟮X⟯)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RatFunc.ofFractionRing.inj`：∀ {K : Type u} {inst : CommRing K} {toFracti
onRing toFractionRing_1 : FractionRing (Polynomial K)},   { toFractionRing := to
FractionRing } =…

--- 原说明 ---
### Constructing `RatFunc`s and their induction principles
-/
theorem ofFractionRing_injective : Function.Injective (ofFractionRing : _ → K⟮X⟯) :=
  fun _ _ => ofFractionRing.inj
/-
**RatFunc.toFractionRing_injective** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：∀ {K : Type u} [inst : CommRing K], Function.Injective RatFunc.toFractionR
ing
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFractionRing_injective : Function.Injective (toFractionRing : _ → FractionRing K[X])
  | ⟨x⟩, ⟨y⟩, xy => by subst xy; rfl
/-
**RatFunc.toFractionRing_inj** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：∀ {K : Type u} [inst : CommRing K] {x y : RatFunc K}, x.toFractionRing = y
.toFractionRing ↔ x = y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `RatFunc.toFractionRing_injective`：∀ {K : Type u} [inst : CommRing K], Fu
nction.Injective RatFunc.toFractionRing
-/
@[simp] lemma toFractionRing_inj {x y : K⟮X⟯} :
    toFractionRing x = toFractionRing y ↔ x = y :=
  toFractionRing_injective.eq_iff

/-- Non-dependent recursion principle for `K⟮X⟯`:
To construct a term of `P : Sort*` out of `x : K⟮X⟯`,
it suffices to provide a constructor `f : Π (p q : K[X]), P`
and a proof that `f p q = f p' q'` for all `p q p' q'` such that `q' * p = q * p'` where
both `q` and `q'` are not zero divisors, stated as `q ∉ K[X]⁰`, `q' ∉ K[X]⁰`.

If considering `K` as an integral domain, this is the same as saying that
we construct a value of `P` for such elements of `K⟮X⟯` by setting
`liftOn (p / q) f _ = f p q`.

When `[IsDomain K]`, one can use `RatFunc.liftOn'`, which has the stronger requirement
of `∀ {p q a : K[X]} (hq : q ≠ 0) (ha : a ≠ 0), f (a * p) (a * q) = f p q)`.
-/
protected irreducible_def liftOn {P : Sort v} (x : K⟮X⟯) (f : K[X] → K[X] → P)
    (H : ∀ {p q p' q'} (_hq : q ∈ K[X]⁰) (_hq' : q' ∈ K[X]⁰), q' * p = q * p' → f p q = f p' q') :
    P :=
  Localization.liftOn (toFractionRing x) (fun p q => f p q) fun {_ _ q q'} h =>
    H q.2 q'.2 (let ⟨⟨_, _⟩, mul_eq⟩ := Localization.r_iff_exists.mp h
      mul_cancel_left_coe_nonZeroDivisors.mp mul_eq)

/-
**RatFunc.liftOn_ofFractionRing_mk** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：liftOn_ofFractionRing_mk {P : Sort v} (n : K[X]) (d : K[X]⁰) (f : K[X] -> 
K[X] -> P) (H : forall {p q p' q'} (_hq : q in K[X]⁰) (_hq' : q' in K[X]⁰), q' *
 p = q * p' -> f p q = f p' q') : RatFunc.liftOn (ofFractionRing (Localization.m
k n d)) f @H = f n d
参数：n : K[X]；d : K[X]⁰；f : K[X] -> K[X] -> P；H : forall {p q p' q'} (_hq : q in K
[X]⁰) (_hq' : q' in K[X]⁰), q' * p = q * p' -> f p q = f p' q'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RatFunc.liftOn_def`：∀ {K : Type u_1} [inst : CommRing K] {P : Sort u_2} 
(x : RatFunc K) (f : Polynomial K → Polynomial K → P)   (H :     ∀ {p q p' q' : 
Polynomi…
· 使用定理 `Localization.liftOn_mk`：liftOn_mk {p : Sort u} (f : M -> S -> p) (H) (a 
: M) (b : S) : liftOn (mk a b) f H = f a b
-/
theorem liftOn_ofFractionRing_mk {P : Sort v} (n : K[X]) (d : K[X]⁰) (f : K[X] → K[X] → P)
    (H : ∀ {p q p' q'} (_hq : q ∈ K[X]⁰) (_hq' : q' ∈ K[X]⁰), q' * p = q * p' → f p q = f p' q') :
    RatFunc.liftOn (ofFractionRing (Localization.mk n d)) f @H = f n d := by
  rw [RatFunc.liftOn]
  exact Localization.liftOn_mk _ _ _ _
/-
**RatFunc.liftOn_condition_of_liftOn'_condition** 是 Mathlib 中的一个定理，位于命名空间 `RatFu
nc`。
形式化陈述：∀ {K : Type u} [inst : CommRing K] {P : Sort v} {f : Polynomial K → Polyno
mial K → P},   (∀ {p q a : Polynomial K}, q ≠ 0 → a ≠ 0 → f (a * p) (a * q) = f 
p q) →     ∀ ⦃p q p' q' : Polynomial K⦄, q ≠ 0 → q' ≠ 0 → q' * p = q * p' → f p 
q = f p' q'
参数：∀ {p q a : Polynomial K}, q ≠ 0 → a ≠ 0 → f (a * p) (a * q) = f p q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem liftOn_condition_of_liftOn'_condition {P : Sort v} {f : K[X] → K[X] → P}
    (H : ∀ {p q a} (_ : q ≠ 0) (_ha : a ≠ 0), f (a * p) (a * q) = f p q) ⦃p q p' q' : K[X]⦄
    (hq : q ≠ 0) (hq' : q' ≠ 0) (h : q' * p = q * p') : f p q = f p' q' :=
  calc
    f p q = f (q' * p) (q' * q) := (H hq hq').symm
    _ = f (q * p') (q * q') := by rw [h, mul_comm q']
    _ = f p' q' := H hq' hq

section IsDomain

variable [IsDomain K]

/-- `RatFunc.mk (p q : K[X])` is `p / q` as a rational function.

If `q = 0`, then `mk` returns 0.

This is an auxiliary definition used to define an `Algebra` structure on `RatFunc`;
the `simp` normal form of `mk p q` is `algebraMap _ _ p / algebraMap _ _ q`.
-/
protected irreducible_def mk (p q : K[X]) : K⟮X⟯ :=
  ofFractionRing (algebraMap _ _ p / algebraMap _ _ q)

/-
**RatFunc.mk_eq_div'** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：mk_eq_div' (p q : K[X]) : RatFunc.mk p q = ofFractionRing (algebraMap _ _ 
p / algebraMap _ _ q)
参数：p q : K[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RatFunc.mk_def`：∀ {K : Type u_1} [inst : CommRing K] [inst_1 : IsDomain 
K] (p q : Polynomial K),   RatFunc.mk p q =     {       toFractionRing :=       
  (a…
-/
theorem mk_eq_div' (p q : K[X]) :
    RatFunc.mk p q = ofFractionRing (algebraMap _ _ p / algebraMap _ _ q) := by rw [RatFunc.mk]
/-
**RatFunc.mk_zero** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：mk_zero (p : K[X]) : RatFunc.mk p 0 = ofFractionRing (0 : FractionRing K[X
])
参数：p : K[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RatFunc.mk_eq_div'`：mk_eq_div' (p q : K[X]) : RatFunc.mk p q = ofFractio
nRing (algebraMap _ _ p / algebraMap _ _ q)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
-/
theorem mk_zero (p : K[X]) : RatFunc.mk p 0 = ofFractionRing (0 : FractionRing K[X]) := by
  rw [mk_eq_div', map_zero, div_zero]
/-
**RatFunc.mk_coe_def** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：mk_coe_def (p : K[X]) (q : K[X]⁰) : RatFunc.mk p q = ofFractionRing (IsLoc
alization.mk' _ p q)
参数：p : K[X]；q : K[X]⁰。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Polynomial.instIsDomainOfIsCancelAdd`：∀ {R : Type u} [inst : Semiring R]
 [IsCancelAdd R] [IsDomain R], IsDomain (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RatFunc.mk_eq_div'`：mk_eq_div' (p q : K[X]) : RatFunc.mk p q = ofFractio
nRing (algebraMap _ _ p / algebraMap _ _ q)
· 使用定理 `FractionRing.mk_eq_div`：mk_eq_div {r s} : (Localization.mk r s : Fractio
nRing A) = (algebraMap _ _ r / algebraMap A _ s : FractionRing A)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_coe_def (p : K[X]) (q : K[X]⁰) :
    RatFunc.mk p q = ofFractionRing (IsLocalization.mk' _ p q) := by
  simp only [mk_eq_div', ← Localization.mk_eq_mk', FractionRing.mk_eq_div]
/-
**RatFunc.mk_def_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：mk_def_of_mem (p : K[X]) {q} (hq : q in K[X]⁰) : RatFunc.mk p q = ofFracti
onRing (IsLocalization.mk' (FractionRing K[X]) p ⟨q, hq⟩)
参数：p : K[X]；hq : q in K[X]⁰。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_def_of_mem (p : K[X]) {q} (hq : q ∈ K[X]⁰) :
    RatFunc.mk p q = ofFractionRing (IsLocalization.mk' (FractionRing K[X]) p ⟨q, hq⟩) := by
  simp only [← mk_coe_def]
/-
**RatFunc.mk_def_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：mk_def_of_ne (p : K[X]) {q : K[X]} (hq : q != 0) : RatFunc.mk p q = ofFrac
tionRing (IsLocalization.mk' (FractionRing K[X]) p ⟨q, mem_nonZeroDivisors_iff_n
e_zero.mpr hq⟩)
参数：p : K[X]；hq : q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RatFunc.mk_def_of_mem`：mk_def_of_mem (p : K[X]) {q} (hq : q in K[X]⁰) : 
RatFunc.mk p q = ofFractionRing (IsLocalization.mk' (FractionRing K[X]) p ⟨q, hq
⟩)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_nonZeroDivisors_iff_ne_zero`：∀ {M₀ : Type u_2} [inst : MonoidWithZer
o M₀] {x : M₀} [NoZeroDivisors M₀] [Nontrivial M₀],   x ∈ nonZeroDivisors M₀ ↔ x
 ≠ 0
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
-/
theorem mk_def_of_ne (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
    RatFunc.mk p q =
      ofFractionRing (IsLocalization.mk' (FractionRing K[X]) p
        ⟨q, mem_nonZeroDivisors_iff_ne_zero.mpr hq⟩) :=
  mk_def_of_mem p _
/-
**RatFunc.mk_eq_localization_mk** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：mk_eq_localization_mk (p : K[X]) {q : K[X]} (hq : q != 0) : RatFunc.mk p q
 = ofFractionRing (Localization.mk p ⟨q, mem_nonZeroDivisors_iff_ne_zero.mpr hq⟩
)
参数：p : K[X]；hq : q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_nonZeroDivisors_iff_ne_zero`：∀ {M₀ : Type u_2} [inst : MonoidWithZer
o M₀] {x : M₀} [NoZeroDivisors M₀] [Nontrivial M₀],   x ∈ nonZeroDivisors M₀ ↔ x
 ≠ 0
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RatFunc.mk_def_of_ne`：mk_def_of_ne (p : K[X]) {q : K[X]} (hq : q != 0) :
 RatFunc.mk p q = ofFractionRing (IsLocalization.mk' (FractionRing K[X]) p ⟨q, m
em_nonZero…
· 使用定理 `Localization.mk_eq_mk'`：mk_eq_mk'_apply (x y) : mk x y = IsLocalization.
mk' (Localization M) x y
-/
theorem mk_eq_localization_mk (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
    RatFunc.mk p q =
      ofFractionRing (Localization.mk p ⟨q, mem_nonZeroDivisors_iff_ne_zero.mpr hq⟩) := by
  rw [mk_def_of_ne _ hq, Localization.mk_eq_mk']
/-
**RatFunc.mk_one'** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：mk_one' (p : K[X]) : RatFunc.mk p 1 = ofFractionRing (algebraMap _ _ p)
参数：p : K[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.mk'_one`：∀ {R : Type u_1} [inst : CommSemiring R] {M : Su
bmonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [in
st_3 : IsLoc…
· 使用定理 `RatFunc.mk_coe_def`：mk_coe_def (p : K[X]) (q : K[X]⁰) : RatFunc.mk p q =
 ofFractionRing (IsLocalization.mk' _ p q)
· 使用定理 `Submonoid.coe_one`：coe_one : ((1 : S) : M) = 1
-/
theorem mk_one' (p : K[X]) :
    RatFunc.mk p 1 = ofFractionRing (algebraMap _ _ p) := by
  rw [← IsLocalization.mk'_one (M := K[X]⁰) (FractionRing K[X]) p, ← mk_coe_def, Submonoid.coe_one]
/-
**RatFunc.mk_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：mk_eq_mk {p q p' q' : K[X]} (hq : q != 0) (hq' : q' != 0) : RatFunc.mk p q
 = RatFunc.mk p' q' ↔ p * q' = p' * q
参数：hq : q != 0；hq' : q' != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_nonZeroDivisors_iff_ne_zero`：∀ {M₀ : Type u_2} [inst : MonoidWithZer
o M₀] {x : M₀} [NoZeroDivisors M₀] [Nontrivial M₀],   x ∈ nonZeroDivisors M₀ ↔ x
 ≠ 0
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RatFunc.mk_def_of_ne`：mk_def_of_ne (p : K[X]) {q : K[X]} (hq : q != 0) :
 RatFunc.mk p q = ofFractionRing (IsLocalization.mk' (FractionRing K[X]) p ⟨q, m
em_nonZero…
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `RatFunc.ofFractionRing_injective`：ofFractionRing_injective : Function.In
jective (ofFractionRing : _ -> K⟮X⟯)
· 使用定理 `IsLocalization.mk'_eq_iff_eq'`：∀ {R : Type u_1} [inst : CommSemiring R] 
{M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R
 S] [inst_3 : IsLoc…
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_eq_mk {p q p' q' : K[X]} (hq : q ≠ 0) (hq' : q' ≠ 0) :
    RatFunc.mk p q = RatFunc.mk p' q' ↔ p * q' = p' * q := by
  rw [mk_def_of_ne _ hq, mk_def_of_ne _ hq', ofFractionRing_injective.eq_iff,
    IsLocalization.mk'_eq_iff_eq',
    (IsFractionRing.injective K[X] (FractionRing K[X])).eq_iff]
/-
**RatFunc.liftOn_mk** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：liftOn_mk {P : Sort v} (p q : K[X]) (f : K[X] -> K[X] -> P) (f0 : forall p
, f p 0 = f 0 1) (H' : forall {p q p' q'} (_hq : q != 0) (_hq' : q' != 0), q' * 
p = q * p' -> f p q = f p' q') (H : forall {p q p' q'} (_hq : q in K[X]⁰) (_hq' 
: q' in K[X]⁰), q' * p = q * p' -> f p q = f p' q'
参数：p q : K[X]；f : K[X] -> K[X] -> P；f0 : forall p, f p 0 = f 0 1；H' : forall {p 
q p' q'} (_hq : q != 0) (_hq' : q' != 0), q' * p = q * p' -> f p q = f p' q'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RatFunc.liftOn.congr_simp`：∀ {K : Type u_1} [inst : CommRing K] {P : Sor
t u_2} (x x_1 : RatFunc K),   x = x_1 →     ∀ (f f_1 : Polynomial K → Polynomial
 K → P) (e_f : …
· 使用定理 `RatFunc.mk_zero`：mk_zero (p : K[X]) : RatFunc.mk p 0 = ofFractionRing (0
 : FractionRing K[X])
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Localization.mk_zero`：mk_zero (x : S) : mk 0 (x : S) = 0
· 使用定理 `RatFunc.liftOn_ofFractionRing_mk`：liftOn_ofFractionRing_mk {P : Sort v} 
(n : K[X]) (d : K[X]⁰) (f : K[X] -> K[X] -> P) (H : forall {p q p' q'} (_hq : q 
in K[X]⁰) (_hq' : q' i…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_nonZeroDivisors_iff_ne_zero`：∀ {M₀ : Type u_2} [inst : MonoidWithZer
o M₀] {x : M₀} [NoZeroDivisors M₀] [Nontrivial M₀],   x ∈ nonZeroDivisors M₀ ↔ x
 ≠ 0
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `RatFunc.mk_eq_localization_mk`：mk_eq_localization_mk (p : K[X]) {q : K[X
]} (hq : q != 0) : RatFunc.mk p q = ofFractionRing (Localization.mk p ⟨q, mem_no
nZeroDivisors_iff_n…
-/
theorem liftOn_mk {P : Sort v} (p q : K[X]) (f : K[X] → K[X] → P) (f0 : ∀ p, f p 0 = f 0 1)
    (H' : ∀ {p q p' q'} (_hq : q ≠ 0) (_hq' : q' ≠ 0), q' * p = q * p' → f p q = f p' q')
    (H : ∀ {p q p' q'} (_hq : q ∈ K[X]⁰) (_hq' : q' ∈ K[X]⁰), q' * p = q * p' → f p q = f p' q' :=
      fun {_ _ _ _} hq hq' h => H' (nonZeroDivisors.ne_zero hq) (nonZeroDivisors.ne_zero hq') h) :
    (RatFunc.mk p q).liftOn f @H = f p q := by
  by_cases hq : q = 0
  · subst hq
    simp only [mk_zero, f0, ← Localization.mk_zero 1,
      liftOn_ofFractionRing_mk, Submonoid.coe_one]
  · simp only [mk_eq_localization_mk _ hq, liftOn_ofFractionRing_mk]

/-- Non-dependent recursion principle for `K⟮X⟯`: if `f p q : P` for all `p q`,
such that `f (a * p) (a * q) = f p q`, then we can find a value of `P`
for all elements of `K⟮X⟯` by setting `lift_on' (p / q) f _ = f p q`.

The value of `f p 0` for any `p` is never used and in principle this may be anything,
although many usages of `lift_on'` assume `f p 0 = f 0 1`.
-/
protected irreducible_def liftOn' {P : Sort v} (x : K⟮X⟯) (f : K[X] → K[X] → P)
  (H : ∀ {p q a} (_hq : q ≠ 0) (_ha : a ≠ 0), f (a * p) (a * q) = f p q) : P :=
  x.liftOn f fun {_p _q _p' _q'} hq hq' =>
    liftOn_condition_of_liftOn'_condition (@H) (nonZeroDivisors.ne_zero hq)
      (nonZeroDivisors.ne_zero hq')

/-
**RatFunc.liftOn'_mk** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：∀ {K : Type u} [inst : CommRing K] [inst_1 : IsDomain K] {P : Sort v} (p q
 : Polynomial K)   (f : Polynomial K → Polynomial K → P),   (∀ (p : Polynomial K
), f p 0 = f 0 1) →     ∀ (H : ∀ {p q a : Polynomial K}, q ≠ 0 → a ≠ 0 → f (a * 
p) (a * q) = f p q), (RatFunc.mk p q).liftOn' f H = f p q
参数：p q : Polynomial K；f : Polynomial K → Polynomial K → P；∀ (p : Polynomial K), 
f p 0 = f 0 1；H : ∀ {p q a : Polynomial K}, q ≠ 0 → a ≠ 0 → f (a * p) (a * q) = 
f p q；RatFunc.mk p q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RatFunc.liftOn'`：liftOn'_div {P : Sort v} (p q : K[X]) (f : K[X] -> K[X]
 -> P) (f0 : forall p, f p 0 = f 0 1) (H) : (RatFunc.liftOn' (algebraMap _ K⟮X⟯ 
p / a…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RatFunc.liftOn'_def`：∀ {K : Type u_1} [inst : CommRing K] [inst_1 : IsDo
main K] {P : Sort u_2} (x : RatFunc K)   (f : Polynomial K → Polynomial K → P) (
H : ∀ {p …
· 使用定理 `RatFunc.liftOn_condition_of_liftOn'_condition`：∀ {K : Type u} [inst : Co
mmRing K] {P : Sort v} {f : Polynomial K → Polynomial K → P},   (∀ {p q a : Poly
nomial K}, q ≠ 0 → a ≠ 0 → f (a * p…
· 使用定理 `nonZeroDivisors.ne_zero`：nonZeroDivisors.ne_zero (hx : x in M₀⁰) : x != 
0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `RatFunc.liftOn_mk`：liftOn_mk {P : Sort v} (p q : K[X]) (f : K[X] -> K[X]
 -> P) (f0 : forall p, f p 0 = f 0 1) (H' : forall {p q p' q'} (_hq : q != 0) (_
hq' : q…
-/
theorem liftOn'_mk {P : Sort v} (p q : K[X]) (f : K[X] → K[X] → P) (f0 : ∀ p, f p 0 = f 0 1)
    (H : ∀ {p q a} (_hq : q ≠ 0) (_ha : a ≠ 0), f (a * p) (a * q) = f p q) :
    (RatFunc.mk p q).liftOn' f @H = f p q := by
  rw [RatFunc.liftOn', RatFunc.liftOn_mk _ _ _ f0]
  apply liftOn_condition_of_liftOn'_condition H

/-- Induction principle for `K⟮X⟯`: if `f p q : P (RatFunc.mk p q)` for all `p q`,
then `P` holds on all elements of `K⟮X⟯`.

See also `induction_on`, which is a recursion principle defined in terms of `algebraMap`.
-/
@[elab_as_elim]
/-
**RatFunc.induction_on'** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：∀ {K : Type u} [inst : CommRing K] [inst_1 : IsDomain K] {P : RatFunc K → 
Prop} (x : RatFunc K),   (∀ (p q : Polynomial K), q ≠ 0 → P (RatFunc.mk p q)) → 
P x
参数：x : RatFunc K；∀ (p q : Polynomial K), q ≠ 0 → P (RatFunc.mk p q)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Localization.induction_on`：induction_on {p : Localization S -> Prop} (x)
 (H : forall y : M × S, p (mk y.1 y.2)) : p x
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Localization.mk_eq_mk'`：mk_eq_mk'_apply (x y) : mk x y = IsLocalization.
mk' (Localization M) x y
· 使用定理 `RatFunc.mk_coe_def`：mk_coe_def (p : K[X]) (q : K[X]⁰) : RatFunc.mk p q =
 ofFractionRing (IsLocalization.mk' _ p q)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nonZeroDivisors_iff_ne_zero`：∀ {M₀ : Type u_2} [inst : MonoidWithZer
o M₀] {x : M₀} [NoZeroDivisors M₀] [Nontrivial M₀],   x ∈ nonZeroDivisors M₀ ↔ x
 ≠ 0
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
Induction principle for `K⟮X⟯`: if `f p q : P (RatFunc.mk p q)` for all `p q`,
then `P` holds on all elements of `K⟮X⟯`.

See also `induction_on`, which is a recursion principle defined in terms of `alg
ebraMap`.
-/
protected theorem induction_on' {P : K⟮X⟯ → Prop} :
    ∀ (x : K⟮X⟯) (_pq : ∀ (p q : K[X]) (_ : q ≠ 0), P (RatFunc.mk p q)), P x
  | ⟨x⟩, f =>
    Localization.induction_on x fun ⟨p, q⟩ => by
      simpa only [mk_coe_def, Localization.mk_eq_mk'] using
        f p q (mem_nonZeroDivisors_iff_ne_zero.mp q.2)

end IsDomain

end Rec

end CommRing

end RatFunc

