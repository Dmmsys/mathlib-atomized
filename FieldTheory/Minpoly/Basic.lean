/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johan Commelin
-/
module

public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Minimal polynomials

This file defines the minimal polynomial of an element `x` of an `A`-algebra `B`,
under the assumption that x is integral over `A`, and derives some basic properties
such as irreducibility under the assumption `B` is a domain.

-/

@[expose] public section


open Polynomial Set Function

variable {A B B' : Type*}

section MinPolyDef

variable (A) [CommRing A] [Ring B] [Algebra A B]

open scoped Classical in
/-- Suppose `x : B`, where `B` is an `A`-algebra.

The minimal polynomial `minpoly A x` of `x`
is a monic polynomial with coefficients in `A` of smallest degree that has `x` as its root,
if such exists (`IsIntegral A x`) or zero otherwise.

For example, if `V` is a `𝕜`-vector space for some field `𝕜` and `f : V →ₗ[𝕜] V` then
the minimal polynomial of `f` is `minpoly 𝕜 f`.
-/
@[stacks 09GM]
/-
**minpoly** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：minpoly (x : B) : A[X]
参数：x : B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Suppose `x : B`, where `B` is an `A`-algebra.

The minimal polynomial `minpoly A x` of `x`
is a monic polynomial with coefficients in `A` of smallest degree that has `x` a
s its root,
if such exists (`IsIntegral A x`) or zero otherwise.

For example, if `V` is a `𝕜`-vector space for some field `𝕜` and `f : V →ₗ[𝕜] V`
 then
the minimal polynomial of `f` is `minpoly 𝕜 f`.
-/
noncomputable def minpoly (x : B) : A[X] :=
  if hx : IsIntegral A x then degree_lt_wf.min _ hx else 0

end MinPolyDef

namespace minpoly

section CommRing

variable [CommRing A] [Ring B] [Ring B'] [Algebra A B] [Algebra A B']
variable {x : B}

/-- A minimal polynomial is monic. -/
/-
**minpoly.monic** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：monic (hx : IsIntegral A x) : Monic (minpoly A x)
参数：hx : IsIntegral A x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Polynomial.degree_lt_wf`：degree_lt_wf : WellFounded fun p q : R[X] => de
gree p < degree q
· 使用定理 `WellFounded.min_mem`：min_mem {r : α -> α -> Prop} (H : WellFounded r) (s
 : Set α) (h : s.Nonempty) : H.min s h in s

--- 原说明 ---
A minimal polynomial is monic.
-/
theorem monic (hx : IsIntegral A x) : Monic (minpoly A x) := by
  delta minpoly
  rw [dif_pos hx]
  exact (degree_lt_wf.min_mem _ hx).1

/-- A minimal polynomial is nonzero. -/
/-
**minpoly.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：ne_zero [Nontrivial A] (hx : IsIntegral A x) : minpoly A x != 0
参数：hx : IsIntegral A x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)

--- 原说明 ---
A minimal polynomial is nonzero.
-/
theorem ne_zero [Nontrivial A] (hx : IsIntegral A x) : minpoly A x ≠ 0 :=
  (monic hx).ne_zero
/-
**minpoly.eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：eq_zero (hx : ¬IsIntegral A x) : minpoly A x = 0
参数：hx : ¬IsIntegral A x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem eq_zero (hx : ¬IsIntegral A x) : minpoly A x = 0 :=
  dif_neg hx
/-
**minpoly.ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：ne_zero_iff [Nontrivial A] : minpoly A x != 0 ↔ IsIntegral A x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_not_not`：of_not_not {a : Prop} : ¬¬a -> a
· 使用定理 `Function.mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `minpoly.eq_zero`：eq_zero (hx : ¬IsIntegral A x) : minpoly A x = 0
· 使用定理 `minpoly.ne_zero`：ne_zero [Nontrivial A] (hx : IsIntegral A x) : minpoly 
A x != 0
-/
theorem ne_zero_iff [Nontrivial A] : minpoly A x ≠ 0 ↔ IsIntegral A x :=
  ⟨fun h => of_not_not <| eq_zero.mt h, ne_zero⟩
/-
**minpoly.algHom_eq** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：algHom_eq (f : B ->ₐ[A] B') (hf : Function.Injective f) (x : B) : minpoly 
A (f x) = minpoly A x
参数：f : B ->ₐ[A] B'；hf : Function.Injective f；x : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `isIntegral_algHom_iff`：isIntegral_algHom_iff (f : A ->ₐ[R] B) (hf : Func
tion.Injective f) {x : A} : IsIntegral R (f x) ↔ IsIntegral R x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.aeval_algHom`：aeval_algHom (f : A ->ₐ[R] B) (x : A) : aeval (
f x) = f.comp (aeval x)
· 使用定理 `WellFounded.min.congr_simp`：∀ {α : Type u_1} {r r_1 : α → α → Prop} (e_r
 : r = r_1) (H : WellFounded r) (s s_1 : Set α) (e_s : s = s_1)   (h : s.Nonempt
y), H.min s h = …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_eq_zero_iff`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : 
Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F
), Fu…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem algHom_eq (f : B →ₐ[A] B') (hf : Function.Injective f) (x : B) :
    minpoly A (f x) = minpoly A x := by
  classical
  simp_rw [minpoly, isIntegral_algHom_iff _ hf, ← Polynomial.aeval_def, aeval_algHom,
    AlgHom.comp_apply, _root_.map_eq_zero_iff f hf]
/-
**minpoly.algebraMap_eq** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：algebraMap_eq {B} [CommRing B] [Algebra A B] [Algebra B B'] [IsScalarTower
 A B B'] (h : Function.Injective (algebraMap B B')) (x : B) : minpoly A (algebra
Map B B' x) = minpoly A x
参数：h : Function.Injective (algebraMap B B')；x : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minpoly.algHom_eq`：algHom_eq (f : B ->ₐ[A] B') (hf : Function.Injective 
f) (x : B) : minpoly A (f x) = minpoly A x
-/
theorem algebraMap_eq {B} [CommRing B] [Algebra A B] [Algebra B B'] [IsScalarTower A B B']
    (h : Function.Injective (algebraMap B B')) (x : B) :
    minpoly A (algebraMap B B' x) = minpoly A x :=
  algHom_eq (IsScalarTower.toAlgHom A B B') h x

@[simp]
/-
**minpoly.algEquiv_eq** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：algEquiv_eq (f : B ≃ₐ[A] B') (x : B) : minpoly A (f x) = minpoly A x
参数：f : B ≃ₐ[A] B'；x : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minpoly.algHom_eq`：algHom_eq (f : B ->ₐ[A] B') (hf : Function.Injective 
f) (x : B) : minpoly A (f x) = minpoly A x
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
-/
theorem algEquiv_eq (f : B ≃ₐ[A] B') (x : B) : minpoly A (f x) = minpoly A x :=
  algHom_eq (f : B →ₐ[A] B') f.injective x

section
variable (A x)

/-- An element is a root of its minimal polynomial. -/
@[simp]
/-
**minpoly.aeval** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：aeval : aeval x (minpoly A x) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Polynomial.degree_lt_wf`：degree_lt_wf : WellFounded fun p q : R[X] => de
gree p < degree q
· 使用定理 `WellFounded.min_mem`：min_mem {r : α -> α -> Prop} (H : WellFounded r) (s
 : Set α) (h : s.Nonempty) : H.min s h in s
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Polynomial.aeval_zero`：aeval_zero : aeval x (0 : R[X]) = 0

--- 原说明 ---
An element is a root of its minimal polynomial.
-/
theorem aeval : aeval x (minpoly A x) = 0 := by
  delta minpoly
  split_ifs with hx
  · exact (degree_lt_wf.min_mem _ hx).2
  · exact aeval_zero _

/-- Given any `f : B →ₐ[A] B'` and any `x : L`, the minimal polynomial of `x` vanishes at `f x`. -/
@[simp]
/-
**minpoly.aeval_algHom** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：aeval_algHom (f : B ->ₐ[A] B') (x : B) : (Polynomial.aeval (f x)) (minpoly
 A x) = 0
参数：f : B ->ₐ[A] B'；x : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_algHom`：aeval_algHom (f : A ->ₐ[R] B) (x : A) : aeval (
f x) = f.comp (aeval x)
· 使用定理 `AlgHom.coe_comp`：coe_comp (φ₁ : B ->ₐ[R] C) (φ₂ : A ->ₐ[R] B) : ⇑(φ₁.com
p φ₂) = φ₁ ∘ φ₂
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …

--- 原说明 ---
Given any `f : B →ₐ[A] B'` and any `x : L`, the minimal polynomial of `x` vanish
es at `f x`.
-/
theorem aeval_algHom (f : B →ₐ[A] B') (x : B) : (Polynomial.aeval (f x)) (minpoly A x) = 0 := by
  rw [Polynomial.aeval_algHom, AlgHom.coe_comp, comp_apply, aeval, map_zero]

/-- A minimal polynomial is not `1`. -/
/-
**minpoly.ne_one** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：ne_one [Nontrivial B] : minpoly A x != 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
A minimal polynomial is not `1`.
-/
theorem ne_one [Nontrivial B] : minpoly A x ≠ 1 := by
  intro h
  refine (one_ne_zero : (1 : B) ≠ 0) ?_
  simpa using congr_arg (Polynomial.aeval x) h
/-
**minpoly.map_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：map_ne_one [Nontrivial B] {R : Type*} [Semiring R] [Nontrivial R] (f : A -
>+* R) : (minpoly A x).map f != 1
参数：f : A ->+* R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Polynomial.Monic.eq_one_of_map_eq_one`：eq_one_of_map_eq_one {S : Type*} 
[Semiring S] [Nontrivial S] (f : R ->+* S) (hp : p.Monic) (map_eq : p.map f = 1)
 : p = 1
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `minpoly.ne_one`：ne_one [Nontrivial B] : minpoly A x != 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `minpoly.eq_zero`：eq_zero (hx : ¬IsIntegral A x) : minpoly A x = 0
· 使用定理 `Polynomial.map_zero`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [in
st_1 : Semiring S] (f : R →+* S), Polynomial.map f 0 = 0
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
-/
theorem map_ne_one [Nontrivial B] {R : Type*} [Semiring R] [Nontrivial R] (f : A →+* R) :
    (minpoly A x).map f ≠ 1 := by
  by_cases hx : IsIntegral A x
  · exact mt ((monic hx).eq_one_of_map_eq_one f) (ne_one A x)
  · rw [eq_zero hx, Polynomial.map_zero]
    exact zero_ne_one

/-- A minimal polynomial is not a unit. -/
/-
**minpoly.not_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：not_isUnit [Nontrivial B] : ¬IsUnit (minpoly A x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.domain_nontrivial`：domain_nontrivial [Nontrivial β] : Nontrivial
 α
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Polynomial.Monic.eq_one_of_isUnit`：∀ {R : Type u} [inst : Semiring R] {p
 : Polynomial R}, p.Monic → IsUnit p → p = 1
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `minpoly.ne_one`：ne_one [Nontrivial B] : minpoly A x != 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `minpoly.eq_zero`：eq_zero (hx : ¬IsIntegral A x) : minpoly A x = 0
· 使用定理 `not_isUnit_zero`：not_isUnit_zero [Nontrivial M₀] : ¬IsUnit (0 : M₀)

--- 原说明 ---
A minimal polynomial is not a unit.
-/
theorem not_isUnit [Nontrivial B] : ¬IsUnit (minpoly A x) := by
  have : Nontrivial A := (algebraMap A B).domain_nontrivial
  by_cases hx : IsIntegral A x
  · exact mt (monic hx).eq_one_of_isUnit (ne_one A x)
  · rw [eq_zero hx]
    exact not_isUnit_zero
/-
**minpoly.mem_range_of_degree_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：mem_range_of_degree_eq_one (hx : (minpoly A x).degree = 1) : x in (algebra
Map A B).range
参数：hx : (minpoly A x).degree = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用引理 `WithBot.bot_lt_coe`：bot_lt_coe (a : α) : ⊥ < (a : WithBot α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithBot.coe_one`：∀ {α : Type u} [inst : One α], ↑1 = 1
· 使用定理 `Polynomial.degree_zero`：degree_zero : degree (0 : R[X]) = ⊥
· 使用定理 `minpoly.eq_zero`：eq_zero (hx : ¬IsIntegral A x) : minpoly A x = 0
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `eq_neg_iff_add_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a = -b ↔ a + b = 0
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `Polynomial.aeval_add`：aeval_add : aeval x (p + q) = aeval x p + aeval x 
q
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Polynomial.C_1`：C_1 : C (1 : R) = 1
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `Polynomial.eq_X_add_C_of_degree_eq_one`：eq_X_add_C_of_degree_eq_one (h :
 degree p = 1) : p = C p.leadingCoeff * X + C (p.coeff 0)
-/
theorem mem_range_of_degree_eq_one (hx : (minpoly A x).degree = 1) :
    x ∈ (algebraMap A B).range := by
  have h : IsIntegral A x := by
    by_contra h
    rw [eq_zero h, degree_zero, ← WithBot.coe_one] at hx
    exact ne_of_lt (show ⊥ < ↑1 from WithBot.bot_lt_coe 1) hx
  have key := minpoly.aeval A x
  rw [eq_X_add_C_of_degree_eq_one hx, (minpoly.monic h).leadingCoeff, C_1, one_mul, aeval_add,
    aeval_C, aeval_X, ← eq_neg_iff_add_eq_zero, ← map_neg] at key
  exact ⟨-(minpoly A x).coeff 0, key.symm⟩

/-- The defining property of the minimal polynomial of an element `x`:
it is the monic polynomial with smallest degree that has `x` as its root. -/
/-
**minpoly.min** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：min {p : A[X]} (pmonic : p.Monic) (hp : Polynomial.aeval x p = 0) : degree
 (minpoly A x) <= degree p
参数：pmonic : p.Monic；hp : Polynomial.aeval x p = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `WellFounded.not_lt_min`：not_lt_min {r : α -> α -> Prop} (H : WellFounded
 r) (s : Set α) {x} (hx : x in s) : ¬r x (H.min s ⟨x, hx⟩)
· 使用定理 `Polynomial.degree_lt_wf`：degree_lt_wf : WellFounded fun p q : R[X] => de
gree p < degree q
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
The defining property of the minimal polynomial of an element `x`:
it is the monic polynomial with smallest degree that has `x` as its root.
-/
theorem min {p : A[X]} (pmonic : p.Monic) (hp : Polynomial.aeval x p = 0) :
    degree (minpoly A x) ≤ degree p := by
  delta minpoly; split_ifs with hx
  · refine le_of_not_gt <| degree_lt_wf.not_lt_min _ ?_
    exact ⟨pmonic, hp⟩
  · simp only [degree_zero, bot_le]
/-
**minpoly.unique'** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：unique' {p : A[X]} (hm : p.Monic) (hp : Polynomial.aeval x p = 0) (hl : fo
rall q : A[X], degree q < degree p -> q = 0 ∨ Polynomial.aeval x q != 0) : p = m
inpoly A x
参数：hm : p.Monic；hp : Polynomial.aeval x p = 0；hl : forall q : A[X], degree q < d
egree p -> q = 0 ∨ Polynomial.aeval x q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Polynomial.degree_modByMonic_lt`：degree_modByMonic_lt [Nontrivial R] : f
orall (p : R[X]) {q : R[X]} (_hq : Monic q), degree (p %ₘ q) < degree q | p, q, 
hq => letI
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.modByMonic_eq_zero_iff_dvd`：modByMonic_eq_zero_iff_dvd (hq : 
Monic q) : p %ₘ q = 0 ↔ q ∣ p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `minpoly.ne_zero`：ne_zero [Nontrivial A] (hx : IsIntegral A x) : minpoly 
A x != 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `Polynomial.leadingCoeff_mul_monic`：leadingCoeff_mul_monic {p q : R[X]} (
hq : Monic q) : leadingCoeff (p * q) = leadingCoeff p
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Nat.le_of_add_le_add_left`：∀ {a b c : ℕ}, a + b ≤ a + c → b ≤ c
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Polynomial.Monic.natDegree_mul'`：∀ {R : Type u} [inst : Semiring R] {p q
 : Polynomial R}, p.Monic → q ≠ 0 → (p * q).natDegree = p.natDegree + q.natDegre
e
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Polynomial.natDegree_le_natDegree`：natDegree_le_natDegree [Semiring S] {
q : S[X]} (hpq : p.degree <= q.degree) : p.natDegree <= q.natDegree
· 使用定理 `minpoly.min`：min {p : A[X]} (pmonic : p.Monic) (hp : Polynomial.aeval x 
p = 0) : degree (minpoly A x) <= degree p
· 使用定理 `Polynomial.eq_C_of_natDegree_le_zero`：eq_C_of_natDegree_le_zero (h : nat
Degree p <= 0) : p = C (coeff p 0)
· 使用定理 `Nat.eq_zero_of_le_zero`：∀ {n : ℕ}, n ≤ 0 → n = 0
· 使用定理 `Polynomial.leadingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Po
lynomial R), p.leadingCoeff = p.coeff p.natDegree
· 使用定理 `Polynomial.C_1`：C_1 : C (1 : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.aeval_modByMonic_eq_self_of_root`：aeval_modByMonic_eq_self_of
_root [Algebra R S] {p q : R[X]} {x : S} (hx : aeval x q = 0) : aeval x (p %ₘ q)
 = aeval x p
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
-/
theorem unique' {p : A[X]} (hm : p.Monic) (hp : Polynomial.aeval x p = 0)
    (hl : ∀ q : A[X], degree q < degree p → q = 0 ∨ Polynomial.aeval x q ≠ 0) :
    p = minpoly A x := by
  nontriviality A
  have hx : IsIntegral A x := ⟨p, hm, hp⟩
  obtain h | h := hl _ ((minpoly A x).degree_modByMonic_lt hm)
  swap
  · exact (h <| (aeval_modByMonic_eq_self_of_root hp).trans <| aeval A x).elim
  obtain ⟨r, hr⟩ := (modByMonic_eq_zero_iff_dvd hm).1 h
  rw [hr]
  have hlead := congr_arg leadingCoeff hr
  rw [mul_comm, leadingCoeff_mul_monic hm, (monic hx).leadingCoeff] at hlead
  have : natDegree r ≤ 0 := by
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact ne_zero hx (mul_zero p ▸ hr)
    apply_fun natDegree at hr
    rw [hm.natDegree_mul' hr0] at hr
    apply Nat.le_of_add_le_add_left
    rw [add_zero]
    exact hr.symm.trans_le (natDegree_le_natDegree <| min A x hm hp)
  rw [eq_C_of_natDegree_le_zero this, ← Nat.eq_zero_of_le_zero this, ← leadingCoeff, ← hlead, C_1,
    mul_one]

open Polynomial in
/-- If a monic polynomial `p : A[X]` of degree `n` annihilates an element `x` in an `A`-algebra `B`,
such that `{xⁱ | 0 ≤ i < n}` is linearly independent over `A`, then `p` is the minimal polynomial
of `x` over `A`. -/
/-
**minpoly.eq_of_linearIndependent** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：eq_of_linearIndependent {p : A[X]} (monic : p.Monic) (hp0 : p.aeval x = 0)
 (n : Nat) (hpn : p.degree = n) (ind : LinearIndependent A fun i : Fin n => x ^ 
i.val) : minpoly A x = p
参数：monic : p.Monic；hp0 : p.aeval x = 0；n : Nat；hpn : p.degree = n；ind : LinearIn
dependent A fun i : Fin n => x ^ i.val。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `minpoly.unique'`：unique' {p : A[X]} (hm : p.Monic) (hp : Polynomial.aeva
l x p = 0) (hl : forall q : A[X], degree q < degree p -> q = 0 ∨ Polynomial.aeva
l x q…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fintype.linearIndependent_iff`：Fintype.linearIndependent_iff [Fintype ι]
 : LinearIndependent R v ↔ forall g : ι -> R, ∑ i, g i • v i = 0 -> forall i, g 
i = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_range`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ} (f :
 ℕ → M), ∑ i ∈ Finset.range n, f i = ∑ i, f ↑i
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Polynomial.aeval_monomial`：aeval_monomial {n : Nat} {r : R} : aeval x (m
onomial n r) = algebraMap _ _ r * x ^ n
· 使用定理 `Polynomial.as_sum_range'`：as_sum_range' (p : R[X]) (n : Nat) (hn : p.nat
Degree < n) : p = ∑ i in range n, monomial i (coeff p i)
· 使用定理 `Polynomial.natDegree_lt_iff_degree_lt`：natDegree_lt_iff_degree_lt (hp : 
p != 0) : p.natDegree < n ↔ p.degree < ↑n
· 使用定理 `Polynomial.coeff_eq_zero_of_degree_lt`：coeff_eq_zero_of_degree_lt (h : d
egree p < n) : coeff p n = 0
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b

--- 原说明 ---
If a monic polynomial `p : A[X]` of degree `n` annihilates an element `x` in an 
`A`-algebra `B`,
such that `{xⁱ | 0 ≤ i < n}` is linearly independent over `A`, then `p` is the m
inimal polynomial
of `x` over `A`.
-/
theorem eq_of_linearIndependent {p : A[X]} (monic : p.Monic) (hp0 : p.aeval x = 0)
    (n : ℕ) (hpn : p.degree = n) (ind : LinearIndependent A fun i : Fin n ↦ x ^ i.val) :
    minpoly A x = p :=
  .symm <| unique' _ _ monic hp0 fun q lt ↦ or_iff_not_imp_left.mpr fun ne hq ↦ ne <| ext fun i ↦ by
    rw [q.as_sum_range' _ ((natDegree_lt_iff_degree_lt ne).mpr (hpn ▸ lt))] at hq
    obtain lt | le := lt_or_ge i n
    · simpa using Fintype.linearIndependent_iff.mp ind (q.coeff ·)
        (by simpa [Finset.sum_range, Algebra.smul_def] using hq) ⟨i, lt⟩
    · exact coeff_eq_zero_of_degree_lt ((hpn ▸ lt).trans_le <| WithBot.coe_le_coe.mpr le)

@[nontriviality]
/-
**minpoly.subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：subsingleton [Subsingleton B] : minpoly A x = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `minpoly.min`：min {p : A[X]} (pmonic : p.Monic) (hp : Polynomial.aeval x 
p = 0) : degree (minpoly A x) <= degree p
· 使用定理 `Polynomial.monic_one`：monic_one : Monic (1 : R[X])
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.degree_le_zero_iff_eq_one`：degree_le_zero_iff_eq_one (h
p : p.Monic) : p.degree <= 0 ↔ p = 1
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eval₂_one`：eval₂_one : (1 : R[X]).eval₂ f x = 1
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Polynomial.degree_one`：degree_one : degree (1 : R[X]) = (0 : WithBot Nat
)
-/
theorem subsingleton [Subsingleton B] : minpoly A x = 1 := by
  nontriviality A
  have := minpoly.min A x monic_one (Subsingleton.elim _ _)
  rw [degree_one] at this
  rcases le_or_gt (minpoly A x).degree 0 with h | h
  · rwa [(monic ⟨1, monic_one, by simp [eq_iff_true_of_subsingleton]⟩ :
           (minpoly A x).Monic).degree_le_zero_iff_eq_one] at h
  · exact (this.not_gt h).elim

end

/-- The degree of a minimal polynomial, as a natural number, is positive. -/
/-
**minpoly.natDegree_pos** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：natDegree_pos [Nontrivial B] (hx : IsIntegral A x) : 0 < natDegree (minpol
y A x)
参数：hx : IsIntegral A x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Polynomial.eq_C_of_natDegree_eq_zero`：eq_C_of_natDegree_eq_zero (h : nat
Degree p = 0) : p = C (coeff p 0)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `Polynomial.C_1`：C_1 : C (1 : R) = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0

--- 原说明 ---
The degree of a minimal polynomial, as a natural number, is positive.
-/
theorem natDegree_pos [Nontrivial B] (hx : IsIntegral A x) : 0 < natDegree (minpoly A x) := by
  rw [pos_iff_ne_zero]
  intro ndeg_eq_zero
  have eq_one : minpoly A x = 1 := by
    rw [eq_C_of_natDegree_eq_zero ndeg_eq_zero]
    convert C_1 (R := A)
    simpa only [ndeg_eq_zero.symm] using! (monic hx).leadingCoeff
  simpa only [eq_one, map_one, one_ne_zero] using! aeval A x

/-- The degree of a minimal polynomial is positive. -/
/-
**minpoly.degree_pos** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：degree_pos [Nontrivial B] (hx : IsIntegral A x) : 0 < degree (minpoly A x)
参数：hx : IsIntegral A x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.natDegree_pos_iff_degree_pos`：natDegree_pos_iff_degree_pos : 
0 < natDegree p ↔ 0 < degree p
· 使用定理 `minpoly.natDegree_pos`：natDegree_pos [Nontrivial B] (hx : IsIntegral A x
) : 0 < natDegree (minpoly A x)

--- 原说明 ---
The degree of a minimal polynomial is positive.
-/
theorem degree_pos [Nontrivial B] (hx : IsIntegral A x) : 0 < degree (minpoly A x) :=
  natDegree_pos_iff_degree_pos.mp (natDegree_pos hx)

@[simp]
/-
**minpoly.aeval_modByMonic_minpoly** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：aeval_modByMonic_minpoly (p : A[X]) (x : B) : (p %ₘ minpoly A x).aeval x =
 p.aeval x
参数：p : A[X]；x : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.aeval_modByMonic_eq_self_of_root`：aeval_modByMonic_eq_self_of
_root [Algebra R S] {p q : R[X]} {x : S} (hx : aeval x q = 0) : aeval x (p %ₘ q)
 = aeval x p
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
-/
theorem aeval_modByMonic_minpoly (p : A[X]) (x : B) : (p %ₘ minpoly A x).aeval x = p.aeval x :=
  aeval_modByMonic_eq_self_of_root (minpoly.aeval ..)

section
variable [Nontrivial B]

open Polynomial in
/-
**minpoly.degree_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：degree_eq_one_iff : (minpoly A x).degree = 1 ↔ x in (algebraMap A B).range
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minpoly.mem_range_of_degree_eq_one`：mem_range_of_degree_eq_one (hx : (mi
npoly A x).degree = 1) : x in (algebraMap A B).range
· 使用定理 `Module.nontrivial`：∀ (R : Type u_5) (M : Type u_6) [inst : MonoidWithZer
o R] [Nontrivial M] [inst_2 : Zero M] [MulActionWithZero R M],   Nontrivial R
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `minpoly.min`：min {p : A[X]} (pmonic : p.Monic) (hp : Polynomial.aeval x 
p = 0) : degree (minpoly A x) <= degree p
· 使用定理 `Polynomial.monic_X_sub_C`：monic_X_sub_C (x : R) : Monic (X - C x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_sub`：aeval_sub {p q : R[X]} [Ring A] [Algebra R A] (x :
 A) : aeval x (p - q) = aeval x p - aeval x q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.degree_X_sub_C`：degree_X_sub_C (a : R) : degree (X - C a) = 1
· 使用定理 `Nat.WithBot.add_one_le_of_lt`：add_one_le_of_lt {n m : WithBot Nat} (h : 
n < m) : n + 1 <= m
· 使用定理 `minpoly.degree_pos`：degree_pos [Nontrivial B] (hx : IsIntegral A x) : 0 
< degree (minpoly A x)
· 使用定理 `isIntegral_algebraMap`：isIntegral_algebraMap {x : R} : IsIntegral R (alg
ebraMap R A x)
-/
theorem degree_eq_one_iff : (minpoly A x).degree = 1 ↔ x ∈ (algebraMap A B).range := by
  refine ⟨minpoly.mem_range_of_degree_eq_one _ _, ?_⟩
  rintro ⟨x, rfl⟩
  have := Module.nontrivial A B
  exact (degree_X_sub_C x ▸ minpoly.min A (algebraMap A B x) (monic_X_sub_C x) (by simp)).antisymm
    (Nat.WithBot.add_one_le_of_lt <| minpoly.degree_pos isIntegral_algebraMap)
/-
**minpoly.natDegree_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：natDegree_eq_one_iff : (minpoly A x).natDegree = 1 ↔ x in (algebraMap A B)
.range
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.degree_eq_iff_natDegree_eq_of_pos`：degree_eq_iff_natDegree_eq
_of_pos {p : R[X]} {n : Nat} (hn : 0 < n) : p.degree = n ↔ p.natDegree = n
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `minpoly.degree_eq_one_iff`：degree_eq_one_iff : (minpoly A x).degree = 1 
↔ x in (algebraMap A B).range
-/
theorem natDegree_eq_one_iff :
    (minpoly A x).natDegree = 1 ↔ x ∈ (algebraMap A B).range := by
  rw [← Polynomial.degree_eq_iff_natDegree_eq_of_pos zero_lt_one]
  exact degree_eq_one_iff
/-
**minpoly.two_le_natDegree_iff** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：two_le_natDegree_iff (int : IsIntegral A x) : 2 <= (minpoly A x).natDegree
 ↔ x ∉ (algebraMap A B).range
参数：int : IsIntegral A x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_not_comm`：iff_not_comm : (a ↔ ¬b) ↔ (b ↔ ¬a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `minpoly.natDegree_eq_one_iff`：natDegree_eq_one_iff : (minpoly A x).natDe
gree = 1 ↔ x in (algebraMap A B).range
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Eq.trans_lt`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a = b → b < c →
 a < c
· 使用引理 `one_lt_two`：one_lt_two [AddLeftStrictMono α] : (1 : α) < 2
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `Mathlib.Tactic.Linarith.eq_of_not_lt_of_not_gt`：eq_of_not_lt_of_not_gt {
α} [LinearOrder α] (a b : α) (h1 : ¬ a < b) (h2 : ¬ b < a) : a = b
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
（共 56 条，此处仅展示前 30 条）
-/
theorem two_le_natDegree_iff (int : IsIntegral A x) :
    2 ≤ (minpoly A x).natDegree ↔ x ∉ (algebraMap A B).range := by
  rw [iff_not_comm, ← natDegree_eq_one_iff, not_le]
  exact ⟨fun h ↦ h.trans_lt one_lt_two, fun h ↦ by linarith only [minpoly.natDegree_pos int, h]⟩
/-
**minpoly.two_le_natDegree_subalgebra** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：two_le_natDegree_subalgebra {B} [CommRing B] [Algebra A B] [Nontrivial B] 
{S : Subalgebra A B} {x : B} (int : IsIntegral S x) : 2 <= (minpoly S x).natDegr
ee ↔ x ∉ S
参数：int : IsIntegral S x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `minpoly.two_le_natDegree_iff`：two_le_natDegree_iff (int : IsIntegral A x
) : 2 <= (minpoly A x).natDegree ↔ x ∉ (algebraMap A B).range
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `Subtype.range_val_subtype`：range_val_subtype {p : α -> Prop} : range (Su
btype.val : Subtype p -> α) = { x | p x }
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem two_le_natDegree_subalgebra {B} [CommRing B] [Algebra A B] [Nontrivial B]
    {S : Subalgebra A B} {x : B} (int : IsIntegral S x) : 2 ≤ (minpoly S x).natDegree ↔ x ∉ S := by
  rw [two_le_natDegree_iff int, Iff.not]
  apply Set.ext_iff.mp Subtype.range_val_subtype

end

/-- If `B/A` is an injective ring extension, and `a` is an element of `A`,
then the minimal polynomial of `algebraMap A B a` is `X - C a`. -/
/-
**minpoly.eq_X_sub_C_of_algebraMap_inj** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：eq_X_sub_C_of_algebraMap_inj (a : A) (hf : Function.Injective (algebraMap 
A B)) : minpoly A (algebraMap A B a) = X - C a
参数：a : A；hf : Function.Injective (algebraMap A B)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `minpoly.unique'`：unique' {p : A[X]} (hm : p.Monic) (hp : Polynomial.aeva
l x p = 0) (hl : forall q : A[X], degree q < degree p -> q = 0 ∨ Polynomial.aeva
l x q…
· 使用定理 `Polynomial.monic_X_sub_C`：monic_X_sub_C (x : R) : Monic (X - C x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Polynomial.eq_C_of_natDegree_eq_zero`：eq_C_of_natDegree_eq_zero (h : nat
Degree p = 0) : p = C (coeff p 0)
· 使用定理 `Nat.lt_one_iff`：∀ {n : ℕ}, n < 1 ↔ n = 0
· 使用定理 `Polynomial.natDegree_X_sub_C`：natDegree_X_sub_C (x : R) : (X - C x).natD
egree = 1
· 使用定理 `Polynomial.natDegree_lt_natDegree_iff`：natDegree_lt_natDegree_iff (hp : 
p != 0) : natDegree p < natDegree q ↔ degree p < degree q
· 使用定理 `map_ne_zero_iff`：∀ {R : Type u_10} {S : Type u_11} {F : Type u_12} [inst
 : Zero R] [inst_1 : Zero S] [inst_2 : FunLike F R S]   [ZeroHomClass F R S] (f 
: F),…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Polynomial.C_ne_zero`：C_ne_zero : C a != 0 ↔ a != 0

--- 原说明 ---
If `B/A` is an injective ring extension, and `a` is an element of `A`,
then the minimal polynomial of `algebraMap A B a` is `X - C a`.
-/
theorem eq_X_sub_C_of_algebraMap_inj (a : A) (hf : Function.Injective (algebraMap A B)) :
    minpoly A (algebraMap A B a) = X - C a := by
  nontriviality A
  refine (unique' A _ (monic_X_sub_C a) ?_ ?_).symm
  · rw [map_sub, aeval_C, aeval_X, sub_self]
  simp_rw [or_iff_not_imp_left]
  intro q hl h0
  rw [← natDegree_lt_natDegree_iff h0, natDegree_X_sub_C, Nat.lt_one_iff] at hl
  rw [eq_C_of_natDegree_eq_zero hl] at h0 ⊢
  rwa [aeval_C, map_ne_zero_iff _ hf, ← C_ne_zero]

/-- If `a` strictly divides the minimal polynomial of `x`, then `x` cannot be a root for `a`. -/
/-
**minpoly.aeval_ne_zero_of_dvdNotUnit_minpoly** 是 Mathlib 中的一个定理，位于命名空间 `minpoly
`。
形式化陈述：aeval_ne_zero_of_dvdNotUnit_minpoly {a : A[X]} (hx : IsIntegral A x) (hamo
nic : a.Monic) (hdvd : DvdNotUnit a (minpoly A x)) : Polynomial.aeval x a != 0
参数：hx : IsIntegral A x；hamonic : a.Monic；hdvd : DvdNotUnit a (minpoly A x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `minpoly.min`：min {p : A[X]} (pmonic : p.Monic) (hp : Polynomial.aeval x 
p = 0) : degree (minpoly A x) <= degree p
· 使用定理 `Polynomial.degree_lt_degree`：degree_lt_degree (h : natDegree p < natDegr
ee q) : degree p < degree q
· 使用定理 `Polynomial.Monic.of_mul_monic_left`：∀ {R : Type u} [inst : Semiring R] {
p q : Polynomial R}, p.Monic → (p * q).Monic → q.Monic
· 使用定理 `Eq.subst`：∀ {α : Sort u} {motive : α → Prop} {a b : α}, a = b → motive a
 → motive b
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.natDegree_mul`：natDegree_mul (hp : p.Monic) (hq : q.Mon
ic) : (p * q).natDegree = p.natDegree + q.natDegree
· 使用定理 `lt_add_of_pos_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
LT α] [AddLeftStrictMono α] (a : α) {b : α}, 0 < b → a < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Polynomial.eq_C_of_natDegree_le_zero`：eq_C_of_natDegree_le_zero (h : nat
Degree p <= 0) : p = C (coeff p 0)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.eq_zero_of_le_zero`：∀ {n : ℕ}, n ≤ 0 → n = 0
· 使用定理 `Polynomial.leadingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Po
lynomial R), p.leadingCoeff = p.coeff p.natDegree
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `Polynomial.C_1`：C_1 : C (1 : R) = 1
· 使用定理 `isUnit_one`：isUnit_one [Monoid M] : IsUnit (1 : M)

--- 原说明 ---
If `a` strictly divides the minimal polynomial of `x`, then `x` cannot be a root
 for `a`.
-/
theorem aeval_ne_zero_of_dvdNotUnit_minpoly {a : A[X]} (hx : IsIntegral A x) (hamonic : a.Monic)
    (hdvd : DvdNotUnit a (minpoly A x)) : Polynomial.aeval x a ≠ 0 := by
  refine fun ha => (min A x hamonic ha).not_gt (degree_lt_degree ?_)
  obtain ⟨_, c, hu, he⟩ := hdvd
  have hcm := hamonic.of_mul_monic_left (he.subst <| monic hx)
  rw [he, hamonic.natDegree_mul hcm]
  -- TODO: port Nat.lt_add_of_zero_lt_left from lean3 core
  apply lt_add_of_pos_right
  refine (lt_of_not_ge fun h => hu ?_)
  rw [eq_C_of_natDegree_le_zero h, ← Nat.eq_zero_of_le_zero h, ← leadingCoeff, hcm.leadingCoeff,
    C_1]
  exact isUnit_one

section IsDomain

variable [IsDomain A] [IsDomain B]

/-- A minimal polynomial is irreducible. -/
/-
**minpoly.irreducible** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：irreducible (hx : IsIntegral A x) : Irreducible (minpoly A x)
参数：hx : IsIntegral A x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Polynomial.irreducible_of_monic`：irreducible_of_monic (hp : p.Monic) (hp
1 : p != 1) : Irreducible p ↔ forall f g : R[X], f.Monic -> g.Monic -> f * g = p
 -> f = 1 ∨ g = 1
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `minpoly.ne_one`：ne_one [Nontrivial B] : minpoly A x != 1
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.Monic.isUnit_iff`：∀ {R : Type u} [inst : Semiring R] {p : Pol
ynomial R}, p.Monic → (IsUnit p ↔ p = 1)
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `Polynomial.aeval_mul`：aeval_mul : aeval x (p * q) = aeval x p * aeval x 
q
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `minpoly.aeval_ne_zero_of_dvdNotUnit_minpoly`：aeval_ne_zero_of_dvdNotUnit
_minpoly {a : A[X]} (hx : IsIntegral A x) (hamonic : a.Monic) (hdvd : DvdNotUnit
 a (minpoly A x)) : Polynomial.ae…
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
A minimal polynomial is irreducible.
-/
theorem irreducible (hx : IsIntegral A x) : Irreducible (minpoly A x) := by
  refine (irreducible_of_monic (monic hx) <| ne_one A x).2 fun f g hf hg he => ?_
  rw [← hf.isUnit_iff, ← hg.isUnit_iff]
  by_contra! h
  have heval := congr_arg (Polynomial.aeval x) he
  rw [aeval A x, aeval_mul, mul_eq_zero] at heval
  rcases heval with heval | heval
  · exact aeval_ne_zero_of_dvdNotUnit_minpoly hx hf ⟨hf.ne_zero, g, h.2, he.symm⟩ heval
  · refine aeval_ne_zero_of_dvdNotUnit_minpoly hx hg ⟨hg.ne_zero, f, h.1, ?_⟩ heval
    rw [mul_comm, he]

end IsDomain

end CommRing

end minpoly

