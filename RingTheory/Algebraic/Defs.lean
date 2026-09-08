/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Algebraic elements and algebraic extensions

An element of an R-algebra is algebraic over R if it is the root of a nonzero polynomial.
An R-algebra is algebraic over R if and only if all its elements are algebraic over R.

## Main definitions

* `IsAlgebraic`: algebraic elements of an algebra.
* `Transcendental`: transcendental elements of an algebra are those that are not algebraic.
* `Subalgebra.IsAlgebraic`: a subalgebra is algebraic if all its elements are algebraic.
* `Algebra.IsAlgebraic`: an algebra is algebraic if all its elements are algebraic.
* `Algebra.Transcendental`: an algebra is transcendental if some element is transcendental.

## Main results

* `transcendental_iff`: an element `x : A` is transcendental over `R` iff out of `R[X]`
  only the zero polynomial evaluates to 0 at `x`.
* `Subalgebra.isAlgebraic_iff`: a subalgebra is algebraic iff it is algebraic as an algebra.
-/

@[expose] public section

assert_not_exists IsIntegralClosure LinearIndependent IsLocalRing MvPolynomial

universe u v w
open Polynomial

section

variable (R : Type u) {A : Type v} [CommRing R] [Ring A] [Algebra R A]

/-- An element of an R-algebra is algebraic over R if it is a root of a nonzero polynomial
with coefficients in R. -/
@[stacks 09GC "Algebraic elements"]
/-
**IsAlgebraic** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsAlgebraic (x : A) : Prop
参数：x : A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element of an R-algebra is algebraic over R if it is a root of a nonzero poly
nomial
with coefficients in R.
-/
def IsAlgebraic (x : A) : Prop :=
  ∃ p : R[X], p ≠ 0 ∧ aeval x p = 0

/-- An element of an R-algebra is transcendental over R if it is not algebraic over R. -/
/-
**Transcendental** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Transcendental (x : A) : Prop
参数：x : A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element of an R-algebra is transcendental over R if it is not algebraic over 
R.
-/
def Transcendental (x : A) : Prop :=
  ¬IsAlgebraic R x

variable {R}

/-- An element `x` is transcendental over `R` if and only if for any polynomial `p`,
`Polynomial.aeval x p = 0` implies `p = 0`. This is similar to `algebraicIndependent_iff`. -/
/-
**transcendental_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：transcendental_iff {x : A} : Transcendental R x ↔ forall p : R[X], aeval x
 p = 0 -> p = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Transcendental.eq_1`：∀ (R : Type u) {A : Type v} [inst : CommRing R] [in
st_1 : Ring A] [inst_2 : Algebra R A] (x : A),   Transcendental R x = ¬IsAlgebra
ic R x
· 使用定理 `IsAlgebraic.eq_1`：∀ (R : Type u) {A : Type v} [inst : CommRing R] [inst_
1 : Ring A] [inst_2 : Algebra R A] (x : A),   IsAlgebraic R x = ∃ p, p ≠ 0 ∧ (Po
lynomi…
· 使用定理 `not_exists`：∀ {α : Sort u_1} {p : α → Prop}, (¬∃ x, p x) ↔ ∀ (x : α), ¬p
 x
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.not_and_iff_not_or_not'`：∀ {b a : Prop} [Decidable b], ¬(a ∧ b
) ↔ ¬a ∨ ¬b
· 使用定理 `Decidable.of_not_not`：∀ {p : Prop} [Decidable p], ¬¬p → p
· 使用定理 `Decidable.not_or_of_imp`：∀ {a b : Prop} [Decidable a], (a → b) → ¬a ∨ b

--- 原说明 ---
An element `x` is transcendental over `R` if and only if for any polynomial `p`,
`Polynomial.aeval x p = 0` implies `p = 0`. This is similar to `algebraicIndepen
dent_iff`.
-/
theorem transcendental_iff {x : A} :
    Transcendental R x ↔ ∀ p : R[X], aeval x p = 0 → p = 0 := by
  rw [Transcendental, IsAlgebraic, not_exists]
  congr! 1; tauto

/-- A subalgebra is algebraic if all its elements are algebraic. -/
/-
**Subalgebra.IsAlgebraic** 是 Mathlib 中的一个定义，位于命名空间 `Subalgebra`。
形式化陈述：{R : Type u} → {A : Type v} → [inst : CommRing R] → [inst_1 : Ring A] → [i
nst_2 : Algebra R A] → Subalgebra R A → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subalgebra is algebraic if all its elements are algebraic.
-/
protected def Subalgebra.IsAlgebraic (S : Subalgebra R A) : Prop :=
  ∀ x ∈ S, IsAlgebraic R x

variable (R A) in
/-- An algebra is algebraic if all its elements are algebraic. -/
@[stacks 09GC "Algebraic extensions"]
/-
**Algebra.IsAlgebraic** 是 Mathlib 中的一个归纳类型，位于命名空间 `Algebra`。
形式化陈述：(R : Type u) → (A : Type v) → [inst : CommRing R] → [inst_1 : Ring A] → [A
lgebra R A] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An algebra is algebraic if all its elements are algebraic.
-/
protected class Algebra.IsAlgebraic : Prop where
  isAlgebraic : ∀ x : A, IsAlgebraic R x

variable (R A) in
/-- An algebra is transcendental if some element is transcendental. -/
/-
**Algebra.Transcendental** 是 Mathlib 中的一个归纳类型，位于命名空间 `Algebra`。
形式化陈述：(R : Type u) → (A : Type v) → [inst : CommRing R] → [inst_1 : Ring A] → [A
lgebra R A] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An algebra is transcendental if some element is transcendental.
-/
protected class Algebra.Transcendental : Prop where
  transcendental : ∃ x : A, Transcendental R x

variable (R A) in
/-
**Algebra.nontrivial_of_isAlgebraic** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.nontrivial_of_isAlgebraic [Algebra.IsAlgebraic R A] : Nontrivial R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…
· 使用定理 `Polynomial.Nontrivial.of_polynomial_ne`：∀ {R : Type u} [inst : Semiring 
R] {p q : Polynomial R}, p ≠ q → Nontrivial R
-/
lemma Algebra.nontrivial_of_isAlgebraic [Algebra.IsAlgebraic R A] : Nontrivial R := by
  obtain ⟨p, hp, -⟩ := Algebra.IsAlgebraic.isAlgebraic (R := R) (0 : A)
  exact .of_polynomial_ne hp
/-
**Algebra.isAlgebraic_def** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.isAlgebraic_def : Algebra.IsAlgebraic R A ↔ forall x : A, IsAlgebr
aic R x
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Algebra.isAlgebraic_def : Algebra.IsAlgebraic R A ↔ ∀ x : A, IsAlgebraic R x :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩
/-
**Algebra.transcendental_def** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.transcendental_def : Algebra.Transcendental R A ↔ exists x : A, Tr
anscendental R x
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Algebra.transcendental_def : Algebra.Transcendental R A ↔ ∃ x : A, Transcendental R x :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩
/-
**Algebra.transcendental_iff_not_isAlgebraic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.transcendental_iff_not_isAlgebraic : Algebra.Transcendental R A ↔ 
¬ Algebra.IsAlgebraic R A
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
theorem Algebra.transcendental_iff_not_isAlgebraic :
    Algebra.Transcendental R A ↔ ¬ Algebra.IsAlgebraic R A := by
  simp [isAlgebraic_def, transcendental_def, Transcendental]

/-- A subalgebra is algebraic if and only if it is algebraic as an algebra. -/
/-
**Subalgebra.isAlgebraic_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subalgebra.isAlgebraic_iff (S : Subalgebra R A) : S.IsAlgebraic ↔ Algebra.
IsAlgebraic R S
参数：S : Subalgebra R A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.forall'`：∀ {α : Sort u_1} {p : α → Prop} {q : (x : α) → p x → Pr
op}, (∀ (x : α) (h : p x), q x h) ↔ ∀ (x : { a // p a }), q ↑x ⋯
· 使用引理 `Algebra.isAlgebraic_def`：Algebra.isAlgebraic_def : Algebra.IsAlgebraic R
 A ↔ forall x : A, IsAlgebraic R x
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
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
· 使用定理 `Polynomial.aeval_algHom_apply`：aeval_algHom_apply {F : Type*} [FunLike F
 A B] [AlgHomClass F R A B] (f : F) (x : A) (p : R[X]) : aeval (f x) p = f (aeva
l x p)
· 使用定理 `Subalgebra.val_apply`：val_apply (x : S) : S.val x = (x : A)

--- 原说明 ---
A subalgebra is algebraic if and only if it is algebraic as an algebra.
-/
theorem Subalgebra.isAlgebraic_iff (S : Subalgebra R A) :
    S.IsAlgebraic ↔ Algebra.IsAlgebraic R S := by
  delta Subalgebra.IsAlgebraic
  rw [Subtype.forall', Algebra.isAlgebraic_def]
  refine forall_congr' fun x => exists_congr fun p => and_congr Iff.rfl ?_
  have h : Function.Injective S.val := Subtype.val_injective
  conv_rhs => rw [← h.eq_iff, map_zero]
  rw [← aeval_algHom_apply, S.val_apply]

/-- An algebra is algebraic if and only if it is algebraic as a subalgebra. -/
/-
**Algebra.isAlgebraic_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.isAlgebraic_iff : Algebra.IsAlgebraic R A ↔ (⊤ : Subalgebra R A).I
sAlgebraic
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
An algebra is algebraic if and only if it is algebraic as a subalgebra.
-/
theorem Algebra.isAlgebraic_iff : Algebra.IsAlgebraic R A ↔ (⊤ : Subalgebra R A).IsAlgebraic := by
  delta Subalgebra.IsAlgebraic
  simp only [Algebra.isAlgebraic_def, Algebra.mem_top, forall_prop_of_true]

end

