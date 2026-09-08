/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.RingTheory.Adjoin.Polynomial.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Polynomial.Tower
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Algebraic elements and algebraic extensions

An element of an R-algebra is algebraic over R if it is the root of a nonzero polynomial.
An R-algebra is algebraic over R if and only if all its elements are algebraic over R.
The main result in this file proves transitivity of algebraicity:
a tower of algebraic field extensions is algebraic.
-/

@[expose] public section

universe u v w

open Module Polynomial nonZeroDivisors

section

variable (R : Type u) {A : Type v} [CommRing R] [Ring A] [Algebra R A]

@[nontriviality]
/-
**is_transcendental_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：is_transcendental_of_subsingleton [Subsingleton R] (x : A) : Transcendenta
l R x
参数：x : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem is_transcendental_of_subsingleton [Subsingleton R] (x : A) : Transcendental R x :=
  fun ⟨p, h, _⟩ => h <| Subsingleton.elim p 0

variable {R}
/-
**IsAlgebraic.nontrivial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAlgebraic.nontrivial {a : A} (h : IsAlgebraic R a) : Nontrivial R
参数：h : IsAlgebraic R a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `is_transcendental_of_subsingleton`：is_transcendental_of_subsingleton [Su
bsingleton R] (x : A) : Transcendental R x
-/
theorem IsAlgebraic.nontrivial {a : A} (h : IsAlgebraic R a) : Nontrivial R := by
  contrapose! h
  apply is_transcendental_of_subsingleton

variable (R A)
/-
**Algebra.IsAlgebraic.nontrivial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.IsAlgebraic.nontrivial [alg : Algebra.IsAlgebraic R A] : Nontrivia
l R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgebraic.nontrivial`：IsAlgebraic.nontrivial {a : A} (h : IsAlgebraic 
R a) : Nontrivial R
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…
-/
theorem Algebra.IsAlgebraic.nontrivial [alg : Algebra.IsAlgebraic R A] : Nontrivial R :=
  (alg.1 0).nontrivial
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) Algebra.transcendental_of_subsingleton [Subsingleton R] :
    Algebra.Transcendental R A :=
  ⟨⟨0, is_transcendental_of_subsingleton R 0⟩⟩
/-
**Polynomial.transcendental_X** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Polynomial.transcendental_X : Transcendental R (X (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_X_left`：aeval_X_left : aeval (X : R[X]) = AlgHom.id R R
[X]
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem Polynomial.transcendental_X : Transcendental R (X (R := R)) := by
  simp [transcendental_iff]

variable {R A}
/-
**IsAlgebraic.of_aeval** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAlgebraic.of_aeval {r : A} (f : R[X]) (hf : f.natDegree != 0) (hf' : f.l
eadingCoeff in R⁰) (H : IsAlgebraic R (aeval r f)) : IsAlgebraic R r
参数：f : R[X]；hf : f.natDegree != 0；hf' : f.leadingCoeff in R⁰；H : IsAlgebraic R (
aeval r f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
· 使用定理 `mul_right_mem_nonZeroDivisors_eq_zero_iff`：mul_right_mem_nonZeroDivisors
_eq_zero_iff (hr : r in M₀⁰) : x * r = 0 ↔ x = 0
· 使用定理 `pow_mem`：∀ {M : Type u_3} {A : Type u_4} [inst : Monoid M] [inst_1 : Set
Like A M] [SubmonoidClass A M] {S : A} {x : M},   x ∈ S → ∀ (n : ℕ), x ^ n ∈ …
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Polynomial.coeff_comp_degree_mul_degree`：coeff_comp_degree_mul_degree (h
qd0 : natDegree q != 0) : coeff (p.comp q) (natDegree p * natDegree q) = leading
Coeff p * leadingCoeff q ^ na…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.aeval_comp`：aeval_comp {A : Type*} [Semiring A] [Algebra R A]
 (x : A) : aeval x (p.comp q) = aeval (aeval x q) p
-/
theorem IsAlgebraic.of_aeval {r : A} (f : R[X]) (hf : f.natDegree ≠ 0)
    (hf' : f.leadingCoeff ∈ R⁰) (H : IsAlgebraic R (aeval r f)) :
    IsAlgebraic R r := by
  obtain ⟨p, h1, h2⟩ := H
  have : (p.comp f).coeff (p.natDegree * f.natDegree) ≠ 0 := fun h ↦ h1 <| by
    rwa [coeff_comp_degree_mul_degree hf,
      mul_right_mem_nonZeroDivisors_eq_zero_iff (pow_mem hf' _),
      leadingCoeff_eq_zero] at h
  exact ⟨p.comp f, fun h ↦ this (by simp [h]), by rwa [aeval_comp]⟩
/-
**Transcendental.aeval** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Transcendental.aeval {r : A} (H : Transcendental R r) (f : R[X]) (hf : f.n
atDegree != 0) (hf' : f.leadingCoeff in R⁰) : Transcendental R (aeval r f)
参数：H : Transcendental R r；f : R[X]；hf : f.natDegree != 0；hf' : f.leadingCoeff in
 R⁰。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgebraic.of_aeval`：IsAlgebraic.of_aeval {r : A} (f : R[X]) (hf : f.na
tDegree != 0) (hf' : f.leadingCoeff in R⁰) (H : IsAlgebraic R (aeval r f)) : IsA
lgebraic R…
-/
theorem Transcendental.aeval {r : A} (H : Transcendental R r) (f : R[X]) (hf : f.natDegree ≠ 0)
    (hf' : f.leadingCoeff ∈ R⁰) :
    Transcendental R (aeval r f) := fun h ↦ H (h.of_aeval f hf hf')

/-- If `r : A` and `f : R[X]` are transcendental over `R`, then `Polynomial.aeval r f` is also
transcendental over `R`. For the converse, see `Transcendental.of_aeval` and
`transcendental_aeval_iff`. -/
/-
**Transcendental.aeval_of_transcendental** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Transcendental.aeval_of_transcendental {r : A} (H : Transcendental R r) {f
 : R[X]} (hf : Transcendental R f) : Transcendental R (Polynomial.aeval r f)
参数：H : Transcendental R r；hf : Transcendental R f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `transcendental_iff`：transcendental_iff {x : A} : Transcendental R x ↔ fo
rall p : R[X], aeval x p = 0 -> p = 0
· 使用定理 `Polynomial.comp_eq_aeval`：comp_eq_aeval : p.comp q = aeval q p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.aeval_comp`：aeval_comp {A : Type*} [Semiring A] [Algebra R A]
 (x : A) : aeval x (p.comp q) = aeval (aeval x q) p

--- 原说明 ---
If `r : A` and `f : R[X]` are transcendental over `R`, then `Polynomial.aeval r 
f` is also
transcendental over `R`. For the converse, see `Transcendental.of_aeval` and
`transcendental_aeval_iff`.
-/
theorem Transcendental.aeval_of_transcendental {r : A} (H : Transcendental R r)
    {f : R[X]} (hf : Transcendental R f) : Transcendental R (Polynomial.aeval r f) := by
  rw [transcendental_iff] at H hf ⊢
  intro p hp
  exact hf _ (H _ (by rwa [← aeval_comp, comp_eq_aeval] at hp))

/-- If `Polynomial.aeval r f` is transcendental over `R`, then `f : R[X]` is also
transcendental over `R`. In fact, the `r` is also transcendental over `R` provided that `R`
is a field (see `transcendental_aeval_iff`). -/
/-
**Transcendental.of_aeval** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Transcendental.of_aeval {r : A} {f : R[X]} (H : Transcendental R (Polynomi
al.aeval r f)) : Transcendental R f
参数：H : Transcendental R (Polynomial.aeval r f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `transcendental_iff`：transcendental_iff {x : A} : Transcendental R x ↔ fo
rall p : R[X], aeval x p = 0 -> p = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.aeval_comp`：aeval_comp {A : Type*} [Semiring A] [Algebra R A]
 (x : A) : aeval x (p.comp q) = aeval (aeval x q) p
· 使用定理 `Polynomial.comp_eq_aeval`：comp_eq_aeval : p.comp q = aeval q p
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
If `Polynomial.aeval r f` is transcendental over `R`, then `f : R[X]` is also
transcendental over `R`. In fact, the `r` is also transcendental over `R` provid
ed that `R`
is a field (see `transcendental_aeval_iff`).
-/
theorem Transcendental.of_aeval {r : A} {f : R[X]}
    (H : Transcendental R (Polynomial.aeval r f)) : Transcendental R f := by
  rw [transcendental_iff] at H ⊢
  intro p hp
  exact H p (by rw [← aeval_comp, comp_eq_aeval, hp, map_zero])
/-
**IsAlgebraic.of_aeval_of_transcendental** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAlgebraic.of_aeval_of_transcendental {r : A} {f : R[X]} (H : IsAlgebraic
 R (aeval r f)) (hf : Transcendental R f) : IsAlgebraic R r
参数：H : IsAlgebraic R (aeval r f)；hf : Transcendental R f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Transcendental.aeval_of_transcendental`：Transcendental.aeval_of_transcen
dental {r : A} (H : Transcendental R r) {f : R[X]} (hf : Transcendental R f) : T
ranscendental R (Polynomial.…
-/
theorem IsAlgebraic.of_aeval_of_transcendental {r : A} {f : R[X]}
    (H : IsAlgebraic R (aeval r f)) (hf : Transcendental R f) : IsAlgebraic R r := by
  contrapose H
  exact Transcendental.aeval_of_transcendental H hf
/-
**Polynomial.transcendental** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Polynomial.transcendental (f : R[X]) (hf : f.natDegree != 0) (hf' : f.lead
ingCoeff in R⁰) : Transcendental R f
参数：f : R[X]；hf : f.natDegree != 0；hf' : f.leadingCoeff in R⁰。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.aeval_X_left`：aeval_X_left : aeval (X : R[X]) = AlgHom.id R R
[X]
· 使用定理 `Transcendental.aeval`：Transcendental.aeval {r : A} (H : Transcendental R
 r) (f : R[X]) (hf : f.natDegree != 0) (hf' : f.leadingCoeff in R⁰) : Transcende
ntal R (ae…
· 使用定理 `Polynomial.transcendental_X`：Polynomial.transcendental_X : Transcendenta
l R (X (R
-/
theorem Polynomial.transcendental (f : R[X]) (hf : f.natDegree ≠ 0)
    (hf' : f.leadingCoeff ∈ R⁰) :
    Transcendental R f := by
  simpa using (transcendental_X R).aeval f hf hf'
/-
**isAlgebraic_iff_not_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isAlgebraic_iff_not_injective {x : A} : IsAlgebraic R x ↔ ¬Function.Inject
ive (Polynomial.aeval x : R[X] ->ₐ[R] A)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isAlgebraic_iff_not_injective {x : A} :
    IsAlgebraic R x ↔ ¬Function.Injective (Polynomial.aeval x : R[X] →ₐ[R] A) := by
  simp only [IsAlgebraic, injective_iff_map_eq_zero, not_forall, and_comm, exists_prop]

/-- An element `x` is transcendental over `R` if and only if the map `Polynomial.aeval x`
is injective. This is similar to `algebraicIndependent_iff_injective_aeval`. -/
/-
**transcendental_iff_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：transcendental_iff_injective {x : A} : Transcendental R x ↔ Function.Injec
tive (Polynomial.aeval x : R[X] ->ₐ[R] A)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not_left`：Iff.not_left (h : a ↔ ¬b) : ¬a ↔ b
· 使用定理 `isAlgebraic_iff_not_injective`：isAlgebraic_iff_not_injective {x : A} : I
sAlgebraic R x ↔ ¬Function.Injective (Polynomial.aeval x : R[X] ->ₐ[R] A)

--- 原说明 ---
An element `x` is transcendental over `R` if and only if the map `Polynomial.aev
al x`
is injective. This is similar to `algebraicIndependent_iff_injective_aeval`.
-/
theorem transcendental_iff_injective {x : A} :
    Transcendental R x ↔ Function.Injective (Polynomial.aeval x : R[X] →ₐ[R] A) :=
  isAlgebraic_iff_not_injective.not_left

/-- An element `x` is transcendental over `R` if and only if the kernel of the ring homomorphism
`Polynomial.aeval x` is the zero ideal. This is similar to `algebraicIndependent_iff_ker_eq_bot`. -/
/-
**transcendental_iff_ker_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：transcendental_iff_ker_eq_bot {x : A} : Transcendental R x ↔ RingHom.ker (
aeval (R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `transcendental_iff_injective`：transcendental_iff_injective {x : A} : Tra
nscendental R x ↔ Function.Injective (Polynomial.aeval x : R[X] ->ₐ[R] A)
· 使用定理 `RingHom.injective_iff_ker_eq_bot`：injective_iff_ker_eq_bot : Function.In
jective f ↔ ker f = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
An element `x` is transcendental over `R` if and only if the kernel of the ring 
homomorphism
`Polynomial.aeval x` is the zero ideal. This is similar to `algebraicIndependent
_iff_ker_eq_bot`.
-/
theorem transcendental_iff_ker_eq_bot {x : A} :
    Transcendental R x ↔ RingHom.ker (aeval (R := R) x) = ⊥ := by
  rw [transcendental_iff_injective, RingHom.injective_iff_ker_eq_bot]
/-
**Algebra.isAlgebraic_of_not_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.isAlgebraic_of_not_injective (h : ¬ Function.Injective (algebraMap
 R A)) : Algebra.IsAlgebraic R A where isAlgebraic a
参数：h : ¬ Function.Injective (algebraMap R A)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isAlgebraic_iff_not_injective`：isAlgebraic_iff_not_injective {x : A} : I
sAlgebraic R x ↔ ¬Function.Injective (Polynomial.aeval x : R[X] ->ₐ[R] A)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Polynomial.C_injective`：C_injective : Injective (C : R -> R[X])
-/
theorem Algebra.isAlgebraic_of_not_injective (h : ¬ Function.Injective (algebraMap R A)) :
    Algebra.IsAlgebraic R A where
  isAlgebraic a := isAlgebraic_iff_not_injective.mpr
    fun inj ↦ h <| by convert! inj.comp C_injective; ext; simp
/-
**Algebra.injective_of_transcendental** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.injective_of_transcendental [h : Algebra.Transcendental R A] : Fun
ction.Injective (algebraMap R A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `Algebra.isAlgebraic_of_not_injective`：Algebra.isAlgebraic_of_not_injecti
ve (h : ¬ Function.Injective (algebraMap R A)) : Algebra.IsAlgebraic R A where i
sAlgebraic a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.transcendental_iff_not_isAlgebraic`：Algebra.transcendental_iff_n
ot_isAlgebraic : Algebra.Transcendental R A ↔ ¬ Algebra.IsAlgebraic R A
-/
theorem Algebra.injective_of_transcendental [h : Algebra.Transcendental R A] :
    Function.Injective (algebraMap R A) := by
  rw [transcendental_iff_not_isAlgebraic] at h
  contrapose h
  exact isAlgebraic_of_not_injective h

end

section zero_ne_one

variable {R : Type u} {S : Type*} {A : Type v} [CommRing R]
variable [CommRing S] [Ring A] [Algebra R A] [Algebra R S] [Algebra S A]
variable [IsScalarTower R S A]

/-
**isAlgebraic_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isAlgebraic_zero [Nontrivial R] : IsAlgebraic R (0 : A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.X_ne_zero`：X_ne_zero [Nontrivial R] : (X : R[X]) != 0
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
-/
theorem isAlgebraic_zero [Nontrivial R] : IsAlgebraic R (0 : A) :=
  ⟨_, X_ne_zero, aeval_X 0⟩

/-- An element of `R` is algebraic, when viewed as an element of the `R`-algebra `A`. -/
/-
**isAlgebraic_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isAlgebraic_algebraMap [Nontrivial R] (x : R) : IsAlgebraic R (algebraMap 
R A x)
参数：x : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.X_sub_C_ne_zero`：X_sub_C_ne_zero (r : R) : X - C r != 0
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
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0

--- 原说明 ---
An element of `R` is algebraic, when viewed as an element of the `R`-algebra `A`
.
-/
theorem isAlgebraic_algebraMap [Nontrivial R] (x : R) : IsAlgebraic R (algebraMap R A x) :=
  ⟨_, X_sub_C_ne_zero x, by rw [map_sub, aeval_X, aeval_C, sub_self]⟩
/-
**isAlgebraic_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isAlgebraic_one [Nontrivial R] : IsAlgebraic R (1 : A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `isAlgebraic_algebraMap`：isAlgebraic_algebraMap [Nontrivial R] (x : R) : 
IsAlgebraic R (algebraMap R A x)
-/
theorem isAlgebraic_one [Nontrivial R] : IsAlgebraic R (1 : A) := by
  rw [← map_one (algebraMap R A)]
  exact isAlgebraic_algebraMap 1
/-
**isAlgebraic_natCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isAlgebraic_natCast [Nontrivial R] (n : Nat) : IsAlgebraic R (n : A)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `isAlgebraic_algebraMap`：isAlgebraic_algebraMap [Nontrivial R] (x : R) : 
IsAlgebraic R (algebraMap R A x)
-/
theorem isAlgebraic_natCast [Nontrivial R] (n : ℕ) : IsAlgebraic R (n : A) := by
  rw [← map_natCast (_ : R →+* A) n]
  exact isAlgebraic_algebraMap (Nat.cast n)
/-
**isAlgebraic_intCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isAlgebraic_intCast [Nontrivial R] (n : Int) : IsAlgebraic R (n : A)
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_intCast`：map_intCast [FunLike F α β] [RingHomClass F α β] (f : F) (n
 : Int) : f n = n
· 使用定理 `isAlgebraic_algebraMap`：isAlgebraic_algebraMap [Nontrivial R] (x : R) : 
IsAlgebraic R (algebraMap R A x)
-/
theorem isAlgebraic_intCast [Nontrivial R] (n : ℤ) : IsAlgebraic R (n : A) := by
  rw [← map_intCast (algebraMap R A)]
  exact isAlgebraic_algebraMap (Int.cast n)
/-
**isAlgebraic_ratCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isAlgebraic_ratCast (R : Type u) {A : Type v} [DivisionRing A] [Field R] [
Algebra R A] (n : Rat) : IsAlgebraic R (n : A)
参数：R : Type u；n : Rat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_ratCast`：map_ratCast [DivisionRing α] [DivisionRing β] [RingHomClass
 F α β] (f : F) (q : Rat) : f q = q
· 使用定理 `isAlgebraic_algebraMap`：isAlgebraic_algebraMap [Nontrivial R] (x : R) : 
IsAlgebraic R (algebraMap R A x)
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
-/
theorem isAlgebraic_ratCast (R : Type u) {A : Type v} [DivisionRing A] [Field R] [Algebra R A]
    (n : ℚ) : IsAlgebraic R (n : A) := by
  rw [← map_ratCast (algebraMap R A)]
  exact isAlgebraic_algebraMap (Rat.cast n)

@[deprecated (since := "2026-07-14")] alias isAlgebraic_nat := isAlgebraic_natCast
@[deprecated (since := "2026-07-14")] alias isAlgebraic_int := isAlgebraic_intCast
@[deprecated (since := "2026-07-14")] alias isAlgebraic_rat := isAlgebraic_ratCast
/-
**isAlgebraic_of_mem_rootSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isAlgebraic_of_mem_rootSet {R : Type u} {A : Type v} [CommRing R] [Field A
] [Algebra R A] {p : R[X]} {x : A} (hx : x in p.rootSet A) : IsAlgebraic R x
参数：hx : x in p.rootSet A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.ne_zero_of_mem_rootSet`：ne_zero_of_mem_rootSet {p : T[X]} [Co
mmRing S] [IsDomain S] [Algebra T S] {a : S} (h : a in p.rootSet S) : p != 0
· 使用定理 `Polynomial.aeval_eq_zero_of_mem_rootSet`：aeval_eq_zero_of_mem_rootSet {p
 : T[X]} [CommRing S] [IsDomain S] [Algebra T S] {a : S} (hx : a in p.rootSet S)
 : aeval a p = 0
-/
theorem isAlgebraic_of_mem_rootSet {R : Type u} {A : Type v} [CommRing R] [Field A] [Algebra R A]
    {p : R[X]} {x : A} (hx : x ∈ p.rootSet A) : IsAlgebraic R x :=
  ⟨p, ne_zero_of_mem_rootSet hx, aeval_eq_zero_of_mem_rootSet hx⟩

variable (S) in
/-
**IsLocalization.isAlgebraic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalization.isAlgebraic [Nontrivial R] (M : Submonoid R) [IsLocalizatio
n M S] : Algebra.IsAlgebraic R S where isAlgebraic x
参数：M : Submonoid R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `isAlgebraic_zero`：isAlgebraic_zero [Nontrivial R] : IsAlgebraic R (0 : A
)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.surj`：surj : forall z : S, exists x : R × M, z * algebraM
ap R S x.2 = algebraMap R S x.1
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.mk'_zero`：∀ {R : Type u_1} [inst : CommSemiring R] {M : S
ubmonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [i
nst_3 : IsLoc…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coeff_sub`：coeff_sub (p q : R[X]) (n : Nat) : coeff (p - q) n
 = coeff p n - coeff q n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.mul_coeff_zero`：mul_coeff_zero (p q : R[X]) : coeff (p * q) 0
 = coeff p 0 * coeff q 0
· 使用定理 `Polynomial.coeff_C_zero`：coeff_C_zero : coeff (C a) 0 = a
· 使用定理 `Polynomial.coeff_X_zero`：coeff_X_zero : coeff (X : R[X]) 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `IsLocalization.eq_mk'_iff_mul_eq`：∀ {R : Type u_1} [inst : CommSemiring 
R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebr
a R S] [inst_3 : IsLoc…
· 使用定理 `Polynomial.aeval_sub`：aeval_sub {p q : R[X]} [Ring A] [Algebra R A] (x :
 A) : aeval x (p - q) = aeval x p - aeval x q
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem IsLocalization.isAlgebraic [Nontrivial R] (M : Submonoid R) [IsLocalization M S] :
    Algebra.IsAlgebraic R S where
  isAlgebraic x := by
    obtain rfl | hx := eq_or_ne x 0
    · exact isAlgebraic_zero
    have ⟨⟨r, m⟩, h⟩ := surj M x
    refine ⟨C m.1 * X - C r, fun eq ↦ hx ?_, by simpa [sub_eq_zero, mul_comm x] using h⟩
    rwa [← eq_mk'_iff_mul_eq, show r = 0 by simpa using congr(coeff $eq 0), mk'_zero] at h

open IsScalarTower
/-
**IsAlgebraic.algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `IsAlgebraic`。
形式化陈述：∀ {R : Type u} {S : Type u_1} {A : Type v} [inst : CommRing R] [inst_1 : C
ommRing S] [inst_2 : Ring A]   [inst_3 : Algebra R A] [inst_4 : Algebra R S] [in
st_5 : Algebra S A] [IsScalarTower R S A] {a : S},   IsAlgebraic R a → IsAlgebra
ic R ((algebraMap S A) a)
参数：(algebraMap S A) a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_algebraMap_apply`：aeval_algebraMap_apply (x : A) (p : R
[X]) : aeval (algebraMap A B x) p = algebraMap A B (aeval x p)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
protected theorem IsAlgebraic.algebraMap {a : S} :
    IsAlgebraic R a → IsAlgebraic R (algebraMap S A a) := fun ⟨f, hf₁, hf₂⟩ =>
  ⟨f, hf₁, by rw [aeval_algebraMap_apply, hf₂, map_zero]⟩

section

variable {B : Type*} [Ring B] [Algebra R B]

/-- This is slightly more general than `IsAlgebraic.algebraMap` in that it
  allows noncommutative intermediate rings `A`. -/
/-
**IsAlgebraic.algHom** 是 Mathlib 中的一个定理，位于命名空间 `IsAlgebraic`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommRing R] [inst_1 : Ring A] [inst_2 
: Algebra R A] {B : Type u_2}   [inst_3 : Ring B] [inst_4 : Algebra R B] (f : A 
→ₐ[R] B) {a : A}, IsAlgebraic R a → IsAlgebraic R (f a)
参数：f : A →ₐ[R] B；f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_algHom`：aeval_algHom (f : A ->ₐ[R] B) (x : A) : aeval (
f x) = f.comp (aeval x)
· 使用定理 `AlgHom.comp_apply`：comp_apply (φ₁ : B ->ₐ[R] C) (φ₂ : A ->ₐ[R] B) (p : A
) : φ₁.comp φ₂ p = φ₁ (φ₂ p)
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
This is slightly more general than `IsAlgebraic.algebraMap` in that it
  allows noncommutative intermediate rings `A`.
-/
protected theorem IsAlgebraic.algHom (f : A →ₐ[R] B) {a : A}
    (h : IsAlgebraic R a) : IsAlgebraic R (f a) :=
  let ⟨p, hp, ha⟩ := h
  ⟨p, hp, by rw [aeval_algHom, f.comp_apply, ha, map_zero]⟩
/-
**isAlgebraic_algHom_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isAlgebraic_algHom_iff (f : A ->ₐ[R] B) (hf : Function.Injective f) {a : A
} : IsAlgebraic R (f a) ↔ IsAlgebraic R a
参数：f : A ->ₐ[R] B；hf : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.comp_apply`：comp_apply (φ₁ : B ->ₐ[R] C) (φ₂ : A ->ₐ[R] B) (p : A
) : φ₁.comp φ₂ p = φ₁ (φ₂ p)
· 使用定理 `Polynomial.aeval_algHom`：aeval_algHom (f : A ->ₐ[R] B) (x : A) : aeval (
f x) = f.comp (aeval x)
· 使用定理 `IsAlgebraic.algHom`：∀ {R : Type u} {A : Type v} [inst : CommRing R] [ins
t_1 : Ring A] [inst_2 : Algebra R A] {B : Type u_2}   [inst_3 : Ring B] [inst_4 
: Algebr…
-/
theorem isAlgebraic_algHom_iff (f : A →ₐ[R] B) (hf : Function.Injective f)
    {a : A} : IsAlgebraic R (f a) ↔ IsAlgebraic R a :=
  ⟨fun ⟨p, hp0, hp⟩ ↦ ⟨p, hp0, hf <| by rwa [map_zero, ← f.comp_apply, ← aeval_algHom]⟩,
    IsAlgebraic.algHom f⟩

section RingHom

omit [Algebra R S] [Algebra S A] [IsScalarTower R S A] [Algebra R B]
variable [Algebra S B] {FRS FAB : Type*}

section

variable [FunLike FRS R S] [RingHomClass FRS R S] [FunLike FAB A B] [RingHomClass FAB A B]
  (f : FRS) (g : FAB) {a : A}

/-
**IsAlgebraic.ringHom_of_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAlgebraic.ringHom_of_comp_eq (halg : IsAlgebraic R a) (hf : Function.Inj
ective f) (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)
) : IsAlgebraic S (g a)
参数：halg : IsAlgebraic R a；hf : Function.Injective f；h : RingHom.comp (algebraMap
 S B) f = RingHom.comp g (algebraMap R A)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.map_ne_zero_iff`：∀ {R : Type u} {S : Type v} [inst : Semiring
 R] {p : Polynomial R} [inst_1 : Semiring S] {f : R →+* S},   Function.Injective
 ⇑f → (Polynomia…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.map_aeval_eq_aeval_map`：map_aeval_eq_aeval_map {S T U : Type*
} [Semiring S] [CommSemiring T] [Semiring U] [Algebra R S] [Algebra T U] {φ : R 
->+* T} {ψ : S ->+* U} …
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem IsAlgebraic.ringHom_of_comp_eq (halg : IsAlgebraic R a)
    (hf : Function.Injective f)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    IsAlgebraic S (g a) := by
  obtain ⟨p, h1, h2⟩ := halg
  refine ⟨p.map f, (Polynomial.map_ne_zero_iff hf).2 h1, ?_⟩
  change aeval ((g : A →+* B) a) _ = 0
  rw [← map_aeval_eq_aeval_map h, h2, map_zero]
/-
**Transcendental.of_ringHom_of_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Transcendental.of_ringHom_of_comp_eq (H : Transcendental S (g a)) (hf : Fu
nction.Injective f) (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algeb
raMap R A)) : Transcendental R a
参数：H : Transcendental S (g a)；hf : Function.Injective f；h : RingHom.comp (algebr
aMap S B) f = RingHom.comp g (algebraMap R A)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgebraic.ringHom_of_comp_eq`：IsAlgebraic.ringHom_of_comp_eq (halg : I
sAlgebraic R a) (hf : Function.Injective f) (h : RingHom.comp (algebraMap S B) f
 = RingHom.comp g (a…
-/
theorem Transcendental.of_ringHom_of_comp_eq (H : Transcendental S (g a))
    (hf : Function.Injective f)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    Transcendental R a := fun halg ↦ H (halg.ringHom_of_comp_eq f g hf h)
/-
**Algebra.IsAlgebraic.ringHom_of_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.IsAlgebraic.ringHom_of_comp_eq [Algebra.IsAlgebraic R A] (hf : Fun
ction.Injective f) (hg : Function.Surjective g) (h : RingHom.comp (algebraMap S 
B) f = RingHom.comp g (algebraMap R A)) : Algebra.IsAlgebraic S B
参数：hf : Function.Injective f；hg : Function.Surjective g；h : RingHom.comp (algebr
aMap S B) f = RingHom.comp g (algebraMap R A)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgebraic.ringHom_of_comp_eq`：IsAlgebraic.ringHom_of_comp_eq (halg : I
sAlgebraic R a) (hf : Function.Injective f) (h : RingHom.comp (algebraMap S B) f
 = RingHom.comp g (a…
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…
-/
theorem Algebra.IsAlgebraic.ringHom_of_comp_eq [Algebra.IsAlgebraic R A]
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    Algebra.IsAlgebraic S B := by
  refine ⟨fun b ↦ ?_⟩
  obtain ⟨a, rfl⟩ := hg b
  exact (Algebra.IsAlgebraic.isAlgebraic a).ringHom_of_comp_eq f g hf h
/-
**Algebra.Transcendental.of_ringHom_of_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.Transcendental.of_ringHom_of_comp_eq [H : Algebra.Transcendental S
 B] (hf : Function.Injective f) (hg : Function.Surjective g) (h : RingHom.comp (
algebraMap S B) f = RingHom.comp g (algebraMap R A)) : Algebra.Transcendental R 
A
参数：hf : Function.Injective f；hg : Function.Surjective g；h : RingHom.comp (algebr
aMap S B) f = RingHom.comp g (algebraMap R A)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.transcendental_iff_not_isAlgebraic`：Algebra.transcendental_iff_n
ot_isAlgebraic : Algebra.Transcendental R A ↔ ¬ Algebra.IsAlgebraic R A
· 使用定理 `Algebra.IsAlgebraic.ringHom_of_comp_eq`：Algebra.IsAlgebraic.ringHom_of_c
omp_eq [Algebra.IsAlgebraic R A] (hf : Function.Injective f) (hg : Function.Surj
ective g) (h : RingHom.comp …
-/
theorem Algebra.Transcendental.of_ringHom_of_comp_eq [H : Algebra.Transcendental S B]
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    Algebra.Transcendental R A := by
  rw [Algebra.transcendental_iff_not_isAlgebraic] at H ⊢
  exact fun halg ↦ H (halg.ringHom_of_comp_eq f g hf hg h)
/-
**IsAlgebraic.of_ringHom_of_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAlgebraic.of_ringHom_of_comp_eq (halg : IsAlgebraic S (g a)) (hf : Funct
ion.Surjective f) (hg : Function.Injective g) (h : RingHom.comp (algebraMap S B)
 f = RingHom.comp g (algebraMap R A)) : IsAlgebraic R a
参数：halg : IsAlgebraic S (g a)；hf : Function.Surjective f；hg : Function.Injective
 g；h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.map_surjective`：map_surjective (hf : Function.Surjective f) :
 Function.Surjective (map f)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_zero`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [in
st_1 : Semiring S] (f : R →+* S), Polynomial.map f 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Polynomial.map_aeval_eq_aeval_map`：map_aeval_eq_aeval_map {S T U : Type*
} [Semiring S] [CommSemiring T] [Semiring U] [Algebra R S] [Algebra T U] {φ : R 
->+* T} {ψ : S ->+* U} …
-/
theorem IsAlgebraic.of_ringHom_of_comp_eq (halg : IsAlgebraic S (g a))
    (hf : Function.Surjective f) (hg : Function.Injective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    IsAlgebraic R a := by
  obtain ⟨p, h1, h2⟩ := halg
  obtain ⟨q, rfl⟩ := map_surjective (f : R →+* S) hf p
  refine ⟨q, fun h' ↦ by simp [h'] at h1, hg ?_⟩
  change aeval ((g : A →+* B) a) _ = 0 at h2
  change (g : A →+* B) _ = _
  rw [map_zero, map_aeval_eq_aeval_map h, h2]
/-
**Transcendental.ringHom_of_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Transcendental.ringHom_of_comp_eq (H : Transcendental R a) (hf : Function.
Surjective f) (hg : Function.Injective g) (h : RingHom.comp (algebraMap S B) f =
 RingHom.comp g (algebraMap R A)) : Transcendental S (g a)
参数：H : Transcendental R a；hf : Function.Surjective f；hg : Function.Injective g；h
 : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgebraic.of_ringHom_of_comp_eq`：IsAlgebraic.of_ringHom_of_comp_eq (ha
lg : IsAlgebraic S (g a)) (hf : Function.Surjective f) (hg : Function.Injective 
g) (h : RingHom.comp (a…
-/
theorem Transcendental.ringHom_of_comp_eq (H : Transcendental R a)
    (hf : Function.Surjective f) (hg : Function.Injective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    Transcendental S (g a) := fun halg ↦ H (halg.of_ringHom_of_comp_eq f g hf hg h)
/-
**Algebra.IsAlgebraic.of_ringHom_of_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.IsAlgebraic.of_ringHom_of_comp_eq [Algebra.IsAlgebraic S B] (hf : 
Function.Surjective f) (hg : Function.Injective g) (h : RingHom.comp (algebraMap
 S B) f = RingHom.comp g (algebraMap R A)) : Algebra.IsAlgebraic R A
参数：hf : Function.Surjective f；hg : Function.Injective g；h : RingHom.comp (algebr
aMap S B) f = RingHom.comp g (algebraMap R A)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgebraic.of_ringHom_of_comp_eq`：IsAlgebraic.of_ringHom_of_comp_eq (ha
lg : IsAlgebraic S (g a)) (hf : Function.Surjective f) (hg : Function.Injective 
g) (h : RingHom.comp (a…
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…
-/
theorem Algebra.IsAlgebraic.of_ringHom_of_comp_eq [Algebra.IsAlgebraic S B]
    (hf : Function.Surjective f) (hg : Function.Injective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    Algebra.IsAlgebraic R A :=
  ⟨fun a ↦ (Algebra.IsAlgebraic.isAlgebraic (g a)).of_ringHom_of_comp_eq f g hf hg h⟩
/-
**Algebra.Transcendental.ringHom_of_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.Transcendental.ringHom_of_comp_eq [H : Algebra.Transcendental R A]
 (hf : Function.Surjective f) (hg : Function.Injective g) (h : RingHom.comp (alg
ebraMap S B) f = RingHom.comp g (algebraMap R A)) : Algebra.Transcendental S B
参数：hf : Function.Surjective f；hg : Function.Injective g；h : RingHom.comp (algebr
aMap S B) f = RingHom.comp g (algebraMap R A)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.transcendental_iff_not_isAlgebraic`：Algebra.transcendental_iff_n
ot_isAlgebraic : Algebra.Transcendental R A ↔ ¬ Algebra.IsAlgebraic R A
· 使用定理 `Algebra.IsAlgebraic.of_ringHom_of_comp_eq`：Algebra.IsAlgebraic.of_ringHo
m_of_comp_eq [Algebra.IsAlgebraic S B] (hf : Function.Surjective f) (hg : Functi
on.Injective g) (h : RingHom.co…
-/
theorem Algebra.Transcendental.ringHom_of_comp_eq [H : Algebra.Transcendental R A]
    (hf : Function.Surjective f) (hg : Function.Injective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    Algebra.Transcendental S B := by
  rw [Algebra.transcendental_iff_not_isAlgebraic] at H ⊢
  exact fun halg ↦ H (halg.of_ringHom_of_comp_eq f g hf hg h)

end

section

variable [EquivLike FRS R S] [RingEquivClass FRS R S] [FunLike FAB A B] [RingHomClass FAB A B]
  (f : FRS) (g : FAB)

/-
**isAlgebraic_ringHom_iff_of_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isAlgebraic_ringHom_iff_of_comp_eq (hg : Function.Injective g) (h : RingHo
m.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) {a : A} : IsAlgebra
ic S (g a) ↔ IsAlgebraic R a
参数：hg : Function.Injective g；h : RingHom.comp (algebraMap S B) f = RingHom.comp 
g (algebraMap R A)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `IsAlgebraic.of_ringHom_of_comp_eq`：IsAlgebraic.of_ringHom_of_comp_eq (ha
lg : IsAlgebraic S (g a)) (hf : Function.Surjective f) (hg : Function.Injective 
g) (h : RingHom.comp (a…
· 使用定理 `EquivLike.surjective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [in
st : EquivLike E α β] (e : E), Function.Surjective ⇑e
· 使用定理 `IsAlgebraic.ringHom_of_comp_eq`：IsAlgebraic.ringHom_of_comp_eq (halg : I
sAlgebraic R a) (hf : Function.Injective f) (h : RingHom.comp (algebraMap S B) f
 = RingHom.comp g (a…
· 使用定理 `EquivLike.injective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [ins
t : EquivLike E α β] (e : E), Function.Injective ⇑e
-/
theorem isAlgebraic_ringHom_iff_of_comp_eq
    (hg : Function.Injective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) {a : A} :
    IsAlgebraic S (g a) ↔ IsAlgebraic R a :=
  ⟨fun H ↦ H.of_ringHom_of_comp_eq f g (EquivLike.surjective f) hg h,
    fun H ↦ H.ringHom_of_comp_eq f g (EquivLike.injective f) h⟩
/-
**transcendental_ringHom_iff_of_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：transcendental_ringHom_iff_of_comp_eq (hg : Function.Injective g) (h : Rin
gHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) {a : A} : Transc
endental S (g a) ↔ Transcendental R a
参数：hg : Function.Injective g；h : RingHom.comp (algebraMap S B) f = RingHom.comp 
g (algebraMap R A)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `isAlgebraic_ringHom_iff_of_comp_eq`：isAlgebraic_ringHom_iff_of_comp_eq (
hg : Function.Injective g) (h : RingHom.comp (algebraMap S B) f = RingHom.comp g
 (algebraMap R A)) {a : …
-/
theorem transcendental_ringHom_iff_of_comp_eq
    (hg : Function.Injective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) {a : A} :
    Transcendental S (g a) ↔ Transcendental R a :=
  not_congr (isAlgebraic_ringHom_iff_of_comp_eq f g hg h)

end

section

variable [EquivLike FRS R S] [RingEquivClass FRS R S] [EquivLike FAB A B] [RingEquivClass FAB A B]
  (f : FRS) (g : FAB)

/-
**Algebra.isAlgebraic_ringHom_iff_of_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.isAlgebraic_ringHom_iff_of_comp_eq (h : RingHom.comp (algebraMap S
 B) f = RingHom.comp g (algebraMap R A)) : Algebra.IsAlgebraic S B ↔ Algebra.IsA
lgebraic R A
参数：h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `Algebra.IsAlgebraic.of_ringHom_of_comp_eq`：Algebra.IsAlgebraic.of_ringHo
m_of_comp_eq [Algebra.IsAlgebraic S B] (hf : Function.Surjective f) (hg : Functi
on.Injective g) (h : RingHom.co…
· 使用定理 `EquivLike.surjective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [in
st : EquivLike E α β] (e : E), Function.Surjective ⇑e
· 使用定理 `EquivLike.injective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [ins
t : EquivLike E α β] (e : E), Function.Injective ⇑e
· 使用定理 `Algebra.IsAlgebraic.ringHom_of_comp_eq`：Algebra.IsAlgebraic.ringHom_of_c
omp_eq [Algebra.IsAlgebraic R A] (hf : Function.Injective f) (hg : Function.Surj
ective g) (h : RingHom.comp …
-/
theorem Algebra.isAlgebraic_ringHom_iff_of_comp_eq
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    Algebra.IsAlgebraic S B ↔ Algebra.IsAlgebraic R A :=
  ⟨fun H ↦ H.of_ringHom_of_comp_eq f g (EquivLike.surjective f) (EquivLike.injective g) h,
    fun H ↦ H.ringHom_of_comp_eq f g (EquivLike.injective f) (EquivLike.surjective g) h⟩
/-
**Algebra.transcendental_ringHom_iff_of_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.transcendental_ringHom_iff_of_comp_eq (h : RingHom.comp (algebraMa
p S B) f = RingHom.comp g (algebraMap R A)) : Algebra.Transcendental S B ↔ Algeb
ra.Transcendental R A
参数：h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.isAlgebraic_ringHom_iff_of_comp_eq`：Algebra.isAlgebraic_ringHom_
iff_of_comp_eq (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap
 R A)) : Algebra.IsAlgebraic S B…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Algebra.transcendental_ringHom_iff_of_comp_eq
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    Algebra.Transcendental S B ↔ Algebra.Transcendental R A := by
  simp_rw [Algebra.transcendental_iff_not_isAlgebraic,
    Algebra.isAlgebraic_ringHom_iff_of_comp_eq f g h]

end

end RingHom

/-
**Algebra.IsAlgebraic.of_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.IsAlgebraic.of_injective (f : A ->ₐ[R] B) (hf : Function.Injective
 f) [Algebra.IsAlgebraic R B] : Algebra.IsAlgebraic R A
参数：f : A ->ₐ[R] B；hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isAlgebraic_algHom_iff`：isAlgebraic_algHom_iff (f : A ->ₐ[R] B) (hf : Fu
nction.Injective f) {a : A} : IsAlgebraic R (f a) ↔ IsAlgebraic R a
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…
-/
theorem Algebra.IsAlgebraic.of_injective (f : A →ₐ[R] B) (hf : Function.Injective f)
    [Algebra.IsAlgebraic R B] : Algebra.IsAlgebraic R A :=
  ⟨fun _ ↦ (isAlgebraic_algHom_iff f hf).mp (Algebra.IsAlgebraic.isAlgebraic _)⟩

/-- Transfer `Algebra.IsAlgebraic` across an `AlgEquiv`. -/
/-
**AlgEquiv.isAlgebraic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgEquiv.isAlgebraic (e : A ≃ₐ[R] B) [Algebra.IsAlgebraic R A] : Algebra.I
sAlgebraic R B
参数：e : A ≃ₐ[R] B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsAlgebraic.of_injective`：Algebra.IsAlgebraic.of_injective (f : 
A ->ₐ[R] B) (hf : Function.Injective f) [Algebra.IsAlgebraic R B] : Algebra.IsAl
gebraic R A
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …

--- 原说明 ---
Transfer `Algebra.IsAlgebraic` across an `AlgEquiv`.
-/
theorem AlgEquiv.isAlgebraic (e : A ≃ₐ[R] B)
    [Algebra.IsAlgebraic R A] : Algebra.IsAlgebraic R B :=
  Algebra.IsAlgebraic.of_injective e.symm.toAlgHom e.symm.injective
/-
**AlgEquiv.isAlgebraic_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgEquiv.isAlgebraic_iff (e : A ≃ₐ[R] B) : Algebra.IsAlgebraic R A ↔ Algeb
ra.IsAlgebraic R B
参数：e : A ≃ₐ[R] B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.isAlgebraic`：AlgEquiv.isAlgebraic (e : A ≃ₐ[R] B) [Algebra.IsAl
gebraic R A] : Algebra.IsAlgebraic R B
-/
theorem AlgEquiv.isAlgebraic_iff (e : A ≃ₐ[R] B) :
    Algebra.IsAlgebraic R A ↔ Algebra.IsAlgebraic R B :=
  ⟨fun _ ↦ e.isAlgebraic, fun _ ↦ e.symm.isAlgebraic⟩

end

/-
**isAlgebraic_algebraMap_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isAlgebraic_algebraMap_iff {a : S} (h : Function.Injective (algebraMap S A
)) : IsAlgebraic R (algebraMap S A a) ↔ IsAlgebraic R a
参数：h : Function.Injective (algebraMap S A)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isAlgebraic_algHom_iff`：isAlgebraic_algHom_iff (f : A ->ₐ[R] B) (hf : Fu
nction.Injective f) {a : A} : IsAlgebraic R (f a) ↔ IsAlgebraic R a
-/
theorem isAlgebraic_algebraMap_iff {a : S} (h : Function.Injective (algebraMap S A)) :
    IsAlgebraic R (algebraMap S A a) ↔ IsAlgebraic R a :=
  isAlgebraic_algHom_iff (IsScalarTower.toAlgHom R S A) h
/-
**transcendental_algebraMap_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：transcendental_algebraMap_iff {a : S} (h : Function.Injective (algebraMap 
S A)) : Transcendental R (algebraMap S A a) ↔ Transcendental R a
参数：h : Function.Injective (algebraMap S A)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isAlgebraic_algebraMap_iff`：isAlgebraic_algebraMap_iff {a : S} (h : Func
tion.Injective (algebraMap S A)) : IsAlgebraic R (algebraMap S A a) ↔ IsAlgebrai
c R a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem transcendental_algebraMap_iff {a : S} (h : Function.Injective (algebraMap S A)) :
    Transcendental R (algebraMap S A a) ↔ Transcendental R a := by
  simp_rw [Transcendental, isAlgebraic_algebraMap_iff h]

namespace Subalgebra

/-
**Subalgebra.isAlgebraic_iff_isAlgebraic_val** 是 Mathlib 中的一个定理，位于命名空间 `Subalgeb
ra`。
形式化陈述：isAlgebraic_iff_isAlgebraic_val {S : Subalgebra R A} {x : S} : IsAlgebraic
 R x ↔ IsAlgebraic R x.1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `isAlgebraic_algHom_iff`：isAlgebraic_algHom_iff (f : A ->ₐ[R] B) (hf : Fu
nction.Injective f) {a : A} : IsAlgebraic R (f a) ↔ IsAlgebraic R a
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
theorem isAlgebraic_iff_isAlgebraic_val {S : Subalgebra R A} {x : S} :
    IsAlgebraic R x ↔ IsAlgebraic R x.1 :=
  (isAlgebraic_algHom_iff S.val Subtype.val_injective).symm
/-
**Subalgebra.transcendental_iff_transcendental_val** 是 Mathlib 中的一个定理，位于命名空间 `Su
balgebra`。
形式化陈述：transcendental_iff_transcendental_val {S : Subalgebra R A} {x : S} : Trans
cendental R x ↔ Transcendental R x.1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Subalgebra.isAlgebraic_iff_isAlgebraic_val`：isAlgebraic_iff_isAlgebraic_
val {S : Subalgebra R A} {x : S} : IsAlgebraic R x ↔ IsAlgebraic R x.1
-/
theorem transcendental_iff_transcendental_val {S : Subalgebra R A} {x : S} :
    Transcendental R x ↔ Transcendental R x.1 :=
  isAlgebraic_iff_isAlgebraic_val.not
/-
**Subalgebra.isAlgebraic_of_isAlgebraic_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebr
a`。
形式化陈述：isAlgebraic_of_isAlgebraic_bot {x : S} (halg : IsAlgebraic (⊥ : Subalgebra
 R S) x) : IsAlgebraic R x
参数：halg : IsAlgebraic (⊥ : Subalgebra R S) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgebraic.of_ringHom_of_comp_eq`：IsAlgebraic.of_ringHom_of_comp_eq (ha
lg : IsAlgebraic S (g a)) (hf : Function.Surjective f) (hg : Function.Injective 
g) (h : RingHom.comp (a…
· 使用定理 `Function.injective_id`：∀ {α : Sort u_1}, Function.Injective id
-/
theorem isAlgebraic_of_isAlgebraic_bot {x : S} (halg : IsAlgebraic (⊥ : Subalgebra R S) x) :
    IsAlgebraic R x :=
  halg.of_ringHom_of_comp_eq (algebraMap R (⊥ : Subalgebra R S))
    (RingHom.id S) (by rintro ⟨_, r, rfl⟩; exact ⟨r, rfl⟩) Function.injective_id rfl
/-
**Subalgebra.isAlgebraic_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：isAlgebraic_bot_iff (h : Function.Injective (algebraMap R S)) {x : S} : Is
Algebraic (⊥ : Subalgebra R S) x ↔ IsAlgebraic R x
参数：h : Function.Injective (algebraMap R S)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isAlgebraic_ringHom_iff_of_comp_eq`：isAlgebraic_ringHom_iff_of_comp_eq (
hg : Function.Injective g) (h : RingHom.comp (algebraMap S B) f = RingHom.comp g
 (algebraMap R A)) {a : …
· 使用定理 `AlgEquivClass.toRingEquivClass`：∀ {F : Type u_1} {R : outParam (Type u_2
)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}  
 {inst_1 : Semiring …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `Function.injective_id`：∀ {α : Sort u_1}, Function.Injective id
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
-/
theorem isAlgebraic_bot_iff (h : Function.Injective (algebraMap R S)) {x : S} :
    IsAlgebraic (⊥ : Subalgebra R S) x ↔ IsAlgebraic R x :=
  isAlgebraic_ringHom_iff_of_comp_eq (Algebra.botEquivOfInjective h).symm (RingHom.id S)
    Function.injective_id rfl

variable (R S) in
/-
**Subalgebra.algebra_isAlgebraic_of_algebra_isAlgebraic_bot_left** 是 Mathlib 中的一
个定理，位于命名空间 `Subalgebra`。
形式化陈述：algebra_isAlgebraic_of_algebra_isAlgebraic_bot_left [Algebra.IsAlgebraic (
⊥ : Subalgebra R S) S] : Algebra.IsAlgebraic R S
参数：⊥ : Subalgebra R S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsAlgebraic.of_ringHom_of_comp_eq`：Algebra.IsAlgebraic.of_ringHo
m_of_comp_eq [Algebra.IsAlgebraic S B] (hf : Function.Surjective f) (hg : Functi
on.Injective g) (h : RingHom.co…
· 使用定理 `Function.injective_id`：∀ {α : Sort u_1}, Function.Injective id
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
-/
theorem algebra_isAlgebraic_of_algebra_isAlgebraic_bot_left
    [Algebra.IsAlgebraic (⊥ : Subalgebra R S) S] : Algebra.IsAlgebraic R S :=
  Algebra.IsAlgebraic.of_ringHom_of_comp_eq (algebraMap R (⊥ : Subalgebra R S))
    (RingHom.id S) (by rintro ⟨_, r, rfl⟩; exact ⟨r, rfl⟩) Function.injective_id (by ext; rfl)
/-
**Subalgebra.algebra_isAlgebraic_bot_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subalge
bra`。
形式化陈述：algebra_isAlgebraic_bot_left_iff (h : Function.Injective (algebraMap R S))
 : Algebra.IsAlgebraic (⊥ : Subalgebra R S) S ↔ Algebra.IsAlgebraic R S
参数：h : Function.Injective (algebraMap R S)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Subalgebra.isAlgebraic_bot_iff`：isAlgebraic_bot_iff (h : Function.Inject
ive (algebraMap R S)) {x : S} : IsAlgebraic (⊥ : Subalgebra R S) x ↔ IsAlgebraic
 R x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem algebra_isAlgebraic_bot_left_iff (h : Function.Injective (algebraMap R S)) :
    Algebra.IsAlgebraic (⊥ : Subalgebra R S) S ↔ Algebra.IsAlgebraic R S := by
  simp_rw [Algebra.isAlgebraic_def, isAlgebraic_bot_iff h]
/-
**Subalgebra.algebra_isAlgebraic_bot_right** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra
`。
形式化陈述：algebra_isAlgebraic_bot_right [Nontrivial R] : Algebra.IsAlgebraic R (⊥ : 
Subalgebra R S)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `isAlgebraic_algebraMap`：isAlgebraic_algebraMap [Nontrivial R] (x : R) : 
IsAlgebraic R (algebraMap R A x)
-/
instance algebra_isAlgebraic_bot_right [Nontrivial R] :
    Algebra.IsAlgebraic R (⊥ : Subalgebra R S) :=
  ⟨by rintro ⟨_, x, rfl⟩; exact isAlgebraic_algebraMap _⟩

end Subalgebra

/-
**IsAlgebraic.of_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAlgebraic.of_pow {r : A} {n : Nat} (hn : 0 < n) (ht : IsAlgebraic R (r ^
 n)) : IsAlgebraic R r
参数：hn : 0 < n；ht : IsAlgebraic R (r ^ n)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.expand_ne_zero`：expand_ne_zero {p : Nat} (hp : 0 < p) {f : R[
X]} : expand R p f != 0 ↔ f != 0
· 使用定理 `Polynomial.expand_aeval`：expand_aeval {A : Type*} [Semiring A] [Algebra 
R A] (p : Nat) (P : R[X]) (r : A) : aeval r (expand R p P) = aeval (r ^ p) P
-/
theorem IsAlgebraic.of_pow {r : A} {n : ℕ} (hn : 0 < n) (ht : IsAlgebraic R (r ^ n)) :
    IsAlgebraic R r :=
  have ⟨p, p_nonzero, hp⟩ := ht
  ⟨_, by rwa [expand_ne_zero hn], by rwa [expand_aeval n p r]⟩
/-
**Transcendental.pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Transcendental.pow {r : A} (ht : Transcendental R r) {n : Nat} (hn : 0 < n
) : Transcendental R (r ^ n)
参数：ht : Transcendental R r；hn : 0 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgebraic.of_pow`：IsAlgebraic.of_pow {r : A} {n : Nat} (hn : 0 < n) (h
t : IsAlgebraic R (r ^ n)) : IsAlgebraic R r
-/
theorem Transcendental.pow {r : A} (ht : Transcendental R r) {n : ℕ} (hn : 0 < n) :
    Transcendental R (r ^ n) := fun ht' ↦ ht <| ht'.of_pow hn
/-
**IsAlgebraic.invOf** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsAlgebraic.invOf {x : S} [Invertible x] (h : IsAlgebraic R x) : IsAlgebra
ic R (⅟x)
参数：h : IsAlgebraic R x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_def`：aeval_def (p : R[X]) : aeval x p = eval₂ (algebraM
ap R A) x p
· 使用定理 `Polynomial.eval₂_reverse_eq_zero_iff`：eval₂_reverse_eq_zero_iff (i : R -
>+* S) (x : S) [Invertible x] (f : R[X]) : eval₂ i (⅟x) (reverse f) = 0 ↔ eval₂ 
i x f = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma IsAlgebraic.invOf {x : S} [Invertible x] (h : IsAlgebraic R x) : IsAlgebraic R (⅟x) := by
  obtain ⟨p, hp, hp'⟩ := h
  refine ⟨p.reverse, by simpa using hp, ?_⟩
  rwa [Polynomial.aeval_def, Polynomial.eval₂_reverse_eq_zero_iff, ← Polynomial.aeval_def]
/-
**IsAlgebraic.invOf_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsAlgebraic.invOf_iff {x : S} [Invertible x] : IsAlgebraic R (⅟x) ↔ IsAlge
braic R x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsAlgebraic.invOf`：IsAlgebraic.invOf {x : S} [Invertible x] (h : IsAlgeb
raic R x) : IsAlgebraic R (⅟x)
-/
lemma IsAlgebraic.invOf_iff {x : S} [Invertible x] :
    IsAlgebraic R (⅟x) ↔ IsAlgebraic R x :=
  ⟨IsAlgebraic.invOf, IsAlgebraic.invOf⟩
/-
**IsAlgebraic.inv_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsAlgebraic.inv_iff {K} [Field K] [Algebra R K] {x : K} : IsAlgebraic R (x
⁻¹) ↔ IsAlgebraic R x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `IsAlgebraic.invOf_iff`：IsAlgebraic.invOf_iff {x : S} [Invertible x] : Is
Algebraic R (⅟x) ↔ IsAlgebraic R x
-/
lemma IsAlgebraic.inv_iff {K} [Field K] [Algebra R K] {x : K} :
    IsAlgebraic R (x⁻¹) ↔ IsAlgebraic R x := by
  by_cases hx : x = 0
  · simp [hx]
  let := invertibleOfNonzero hx
  exact IsAlgebraic.invOf_iff (R := R) (x := x)

alias ⟨_, IsAlgebraic.inv⟩ := IsAlgebraic.inv_iff

end zero_ne_one

section

variable {K L R S A : Type*}

section Ring

section CommRing

variable [CommRing R] [CommRing S] [Ring A]
variable [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]

/-- If `x` is algebraic over `R`, then `x` is algebraic over `S` when `S` is an extension of `R`,
  and the map from `R` to `S` is injective. -/
/-
**IsAlgebraic.extendScalars** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAlgebraic.extendScalars (hinj : Function.Injective (algebraMap R S)) {x 
: A} (A_alg : IsAlgebraic R x) : IsAlgebraic S x
参数：hinj : Function.Injective (algebraMap R S)；A_alg : IsAlgebraic R x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.degree_eq_bot`：degree_eq_bot : degree p = ⊥ ↔ p = 0
· 使用定理 `Polynomial.degree_map_eq_of_injective`：degree_map_eq_of_injective {f : R
 ->+* S} (hf : Function.Injective f) (p : Polynomial R) : (p.map f).degree = p.d
egree
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.aeval_map_algebraMap`：aeval_map_algebraMap (x : B) (p : R[X])
 : aeval x (map (algebraMap R A) p) = aeval x p

--- 原说明 ---
If `x` is algebraic over `R`, then `x` is algebraic over `S` when `S` is an exte
nsion of `R`,
  and the map from `R` to `S` is injective.
-/
theorem IsAlgebraic.extendScalars (hinj : Function.Injective (algebraMap R S)) {x : A}
    (A_alg : IsAlgebraic R x) : IsAlgebraic S x :=
  let ⟨p, hp₁, hp₂⟩ := A_alg
  ⟨p.map (algebraMap _ _), by
    rwa [Ne, ← degree_eq_bot, degree_map_eq_of_injective hinj, degree_eq_bot], by simpa⟩

/-- A special case of `IsAlgebraic.extendScalars`. This is extracted as a theorem
  because in some cases `IsAlgebraic.extendScalars` will just runs out of memory. -/
/-
**IsAlgebraic.tower_top_of_subalgebra_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAlgebraic.tower_top_of_subalgebra_le {A B : Subalgebra R S} (hle : A <= 
B) {x : S} (h : IsAlgebraic A x) : IsAlgebraic B x
参数：hle : A <= B；h : IsAlgebraic A x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `IsAlgebraic.extendScalars`：IsAlgebraic.extendScalars (hinj : Function.In
jective (algebraMap R S)) {x : A} (A_alg : IsAlgebraic R x) : IsAlgebraic S x
· 使用定理 `Subalgebra.inclusion_injective`：inclusion_injective : Function.Injective
 (inclusion h)

--- 原说明 ---
A special case of `IsAlgebraic.extendScalars`. This is extracted as a theorem
  because in some cases `IsAlgebraic.extendScalars` will just runs out of memory
.
-/
theorem IsAlgebraic.tower_top_of_subalgebra_le
    {A B : Subalgebra R S} (hle : A ≤ B) {x : S}
    (h : IsAlgebraic A x) : IsAlgebraic B x := by
  let : Algebra A B := (Subalgebra.inclusion hle).toAlgebra
  have : IsScalarTower A B S := .of_algebraMap_eq fun _ ↦ rfl
  exact h.extendScalars (Subalgebra.inclusion_injective hle)

/-- If `x` is transcendental over `S`, then `x` is transcendental over `R` when `S` is an extension
  of `R`, and the map from `R` to `S` is injective. -/
/-
**Transcendental.restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Transcendental.restrictScalars (hinj : Function.Injective (algebraMap R S)
) {x : A} (h : Transcendental S x) : Transcendental R x
参数：hinj : Function.Injective (algebraMap R S)；h : Transcendental S x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgebraic.extendScalars`：IsAlgebraic.extendScalars (hinj : Function.In
jective (algebraMap R S)) {x : A} (A_alg : IsAlgebraic R x) : IsAlgebraic S x

--- 原说明 ---
If `x` is transcendental over `S`, then `x` is transcendental over `R` when `S` 
is an extension
  of `R`, and the map from `R` to `S` is injective.
-/
theorem Transcendental.restrictScalars (hinj : Function.Injective (algebraMap R S)) {x : A}
    (h : Transcendental S x) : Transcendental R x := fun H ↦ h (H.extendScalars hinj)

/-- A special case of `Transcendental.restrictScalars`. This is extracted as a theorem
  because in some cases `Transcendental.restrictScalars` will just runs out of memory. -/
/-
**Transcendental.of_tower_top_of_subalgebra_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Transcendental.of_tower_top_of_subalgebra_le {A B : Subalgebra R S} (hle :
 A <= B) {x : S} (h : Transcendental B x) : Transcendental A x
参数：hle : A <= B；h : Transcendental B x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgebraic.tower_top_of_subalgebra_le`：IsAlgebraic.tower_top_of_subalge
bra_le {A B : Subalgebra R S} (hle : A <= B) {x : S} (h : IsAlgebraic A x) : IsA
lgebraic B x

--- 原说明 ---
A special case of `Transcendental.restrictScalars`. This is extracted as a theor
em
  because in some cases `Transcendental.restrictScalars` will just runs out of m
emory.
-/
theorem Transcendental.of_tower_top_of_subalgebra_le
    {A B : Subalgebra R S} (hle : A ≤ B) {x : S}
    (h : Transcendental B x) : Transcendental A x :=
  fun H ↦ h (H.tower_top_of_subalgebra_le hle)

/-- If A is an algebraic algebra over R, then A is algebraic over S when S is an extension of R,
  and the map from `R` to `S` is injective. -/
/-
**Algebra.IsAlgebraic.extendScalars** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.IsAlgebraic.extendScalars (hinj : Function.Injective (algebraMap R
 S)) [Algebra.IsAlgebraic R A] : Algebra.IsAlgebraic S A
参数：hinj : Function.Injective (algebraMap R S)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgebraic.extendScalars`：IsAlgebraic.extendScalars (hinj : Function.In
jective (algebraMap R S)) {x : A} (A_alg : IsAlgebraic R x) : IsAlgebraic S x
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…

--- 原说明 ---
If A is an algebraic algebra over R, then A is algebraic over S when S is an ext
ension of R,
  and the map from `R` to `S` is injective.
-/
theorem Algebra.IsAlgebraic.extendScalars (hinj : Function.Injective (algebraMap R S))
    [Algebra.IsAlgebraic R A] : Algebra.IsAlgebraic S A :=
  ⟨fun _ ↦ (Algebra.IsAlgebraic.isAlgebraic _).extendScalars hinj⟩
/-
**Algebra.IsAlgebraic.tower_bot_of_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.IsAlgebraic.tower_bot_of_injective [Algebra.IsAlgebraic R A] (hinj
 : Function.Injective (algebraMap S A)) : Algebra.IsAlgebraic R S where isAlgebr
aic x
参数：hinj : Function.Injective (algebraMap S A)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isAlgebraic_algebraMap_iff`：isAlgebraic_algebraMap_iff {a : S} (h : Func
tion.Injective (algebraMap S A)) : IsAlgebraic R (algebraMap S A a) ↔ IsAlgebrai
c R a
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…
-/
theorem Algebra.IsAlgebraic.tower_bot_of_injective [Algebra.IsAlgebraic R A]
    (hinj : Function.Injective (algebraMap S A)) :
    Algebra.IsAlgebraic R S where
  isAlgebraic x := by
    simpa [isAlgebraic_algebraMap_iff hinj] using isAlgebraic (R := R) (A := A) (algebraMap _ _ x)

end CommRing

section Field

variable [Field K] [Field L] [Ring A]
variable [Algebra K L] [Algebra L A] [Algebra K A] [IsScalarTower K L A]
variable (L)

/-- If `x` is algebraic over `K`, then `x` is algebraic over `L` when `L` is an extension of `K` -/
@[stacks 09GF "part one"]
/-
**IsAlgebraic.tower_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAlgebraic.tower_top {x : A} (A_alg : IsAlgebraic K x) : IsAlgebraic L x
参数：A_alg : IsAlgebraic K x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgebraic.extendScalars`：IsAlgebraic.extendScalars (hinj : Function.In
jective (algebraMap R S)) {x : A} (A_alg : IsAlgebraic R x) : IsAlgebraic S x
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R

--- 原说明 ---
If `x` is algebraic over `K`, then `x` is algebraic over `L` when `L` is an exte
nsion of `K`
-/
theorem IsAlgebraic.tower_top {x : A} (A_alg : IsAlgebraic K x) :
    IsAlgebraic L x :=
  A_alg.extendScalars (algebraMap K L).injective

variable {L} (K) in
/-- If `x` is transcendental over `L`, then `x` is transcendental over `K` when
  `L` is an extension of `K` -/
/-
**Transcendental.of_tower_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Transcendental.of_tower_top {x : A} (h : Transcendental L x) : Transcenden
tal K x
参数：h : Transcendental L x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgebraic.tower_top`：IsAlgebraic.tower_top {x : A} (A_alg : IsAlgebrai
c K x) : IsAlgebraic L x

--- 原说明 ---
If `x` is transcendental over `L`, then `x` is transcendental over `K` when
  `L` is an extension of `K`
-/
theorem Transcendental.of_tower_top {x : A} (h : Transcendental L x) :
    Transcendental K x := fun H ↦ h (H.tower_top L)

/-- If A is an algebraic algebra over K, then A is algebraic over L when L is an extension of K -/
@[stacks 09GF "part two"]
/-
**Algebra.IsAlgebraic.tower_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.IsAlgebraic.tower_top [Algebra.IsAlgebraic K A] : Algebra.IsAlgebr
aic L A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsAlgebraic.extendScalars`：Algebra.IsAlgebraic.extendScalars (hi
nj : Function.Injective (algebraMap R S)) [Algebra.IsAlgebraic R A] : Algebra.Is
Algebraic S A
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R

--- 原说明 ---
If A is an algebraic algebra over K, then A is algebraic over L when L is an ext
ension of K
-/
theorem Algebra.IsAlgebraic.tower_top [Algebra.IsAlgebraic K A] : Algebra.IsAlgebraic L A :=
  Algebra.IsAlgebraic.extendScalars (algebraMap K L).injective

variable (K) (A)
/-
**Algebra.IsAlgebraic.tower_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.IsAlgebraic.tower_bot (K L A : Type*) [CommRing K] [Field L] [Ring
 A] [Algebra K L] [Algebra L A] [Algebra K A] [IsScalarTower K L A] [Nontrivial 
A] [Algebra.IsAlgebraic K A] : Algebra.IsAlgebraic K L
参数：K L A : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsAlgebraic.tower_bot_of_injective`：Algebra.IsAlgebraic.tower_bo
t_of_injective [Algebra.IsAlgebraic R A] (hinj : Function.Injective (algebraMap 
S A)) : Algebra.IsAlgebraic R S …
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
-/
theorem Algebra.IsAlgebraic.tower_bot (K L A : Type*) [CommRing K] [Field L] [Ring A]
    [Algebra K L] [Algebra L A] [Algebra K A] [IsScalarTower K L A]
    [Nontrivial A] [Algebra.IsAlgebraic K A] :
    Algebra.IsAlgebraic K L :=
  tower_bot_of_injective (algebraMap L A).injective

end Field

end Ring

section IsTorsionFree

namespace Algebra.IsAlgebraic

variable [CommRing K] [IsDomain K] [Field L] [Algebra K L]

/-
**Algebra.IsAlgebraic.algHom_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.IsAlge
braic`。
形式化陈述：algHom_bijective [IsTorsionFree K L] [Algebra.IsAlgebraic K L] (f : L ->ₐ[
K] L) : Function.Bijective f
参数：f : L ->ₐ[K] L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.rootSet_maps_to'`：rootSet_maps_to' {p : T[X]} {S S'} [CommRin
g S] [IsDomain S] [Algebra T S] [CommRing S'] [IsDomain S'] [Algebra T S'] (hp :
 p.map (algebraMa…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finite.injective_iff_surjective`：injective_iff_surjective {f : α -> α} :
 Injective f ↔ Surjective f
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.mem_rootSet`：mem_rootSet {p : T[X]} {S : Type*} [IsDomain T] 
[CommRing S] [IsDomain S] [Algebra T S] [Module.IsTorsionFree T S] {a : S} : a i
n p.rootSet …
-/
theorem algHom_bijective [IsTorsionFree K L] [Algebra.IsAlgebraic K L] (f : L →ₐ[K] L) :
    Function.Bijective f := by
  refine ⟨f.injective, fun b ↦ ?_⟩
  obtain ⟨p, hp, he⟩ := Algebra.IsAlgebraic.isAlgebraic (R := K) b
  let f' : p.rootSet L → p.rootSet L := (rootSet_maps_to' (fun x ↦ x) f).restrict f _ _
  have : f'.Surjective := Finite.injective_iff_surjective.1
    fun _ _ h ↦ Subtype.ext <| f.injective <| Subtype.ext_iff.1 h
  obtain ⟨a, ha⟩ := this ⟨b, mem_rootSet.2 ⟨hp, he⟩⟩
  exact ⟨a, Subtype.ext_iff.1 ha⟩
/-
**Algebra.IsAlgebraic.algHom_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.IsAlge
braic`。
形式化陈述：algHom_bijective [IsTorsionFree K L] [Algebra.IsAlgebraic K L] (f : L ->ₐ[
K] L) : Function.Bijective f
参数：f : L ->ₐ[K] L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.rootSet_maps_to'`：rootSet_maps_to' {p : T[X]} {S S'} [CommRin
g S] [IsDomain S] [Algebra T S] [CommRing S'] [IsDomain S'] [Algebra T S'] (hp :
 p.map (algebraMa…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finite.injective_iff_surjective`：injective_iff_surjective {f : α -> α} :
 Injective f ↔ Surjective f
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.mem_rootSet`：mem_rootSet {p : T[X]} {S : Type*} [IsDomain T] 
[CommRing S] [IsDomain S] [Algebra T S] [Module.IsTorsionFree T S] {a : S} : a i
n p.rootSet …
-/
theorem algHom_bijective₂ [IsTorsionFree K L] [DivisionRing R] [Algebra K R]
    [Algebra.IsAlgebraic K L] (f : L →ₐ[K] R) (g : R →ₐ[K] L) :
    Function.Bijective f ∧ Function.Bijective g :=
  (g.injective.bijective₂_of_surjective f.injective (algHom_bijective <| g.comp f).2).symm
/-
**Algebra.IsAlgebraic.bijective_of_isScalarTower** 是 Mathlib 中的一个定理，位于命名空间 `Alge
bra.IsAlgebraic`。
形式化陈述：bijective_of_isScalarTower [IsTorsionFree K L] [Algebra.IsAlgebraic K L] [
DivisionRing R] [Algebra K R] [Algebra L R] [IsScalarTower K L R] (f : R ->ₐ[K] 
L) : Function.Bijective f
参数：f : R ->ₐ[K] L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Algebra.IsAlgebraic.algHom_bijective₂`：algHom_bijective₂ [IsTorsionFree 
K L] [DivisionRing R] [Algebra K R] [Algebra.IsAlgebraic K L] (f : L ->ₐ[K] R) (
g : R ->ₐ[K] L) : Function.…
-/
theorem bijective_of_isScalarTower [IsTorsionFree K L] [Algebra.IsAlgebraic K L]
    [DivisionRing R] [Algebra K R] [Algebra L R] [IsScalarTower K L R] (f : R →ₐ[K] L) :
    Function.Bijective f :=
  (algHom_bijective₂ (IsScalarTower.toAlgHom K L R) f).2
/-
**Algebra.IsAlgebraic.bijective_of_isScalarTower'** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebra.IsAlgebraic`。
形式化陈述：bijective_of_isScalarTower' [Field R] [Algebra K R] [IsTorsionFree K R] [A
lgebra.IsAlgebraic K R] [Algebra L R] [IsScalarTower K L R] (f : R ->ₐ[K] L) : F
unction.Bijective f
参数：f : R ->ₐ[K] L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Algebra.IsAlgebraic.algHom_bijective₂`：algHom_bijective₂ [IsTorsionFree 
K L] [DivisionRing R] [Algebra K R] [Algebra.IsAlgebraic K L] (f : L ->ₐ[K] R) (
g : R ->ₐ[K] L) : Function.…
-/
theorem bijective_of_isScalarTower' [Field R] [Algebra K R]
    [IsTorsionFree K R]
    [Algebra.IsAlgebraic K R] [Algebra L R] [IsScalarTower K L R] (f : R →ₐ[K] L) :
    Function.Bijective f :=
  (algHom_bijective₂ f (IsScalarTower.toAlgHom K L R)).1

variable (K L)

/-- Bijection between algebra equivalences and algebra homomorphisms -/
@[simps]
/-
**Algebra.IsAlgebraic.algEquivEquivAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.IsA
lgebraic`。
形式化陈述：algEquivEquivAlgHom [IsTorsionFree K L] [Algebra.IsAlgebraic K L] : (L ≃ₐ[
K] L) ≃* (L ->ₐ[K] L) where toFun ϕ
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsAlgebraic.algHom_bijective`：algHom_bijective [IsTorsionFree K 
L] [Algebra.IsAlgebraic K L] (f : L ->ₐ[K] L) : Function.Bijective f

--- 原说明 ---
Bijection between algebra equivalences and algebra homomorphisms
-/
noncomputable def algEquivEquivAlgHom [IsTorsionFree K L] [Algebra.IsAlgebraic K L] :
    (L ≃ₐ[K] L) ≃* (L →ₐ[K] L) where
  toFun ϕ := ϕ.toAlgHom
  invFun ϕ := AlgEquiv.ofBijective ϕ (algHom_bijective ϕ)
  map_mul' _ _ := rfl

end Algebra.IsAlgebraic

end IsTorsionFree

end

section

variable {R S : Type*} [CommRing R]

section

open Algebra

variable [Ring S] [Algebra R S]

/-
**IsAlgebraic.exists_nonzero_coeff_and_aeval_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：IsAlgebraic.exists_nonzero_coeff_and_aeval_eq_zero {s : S} (hRs : IsAlgebr
aic R s) (hs : s in S⁰) : exists q : R[X], q.coeff 0 != 0 ∧ aeval s q = 0
参数：hRs : IsAlgebraic R s；hs : s in S⁰。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd`：exists_eq_pow
_rootMultiplicity_mul_and_not_dvd (p : R[X]) (hp : p != 0) (a : R) : exists q : 
R[X], p = (X - C a) ^ p.rootMultiplicity a * q …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.C_0`：C_0 : C (0 : R) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Submonoid.pow_mem`：∀ {M : Type u_5} [inst : Monoid M] (S : Submonoid M) 
{x : M}, x ∈ S → ∀ (n : ℕ), x ^ n ∈ S
· 使用定理 `Polynomial.aeval_X_pow`：aeval_X_pow {n : Nat} : aeval x ((X : R[X]) ^ n)
 = x ^ n
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Polynomial.X_pow_mul`：X_pow_mul {n : Nat} : X ^ n * p = p * X ^ n
-/
theorem IsAlgebraic.exists_nonzero_coeff_and_aeval_eq_zero
    {s : S} (hRs : IsAlgebraic R s) (hs : s ∈ S⁰) :
    ∃ q : R[X], q.coeff 0 ≠ 0 ∧ aeval s q = 0 := by
  obtain ⟨p, hp0, hp⟩ := hRs
  obtain ⟨q, hpq, hq⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp0 0
  simp only [C_0, sub_zero, X_pow_mul, X_dvd_iff] at hpq hq
  rw [hpq, map_mul, aeval_X_pow] at hp
  exact ⟨q, hq, (S⁰.pow_mem hs (rootMultiplicity 0 p)).2 (aeval s q) hp⟩
/-
**IsAlgebraic.exists_nonzero_eq_adjoin_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAlgebraic.exists_nonzero_eq_adjoin_mul {s : S} (hRs : IsAlgebraic R s) (
hs : s in S⁰) : existsᵉ (t in R[s]) (r != (0 : R)), s * t = algebraMap R S r
参数：hRs : IsAlgebraic R s；hs : s in S⁰。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgebraic.exists_nonzero_coeff_and_aeval_eq_zero`：IsAlgebraic.exists_n
onzero_coeff_and_aeval_eq_zero {s : S} (hRs : IsAlgebraic R s) (hs : s in S⁰) : 
exists q : R[X], q.coeff 0 != 0 ∧ aeval …
· 使用定理 `Polynomial.X_dvd_sub_C`：X_dvd_sub_C : X ∣ p - C (p.coeff 0)
· 使用定理 `Polynomial.aeval_mem_adjoin_singleton`：∀ (R : Type u) {A : Type z} [inst
 : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] {p : Polynomial 
R}   (x : A), (Polynomial.a…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem IsAlgebraic.exists_nonzero_eq_adjoin_mul {s : S} (hRs : IsAlgebraic R s) (hs : s ∈ S⁰) :
    ∃ᵉ (t ∈ R[s]) (r ≠ (0 : R)), s * t = algebraMap R S r := by
  have ⟨q, hq0, hq⟩ := hRs.exists_nonzero_coeff_and_aeval_eq_zero hs
  have ⟨p, hp⟩ := X_dvd_sub_C (p := q)
  refine ⟨aeval s p, aeval_mem_adjoin_singleton _ _, _, neg_ne_zero.mpr hq0, ?_⟩
  apply_fun aeval s at hp
  rwa [map_sub, hq, zero_sub, map_mul, aeval_X, aeval_C, ← map_neg, eq_comm] at hp
/-
**IsAlgebraic.exists_nonzero_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAlgebraic.exists_nonzero_dvd {s : S} (hRs : IsAlgebraic R s) (hs : s in 
S⁰) : exists r : R, r != 0 ∧ s ∣ algebraMap R S r
参数：hRs : IsAlgebraic R s；hs : s in S⁰。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgebraic.exists_nonzero_coeff_and_aeval_eq_zero`：IsAlgebraic.exists_n
onzero_coeff_and_aeval_eq_zero {s : S} (hRs : IsAlgebraic R s) (hs : s in S⁰) : 
exists q : R[X], q.coeff 0 != 0 ∧ aeval …
· 使用定理 `map_dvd`：∀ {M : Type u_1} {N : Type u_2} [inst : Semigroup M] [inst_1 : 
Semigroup N] {F : Type u_3} [inst_2 : FunLike F M N]   [MulHomClass F M N] (f…
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Polynomial.X_dvd_sub_C`：X_dvd_sub_C : X ∣ p - C (p.coeff 0)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `dvd_neg`：dvd_neg : a ∣ -b ↔ a ∣ b
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
-/
theorem IsAlgebraic.exists_nonzero_dvd {s : S} (hRs : IsAlgebraic R s) (hs : s ∈ S⁰) :
    ∃ r : R, r ≠ 0 ∧ s ∣ algebraMap R S r := by
  obtain ⟨q, hq0, hq⟩ := hRs.exists_nonzero_coeff_and_aeval_eq_zero hs
  have key := map_dvd (aeval s) (X_dvd_sub_C (p := q))
  rw [map_sub, hq, zero_sub, dvd_neg, aeval_X, aeval_C] at key
  exact ⟨q.coeff 0, hq0, key⟩

/-- A fraction `(a : S) / (b : S)` can be reduced to `(c : S) / (d : R)`,
if `b` is algebraic over `R`. -/
/-
**IsAlgebraic.exists_smul_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAlgebraic.exists_smul_eq_mul (a : S) {b : S} (hRb : IsAlgebraic R b) (hb
 : b in S⁰) : existsᵉ (c : S) (d != (0 : R)), d • a = b * c
参数：a : S；hRb : IsAlgebraic R b；hb : b in S⁰。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgebraic.exists_nonzero_dvd`：IsAlgebraic.exists_nonzero_dvd {s : S} (
hRs : IsAlgebraic R s) (hs : s in S⁰) : exists r : R, r != 0 ∧ s ∣ algebraMap R 
S r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)

--- 原说明 ---
A fraction `(a : S) / (b : S)` can be reduced to `(c : S) / (d : R)`,
if `b` is algebraic over `R`.
-/
theorem IsAlgebraic.exists_smul_eq_mul
    (a : S) {b : S} (hRb : IsAlgebraic R b) (hb : b ∈ S⁰) :
    ∃ᵉ (c : S) (d ≠ (0 : R)), d • a = b * c :=
  have ⟨r, hr, s, h⟩ := hRb.exists_nonzero_dvd hb
  ⟨s * a, r, hr, by rw [smul_def, h, mul_assoc]⟩

variable (R)

/-- A fraction `(a : S) / (b : S)` can be reduced to `(c : S) / (d : R)`,
if `b` is algebraic over `R`. -/
/-
**Algebra.IsAlgebraic.exists_smul_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.IsAlgebraic.exists_smul_eq_mul [NoZeroDivisors S] [Algebra.IsAlgeb
raic R S] (a : S) {b : S} (hb : b != 0) : existsᵉ (c : S) (d != (0 : R)), d • a 
= b * c
参数：a : S；hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgebraic.exists_smul_eq_mul`：IsAlgebraic.exists_smul_eq_mul (a : S) {
b : S} (hRb : IsAlgebraic R b) (hb : b in S⁰) : existsᵉ (c : S) (d != (0 : R)), 
d • a = b * c
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…
· 使用定理 `mem_nonZeroDivisors_of_ne_zero`：mem_nonZeroDivisors_of_ne_zero (hx : x !
= 0) : x in M₀⁰

--- 原说明 ---
A fraction `(a : S) / (b : S)` can be reduced to `(c : S) / (d : R)`,
if `b` is algebraic over `R`.
-/
theorem Algebra.IsAlgebraic.exists_smul_eq_mul [NoZeroDivisors S] [Algebra.IsAlgebraic R S]
    (a : S) {b : S} (hb : b ≠ 0) :
    ∃ᵉ (c : S) (d ≠ (0 : R)), d • a = b * c :=
  (isAlgebraic b).exists_smul_eq_mul a (mem_nonZeroDivisors_of_ne_zero hb)

namespace Polynomial

/-- Given a transcendental element `s : S` over `R`, the `R`-algebra equivalence
between `R[X]` and `R[s]` given by sending `X` to `s`. -/
/-
**Polynomial.algEquivOfTranscendental** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：algEquivOfTranscendental (s : S) (h : Transcendental R s) : R[X] ≃ₐ[R] R[s
]
参数：s : S；h : Transcendental R s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a transcendental element `s : S` over `R`, the `R`-algebra equivalence
between `R[X]` and `R[s]` given by sending `X` to `s`.
-/
noncomputable def algEquivOfTranscendental (s : S) (h : Transcendental R s) :
    R[X] ≃ₐ[R] R[s] :=
  AlgEquiv.ofBijective (aeval ⟨s, self_mem_adjoin_singleton R s⟩) <| by
    refine ⟨transcendental_iff_injective.mp ?_, ?_⟩
    · rwa [Subalgebra.transcendental_iff_transcendental_val]
    rw [← AlgHom.range_eq_top, _root_.eq_top_iff]
    rintro ⟨t, ht⟩ _
    obtain ⟨r, rfl⟩ := adjoin_mem_exists_aeval _ _ ht
    exact ⟨r, by ext; simp⟩

@[simp]
/-
**Polynomial.algEquivOfTranscendental_coe** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`
。
形式化陈述：algEquivOfTranscendental_coe (s : S) (h : Transcendental R s) : (algEquivO
fTranscendental R s h : R[X] ->+* R[s]) = aeval (R
参数：s : S；h : Transcendental R s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
-/
theorem algEquivOfTranscendental_coe (s : S) (h : Transcendental R s) :
    (algEquivOfTranscendental R s h : R[X] →+* R[s]) =
    aeval (R := R) (A := R[s]) ⟨s, self_mem_adjoin_singleton R s⟩ := rfl

@[simp]
/-
**Polynomial.algEquivOfTranscendental_apply** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：algEquivOfTranscendental_apply (s : S) (h : Transcendental R s) (f : R[X])
 : algEquivOfTranscendental R s h f = aeval (⟨s, self_mem_adjoin_singleton R s⟩)
 f
参数：s : S；h : Transcendental R s；f : R[X]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algEquivOfTranscendental_apply (s : S) (h : Transcendental R s) (f : R[X]) :
    algEquivOfTranscendental R s h f = aeval (⟨s, self_mem_adjoin_singleton R s⟩) f := rfl
/-
**Polynomial.algEquivOfTranscendental_apply_X** 是 Mathlib 中的一个引理，位于命名空间 `Polynom
ial`。
形式化陈述：algEquivOfTranscendental_apply_X (s : S) (h : Transcendental R s) : algEqu
ivOfTranscendental R s h X = ⟨s, self_mem_adjoin_singleton R s⟩
参数：s : S；h : Transcendental R s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.self_mem_adjoin_singleton`：self_mem_adjoin_singleton (x : A) : x
 in R[x]
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma algEquivOfTranscendental_apply_X (s : S) (h : Transcendental R s) :
    algEquivOfTranscendental R s h X = ⟨s, self_mem_adjoin_singleton R s⟩ := by simp

@[simp]
/-
**Polynomial.algEquivOfTranscendental_symm_aeval** 是 Mathlib 中的一个定理，位于命名空间 `Poly
nomial`。
形式化陈述：algEquivOfTranscendental_symm_aeval (s : S) (h : Transcendental R s) (f : 
R[X]) : (algEquivOfTranscendental R s h).symm (aeval (⟨s, self_mem_adjoin_single
ton R s⟩) f) = f
参数：s : S；h : Transcendental R s；f : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Algebra.self_mem_adjoin_singleton`：self_mem_adjoin_singleton (x : A) : x
 in R[x]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem algEquivOfTranscendental_symm_aeval (s : S) (h : Transcendental R s) (f : R[X]) :
    (algEquivOfTranscendental R s h).symm
      (aeval (⟨s, self_mem_adjoin_singleton R s⟩) f) = f := by
  apply (algEquivOfTranscendental R s h).toEquiv.injective
  simp

@[simp]
/-
**Polynomial.algEquivOfTranscendental_symm_gen** 是 Mathlib 中的一个定理，位于命名空间 `Polyno
mial`。
形式化陈述：algEquivOfTranscendental_symm_gen (s : S) (h : Transcendental R s) : (algE
quivOfTranscendental R s h).symm ⟨s, self_mem_adjoin_singleton R s⟩ = X
参数：s : S；h : Transcendental R s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Algebra.self_mem_adjoin_singleton`：self_mem_adjoin_singleton (x : A) : x
 in R[x]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem algEquivOfTranscendental_symm_gen (s : S) (h : Transcendental R s) :
    (algEquivOfTranscendental R s h).symm ⟨s, self_mem_adjoin_singleton R s⟩ = X := by
  apply (algEquivOfTranscendental R s h).toEquiv.injective
  simp

end Polynomial

/-
**Transcendental.uniqueFactorizationMonoid_adjoin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Transcendental.uniqueFactorizationMonoid_adjoin [UniqueFactorizationMonoid
 R] {s : S} (h : Transcendental R s) : UniqueFactorizationMonoid (R[s])
参数：h : Transcendental R s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.uniqueFactorizationMonoid`：MulEquiv.uniqueFactorizationMonoid (
e : α ≃* β) (hα : UniqueFactorizationMonoid α) : UniqueFactorizationMonoid β
· 使用定理 `Polynomial.uniqueFactorizationMonoid`：∀ {D : Type u} [inst : CommRing D]
 [UniqueFactorizationMonoid D], UniqueFactorizationMonoid (Polynomial D)
-/
theorem Transcendental.uniqueFactorizationMonoid_adjoin [UniqueFactorizationMonoid R] {s : S}
      (h : Transcendental R s) : UniqueFactorizationMonoid (R[s]) :=
  (algEquivOfTranscendental R s h).toMulEquiv.uniqueFactorizationMonoid inferInstance

end

namespace Algebra.IsAlgebraic

variable (S) {A : Type*} [CommRing S] [NoZeroDivisors S] [Algebra R S]
  [alg : Algebra.IsAlgebraic R S] [Ring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]

open Function (Injective) in
/-
**Algebra.IsAlgebraic.injective_tower_top** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.IsA
lgebraic`。
形式化陈述：injective_tower_top (inj : Injective (algebraMap R A)) : Injective (algebr
aMap S A)
参数：inj : Injective (algebraMap R A)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `of_not_not`：of_not_not {a : Prop} : ¬¬a -> a
· 使用定理 `IsAlgebraic.exists_nonzero_dvd`：IsAlgebraic.exists_nonzero_dvd {s : S} (
hRs : IsAlgebraic R s) (hs : s in S⁰) : exists r : R, r != 0 ∧ s ∣ algebraMap R 
S r
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…
· 使用定理 `mem_nonZeroDivisors_of_ne_zero`：mem_nonZeroDivisors_of_ne_zero (hx : x !
= 0) : x in M₀⁰
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `zero_dvd_iff`：zero_dvd_iff : 0 ∣ a ↔ a = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `map_dvd`：∀ {M : Type u_1} {N : Type u_2} [inst : Semigroup M] [inst_1 : 
Semigroup N] {F : Type u_3} [inst_2 : FunLike F M N]   [MulHomClass F M N] (f…
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem injective_tower_top (inj : Injective (algebraMap R A)) : Injective (algebraMap S A) := by
  refine (injective_iff_map_eq_zero _).mpr fun s eq ↦ of_not_not fun ne ↦ ?_
  have ⟨r, ne, dvd⟩ := (alg.1 s).exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero ne)
  refine ne (inj <| map_zero (algebraMap R A) ▸ zero_dvd_iff.mp ?_)
  simp_rw [← eq, IsScalarTower.algebraMap_apply R S A, map_dvd (algebraMap S A) dvd]

variable (R A)
/-
**Algebra.IsAlgebraic.faithfulSMul_tower_top** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.
IsAlgebraic`。
形式化陈述：faithfulSMul_tower_top [FaithfulSMul R A] : FaithfulSMul S A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `faithfulSMul_iff_algebraMap_injective`：faithfulSMul_iff_algebraMap_injec
tive : FaithfulSMul R A ↔ Injective (algebraMap R A)
· 使用定理 `Algebra.IsAlgebraic.injective_tower_top`：injective_tower_top (inj : Inje
ctive (algebraMap R A)) : Injective (algebraMap S A)
-/
theorem faithfulSMul_tower_top [FaithfulSMul R A] : FaithfulSMul S A := by
  rw [faithfulSMul_iff_algebraMap_injective] at *
  exact injective_tower_top S ‹_›

end Algebra.IsAlgebraic

end

section Field

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (A : Subalgebra K L)

/-
**inv_eq_of_aeval_divX_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_eq_of_aeval_divX_ne_zero {x : L} {p : K[X]} (aeval_ne : aeval x (divX 
p) != 0) : x⁻¹ = aeval x (divX p) / (aeval x p - algebraMap _ _ (p.coeff 0))
参数：aeval_ne : aeval x (divX p) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_eq_iff_eq_inv`：inv_eq_iff_eq_inv : a⁻¹ = b ↔ a = b⁻¹
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `div_eq_iff`：div_eq_iff (hb : b != 0) : a / b = c ↔ a = c * b
· 使用定理 `sub_eq_iff_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a -
 b = c ↔ a = c + b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.divX_mul_X_add`：divX_mul_X_add (p : R[X]) : divX p * X + C (p
.coeff 0) = p
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
-/
theorem inv_eq_of_aeval_divX_ne_zero {x : L} {p : K[X]} (aeval_ne : aeval x (divX p) ≠ 0) :
    x⁻¹ = aeval x (divX p) / (aeval x p - algebraMap _ _ (p.coeff 0)) := by
  rw [inv_eq_iff_eq_inv, inv_div, eq_comm, div_eq_iff, sub_eq_iff_eq_add, mul_comm]
  conv_lhs => rw [← divX_mul_X_add p]
  · rw [map_add, map_mul, aeval_X, aeval_C]
  · exact aeval_ne
/-
**inv_eq_of_root_of_coeff_zero_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_eq_of_root_of_coeff_zero_ne_zero {x : L} {p : K[X]} (aeval_eq : aeval 
x p = 0) (coeff_zero_ne : p.coeff 0 != 0) : x⁻¹ = -(aeval x (divX p) / algebraMa
p _ _ (p.coeff 0))
参数：aeval_eq : aeval x p = 0；coeff_zero_ne : p.coeff 0 != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用引理 `div_neg`：div_neg (a : R) : a / -b = -(a / b)
· 使用定理 `inv_eq_of_aeval_divX_ne_zero`：inv_eq_of_aeval_divX_ne_zero {x : L} {p : 
K[X]} (aeval_ne : aeval x (divX p) != 0) : x⁻¹ = aeval x (divX p) / (aeval x p -
 algebraMap _ _ (p…
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `RingHom.map_zero`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring 
α} {x_1 : NonAssocSemiring β} (f : α →+* β), f 0 = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.divX_mul_X_add`：divX_mul_X_add (p : R[X]) : divX p * X + C (p
.coeff 0) = p
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
-/
theorem inv_eq_of_root_of_coeff_zero_ne_zero {x : L} {p : K[X]} (aeval_eq : aeval x p = 0)
    (coeff_zero_ne : p.coeff 0 ≠ 0) : x⁻¹ = -(aeval x (divX p) / algebraMap _ _ (p.coeff 0)) := by
  convert!
    inv_eq_of_aeval_divX_ne_zero (p := p) (L := L)
      (mt (fun h => (algebraMap K L).injective ?_) coeff_zero_ne) using 1
  · rw [aeval_eq, zero_sub, div_neg]
  rw [RingHom.map_zero]
  convert! aeval_eq
  conv_rhs => rw [← divX_mul_X_add p]
  rw [map_add, map_mul, h, zero_mul, zero_add, aeval_C]
/-
**Subalgebra.inv_mem_of_root_of_coeff_zero_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subalgebra.inv_mem_of_root_of_coeff_zero_ne_zero {x : A} {p : K[X]} (aeval
_eq : aeval x p = 0) (coeff_zero_ne : p.coeff 0 != 0) : (x⁻¹ : L) in A
参数：aeval_eq : aeval x p = 0；coeff_zero_ne : p.coeff 0 != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subalgebra.aeval_coe`：aeval_coe (S : Subalgebra R A) (x : S) (p : R[X]) 
: aeval (x : A) p = aeval x p
· 使用定理 `Subalgebra.coe_zero`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A),   ↑0 = 0
· 使用定理 `inv_eq_of_root_of_coeff_zero_ne_zero`：inv_eq_of_root_of_coeff_zero_ne_ze
ro {x : L} {p : K[X]} (aeval_eq : aeval x p = 0) (coeff_zero_ne : p.coeff 0 != 0
) : x⁻¹ = -(aeval x (divX …
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用引理 `inv_neg`：inv_neg : (-a)⁻¹ = -a⁻¹
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Subalgebra.smul_mem`：smul_mem {x : A} (hx : x in S) (r : R) : r • x in S
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem Subalgebra.inv_mem_of_root_of_coeff_zero_ne_zero {x : A} {p : K[X]}
    (aeval_eq : aeval x p = 0) (coeff_zero_ne : p.coeff 0 ≠ 0) : (x⁻¹ : L) ∈ A := by
  suffices (x⁻¹ : L) = (-p.coeff 0)⁻¹ • aeval x (divX p) by
    rw [this]
    exact A.smul_mem (aeval x _).2 _
  have : aeval (x : L) p = 0 := by rw [Subalgebra.aeval_coe, aeval_eq, Subalgebra.coe_zero]
  rw [inv_eq_of_root_of_coeff_zero_ne_zero this coeff_zero_ne, div_eq_inv_mul, Algebra.smul_def,
    aeval_coe, map_inv₀, map_neg, inv_neg, neg_mul]
/-
**Subalgebra.inv_mem_of_algebraic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subalgebra.inv_mem_of_algebraic {x : A} (hx : IsAlgebraic K (x : L)) : (x⁻
¹ : L) in A
参数：hx : IsAlgebraic K (x : L)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `Subalgebra.inv_mem_of_root_of_coeff_zero_ne_zero`：Subalgebra.inv_mem_of_
root_of_coeff_zero_ne_zero {x : A} {p : K[X]} (aeval_eq : aeval x p = 0) (coeff_
zero_ne : p.coeff 0 != 0) : (x⁻¹ : L) …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Polynomial.coeff_C`：coeff_C : coeff (C a) n = ite (n = 0) a 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Subalgebra.coe_zero`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A),   ↑0 = 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `Subalgebra.zero_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A),   0 ∈ S
· 使用定理 `Subalgebra.coe_eq_zero`：∀ {R : Type u} {A : Type v} [inst : CommSemiring
 R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {x : ↥S}
, ↑x = 0 ↔ x…
· 使用定理 `Subalgebra.aeval_coe`：aeval_coe (S : Subalgebra R A) (x : S) (p : R[X]) 
: aeval (x : A) p = aeval x p
-/
theorem Subalgebra.inv_mem_of_algebraic {x : A} (hx : IsAlgebraic K (x : L)) :
    (x⁻¹ : L) ∈ A := by
  obtain ⟨p, ne_zero, aeval_eq⟩ := hx
  rw [Subalgebra.aeval_coe, Subalgebra.coe_eq_zero] at aeval_eq
  revert ne_zero aeval_eq
  refine p.recOnHorner ?_ ?_ ?_
  · intro h
    contradiction
  · intro p a hp ha _ih _ne_zero aeval_eq
    refine A.inv_mem_of_root_of_coeff_zero_ne_zero aeval_eq ?_
    rwa [coeff_add, hp, zero_add, coeff_C, if_pos rfl]
  · intro p hp ih _ne_zero aeval_eq
    rw [map_mul, aeval_X, mul_eq_zero] at aeval_eq
    rcases aeval_eq with aeval_eq | x_eq
    · exact ih hp aeval_eq
    · rw [x_eq, Subalgebra.coe_zero, inv_zero]
      exact A.zero_mem

/-- In an algebraic extension L/K, an intermediate subalgebra is a field. -/
@[stacks 0BID]
/-
**Subalgebra.isField_of_algebraic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subalgebra.isField_of_algebraic [Algebra.IsAlgebraic K L] : IsField A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Nontrivial.exists_pair_ne`：∀ {α : Type u_3} [self : Nontrivial α], ∃ x y
, x ≠ y
· 使用定理 `CommRing.mul_comm`：∀ {α : Type u} [self : CommRing α] (a b : α), a * b =
 b * a
· 使用定理 `Subalgebra.inv_mem_of_algebraic`：Subalgebra.inv_mem_of_algebraic {x : A}
 (hx : IsAlgebraic K (x : L)) : (x⁻¹ : L) in A
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subalgebra.coe_eq_zero`：∀ {R : Type u} {A : Type v} [inst : CommSemiring
 R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {x : ↥S}
, ↑x = 0 ↔ x…

--- 原说明 ---
In an algebraic extension L/K, an intermediate subalgebra is a field.
-/
theorem Subalgebra.isField_of_algebraic [Algebra.IsAlgebraic K L] : IsField A :=
  { show Nontrivial A by infer_instance, Subalgebra.toCommRing A with
    mul_inv_cancel := fun {a} ha =>
      ⟨⟨a⁻¹, A.inv_mem_of_algebraic (Algebra.IsAlgebraic.isAlgebraic (a : L))⟩,
        Subtype.ext (mul_inv_cancel₀ (mt (Subalgebra.coe_eq_zero _).mp ha))⟩ }

end Field

section Infinite

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] [Nontrivial R]

/-
**Transcendental.infinite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Transcendental.infinite {x : A} (hx : Transcendental R x) : Infinite A
参数：hx : Transcendental R x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Infinite.of_injective`：of_injective {α β} [Infinite β] (f : β -> α) (hf 
: Injective f) : Infinite α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `transcendental_iff_injective`：transcendental_iff_injective {x : A} : Tra
nscendental R x ↔ Function.Injective (Polynomial.aeval x : R[X] ->ₐ[R] A)
-/
theorem Transcendental.infinite {x : A} (hx : Transcendental R x) : Infinite A :=
  .of_injective _ (transcendental_iff_injective.mp hx)

variable (R A) in
/-
**Algebra.Transcendental.infinite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.Transcendental.infinite [Algebra.Transcendental R A] : Infinite A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Transcendental.infinite`：Transcendental.infinite {x : A} (hx : Transcend
ental R x) : Infinite A
-/
theorem Algebra.Transcendental.infinite [Algebra.Transcendental R A] : Infinite A :=
  have ⟨x, hx⟩ := ‹Algebra.Transcendental R A›
  hx.infinite

end Infinite

