/-
Copyright (c) 2023 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.RingTheory.Conductor
public import Mathlib.RingTheory.FractionalIdeal.Extended
public import Mathlib.RingTheory.Trace.Quotient

/-!
# The different ideal

## Main definition
- `Submodule.traceDual`: The dual `L`-sub `B`-module under the trace form.
- `FractionalIdeal.dual`: The dual fractional ideal under the trace form.
- `differentIdeal`: The different ideal of an extension of integral domains.

## Main results
- `conductor_mul_differentIdeal`:
  If `L = K[x]`, with `x` integral over `A`, then `𝔣 * 𝔇 = (f'(x))`
    with `f` being the minimal polynomial of `x`.
- `aeval_derivative_mem_differentIdeal`:
  If `L = K[x]`, with `x` integral over `A`, then `f'(x) ∈ 𝔇`
    with `f` being the minimal polynomial of `x`.
- `not_dvd_differentIdeal_iff`: A prime does not divide the different ideal iff it is unramified
  (in the sense of `Algebra.IsUnramifiedAt`).
- `differentIdeal_eq_differentIdeal_mul_differentIdeal`: Transitivity of the different ideal.

## TODO
- Show properties of the different ideal
-/

@[expose] public section

open Module

universe u

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
  Ideal.Quotient.field

variable (A K : Type*) {L : Type u} {B} [CommRing A] [Field K] [CommRing B] [Field L]
variable [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
variable [IsScalarTower A K L] [IsScalarTower A B L]

open nonZeroDivisors IsLocalization Matrix Algebra Pointwise Polynomial Submodule
section BIsDomain

/-- Under the AKLB setting, `Iᵛ := traceDual A K (I : Submodule B L)` is the
`Submodule B L` such that `x ∈ Iᵛ ↔ ∀ y ∈ I, Tr(x, y) ∈ A` -/
noncomputable
/-
**Submodule.traceDual** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Submodule.traceDual (I : Submodule B L) : Submodule B L where __
参数：I : Submodule B L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Submodule.traceDual (I : Submodule B L) : Submodule B L where
  __ := (traceForm K L).dualSubmodule (I.restrictScalars A)
  smul_mem' c x hx a ha := by
    rw [traceForm_apply, smul_mul_assoc, mul_comm, ← smul_mul_assoc, mul_comm]
    exact hx _ (Submodule.smul_mem _ c ha)

variable {A K}

local notation:max I:max "ᵛ" => Submodule.traceDual A K I

namespace Submodule

/-
**Submodule.mem_traceDual** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：mem_traceDual {I : Submodule B L} {x} : x in Iᵛ ↔ forall a in I, traceForm
 K L x a in (algebraMap A K).range
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `Submodule.mem_one`：mem_one {x : A} : x in (1 : Submodule R A) ↔ exists y
, algebraMap R A y = x
-/
lemma mem_traceDual {I : Submodule B L} {x} :
    x ∈ Iᵛ ↔ ∀ a ∈ I, traceForm K L x a ∈ (algebraMap A K).range :=
  forall₂_congr fun _ _ ↦ mem_one
/-
**Submodule.le_traceDual_iff_map_le_one** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：le_traceDual_iff_map_le_one {I J : Submodule B L} : I <= Jᵛ ↔ ((I * J : Su
bmodule B L).restrictScalars A).map ((trace K L).restrictScalars A) <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map_le_iff_le_comap`：map_le_iff_le_comap {f : M ->ₛₗ[σ₁₂] M₂} 
{p : Submodule R M} {q : Submodule R₂ M₂} : map f p <= q ↔ p <= comap f q
· 使用引理 `Submodule.restrictScalars_mul`：restrictScalars_mul {A B C} [Semiring A] 
[Semiring B] [Semiring C] [SMul A B] [Module A C] [Module B C] [IsScalarTower A 
C C] [IsScalarTower…
· 使用定理 `Submodule.mul_le`：mul_le : M * N <= P ↔ forall m in M, forall n in N, m 
* n in P
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma le_traceDual_iff_map_le_one {I J : Submodule B L} :
    I ≤ Jᵛ ↔ ((I * J : Submodule B L).restrictScalars A).map
      ((trace K L).restrictScalars A) ≤ 1 := by
  rw [Submodule.map_le_iff_le_comap, Submodule.restrictScalars_mul, Submodule.mul_le]
  simp [SetLike.le_def, mem_traceDual]
/-
**Submodule.le_traceDual_mul_iff** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：le_traceDual_mul_iff {I J J' : Submodule B L} : I <= (J * J')ᵛ ↔ I * J <= 
J'ᵛ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `Submodule.restrictScalars.congr_simp`：∀ (S : Type u_1) {R : Type u_2} {M
 : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : Semiring S
]   [inst_3 : _root_.Modul…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma le_traceDual_mul_iff {I J J' : Submodule B L} :
    I ≤ (J * J')ᵛ ↔ I * J ≤ J'ᵛ := by
  simp_rw [le_traceDual_iff_map_le_one, mul_assoc]
/-
**Submodule.le_traceDual** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：le_traceDual {I J : Submodule B L} : I <= Jᵛ ↔ I * J <= 1ᵛ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.le_traceDual_mul_iff`：le_traceDual_mul_iff {I J J' : Submodule
 B L} : I <= (J * J')ᵛ ↔ I * J <= J'ᵛ
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma le_traceDual {I J : Submodule B L} :
    I ≤ Jᵛ ↔ I * J ≤ 1ᵛ := by
  rw [← le_traceDual_mul_iff, mul_one]
/-
**Submodule.le_traceDual_comm** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：le_traceDual_comm {I J : Submodule B L} : I <= Jᵛ ↔ J <= Iᵛ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Submodule.le_traceDual`：le_traceDual {I J : Submodule B L} : I <= Jᵛ ↔ I
 * J <= 1ᵛ
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma le_traceDual_comm {I J : Submodule B L} :
    I ≤ Jᵛ ↔ J ≤ Iᵛ := by rw [le_traceDual, mul_comm, ← le_traceDual]
/-
**Submodule.le_traceDual_traceDual** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：le_traceDual_traceDual {I : Submodule B L} : I <= Iᵛᵛ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Submodule.le_traceDual_comm`：le_traceDual_comm {I J : Submodule B L} : I
 <= Jᵛ ↔ J <= Iᵛ
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma le_traceDual_traceDual {I : Submodule B L} :
    I ≤ Iᵛᵛ := le_traceDual_comm.mpr le_rfl

@[simp]
/-
**Submodule.restrictScalars_traceDual** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：restrictScalars_traceDual {I : Submodule B L} : Iᵛ.restrictScalars A = (Al
gebra.traceForm K L).dualSubmodule (I.restrictScalars A)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrictScalars_traceDual {I : Submodule B L} :
    Iᵛ.restrictScalars A = (Algebra.traceForm K L).dualSubmodule (I.restrictScalars A) := rfl

variable (A) in
/--
If the module `I` is spanned by the basis `b`, then its `traceDual` module is spanned by
`b.traceDual`.
-/
/-
**Submodule.traceDual_span_of_basis** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：traceDual_span_of_basis [FiniteDimensional K L] [Algebra.IsSeparable K L] 
(I : Submodule B L) {ι : Type*} [Finite ι] [DecidableEq ι] (b : Basis ι K L) (hb
 : I.restrictScalars A = Submodule.span A (Set.range b)) : (traceDual A K I).res
trictScalars A = span A (Set.range b.traceDual)
参数：I : Submodule B L；b : Basis ι K L；hb : I.restrictScalars A = Submodule.span A
 (Set.range b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Submodule.restrictScalars_traceDual`：restrictScalars_traceDual {I : Subm
odule B L} : Iᵛ.restrictScalars A = (Algebra.traceForm K L).dualSubmodule (I.res
trictScalars A)
· 使用引理 `LinearMap.BilinForm.dualSubmodule_span_of_basis`：dualSubmodule_span_of_b
asis {ι} [Finite ι] [DecidableEq ι] (hB : B.Nondegenerate) (b : Basis ι S M) : B
.dualSubmodule (Submodule.span R (Set…
· 使用定理 `traceForm_nondegenerate`：traceForm_nondegenerate [FiniteDimensional K L]
 [Algebra.IsSeparable K L] : (traceForm K L).Nondegenerate

--- 原说明 ---
If the module `I` is spanned by the basis `b`, then its `traceDual` module is sp
anned by
`b.traceDual`.
-/
theorem traceDual_span_of_basis [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (I : Submodule B L) {ι : Type*} [Finite ι] [DecidableEq ι] (b : Basis ι K L)
    (hb : I.restrictScalars A = Submodule.span A (Set.range b)) :
    (traceDual A K I).restrictScalars A = span A (Set.range b.traceDual) := by
  rw [restrictScalars_traceDual, hb]
  exact (traceForm K L).dualSubmodule_span_of_basis (traceForm_nondegenerate K L) b

@[simp]
/-
**Submodule.traceDual_bot** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：traceDual_bot : (⊥ : Submodule B L)ᵛ = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
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
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma traceDual_bot :
    (⊥ : Submodule B L)ᵛ = ⊤ := by ext; simp [mem_traceDual, -RingHom.mem_range]

open scoped Classical in
/-
**Submodule.traceDual_top'** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：traceDual_top' : (⊤ : Submodule B L)ᵛ = if ((LinearMap.range (Algebra.trac
e K L)).restrictScalars A <= 1) then ⊤ else ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_implies`：∀ (p : Prop), (True → p) = p
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `mul_inv_cancel_left₀`：mul_inv_cancel_left₀ (h : a != 0) (b : G₀) : a * (
a⁻¹ * b) = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma traceDual_top' :
    (⊤ : Submodule B L)ᵛ =
      if ((LinearMap.range (Algebra.trace K L)).restrictScalars A ≤ 1) then ⊤ else ⊥ := by
  split_ifs with h
  · rw [_root_.eq_top_iff]
    exact fun _ _ _ _ ↦ h ⟨_, rfl⟩
  · simp only [SetLike.le_def, restrictScalars_mem, LinearMap.mem_range, mem_one,
      forall_exists_index, forall_apply_eq_imp_iff, not_forall, not_exists] at h
    obtain ⟨b, hb⟩ := h
    simp_rw [eq_bot_iff, SetLike.le_def, mem_bot, mem_traceDual, mem_top, true_implies,
      traceForm_apply, RingHom.mem_range]
    contrapose! hb with hx'
    obtain ⟨c, hc, hc0⟩ := hx'
    simpa [hc0] using hc (c⁻¹ * b)

variable [IsDomain A] [IsFractionRing A K] [FiniteDimensional K L] [Algebra.IsSeparable K L]
/-
**Submodule.traceDual_top** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：traceDual_top [Decidable (IsField A)] : (⊤ : Submodule B L)ᵛ = if IsField 
A then ⊤ else ⊥
参数：IsField A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsFractionRing.surjective_iff_isField`：surjective_iff_isField [IsDomain 
R] : Function.Surjective (algebraMap R K) ↔ IsField R where mp h
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `Algebra.trace_surjective`：Algebra.trace_surjective [FiniteDimensional K 
L] [Algebra.IsSeparable K L] : Function.Surjective (Algebra.trace K L)
· 使用定理 `RingHom.range_eq_top`：range_eq_top {f : R ->+* S} : f.range = (⊤ : Subri
ng S) ↔ Function.Surjective f
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `Submodule.traceDual_top'`：traceDual_top' : (⊤ : Submodule B L)ᵛ = if ((L
inearMap.range (Algebra.trace K L)).restrictScalars A <= 1) then ⊤ else ⊥
-/
lemma traceDual_top [Decidable (IsField A)] :
    (⊤ : Submodule B L)ᵛ = if IsField A then ⊤ else ⊥ := by
  convert! traceDual_top'
  rw [← IsFractionRing.surjective_iff_isField (R := A) (K := K),
    LinearMap.range_eq_top.mpr (Algebra.trace_surjective K L),
    ← RingHom.range_eq_top, _root_.eq_top_iff]
  simp [SetLike.le_def]

end Submodule

open Submodule

variable [IsFractionRing A K]

variable (A K) in
/-
**map_equiv_traceDual** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：map_equiv_traceDual [IsDomain A] [IsFractionRing B L] [IsDomain B] [Faithf
ulSMul A B] (I : Submodule B (FractionRing B)) : (traceDual A (FractionRing A) I
).map (FractionRing.algEquiv B L).toLinearMap = traceDual A K (I.map (FractionRi
ng.algEquiv B L).toLinearMap)
参数：I : Submodule B (FractionRing B)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `FractionRing.instIsScalarTower`：∀ (R : Type u_1) [inst : CommRing R] (K 
: Type u_5) [inst_1 : Field K] [inst_2 : Algebra R K]   [inst_3 : FaithfulSMul R
 K] {R₀ : Type u_6} …
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `Submodule.map_equiv_eq_comap_symm`：map_equiv_eq_comap_symm (e : M ≃ₛₗ[τ₁
₂] M₂) (K : Submodule R M) : K.map (e : M ->ₛₗ[τ₁₂] M₂) = K.comap (e.symm : M₂ -
>ₛₗ[τ₂₁] M)
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.forall_congr`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} {q : β → 
Prop} (e : α ≃ β),   (∀ (a : α), p a ↔ q (e a)) → ((∀ (a : α), p a) ↔ ∀ (b : β),
 q b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgEquiv.symm_apply_apply`：symm_apply_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e.symm (e x) = x
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用引理 `Algebra.trace_eq_of_equiv_equiv`：Algebra.trace_eq_of_equiv_equiv {A₁ B₁ 
A₂ B₂ : Type*} [CommRing A₁] [CommRing B₁] [CommRing A₂] [CommRing B₂] [Algebra 
A₁ B₁] [Algebra A₂ B₂…
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `IsFractionRing.algEquiv_commutes`：algEquiv_commutes (e : K₁ ≃ₐ[A] K₂) (f
 : L₁ ≃ₐ[B] L₂) (x : K₁) : algebraMap K₂ L₂ (e x) = f (algebraMap K₁ L₁ x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma map_equiv_traceDual [IsDomain A] [IsFractionRing B L] [IsDomain B]
    [FaithfulSMul A B] (I : Submodule B (FractionRing B)) :
    (traceDual A (FractionRing A) I).map (FractionRing.algEquiv B L).toLinearMap =
      traceDual A K (I.map (FractionRing.algEquiv B L).toLinearMap) := by
  change Submodule.map (FractionRing.algEquiv B L).toLinearEquiv.toLinearMap _ =
    traceDual A K (I.map (FractionRing.algEquiv B L).toLinearEquiv.toLinearMap)
  rw [Submodule.map_equiv_eq_comap_symm, Submodule.map_equiv_eq_comap_symm]
  ext x
  simp only [traceDual, Submodule.mem_comap]
  apply (FractionRing.algEquiv B L).forall_congr
  simp only [restrictScalars_mem, LinearEquiv.coe_coe, AlgEquiv.coe_symm_toLinearEquiv,
    traceForm_apply, mem_one, AlgEquiv.toEquiv_eq_coe, EquivLike.coe_coe, mem_comap,
    AlgEquiv.symm_apply_apply]
  refine fun {y} ↦ (forall_congr' fun hy ↦ ?_)
  rw [Algebra.trace_eq_of_equiv_equiv (FractionRing.algEquiv A K).toRingEquiv
    (FractionRing.algEquiv B L).toRingEquiv]
  swap
  · ext
    exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv A K) (FractionRing.algEquiv B L) _
  simp only [map_mul, AlgEquiv.coe_ringEquiv,
    AlgEquiv.apply_symm_apply, ← AlgEquiv.symm_toRingEquiv, AlgEquiv.algebraMap_eq_apply]

variable [IsIntegrallyClosed A]
/-
**Submodule.mem_traceDual_iff_isIntegral** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Submodule.mem_traceDual_iff_isIntegral {I : Submodule B L} {x} : x in Iᵛ ↔
 forall a in I, IsIntegral A (traceForm K L x a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Submodule.mem_one`：mem_one {x : A} : x in (1 : Submodule R A) ↔ exists y
, algebraMap R A y = x
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `IsIntegrallyClosed.isIntegral_iff`：isIntegral_iff [IsIntegrallyClosed R]
 {x : K} : IsIntegral R x ↔ exists y : R, algebraMap R K y = x
-/
lemma Submodule.mem_traceDual_iff_isIntegral {I : Submodule B L} {x} :
    x ∈ Iᵛ ↔ ∀ a ∈ I, IsIntegral A (traceForm K L x a) :=
  forall₂_congr fun _ _ ↦ mem_one.trans IsIntegrallyClosed.isIntegral_iff.symm

variable [FiniteDimensional K L] [IsIntegralClosure B A L]
/-
**Submodule.one_le_traceDual_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Submodule.one_le_traceDual_one : (1 : Submodule B L) <= 1ᵛ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Submodule.le_traceDual_iff_map_le_one`：le_traceDual_iff_map_le_one {I J 
: Submodule B L} : I <= Jᵛ ↔ ((I * J : Submodule B L).restrictScalars A).map ((t
race K L).restrictScalars A…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Submodule.one_eq_range`：one_eq_range : (1 : Submodule R A) = LinearMap.r
ange (Algebra.linearMap R A)
· 使用定理 `Submodule.mem_one`：mem_one {x : A} : x in (1 : Submodule R A) ↔ exists y
, algebraMap R A y = x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsIntegrallyClosed.isIntegral_iff`：isIntegral_iff [IsIntegrallyClosed R]
 {x : K} : IsIntegral R x ↔ exists y : R, algebraMap R K y = x
· 使用定理 `Algebra.isIntegral_trace`：Algebra.isIntegral_trace [FiniteDimensional L 
F] {x : F} (hx : IsIntegral R x) : IsIntegral R (Algebra.trace L F x)
· 使用定理 `IsIntegralClosure.isIntegral_iff`：∀ {A : Type u_1} {R : Type u_2} {B : T
ype u_3} {inst : CommRing R} {inst_1 : CommSemiring A} {inst_2 : CommRing B}   {
inst_3 : Algebra R B} …
-/
lemma Submodule.one_le_traceDual_one :
    (1 : Submodule B L) ≤ 1ᵛ := by
  rw [le_traceDual_iff_map_le_one, mul_one, one_eq_range]
  rintro _ ⟨x, ⟨x, rfl⟩, rfl⟩
  rw [mem_one]
  apply IsIntegrallyClosed.isIntegral_iff.mp
  apply isIntegral_trace
  rw [IsIntegralClosure.isIntegral_iff (A := B)]
  exact ⟨_, rfl⟩

variable [Algebra.IsSeparable K L]

/-- If `b` is an `A`-integral basis of `L` with discriminant `b`, then `d • a * x` is integral over
  `A` for all `a ∈ I` and `x ∈ Iᵛ`. -/
/-
**isIntegral_discr_mul_of_mem_traceDual** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isIntegral_discr_mul_of_mem_traceDual (I : Submodule B L) {ι} [DecidableEq
 ι] [Fintype ι] {b : Basis ι K L} (hb : forall i, IsIntegral A (b i)) {a x : L} 
(ha : a in I) (hx : x in Iᵛ) : IsIntegral A ((discr K b) • a * x)
参数：I : Submodule B L；hb : forall i, IsIntegral A (b i)；ha : a in I；hx : x in Iᵛ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.discr_isUnit_of_basis`：discr_isUnit_of_basis [Algebra.IsSeparabl
e K L] (b : Basis ι K L) : IsUnit (discr K b)
· 使用定理 `Matrix.mulVec_cramer`：mulVec_cramer (A : Matrix n n α) (b : n -> α) : A 
*ᵥ cramer A b = A.det • b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.mulVec_injective_iff_isUnit`：mulVec_injective_iff_isUnit {A : Mat
rix m m K} : Function.Injective A.mulVec ↔ IsUnit A
· 使用定理 `Matrix.isUnit_iff_isUnit_det`：isUnit_iff_isUnit_det : IsUnit A ↔ IsUnit 
A.det
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用定理 `Module.Basis.equivFun_symm_apply`：∀ {ι : Type u_1} {R : Type u_3} {M : T
ype u_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Modul
e R M] [inst_3 : Finty…
· 使用定理 `IsIntegral.sum`：IsIntegral.sum {α : Type*} {s : Finset α} (f : α -> A) (
h : forall x in s, IsIntegral R (f x)) : IsIntegral R (∑ x in s, f x)
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearEquiv.map_smul`：map_smul (e : N₁ ≃ₗ[R₁] N₂) (c : R₁) (x : N₁) : e 
(c • x) = c • e x
· 使用定理 `Algebra.discr_def`：discr_def [Fintype ι] (b : ι -> B) : discr A b = (tra
ceMatrix A b).det
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Algebra.traceMatrix_of_basis_mulVec`：traceMatrix_of_basis_mulVec [Fintyp
e ι] (b : Basis ι A B) (z : B) : traceMatrix A b *ᵥ b.equivFun z = fun i => trac
e A B (z * b i)
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Matrix.mulVec_smul`：mulVec_smul [Fintype n] [DistribSMul R α] [SMulCommC
lass R α α] (M : Matrix m n α) (b : R) (v : n -> α) : M *ᵥ (b • v) = b • M *ᵥ v
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `RingHom.IsIntegralElem.mul`：RingHom.IsIntegralElem.mul {x y : S} (hx : f
.IsIntegralElem x) (hy : f.IsIntegralElem y) : f.IsIntegralElem (x * y)
· 使用定理 `IsIntegral.algebraMap`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [i
nst : CommRing R] [inst_1 : CommRing A] [inst_2 : Ring B]   [inst_3 : Algebra R 
A] [inst_4 …
· 使用定理 `Matrix.cramer_apply`：cramer_apply (i : n) : cramer A b i = (A.updateCol 
i b).det
· 使用定理 `IsIntegral.det`：IsIntegral.det {n : Type*} [Fintype n] [DecidableEq n] {
M : Matrix n n A} (h : forall i j, IsIntegral R (M i j)) : IsIntegral R M.det
· 使用定理 `Matrix.updateCol_apply`：updateCol_apply [DecidableEq n] {j' : n} : updat
eCol M j c i j' = if j' = j then c i else M i j'
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Algebra.isIntegral_trace`：Algebra.isIntegral_trace [FiniteDimensional L 
F] {x : F} (hx : IsIntegral R x) : IsIntegral R (Algebra.trace L F x)
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `Submodule.mem_traceDual_iff_isIntegral`：Submodule.mem_traceDual_iff_isIn
tegral {I : Submodule B L} {x} : x in Iᵛ ↔ forall a in I, IsIntegral A (traceFor
m K L x a)
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
If `b` is an `A`-integral basis of `L` with discriminant `b`, then `d • a * x` i
s integral over
  `A` for all `a ∈ I` and `x ∈ Iᵛ`.
-/
lemma isIntegral_discr_mul_of_mem_traceDual
    (I : Submodule B L) {ι} [DecidableEq ι] [Fintype ι]
    {b : Basis ι K L} (hb : ∀ i, IsIntegral A (b i))
    {a x : L} (ha : a ∈ I) (hx : x ∈ Iᵛ) :
    IsIntegral A ((discr K b) • a * x) := by
  have hinv : IsUnit (traceMatrix K b).det := by
    simpa [← discr_def] using discr_isUnit_of_basis _ b
  have H := mulVec_cramer (traceMatrix K b) fun i => trace K L (x * a * b i)
  have : Function.Injective (traceMatrix K b).mulVec := by
    rwa [mulVec_injective_iff_isUnit, isUnit_iff_isUnit_det]
  rw [← traceMatrix_of_basis_mulVec, ← mulVec_smul, this.eq_iff,
    traceMatrix_of_basis_mulVec] at H
  rw [← b.equivFun.symm_apply_apply (_ * _), b.equivFun_symm_apply]
  apply IsIntegral.sum
  intro i _
  rw [smul_mul_assoc, b.equivFun.map_smul, discr_def, mul_comm, ← H, Algebra.smul_def]
  refine RingHom.IsIntegralElem.mul _ ?_ (hb _)
  apply IsIntegral.algebraMap
  rw [cramer_apply]
  apply IsIntegral.det
  intro j k
  rw [updateCol_apply]
  split
  · rw [mul_assoc]
    rw [mem_traceDual_iff_isIntegral] at hx
    apply hx
    have ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := B)).mp (hb j)
    rw [mul_comm, ← hy, ← Algebra.smul_def]
    exact I.smul_mem _ (ha)
  · exact isIntegral_trace (RingHom.IsIntegralElem.mul _ (hb j) (hb k))

variable (A K)

variable [IsDomain A] [IsFractionRing B L] [Nontrivial B] [NoZeroDivisors B]

namespace FractionalIdeal

/-- The dual of a non-zero fractional ideal is the dual of the submodule under the trace form. -/
noncomputable
/-
**FractionalIdeal.dual** 是 Mathlib 中的一个定义，位于命名空间 `FractionalIdeal`。
形式化陈述：dual (I : FractionalIdeal B⁰ L) : FractionalIdeal B⁰ L
参数：I : FractionalIdeal B⁰ L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def dual (I : FractionalIdeal B⁰ L) :
    FractionalIdeal B⁰ L :=
  open scoped Classical in
  if hI : I = 0 then 0 else
  ⟨Iᵛ, by
    classical
    have ⟨s, b, hb⟩ := FiniteDimensional.exists_is_basis_integral A K L
    obtain ⟨x, hx, hx'⟩ := exists_ne_zero_mem_isInteger hI
    have ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := B)).mp
      (IsIntegral.algebraMap (B := L) (discr_isIntegral K hb))
    refine ⟨y * x, mem_nonZeroDivisors_iff_ne_zero.mpr (mul_ne_zero ?_ hx), fun z hz ↦ ?_⟩
    · rw [← (IsIntegralClosure.algebraMap_injective B A L).ne_iff, hy, map_zero,
        ← (algebraMap K L).map_zero, (algebraMap K L).injective.ne_iff]
      exact discr_not_zero_of_basis K b
    · convert! isIntegral_discr_mul_of_mem_traceDual I hb hx' hz using 1
      · ext w; exact (IsIntegralClosure.isIntegral_iff (A := B)).symm
      · rw [Algebra.smul_def, map_mul, hy, ← Algebra.smul_def]⟩

end FractionalIdeal

end BIsDomain

variable [IsDomain A] [IsFractionRing A K]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B A L]

namespace FractionalIdeal

variable [IsFractionRing B L] [IsIntegrallyClosed A]

open Submodule

local notation:max I:max "ᵛ" => Submodule.traceDual A K I

variable [IsDedekindDomain B] {I J : FractionalIdeal B⁰ L}

set_option backward.isDefEq.respectTransparency.types false in
/-
**FractionalIdeal.coe_dual** 是 Mathlib 中的一个引理，位于命名空间 `FractionalIdeal`。
形式化陈述：coe_dual (hI : I != 0) : (dual A K I : Submodule B L) = Iᵛ
参数：hI : I != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.dual.eq_1`：∀ (A : Type u_1) (K : Type u_2) {L : Type u} 
{B : Type u_3} [inst : CommRing A] [inst_1 : Field K] [inst_2 : CommRing B]   [i
nst_3 : Field L…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `FractionalIdeal.coe_mk`：coe_mk (I : Submodule R P) (hI : IsFractional S 
I) : coeToSubmodule ⟨I, hI⟩ = I
-/
lemma coe_dual (hI : I ≠ 0) :
    (dual A K I : Submodule B L) = Iᵛ := by rw [dual, dif_neg hI, coe_mk]

variable (B L)

@[simp]
/-
**FractionalIdeal.coe_dual_one** 是 Mathlib 中的一个引理，位于命名空间 `FractionalIdeal`。
形式化陈述：coe_dual_one : (dual A K (1 : FractionalIdeal B⁰ L) : Submodule B L) = 1ᵛ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FractionalIdeal.coe_one`：coe_one : (↑(1 : FractionalIdeal S P) : Submodu
le R P) = 1
· 使用引理 `FractionalIdeal.coe_dual`：coe_dual (hI : I != 0) : (dual A K I : Submodu
le B L) = Iᵛ
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FractionalIdeal.instNontrivialNonZeroDivisors`：∀ {R₁ : Type u_3} [inst :
 CommRing R₁] {K : Type u_4} [inst_1 : Field K] [inst_2 : Algebra R₁ K],   Nontr
ivial (FractionalIdeal (nonZeroDivi…
-/
lemma coe_dual_one :
    (dual A K (1 : FractionalIdeal B⁰ L) : Submodule B L) = 1ᵛ := by
  rw [← coe_one, coe_dual]
  exact one_ne_zero

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**FractionalIdeal.dual_zero** 是 Mathlib 中的一个引理，位于命名空间 `FractionalIdeal`。
形式化陈述：dual_zero : dual A K (0 : FractionalIdeal B⁰ L) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.dual.eq_1`：∀ (A : Type u_1) (K : Type u_2) {L : Type u} 
{B : Type u_3} [inst : CommRing A] [inst_1 : Field K] [inst_2 : CommRing B]   [i
nst_3 : Field L…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
lemma dual_zero :
    dual A K (0 : FractionalIdeal B⁰ L) = 0 := by rw [dual, dif_pos rfl]

variable {A K L B}

set_option backward.isDefEq.respectTransparency.types false in
/-
**FractionalIdeal.mem_dual** 是 Mathlib 中的一个引理，位于命名空间 `FractionalIdeal`。
形式化陈述：mem_dual (hI : I != 0) {x} : x in dual A K I ↔ forall a in I, traceForm K 
L x a in (algebraMap A K).range
参数：hI : I != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.dual.eq_1`：∀ (A : Type u_1) (K : Type u_2) {L : Type u} 
{B : Type u_3} [inst : CommRing A] [inst_1 : Field K] [inst_2 : CommRing B]   [i
nst_3 : Field L…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `Submodule.mem_one`：mem_one {x : A} : x in (1 : Submodule R A) ↔ exists y
, algebraMap R A y = x
-/
lemma mem_dual (hI : I ≠ 0) {x} :
    x ∈ dual A K I ↔ ∀ a ∈ I, traceForm K L x a ∈ (algebraMap A K).range := by
  rw [dual, dif_neg hI]; exact forall₂_congr fun _ _ ↦ mem_one

variable (A K)
/-
**FractionalIdeal.dual_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `FractionalIdeal`。
形式化陈述：dual_ne_zero (hI : I != 0) : dual A K I != 0
参数：hI : I != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `FractionalIdeal.mem_dual`：mem_dual (hI : I != 0) {x} : x in dual A K I ↔
 forall a in I, traceForm K L x a in (algebraMap A K).range
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsIntegrallyClosed.isIntegral_iff`：isIntegral_iff [IsIntegrallyClosed R]
 {x : K} : IsIntegral R x ↔ exists y : R, algebraMap R K y = x
· 使用定理 `Algebra.isIntegral_trace`：Algebra.isIntegral_trace [FiniteDimensional L 
F] {x : F} (hx : IsIntegral R x) : IsIntegral R (Algebra.trace L F x)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsIntegralClosure.isIntegral_iff`：∀ {A : Type u_1} {R : Type u_2} {B : T
ype u_3} {inst : CommRing R} {inst_1 : CommSemiring A} {inst_2 : CommRing B}   {
inst_3 : Algebra R B} …
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `mem_nonZeroDivisors_iff_ne_zero`：∀ {M₀ : Type u_2} [inst : MonoidWithZer
o M₀] {x : M₀} [NoZeroDivisors M₀] [Nontrivial M₀],   x ∈ nonZeroDivisors M₀ ↔ x
 ≠ 0
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `IsIntegralClosure.algebraMap_injective`：∀ (A : Type u_1) (R : Type u_2) 
(B : Type u_3) {inst : CommRing R} {inst_1 : CommSemiring A} {inst_2 : CommRing 
B}   {inst_3 : Algebra R B} …
· 使用定理 `RingHom.map_zero`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring 
α} {x_1 : NonAssocSemiring β} (f : α →+* β), f 0 = 0
· 使用定理 `FractionalIdeal.mem_zero_iff`：mem_zero_iff {x : P} : x in (0 : Fractiona
lIdeal S P) ↔ x = 0
-/
lemma dual_ne_zero (hI : I ≠ 0) :
    dual A K I ≠ 0 := by
  obtain ⟨b, hb, hb'⟩ := I.prop
  suffices algebraMap B L b ∈ dual A K I by
    intro e
    rw [e, mem_zero_iff, ← (algebraMap B L).map_zero,
      (IsIntegralClosure.algebraMap_injective B A L).eq_iff] at this
    exact mem_nonZeroDivisors_iff_ne_zero.mp hb this
  rw [mem_dual hI]
  intro a ha
  apply IsIntegrallyClosed.isIntegral_iff.mp
  apply isIntegral_trace
  dsimp
  convert! hb' a ha using 1
  · ext w
    exact IsIntegralClosure.isIntegral_iff (A := B)
  · exact (Algebra.smul_def _ _).symm

variable {A K}

@[simp]
/-
**FractionalIdeal.dual_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `FractionalIdeal`。
形式化陈述：dual_eq_zero_iff : dual A K I = 0 ↔ I = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用引理 `FractionalIdeal.dual_ne_zero`：dual_ne_zero (hI : I != 0) : dual A K I !=
 0
· 使用引理 `FractionalIdeal.dual_zero`：dual_zero : dual A K (0 : FractionalIdeal B⁰ 
L) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma dual_eq_zero_iff :
    dual A K I = 0 ↔ I = 0 :=
  ⟨not_imp_not.mp (dual_ne_zero A K), fun e ↦ e.symm ▸ dual_zero A K L B⟩
/-
**FractionalIdeal.dual_ne_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `FractionalIdeal`。
形式化陈述：dual_ne_zero_iff : dual A K I != 0 ↔ I != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用引理 `FractionalIdeal.dual_eq_zero_iff`：dual_eq_zero_iff : dual A K I = 0 ↔ I 
= 0
-/
lemma dual_ne_zero_iff :
    dual A K I ≠ 0 ↔ I ≠ 0 := dual_eq_zero_iff.not

variable (A K)

set_option backward.isDefEq.respectTransparency.types false in
/-
**FractionalIdeal.le_dual_inv_aux** 是 Mathlib 中的一个引理，位于命名空间 `FractionalIdeal`。
形式化陈述：le_dual_inv_aux (hI : I != 0) (hIJ : I * J <= 1) : J <= dual A K I
参数：hI : I != 0；hIJ : I * J <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.dual.eq_1`：∀ (A : Type u_1) (K : Type u_2) {L : Type u} 
{B : Type u_3} [inst : CommRing A] [inst_1 : Field K] [inst_2 : CommRing B]   [i
nst_3 : Field L…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Submodule.mem_one`：mem_one {x : A} : x in (1 : Submodule R A) ↔ exists y
, algebraMap R A y = x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsIntegrallyClosed.isIntegral_iff`：isIntegral_iff [IsIntegrallyClosed R]
 {x : K} : IsIntegral R x ↔ exists y : R, algebraMap R K y = x
· 使用定理 `Algebra.isIntegral_trace`：Algebra.isIntegral_trace [FiniteDimensional L 
F] {x : F} (hx : IsIntegral R x) : IsIntegral R (Algebra.trace L F x)
· 使用定理 `IsIntegralClosure.isIntegral_iff`：∀ {A : Type u_1} {R : Type u_2} {B : T
ype u_3} {inst : CommRing R} {inst_1 : CommSemiring A} {inst_2 : CommRing B}   {
inst_3 : Algebra R B} …
· 使用定理 `FractionalIdeal.mul_mem_mul`：mul_mem_mul {I J : FractionalIdeal S P} {i 
j : P} (hi : i in I) (hj : j in J) : i * j in I * J
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
lemma le_dual_inv_aux (hI : I ≠ 0) (hIJ : I * J ≤ 1) :
    J ≤ dual A K I := by
  rw [dual, dif_neg hI]
  intro x hx y hy
  rw [mem_one]
  apply IsIntegrallyClosed.isIntegral_iff.mp
  apply isIntegral_trace
  rw [IsIntegralClosure.isIntegral_iff (A := B)]
  have ⟨z, _, hz⟩ := hIJ (FractionalIdeal.mul_mem_mul hy hx)
  rw [mul_comm] at hz
  exact ⟨z, hz⟩
/-
**FractionalIdeal.one_le_dual_one** 是 Mathlib 中的一个引理，位于命名空间 `FractionalIdeal`。
形式化陈述：one_le_dual_one : 1 <= dual A K (1 : FractionalIdeal B⁰ L)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `FractionalIdeal.le_dual_inv_aux`：le_dual_inv_aux (hI : I != 0) (hIJ : I 
* J <= 1) : J <= dual A K I
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FractionalIdeal.instNontrivialNonZeroDivisors`：∀ {R₁ : Type u_3} [inst :
 CommRing R₁] {K : Type u_4} [inst_1 : Field K] [inst_2 : Algebra R₁ K],   Nontr
ivial (FractionalIdeal (nonZeroDivi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma one_le_dual_one :
    1 ≤ dual A K (1 : FractionalIdeal B⁰ L) :=
  le_dual_inv_aux A K one_ne_zero (by rw [one_mul])
/-
**FractionalIdeal.le_dual_iff** 是 Mathlib 中的一个引理，位于命名空间 `FractionalIdeal`。
形式化陈述：le_dual_iff (hJ : J != 0) : I <= dual A K J ↔ I * J <= dual A K 1
参数：hJ : J != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `FractionalIdeal.instCanonicallyOrderedAdd`：∀ {R : Type u_1} [inst : Comm
Ring R] {S : Submonoid R} {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra
 R P],   CanonicallyOrderedAdd …
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FractionalIdeal.coe_le_coe`：coe_le_coe {I J : FractionalIdeal S P} : (I 
: Submodule R P) <= (J : Submodule R P) ↔ I <= J
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `FractionalIdeal.coe_mul`：coe_mul (I J : FractionalIdeal S P) : (↑(I * J)
 : Submodule R P) = I * J
· 使用引理 `FractionalIdeal.coe_dual`：coe_dual (hI : I != 0) : (dual A K I : Submodu
le B L) = Iᵛ
· 使用引理 `FractionalIdeal.coe_dual_one`：coe_dual_one : (dual A K (1 : FractionalId
eal B⁰ L) : Submodule B L) = 1ᵛ
· 使用引理 `Submodule.le_traceDual`：le_traceDual {I J : Submodule B L} : I <= Jᵛ ↔ I
 * J <= 1ᵛ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma le_dual_iff (hJ : J ≠ 0) :
    I ≤ dual A K J ↔ I * J ≤ dual A K 1 := by
  by_cases hI : I = 0
  · simp [hI]
  rw [← coe_le_coe, ← coe_le_coe, coe_mul, coe_dual A K hJ, coe_dual_one, le_traceDual]

variable (I)
/-
**FractionalIdeal.inv_le_dual** 是 Mathlib 中的一个引理，位于命名空间 `FractionalIdeal`。
形式化陈述：inv_le_dual : I⁻¹ <= dual A K I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `FractionalIdeal.dual.congr_simp`：∀ (A : Type u_1) (K : Type u_2) {L : Ty
pe u} {B : Type u_3} [inst : CommRing A] [inst_1 : Field K] [inst_2 : CommRing B
]   [inst_3 : Field L…
· 使用引理 `FractionalIdeal.dual_zero`：dual_zero : dual A K (0 : FractionalIdeal B⁰ 
L) = 0
· 使用引理 `FractionalIdeal.le_dual_inv_aux`：le_dual_inv_aux (hI : I != 0) (hIJ : I 
* J <= 1) : J <= dual A K I
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
-/
lemma inv_le_dual :
    I⁻¹ ≤ dual A K I := by
  classical
  exact if hI : I = 0 then by simp [hI] else le_dual_inv_aux A K hI (le_of_eq (mul_inv_cancel₀ hI))
/-
**FractionalIdeal.dual_inv_le** 是 Mathlib 中的一个引理，位于命名空间 `FractionalIdeal`。
形式化陈述：dual_inv_le : (dual A K I)⁻¹ <= I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.dual.congr_simp`：∀ (A : Type u_1) (K : Type u_2) {L : Ty
pe u} {B : Type u_3} [inst : CommRing A] [inst_1 : Field K] [inst_2 : CommRing B
]   [inst_3 : Field L…
· 使用引理 `FractionalIdeal.dual_zero`：dual_zero : dual A K (0 : FractionalIdeal B⁰ 
L) = 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用引理 `inv_le_comm₀`：inv_le_comm₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ <= b ↔ b⁻¹ <=
 a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `FractionalIdeal.instPosMulReflectLENonZeroDivisors`：∀ {A : Type u_2} (K 
: Type u_3) [inst : CommRing A] [inst_1 : Field K] [IsDedekindDomain A] [inst_3 
: Algebra A K]   [IsFractionRing A K], P…
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `FractionalIdeal.instMulPosReflectLENonZeroDivisors`：∀ {A : Type u_2} (K 
: Type u_3) [inst : CommRing A] [inst_1 : Field K] [IsDedekindDomain A] [inst_3 
: Algebra A K]   [IsFractionRing A K], M…
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `FractionalIdeal.instCanonicallyOrderedAdd`：∀ {R : Type u_1} [inst : Comm
Ring R] {S : Submonoid R} {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra
 R P],   CanonicallyOrderedAdd …
· 使用引理 `FractionalIdeal.inv_le_dual`：inv_le_dual : I⁻¹ <= dual A K I
-/
lemma dual_inv_le :
    (dual A K I)⁻¹ ≤ I := by
  by_cases hI : I = 0; · simp [hI]
  rw [inv_le_comm₀ (by simpa [pos_iff_ne_zero]) (by simpa [pos_iff_ne_zero])]
  exact inv_le_dual ..
/-
**FractionalIdeal.dual_eq_mul_inv** 是 Mathlib 中的一个引理，位于命名空间 `FractionalIdeal`。
形式化陈述：dual_eq_mul_inv : dual A K I = dual A K 1 * I⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.dual.congr_simp`：∀ (A : Type u_1) (K : Type u_2) {L : Ty
pe u} {B : Type u_3} [inst : CommRing A] [inst_1 : Field K] [inst_2 : CommRing B
]   [inst_3 : Field L…
· 使用引理 `FractionalIdeal.dual_zero`：dual_zero : dual A K (0 : FractionalIdeal B⁰ 
L) = 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `le_mul_inv_iff₀`：le_mul_inv_iff₀ (hc : 0 < c) : a <= b * c⁻¹ ↔ a * c <= 
b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `FractionalIdeal.instMulPosReflectLENonZeroDivisors`：∀ {A : Type u_2} (K 
: Type u_3) [inst : CommRing A] [inst_1 : Field K] [IsDedekindDomain A] [inst_3 
: Algebra A K]   [IsFractionRing A K], M…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `FractionalIdeal.instCanonicallyOrderedAdd`：∀ {R : Type u_1} [inst : Comm
Ring R] {S : Submonoid R} {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra
 R P],   CanonicallyOrderedAdd …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `FractionalIdeal.le_dual_iff`：le_dual_iff (hJ : J != 0) : I <= dual A K J
 ↔ I * J <= dual A K 1
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma dual_eq_mul_inv :
    dual A K I = dual A K 1 * I⁻¹ := by
  by_cases hI : I = 0; · simp [hI]
  apply le_antisymm
  · rw [le_mul_inv_iff₀ (pos_iff_ne_zero.2 hI), ← le_dual_iff A K hI]
  rw [le_dual_iff A K hI, mul_assoc, inv_mul_cancel₀ hI, mul_one]

variable {I}
/-
**FractionalIdeal.dual_div_dual** 是 Mathlib 中的一个引理，位于命名空间 `FractionalIdeal`。
形式化陈述：dual_div_dual : dual A K J / dual A K I = I / J
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `FractionalIdeal.dual_eq_mul_inv`：dual_eq_mul_inv : dual A K I = dual A K
 1 * I⁻¹
· 使用定理 `mul_div_mul_comm`：mul_div_mul_comm : a * b / (c * d) = a / c * (b / d)
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FractionalIdeal.instNontrivialNonZeroDivisors`：∀ {R₁ : Type u_3} [inst :
 CommRing R₁] {K : Type u_4} [inst_1 : Field K] [inst_2 : Algebra R₁ K],   Nontr
ivial (FractionalIdeal (nonZeroDivi…
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `inv_div_inv`：inv_div_inv : a⁻¹ / b⁻¹ = b / a
-/
lemma dual_div_dual :
    dual A K J / dual A K I = I / J := by
  rw [dual_eq_mul_inv A K J, dual_eq_mul_inv A K I, mul_div_mul_comm, div_self, one_mul]
  · exact inv_div_inv J I
  · simp only [ne_eq, dual_eq_zero_iff, one_ne_zero, not_false_eq_true]
/-
**FractionalIdeal.dual_mul_self** 是 Mathlib 中的一个引理，位于命名空间 `FractionalIdeal`。
形式化陈述：dual_mul_self (hI : I != 0) : dual A K I * I = dual A K 1
参数：hI : I != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `FractionalIdeal.dual_eq_mul_inv`：dual_eq_mul_inv : dual A K I = dual A K
 1 * I⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma dual_mul_self (hI : I ≠ 0) :
    dual A K I * I = dual A K 1 := by
  rw [dual_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hI, mul_one]
/-
**FractionalIdeal.self_mul_dual** 是 Mathlib 中的一个引理，位于命名空间 `FractionalIdeal`。
形式化陈述：self_mul_dual (hI : I != 0) : I * dual A K I = dual A K 1
参数：hI : I != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `FractionalIdeal.dual_mul_self`：dual_mul_self (hI : I != 0) : dual A K I 
* I = dual A K 1
-/
lemma self_mul_dual (hI : I ≠ 0) :
    I * dual A K I = dual A K 1 := by
  rw [mul_comm, dual_mul_self A K hI]
/-
**FractionalIdeal.dual_inv** 是 Mathlib 中的一个引理，位于命名空间 `FractionalIdeal`。
形式化陈述：dual_inv : dual A K I⁻¹ = dual A K 1 * I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `FractionalIdeal.dual_eq_mul_inv`：dual_eq_mul_inv : dual A K I = dual A K
 1 * I⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
lemma dual_inv :
    dual A K I⁻¹ = dual A K 1 * I := by rw [dual_eq_mul_inv, inv_inv]

variable (I)

@[simp]
/-
**FractionalIdeal.dual_dual** 是 Mathlib 中的一个引理，位于命名空间 `FractionalIdeal`。
形式化陈述：dual_dual : dual A K (dual A K I) = I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `FractionalIdeal.dual_eq_mul_inv`：dual_eq_mul_inv : dual A K I = dual A K
 1 * I⁻¹
· 使用定理 `mul_inv`：mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用引理 `FractionalIdeal.dual_ne_zero_iff`：dual_ne_zero_iff : dual A K I != 0 ↔ I
 != 0
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FractionalIdeal.instNontrivialNonZeroDivisors`：∀ {R₁ : Type u_3} [inst :
 CommRing R₁] {K : Type u_4} [inst_1 : Field K] [inst_2 : Algebra R₁ K],   Nontr
ivial (FractionalIdeal (nonZeroDivi…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma dual_dual :
    dual A K (dual A K I) = I := by
  rw [dual_eq_mul_inv, dual_eq_mul_inv A K (I := I), mul_inv, inv_inv, ← mul_assoc, mul_inv_cancel₀,
    one_mul]
  rw [dual_ne_zero_iff]
  exact one_ne_zero

variable {I}

@[simp]
/-
**FractionalIdeal.dual_le_dual** 是 Mathlib 中的一个引理，位于命名空间 `FractionalIdeal`。
形式化陈述：dual_le_dual (hI : I != 0) (hJ : J != 0) : dual A K I <= dual A K J ↔ J <=
 I
参数：hI : I != 0；hJ : J != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `FractionalIdeal.dual_dual`：dual_dual : dual A K (dual A K I) = I
· 使用引理 `FractionalIdeal.le_dual_iff`：le_dual_iff (hJ : J != 0) : I <= dual A K J
 ↔ I * J <= dual A K 1
· 使用引理 `FractionalIdeal.dual_ne_zero_iff`：dual_ne_zero_iff : dual A K I != 0 ↔ I
 != 0
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma dual_le_dual (hI : I ≠ 0) (hJ : J ≠ 0) :
    dual A K I ≤ dual A K J ↔ J ≤ I := by
  nth_rewrite 2 [← dual_dual A K I]
  rw [le_dual_iff A K hJ, le_dual_iff A K (I := J) (by rwa [dual_ne_zero_iff]), mul_comm]

variable {A K}
/-
**FractionalIdeal.dual_involutive** 是 Mathlib 中的一个引理，位于命名空间 `FractionalIdeal`。
形式化陈述：dual_involutive : Function.Involutive (dual A K : FractionalIdeal B⁰ L -> 
FractionalIdeal B⁰ L)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `FractionalIdeal.dual_dual`：dual_dual : dual A K (dual A K I) = I
-/
lemma dual_involutive :
    Function.Involutive (dual A K : FractionalIdeal B⁰ L → FractionalIdeal B⁰ L) := dual_dual A K
/-
**FractionalIdeal.dual_injective** 是 Mathlib 中的一个引理，位于命名空间 `FractionalIdeal`。
形式化陈述：dual_injective : Function.Injective (dual A K : FractionalIdeal B⁰ L -> Fr
actionalIdeal B⁰ L)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.injective`：∀ {α : Sort u} {f : α → α}, Function.Invo
lutive f → Function.Injective f
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用引理 `FractionalIdeal.dual_involutive`：dual_involutive : Function.Involutive (
dual A K : FractionalIdeal B⁰ L -> FractionalIdeal B⁰ L)
-/
lemma dual_injective :
    Function.Injective (dual A K : FractionalIdeal B⁰ L → FractionalIdeal B⁰ L) :=
  dual_involutive.injective

variable (A K B L)

attribute [local instance] SMulCommClass.of_commMonoid

variable (C M : Type*) [CommRing C] [IsDedekindDomain C] [Field M] [Algebra C M]
  [IsFractionRing C M] [Algebra A C] [Algebra B C] [Algebra A M] [Algebra B M] [Algebra K M]
  [Algebra L M] [IsScalarTower A C M] [IsScalarTower A K M] [IsScalarTower B C M]
  [IsScalarTower B L M] [IsScalarTower K L M] [IsIntegralClosure C A M] [FiniteDimensional K M]
  [FiniteDimensional L M] [Algebra.IsSeparable K M]
/-
**FractionalIdeal.trace_mem_dual_one** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`
。
形式化陈述：trace_mem_dual_one (x : M) (hx : x in dual A K (1 : FractionalIdeal C⁰ M))
 : Algebra.trace L M x in dual A K (1 : FractionalIdeal B⁰ L)
参数：x : M；hx : x in dual A K (1 : FractionalIdeal C⁰ M)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.instNontrivialNonZeroDivisors`：∀ {R₁ : Type u_3} [inst :
 CommRing R₁] {K : Type u_4} [inst_1 : Field K] [inst_2 : Algebra R₁ K],   Nontr
ivial (FractionalIdeal (nonZeroDivi…
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.trace_trace`：trace_trace [Algebra S T] [IsScalarTower R S T] [Mo
dule.Free R S] [Module.Finite R S] [Module.Free S T] [Module.Finite S T] (x : T)
 : trace …
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Module.FaithfullyFlat.toFlat`：∀ {R : Type u} {M : Type v} {inst : CommRi
ng R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : Module.Fa
ithfullyFlat R M],…
· 使用定理 `Module.FaithfullyFlat.instOfNontrivialOfFree`：∀ (R : Type u) (M : Type v
) [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] [No
ntrivial M]   [Module.Free R M], M…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
-/
theorem trace_mem_dual_one (x : M) (hx : x ∈ dual A K (1 : FractionalIdeal C⁰ M)) :
    Algebra.trace L M x ∈ dual A K (1 : FractionalIdeal B⁰ L) := by
  simp only [ne_eq, one_ne_zero, not_false_eq_true, mem_dual, mem_one_iff, traceForm_apply,
    RingHom.mem_range, forall_exists_index, forall_apply_eq_imp_iff,
    mul_comm _ (algebraMap _ _ _), ← Algebra.smul_def, ← LinearMap.map_smul_of_tower,
    Algebra.trace_trace] at hx ⊢
  simpa using fun b ↦ hx (algebraMap B C b)

variable [IsIntegralClosure C B M] [Algebra.IsSeparable L M]
/-
**FractionalIdeal.smul_mem_dual_one** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：smul_mem_dual_one {x : L} (hx : x in dual A K (1 : FractionalIdeal B⁰ L)) 
{y : M} (hy : y in dual B L (1 : FractionalIdeal C⁰ M)) : x • y in dual A K (1 :
 FractionalIdeal C⁰ M)
参数：hx : x in dual A K (1 : FractionalIdeal B⁰ L)；hy : y in dual B L (1 : Fractio
nalIdeal C⁰ M)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.instNontrivialNonZeroDivisors`：∀ {R₁ : Type u_3} [inst :
 CommRing R₁] {K : Type u_4} [inst_1 : Field K] [inst_2 : Algebra R₁ K],   Nontr
ivial (FractionalIdeal (nonZeroDivi…
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用引理 `SMulCommClass.of_commMonoid`：SMulCommClass.of_commMonoid (A B G : Type*)
 [CommMonoid G] [SMul A G] [SMul B G] [IsScalarTower A G G] [IsScalarTower B G G
] : SMulCommClass…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.trace_trace`：trace_trace [Algebra S T] [IsScalarTower R S T] [Mo
dule.Free R S] [Module.Finite R S] [Module.Free S T] [Module.Finite S T] (x : T)
 : trace …
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Module.FaithfullyFlat.toFlat`：∀ {R : Type u} {M : Type v} {inst : CommRi
ng R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : Module.Fa
ithfullyFlat R M],…
· 使用定理 `Module.FaithfullyFlat.instOfNontrivialOfFree`：∀ (R : Type u) (M : Type v
) [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] [No
ntrivial M]   [Module.Free R M], M…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
-/
theorem smul_mem_dual_one {x : L} (hx : x ∈ dual A K (1 : FractionalIdeal B⁰ L))
    {y : M} (hy : y ∈ dual B L (1 : FractionalIdeal C⁰ M)) :
    x • y ∈ dual A K (1 : FractionalIdeal C⁰ M) := by
  simp only [ne_eq, one_ne_zero, not_false_eq_true, mem_dual, mem_one_iff, traceForm_apply,
    RingHom.mem_range, forall_exists_index, forall_apply_eq_imp_iff, mul_comm _ (algebraMap _ _ _),
    ← Algebra.smul_def] at hx hy ⊢
  intro c
  obtain ⟨b, hb⟩ := hy c
  obtain ⟨a, ha⟩ := hx b
  use a
  simpa [Algebra.smul_def b, hb, mul_comm _ x, ← smul_eq_mul, ← (Algebra.trace L M).map_smul,
    Algebra.trace_trace, smul_comm x c y] using ha

variable [IsTorsionFree B C]
/-
**FractionalIdeal.dual_eq_dual_mul_dual** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIde
al`。
形式化陈述：dual_eq_dual_mul_dual : dual A K (1 : FractionalIdeal C⁰ M) = dual B L (1 
: FractionalIdeal C⁰ M) * (dual A K (1 : FractionalIdeal B⁰ L)).extendedHom M C
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegralClosure.isLocalization`：IsIntegralClosure.isLocalization [IsDo
main A] [Algebra.IsAlgebraic K L] : IsLocalization (Algebra.algebraMapSubmonoid 
C A⁰) L
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `nonZeroDivisors_le_comap_nonZeroDivisors_of_injective`：nonZeroDivisors_l
e_comap_nonZeroDivisors_of_injective [NoZeroDivisors M₀'] [MonoidWithZeroHomClas
s F M₀ M₀'] (f : F) (hf : Injective f) : M₀…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsLocalization.algebraMap_apply_eq_map_map_submonoid`：IsLocalization.alg
ebraMap_apply_eq_map_map_submonoid (x) : algebraMap Rₘ Sₘ x = map Sₘ (algebraMap
 R S) (show _ <= (Algebra.algebraMapSubmon…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FractionalIdeal.spanSingleton_le_iff_mem`：spanSingleton_le_iff_mem {x : 
P} {I : FractionalIdeal S P} : spanSingleton S x <= I ↔ x in I
· 使用引理 `mul_inv_le_iff₀`：mul_inv_le_iff₀ (hc : 0 < c) : b * c⁻¹ <= a ↔ b <= a * 
c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `FractionalIdeal.instMulPosReflectLENonZeroDivisors`：∀ {A : Type u_2} (K 
: Type u_3) [inst : CommRing A] [inst_1 : Field K] [IsDedekindDomain A] [inst_3 
: Algebra A K]   [IsFractionRing A K], M…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FractionalIdeal.instNontrivialNonZeroDivisors`：∀ {R₁ : Type u_3} [inst :
 CommRing R₁] {K : Type u_4} [inst_1 : Field K] [inst_2 : Algebra R₁ K],   Nontr
ivial (FractionalIdeal (nonZeroDivi…
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `FractionalIdeal.coe_le_coe`：coe_le_coe {I J : FractionalIdeal S P} : (I 
: Submodule R P) <= (J : Submodule R P) ↔ I <= J
· 使用定理 `FractionalIdeal.extendedHom'_apply`：∀ {A : Type u_1} [inst : CommRing A]
 {B : Type u_2} [inst_1 : CommRing B] {f : A →+* B} {K : Type u_3} {M : Submonoi
d A}   [inst_2 : CommRin…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
（共 51 条，此处仅展示前 30 条）
-/
theorem dual_eq_dual_mul_dual :
    dual A K (1 : FractionalIdeal C⁰ M) = dual B L (1 : FractionalIdeal C⁰ M) *
        (dual A K (1 : FractionalIdeal B⁰ L)).extendedHom M C := by
  have := IsIntegralClosure.isLocalization B L M C
  have h : B⁰ ≤ Submonoid.comap (algebraMap B C) C⁰ :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ <| FaithfulSMul.algebraMap_injective _ _
  have h_alg {x : L} : algebraMap L M x = IsLocalization.map M (algebraMap B C) h x :=
    IsLocalization.algebraMap_apply_eq_map_map_submonoid B⁰ C L M x
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [← spanSingleton_le_iff_mem, ← mul_inv_le_iff₀ (bot_lt_iff_ne_bot.mpr
      (by simp [-extendedHom'_apply])), ← map_inv₀, ← FractionalIdeal.coe_le_coe,
        extendedHom'_apply, coe_mul, coe_spanSingleton, coe_extended_eq_span, coe_dual_one,
        span_mul_span, span_le]
    rintro _ ⟨x, rfl, _, ⟨a, ha, rfl⟩, rfl⟩ _ ⟨m, rfl⟩
    simp only [← h_alg, mul_comm _ (algebraMap _ _ _), ← Algebra.smul_def a, map_smul,
      LinearMap.toSpanSingleton_apply, Algebra.smul_def m, mul_one,
      LinearMap.smul_apply, traceForm_apply, smul_eq_mul]
    rw [← FractionalIdeal.coe_one (S := B⁰)]
    refine (mem_inv_iff (by simp)).mp ha _ (trace_mem_dual_one A K L B C M _ ?_)
    exact Algebra.smul_def m x ▸ smul_mem _ _ hx
  · rw [← FractionalIdeal.coe_le_coe, coe_mul, extendedHom'_apply,
      coe_extended_eq_span, ← span_eq (coeToSubmodule _), span_mul_span, span_le]
    rintro _ ⟨a, ha, _, ⟨b, hb, rfl⟩, rfl⟩
    simp only [SetLike.mem_coe, mem_coe, ← h_alg, mul_comm a, ← Algebra.smul_def] at ha hb ⊢
    exact smul_mem_dual_one A K L B C M hb ha

end FractionalIdeal

section IsIntegrallyClosed

variable (B)
variable [IsIntegrallyClosed A] [IsDedekindDomain B] [IsTorsionFree A B]

/-- The different ideal of an extension of integral domains `B/A` is the inverse of the dual of `A`
as an ideal of `B`. See `coeIdeal_differentIdeal` and `coeSubmodule_differentIdeal`. -/
/-
**differentIdeal** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：differentIdeal : Ideal B
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A

--- 原说明 ---
The different ideal of an extension of integral domains `B/A` is the inverse of 
the dual of `A`
as an ideal of `B`. See `coeIdeal_differentIdeal` and `coeSubmodule_differentIde
al`.
-/
noncomputable def differentIdeal : Ideal B :=
  (1 / Submodule.traceDual A (FractionRing A) 1 : Submodule B (FractionRing B)).comap
    (Algebra.linearMap B (FractionRing B))
/-
**coeSubmodule_differentIdeal_fractionRing** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：coeSubmodule_differentIdeal_fractionRing [Algebra.IsIntegral A B] [Algebra
.IsSeparable (FractionRing A) (FractionRing B)] [FiniteDimensional (FractionRing
 A) (FractionRing B)] : coeSubmodule (FractionRing B) (differentIdeal A B) = 1 /
 Submodule.traceDual A (FractionRing A) 1
参数：FractionRing A；FractionRing B；FractionRing A；FractionRing B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `FractionRing.instIsScalarTower`：∀ (R : Type u_1) [inst : CommRing R] (K 
: Type u_5) [inst_1 : Field K] [inst_2 : Algebra R K]   [inst_3 : FaithfulSMul R
 K] {R₀ : Type u_6} …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.coeSubmodule.eq_1`：∀ {R : Type u_1} [inst : CommSemiring 
R] (S : Type u_2) [inst_1 : CommSemiring S] [inst_2 : Algebra R S] (I : Ideal R)
,   IsLocalization.coe…
· 使用定理 `differentIdeal.eq_1`：∀ (A : Type u_1) (B : Type u_3) [inst : CommRing A]
 [inst_1 : CommRing B] [inst_2 : Algebra A B] [inst_3 : IsDomain A]   [inst_4 : 
IsDedekin…
· 使用定理 `Submodule.map_comap_eq`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_5} 
{M₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMo
noid M] [ins…
· 使用定理 `inf_eq_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
= b ↔ b ≤ a
· 使用定理 `IsIntegralClosure.of_isIntegrallyClosed`：∀ (R : Type u_1) (S : Type u_2)
 [inst : CommRing R] [inst_1 : CommRing S] (K : Type u_3) [inst_2 : CommRing K] 
  [inst_3 : Algebra R K] [ifr…
· 使用引理 `FractionalIdeal.dual_inv_le`：dual_inv_le : (dual A K I)⁻¹ <= I
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Submodule.one_eq_range`：one_eq_range : (1 : Submodule R A) = LinearMap.r
ange (Algebra.linearMap R A)
· 使用定理 `Submodule.traceDual.congr_simp`：∀ (A : Type u_1) (K : Type u_2) {L : Typ
e u} {B : Type u_3} [inst : CommRing A] [inst_1 : Field K] [inst_2 : CommRing B]
   [inst_3 : Field L…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FractionalIdeal.coe_one`：coe_one : (↑(1 : FractionalIdeal S P) : Submodu
le R P) = 1
· 使用引理 `FractionalIdeal.coe_dual`：coe_dual (hI : I != 0) : (dual A K I : Submodu
le B L) = Iᵛ
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FractionalIdeal.instNontrivialNonZeroDivisors`：∀ {R₁ : Type u_3} [inst :
 CommRing R₁] {K : Type u_4} [inst_1 : Field K] [inst_2 : Algebra R₁ K],   Nontr
ivial (FractionalIdeal (nonZeroDivi…
· 使用定理 `FractionalIdeal.coe_div`：coe_div {I J : FractionalIdeal R₁⁰ K} (hJ : J !
= 0) : (↑(I / J) : Submodule R₁ K) = ↑I / (↑J : Submodule R₁ K)
· 使用引理 `FractionalIdeal.dual_ne_zero`：dual_ne_zero (hI : I != 0) : dual A K I !=
 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
-/
lemma coeSubmodule_differentIdeal_fractionRing [Algebra.IsIntegral A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    [FiniteDimensional (FractionRing A) (FractionRing B)] :
    coeSubmodule (FractionRing B) (differentIdeal A B) =
      1 / Submodule.traceDual A (FractionRing A) 1 := by
  rw [coeSubmodule, differentIdeal, Submodule.map_comap_eq, inf_eq_right]
  have := FractionalIdeal.dual_inv_le (A := A) (K := FractionRing A)
    (1 : FractionalIdeal B⁰ (FractionRing B))
  have : _ ≤ ((1 : FractionalIdeal B⁰ (FractionRing B)) : Submodule B (FractionRing B)) := this
  rw [← one_div, FractionalIdeal.coe_div (FractionalIdeal.dual_ne_zero _ _ _),
    FractionalIdeal.coe_dual] at this
  · simpa only [FractionalIdeal.coe_one, Submodule.one_eq_range] using this
  · exact one_ne_zero
  · exact one_ne_zero

section

variable [IsFractionRing B L]

/-
**coeSubmodule_differentIdeal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：coeSubmodule_differentIdeal : coeSubmodule L (differentIdeal A B) = 1 / Su
bmodule.traceDual A K 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsLocalization.coeSubmodule.eq_1`：∀ {R : Type u_1} [inst : CommSemiring 
R] (S : Type u_2) [inst_1 : CommSemiring S] [inst_2 : Algebra R S] (I : Ideal R)
,   IsLocalization.coe…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `IsLocalization.ringHom_ext`：ringHom_ext {P : Type*} [Semiring P] ⦃j k : 
S ->+* P⦄ (h : j.comp (algebraMap R S) = k.comp (algebraMap R S)) : j = k
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `AlgEquiv.commutes`：commutes : forall r : R, e (algebraMap R A₁ r) = alge
braMap R A₂ r
· 使用定理 `FractionRing.instIsScalarTower`：∀ (R : Type u_1) [inst : CommRing R] (K 
: Type u_5) [inst_1 : Field K] [inst_2 : Algebra R K]   [inst_3 : FaithfulSMul R
 K] {R₀ : Type u_6} …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用引理 `Algebra.IsSeparable.of_equiv_equiv`：Algebra.IsSeparable.of_equiv_equiv [
Algebra.IsSeparable A₁ B₁] : Algebra.IsSeparable A₂ B₂
（共 45 条，此处仅展示前 30 条）
-/
lemma coeSubmodule_differentIdeal :
    coeSubmodule L (differentIdeal A B) = 1 / Submodule.traceDual A K 1 := by
  have : (FractionRing.algEquiv B L).toLinearEquiv.comp (Algebra.linearMap B (FractionRing B)) =
    Algebra.linearMap B L := by ext; simp
  rw [coeSubmodule, ← this]
  have H : RingHom.comp (algebraMap (FractionRing A) (FractionRing B))
      ↑(FractionRing.algEquiv A K).symm.toRingEquiv =
        RingHom.comp ↑(FractionRing.algEquiv B L).symm.toRingEquiv (algebraMap K L) := by
    apply IsLocalization.ringHom_ext A⁰
    ext
    simp only [RingHom.coe_comp, RingHom.coe_coe,
      AlgEquiv.coe_ringEquiv, Function.comp_apply, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply A B L, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  have : Algebra.IsSeparable (FractionRing A) (FractionRing B) :=
    Algebra.IsSeparable.of_equiv_equiv _ _ H
  have : FiniteDimensional (FractionRing A) (FractionRing B) := Module.Finite.of_equiv_equiv _ _ H
  have : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra _ L
  simp only [AlgEquiv.toLinearEquiv_toLinearMap, Submodule.map_comp]
  rw [← coeSubmodule, coeSubmodule_differentIdeal_fractionRing _ _,
    Submodule.map_div, AlgEquiv.toLinearMap, ← AlgEquiv.toAlgHom_toLinearMap, Submodule.map_one]
  congr 1
  refine (map_equiv_traceDual A K _).trans ?_
  congr 1
  ext
  simp

variable (L)
/-
**coeIdeal_differentIdeal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：coeIdeal_differentIdeal : ↑(differentIdeal A B) = (FractionalIdeal.dual A 
K (1 : FractionalIdeal B⁰ L))⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.coeToSubmodule_injective`：coeToSubmodule_injective : Fun
ction.Injective (fun (I : FractionalIdeal S P) => (I : Submodule R P))
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `coeSubmodule_differentIdeal`：coeSubmodule_differentIdeal : coeSubmodule 
L (differentIdeal A B) = 1 / Submodule.traceDual A K 1
· 使用定理 `inv_eq_one_div`：inv_eq_one_div (x : G) : x⁻¹ = 1 / x
· 使用定理 `FractionalIdeal.coe_div`：coe_div {I J : FractionalIdeal R₁⁰ K} (hJ : J !
= 0) : (↑(I / J) : Submodule R₁ K) = ↑I / (↑J : Submodule R₁ K)
· 使用引理 `FractionalIdeal.dual_ne_zero`：dual_ne_zero (hI : I != 0) : dual A K I !=
 0
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FractionalIdeal.instNontrivialNonZeroDivisors`：∀ {R₁ : Type u_3} [inst :
 CommRing R₁] {K : Type u_4} [inst_1 : Field K] [inst_2 : Algebra R₁ K],   Nontr
ivial (FractionalIdeal (nonZeroDivi…
· 使用定理 `FractionalIdeal.coe_one`：coe_one : (↑(1 : FractionalIdeal S P) : Submodu
le R P) = 1
· 使用引理 `FractionalIdeal.coe_dual_one`：coe_dual_one : (dual A K (1 : FractionalId
eal B⁰ L) : Submodule B L) = 1ᵛ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coeIdeal_differentIdeal :
    ↑(differentIdeal A B) = (FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L))⁻¹ := by
  apply FractionalIdeal.coeToSubmodule_injective
  simp only [FractionalIdeal.coe_div
    (FractionalIdeal.dual_ne_zero _ _ (@one_ne_zero (FractionalIdeal B⁰ L) _ _ _)),
    FractionalIdeal.coe_coeIdeal, coeSubmodule_differentIdeal A K, inv_eq_one_div,
    FractionalIdeal.coe_dual_one, FractionalIdeal.coe_one]

variable {A K B L}
/-
**differentIdeal_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentIdeal_ne_bot [Module.Finite A B] [Algebra.IsSeparable (FractionRi
ng A) (FractionRing B)] : differentIdeal A B != ⊥
参数：FractionRing A；FractionRing B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FractionalIdeal.coeIdeal_inj`：coeIdeal_inj {I J : Ideal R} : (I : Fracti
onalIdeal R⁰ K) = (J : FractionalIdeal R⁰ K) ↔ I = J
· 使用定理 `FractionRing.instIsScalarTower`：∀ (R : Type u_1) [inst : CommRing R] (K 
: Type u_5) [inst_1 : Field K] [inst_2 : Algebra R K]   [inst_3 : FaithfulSMul R
 K] {R₀ : Type u_6} …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `instFiniteDimensionalFractionRingOfFinite`：∀ {R : Type u_1} {S : Type u_
2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] [inst_3 : Is
Domain R]   [inst_4 : IsDomain …
· 使用定理 `IsIntegralClosure.of_isIntegrallyClosed`：∀ (R : Type u_1) (S : Type u_2)
 [inst : CommRing R] [inst_1 : CommRing S] (K : Type u_3) [inst_2 : CommRing K] 
  [inst_3 : Algebra R K] [ifr…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用引理 `coeIdeal_differentIdeal`：coeIdeal_differentIdeal : ↑(differentIdeal A B)
 = (FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L))⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FractionalIdeal.instNontrivialNonZeroDivisors`：∀ {R₁ : Type u_3} [inst :
 CommRing R₁] {K : Type u_4} [inst_1 : Field K] [inst_2 : Algebra R₁ K],   Nontr
ivial (FractionalIdeal (nonZeroDivi…
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem differentIdeal_ne_bot [Module.Finite A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)] :
    differentIdeal A B ≠ ⊥ := by
  let K := FractionRing A
  let L := FractionRing B
  rw [ne_eq, ← FractionalIdeal.coeIdeal_inj (K := L), coeIdeal_differentIdeal (K := K)]
  simp
/-
**differentialIdeal_le_fractionalIdeal_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：differentialIdeal_le_fractionalIdeal_iff {I : FractionalIdeal B⁰ L} (hI : 
I != 0) : differentIdeal A B <= I ↔ (((I⁻¹ :) : Submodule B L).restrictScalars A
).map ((Algebra.trace K L).restrictScalars A) <= 1
参数：hI : I != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `coeIdeal_differentIdeal`：coeIdeal_differentIdeal : ↑(differentIdeal A B)
 = (FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L))⁻¹
· 使用引理 `FractionalIdeal.inv_le_comm`：inv_le_comm {I J : FractionalIdeal A⁰ K} (h
I : I != 0) (hJ : J != 0) : I⁻¹ <= J ↔ J⁻¹ <= I
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FractionalIdeal.instNontrivialNonZeroDivisors`：∀ {R₁ : Type u_3} [inst :
 CommRing R₁] {K : Type u_4} [inst_1 : Field K] [inst_2 : Algebra R₁ K],   Nontr
ivial (FractionalIdeal (nonZeroDivi…
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FractionalIdeal.coe_le_coe`：coe_le_coe {I J : FractionalIdeal S P} : (I 
: Submodule R P) <= (J : Submodule R P) ↔ I <= J
· 使用引理 `FractionalIdeal.coe_dual_one`：coe_dual_one : (dual A K (1 : FractionalId
eal B⁰ L) : Submodule B L) = 1ᵛ
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `Submodule.le_traceDual_iff_map_le_one`：le_traceDual_iff_map_le_one {I J 
: Submodule B L} : I <= Jᵛ ↔ ((I * J : Submodule B L).restrictScalars A).map ((t
race K L).restrictScalars A…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `Submodule.restrictScalars.congr_simp`：∀ (S : Type u_1) {R : Type u_2} {M
 : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : Semiring S
]   [inst_3 : _root_.Modul…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma differentialIdeal_le_fractionalIdeal_iff
    {I : FractionalIdeal B⁰ L} (hI : I ≠ 0) :
    differentIdeal A B ≤ I ↔ (((I⁻¹ :) : Submodule B L).restrictScalars A).map
      ((Algebra.trace K L).restrictScalars A) ≤ 1 := by
  rw [coeIdeal_differentIdeal A K L B, FractionalIdeal.inv_le_comm (by simp) hI,
    ← FractionalIdeal.coe_le_coe, FractionalIdeal.coe_dual_one]
  refine le_traceDual_iff_map_le_one.trans ?_
  simp
/-
**differentialIdeal_le_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：differentialIdeal_le_iff {I : Ideal B} (hI : I != ⊥) : differentIdeal A B 
<= I ↔ (((I⁻¹ : FractionalIdeal B⁰ L) : Submodule B L).restrictScalars A).map ((
Algebra.trace K L).restrictScalars A) <= 1
参数：hI : I != ⊥。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `FractionalIdeal.coeIdeal_le_coeIdeal`：coeIdeal_le_coeIdeal (K : Type*) [
CommRing K] [Algebra R K] [IsFractionRing R K] {I J : Ideal R} : (I : Fractional
Ideal R⁰ K) <= J ↔ I <= J
· 使用引理 `differentialIdeal_le_fractionalIdeal_iff`：differentialIdeal_le_fractiona
lIdeal_iff {I : FractionalIdeal B⁰ L} (hI : I != 0) : differentIdeal A B <= I ↔ 
(((I⁻¹ :) : Submodule B L).res…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma differentialIdeal_le_iff {I : Ideal B} (hI : I ≠ ⊥) :
    differentIdeal A B ≤ I ↔ (((I⁻¹ : FractionalIdeal B⁰ L) : Submodule B L).restrictScalars A).map
      ((Algebra.trace K L).restrictScalars A) ≤ 1 :=
  (FractionalIdeal.coeIdeal_le_coeIdeal _).symm.trans
    (differentialIdeal_le_fractionalIdeal_iff (I := (I : FractionalIdeal B⁰ L)) (by simpa))

variable (A K B L)

set_option linter.overlappingInstances false

open FractionalIdeal in
/-- Transitivity of the different ideal. -/
/-
**differentIdeal_eq_differentIdeal_mul_differentIdeal** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：differentIdeal_eq_differentIdeal_mul_differentIdeal (C : Type*) [IsDomain 
B] [CommRing C] [Algebra B C] [Algebra A C] [IsDedekindDomain C] [Module.Finite 
A B] [Module.Finite A C] [Module.Finite B C] [IsTorsionFree A C] [IsTorsionFree 
B C] [IsScalarTower A B C] [Algebra.IsSeparable (FractionRing A) (FractionRing C
)] : differentIdeal A C = differentIdeal B C * (differentIdeal A B).map (algebra
Map B C)
参数：C : Type*；FractionRing A；FractionRing C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Module.Flat.instOfIsDedekindDomainOfIsTorsionFree`：∀ {R : Type u_1} {M :
 Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module
 R M]   [IsDedekindDomain R] [Module.Is…
· 使用定理 `Algebra.isSeparable_tower_top_of_isSeparable`：Algebra.isSeparable_tower_
top_of_isSeparable [Algebra.IsSeparable F E] : Algebra.IsSeparable L E
· 使用定理 `FractionRing.instIsScalarTower_1`：∀ (A : Type u_4) [inst : CommRing A] [
IsDomain A] (k : Type u_6) (K : Type u_7) [inst_2 : Field k] [inst_3 : Field K] 
  [inst_4 : Algebra A …
· 使用定理 `FractionRing.instIsScalarTower`：∀ (R : Type u_1) [inst : CommRing R] (K 
: Type u_5) [inst_1 : Field K] [inst_2 : Algebra R K]   [inst_3 : FaithfulSMul R
 K] {R₀ : Type u_6} …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `Algebra.isSeparable_tower_bot_of_isSeparable`：Algebra.isSeparable_tower_
bot_of_isSeparable [h : Algebra.IsSeparable F E] : Algebra.IsSeparable F K
· 使用定理 `FractionRing.instNontrivial`：∀ (R : Type u_1) [inst : CommRing R] [Nontr
ivial R], Nontrivial (FractionRing R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用引理 `Module.Finite.of_isLocalization`：of_isLocalization (R S) {Rₚ Sₚ : Type*}
 [CommSemiring R] [CommSemiring S] [CommSemiring Rₚ] [CommSemiring Sₚ] [Algebra 
R S] [Algebra R Rₚ] […
· 使用定理 `Algebra.IsAlgebraic.instIsLocalizationAlgebraMapSubmonoidNonZeroDivisors
`：∀ (R : Type u_1) (S : Type u_2) [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] (S' : Type u_5)   [inst_3 : CommRing S'] [F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FractionalIdeal.coeIdeal_inj`：coeIdeal_inj {I J : Ideal R} : (I : Fracti
onalIdeal R⁰ K) = (J : FractionalIdeal R⁰ K) ↔ I = J
· 使用定理 `FractionalIdeal.coeIdeal_mul`：coeIdeal_mul (I J : Ideal R) : (↑(I * J) :
 FractionalIdeal S P) = I * J
· 使用定理 `IsIntegralClosure.of_isIntegrallyClosed`：∀ (R : Type u_1) (S : Type u_2)
 [inst : CommRing R] [inst_1 : CommRing S] (K : Type u_3) [inst_2 : CommRing K] 
  [inst_3 : Algebra R K] [ifr…
· 使用引理 `coeIdeal_differentIdeal`：coeIdeal_differentIdeal : ↑(differentIdeal A B)
 = (FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L))⁻¹
· 使用定理 `FractionalIdeal.extendedHom_coeIdeal_eq_map`：extendedHom_coeIdeal_eq_map
 (I : Ideal A) : (I : FractionalIdeal A⁰ K).extendedHom L B = (I.map (algebraMap
 A B) : FractionalIdeal B⁰ L)
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `mul_inv`：mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹
· 使用定理 `inv_eq_iff_eq_inv`：inv_eq_iff_eq_inv : a⁻¹ = b ↔ a = b⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `FractionalIdeal.dual_eq_dual_mul_dual`：dual_eq_dual_mul_dual : dual A K 
(1 : FractionalIdeal C⁰ M) = dual B L (1 : FractionalIdeal C⁰ M) * (dual A K (1 
: FractionalIdeal B⁰ L)).ex…

--- 原说明 ---
Transitivity of the different ideal.
-/
theorem differentIdeal_eq_differentIdeal_mul_differentIdeal (C : Type*) [IsDomain B] [CommRing C]
    [Algebra B C] [Algebra A C] [IsDedekindDomain C]
    [Module.Finite A B] [Module.Finite A C] [Module.Finite B C]
    [IsTorsionFree A C] [IsTorsionFree B C] [IsScalarTower A B C]
    [Algebra.IsSeparable (FractionRing A) (FractionRing C)] :
    differentIdeal A C = differentIdeal B C * (differentIdeal A B).map (algebraMap B C) := by
  have : Algebra.IsSeparable (FractionRing B) (FractionRing C) :=
    isSeparable_tower_top_of_isSeparable (FractionRing A) _ _
  have : Algebra.IsSeparable (FractionRing A) (FractionRing B) :=
    isSeparable_tower_bot_of_isSeparable _ _ (FractionRing C)
  have : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  have : FiniteDimensional (FractionRing A) (FractionRing C) := .of_isLocalization A C A⁰
  have : FiniteDimensional (FractionRing B) (FractionRing C) := .of_isLocalization B C B⁰
  rw [← coeIdeal_inj (K := FractionRing C), coeIdeal_mul, coeIdeal_differentIdeal A
    (FractionRing A), coeIdeal_differentIdeal B (FractionRing B)]
  rw [← extendedHom_coeIdeal_eq_map (K := FractionRing B), coeIdeal_differentIdeal A
    (FractionRing A), map_inv₀, ← mul_inv, ← inv_eq_iff_eq_inv, inv_inv]
  exact dual_eq_dual_mul_dual A (FractionRing A) (FractionRing B) B C (FractionRing C)

variable {B L}
/-
**traceForm_dualSubmodule_adjoin** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：traceForm_dualSubmodule_adjoin {x : L} (hx : Algebra.adjoin K {x} = ⊤) (hA
x : IsIntegral A x) : (traceForm K L).dualSubmodule (Subalgebra.toSubmodule (Alg
ebra.adjoin A {x})) = (aeval x (derivative <| minpoly K x) : L)⁻¹ • (Subalgebra.
toSubmodule (Algebra.adjoin A {x}))
参数：hx : Algebra.adjoin K {x} = ⊤；hAx : IsIntegral A x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Algebra.adjoin.powerBasis'`：Algebra.adjoin.powerBasis'_minpoly_gen [IsDo
main R] [IsDomain S] [IsTorsionFree R S] [IsIntegrallyClosed R] {x : S} (hx' : I
sIntegral R x) :…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `Module.FaithfullyFlat.toFlat`：∀ {R : Type u} {M : Type v} {inst : CommRi
ng R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : Module.Fa
ithfullyFlat R M],…
· 使用定理 `Module.Flat.instOfIsDedekindDomainOfIsTorsionFree`：∀ {R : Type u_1} {M :
 Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module
 R M]   [IsDedekindDomain R] [Module.Is…
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Module.FaithfullyFlat.instOfNontrivialOfFree`：∀ (R : Type u) (M : Type v
) [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] [No
ntrivial M]   [Module.Free R M], M…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `PowerBasis.map_gen`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] 
[inst_1 : Ring S] [inst_2 : Algebra R S] {S' : Type u_7}   [inst_3 : CommRing S'
] [inst_…
· 使用定理 `Algebra.adjoin.powerBasis'_gen`：∀ {R : Type u_1} {S : Type u_2} [inst : 
CommRing R] [inst_1 : CommRing S] [inst_2 : IsDomain R] [inst_3 : Algebra R S]  
 [inst_4 : IsIntegra…
· 使用定理 `Subalgebra.equivOfEq_apply`：∀ {R : Type u} {A : Type v} [inst : CommSemi
ring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (S T : Subalgebra R A)   (h
 : S = T) (x : ↥…
· 使用定理 `Subalgebra.topEquiv_apply`：∀ {R : Type u} {A : Type v} [inst : CommSemir
ing R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (a : ↥⊤),   Subalgebra.topEq
uiv a = ↑a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `traceForm_nondegenerate`：traceForm_nondegenerate [FiniteDimensional K L]
 [Algebra.IsSeparable K L] : (traceForm K L).Nondegenerate
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
（共 61 条，此处仅展示前 30 条）
-/
lemma traceForm_dualSubmodule_adjoin
    {x : L} (hx : Algebra.adjoin K {x} = ⊤) (hAx : IsIntegral A x) :
    (traceForm K L).dualSubmodule (Subalgebra.toSubmodule (Algebra.adjoin A {x})) =
      (aeval x (derivative <| minpoly K x) : L)⁻¹ •
        (Subalgebra.toSubmodule (Algebra.adjoin A {x})) := by
  have hKx : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  let pb := (Algebra.adjoin.powerBasis' hKx).map
    ((Subalgebra.equivOfEq _ _ hx).trans (Subalgebra.topEquiv))
  have pbgen : pb.gen = x := by simp [pb]
  have hnondeg : (traceForm K L).Nondegenerate := traceForm_nondegenerate K L
  have hpb : ⇑(LinearMap.BilinForm.dualBasis (traceForm K L) hnondeg pb.basis) = _ :=
    _root_.funext (Basis.traceDual_powerBasis_eq pb)
  have : (Subalgebra.toSubmodule (Algebra.adjoin A {x})) =
      Submodule.span A (Set.range pb.basis) := by
    rw [← span_range_natDegree_eq_adjoin (minpoly.monic hAx) (minpoly.aeval _ _)]
    congr; ext y
    have : natDegree (minpoly A x) = natDegree (minpoly K x) := by
      rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hAx, (minpoly.monic hAx).natDegree_map]
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio, Set.mem_range,
      pb.basis_eq_pow, pbgen]
    simp only [this]
    exact ⟨fun ⟨a, b, c⟩ ↦ ⟨⟨a, b⟩, c⟩, fun ⟨⟨a, b⟩, c⟩ ↦ ⟨a, b, c⟩⟩
  clear_value pb
  conv_lhs => rw [this]
  rw [← span_coeff_minpolyDiv hAx, LinearMap.BilinForm.dualSubmodule_span_of_basis _ hnondeg,
    Submodule.smul_span, hpb]
  change _ = Submodule.span A (_ '' _)
  simp only [← Set.range_comp, smul_eq_mul, div_eq_inv_mul, pbgen,
    minpolyDiv_eq_of_isIntegrallyClosed K hAx]
  apply le_antisymm <;> rw [Submodule.span_le]
  · rintro _ ⟨i, rfl⟩; exact Submodule.subset_span ⟨i, rfl⟩
  · rintro _ ⟨i, rfl⟩
    by_cases! hi : i < pb.dim
    · exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
    · rw [Function.comp_apply, coeff_eq_zero_of_natDegree_lt, mul_zero]
      · exact zero_mem _
      rw [← pb.natDegree_minpoly, pbgen, ← natDegree_minpolyDiv_succ hKx,
        ← Nat.succ_eq_add_one] at hi
      exact hi

end

variable (L) {B}

open Polynomial Pointwise in
/-
**conductor_mul_differentIdeal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：conductor_mul_differentIdeal (x : B) (hx : Algebra.adjoin K {algebraMap B 
L x} = ⊤) : (conductor A x) * differentIdeal A B = Ideal.span {aeval x (derivati
ve (minpoly A x))}
参数：x : B；hx : Algebra.adjoin K {algebraMap B L x} = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegralClosure.isIntegral`：∀ (R : Type u_1) {A : Type u_2} (B : Type 
u_3) [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : CommRing B]   [inst_3 :
 Algebra R B] [ins…
· 使用定理 `IsIntegralClosure.isFractionRing_of_finite_extension`：isFractionRing_of_
finite_extension [IsDomain A] [Algebra K L] [IsScalarTower A K L] [FiniteDimensi
onal K L] : IsFractionRing C L
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `FractionalIdeal.coeIdeal_injective`：coeIdeal_injective : Function.Inject
ive (fun (I : Ideal R) => (I : FractionalIdeal R⁰ K))
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.coeIdeal_mul`：coeIdeal_mul (I J : Ideal R) : (↑(I * J) :
 FractionalIdeal S P) = I * J
· 使用定理 `FractionalIdeal.coeIdeal_span_singleton`：coeIdeal_span_singleton (x : R)
 : (↑(Ideal.span {x} : Ideal R) : FractionalIdeal S P) = spanSingleton S (algebr
aMap R P x)
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用引理 `coeIdeal_differentIdeal`：coeIdeal_differentIdeal : ↑(differentIdeal A B)
 = (FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L))⁻¹
· 使用引理 `mul_inv_eq_iff_eq_mul₀`：mul_inv_eq_iff_eq_mul₀ (hb : b != 0) : a * b⁻¹ =
 c ↔ a = c * b
· 使用引理 `FractionalIdeal.dual_ne_zero`：dual_ne_zero (hI : I != 0) : dual A K I !=
 0
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FractionalIdeal.instNontrivialNonZeroDivisors`：∀ {R₁ : Type u_3} [inst :
 CommRing R₁] {K : Type u_4} [inst_1 : Field K] [inst_2 : Algebra R₁ K],   Nontr
ivial (FractionalIdeal (nonZeroDivi…
· 使用定理 `FractionalIdeal.coeToSubmodule_injective`：coeToSubmodule_injective : Fun
ction.Injective (fun (I : FractionalIdeal S P) => (I : Submodule R P))
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FractionalIdeal.coe_mul`：coe_mul (I J : FractionalIdeal S P) : (↑(I * J)
 : Submodule R P) = I * J
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FractionalIdeal.coe_spanSingleton`：coe_spanSingleton (x : P) : (spanSing
leton S x : Submodule R P) = span R {x}
· 使用引理 `Submodule.span_singleton_mul`：span_singleton_mul {x : A} {p : Submodule 
R A} : Submodule.span R {x} * p = x • p
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Polynomial.Separable.aeval_derivative_ne_zero`：∀ {R : Type u} [inst : Co
mmSemiring R] {S : Type v} [inst_1 : CommSemiring S] [Nontrivial S] [inst_3 : Al
gebra R S]   {p : Polynomial R},   …
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Algebra.IsSeparable.isSeparable`：Algebra.IsSeparable.isSeparable [Algebr
a.IsSeparable F K] : forall x : K, IsSeparable F x
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `Polynomial.aeval_algebraMap_apply`：aeval_algebraMap_apply (x : A) (p : R
[X]) : aeval (algebraMap A B x) p = algebraMap A B (aeval x p)
（共 61 条，此处仅展示前 30 条）
-/
lemma conductor_mul_differentIdeal
    (x : B) (hx : Algebra.adjoin K {algebraMap B L x} = ⊤) :
    (conductor A x) * differentIdeal A B = Ideal.span {aeval x (derivative (minpoly A x))} := by
  have hAx : IsIntegral A x := IsIntegralClosure.isIntegral A L x
  have := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  apply FractionalIdeal.coeIdeal_injective (K := L)
  simp only [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton]
  rw [coeIdeal_differentIdeal A K L B, mul_inv_eq_iff_eq_mul₀]
  swap
  · exact FractionalIdeal.dual_ne_zero A K one_ne_zero
  apply FractionalIdeal.coeToSubmodule_injective
  simp only [FractionalIdeal.coe_coeIdeal, FractionalIdeal.coe_mul,
    FractionalIdeal.coe_spanSingleton, Submodule.span_singleton_mul]
  ext y
  have hne₁ : aeval (algebraMap B L x) (derivative (minpoly K (algebraMap B L x))) ≠ 0 :=
    (Algebra.IsSeparable.isSeparable _ _).aeval_derivative_ne_zero (minpoly.aeval _ _)
  have : algebraMap B L (aeval x (derivative (minpoly A x))) ≠ 0 := by
    rwa [minpoly.isIntegrallyClosed_eq_field_fractions K L hAx, derivative_map,
      aeval_map_algebraMap, aeval_algebraMap_apply] at hne₁
  rw [Submodule.mem_smul_iff_inv_mul_mem this, FractionalIdeal.mem_coe, FractionalIdeal.mem_dual,
    mem_coeSubmodule_conductor]
  swap
  · exact one_ne_zero
  have hne₂ : (aeval (algebraMap B L x) (derivative (minpoly K (algebraMap B L x))))⁻¹ ≠ 0 := by
    rwa [ne_eq, inv_eq_zero]
  have : IsIntegral A (algebraMap B L x) := IsIntegral.map (IsScalarTower.toAlgHom A B L) hAx
  simp_rw [← Subalgebra.mem_toSubmodule, ← Submodule.mul_mem_smul_iff (y := y * _)
    (mem_nonZeroDivisors_of_ne_zero hne₂)]
  rw [← traceForm_dualSubmodule_adjoin A K hx this]
  simp only [LinearMap.BilinForm.mem_dualSubmodule, traceForm_apply, Subalgebra.mem_toSubmodule,
    minpoly.isIntegrallyClosed_eq_field_fractions K L hAx,
    derivative_map, aeval_map_algebraMap, aeval_algebraMap_apply, mul_assoc,
    FractionalIdeal.mem_one_iff, forall_exists_index, forall_apply_eq_imp_iff]
  simp_rw [← IsScalarTower.toAlgHom_apply A B L x, ← AlgHom.map_adjoin_singleton]
  simp only [Subalgebra.mem_map, IsScalarTower.coe_toAlgHom', Submodule.one_eq_range,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, ← map_mul]
  exact ⟨fun H b ↦ (mul_one b) ▸ H b 1 (one_mem _), fun H _ _ _ ↦ H _⟩

open Polynomial Pointwise in
/-
**aeval_derivative_mem_differentIdeal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：aeval_derivative_mem_differentIdeal (x : B) (hx : Algebra.adjoin K {algebr
aMap B L x} = ⊤) : aeval x (derivative (minpoly A x)) in differentIdeal A B
参数：x : B；hx : Algebra.adjoin K {algebraMap B L x} = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `conductor_mul_differentIdeal`：conductor_mul_differentIdeal (x : B) (hx :
 Algebra.adjoin K {algebraMap B L x} = ⊤) : (conductor A x) * differentIdeal A B
 = Ideal.span {aev…
· 使用定理 `Ideal.mul_le_right`：mul_le_right : I * J <= J
· 使用定理 `Ideal.mem_span_singleton_self`：mem_span_singleton_self (x : α) : x in sp
an ({x} : Set α)
-/
lemma aeval_derivative_mem_differentIdeal
    (x : B) (hx : Algebra.adjoin K {algebraMap B L x} = ⊤) :
    aeval x (derivative (minpoly A x)) ∈ differentIdeal A B := by
  refine SetLike.le_def.mp ?_ (Ideal.mem_span_singleton_self _)
  rw [← conductor_mul_differentIdeal A K L x hx]
  exact Ideal.mul_le_right

end IsIntegrallyClosed
section

variable (L)
variable [IsFractionRing B L] [IsDedekindDomain A] [IsDedekindDomain B]
  [IsTorsionFree A B] [Module.Finite A B]

set_option linter.overlappingInstances false

include K L in
/-
**pow_sub_one_dvd_differentIdeal_aux** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_sub_one_dvd_differentIdeal_aux {p : Ideal A} [p.IsMaximal] (P : Ideal 
B) {e : Nat} (he : e != 0) (hp : p != ⊥) (hP : P ^ e ∣ p.map (algebraMap A B)) :
 P ^ (e - 1) ∣ differentIdeal A B
参数：P : Ideal B；he : e != 0；hp : p != ⊥；hP : P ^ e ∣ p.map (algebraMap A B)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用引理 `pow_dvd_pow`：pow_dvd_pow (a : α) (h : m <= n) : a ^ m ∣ a ^ n
· 使用定理 `Nat.sub_le`：∀ (n m : ℕ), n - m ≤ n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Ideal.map_eq_bot_iff_of_injective`：map_eq_bot_iff_of_injective {I : Idea
l R} {f : F} (hf : Function.Injective f) : I.map f = ⊥ ↔ I = ⊥
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.mul_bot`：mul_bot : M * ⊥ = ⊥
· 使用定理 `Ideal.zero_eq_bot`：zero_eq_bot : (0 : Ideal R) = ⊥
· 使用定理 `zero_dvd_iff`：zero_dvd_iff : 0 ∣ a ↔ a = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用引理 `mul_right_inj'`：mul_right_inj' (ha : a != 0) : a * b = a * c ↔ b = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
（共 73 条，此处仅展示前 30 条）
-/
lemma pow_sub_one_dvd_differentIdeal_aux
    {p : Ideal A} [p.IsMaximal] (P : Ideal B) {e : ℕ} (he : e ≠ 0) (hp : p ≠ ⊥)
    (hP : P ^ e ∣ p.map (algebraMap A B)) : P ^ (e - 1) ∣ differentIdeal A B := by
  obtain ⟨a, ha⟩ := (pow_dvd_pow _ (Nat.sub_le e 1)).trans hP
  have hp' := (Ideal.map_eq_bot_iff_of_injective
    (FaithfulSMul.algebraMap_injective A B)).not.mpr hp
  have habot : a ≠ ⊥ := fun ha' ↦ hp' (by simpa [ha'] using ha)
  have hPbot : P ≠ ⊥ := by
    rintro rfl; apply hp'
    rwa [← Ideal.zero_eq_bot, zero_pow he, zero_dvd_iff, Ideal.zero_eq_bot] at hP
  have : p.map (algebraMap A B) ∣ a ^ e := by
    obtain ⟨b, hb⟩ := hP
    apply_fun (· ^ e : Ideal B → _) at ha
    apply_fun (· ^ (e - 1) : Ideal B → _) at hb
    simp only [mul_pow, ← pow_mul, mul_comm e] at ha hb
    conv_lhs at ha => rw [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr he)]
    rw [pow_add, hb, mul_assoc, mul_right_inj' (pow_ne_zero _ hPbot), pow_one, mul_comm] at ha
    exact ⟨_, ha.symm⟩
  suffices ∀ x ∈ a, intTrace A B x ∈ p by
    have hP : ((P ^ (e - 1) :)⁻¹ : FractionalIdeal B⁰ L) = a / p.map (algebraMap A B) := by
      apply inv_involutive.injective
      simp only [inv_inv, ha, FractionalIdeal.coeIdeal_mul, inv_div,
          mul_div_assoc]
      rw [div_self (by simpa), mul_one]
    rw [Ideal.dvd_iff_le, differentialIdeal_le_iff (K := K) (L := L) (pow_ne_zero _ hPbot), hP,
      Submodule.map_le_iff_le_comap]
    intro x hx
    rw [Submodule.restrictScalars_mem, FractionalIdeal.mem_coe,
      FractionalIdeal.mem_div_iff_of_ne_zero (by simpa using hp')] at hx
    rw [Submodule.mem_comap, LinearMap.coe_restrictScalars, ← FractionalIdeal.coe_one,
      ← div_self (G₀ := FractionalIdeal A⁰ K) (a := p) (by simpa using hp),
      FractionalIdeal.mem_coe, FractionalIdeal.mem_div_iff_of_ne_zero (by simpa using hp)]
    simp only [FractionalIdeal.mem_coeIdeal, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] at hx
    intro y hy'
    obtain ⟨y, hy, rfl : algebraMap A K _ = _⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy'
    obtain ⟨z, hz, hz'⟩ := hx _ (Ideal.mem_map_of_mem _ hy)
    have : trace K L (algebraMap B L z) ∈ (p : FractionalIdeal A⁰ K) := by
      rw [← algebraMap_intTrace (A := A)]
      exact ⟨intTrace A B z, this z hz, rfl⟩
    rwa [mul_comm, ← smul_eq_mul, ← map_smul, Algebra.smul_def, mul_comm,
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B L, ← hz']
  intro x hx
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← trace_quotient_eq_of_isDedekindDomain,
    ← isNilpotent_iff_eq_zero]
  refine isNilpotent_trace_of_isNilpotent ⟨e, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact (Ideal.dvd_iff_le.mp this) <| Ideal.pow_mem_pow hx _
/-
**pow_sub_one_dvd_differentIdeal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_sub_one_dvd_differentIdeal [Algebra.IsSeparable (FractionRing A) (Frac
tionRing B)] {p : Ideal A} [p.IsMaximal] (P : Ideal B) (e : Nat) (hp : p != ⊥) (
hP : P ^ e ∣ p.map (algebraMap A B)) : P ^ (e - 1) ∣ differentIdeal A B
参数：FractionRing A；FractionRing B；P : Ideal B；e : Nat；hp : p != ⊥；hP : P ^ e ∣ p.
map (algebraMap A B)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.Flat.instOfIsDedekindDomainOfIsTorsionFree`：∀ {R : Type u_1} {M :
 Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module
 R M]   [IsDedekindDomain R] [Module.Is…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsIntegralClosure.isLocalization`：IsIntegralClosure.isLocalization [IsDo
main A] [Algebra.IsAlgebraic K L] : IsLocalization (Algebra.algebraMapSubmonoid 
C A⁰) L
· 使用定理 `FractionRing.instIsScalarTower`：∀ (R : Type u_1) [inst : CommRing R] (K 
: Type u_5) [inst_1 : Field K] [inst_2 : Algebra R K]   [inst_3 : FaithfulSMul R
 K] {R₀ : Type u_6} …
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsIntegralClosure.of_isIntegrallyClosed`：∀ (R : Type u_1) (S : Type u_2)
 [inst : CommRing R] [inst_1 : CommRing S] (K : Type u_3) [inst_2 : CommRing K] 
  [inst_3 : Algebra R K] [ifr…
· 使用定理 `FractionRing.instNontrivial`：∀ (R : Type u_1) [inst : CommRing R] [Nontr
ivial R], Nontrivial (FractionRing R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用引理 `Module.Finite.of_isLocalization`：of_isLocalization (R S) {Rₚ Sₚ : Type*}
 [CommSemiring R] [CommSemiring S] [CommSemiring Rₚ] [CommSemiring Sₚ] [Algebra 
R S] [Algebra R Rₚ] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_dvd`：one_dvd (a : α) : 1 ∣ a
· 使用引理 `pow_sub_one_dvd_differentIdeal_aux`：pow_sub_one_dvd_differentIdeal_aux {
p : Ideal A} [p.IsMaximal] (P : Ideal B) {e : Nat} (he : e != 0) (hp : p != ⊥) (
hP : P ^ e ∣ p.map (alge…
-/
lemma pow_sub_one_dvd_differentIdeal [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    {p : Ideal A} [p.IsMaximal] (P : Ideal B) (e : ℕ) (hp : p ≠ ⊥)
    (hP : P ^ e ∣ p.map (algebraMap A B)) : P ^ (e - 1) ∣ differentIdeal A B := by
  have : IsLocalization (algebraMapSubmonoid B A⁰) (FractionRing B) :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  have : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  by_cases he : e = 0
  · rw [he, pow_zero]; exact one_dvd _
  exact pow_sub_one_dvd_differentIdeal_aux A (FractionRing A) (FractionRing B) _ he hp hP
/-
**not_dvd_differentIdeal_of_intTrace_not_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_dvd_differentIdeal_of_intTrace_not_mem [Algebra.IsSeparable (FractionR
ing A) (FractionRing B)] {p : Ideal A} (P Q : Ideal B) (hP : P * Q = Ideal.map (
algebraMap A B) p) (x : B) (hxQ : x in Q) (hx : Algebra.intTrace A B x ∉ p) : ¬ 
P ∣ differentIdeal A B
参数：FractionRing A；FractionRing B；P Q : Ideal B；hP : P * Q = Ideal.map (algebraMa
p A B) p；x : B；hxQ : x in Q；hx : Algebra.intTrace A B x ∉ p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.Flat.instOfIsDedekindDomainOfIsTorsionFree`：∀ {R : Type u_1} {M :
 Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module
 R M]   [IsDedekindDomain R] [Module.Is…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.map_bot`：map_bot : (⊥ : Ideal R).map f = ⊥
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.zero_eq_bot`：zero_eq_bot : (0 : Ideal R) = ⊥
· 使用定理 `zero_dvd_iff`：zero_dvd_iff : 0 ∣ a ↔ a = 0
· 使用定理 `differentIdeal_ne_bot`：differentIdeal_ne_bot [Module.Finite A B] [Algebr
a.IsSeparable (FractionRing A) (FractionRing B)] : differentIdeal A B != ⊥
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用定理 `Ideal.mul_le_right`：mul_le_right : I * J <= J
· 使用定理 `IsIntegralClosure.isLocalization`：IsIntegralClosure.isLocalization [IsDo
main A] [Algebra.IsAlgebraic K L] : IsLocalization (Algebra.algebraMapSubmonoid 
C A⁰) L
· 使用定理 `FractionRing.instIsScalarTower`：∀ (R : Type u_1) [inst : CommRing R] (K 
: Type u_5) [inst_1 : Field K] [inst_2 : Algebra R K]   [inst_3 : FaithfulSMul R
 K] {R₀ : Type u_6} …
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsIntegralClosure.of_isIntegrallyClosed`：∀ (R : Type u_1) (S : Type u_2)
 [inst : CommRing R] [inst_1 : CommRing S] (K : Type u_3) [inst_2 : CommRing K] 
  [inst_3 : Algebra R K] [ifr…
· 使用定理 `FractionRing.instNontrivial`：∀ (R : Type u_1) [inst : CommRing R] [Nontr
ivial R], Nontrivial (FractionRing R)
· 使用引理 `Module.Finite.of_isLocalization`：of_isLocalization (R S) {Rₚ Sₚ : Type*}
 [CommSemiring R] [CommSemiring S] [CommSemiring Rₚ] [CommSemiring Sₚ] [Algebra 
R S] [Algebra R Rₚ] […
（共 83 条，此处仅展示前 30 条）
-/
theorem not_dvd_differentIdeal_of_intTrace_not_mem
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    {p : Ideal A} (P Q : Ideal B) (hP : P * Q = Ideal.map (algebraMap A B) p)
    (x : B) (hxQ : x ∈ Q) (hx : Algebra.intTrace A B x ∉ p) :
    ¬ P ∣ differentIdeal A B := by
  by_cases hp : p = ⊥
  · subst hp
    simp only [Ideal.map_bot, Ideal.mul_eq_bot] at hP
    obtain (rfl | rfl) := hP
    · rw [← Ideal.zero_eq_bot, zero_dvd_iff]
      exact differentIdeal_ne_bot
    · obtain rfl := hxQ
      simp at hx
  let : Algebra (A ⧸ p) (B ⧸ Q) := Ideal.Quotient.algebraQuotientOfLEComap (by
      rw [← Ideal.map_le_iff_le_comap, ← hP]
      exact Ideal.mul_le_right)
  let K := FractionRing A
  let L := FractionRing B
  have : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L :=
    IsIntegralClosure.isLocalization _ K _ _
  have : FiniteDimensional K L := .of_isLocalization A B A⁰
  rw [Ideal.dvd_iff_le]
  intro H
  replace H := (mul_le_mul_left H Q).trans_eq hP
  replace H := (FractionalIdeal.coeIdeal_le_coeIdeal' _ (P := L) le_rfl).mpr H
  rw [FractionalIdeal.coeIdeal_mul, coeIdeal_differentIdeal A K] at H
  replace H := mul_le_mul_right H (FractionalIdeal.dual A K 1)
  have hne : (1 : FractionalIdeal B⁰ L) ≠ 0 := one_ne_zero
  rw [mul_inv_cancel_left₀ (FractionalIdeal.dual_ne_zero A K hne)] at H
  apply hx
  suffices Algebra.trace K L (algebraMap B L x) ∈ (p : FractionalIdeal A⁰ K) by
    obtain ⟨y, hy, e⟩ := this
    rw [← Algebra.algebraMap_intTrace (A := A), Algebra.linearMap_apply,
      (IsLocalization.injective _ le_rfl).eq_iff] at e
    exact e ▸ hy
  refine FractionalIdeal.mul_induction_on (H ⟨_, hxQ, rfl⟩) ?_ ?_
  · rintro x hx _ ⟨y, hy, rfl⟩
    induction hy using Submodule.span_induction generalizing x with
    | mem y h =>
      obtain ⟨y, hy, rfl⟩ := h
      obtain ⟨z, hz⟩ :=
        (FractionalIdeal.mem_dual (by simp)).mp hx 1 ⟨1, trivial, (algebraMap B L).map_one⟩
      simp only [Algebra.traceForm_apply, mul_one] at hz
      refine ⟨z * y, Ideal.mul_mem_left _ _ hy, ?_⟩
      rw [Algebra.linearMap_apply, Algebra.linearMap_apply, mul_comm x,
        ← IsScalarTower.algebraMap_apply,
        ← Algebra.smul_def, LinearMap.map_smul_of_tower, ← hz,
        Algebra.smul_def, map_mul, mul_comm]
    | zero => simp
    | add y z _ _ hy hz =>
      simp only [map_add, mul_add]
      exact Submodule.add_mem _ (hy x hx) (hz x hx)
    | smul y z hz IH =>
      simpa [Algebra.smul_def, mul_assoc, -FractionalIdeal.mem_coeIdeal, mul_left_comm x] using
        IH _ (Submodule.smul_mem _ y hx)
  · simp only [map_add]
    exact fun _ _ h₁ h₂ ↦ Submodule.add_mem _ h₁ h₂

open nonZeroDivisors
/-
**not_dvd_differentIdeal_of_isCoprime_of_isSeparable** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：not_dvd_differentIdeal_of_isCoprime_of_isSeparable [Algebra.IsSeparable (F
ractionRing A) (FractionRing B)] {p : Ideal A} [p.IsMaximal] (P Q : Ideal B) [P.
IsMaximal] [P.LiesOver p] (hPQ : IsCoprime P Q) (hP : P * Q = Ideal.map (algebra
Map A B) p) [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)] : ¬ P ∣ differentIdeal A B
参数：FractionRing A；FractionRing B；P Q : Ideal B；hPQ : IsCoprime P Q；hP : P * Q = 
Ideal.map (algebraMap A B) p；A ⧸ p；B ⧸ P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.Flat.instOfIsDedekindDomainOfIsTorsionFree`：∀ {R : Type u_1} {M :
 Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module
 R M]   [IsDedekindDomain R] [Module.Is…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用定理 `Ideal.mul_le_right`：mul_le_right : I * J <= J
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Module.Finite.of_restrictScalars_finite`：of_restrictScalars_finite (R A 
M : Type*) [Semiring R] [Semiring A] [AddCommMonoid M] [Module R M] [Module A M]
 [SMul R A] [IsScalarTower R …
· 使用定理 `RingEquiv.map_mul'`：∀ {R : Type u_7} {S : Type u_8} [inst : Mul R] [inst
_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (self : R ≃+* S)   (x y : R), self
.toFun (…
· 使用定理 `RingEquiv.map_add'`：∀ {R : Type u_7} {S : Type u_8} [inst : Mul R] [inst
_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (self : R ≃+* S)   (x y : R), self
.toFun (…
· 使用定理 `Quotient.ind`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s → Prop}
, (∀ (a : α), motive ⟦a⟧) → ∀ (q : Quotient s), motive q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Algebra.trace_ne_zero`：Algebra.trace_ne_zero [FiniteDimensional K L] [Al
gebra.IsSeparable K L] : Algebra.trace K L != 0
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `not_dvd_differentIdeal_of_intTrace_not_mem`：not_dvd_differentIdeal_of_in
tTrace_not_mem [Algebra.IsSeparable (FractionRing A) (FractionRing B)] {p : Idea
l A} (P Q : Ideal B) (hP : P * Q…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ideal.quotientMulEquivQuotientProd_snd`：quotientMulEquivQuotientProd_snd
 (I J : Ideal R) (coprime : IsCoprime I J) (x : R ⧸ I * J) : (quotientMulEquivQu
otientProd I J coprime x).sn…
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用引理 `Algebra.trace_quotient_eq_of_isDedekindDomain`：Algebra.trace_quotient_eq
_of_isDedekindDomain (x) [IsDedekindDomain R] [IsDomain S] [Module.IsTorsionFree
 R S] [Module.Finite R S] [IsIntegr…
· 使用引理 `Algebra.trace_eq_of_algEquiv`：Algebra.trace_eq_of_algEquiv {A B C : Type
*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C] (e : B ≃ₐ[
A] C) (x) : Algebr…
· 使用定理 `Algebra.trace_prod_apply`：trace_prod_apply [Module.Free R S] [Module.Fre
e R T] [Module.Finite R S] [Module.Finite R T] (x : S × T) : trace R (S × T) x =
 trace R S x.f…
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
（共 42 条，此处仅展示前 30 条）
-/
theorem not_dvd_differentIdeal_of_isCoprime_of_isSeparable
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    {p : Ideal A} [p.IsMaximal] (P Q : Ideal B) [P.IsMaximal] [P.LiesOver p]
    (hPQ : IsCoprime P Q) (hP : P * Q = Ideal.map (algebraMap A B) p)
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)] :
    ¬ P ∣ differentIdeal A B := by
  let : Algebra (A ⧸ p) (B ⧸ Q) := Ideal.Quotient.algebraQuotientOfLEComap (by
      rw [← Ideal.map_le_iff_le_comap, ← hP]
      exact Ideal.mul_le_right)
  have : IsScalarTower A (A ⧸ p) (B ⧸ Q) := .of_algebraMap_eq' rfl
  have : Module.Finite (A ⧸ p) (B ⧸ Q) :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ p) (B ⧸ Q)
  let e : (B ⧸ p.map (algebraMap A B)) ≃ₐ[A ⧸ p] ((B ⧸ P) × B ⧸ Q) :=
    { __ := (Ideal.quotEquivOfEq hP.symm).trans (Ideal.quotientMulEquivQuotientProd P Q hPQ),
      commutes' := Quotient.ind fun _ ↦ rfl }
  obtain ⟨x, hx⟩ : ∃ x, Algebra.trace (A ⧸ p) (B ⧸ P) x ≠ 0 := by
    simpa [LinearMap.ext_iff] using Algebra.trace_ne_zero (A ⧸ p) (B ⧸ P)
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (e.symm (x, 0))
  refine not_dvd_differentIdeal_of_intTrace_not_mem A P Q hP y ?_ ?_
  · have := congr((e $hy).2)
    simp at this
    simpa [e, Ideal.Quotient.eq_zero_iff_mem] using this
  · rw [← Ideal.Quotient.eq_zero_iff_mem, ← Algebra.trace_quotient_eq_of_isDedekindDomain,
      hy, Algebra.trace_eq_of_algEquiv, Algebra.trace_prod_apply]
    simpa
/-
**not_dvd_differentIdeal_of_isCoprime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_dvd_differentIdeal_of_isCoprime [Algebra.IsSeparable (FractionRing A) 
(FractionRing B)] {p : Ideal A} [p.IsMaximal] [Finite (A ⧸ p)] (P Q : Ideal B) [
P.IsMaximal] (hPQ : IsCoprime P Q) (hP : P * Q = Ideal.map (algebraMap A B) p) :
 ¬ P ∣ differentIdeal A B
参数：FractionRing A；FractionRing B；A ⧸ p；P Q : Ideal B；hPQ : IsCoprime P Q；hP : P 
* Q = Ideal.map (algebraMap A B) p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.Flat.instOfIsDedekindDomainOfIsTorsionFree`：∀ {R : Type u_1} {M :
 Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module
 R M]   [IsDedekindDomain R] [Module.Is…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.IsMaximal.eq_of_le`：∀ {α : Type u} [inst : Semiring α] {I J : Idea
l α}, I.IsMaximal → J ≠ ⊤ → I ≤ J → I = J
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.IsMaximal.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}
, I.IsMaximal → I ≠ ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用定理 `Ideal.mul_le_left`：mul_le_left [I.IsTwoSided] : I * J <= I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `not_dvd_differentIdeal_of_isCoprime_of_isSeparable`：not_dvd_differentIde
al_of_isCoprime_of_isSeparable [Algebra.IsSeparable (FractionRing A) (FractionRi
ng B)] {p : Ideal A} [p.IsMaximal] (P Q …
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
theorem not_dvd_differentIdeal_of_isCoprime
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    {p : Ideal A} [p.IsMaximal] [Finite (A ⧸ p)] (P Q : Ideal B) [P.IsMaximal]
    (hPQ : IsCoprime P Q) (hP : P * Q = Ideal.map (algebraMap A B) p) :
    ¬ P ∣ differentIdeal A B := by
  have : P.LiesOver p := by
    constructor
    refine ‹p.IsMaximal›.eq_of_le ?_ ?_
    · simpa using ‹P.IsMaximal›.ne_top
    · rw [← Ideal.map_le_iff_le_comap, ← hP]
      exact Ideal.mul_le_left
  exact not_dvd_differentIdeal_of_isCoprime_of_isSeparable A P Q hPQ hP
/-
**dvd_differentIdeal_of_not_isSeparable** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dvd_differentIdeal_of_not_isSeparable [Algebra.IsSeparable (FractionRing A
) (FractionRing B)] {p : Ideal A} [p.IsMaximal] (hp : p != ⊥) (P : Ideal B) [P.I
sMaximal] [P.LiesOver p] (H : ¬ Algebra.IsSeparable (A ⧸ p) (B ⧸ P)) : P ∣ diffe
rentIdeal A B
参数：FractionRing A；FractionRing B；hp : p != ⊥；P : Ideal B；H : ¬ Algebra.IsSeparab
le (A ⧸ p) (B ⧸ P)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.Flat.instOfIsDedekindDomainOfIsTorsionFree`：∀ {R : Type u_1} {M :
 Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module
 R M]   [IsDedekindDomain R] [Module.Is…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.dvd_iff_le`：Ideal.dvd_iff_le {I J : Ideal A} : I ∣ J ↔ J <= I
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Ideal.LiesOver.over`：∀ {A : Type u_2} {inst : CommSemiring A} {B : Type 
u_3} {inst_1 : Semiring B} {inst_2 : Algebra A B} {P : Ideal B}   {p : Ideal A} 
[self : P…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用引理 `pow_sub_one_dvd_differentIdeal`：pow_sub_one_dvd_differentIdeal [Algebra.
IsSeparable (FractionRing A) (FractionRing B)] {p : Ideal A} [p.IsMaximal] (P : 
Ideal B) (e : Nat) (…
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `mul_dvd_mul_left`：mul_dvd_mul_left (a : α) (h : b ∣ c) : a * b ∣ a * c
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Ideal.map_eq_bot_iff_of_injective`：map_eq_bot_iff_of_injective {I : Idea
l R} {f : F} (hf : Function.Injective f) : I.map f = ⊥ ↔ I = ⊥
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.mul_bot`：mul_bot : M * ⊥ = ⊥
· 使用定理 `Ideal.bot_mul`：bot_mul : ⊥ * I = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用引理 `Algebra.trace_quotient_eq_of_isDedekindDomain`：Algebra.trace_quotient_eq
_of_isDedekindDomain (x) [IsDedekindDomain R] [IsDomain S] [Module.IsTorsionFree
 R S] [Module.Finite R S] [IsIntegr…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
（共 89 条，此处仅展示前 30 条）
-/
lemma dvd_differentIdeal_of_not_isSeparable
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    {p : Ideal A} [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal B) [P.IsMaximal] [P.LiesOver p]
    (H : ¬ Algebra.IsSeparable (A ⧸ p) (B ⧸ P)) : P ∣ differentIdeal A B := by
  obtain ⟨a, ha⟩ : P ∣ p.map (algebraMap A B) :=
    Ideal.dvd_iff_le.mpr (Ideal.map_le_iff_le_comap.mpr Ideal.LiesOver.over.le)
  by_cases hPa : P ∣ a
  · simpa using pow_sub_one_dvd_differentIdeal A P 2 hp
      (by rw [pow_two, ha]; exact mul_dvd_mul_left _ hPa)
  let K := FractionRing A
  let L := FractionRing B
  have hp' := (Ideal.map_eq_bot_iff_of_injective
    (FaithfulSMul.algebraMap_injective A B)).not.mpr hp
  have habot : a ≠ ⊥ := fun ha' ↦ hp' (by simpa [ha'] using ha)
  have hPbot : P ≠ ⊥ := by
    rintro rfl; apply hp'
    rwa [Ideal.bot_mul] at ha
  suffices ∀ x ∈ a, Algebra.intTrace A B x ∈ p by
    have hP : ((P :)⁻¹ : FractionalIdeal B⁰ L) = a / p.map (algebraMap A B) := by
      apply inv_involutive.injective
      simp only [ha, FractionalIdeal.coeIdeal_mul, inv_div, mul_div_assoc]
      rw [div_self (by simpa), mul_one, inv_inv]
    rw [Ideal.dvd_iff_le, differentialIdeal_le_iff (K := K) (L := L) hPbot, hP,
      Submodule.map_le_iff_le_comap]
    intro x hx
    rw [Submodule.restrictScalars_mem, FractionalIdeal.mem_coe,
      FractionalIdeal.mem_div_iff_of_ne_zero (by simpa using hp')] at hx
    rw [Submodule.mem_comap, LinearMap.coe_restrictScalars, ← FractionalIdeal.coe_one,
      ← div_self (G₀ := FractionalIdeal A⁰ K) (a := p) (by simpa using hp),
      FractionalIdeal.mem_coe, FractionalIdeal.mem_div_iff_of_ne_zero (by simpa using hp)]
    simp only [FractionalIdeal.mem_coeIdeal, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] at hx
    intro y hy'
    obtain ⟨y, hy, rfl : algebraMap A K _ = _⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy'
    obtain ⟨z, hz, hz'⟩ := hx _ (Ideal.mem_map_of_mem _ hy)
    have : Algebra.trace K L (algebraMap B L z) ∈ (p : FractionalIdeal A⁰ K) := by
      rw [← Algebra.algebraMap_intTrace (A := A)]
      exact ⟨Algebra.intTrace A B z, this z hz, rfl⟩
    rwa [mul_comm, ← smul_eq_mul, ← map_smul, Algebra.smul_def, mul_comm,
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B L, ← hz']
  intro x hx
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Algebra.trace_quotient_eq_of_isDedekindDomain]
  let : Algebra (A ⧸ p) (B ⧸ a) :=
    Ideal.Quotient.algebraQuotientOfLEComap (Ideal.map_le_iff_le_comap.mp
      (Ideal.dvd_iff_le.mp ⟨_, ha.trans (mul_comm _ _)⟩))
  have : IsScalarTower A (A ⧸ p) (B ⧸ a) := .of_algebraMap_eq' rfl
  have : Module.Finite (A ⧸ p) (B ⧸ a) := .of_restrictScalars_finite A _ _
  have := ((Ideal.prime_iff_isPrime hPbot).mpr inferInstance)
  rw [← this.irreducible.gcd_eq_one_iff, ← Ideal.isCoprime_iff_gcd] at hPa
  let e : (B ⧸ p.map (algebraMap A B)) ≃ₐ[A ⧸ p] ((B ⧸ P) × B ⧸ a) :=
    { __ := (Ideal.quotEquivOfEq ha).trans (Ideal.quotientMulEquivQuotientProd P a hPa),
      commutes' := Quotient.ind fun _ ↦ rfl }
  have hx' : (e (Ideal.Quotient.mk _ x)).2 = 0 := by
    simpa [e, Ideal.Quotient.eq_zero_iff_mem]
  rw [← Algebra.trace_eq_of_algEquiv e, Algebra.trace_prod_apply,
    Algebra.trace_eq_zero_of_not_isSeparable H, LinearMap.zero_apply, zero_add, hx', map_zero]

variable {A}

/-- A prime does not divide the different ideal iff it is unramified. -/
/-
**not_dvd_differentIdeal_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_dvd_differentIdeal_iff [Algebra.IsSeparable (FractionRing A) (Fraction
Ring B)] {P : Ideal B} [P.IsPrime] : ¬ P ∣ differentIdeal A B ↔ Algebra.IsUnrami
fiedAt A P
参数：FractionRing A；FractionRing B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.Flat.instOfIsDedekindDomainOfIsTorsionFree`：∀ {R : Type u_1} {M :
 Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module
 R M]   [IsDedekindDomain R] [Module.Is…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submonoid.ext`：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) :
 S = T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Ideal.one_notMem`：one_notMem (I : Ideal α) [hI : I.IsPrime] : 1 ∉ I
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Algebra.FormallyUnramified.iff_of_equiv`：iff_of_equiv (e : A ≃ₐ[R] B) : 
FormallyUnramified R A ↔ FormallyUnramified R B
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `Algebra.FormallyUnramified.iff_isSeparable`：iff_isSeparable (L : Type u)
 [Field L] [Algebra K L] [EssFiniteType K L] : FormallyUnramified K L ↔ Algebra.
IsSeparable K L
· 使用定理 `Algebra.EssFiniteType.of_finiteType`：∀ (R : Type u_1) (S : Type u_2) [in
st : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.FiniteT
ype R S], Algebra.EssFini…
· 使用定理 `Module.Finite.finiteType`：∀ {R : Type u_1} (A : Type u_2) [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [hRA : Module.Finite R 
A], Algebra.Fi…
· 使用定理 `instFiniteDimensionalFractionRingOfFinite`：∀ {R : Type u_1} {S : Type u_
2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] [inst_3 : Is
Domain R]   [inst_4 : IsDomain …
· 使用定理 `Algebra.FormallyUnramified.comp`：comp [FormallyUnramified R A] [Formally
Unramified A B] : FormallyUnramified R B
· 使用定理 `FractionRing.instIsScalarTower`：∀ (R : Type u_1) [inst : CommRing R] (K 
: Type u_5) [inst_1 : Field K] [inst_2 : Algebra R K]   [inst_3 : FaithfulSMul R
 K] {R₀ : Type u_6} …
（共 64 条，此处仅展示前 30 条）

--- 原说明 ---
A prime does not divide the different ideal iff it is unramified.
-/
theorem not_dvd_differentIdeal_iff
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)] {P : Ideal B} [P.IsPrime] :
    ¬ P ∣ differentIdeal A B ↔ Algebra.IsUnramifiedAt A P := by
  rcases eq_or_ne P ⊥ with rfl | hPbot
  · simp_rw [← Ideal.zero_eq_bot, zero_dvd_iff]
    simp only [Submodule.zero_eq_bot, differentIdeal_ne_bot, not_false_eq_true, true_iff]
    let K := FractionRing A
    let L := FractionRing B
    have : IsLocalization B⁰ (Localization.AtPrime (⊥ : Ideal B)) := by
      convert!
        (inferInstance :
          IsLocalization (⊥ : Ideal B).primeCompl (Localization.AtPrime (⊥ : Ideal B)))
      ext; simp [Ideal.primeCompl]
    refine (Algebra.FormallyUnramified.iff_of_equiv (A := L)
      ((IsLocalization.algEquiv B⁰ _ _).restrictScalars A)).mp ?_
    have : Algebra.FormallyUnramified K L := by
      rwa [Algebra.FormallyUnramified.iff_isSeparable]
    refine .comp A K L
  have hp : P.under A ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hPbot
  have hp' := (Ideal.map_eq_bot_iff_of_injective
    (FaithfulSMul.algebraMap_injective A B)).not.mpr hp
  have := Ideal.IsPrime.isMaximal inferInstance hPbot
  let := Localization.AtPrime.algebraOfLiesOver (P.under A) P
  constructor
  · intro H
    · rw [Algebra.isUnramifiedAt_iff_map_eq (p := P.under A)]
      constructor
      · suffices Algebra.IsSeparable (A ⧸ P.under A) (B ⧸ P) by infer_instance
        contrapose H
        exact dvd_differentIdeal_of_not_isSeparable A hp P H
      · rw [← Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff hPbot Ideal.map_comap_le]
        apply Ideal.ramificationIdx'_spec
        · simp [Ideal.map_le_iff_le_comap]
        · contrapose H
          rw [← pow_one P, show 1 = 2 - 1 by simp]
          apply pow_sub_one_dvd_differentIdeal _ _ _ hp
          simpa [Ideal.dvd_iff_le] using H
  · intro H
    obtain ⟨Q, h₁, h₂⟩ := Ideal.eq_prime_pow_mul_coprime hp' P
    rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count _ _ hp',
      Ideal.ramificationIdx_eq_one_of_isUnramifiedAt, pow_one] at h₂
    obtain ⟨h₃, h₄⟩ := (Algebra.isUnramifiedAt_iff_map_eq (p := P.under A) _ _).mp H
    exact not_dvd_differentIdeal_of_isCoprime_of_isSeparable
      A P Q (Ideal.isCoprime_iff_sup_eq.mpr h₁) h₂.symm

/-- A prime divides the different ideal iff it is ramified. -/
/-
**dvd_differentIdeal_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_differentIdeal_iff [Algebra.IsSeparable (FractionRing A) (FractionRing
 B)] {P : Ideal B} [P.IsPrime] : P ∣ differentIdeal A B ↔ ¬ Algebra.IsUnramified
At A P
参数：FractionRing A；FractionRing B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.Flat.instOfIsDedekindDomainOfIsTorsionFree`：∀ {R : Type u_1} {M :
 Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module
 R M]   [IsDedekindDomain R] [Module.Is…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `iff_not_comm`：iff_not_comm : (a ↔ ¬b) ↔ (b ↔ ¬a)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `not_dvd_differentIdeal_iff`：not_dvd_differentIdeal_iff [Algebra.IsSepara
ble (FractionRing A) (FractionRing B)] {P : Ideal B} [P.IsPrime] : ¬ P ∣ differe
ntIdeal A B ↔ Al…

--- 原说明 ---
A prime divides the different ideal iff it is ramified.
-/
theorem dvd_differentIdeal_iff
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)] {P : Ideal B} [P.IsPrime] :
    P ∣ differentIdeal A B ↔ ¬ Algebra.IsUnramifiedAt A P :=
  iff_not_comm.mp not_dvd_differentIdeal_iff.symm

end

