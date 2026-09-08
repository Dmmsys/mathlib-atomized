/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Nilpotent elements

This file contains results about nilpotent elements that involve ring theory.
-/

@[expose] public section

assert_not_exists Cardinal

universe u v

open Function Module Set

variable {R S : Type*} {x y : R}

/-
**RingHom.ker_isRadical_iff_reduced_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.ker_isRadical_iff_reduced_of_surjective {S F} [CommSemiring R] [Se
miring S] [FunLike F R S] [RingHomClass F R S] {f : F} (hf : Function.Surjective
 f) : (RingHom.ker f).IsRadical ↔ IsReduced S
参数：hf : Function.Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem RingHom.ker_isRadical_iff_reduced_of_surjective {S F} [CommSemiring R] [Semiring S]
    [FunLike F R S] [RingHomClass F R S] {f : F} (hf : Function.Surjective f) :
    (RingHom.ker f).IsRadical ↔ IsReduced S := by
  simp_rw [isReduced_iff, hf.forall, IsNilpotent, ← map_pow, ← RingHom.mem_ker]
  rfl
/-
**isRadical_iff_span_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isRadical_iff_span_singleton [CommSemiring R] : IsRadical y ↔ (Ideal.span 
({y} : Set R)).IsRadical
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `exists_imp`：∀ {α : Sort u_1} {p : α → Prop} {b : Prop}, (∃ x, p x) → b ↔
 ∀ (x : α), p x → b
-/
theorem isRadical_iff_span_singleton [CommSemiring R] :
    IsRadical y ↔ (Ideal.span ({y} : Set R)).IsRadical := by
  simp_rw [IsRadical, ← Ideal.mem_span_singleton]
  exact forall_comm.trans (forall_congr' fun r => exists_imp.symm)
/-
**isNilpotent_iff_zero_mem_powers** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isNilpotent_iff_zero_mem_powers [Monoid R] [Zero R] {x : R} : IsNilpotent 
x ↔ 0 in Submonoid.powers x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isNilpotent_iff_zero_mem_powers [Monoid R] [Zero R] {x : R} :
    IsNilpotent x ↔ 0 ∈ Submonoid.powers x := Iff.rfl

section CommSemiring

variable [CommSemiring R] {x y : R}

/-- The nilradical of a commutative semiring is the ideal of nilpotent elements. -/
/-
**nilradical** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：nilradical (R : Type*) [CommSemiring R] : Ideal R
参数：R : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The nilradical of a commutative semiring is the ideal of nilpotent elements.
-/
def nilradical (R : Type*) [CommSemiring R] : Ideal R :=
  (0 : Ideal R).radical
/-
**mem_nilradical** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_nilradical : x in nilradical R ↔ IsNilpotent x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_nilradical : x ∈ nilradical R ↔ IsNilpotent x :=
  Iff.rfl
/-
**nilradical_eq_sInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nilradical_eq_sInf (R : Type*) [CommSemiring R] : nilradical R = sInf { J 
: Ideal R | J.IsPrime }
参数：R : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.radical_eq_sInf`：radical_eq_sInf (I : Ideal R) : radical I = sInf 
{ J : Ideal R | I <= J ∧ IsPrime J }
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nilradical_eq_sInf (R : Type*) [CommSemiring R] :
    nilradical R = sInf { J : Ideal R | J.IsPrime } :=
  (Ideal.radical_eq_sInf ⊥).trans <| by simp_rw [and_iff_right bot_le]
/-
**nilpotent_iff_mem_prime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nilpotent_iff_mem_prime : IsNilpotent x ↔ forall J : Ideal R, J.IsPrime ->
 x in J
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mem_nilradical`：mem_nilradical : x in nilradical R ↔ IsNilpotent x
· 使用定理 `nilradical_eq_sInf`：nilradical_eq_sInf (R : Type*) [CommSemiring R] : ni
lradical R = sInf { J : Ideal R | J.IsPrime }
· 使用定理 `Submodule.mem_sInf`：mem_sInf {S : Set (Submodule R M)} {x : M} : x in sI
nf S ↔ forall p in S, x in p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nilpotent_iff_mem_prime : IsNilpotent x ↔ ∀ J : Ideal R, J.IsPrime → x ∈ J := by
  rw [← mem_nilradical, nilradical_eq_sInf, Submodule.mem_sInf]
  rfl
/-
**nilradical_le_prime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nilradical_le_prime (J : Ideal R) [H : J.IsPrime] : nilradical R <= J
参数：J : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nilradical_eq_sInf`：nilradical_eq_sInf (R : Type*) [CommSemiring R] : ni
lradical R = sInf { J : Ideal R | J.IsPrime }
-/
theorem nilradical_le_prime (J : Ideal R) [H : J.IsPrime] : nilradical R ≤ J :=
  (nilradical_eq_sInf R).symm ▸ sInf_le H

@[simp]
/-
**nilradical_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nilradical_eq_zero (R : Type*) [CommSemiring R] [IsReduced R] : nilradical
 R = 0
参数：R : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `isNilpotent_iff_eq_zero`：isNilpotent_iff_eq_zero [MonoidWithZero R] [IsR
educed R] : IsNilpotent x ↔ x = 0
-/
theorem nilradical_eq_zero (R : Type*) [CommSemiring R] [IsReduced R] : nilradical R = 0 :=
  Ideal.ext fun _ => isNilpotent_iff_eq_zero
/-
**nilradical_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nilradical_eq_bot_iff {R : Type*} [CommSemiring R] : nilradical R = ⊥ ↔ Is
Reduced R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nilradical_eq_bot_iff {R : Type*} [CommSemiring R] : nilradical R = ⊥ ↔ IsReduced R := by
  simp_rw [eq_bot_iff, SetLike.le_def, Submodule.mem_bot, mem_nilradical, isReduced_iff]

end CommSemiring

namespace LinearMap

variable (R) {A : Type v} [CommSemiring R] [Semiring A] [Algebra R A]

@[simp]
/-
**LinearMap.isNilpotent_mulLeft_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：isNilpotent_mulLeft_iff (a : A) : IsNilpotent (mulLeft R a) ↔ IsNilpotent 
a
参数：a : A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.pow_mulLeft`：pow_mulLeft (a : A) (n : Nat) : mulLeft R a ^ n =
 mulLeft R (a ^ n)
-/
theorem isNilpotent_mulLeft_iff (a : A) : IsNilpotent (mulLeft R a) ↔ IsNilpotent a := by
  constructor <;> rintro ⟨n, hn⟩ <;> use n <;>
      simp only [mulLeft_eq_zero_iff, pow_mulLeft] at hn ⊢ <;>
    exact hn

@[simp]
/-
**LinearMap.isNilpotent_mulRight_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：isNilpotent_mulRight_iff (a : A) : IsNilpotent (mulRight R a) ↔ IsNilpoten
t a
参数：a : A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.pow_mulRight`：pow_mulRight (a : A) (n : Nat) : mulRight R a ^ 
n = mulRight R (a ^ n)
-/
theorem isNilpotent_mulRight_iff (a : A) : IsNilpotent (mulRight R a) ↔ IsNilpotent a := by
  constructor <;> rintro ⟨n, hn⟩ <;> use n <;>
      simp only [mulRight_eq_zero_iff, pow_mulRight] at hn ⊢ <;>
    exact hn

variable {R}
variable {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid M] [Module R M]

@[simp]
/-
**LinearMap.isNilpotent_toMatrix_iff** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：isNilpotent_toMatrix_iff (b : Basis ι R M) (f : M ->ₗ[R] M) : IsNilpotent 
(toMatrix b b f) ↔ IsNilpotent f
参数：b : Basis ι R M；f : M ->ₗ[R] M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.toMatrix_pow`：LinearMap.toMatrix_pow (f : M₁ ->ₗ[R] M₁) (k : N
at) : (toMatrix v₁ v₁ f) ^ k = toMatrix v₁ v₁ (f ^ k)
· 使用定理 `LinearEquiv.map_eq_zero_iff`：map_eq_zero_iff {x : M} : e x = 0 ↔ x = 0
-/
lemma isNilpotent_toMatrix_iff (b : Basis ι R M) (f : M →ₗ[R] M) :
    IsNilpotent (toMatrix b b f) ↔ IsNilpotent f := by
  refine exists_congr fun k ↦ ?_
  rw [toMatrix_pow]
  exact (toMatrix b b).map_eq_zero_iff

end LinearMap

@[simp]
/-
**Matrix.isNilpotent_toLin'_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R : Type u_1} {ι : Type u_3} [inst : DecidableEq ι] [inst_1 : Fintype ι
] [inst_2 : CommSemiring R]   (A : Matrix ι ι R), IsNilpotent (Matrix.toLin' A) 
↔ IsNilpotent A
参数：A : Matrix ι ι R；Matrix.toLin' A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.toMatrix'_toLin'`：∀ {R : Type u_1} [inst : CommSemiring R] {m 
: Type u_4} {n : Type u_5} [inst_1 : DecidableEq n] [inst_2 : Fintype n]   (M : 
Matrix m n R), L…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearMap.isNilpotent_toMatrix_iff`：isNilpotent_toMatrix_iff (b : Basis 
ι R M) (f : M ->ₗ[R] M) : IsNilpotent (toMatrix b b f) ↔ IsNilpotent f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Matrix.isNilpotent_toLin'_iff {ι : Type*} [DecidableEq ι] [Fintype ι] [CommSemiring R]
    (A : Matrix ι ι R) :
    IsNilpotent A.toLin' ↔ IsNilpotent A := by
  have : A.toLin'.toMatrix (Pi.basisFun R ι) (Pi.basisFun R ι) = A := LinearMap.toMatrix'_toLin' A
  conv_rhs => rw [← this]
  rw [LinearMap.isNilpotent_toMatrix_iff]

namespace Module.End

section

variable {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

set_option backward.isDefEq.respectTransparency false in
/-
**Module.End.isNilpotent_restrict_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Module.End`。
形式化陈述：isNilpotent_restrict_of_le {f : End R M} {p q : Submodule R M} {hp : MapsT
o f p p} {hq : MapsTo f q q} (h : p <= q) (hf : IsNilpotent (f.restrict hq)) : I
sNilpotent (f.restrict hp)
参数：h : p <= q；hf : IsNilpotent (f.restrict hq)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `Module.End.pow_apply_mem_of_forall_mem`：∀ {R : Type u_1} {M : Type u_5} 
[inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {f
' : M →ₗ[R] M} {p : Submodul…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.End.pow_restrict`：∀ {R : Type u_1} {M : Type u_5} [inst : Semirin
g R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {f' : M →ₗ[R] M} 
{p : Submodul…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `LinearMap.restrict_apply`：restrict_apply {f : M ->ₛₗ[σ₁₂] M₂} {p : Submo
dule R M} {q : Submodule R₂ M₂} (hf : forall x in p, f x in q) (x : p) : f.restr
ict hf x = ⟨f …
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
lemma isNilpotent_restrict_of_le {f : End R M} {p q : Submodule R M}
    {hp : MapsTo f p p} {hq : MapsTo f q q} (h : p ≤ q) (hf : IsNilpotent (f.restrict hq)) :
    IsNilpotent (f.restrict hp) := by
  obtain ⟨n, hn⟩ := hf
  use n
  ext ⟨x, hx⟩
  replace hn := DFunLike.congr_fun hn ⟨x, h hx⟩
  simp_rw [LinearMap.zero_apply, ZeroMemClass.coe_zero, ZeroMemClass.coe_eq_zero] at hn ⊢
  rw [Module.End.pow_restrict, LinearMap.restrict_apply] at hn ⊢
  ext
  exact (congr_arg Subtype.val hn :)

set_option backward.isDefEq.respectTransparency false in
/-
**Module.End.isNilpotent.restrict** 是 Mathlib 中的一个定理，位于命名空间 `Module.End.isNilpot
ent`。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   {f : M →ₗ[R] M} {p : Submodule R M} (hf : Se
t.MapsTo ⇑f ↑p ↑p), IsNilpotent f → IsNilpotent (f.restrict hf)
参数：hf : Set.MapsTo ⇑f ↑p ↑p；f.restrict hf。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Module.End.pow_apply_mem_of_forall_mem`：∀ {R : Type u_1} {M : Type u_5} 
[inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {f
' : M →ₗ[R] M} {p : Submodul…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Module.End.pow_restrict`：∀ {R : Type u_1} {M : Type u_5} [inst : Semirin
g R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {f' : M →ₗ[R] M} 
{p : Submodul…
· 使用定理 `LinearMap.restrict.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Typ
e u_5} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : Ad
dCommMonoid M] [ins…
-/
lemma isNilpotent.restrict
    {f : M →ₗ[R] M} {p : Submodule R M} (hf : MapsTo f p p) (hnil : IsNilpotent f) :
    IsNilpotent (f.restrict hf) := by
  obtain ⟨n, hn⟩ := hnil
  exact ⟨n, LinearMap.ext fun m ↦ by simp only [Module.End.pow_restrict n, hn,
    LinearMap.restrict_apply, LinearMap.zero_apply]; rfl⟩

end

variable {M : Type v} [Ring R] [AddCommGroup M] [Module R M]
variable {f : Module.End R M} {p : Submodule R M} (hp : p ≤ p.comap f)

/-
**Module.End.IsNilpotent.mapQ** 是 Mathlib 中的一个定理，位于命名空间 `Module.End.IsNilpotent`
。
形式化陈述：∀ {R : Type u_1} {M : Type v} [inst : Ring R] [inst_1 : AddCommGroup M] [i
nst_2 : _root_.Module R M]   {f : Module.End R M} {p : Submodule R M} (hp : p ≤ 
Submodule.comap f p), IsNilpotent f → IsNilpotent (p.mapQ p f hp)
参数：hp : p ≤ Submodule.comap f p；p.mapQ p f hp。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.le_comap_pow_of_le_comap`：le_comap_pow_of_le_comap (p : Submod
ule R M) {f : M ->ₗ[R] M} (h : p <= p.comap f) (k : Nat) : p <= p.comap (f ^ k)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.mapQ_pow`：mapQ_pow {f : M ->ₗ[R] M} (h : p <= p.comap f) (k : 
Nat) (h' : p <= p.comap (f ^ k)
· 使用定理 `Submodule.mapQ.congr_simp`：∀ {R : Type u_1} {M : Type u_2} [inst : Ring 
R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (p : Submodule R M) 
{R₂ : Type u_3}…
· 使用定理 `Submodule.mapQ_zero`：mapQ_zero (h : p <= q.comap (0 : M ->ₛₗ[τ₁₂] M₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsNilpotent.mapQ (hnp : IsNilpotent f) : IsNilpotent (p.mapQ p f hp) := by
  obtain ⟨k, hk⟩ := hnp
  use k
  simp [← p.mapQ_pow, hk]

end Module.End

