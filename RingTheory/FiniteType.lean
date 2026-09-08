/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.RingTheory.Adjoin.Polynomial.Basic
public import Mathlib.RingTheory.Adjoin.Tower
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Noetherian.Orzech

/-!
# Finiteness conditions in commutative algebra

In this file we define a notion of finiteness that is common in commutative algebra.

## Main declarations

- `Algebra.FiniteType`, `RingHom.FiniteType`, `AlgHom.FiniteType`
  all of these express that some object is finitely generated *as an algebra* over some base ring.

-/

@[expose] public section

open Function (Surjective)

open Polynomial

section ModuleAndAlgebra

universe uR uS uA uB uM uN
variable (R : Type uR) (S : Type uS) (A : Type uA) (B : Type uB) (M : Type uM) (N : Type uN)

/-- An algebra over a commutative semiring is of `FiniteType` if it is finitely generated
over the base ring as algebra. -/
/-
**Algebra.FiniteType** 是 Mathlib 中的一个归纳类型，位于命名空间 `Algebra`。
形式化陈述：(R : Type uR) → (A : Type uA) → [inst : CommSemiring R] → [inst_1 : Semiri
ng A] → [Algebra R A] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An algebra over a commutative semiring is of `FiniteType` if it is finitely gene
rated
over the base ring as algebra.
-/
class Algebra.FiniteType [CommSemiring R] [Semiring A] [Algebra R A] : Prop where
  out : (⊤ : Subalgebra R A).FG

namespace Module

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

namespace Finite

open Submodule Set

variable {R S M N}

section Algebra

-- see Note [lower instance priority]
/-
**Module.Finite.** 是 Mathlib 中的一个实例，位于命名空间 `Module.Finite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) finiteType {R : Type*} (A : Type*) [CommSemiring R] [Semiring A]
    [Algebra R A] [hRA : Module.Finite R A] : Algebra.FiniteType R A :=
  ⟨Subalgebra.fg_of_submodule_fg hRA.1⟩

end Algebra

end Finite

end Module

namespace Algebra

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
variable [Algebra R S] [Algebra R A] [Algebra R B]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]

namespace FiniteType

/-
**Algebra.FiniteType.of_restrictScalars_finiteType** 是 Mathlib 中的一个定理，位于命名空间 `Al
gebra.FiniteType`。
形式化陈述：of_restrictScalars_finiteType [Algebra S A] [IsScalarTower R S A] [hA : Fi
niteType R A] : FiniteType S A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FiniteType.out`：∀ {R : Type uR} {A : Type uA} {inst : CommSemiri
ng R} {inst_1 : Semiring A} {inst_2 : Algebra R A}   [self : Algebra.FiniteType 
R A], ⊤.FG
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.eq_top_iff`：eq_top_iff {S : Subalgebra R A} : S = ⊤ ↔ forall x :
 A, x in S
· 使用定理 `Algebra.adjoin_le`：adjoin_le {S : Subalgebra R A} (H : s subseteq S) : a
djoin R s <= S
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem of_restrictScalars_finiteType [Algebra S A] [IsScalarTower R S A] [hA : FiniteType R A] :
    FiniteType S A := by
  obtain ⟨s, hS⟩ := hA.out
  refine ⟨⟨s, eq_top_iff.2 fun b => ?_⟩⟩
  have le : adjoin R (s : Set A) ≤ Subalgebra.restrictScalars R (adjoin S s) := by
    apply (Algebra.adjoin_le _ : adjoin R (s : Set A) ≤ Subalgebra.restrictScalars R (adjoin S ↑s))
    simp only [Subalgebra.coe_restrictScalars]
    exact Algebra.subset_adjoin
  exact le (eq_top_iff.1 hS b)

variable {R S A B}
/-
**Algebra.FiniteType.of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.FiniteType
`。
形式化陈述：of_surjective [FiniteType R A] (f : A ->ₐ[R] B) (hf : Surjective f) : Fini
teType R B
参数：f : A ->ₐ[R] B；hf : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.map_top`：map_top (f : A ->ₐ[R] B) : (⊤ : Subalgebra R A).map f =
 f.range
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Subalgebra.FG.map`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : Comm
Semiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semiring B]
 [inst_…
· 使用定理 `Algebra.FiniteType.out`：∀ {R : Type uR} {A : Type uA} {inst : CommSemiri
ng R} {inst_1 : Semiring A} {inst_2 : Algebra R A}   [self : Algebra.FiniteType 
R A], ⊤.FG
-/
theorem of_surjective [FiniteType R A] (f : A →ₐ[R] B) (hf : Surjective f) : FiniteType R B :=
  ⟨by
    convert ‹FiniteType R A›.1.map f
    simpa only [map_top f, @eq_comm _ ⊤, eq_top_iff, AlgHom.mem_range] using! hf⟩
/-
**Algebra.FiniteType.equiv** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.FiniteType`。
形式化陈述：equiv (hRA : FiniteType R A) (e : A ≃ₐ[R] B) : FiniteType R B
参数：hRA : FiniteType R A；e : A ≃ₐ[R] B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FiniteType.of_surjective`：of_surjective [FiniteType R A] (f : A 
->ₐ[R] B) (hf : Surjective f) : FiniteType R B
· 使用定理 `AlgEquiv.surjective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [in
st : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : A
lgebra R …
-/
theorem equiv (hRA : FiniteType R A) (e : A ≃ₐ[R] B) : FiniteType R B :=
  hRA.of_surjective e e.surjective
/-
**Algebra.FiniteType.trans** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.FiniteType`。
形式化陈述：trans [Algebra S A] [IsScalarTower R S A] (hRS : FiniteType R S) (hSA : Fi
niteType S A) : FiniteType R A
参数：hRS : FiniteType R S；hSA : FiniteType S A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.fg_trans'`：Algebra.fg_trans' {R S A : Type*} [CommSemiring R] [C
ommSemiring S] [Semiring A] [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarT
ower R …
· 使用定理 `Algebra.FiniteType.out`：∀ {R : Type uR} {A : Type uA} {inst : CommSemiri
ng R} {inst_1 : Semiring A} {inst_2 : Algebra R A}   [self : Algebra.FiniteType 
R A], ⊤.FG
-/
theorem trans [Algebra S A] [IsScalarTower R S A] (hRS : FiniteType R S) (hSA : FiniteType S A) :
    FiniteType R A :=
  ⟨fg_trans' hRS.1 hSA.1⟩
/-
**Algebra.FiniteType.quotient** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.FiniteType`。
形式化陈述：quotient (R : Type*) {S : Type*} [CommSemiring R] [CommRing S] [Algebra R 
S] (I : Ideal S) [h : Algebra.FiniteType R S] : Algebra.FiniteType R (S ⧸ I)
参数：R : Type*；I : Ideal S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FiniteType.trans`：trans [Algebra S A] [IsScalarTower R S A] (hRS
 : FiniteType R S) (hSA : FiniteType S A) : FiniteType R A
· 使用定理 `Ideal.Quotient.isScalarTower`：∀ (R₁ : Type u_1) (R₂ : Type u_2) {A : Typ
e u_3} [inst : CommSemiring R₁] [inst_1 : CommSemiring R₂] [inst_2 : Ring A]   [
inst_3 : Algebra R…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Module.Finite.finiteType`：∀ {R : Type u_1} (A : Type u_2) [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [hRA : Module.Finite R 
A], Algebra.Fi…
-/
instance quotient (R : Type*) {S : Type*} [CommSemiring R] [CommRing S] [Algebra R S] (I : Ideal S)
    [h : Algebra.FiniteType R S] : Algebra.FiniteType R (S ⧸ I) :=
  Algebra.FiniteType.trans h inferInstance
/-
**Algebra.FiniteType.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.FiniteType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [FiniteType R S] : FiniteType R S[X] := by
  refine .trans ‹_› ⟨{Polynomial.X}, ?_⟩
  rw [Finset.coe_singleton]
  exact Polynomial.adjoin_X
/-
**Algebra.FiniteType.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.FiniteType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι : Type*} [Finite ι] [FiniteType R S] : FiniteType R (MvPolynomial ι S) := by
  classical
  cases nonempty_fintype ι
  refine .trans ‹_› ⟨Finset.univ.image MvPolynomial.X, ?_⟩
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  exact MvPolynomial.adjoin_range_X
/-
**Algebra.FiniteType.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.FiniteType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι : Type*} [Finite ι] [FiniteType R S] : FiniteType R (FreeAlgebra S ι) := by
  classical
  cases nonempty_fintype ι
  refine .trans ‹_› ⟨Finset.univ.image (FreeAlgebra.ι _), ?_⟩
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  exact FreeAlgebra.adjoin_range_ι ..

/-- An algebra is finitely generated if and only if it is a quotient
of a free algebra whose variables are indexed by a finset. -/
/-
**Algebra.FiniteType.iff_quotient_freeAlgebra** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
.FiniteType`。
形式化陈述：iff_quotient_freeAlgebra : FiniteType R A ↔ exists (s : Finset A) (f : Fre
eAlgebra R s ->ₐ[R] A), Surjective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_eq_univ`：range_eq_univ : range f = univ ↔ Surjective f
· 使用定理 `AlgHom.coe_range`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semiring B] 
[inst_…
· 使用定理 `Algebra.adjoin_range_eq_range_freeAlgebra_lift`：∀ (R : Type u_1) (X : Ty
pe u_2) [inst : CommSemiring R] {A : Type u_3} [inst_1 : Semiring A] [inst_2 : A
lgebra R A]   (f : X → A), Algebra.a…
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Finset.setOfPred_mem`：setOfPred_mem {α} {s : Finset α} : { a | a in s } 
= s
· 使用定理 `Algebra.coe_top`：coe_top : (↑(⊤ : Subalgebra R A) : Set A) = Set.univ
· 使用定理 `Algebra.FiniteType.of_surjective`：of_surjective [FiniteType R A] (f : A 
->ₐ[R] B) (hf : Surjective f) : FiniteType R B
· 使用定理 `Algebra.FiniteType.instFreeAlgebraOfFinite`：∀ {R : Type uR} {S : Type uS
} [inst : CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S] {ι : 
Type u_1}   [Finite ι] [Algebra.…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Module.Finite.finiteType`：∀ {R : Type u_1} (A : Type u_2) [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [hRA : Module.Finite R 
A], Algebra.Fi…

--- 原说明 ---
An algebra is finitely generated if and only if it is a quotient
of a free algebra whose variables are indexed by a finset.
-/
theorem iff_quotient_freeAlgebra :
    FiniteType R A ↔
      ∃ (s : Finset A) (f : FreeAlgebra R s →ₐ[R] A), Surjective f := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, FreeAlgebra.lift _ (↑), ?_⟩
    rw [← Set.range_eq_univ, ← AlgHom.coe_range, ← adjoin_range_eq_range_freeAlgebra_lift,
      Subtype.range_coe_subtype, Finset.setOfPred_mem, hs, coe_top]
  · rintro ⟨s, f, hsur⟩
    exact .of_surjective f hsur

/-- A commutative algebra is finitely generated if and only if it is a quotient
of a polynomial ring whose variables are indexed by a finset. -/
/-
**Algebra.FiniteType.iff_quotient_mvPolynomial** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
a.FiniteType`。
形式化陈述：iff_quotient_mvPolynomial : FiniteType R S ↔ exists (s : Finset S) (f : Mv
Polynomial { x // x in s } R ->ₐ[R] S), Surjective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `AlgHom.coe_range`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semiring B] 
[inst_…
· 使用定理 `Algebra.adjoin_eq_range`：∀ (R : Type u) {S₁ : Type v} [inst : CommSemiri
ng R] [inst_1 : CommSemiring S₁] [inst_2 : Algebra R S₁] (s : Set S₁),   Algebra
.adjoin R s =…
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Algebra.mem_top`：mem_top {x : A} : x in (⊤ : Subalgebra R A)
· 使用定理 `Algebra.FiniteType.of_surjective`：of_surjective [FiniteType R A] (f : A 
->ₐ[R] B) (hf : Surjective f) : FiniteType R B
· 使用定理 `Algebra.FiniteType.instMvPolynomialOfFinite`：∀ {R : Type uR} {S : Type u
S} [inst : CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S] {ι :
 Type u_1}   [Finite ι] [Algebra.…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Module.Finite.finiteType`：∀ {R : Type u_1} (A : Type u_2) [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [hRA : Module.Finite R 
A], Algebra.Fi…

--- 原说明 ---
A commutative algebra is finitely generated if and only if it is a quotient
of a polynomial ring whose variables are indexed by a finset.
-/
theorem iff_quotient_mvPolynomial :
    FiniteType R S ↔
      ∃ (s : Finset S) (f : MvPolynomial { x // x ∈ s } R →ₐ[R] S), Surjective f := by
  constructor
  · rintro ⟨s, hs⟩
    use s, MvPolynomial.aeval (↑)
    intro x
    rw [← Set.mem_range, ← AlgHom.coe_range, ← adjoin_eq_range, SetLike.mem_coe, hs]
    apply mem_top
  · rintro ⟨s, f, hsur⟩
    exact .of_surjective f hsur

/-- An algebra is finitely generated if and only if it is a quotient
of a polynomial ring whose variables are indexed by a fintype. -/
/-
**Algebra.FiniteType.iff_quotient_freeAlgebra'** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
a.FiniteType`。
形式化陈述：iff_quotient_freeAlgebra' : FiniteType R A ↔ exists (ι : Type uA) (_ : Fin
type ι) (f : FreeAlgebra R ι ->ₐ[R] A), Surjective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.FiniteType.iff_quotient_freeAlgebra`：iff_quotient_freeAlgebra : 
FiniteType R A ↔ exists (s : Finset A) (f : FreeAlgebra R s ->ₐ[R] A), Surjectiv
e f
· 使用定理 `Algebra.FiniteType.of_surjective`：of_surjective [FiniteType R A] (f : A 
->ₐ[R] B) (hf : Surjective f) : FiniteType R B
· 使用定理 `Algebra.FiniteType.instFreeAlgebraOfFinite`：∀ {R : Type uR} {S : Type uS
} [inst : CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S] {ι : 
Type u_1}   [Finite ι] [Algebra.…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Module.Finite.finiteType`：∀ {R : Type u_1} (A : Type u_2) [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [hRA : Module.Finite R 
A], Algebra.Fi…

--- 原说明 ---
An algebra is finitely generated if and only if it is a quotient
of a polynomial ring whose variables are indexed by a fintype.
-/
theorem iff_quotient_freeAlgebra' : FiniteType R A ↔
    ∃ (ι : Type uA) (_ : Fintype ι) (f : FreeAlgebra R ι →ₐ[R] A), Surjective f := by
  constructor
  · rw [iff_quotient_freeAlgebra]
    rintro ⟨s, f, hsur⟩
    use { x : A // x ∈ s }, inferInstance, f
  · rintro ⟨ι, hfintype, f, hsur⟩
    let : Fintype ι := hfintype
    exact .of_surjective f hsur

/-- A commutative algebra is finitely generated if and only if it is a quotient
of a polynomial ring whose variables are indexed by a fintype. -/
/-
**Algebra.FiniteType.iff_quotient_mvPolynomial'** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
ra.FiniteType`。
形式化陈述：iff_quotient_mvPolynomial' : FiniteType R S ↔ exists (ι : Type uS) (_ : Fi
ntype ι) (f : MvPolynomial ι R ->ₐ[R] S), Surjective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.FiniteType.iff_quotient_mvPolynomial`：iff_quotient_mvPolynomial 
: FiniteType R S ↔ exists (s : Finset S) (f : MvPolynomial { x // x in s } R ->ₐ
[R] S), Surjective f
· 使用定理 `Algebra.FiniteType.of_surjective`：of_surjective [FiniteType R A] (f : A 
->ₐ[R] B) (hf : Surjective f) : FiniteType R B
· 使用定理 `Algebra.FiniteType.instMvPolynomialOfFinite`：∀ {R : Type uR} {S : Type u
S} [inst : CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S] {ι :
 Type u_1}   [Finite ι] [Algebra.…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Module.Finite.finiteType`：∀ {R : Type u_1} (A : Type u_2) [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [hRA : Module.Finite R 
A], Algebra.Fi…

--- 原说明 ---
A commutative algebra is finitely generated if and only if it is a quotient
of a polynomial ring whose variables are indexed by a fintype.
-/
theorem iff_quotient_mvPolynomial' : FiniteType R S ↔
    ∃ (ι : Type uS) (_ : Fintype ι) (f : MvPolynomial ι R →ₐ[R] S), Surjective f := by
  constructor
  · rw [iff_quotient_mvPolynomial]
    rintro ⟨s, f, hsur⟩
    use { x : S // x ∈ s }, inferInstance, f
  · rintro ⟨ι, hfintype, f, hsur⟩
    let : Fintype ι := hfintype
    exact .of_surjective f hsur

/-- A commutative algebra is finitely generated if and only if it is a quotient of a polynomial ring
in `n` variables. -/
/-
**Algebra.FiniteType.iff_quotient_mvPolynomial''** 是 Mathlib 中的一个定理，位于命名空间 `Alge
bra.FiniteType`。
形式化陈述：iff_quotient_mvPolynomial'' : FiniteType R S ↔ exists (n : Nat) (f : MvPol
ynomial (Fin n) R ->ₐ[R] S), Surjective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.FiniteType.iff_quotient_mvPolynomial'`：iff_quotient_mvPolynomial
' : FiniteType R S ↔ exists (ι : Type uS) (_ : Fintype ι) (f : MvPolynomial ι R 
->ₐ[R] S), Surjective f
· 使用定理 `Algebra.FiniteType.of_surjective`：of_surjective [FiniteType R A] (f : A 
->ₐ[R] B) (hf : Surjective f) : FiniteType R B
· 使用定理 `Algebra.FiniteType.instMvPolynomialOfFinite`：∀ {R : Type uR} {S : Type u
S} [inst : CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S] {ι :
 Type u_1}   [Finite ι] [Algebra.…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Module.Finite.finiteType`：∀ {R : Type u_1} (A : Type u_2) [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [hRA : Module.Finite R 
A], Algebra.Fi…

--- 原说明 ---
A commutative algebra is finitely generated if and only if it is a quotient of a
 polynomial ring
in `n` variables.
-/
theorem iff_quotient_mvPolynomial'' :
    FiniteType R S ↔ ∃ (n : ℕ) (f : MvPolynomial (Fin n) R →ₐ[R] S), Surjective f := by
  constructor
  · rw [iff_quotient_mvPolynomial']
    rintro ⟨ι, hfintype, f, hsur⟩
    have equiv := MvPolynomial.renameEquiv R (Fintype.equivFin ι)
    exact ⟨Fintype.card ι, AlgHom.comp f equiv.symm.toAlgHom, by simpa using hsur⟩
  · rintro ⟨n, f, hsur⟩
    exact .of_surjective f hsur
/-
**Algebra.FiniteType.prod** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.FiniteType`。
形式化陈述：prod [hA : FiniteType R A] [hB : FiniteType R B] : FiniteType R (A × B)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subalgebra.prod_top`：prod_top : (prod ⊤ ⊤ : Subalgebra R (A × B)) = ⊤
· 使用定理 `Subalgebra.FG.prod`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semiring B
] [inst_…
· 使用定理 `Algebra.FiniteType.out`：∀ {R : Type uR} {A : Type uA} {inst : CommSemiri
ng R} {inst_1 : Semiring A} {inst_2 : Algebra R A}   [self : Algebra.FiniteType 
R A], ⊤.FG
-/
instance prod [hA : FiniteType R A] [hB : FiniteType R B] : FiniteType R (A × B) :=
  ⟨by rw [← Subalgebra.prod_top]; exact hA.1.prod hB.1⟩
/-
**Algebra.FiniteType.isNoetherianRing** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.FiniteT
ype`。
形式化陈述：isNoetherianRing (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [h 
: Algebra.FiniteType R S] [IsNoetherianRing R] : IsNoetherianRing S
参数：R S : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FiniteType.out`：∀ {R : Type uR} {A : Type uA} {inst : CommSemiri
ng R} {inst_1 : Semiring A} {inst_2 : Algebra R A}   [self : Algebra.FiniteType 
R A], ⊤.FG
· 使用定理 `isNoetherianRing_of_surjective`：isNoetherianRing_of_surjective (R) [Semi
ring R] (S) [Semiring S] (f : R ->+* S) (hf : Function.Surjective f) [H : IsNoet
herianRing R] : IsNo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_eq_univ`：range_eq_univ : range f = univ ↔ Surjective f
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgHom.toRingHom_eq_coe`：toRingHom_eq_coe (f : A ->ₐ[R] B) : f.toRingHom
 = f
· 使用定理 `RingHom.coe_coe`：coe_coe {F : Type*} [FunLike F α β] [RingHomClass F α β
] (f : F) : ((f : α ->+* β) : α -> β) = f
· 使用定理 `AlgHom.coe_range`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semiring B] 
[inst_…
· 使用定理 `Algebra.adjoin_range_eq_range_aeval`：∀ (R : Type u) {S₁ : Type v} {σ : T
ype u_1} [inst : CommSemiring R] [inst_1 : CommSemiring S₁] [inst_2 : Algebra R 
S₁]   (f : σ → S₁), Algeb…
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Finset.setOfPred_mem`：setOfPred_mem {α} {s : Finset α} : { a | a in s } 
= s
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem isNoetherianRing (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [h : Algebra.FiniteType R S] [IsNoetherianRing R] : IsNoetherianRing S := by
  obtain ⟨s, hs⟩ := h.1
  apply
    isNoetherianRing_of_surjective (MvPolynomial s R) S
      (MvPolynomial.aeval (↑) : MvPolynomial s R →ₐ[R] S).toRingHom
  rw [← Set.range_eq_univ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← AlgHom.coe_range,
    ← Algebra.adjoin_range_eq_range_aeval, Subtype.range_coe_subtype, Finset.setOfPred_mem, hs]
  rfl
/-
**Algebra.FiniteType._root_.Subalgebra.fg_iff_finiteType** 是 Mathlib 中的一个定理，位于命名
空间 `Algebra.FiniteType`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Subalgebra.fg_iff_finiteType (S : Subalgebra R A) : S.FG ↔ Algebra.FiniteType R S :=
  S.fg_top.symm.trans ⟨fun h => ⟨h⟩, fun h => h.out⟩
/-
**Algebra.FiniteType.adjoin_of_finite** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.FiniteT
ype`。
形式化陈述：adjoin_of_finite {A : Type*} [CommSemiring A] [Algebra R A] {t : Set A} (h
 : Set.Finite t) : FiniteType R (Algebra.adjoin R t)
参数：h : Set.Finite t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subalgebra.fg_iff_finiteType`：∀ {R : Type uR} {A : Type uA} [inst : Comm
Semiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A),  
 S.FG ↔ Algebra.Fi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma adjoin_of_finite {A : Type*} [CommSemiring A] [Algebra R A] {t : Set A} (h : Set.Finite t) :
    FiniteType R (Algebra.adjoin R t) := by
  rw [← Subalgebra.fg_iff_finiteType]
  exact ⟨h.toFinset, by simp⟩

end FiniteType

end Algebra

end ModuleAndAlgebra

namespace RingHom

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

/-- A ring morphism `A →+* B` is of `FiniteType` if `B` is finitely generated as `A`-algebra. -/
@[algebraize]
/-
**RingHom.FiniteType** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：FiniteType (f : A ->+* B) : Prop
参数：f : A ->+* B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring morphism `A →+* B` is of `FiniteType` if `B` is finitely generated as `A`
-algebra.
-/
def FiniteType (f : A →+* B) : Prop :=
  @Algebra.FiniteType A B _ _ f.toAlgebra
/-
**RingHom.finiteType_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：finiteType_algebraMap [Algebra A B] : (algebraMap A B).FiniteType ↔ Algebr
a.FiniteType A B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.FiniteType.eq_1`：∀ {A : Type u_1} {B : Type u_2} [inst : CommRin
g A] [inst_1 : CommRing B] (f : A →+* B),   f.FiniteType = Algebra.FiniteType A 
B
· 使用定理 `toAlgebra_algebraMap`：∀ {R : Type u} {S : Type v} [inst : CommSemiring R
] [inst_1 : CommSemiring S] [inst_2 : Algebra R S],   (algebraMap R S).toAlgebra
 = inst_2
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma finiteType_algebraMap [Algebra A B] :
    (algebraMap A B).FiniteType ↔ Algebra.FiniteType A B := by
  rw [FiniteType, toAlgebra_algebraMap]

namespace Finite

/-
**RingHom.Finite.finiteType** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.Finite`。
形式化陈述：finiteType {f : A ->+* B} (hf : f.Finite) : FiniteType f
参数：hf : f.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.finiteType`：∀ {R : Type u_1} (A : Type u_2) [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [hRA : Module.Finite R 
A], Algebra.Fi…
-/
theorem finiteType {f : A →+* B} (hf : f.Finite) : FiniteType f :=
  @Module.Finite.finiteType _ _ _ _ f.toAlgebra hf

end Finite

namespace FiniteType

-- TODO: should infer_instance be marked as normalising?
set_option linter.flexible false in
variable (A) in
/-
**RingHom.FiniteType.id** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.FiniteType`。
形式化陈述：id : FiniteType (RingHom.id A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.finiteType`：∀ {R : Type u_1} (A : Type u_2) [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [hRA : Module.Finite R 
A], Algebra.Fi…
-/
theorem id : FiniteType (RingHom.id A) := by simp [FiniteType]; infer_instance
/-
**RingHom.FiniteType.comp_surjective** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.FiniteTy
pe`。
形式化陈述：comp_surjective {f : A ->+* B} {g : B ->+* C} (hf : f.FiniteType) (hg : Su
rjective g) : (g.comp f).FiniteType
参数：hf : f.FiniteType；hg : Surjective g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FiniteType.of_surjective`：of_surjective [FiniteType R A] (f : A 
->ₐ[R] B) (hf : Surjective f) : FiniteType R B
· 使用定理 `OneHom.map_one'`：∀ {M : Type u_10} {N : Type u_11} [inst : One M] [inst_
1 : One N] (self : OneHom M N), self.toFun 1 = 1
· 使用定理 `MonoidHom.map_mul'`：∀ {M : Type u_10} {N : Type u_11} [inst : MulOne M] 
[inst_1 : MulOne N] (self : M →* N) (x y : M),   (↑self).toFun (x * y) = (↑self)
.toFun x…
· 使用定理 `RingHom.map_zero'`：∀ {α : Type u_5} {β : Type u_6} [inst : NonAssocSemir
ing α] [inst_1 : NonAssocSemiring β] (self : α →+* β),   (↑↑self).toFun 0 = 0
· 使用定理 `RingHom.map_add'`：∀ {α : Type u_5} {β : Type u_6} [inst : NonAssocSemiri
ng α] [inst_1 : NonAssocSemiring β] (self : α →+* β) (x y : α),   (↑↑self).toFun
 (x + …
-/
theorem comp_surjective {f : A →+* B} {g : B →+* C} (hf : f.FiniteType) (hg : Surjective g) :
    (g.comp f).FiniteType := by
  algebraize_only [f, g.comp f]
  exact ‹Algebra.FiniteType _ _›.of_surjective
    { g with
      toFun := g
      commutes' := fun a => rfl }
    hg
/-
**RingHom.FiniteType.of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.FiniteType
`。
形式化陈述：of_surjective (f : A ->+* B) (hf : Surjective f) : f.FiniteType
参数：f : A ->+* B；hf : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.comp_id`：comp_id (f : α ->+* β) : f.comp (id α) = f
· 使用定理 `RingHom.FiniteType.comp_surjective`：comp_surjective {f : A ->+* B} {g : 
B ->+* C} (hf : f.FiniteType) (hg : Surjective g) : (g.comp f).FiniteType
· 使用定理 `RingHom.FiniteType.id`：id : FiniteType (RingHom.id A)
-/
theorem of_surjective (f : A →+* B) (hf : Surjective f) : f.FiniteType := by
  rw [← f.comp_id]
  exact (id A).comp_surjective hf
/-
**RingHom.FiniteType.comp** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.FiniteType`。
形式化陈述：comp {g : B ->+* C} {f : A ->+* B} (hg : g.FiniteType) (hf : f.FiniteType)
 : (g.comp f).FiniteType
参数：hg : g.FiniteType；hf : f.FiniteType。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Algebra.FiniteType.trans`：trans [Algebra S A] [IsScalarTower R S A] (hRS
 : FiniteType R S) (hSA : FiniteType S A) : FiniteType R A
-/
theorem comp {g : B →+* C} {f : A →+* B} (hg : g.FiniteType) (hf : f.FiniteType) :
    (g.comp f).FiniteType := by
  algebraize_only [f, g, g.comp f]
  exact Algebra.FiniteType.trans hf hg
/-
**RingHom.FiniteType.of_finite** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.FiniteType`。
形式化陈述：of_finite {f : A ->+* B} (hf : f.Finite) : f.FiniteType
参数：hf : f.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.finiteType`：∀ {R : Type u_1} (A : Type u_2) [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [hRA : Module.Finite R 
A], Algebra.Fi…
-/
theorem of_finite {f : A →+* B} (hf : f.Finite) : f.FiniteType :=
  @Module.Finite.finiteType _ _ _ _ f.toAlgebra hf

alias _root_.RingHom.Finite.to_finiteType := of_finite
/-
**RingHom.FiniteType.of_comp_finiteType** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.Finit
eType`。
形式化陈述：of_comp_finiteType {f : A ->+* B} {g : B ->+* C} (h : (g.comp f).FiniteTyp
e) : g.FiniteType
参数：h : (g.comp f).FiniteType。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Algebra.FiniteType.of_restrictScalars_finiteType`：of_restrictScalars_fin
iteType [Algebra S A] [IsScalarTower R S A] [hA : FiniteType R A] : FiniteType S
 A
-/
theorem of_comp_finiteType {f : A →+* B} {g : B →+* C} (h : (g.comp f).FiniteType) :
    g.FiniteType := by
  algebraize [f, g, g.comp f]
  exact Algebra.FiniteType.of_restrictScalars_finiteType A B C

end FiniteType

end RingHom

namespace AlgHom

variable {R A B C : Type*} [CommRing R]
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra R A] [Algebra R B] [Algebra R C]

/-- An algebra morphism `A →ₐ[R] B` is of `FiniteType` if it is of finite type as ring morphism.
In other words, if `B` is finitely generated as `A`-algebra. -/
/-
**AlgHom.FiniteType** 是 Mathlib 中的一个定义，位于命名空间 `AlgHom`。
形式化陈述：FiniteType (f : A ->ₐ[R] B) : Prop
参数：f : A ->ₐ[R] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An algebra morphism `A →ₐ[R] B` is of `FiniteType` if it is of finite type as ri
ng morphism.
In other words, if `B` is finitely generated as `A`-algebra.
-/
def FiniteType (f : A →ₐ[R] B) : Prop :=
  f.toRingHom.FiniteType

namespace Finite

/-
**AlgHom.Finite.finiteType** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom.Finite`。
形式化陈述：finiteType {f : A ->ₐ[R] B} (hf : f.Finite) : FiniteType f
参数：hf : f.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.Finite.finiteType`：finiteType {f : A ->+* B} (hf : f.Finite) : F
initeType f
-/
theorem finiteType {f : A →ₐ[R] B} (hf : f.Finite) : FiniteType f :=
  RingHom.Finite.finiteType hf

end Finite

namespace FiniteType

variable (R A)

/-
**AlgHom.FiniteType.id** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom.FiniteType`。
形式化陈述：id : FiniteType (AlgHom.id R A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.FiniteType.id`：id : FiniteType (RingHom.id A)
-/
theorem id : FiniteType (AlgHom.id R A) :=
  RingHom.FiniteType.id A

variable {R A}
/-
**AlgHom.FiniteType.comp** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom.FiniteType`。
形式化陈述：comp {g : B ->ₐ[R] C} {f : A ->ₐ[R] B} (hg : g.FiniteType) (hf : f.FiniteT
ype) : (g.comp f).FiniteType
参数：hg : g.FiniteType；hf : f.FiniteType。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.FiniteType.comp`：comp {g : B ->+* C} {f : A ->+* B} (hg : g.Fini
teType) (hf : f.FiniteType) : (g.comp f).FiniteType
-/
theorem comp {g : B →ₐ[R] C} {f : A →ₐ[R] B} (hg : g.FiniteType) (hf : f.FiniteType) :
    (g.comp f).FiniteType :=
  RingHom.FiniteType.comp hg hf
/-
**AlgHom.FiniteType.comp_surjective** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom.FiniteType
`。
形式化陈述：comp_surjective {f : A ->ₐ[R] B} {g : B ->ₐ[R] C} (hf : f.FiniteType) (hg 
: Surjective g) : (g.comp f).FiniteType
参数：hf : f.FiniteType；hg : Surjective g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.FiniteType.comp_surjective`：comp_surjective {f : A ->+* B} {g : 
B ->+* C} (hf : f.FiniteType) (hg : Surjective g) : (g.comp f).FiniteType
-/
theorem comp_surjective {f : A →ₐ[R] B} {g : B →ₐ[R] C} (hf : f.FiniteType) (hg : Surjective g) :
    (g.comp f).FiniteType :=
  RingHom.FiniteType.comp_surjective hf hg
/-
**AlgHom.FiniteType.of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom.FiniteType`。
形式化陈述：of_surjective (f : A ->ₐ[R] B) (hf : Surjective f) : f.FiniteType
参数：f : A ->ₐ[R] B；hf : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.FiniteType.of_surjective`：of_surjective (f : A ->+* B) (hf : Sur
jective f) : f.FiniteType
-/
theorem of_surjective (f : A →ₐ[R] B) (hf : Surjective f) : f.FiniteType :=
  RingHom.FiniteType.of_surjective f.toRingHom hf
/-
**AlgHom.FiniteType.of_comp_finiteType** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom.FiniteT
ype`。
形式化陈述：of_comp_finiteType {f : A ->ₐ[R] B} {g : B ->ₐ[R] C} (h : (g.comp f).Finit
eType) : g.FiniteType
参数：h : (g.comp f).FiniteType。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.FiniteType.of_comp_finiteType`：of_comp_finiteType {f : A ->+* B}
 {g : B ->+* C} (h : (g.comp f).FiniteType) : g.FiniteType
-/
theorem of_comp_finiteType {f : A →ₐ[R] B} {g : B →ₐ[R] C} (h : (g.comp f).FiniteType) :
    g.FiniteType :=
  RingHom.FiniteType.of_comp_finiteType h

end FiniteType

end AlgHom

section MonoidAlgebra

variable {R : Type*} {M : Type*}

namespace AddMonoidAlgebra

open Algebra AddSubmonoid Submodule

section Span

section Semiring

variable [CommSemiring R] [AddMonoid M]

/-- An element of `R[M]` is in the subalgebra generated by its support. -/
/-
**AddMonoidAlgebra.mem_adjoin_support** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebr
a`。
形式化陈述：mem_adjoin_support (f : R[M]) : f in adjoin R (of' R M '' f.coeff.support)
参数：f : R[M]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `AddMonoidAlgebra.mem_span_support_coeff`：mem_span_support_coeff (f : k[G
]) : f in Submodule.span k (of' k G '' f.coeff.support)

--- 原说明 ---
An element of `R[M]` is in the subalgebra generated by its support.
-/
theorem mem_adjoin_support (f : R[M]) : f ∈ adjoin R (of' R M '' f.coeff.support) :=
  (adjoin R (of' R M '' f.coeff.support)).toSubmodule.span_le.2 subset_adjoin
    (mem_span_support_coeff f)

/-- If a set `S` generates, as algebra, `R[M]`, then the set of supports of
elements of `S` generates `R[M]`. -/
/-
**AddMonoidAlgebra.support_gen_of_gen** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebr
a`。
形式化陈述：support_gen_of_gen {S : Set R[M]} (hS : Algebra.adjoin R S = ⊤) : Algebra.
adjoin R (⋃ f in S, of' R M '' (f.coeff.support : Set M)) = ⊤
参数：hS : Algebra.adjoin R S = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.adjoin_le_iff`：adjoin_le_iff {S : Subalgebra R A} : adjoin R s <
= S ↔ s subseteq S
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion₂`：mem_iUnion₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋃ (i) (j), s i j) ↔ exists i j, x in s i j
· 使用定理 `Algebra.adjoin_mono`：adjoin_mono (H : s subseteq t) : adjoin R s <= adjo
in R t
· 使用定理 `AddMonoidAlgebra.mem_adjoin_support`：mem_adjoin_support (f : R[M]) : f i
n adjoin R (of' R M '' f.coeff.support)

--- 原说明 ---
If a set `S` generates, as algebra, `R[M]`, then the set of supports of
elements of `S` generates `R[M]`.
-/
theorem support_gen_of_gen {S : Set R[M]} (hS : Algebra.adjoin R S = ⊤) :
    Algebra.adjoin R (⋃ f ∈ S, of' R M '' (f.coeff.support : Set M)) = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← hS, adjoin_le_iff]
  intro f hf
  have hincl : of' R M '' f.coeff.support ⊆ ⋃ g ∈ S, of' R M '' g.coeff.support :=
    fun s hs ↦ Set.mem_iUnion₂.2 ⟨f, hf, hs⟩
  exact adjoin_mono hincl (mem_adjoin_support f)

/-- If a set `S` generates, as algebra, `R[M]`, then the image of the union of
the supports of elements of `S` generates `R[M]`. -/
/-
**AddMonoidAlgebra.support_gen_of_gen'** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgeb
ra`。
形式化陈述：support_gen_of_gen' {S : Set R[M]} (hS : Algebra.adjoin R S = ⊤) : Algebra
.adjoin R (of' R M '' ⋃ f in S, (f.coeff.support : Set M)) = ⊤
参数：hS : Algebra.adjoin R S = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_iUnion`：image_iUnion {f : α -> β} {s : ι -> Set α} : (f '' ⋃ i
, s i) = ⋃ i, f '' s i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AddMonoidAlgebra.support_gen_of_gen`：support_gen_of_gen {S : Set R[M]} (
hS : Algebra.adjoin R S = ⊤) : Algebra.adjoin R (⋃ f in S, of' R M '' (f.coeff.s
upport : Set M)) = ⊤

--- 原说明 ---
If a set `S` generates, as algebra, `R[M]`, then the image of the union of
the supports of elements of `S` generates `R[M]`.
-/
theorem support_gen_of_gen' {S : Set R[M]} (hS : Algebra.adjoin R S = ⊤) :
    Algebra.adjoin R (of' R M '' ⋃ f ∈ S, (f.coeff.support : Set M)) = ⊤ := by
  suffices of' R M '' ⋃ f ∈ S, (f.coeff.support : Set M) = ⋃ f ∈ S, of' R M '' f.coeff.support by
    rw [this]
    exact support_gen_of_gen hS
  simp only [Set.image_iUnion]

end Semiring

section Ring

variable [CommRing R] [AddMonoid M]

/-- If `R[M]` is of finite type, then there is a `G : Finset M` such that its
image generates, as algebra, `R[M]`. -/
/-
**AddMonoidAlgebra.exists_finset_adjoin_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `AddMon
oidAlgebra`。
形式化陈述：exists_finset_adjoin_eq_top [h : FiniteType R R[M]] : exists G : Finset M,
 Algebra.adjoin R (of' R M '' G) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.coe_biUnion`：coe_biUnion : (s.biUnion t : Set β) = ⋃ x in (s : Se
t α), t x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AddMonoidAlgebra.support_gen_of_gen'`：support_gen_of_gen' {S : Set R[M]}
 (hS : Algebra.adjoin R S = ⊤) : Algebra.adjoin R (of' R M '' ⋃ f in S, (f.coeff
.support : Set M)) = ⊤

--- 原说明 ---
If `R[M]` is of finite type, then there is a `G : Finset M` such that its
image generates, as algebra, `R[M]`.
-/
theorem exists_finset_adjoin_eq_top [h : FiniteType R R[M]] :
    ∃ G : Finset M, Algebra.adjoin R (of' R M '' G) = ⊤ := by
  obtain ⟨S, hS⟩ := h
  let : DecidableEq M := Classical.decEq M
  use Finset.biUnion S fun f => f.coeff.support
  have : S.biUnion (fun f => f.coeff.support) = ⋃ f ∈ S, (f.coeff.support : Set M) := by
    simp only [Finset.set_biUnion_coe, Finset.coe_biUnion]
  rw [this]
  exact support_gen_of_gen' hS

end Ring

end Span

/-- If a set `S` generates an additive monoid `M`, then the image of `M` generates, as algebra,
`R[M]`. -/
/-
**AddMonoidAlgebra.mvPolynomial_aeval_of_surjective_of_closure** 是 Mathlib 中的一个定
理，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：mvPolynomial_aeval_of_surjective_of_closure [AddCommMonoid M] [CommSemirin
g R] {S : Set M} (hS : closure S = ⊤) : Function.Surjective (MvPolynomial.aeval 
fun s : S => of' R M ↑s : MvPolynomial S R -> R[M])
参数：hS : closure S = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.induction_on`：induction_on [AddMonoid M] {motive : R[M]
 -> Prop} (x : R[M]) (of : forall m, motive (.of R M <| .ofAdd m)) (add : forall
 x y : R[M], motive…
· 使用定理 `AddSubmonoid.mem_top`：∀ {M : Type u_1} [inst : AddZeroClass M] (x : M), 
x ∈ ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddSubmonoid.closure_induction`：∀ {M : Type u_1} [inst : AddZeroClass M]
 {s : Set M} {motive : (x : M) → x ∈ AddSubmonoid.closure s → Prop},   (∀ (x : M
) (h : x ∈ s), motiv…
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `AddMonoidAlgebra.of_apply`：of_apply [AddZeroClass M] (a : Multiplicative
 M) : of R M a = single a.toAdd 1
· 使用定理 `AddMonoidAlgebra.single_mul_single`：∀ {R : Type u_1} {M : Type u_4} [ins
t : Semiring R] [inst_1 : Add M] (m₁ m₂ : M) (r₁ r₂ : R),   AddMonoidAlgebra.sin
gle m₁ r₁ * AddMonoidAlg…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…

--- 原说明 ---
If a set `S` generates an additive monoid `M`, then the image of `M` generates, 
as algebra,
`R[M]`.
-/
theorem mvPolynomial_aeval_of_surjective_of_closure [AddCommMonoid M] [CommSemiring R] {S : Set M}
    (hS : closure S = ⊤) :
    Function.Surjective
      (MvPolynomial.aeval fun s : S => of' R M ↑s : MvPolynomial S R → R[M]) := by
  intro f
  induction f using induction_on with
  | of m =>
    have : m ∈ closure S := hS.symm ▸ mem_top _
    refine AddSubmonoid.closure_induction (fun m hm => ?_) ?_ ?_ this
    · exact ⟨MvPolynomial.X ⟨m, hm⟩, MvPolynomial.aeval_X _ _⟩
    · exact ⟨1, map_one _⟩
    · rintro m₁ m₂ _ _ ⟨P₁, hP₁⟩ ⟨P₂, hP₂⟩
      exact
        ⟨P₁ * P₂, by
          rw [map_mul, hP₁, hP₂, of_apply, of_apply, of_apply, single_mul_single,
            one_mul]; rfl⟩
  | add f g ihf ihg =>
    rcases ihf with ⟨P, rfl⟩
    rcases ihg with ⟨Q, rfl⟩
    exact ⟨P + Q, map_add _ _ _⟩
  | smul r f ih =>
    rcases ih with ⟨P, rfl⟩
    exact ⟨r • P, map_smul _ _ _⟩

variable [AddMonoid M]

/-- If a set `S` generates an additive monoid `M`, then the image of `M` generates, as algebra,
`R[M]`. -/
/-
**AddMonoidAlgebra.freeAlgebra_lift_of_surjective_of_closure** 是 Mathlib 中的一个定理，
位于命名空间 `AddMonoidAlgebra`。
形式化陈述：freeAlgebra_lift_of_surjective_of_closure [CommSemiring R] {S : Set M} (hS
 : closure S = ⊤) : Function.Surjective (FreeAlgebra.lift R fun s : S => of' R M
 ↑s : FreeAlgebra R S -> R[M])
参数：hS : closure S = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.induction_on`：induction_on [AddMonoid M] {motive : R[M]
 -> Prop} (x : R[M]) (of : forall m, motive (.of R M <| .ofAdd m)) (add : forall
 x y : R[M], motive…
· 使用定理 `AddSubmonoid.mem_top`：∀ {M : Type u_1} [inst : AddZeroClass M] (x : M), 
x ∈ ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddSubmonoid.closure_induction`：∀ {M : Type u_1} [inst : AddZeroClass M]
 {s : Set M} {motive : (x : M) → x ∈ AddSubmonoid.closure s → Prop},   (∀ (x : M
) (h : x ∈ s), motiv…
· 使用定理 `FreeAlgebra.lift_ι_apply`：lift_ι_apply (f : X -> A) (x) : lift R f (ι R 
x) = f x
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `AddMonoidAlgebra.of_apply`：of_apply [AddZeroClass M] (a : Multiplicative
 M) : of R M a = single a.toAdd 1
· 使用定理 `AddMonoidAlgebra.single_mul_single`：∀ {R : Type u_1} {M : Type u_4} [ins
t : Semiring R] [inst_1 : Add M] (m₁ m₂ : M) (r₁ r₂ : R),   AddMonoidAlgebra.sin
gle m₁ r₁ * AddMonoidAlg…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…

--- 原说明 ---
If a set `S` generates an additive monoid `M`, then the image of `M` generates, 
as algebra,
`R[M]`.
-/
theorem freeAlgebra_lift_of_surjective_of_closure [CommSemiring R] {S : Set M}
    (hS : closure S = ⊤) :
    Function.Surjective
      (FreeAlgebra.lift R fun s : S => of' R M ↑s : FreeAlgebra R S → R[M]) := by
  intro f
  induction f using induction_on with
  | of m =>
    have : m ∈ closure S := hS.symm ▸ mem_top _
    refine AddSubmonoid.closure_induction (fun m hm => ?_) ?_ ?_ this
    · exact ⟨FreeAlgebra.ι R ⟨m, hm⟩, FreeAlgebra.lift_ι_apply _ _⟩
    · exact ⟨1, map_one _⟩
    · rintro m₁ m₂ _ _ ⟨P₁, hP₁⟩ ⟨P₂, hP₂⟩
      exact
        ⟨P₁ * P₂, by
          rw [map_mul, hP₁, hP₂, of_apply, of_apply, of_apply, single_mul_single,
            one_mul]; rfl⟩
  | add f g ihf ihg =>
    rcases ihf with ⟨P, rfl⟩
    rcases ihg with ⟨Q, rfl⟩
    exact ⟨P + Q, map_add _ _ _⟩
  | smul r f ih =>
    rcases ih with ⟨P, rfl⟩
    exact ⟨r • P, map_smul _ _ _⟩

variable (R M)

/-- If an additive monoid `M` is finitely generated then `R[M]` is of finite
type. -/
/-
**AddMonoidAlgebra.finiteType_of_fg** 是 Mathlib 中的一个实例，位于命名空间 `AddMonoidAlgebra`
。
形式化陈述：finiteType_of_fg [CommRing R] [h : AddMonoid.FG M] : FiniteType R R[M]
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoid.FG.fg_top`：∀ {M : Type u_3} {inst : AddMonoid M} [self : AddMo
noid.FG M], ⊤.FG
· 使用定理 `Algebra.FiniteType.of_surjective`：of_surjective [FiniteType R A] (f : A 
->ₐ[R] B) (hf : Surjective f) : FiniteType R B
· 使用定理 `Algebra.FiniteType.instFreeAlgebraOfFinite`：∀ {R : Type uR} {S : Type uS
} [inst : CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S] {ι : 
Type u_1}   [Finite ι] [Algebra.…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Module.Finite.finiteType`：∀ {R : Type u_1} (A : Type u_2) [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [hRA : Module.Finite R 
A], Algebra.Fi…
· 使用定理 `AddMonoidAlgebra.freeAlgebra_lift_of_surjective_of_closure`：freeAlgebra_
lift_of_surjective_of_closure [CommSemiring R] {S : Set M} (hS : closure S = ⊤) 
: Function.Surjective (FreeAlgebra.lift R fun s …

--- 原说明 ---
If an additive monoid `M` is finitely generated then `R[M]` is of finite
type.
-/
instance finiteType_of_fg [CommRing R] [h : AddMonoid.FG M] :
    FiniteType R R[M] := by
  obtain ⟨S, hS⟩ := h.fg_top
  exact .of_surjective
      (FreeAlgebra.lift R fun s : (S : Set M) => of' R M ↑s)
      (freeAlgebra_lift_of_surjective_of_closure hS)

variable {R M}

/-- An additive monoid `M` is finitely generated if and only if `R[M]` is of
finite type. -/
/-
**AddMonoidAlgebra.finiteType_iff_fg** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra
`。
形式化陈述：finiteType_iff_fg [CommRing R] [Nontrivial R] : FiniteType R R[M] ↔ AddMon
oid.FG M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.exists_finset_adjoin_eq_top`：exists_finset_adjoin_eq_to
p [h : FiniteType R R[M]] : exists G : Finset M, Algebra.adjoin R (of' R M '' G)
 = ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AddMonoid.fg_def`：∀ {M : Type u_1} [inst : AddMonoid M], AddMonoid.FG M 
↔ ⊤.FG
· 使用定理 `AddSubmonoid.eq_top_iff'`：∀ {M : Type u_1} [inst : AddZeroClass M] (S : 
AddSubmonoid M), S = ⊤ ↔ ∀ (x : M), x ∈ S
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AddMonoidAlgebra.mem_closure_of_mem_span_closure`：mem_closure_of_mem_spa
n_closure [AddMonoid M] [Nontrivial R] {m : M} {s : Set M} (h : of' R M m in Sub
module.span R (Submonoid.closure <| of…
· 使用定理 `Algebra.adjoin_eq_span`：adjoin_eq_span : Subalgebra.toSubmodule (adjoin 
R s) = span R (Submonoid.closure s)

--- 原说明 ---
An additive monoid `M` is finitely generated if and only if `R[M]` is of
finite type.
-/
theorem finiteType_iff_fg [CommRing R] [Nontrivial R] :
    FiniteType R R[M] ↔ AddMonoid.FG M := by
  refine ⟨fun h => ?_, fun h => @AddMonoidAlgebra.finiteType_of_fg _ _ _ _ h⟩
  obtain ⟨S, hS⟩ := @exists_finset_adjoin_eq_top R M _ _ h
  refine AddMonoid.fg_def.2 ⟨S, (eq_top_iff' _).2 fun m => ?_⟩
  have hm : of' R M m ∈ Subalgebra.toSubmodule (adjoin R (of' R M '' ↑S)) := by
    simp only [hS, top_toSubmodule, Submodule.mem_top]
  rw [adjoin_eq_span] at hm
  exact mem_closure_of_mem_span_closure hm

/-- If `R[M]` is of finite type then `M` is finitely generated. -/
/-
**AddMonoidAlgebra.fg_of_finiteType** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`
。
形式化陈述：fg_of_finiteType [CommRing R] [Nontrivial R] [h : FiniteType R R[M]] : Add
Monoid.FG M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AddMonoidAlgebra.finiteType_iff_fg`：finiteType_iff_fg [CommRing R] [Nont
rivial R] : FiniteType R R[M] ↔ AddMonoid.FG M

--- 原说明 ---
If `R[M]` is of finite type then `M` is finitely generated.
-/
theorem fg_of_finiteType [CommRing R] [Nontrivial R] [h : FiniteType R R[M]] :
    AddMonoid.FG M :=
  finiteType_iff_fg.1 h

/-- An additive group `G` is finitely generated if and only if `R[G]` is of
finite type. -/
/-
**AddMonoidAlgebra.finiteType_iff_group_fg** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidA
lgebra`。
形式化陈述：finiteType_iff_group_fg {G : Type*} [AddGroup G] [CommRing R] [Nontrivial 
R] : FiniteType R R[G] ↔ AddGroup.FG G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.finiteType_iff_fg`：finiteType_iff_fg [CommRing R] [Nont
rivial R] : FiniteType R R[M] ↔ AddMonoid.FG M

--- 原说明 ---
An additive group `G` is finitely generated if and only if `R[G]` is of
finite type.
-/
theorem finiteType_iff_group_fg {G : Type*} [AddGroup G] [CommRing R] [Nontrivial R] :
    FiniteType R R[G] ↔ AddGroup.FG G := by
  simpa [AddGroup.fg_iff_addMonoid_fg] using finiteType_iff_fg

end AddMonoidAlgebra

namespace MonoidAlgebra

open Algebra Submonoid Submodule

section Span

section Semiring

variable [CommSemiring R] [Monoid M]

/-- An element of `R[M]` is in the subalgebra generated by its support. -/
/-
**MonoidAlgebra.mem_adjoin_support** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebra`。
形式化陈述：mem_adjoin_support (f : R[M]) : f in adjoin R (of R M '' f.coeff.support)
参数：f : R[M]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `MonoidAlgebra.mem_span_support_coeff`：mem_span_support_coeff [MulOneClas
s G] (f : k[G]) : f in Submodule.span k (of k G '' f.coeff.support)

--- 原说明 ---
An element of `R[M]` is in the subalgebra generated by its support.
-/
theorem mem_adjoin_support (f : R[M]) : f ∈ adjoin R (of R M '' f.coeff.support) :=
  (adjoin R (of R M '' f.coeff.support)).toSubmodule.span_le.2 subset_adjoin
    (mem_span_support_coeff f)

/-- If a set `S` generates, as algebra, `R[M]`, then the set of supports of elements
of `S` generates `R[M]`. -/
/-
**MonoidAlgebra.support_gen_of_gen** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebra`。
形式化陈述：support_gen_of_gen {S : Set R[M]} (hS : Algebra.adjoin R S = ⊤) : Algebra.
adjoin R (⋃ f in S, of R M '' (f.coeff.support : Set M)) = ⊤
参数：hS : Algebra.adjoin R S = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.adjoin_le_iff`：adjoin_le_iff {S : Subalgebra R A} : adjoin R s <
= S ↔ s subseteq S
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion₂`：mem_iUnion₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋃ (i) (j), s i j) ↔ exists i j, x in s i j
· 使用定理 `Algebra.adjoin_mono`：adjoin_mono (H : s subseteq t) : adjoin R s <= adjo
in R t
· 使用定理 `MonoidAlgebra.mem_adjoin_support`：mem_adjoin_support (f : R[M]) : f in a
djoin R (of R M '' f.coeff.support)

--- 原说明 ---
If a set `S` generates, as algebra, `R[M]`, then the set of supports of elements
of `S` generates `R[M]`.
-/
theorem support_gen_of_gen {S : Set R[M]} (hS : Algebra.adjoin R S = ⊤) :
    Algebra.adjoin R (⋃ f ∈ S, of R M '' (f.coeff.support : Set M)) = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← hS, adjoin_le_iff]
  intro f hf
  have hincl : of R M '' f.coeff.support ⊆ ⋃ g ∈ S, of R M '' g.coeff.support :=
    fun s hs ↦ Set.mem_iUnion₂.2 ⟨f, hf, hs⟩
  exact adjoin_mono hincl (mem_adjoin_support f)

/-- If a set `S` generates, as algebra, `R[M]`, then the image of the union of the
supports of elements of `S` generates `R[M]`. -/
/-
**MonoidAlgebra.support_gen_of_gen'** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebra`。
形式化陈述：support_gen_of_gen' {S : Set R[M]} (hS : Algebra.adjoin R S = ⊤) : Algebra
.adjoin R (of R M '' ⋃ f in S, (f.coeff.support : Set M)) = ⊤
参数：hS : Algebra.adjoin R S = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_iUnion`：image_iUnion {f : α -> β} {s : ι -> Set α} : (f '' ⋃ i
, s i) = ⋃ i, f '' s i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MonoidAlgebra.support_gen_of_gen`：support_gen_of_gen {S : Set R[M]} (hS 
: Algebra.adjoin R S = ⊤) : Algebra.adjoin R (⋃ f in S, of R M '' (f.coeff.suppo
rt : Set M)) = ⊤

--- 原说明 ---
If a set `S` generates, as algebra, `R[M]`, then the image of the union of the
supports of elements of `S` generates `R[M]`.
-/
theorem support_gen_of_gen' {S : Set R[M]} (hS : Algebra.adjoin R S = ⊤) :
    Algebra.adjoin R (of R M '' ⋃ f ∈ S, (f.coeff.support : Set M)) = ⊤ := by
  suffices of R M '' ⋃ f ∈ S, f.coeff.support = ⋃ f ∈ S, of R M '' f.coeff.support by
    rw [this]
    exact support_gen_of_gen hS
  simp only [Set.image_iUnion]

end Semiring

section Ring

variable [CommRing R] [Monoid M]

/-- If `R[M]` is of finite type, then there is a `G : Finset M` such that its image
generates, as algebra, `R[M]`. -/
/-
**MonoidAlgebra.exists_finset_adjoin_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlg
ebra`。
形式化陈述：exists_finset_adjoin_eq_top [h : FiniteType R R[M]] : exists G : Finset M,
 Algebra.adjoin R (of R M '' G) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.coe_biUnion`：coe_biUnion : (s.biUnion t : Set β) = ⋃ x in (s : Se
t α), t x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MonoidAlgebra.support_gen_of_gen'`：support_gen_of_gen' {S : Set R[M]} (h
S : Algebra.adjoin R S = ⊤) : Algebra.adjoin R (of R M '' ⋃ f in S, (f.coeff.sup
port : Set M)) = ⊤

--- 原说明 ---
If `R[M]` is of finite type, then there is a `G : Finset M` such that its image
generates, as algebra, `R[M]`.
-/
theorem exists_finset_adjoin_eq_top [h : FiniteType R R[M]] :
    ∃ G : Finset M, Algebra.adjoin R (of R M '' G) = ⊤ := by
  obtain ⟨S, hS⟩ := h
  let : DecidableEq M := Classical.decEq M
  use Finset.biUnion S fun f => f.coeff.support
  have : S.biUnion (fun f => f.coeff.support) = ⋃ f ∈ S, (f.coeff.support : Set M) := by
    simp only [Finset.set_biUnion_coe, Finset.coe_biUnion]
  rw [this]
  exact support_gen_of_gen' hS

end Ring

end Span

/-- If a set `S` generates a monoid `M`, then the image of `M` generates, as algebra,
`R[M]`. -/
/-
**MonoidAlgebra.mvPolynomial_aeval_of_surjective_of_closure** 是 Mathlib 中的一个定理，位
于命名空间 `MonoidAlgebra`。
形式化陈述：mvPolynomial_aeval_of_surjective_of_closure [CommMonoid M] [CommSemiring R
] {S : Set M} (hS : closure S = ⊤) : Function.Surjective (MvPolynomial.aeval fun
 s : S => of R M ↑s : MvPolynomial S R -> R[M])
参数：hS : closure S = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidAlgebra.induction_on`：induction_on {motive : R[M] -> Prop} (x : R[
M]) (of : forall m, motive (.of R M m)) (add : forall x y : R[M], motive x -> mo
tive y -> motive…
· 使用定理 `Submonoid.mem_top`：mem_top (x : M) : x in (⊤ : Submonoid M)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submonoid.closure_induction`：closure_induction {s : Set M} {motive : (x 
: M) -> x in closure s -> Prop} (mem : forall (x) (h : x in s), motive x (subset
_closure h)) (one…
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `MonoidAlgebra.of_apply`：∀ (R : Type u_8) (M : Type u_9) [inst : Semiring
 R] [inst_1 : MulOneClass M] (a : M),   (MonoidAlgebra.of R M) a = MonoidAlgebra
.single a 1
· 使用引理 `MonoidAlgebra.single_mul_single`：single_mul_single (m₁ m₂ : M) (r₁ r₂ : 
R) : single m₁ r₁ * single m₂ r₂ = single (m₁ * m₂) (r₁ * r₂)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…

--- 原说明 ---
If a set `S` generates a monoid `M`, then the image of `M` generates, as algebra
,
`R[M]`.
-/
theorem mvPolynomial_aeval_of_surjective_of_closure [CommMonoid M] [CommSemiring R] {S : Set M}
    (hS : closure S = ⊤) :
    Function.Surjective
      (MvPolynomial.aeval fun s : S => of R M ↑s : MvPolynomial S R → R[M]) := by
  intro f
  induction f using induction_on with
  | of m =>
    have : m ∈ closure S := hS.symm ▸ mem_top _
    refine Submonoid.closure_induction (fun m hm => ?_) ?_ ?_ this
    · exact ⟨MvPolynomial.X ⟨m, hm⟩, MvPolynomial.aeval_X _ _⟩
    · exact ⟨1, map_one _⟩
    · rintro m₁ m₂ _ _ ⟨P₁, hP₁⟩ ⟨P₂, hP₂⟩
      exact
        ⟨P₁ * P₂, by
          rw [map_mul, hP₁, hP₂, of_apply, of_apply, of_apply, single_mul_single, one_mul]⟩
  | add f g ihf ihg =>
    rcases ihf with ⟨P, rfl⟩; rcases ihg with ⟨Q, rfl⟩
    exact ⟨P + Q, map_add _ _ _⟩
  | smul r f ih =>
    rcases ih with ⟨P, rfl⟩
    exact ⟨r • P, map_smul _ _ _⟩


variable [Monoid M]

/-- If a set `S` generates an additive monoid `M`, then the image of `M` generates, as algebra,
`R[M]`. -/
/-
**MonoidAlgebra.freeAlgebra_lift_of_surjective_of_closure** 是 Mathlib 中的一个定理，位于命
名空间 `MonoidAlgebra`。
形式化陈述：freeAlgebra_lift_of_surjective_of_closure [CommSemiring R] {S : Set M} (hS
 : closure S = ⊤) : Function.Surjective (FreeAlgebra.lift R fun s : S => of R M 
↑s : FreeAlgebra R S -> R[M])
参数：hS : closure S = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidAlgebra.induction_on`：induction_on {motive : R[M] -> Prop} (x : R[
M]) (of : forall m, motive (.of R M m)) (add : forall x y : R[M], motive x -> mo
tive y -> motive…
· 使用定理 `Submonoid.mem_top`：mem_top (x : M) : x in (⊤ : Submonoid M)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submonoid.closure_induction`：closure_induction {s : Set M} {motive : (x 
: M) -> x in closure s -> Prop} (mem : forall (x) (h : x in s), motive x (subset
_closure h)) (one…
· 使用定理 `FreeAlgebra.lift_ι_apply`：lift_ι_apply (f : X -> A) (x) : lift R f (ι R 
x) = f x
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `MonoidAlgebra.of_apply`：∀ (R : Type u_8) (M : Type u_9) [inst : Semiring
 R] [inst_1 : MulOneClass M] (a : M),   (MonoidAlgebra.of R M) a = MonoidAlgebra
.single a 1
· 使用引理 `MonoidAlgebra.single_mul_single`：single_mul_single (m₁ m₂ : M) (r₁ r₂ : 
R) : single m₁ r₁ * single m₂ r₂ = single (m₁ * m₂) (r₁ * r₂)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…

--- 原说明 ---
If a set `S` generates an additive monoid `M`, then the image of `M` generates, 
as algebra,
`R[M]`.
-/
theorem freeAlgebra_lift_of_surjective_of_closure [CommSemiring R] {S : Set M}
    (hS : closure S = ⊤) :
    Function.Surjective
      (FreeAlgebra.lift R fun s : S => of R M ↑s : FreeAlgebra R S → R[M]) := by
  intro f
  induction f using induction_on with
  | of m =>
    have : m ∈ closure S := hS.symm ▸ mem_top _
    refine Submonoid.closure_induction (fun m hm => ?_) ?_ ?_ this
    · exact ⟨FreeAlgebra.ι R ⟨m, hm⟩, FreeAlgebra.lift_ι_apply _ _⟩
    · exact ⟨1, map_one _⟩
    · rintro m₁ m₂ _ _ ⟨P₁, hP₁⟩ ⟨P₂, hP₂⟩
      exact
        ⟨P₁ * P₂, by
          rw [map_mul, hP₁, hP₂, of_apply, of_apply, of_apply, single_mul_single, one_mul]⟩
  | add f g ihf ihg =>
    rcases ihf with ⟨P, rfl⟩
    rcases ihg with ⟨Q, rfl⟩
    exact ⟨P + Q, map_add _ _ _⟩
  | smul r f ih =>
    rcases ih with ⟨P, rfl⟩
    exact ⟨r • P, map_smul _ _ _⟩

/-- If a monoid `M` is finitely generated then `R[M]` is of finite type. -/
/-
**MonoidAlgebra.finiteType_of_fg** 是 Mathlib 中的一个实例，位于命名空间 `MonoidAlgebra`。
形式化陈述：finiteType_of_fg [CommRing R] [Monoid.FG M] : FiniteType R R[M]
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FiniteType.equiv`：equiv (hRA : FiniteType R A) (e : A ≃ₐ[R] B) :
 FiniteType R B

--- 原说明 ---
If a monoid `M` is finitely generated then `R[M]` is of finite type.
-/
instance finiteType_of_fg [CommRing R] [Monoid.FG M] : FiniteType R R[M] :=
  (AddMonoidAlgebra.finiteType_of_fg R (Additive M)).equiv (toAdditiveAlgEquiv R R M).symm

/-- A monoid `M` is finitely generated if and only if `R[M]` is of finite type. -/
/-
**MonoidAlgebra.finiteType_iff_fg** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebra`。
形式化陈述：finiteType_iff_fg [CommRing R] [Nontrivial R] : FiniteType R R[M] ↔ Monoid
.FG M where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Monoid.fg_iff_add_fg`：Monoid.fg_iff_add_fg : Monoid.FG M ↔ AddMonoid.FG 
(Additive M) where mp _
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AddMonoidAlgebra.finiteType_iff_fg`：finiteType_iff_fg [CommRing R] [Nont
rivial R] : FiniteType R R[M] ↔ AddMonoid.FG M
· 使用定理 `Algebra.FiniteType.equiv`：equiv (hRA : FiniteType R A) (e : A ≃ₐ[R] B) :
 FiniteType R B

--- 原说明 ---
A monoid `M` is finitely generated if and only if `R[M]` is of finite type.
-/
theorem finiteType_iff_fg [CommRing R] [Nontrivial R] : FiniteType R R[M] ↔ Monoid.FG M where
  mp h := Monoid.fg_iff_add_fg.2 <|
    AddMonoidAlgebra.finiteType_iff_fg.1 <| h.equiv <| toAdditiveAlgEquiv R R M
  mpr _ := inferInstance

/-- If `R[M]` is of finite type then `M` is finitely generated. -/
/-
**MonoidAlgebra.fg_of_finiteType** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebra`。
形式化陈述：fg_of_finiteType [CommRing R] [Nontrivial R] [h : FiniteType R R[M]] : Mon
oid.FG M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MonoidAlgebra.finiteType_iff_fg`：finiteType_iff_fg [CommRing R] [Nontriv
ial R] : FiniteType R R[M] ↔ Monoid.FG M where mp h

--- 原说明 ---
If `R[M]` is of finite type then `M` is finitely generated.
-/
theorem fg_of_finiteType [CommRing R] [Nontrivial R] [h : FiniteType R R[M]] :
    Monoid.FG M :=
  finiteType_iff_fg.1 h

/-- A group `G` is finitely generated if and only if `R[G]` is of finite type. -/
/-
**MonoidAlgebra.finiteType_iff_group_fg** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebra
`。
形式化陈述：finiteType_iff_group_fg {G : Type*} [Group G] [CommRing R] [Nontrivial R] 
: FiniteType R R[G] ↔ Group.FG G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidAlgebra.finiteType_iff_fg`：finiteType_iff_fg [CommRing R] [Nontriv
ial R] : FiniteType R R[M] ↔ Monoid.FG M where mp h

--- 原说明 ---
A group `G` is finitely generated if and only if `R[G]` is of finite type.
-/
theorem finiteType_iff_group_fg {G : Type*} [Group G] [CommRing R] [Nontrivial R] :
    FiniteType R R[G] ↔ Group.FG G := by
  simpa [Group.fg_iff_monoid_fg] using finiteType_iff_fg

end MonoidAlgebra

end MonoidAlgebra

section Orzech

open Submodule Module Module.Finite in
/--
Any commutative ring `R` satisfies the `OrzechProperty`, that is, for any finitely generated
`R`-module `M`, any surjective homomorphism `f : N →ₗ[R] M` from a submodule `N` of `M` to `M`
is injective.

This is a consequence of Noetherian case
(`IsNoetherian.injective_of_surjective_of_injective`), which requires that `M` is a
Noetherian module, but allows `R` to be non-commutative. The reduction of this result to
Noetherian case is adapted from <https://math.stackexchange.com/a/1066110>:
suppose `{ m_j }` is a finite set of generators of `M`, for any `n : N` one can write
`i n = ∑ j, b_j * m_j` for `{ b_j }` in `R`, here `i : N →ₗ[R] M` is the standard inclusion.
We can choose `{ n_j }` which are preimages of `{ m_j }` under `f`, and can choose
`{ c_jl }` in `R` such that `i n_j = ∑ l, c_jl * m_l` for each `j`.
Now let `A` be the subring of `R` generated by `{ b_j }` and `{ c_jl }`, then it is
Noetherian. Let `N'` be the `A`-submodule of `N` generated by `n` and `{ n_j }`,
`M'` be the `A`-submodule of `M` generated by `{ m_j }`,
then it's easy to see that `i` and `f` restrict to `N' →ₗ[A] M'`,
and the restricted version of `f` is surjective, hence by Noetherian case,
it is also injective, in particular, if `f n = 0`, then `n = 0`.

See also Orzech's original paper: *Onto endomorphisms are isomorphisms* [orzech1971].

This implies that nontrivial commutative rings satisfy the strong rank condition:
see `strongRankCondition_of_orzechProperty` in `Mathlib.LinearAlgebra.InvariantBasisNumber`.
A shortcut instance `commRing_strongRankCondition` is also provided.
-/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any commutative ring `R` satisfies the `OrzechProperty`, that is, for any finite
ly generated
`R`-module `M`, any surjective homomorphism `f : N →ₗ[R] M` from a submodule `N`
 of `M` to `M`
is injective.

This is a consequence of Noetherian case
(`IsNoetherian.injective_of_surjective_of_injective`), which requires that `M` i
s a
Noetherian module, but allows `R` to be non-commutative. The reduction of this r
esult to
Noetherian case is adapted from <https://math.stackexchange.com/a/1066110>:
suppose `{ m_j }` is a finite set of generators of `M`, for any `n : N` one can 
write
`i n = ∑ j, b_j * m_j` for `{ b_j }` in `R`, here `i : N →ₗ[R] M` is the standar
d inclusion.
We can choose `{ n_j }` which are preimages of `{ m_j }` under `f`, and can choo
se
`{ c_jl }` in `R` such that `i n_j = ∑ l, c_jl * m_l` for each `j`.
Now let `A` be the subring of `R` generated by `{ b_j }` and `{ c_jl }`, then it
 is
Noetherian. Let `N'` be the `A`-submodule of `N` generated by `n` and `{ n_j }`,
`M'` be the `A`-submodule of `M` generated by `{ m_j }`,
then it's easy to see that `i` and `f` restrict to `N' →ₗ[A] M'`,
and the restricted version of `f` is surjective, hence by Noetherian case,
it is also injective, in particular, if `f n = 0`, then `n = 0`.

See also Orzech's original paper: *Onto endomorphisms are isomorphisms* [orzech1
971].

This implies that nontrivial commutative rings satisfy the strong rank condition
:
see `strongRankCondition_of_orzechProperty` in `Mathlib.LinearAlgebra.InvariantB
asisNumber`.
A shortcut instance `commRing_strongRankCondition` is also provided.
-/
instance (priority := 100) CommRing.orzechProperty
    (R : Type*) [CommRing R] : OrzechProperty R := by
  refine ⟨fun {M} _ _ _ {N} f hf ↦ ?_⟩
  let := addCommMonoidToAddCommGroup R (M := M)
  let := addCommMonoidToAddCommGroup R (M := N)
  let i := N.subtype
  let hi : Function.Injective i := N.injective_subtype
  refine LinearMap.ker_eq_bot.1 <| LinearMap.ker_eq_bot'.2 fun n hn ↦ ?_
  obtain ⟨k, mj, hmj⟩ := exists_fin (R := R) (M := M)
  rw [← surjective_piEquiv_apply_iff] at hmj
  obtain ⟨b, hb⟩ := hmj (i n)
  choose nj hnj using fun j ↦ hf (mj j)
  choose c hc using fun j ↦ hmj (i (nj j))
  let A := Subring.closure (Set.range b ∪ Set.range c.uncurry)
  let N' := span A ({n} ∪ Set.range nj)
  let M' := span A (Set.range mj)
  have : IsNoetherianRing A := is_noetherian_subring_closure _
    (.union (Set.finite_range _) (Set.finite_range _))
  have : Module.Finite A M' := span_of_finite A (Set.finite_range _)
  refine congr($((LinearMap.ker_eq_bot'.1 <| LinearMap.ker_eq_bot.2 <|
    IsNoetherian.injective_of_surjective_of_injective
      ((i.restrictScalars A).restrict fun x hx ↦ ?_ : N' →ₗ[A] M')
      ((f.restrictScalars A).restrict fun x hx ↦ ?_ : N' →ₗ[A] M')
      (fun _ _ h ↦ injective_subtype _ (hi congr(($h).1)))
      fun ⟨x, hx⟩ ↦ ?_) ⟨n, (subset_span (by simp))⟩ (Subtype.val_injective hn)).1)
  · induction hx using span_induction with
    | mem x hx =>
      change i x ∈ M'
      simp only [Set.singleton_union, Set.mem_insert_iff, Set.mem_range] at hx
      rcases hx with hx | ⟨j, rfl⟩
      · rw [hx, ← hb, piEquiv_apply_apply]
        refine Submodule.sum_mem _ fun j _ ↦ ?_
        let b' : A := ⟨b j, Subring.subset_closure (by simp)⟩
        rw [show b j • mj j = b' • mj j from rfl]
        exact smul_mem _ _ (subset_span (by simp))
      · rw [← hc, piEquiv_apply_apply]
        refine Submodule.sum_mem _ fun j' _ ↦ ?_
        let c' : A := ⟨c j j', Subring.subset_closure
          (by simp [show ∃ a b, c a b = c j j' from ⟨j, j', rfl⟩])⟩
        rw [show c j j' • mj j' = c' • mj j' from rfl]
        exact smul_mem _ _ (subset_span (by simp))
    | zero => simp
    | add x _ y _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact smul_mem _ _ hx
  · induction hx using span_induction with
    | mem x hx =>
      change f x ∈ M'
      simp only [Set.singleton_union, Set.mem_insert_iff, Set.mem_range] at hx
      rcases hx with hx | ⟨j, rfl⟩
      · rw [hx, hn]; exact zero_mem _
      · exact subset_span (by simp [hnj])
    | zero => simp
    | add x _ y _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact smul_mem _ _ hx
  suffices x ∈ LinearMap.range ((f.restrictScalars A).domRestrict N') by
    obtain ⟨a, ha⟩ := this
    exact ⟨a, Subtype.val_injective ha⟩
  induction hx using span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact ⟨⟨nj j, subset_span (by simp)⟩, hnj j⟩
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul a x _ hx => exact smul_mem _ a hx

end Orzech

