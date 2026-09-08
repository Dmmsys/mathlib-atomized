/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Yongle Hu
-/
module

public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.Ideal.Over

/-!
# Finiteness of quotient modules
-/

public section

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable (P : Ideal B) (p : Ideal A) [P.LiesOver p]

/-- `B ⧸ P` is a finite `A ⧸ p`-module if `B` is a finite `A`-module. -/
/-
**module_finite_of_liesOver** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：module_finite_of_liesOver [Module.Finite A B] : Module.Finite (A ⧸ p) (B ⧸
 P)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.of_restrictScalars_finite`：of_restrictScalars_finite (R A 
M : Type*) [Semiring R] [Semiring A] [AddCommMonoid M] [Module R M] [Module A M]
 [SMul R A] [IsScalarTower R …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
`B ⧸ P` is a finite `A ⧸ p`-module if `B` is a finite `A`-module.
-/
instance module_finite_of_liesOver [Module.Finite A B] : Module.Finite (A ⧸ p) (B ⧸ P) :=
  Module.Finite.of_restrictScalars_finite A (A ⧸ p) (B ⧸ P)
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [Module.Finite A B] : Module.Finite (A ⧸ P.under A) (B ⧸ P) := inferInstance

/-- `B ⧸ P` is a finitely generated `A ⧸ p`-algebra if `B` is a finitely generated `A`-algebra. -/
/-
**algebra_finiteType_of_liesOver** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：algebra_finiteType_of_liesOver [Algebra.FiniteType A B] : Algebra.FiniteTy
pe (A ⧸ p) (B ⧸ P)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FiniteType.of_restrictScalars_finiteType`：of_restrictScalars_fin
iteType [Algebra S A] [IsScalarTower R S A] [hA : FiniteType R A] : FiniteType S
 A

--- 原说明 ---
`B ⧸ P` is a finitely generated `A ⧸ p`-algebra if `B` is a finitely generated `
A`-algebra.
-/
instance algebra_finiteType_of_liesOver [Algebra.FiniteType A B] :
    Algebra.FiniteType (A ⧸ p) (B ⧸ P) :=
  Algebra.FiniteType.of_restrictScalars_finiteType A (A ⧸ p) (B ⧸ P)

/-- `B ⧸ P` is a Noetherian `A ⧸ p`-module if `B` is a Noetherian `A`-module. -/
/-
**isNoetherian_of_liesOver** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isNoetherian_of_liesOver [IsNoetherian A B] : IsNoetherian (A ⧸ p) (B ⧸ P)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `isNoetherian_of_tower`：isNoetherian_of_tower (R) {S M} [Semiring R] [Sem
iring S] [AddCommMonoid M] [SMul R S] [Module S M] [Module R M] [IsScalarTower R
 S M] (h : …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
`B ⧸ P` is a Noetherian `A ⧸ p`-module if `B` is a Noetherian `A`-module.
-/
instance isNoetherian_of_liesOver [IsNoetherian A B] : IsNoetherian (A ⧸ p) (B ⧸ P) :=
  isNoetherian_of_tower A inferInstance
/-
**QuotientMapQuotient.isNoetherian** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：QuotientMapQuotient.isNoetherian [IsNoetherian A B] : IsNoetherian (A ⧸ p)
 (B ⧸ p.map (algebraMap A B))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `isNoetherian_of_tower`：isNoetherian_of_tower (R) {S M} [Semiring R] [Sem
iring S] [AddCommMonoid M] [SMul R S] [Module S M] [Module R M] [IsScalarTower R
 S M] (h : …
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.Quotient.tower_quotient_map_quotient`：∀ {R : Type u_1} [inst : Com
mRing R] {S : Type u_2} [inst_1 : CommRing S] {p : Ideal R} [inst_2 : Algebra R 
S],   IsScalarTower R (R ⧸ p) (S…
· 使用定理 `isNoetherian_of_surjective`：isNoetherian_of_surjective {σ : R ->+* S} [R
ingHomSurjective σ] (f : M ->ₛₗ[σ] P) (hf : LinearMap.range f = ⊤) [IsNoetherian
 R M] : IsNoethe…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
-/
instance QuotientMapQuotient.isNoetherian [IsNoetherian A B] :
    IsNoetherian (A ⧸ p) (B ⧸ p.map (algebraMap A B)) :=
  isNoetherian_of_tower A <|
    isNoetherian_of_surjective (Ideal.Quotient.mkₐ A _).toLinearMap <|
      LinearMap.range_eq_top.mpr Ideal.Quotient.mk_surjective
