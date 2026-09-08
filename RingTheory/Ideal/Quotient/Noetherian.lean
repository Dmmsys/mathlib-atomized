/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Noetherian quotient rings and quotient modules
-/

public section

/-
**Ideal.Quotient.isNoetherianRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Ideal.Quotient.isNoetherianRing {R : Type*} [CommRing R] [IsNoetherianRing
 R] (I : Ideal R) : IsNoetherianRing (R ⧸ I)
参数：I : Ideal R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isNoetherianRing_iff`：isNoetherianRing_iff {R} [Semiring R] : IsNoetheri
anRing R ↔ IsNoetherian R R
· 使用定理 `isNoetherian_of_tower`：isNoetherian_of_tower (R) {S M} [Semiring R] [Sem
iring S] [AddCommMonoid M] [SMul R S] [Module S M] [Module R M] [IsScalarTower R
 S M] (h : …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
instance Ideal.Quotient.isNoetherianRing {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) : IsNoetherianRing (R ⧸ I) :=
  isNoetherianRing_iff.mpr <| isNoetherian_of_tower R <| inferInstance
