/-
Copyright (c) 2025 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Yunzhou Xie
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Morita equivalence

Two `R`-algebras `A` and `B` are Morita equivalent if the categories of modules over `A` and
`B` are `R`-linearly equivalent. In this file, we prove that Morita equivalence is an equivalence
relation and that isomorphic algebras are Morita equivalent.

## Main definitions

- `MoritaEquivalence R A B`: a structure containing an `R`-linear equivalence of categories between
  the module categories of `A` and `B`.
- `IsMoritaEquivalent R A B`: a predicate asserting that `R`-algebras `A` and `B` are Morita
  equivalent.

## TODO

- For any ring `R`, `R` and `Matₙ(R)` are Morita equivalent.
- Morita equivalence in terms of projective generators.
- Morita equivalence in terms of full idempotents.
- Morita equivalence in terms of existence of an invertible bimodule.
- If `R ≈ S`, then `R` is simple iff `S` is simple.

## References

* [Nathan Jacobson, *Basic Algebra II*][jacobson1989]

## Tags

Morita Equivalence, Category Theory, Noncommutative Ring, Module Theory

-/

@[expose] public section

universe u₀ u₁ u₂ u₃

open CategoryTheory

variable (R : Type u₀) [CommSemiring R]

open scoped ModuleCat.Algebra

/--
Definition of `MoritaEquivalence` / `MoritaEquivalence` 的定义

English:
structure MoritaEquivalence
  axioms and operations (2):
    - eqv : ModuleCat.{max u₁ u₂} A ≌ ModuleCat.{max u₁ u₂} B
    - linear : eqv.functor.Linear R  [default: by infer_instance]

中文:
结构 MoritaEquivalence
  公理与运算 (2 个):
    - eqv : ModuleCat.{max u₁ u₂} A ≌ ModuleCat.{max u₁ u₂} B
    - linear : eqv.functor.Linear R  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
structure MoritaEquivalence
    (A : Type u₁) [Ring A] [Algebra R A]
    (B : Type u₂) [Ring B] [Algebra R B] where
  /-- The underlying equivalence of categories -/
  eqv : ModuleCat.{max u₁ u₂} A ≌ ModuleCat.{max u₁ u₂} B
  linear : eqv.functor.Linear R := by infer_instance

namespace MoritaEquivalence

attribute [instance] MoritaEquivalence.linear

instance {A : Type u₁} [Ring A] [Algebra R A] {B : Type u₂} [Ring B] [Algebra R B]
    (e : MoritaEquivalence R A B) : e.eqv.functor.Additive :=
  e.eqv.functor.additive_of_preserves_binary_products

/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: (A : Type u₁) [Ring A] [Algebra R A]
  body: CategoryTheory.Equivalence.refl
  linear := Functor.instLinearId

中文:
定义 refl
  签名: (A : 类型u₁) [Ring A] [Algebra R A]
  定义体: CategoryTheory.Equivalence.refl
  linear := Functor.instLinearId

Depends on / 依赖: CategoryTheory, CategoryTheory.Equivalence.refl, Equivalence
-/
def refl (A : Type u₁) [Ring A] [Algebra R A] : MoritaEquivalence R A A where
  eqv := CategoryTheory.Equivalence.refl
  linear := Functor.instLinearId

/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: {A : Type u₁} [Ring A] [Algebra R A] {B : Type u₂} [Ring B] [Algebra R B]
  body: e.eqv.symm
  linear := e.eqv.inverseLinear R

中文:
定义 symm
  签名: {A : 类型u₁} [Ring A] [Algebra R A] {B : 类型u₂} [Ring B] [Algebra R B]
  定义体: e.eqv.symm
  linear := e.eqv.inverseLinear R

Depends on / 依赖: e.eqv.symm
-/
def symm {A : Type u₁} [Ring A] [Algebra R A] {B : Type u₂} [Ring B] [Algebra R B]
    (e : MoritaEquivalence R A B) : MoritaEquivalence R B A where
  eqv := e.eqv.symm
  linear := e.eqv.inverseLinear R

-- TODO: We have restricted all the rings to the same universe here because of the complication
-- `max u₁ u₂`, `max u₂ u₃` vs `max u₁ u₃`. But once we proved the definition of Morita
-- equivalence is equivalent to the existence of a full idempotent element, we can remove this
-- restriction in the universe.
-- Or alternatively, @alreadydone has sketched an argument on how the universe restriction can be
-- removed via a categorical argument,
-- see [here](https://github.com/leanprover-community/mathlib4/pull/20640#discussion_r1912189931)
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: {A B C : Type u₁}
  body: e.eqv.trans e'.eqv
  linear := e.eqv.functor.instLinearComp e'.eqv.functor

中文:
定义 trans
  签名: {A B C : 类型u₁}
  定义体: e.eqv.trans e'.eqv
  linear := e.eqv.functor.instLinearComp e'.eqv.functor

Depends on / 依赖: e.eqv.trans
-/
def trans {A B C : Type u₁}
    [Ring A] [Algebra R A] [Ring B] [Algebra R B] [Ring C] [Algebra R C]
    (e : MoritaEquivalence R A B) (e' : MoritaEquivalence R B C) :
    MoritaEquivalence R A C where
  eqv := e.eqv.trans e'.eqv
  linear := e.eqv.functor.instLinearComp e'.eqv.functor

variable {R} in
/--
Definition of `ofAlgEquiv` / `ofAlgEquiv` 的定义

English:
definition ofAlgEquiv
  signature: {A : Type u₁} {B : Type u₂}
  body: ModuleCat.restrictScalarsEquivalenceOfRingEquiv f.symm.toRingEquiv
  linear := ModuleCat.Algebra.restrictScalarsEquivalenceOfRingEquiv_linear f.symm

中文:
定义 ofAlgEquiv
  签名: {A : 类型u₁} {B : 类型u₂}
  定义体: ModuleCat.restrictScalarsEquivalenceOfRingEquiv f.symm.toRingEquiv
  linear := ModuleCat.Algebra.restrictScalarsEquivalenceOfRingEquiv_linear f.symm

Depends on / 依赖: ModuleCat, ModuleCat.restrictScalarsEquivalenceOfRingEquiv, f.symm.toRingEquiv, restrictScalarsEquivalenceOfRingEquiv, toRingEquiv
-/
noncomputable def ofAlgEquiv {A : Type u₁} {B : Type u₂}
    [Ring A] [Algebra R A] [Ring B] [Algebra R B] (f : A ≃ₐ[R] B) :
    MoritaEquivalence R A B where
  eqv := ModuleCat.restrictScalarsEquivalenceOfRingEquiv f.symm.toRingEquiv
  linear := ModuleCat.Algebra.restrictScalarsEquivalenceOfRingEquiv_linear f.symm

end MoritaEquivalence

/--
Definition of `IsMoritaEquivalent` / `IsMoritaEquivalent` 的定义

English:
structure IsMoritaEquivalent
  axioms and operations (1):
    - cond : Nonempty MoritaEquivalence R A B

中文:
结构 IsMoritaEquivalent
  公理与运算 (1 个):
    - cond : Nonempty MoritaEquivalence R A B
-/
structure IsMoritaEquivalent
    (A : Type u₁) [Ring A] [Algebra R A]
    (B : Type u₂) [Ring B] [Algebra R B] : Prop where
cond : Nonempty MoritaEquivalence R A B

namespace IsMoritaEquivalent

/--
lemma `refl` / 引理 `refl`

English:
lemma refl
  given: (A : Type u₁) [Ring A] [Algebra R A]
  statement: IsMoritaEquivalent R A A where
  proof: ⟨.refl R A⟩

中文:
引理 refl
  条件: (A : 类型u₁) [Ring A] [Algebra R A]
  结论: IsMoritaEquivalent R A A where
  证明: ⟨.refl R A⟩
-/
lemma refl (A : Type u₁) [Ring A] [Algebra R A] : IsMoritaEquivalent R A A where
  cond := ⟨.refl R A⟩

/--
lemma `symm` / 引理 `symm`

English:
lemma symm
  statement: {A : Type u₁} [Ring A] [Algebra R A] {B : Type u₂} [Ring B] [Algebra R B]
  proof: h.cond.map .symm R

中文:
引理 symm
  结论: {A : 类型u₁} [Ring A] [Algebra R A] {B : 类型u₂} [Ring B] [Algebra R B]
  证明: h.cond.map .symm R

Depends on / 依赖: h.cond.map
-/
lemma symm {A : Type u₁} [Ring A] [Algebra R A] {B : Type u₂} [Ring B] [Algebra R B]
    (h : IsMoritaEquivalent R A B) : IsMoritaEquivalent R B A where
cond := h.cond.map .symm R

/--
lemma `trans` / 引理 `trans`

English:
lemma trans
  statement: {A B C : Type u₁} [Ring A] [Ring B] [Ring C] [Algebra R A] [Algebra R B] [Algebra R C]
  proof: Nonempty.map2 (.trans R) h.cond h'.cond

中文:
引理 trans
  结论: {A B C : 类型u₁} [Ring A] [Ring B] [Ring C] [Algebra R A] [Algebra R B] [Algebra R C]
  证明: Nonempty.map2 (.trans R) h.cond h'.cond

Depends on / 依赖: Nonempty, Nonempty.map2, h.cond
-/
lemma trans {A B C : Type u₁} [Ring A] [Ring B] [Ring C] [Algebra R A] [Algebra R B] [Algebra R C]
    (h : IsMoritaEquivalent R A B) (h' : IsMoritaEquivalent R B C) :
    IsMoritaEquivalent R A C where
  cond := Nonempty.map2 (.trans R) h.cond h'.cond

/--
lemma `of_algEquiv` / 引理 `of_algEquiv`

English:
lemma of_algEquiv
  statement: {A : Type u₁} [Ring A] [Algebra R A] {B : Type u₂} [Ring B] [Algebra R B]
  proof: ⟨.ofAlgEquiv f⟩

中文:
引理 of_algEquiv
  结论: {A : 类型u₁} [Ring A] [Algebra R A] {B : 类型u₂} [Ring B] [Algebra R B]
  证明: ⟨.ofAlgEquiv f⟩

Depends on / 依赖: ofAlgEquiv
-/
lemma of_algEquiv {A : Type u₁} [Ring A] [Algebra R A] {B : Type u₂} [Ring B] [Algebra R B]
    (f : A ≃ₐ[R] B) : IsMoritaEquivalent R A B where
  cond := ⟨.ofAlgEquiv f⟩

end IsMoritaEquivalent
