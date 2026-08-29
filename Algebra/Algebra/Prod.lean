/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Module.Prod

/-!
# The R-algebra structure on products of R-algebras

The R-algebra structure on `(i : I) → A i` when each `A i` is an R-algebra.

## Main definitions

* `Prod.algebra`
* `AlgHom.fst`
* `AlgHom.snd`
* `AlgHom.prod`
* `AlgEquiv.prodUnique` and `AlgEquiv.uniqueProd`
-/

@[expose] public section


variable {R A B C : Type*}
variable [CommSemiring R]
variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

namespace Prod

variable (R A B)

open Algebra

/--
Instance `algebra` / 实例 `algebra`

English:
instance algebra
  signature: : Algebra R (A × B) where
  body: RingHom.prod (algebraMap R A) (algebraMap R B)
  commutes' := by
    rintro r ⟨a, b⟩
    dsimp
    rw [commutes r a]; rw [commutes r b]
  smul_def' := by
    rintro r ⟨a, b⟩
    dsimp
    rw [Algebra.smul_def r a]; rw [Algebra.smul_def r b]

中文:
实例 algebra
  签名: : Algebra R (A × B) where
  定义体: RingHom.prod (algebraMap R A) (algebraMap R B)
  commutes' := by
    rintro r ⟨a, b⟩
    dsimp
    rw [commutes r a]; rw [commutes r b]
  smul_def' := by
    rintro r ⟨a, b⟩
    dsimp
    rw [Algebra.smul_def r a]; rw [Algebra.smul_def r b]

Depends on / 依赖: RingHom, RingHom.prod, algebraMap
-/
instance algebra : Algebra R (A × B) where
  algebraMap := RingHom.prod (algebraMap R A) (algebraMap R B)
  commutes' := by
    rintro r ⟨a, b⟩
    dsimp
    rw [commutes r a]; rw [commutes r b]
  smul_def' := by
    rintro r ⟨a, b⟩
    dsimp
    rw [Algebra.smul_def r a]; rw [Algebra.smul_def r b]

variable {R A B}

@[simp]
/--
theorem `algebraMap_apply` / 定理 `algebraMap_apply`

English:
theorem algebraMap_apply
  given: (r : R)
  statement: algebraMap R (A × B) r = (algebraMap R A r, algebraMap R B r)
  proof: rfl

中文:
定理 algebraMap_apply
  条件: (r : R)
  结论: algebraMap R (A × B) r = (algebraMap R A r, algebraMap R B r)
  证明: rfl
-/
theorem algebraMap_apply (r : R) : algebraMap R (A × B) r = (algebraMap R A r, algebraMap R B r) :=
  rfl

end Prod

namespace AlgHom

variable (R A B)

/--
Definition of `fst` / `fst` 的定义

English:
definition fst
  signature: : A × B ->ₐ[R] A
  body: { RingHom.fst A B with commutes' := fun _r => rfl }

中文:
定义 fst
  签名: : A × B ->ₐ[R] A
  定义体: { RingHom.fst A B with commutes' := fun _r => rfl }

Depends on / 依赖: RingHom, RingHom.fst, commutes
-/
def fst : A × B ->ₐ[R] A :=
  { RingHom.fst A B with commutes' := fun _r => rfl }

/--
Definition of `snd` / `snd` 的定义

English:
definition snd
  signature: : A × B ->ₐ[R] B
  body: { RingHom.snd A B with commutes' := fun _r => rfl }

中文:
定义 snd
  签名: : A × B ->ₐ[R] B
  定义体: { RingHom.snd A B with commutes' := fun _r => rfl }

Depends on / 依赖: RingHom, RingHom.snd, commutes
-/
def snd : A × B ->ₐ[R] B :=
  { RingHom.snd A B with commutes' := fun _r => rfl }

variable {A B}

@[simp]
/--
theorem `fst_apply` / 定理 `fst_apply`

English:
theorem fst_apply
  given: (a)
  statement: fst R A B a = a.1
  proof: rfl

@[simp]

中文:
定理 fst_apply
  条件: (a)
  结论: fst R A B a = a.1
  证明: rfl

@[simp]
-/
theorem fst_apply (a) : fst R A B a = a.1 := rfl

@[simp]
/--
theorem `snd_apply` / 定理 `snd_apply`

English:
theorem snd_apply
  given: (a)
  statement: snd R A B a = a.2
  proof: rfl

中文:
定理 snd_apply
  条件: (a)
  结论: snd R A B a = a.2
  证明: rfl
-/
theorem snd_apply (a) : snd R A B a = a.2 := rfl

variable {R}

/-- The `Function.prod` of two morphisms is a morphism. -/
@[simps!]
/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (f : A ->ₐ[R] B) (g : A ->ₐ[R] C)
  body: { f.toRingHom.prod g.toRingHom with
    commutes' := fun r => by
      simp only [toRingHom_eq_coe, RingHom.toFun_eq_coe, RingHom.prod_apply, coe_toRingHom,
        commutes, Prod.algebraMap_apply] }

中文:
定义 prod
  签名: (f : A ->ₐ[R] B) (g : A ->ₐ[R] C)
  定义体: { f.toRingHom.prod g.toRingHom with
    commutes' := fun r => by
      simp only [toRingHom_eq_coe, RingHom.toFun_eq_coe, RingHom.prod_apply, coe_toRingHom,
        commutes, Prod.algebraMap_apply] }

Depends on / 依赖: Prod.algebraMap_apply, RingHom, RingHom.prod_apply, RingHom.toFun_eq_coe, algebraMap_apply, coe_toRingHom, commutes, f.toRingHom.prod, g.toRingHom, prod_apply, toFun_eq_coe, toRingHom, toRingHom_eq_coe
-/
def prod (f : A ->ₐ[R] B) (g : A ->ₐ[R] C) : A ->ₐ[R] B × C :=
  { f.toRingHom.prod g.toRingHom with
    commutes' := fun r => by
      simp only [toRingHom_eq_coe, RingHom.toFun_eq_coe, RingHom.prod_apply, coe_toRingHom,
        commutes, Prod.algebraMap_apply] }

/--
theorem `coe_prod` / 定理 `coe_prod`

English:
theorem coe_prod
  given: (f : A ->ₐ[R] B) (g : A ->ₐ[R] C)
  statement: ⇑(f.prod g) = Function.prod f g
  proof: rfl

@[simp]

中文:
定理 coe_prod
  条件: (f : A ->ₐ[R] B) (g : A ->ₐ[R] C)
  结论: ⇑(f.prod g) = Function.prod f g
  证明: rfl

@[simp]
-/
theorem coe_prod (f : A ->ₐ[R] B) (g : A ->ₐ[R] C) : ⇑(f.prod g) = Function.prod f g :=
  rfl

@[simp]
/--
theorem `fst_prod` / 定理 `fst_prod`

English:
theorem fst_prod
  given: (f : A ->ₐ[R] B) (g : A ->ₐ[R] C)
  statement: (fst R B C).comp (prod f g) = f
  proof: by ext; rfl

@[simp]

中文:
定理 fst_prod
  条件: (f : A ->ₐ[R] B) (g : A ->ₐ[R] C)
  结论: (fst R B C).comp (prod f g) = f
  证明: by ext; rfl

@[simp]
-/
theorem fst_prod (f : A ->ₐ[R] B) (g : A ->ₐ[R] C) : (fst R B C).comp (prod f g) = f := by ext; rfl

@[simp]
/--
theorem `snd_prod` / 定理 `snd_prod`

English:
theorem snd_prod
  given: (f : A ->ₐ[R] B) (g : A ->ₐ[R] C)
  statement: (snd R B C).comp (prod f g) = g
  proof: by ext; rfl

@[simp]

中文:
定理 snd_prod
  条件: (f : A ->ₐ[R] B) (g : A ->ₐ[R] C)
  结论: (snd R B C).comp (prod f g) = g
  证明: by ext; rfl

@[simp]
-/
theorem snd_prod (f : A ->ₐ[R] B) (g : A ->ₐ[R] C) : (snd R B C).comp (prod f g) = g := by ext; rfl

@[simp]
/--
theorem `prod_fst_snd` / 定理 `prod_fst_snd`

English:
theorem prod_fst_snd
  statement: prod (fst R A B) (snd R A B) = AlgHom.id R _
  proof: rfl

中文:
定理 prod_fst_snd
  结论: prod (fst R A B) (snd R A B) = AlgHom.id R _
  证明: rfl
-/
theorem prod_fst_snd : prod (fst R A B) (snd R A B) = AlgHom.id R _ := rfl

/--
theorem `prod_comp` / 定理 `prod_comp`

English:
theorem prod_comp
  statement: {C' : Type*} [Semiring C'] [Algebra R C']
  proof: rfl

中文:
定理 prod_comp
  结论: {C' : 类型} [Semiring C'] [Algebra R C']
  证明: rfl
-/
theorem prod_comp {C' : Type*} [Semiring C'] [Algebra R C']
    (f : A ->ₐ[R] B) (g : B ->ₐ[R] C) (g' : B ->ₐ[R] C') :
    (g.prod g').comp f = (g.comp f).prod (g'.comp f) := rfl

/-- Taking the product of two maps with the same domain is equivalent to taking the product of
their codomains. -/
@[simps]
/--
Definition of `prodEquiv` / `prodEquiv` 的定义

English:
definition prodEquiv
  signature: : (A ->ₐ[R] B) × (A ->ₐ[R] C) ≃ (A ->ₐ[R] B × C) where
  body: f.1.prod f.2
  invFun f := ((fst _ _ _).comp f, (snd _ _ _).comp f)

中文:
定义 prodEquiv
  签名: : (A ->ₐ[R] B) × (A ->ₐ[R] C) ≃ (A ->ₐ[R] B × C) where
  定义体: f.1.prod f.2
  invFun f := ((fst _ _ _).comp f, (snd _ _ _).comp f)
-/
def prodEquiv : (A ->ₐ[R] B) × (A ->ₐ[R] C) ≃ (A ->ₐ[R] B × C) where
  toFun f := f.1.prod f.2
  invFun f := ((fst _ _ _).comp f, (snd _ _ _).comp f)

/--
Definition of `prodMap` / `prodMap` 的定义

English:
definition prodMap
  signature: {D : Type*} [Semiring D] [Algebra R D] (f : A ->ₐ[R] B) (g : C ->ₐ[R] D)
  body: { toRingHom := f.toRingHom.prodMap g.toRingHom
    commutes' := fun r => by simp [commutes] }

中文:
定义 prodMap
  签名: {D : 类型} [Semiring D] [Algebra R D] (f : A ->ₐ[R] B) (g : C ->ₐ[R] D)
  定义体: { toRingHom := f.toRingHom.prodMap g.toRingHom
    commutes' := fun r => by simp [commutes] }

Depends on / 依赖: commutes, f.toRingHom.prodMap, g.toRingHom, prodMap, toRingHom
-/
def prodMap {D : Type*} [Semiring D] [Algebra R D] (f : A ->ₐ[R] B) (g : C ->ₐ[R] D) :
    A × C ->ₐ[R] B × D :=
  { toRingHom := f.toRingHom.prodMap g.toRingHom
    commutes' := fun r => by simp [commutes] }

end AlgHom

namespace AlgEquiv

section

variable {S T A B : Type*} [Semiring A] [Semiring B]
  [Semiring S] [Semiring T] [Algebra R S] [Algebra R T] [Algebra R A] [Algebra R B]

/--
Definition of `prodCongr` / `prodCongr` 的定义

English:
definition prodCongr
  signature: (l : S ≃ₐ[R] A) (r : T ≃ₐ[R] B)
  body: .ofRingEquiv (f := RingEquiv.prodCongr l r) by simp

中文:
定义 prodCongr
  签名: (l : S ≃ₐ[R] A) (r : T ≃ₐ[R] B)
  定义体: .ofRingEquiv (f := RingEquiv.prodCongr l r) by simp

Depends on / 依赖: RingEquiv, RingEquiv.prodCongr, ofRingEquiv, prodCongr
-/
def prodCongr (l : S ≃ₐ[R] A) (r : T ≃ₐ[R] B) : (S × T) ≃ₐ[R] A × B :=
.ofRingEquiv (f := RingEquiv.prodCongr l r) by simp

variable (l : S ≃ₐ[R] A) (r : T ≃ₐ[R] B)

-- Priority `low` to ensure generic `map_{add, mul, zero, one}` lemmas are applied first
@[simp low]
/--
lemma `prodCongr_apply` / 引理 `prodCongr_apply`

English:
lemma prodCongr_apply
  given: (x : S × T)
  statement: prodCongr l r x = Equiv.prodCongr l r x
  proof: rfl

中文:
引理 prodCongr_apply
  条件: (x : S × T)
  结论: prodCongr l r x = Equiv.prodCongr l r x
  证明: rfl
-/
lemma prodCongr_apply (x : S × T) : prodCongr l r x = Equiv.prodCongr l r x := rfl

-- Priority `low` to ensure generic `map_{add, mul, zero, one}` lemmas are applied first
@[simp low]
/--
lemma `prodCongr_symm_apply` / 引理 `prodCongr_symm_apply`

English:
lemma prodCongr_symm_apply
  given: (x : A × B)
  proof: rfl

中文:
引理 prodCongr_symm_apply
  条件: (x : A × B)
  证明: rfl
-/
lemma prodCongr_symm_apply (x : A × B) :
    (prodCongr l r).symm x = (Equiv.prodCongr l r).symm x := rfl

end

/-- Multiplying by the trivial algebra from the right does not change the structure.
This is the `AlgEquiv` version of `LinearEquiv.prodUnique` and `RingEquiv.prodZeroRing.symm`. -/
@[simps!]
/--
Definition of `prodUnique` / `prodUnique` 的定义

English:
definition prodUnique
  signature: [Unique B]
  body: Prod.fst
  invFun x := (x, 0)
  __ := (RingEquiv.prodZeroRing A B).symm
  commutes' _ := rfl

中文:
定义 prodUnique
  签名: [Unique B]
  定义体: Prod.fst
  invFun x := (x, 0)
  __ := (RingEquiv.prodZeroRing A B).symm
  commutes' _ := rfl

Depends on / 依赖: Prod.fst
-/
def prodUnique [Unique B] : (A × B) ≃ₐ[R] A where
  toFun := Prod.fst
  invFun x := (x, 0)
  __ := (RingEquiv.prodZeroRing A B).symm
  commutes' _ := rfl

/-- Multiplying by the trivial algebra from the left does not change the structure.
This is the `AlgEquiv` version of `LinearEquiv.uniqueProd` and `RingEquiv.zeroRingProd.symm`.
-/
@[simps!]
/--
Definition of `uniqueProd` / `uniqueProd` 的定义

English:
definition uniqueProd
  signature: [Unique B]
  body: Prod.snd
  invFun x := (0, x)
  __ := (RingEquiv.zeroRingProd A B).symm
  commutes' _ := rfl

中文:
定义 uniqueProd
  签名: [Unique B]
  定义体: Prod.snd
  invFun x := (0, x)
  __ := (RingEquiv.zeroRingProd A B).symm
  commutes' _ := rfl

Depends on / 依赖: Prod.snd
-/
def uniqueProd [Unique B] : (B × A) ≃ₐ[R] A where
  toFun := Prod.snd
  invFun x := (0, x)
  __ := (RingEquiv.zeroRingProd A B).symm
  commutes' _ := rfl

end AlgEquiv
