/-
Copyright (c) 2024 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
module

public import Mathlib.FieldTheory.Extension

/-!
# Conjugate roots

Given two elements `x` and `y` of some `K`-algebra, these two elements are *conjugate roots*
over `K` if they have the same minimal polynomial over `K`.

## Main definitions

* `IsConjRoot`: `IsConjRoot K x y` means `y` is a conjugate root of `x` over `K`.

## Main results

* `isConjRoot_iff_exists_algEquiv`: Let `L / K` be a normal field extension. For any two elements
  `x` and `y` in `L`, `IsConjRoot K x y` is equivalent to the existence of an algebra equivalence
  `σ : Gal(L/K)` such that `y = σ x`.
* `notMem_iff_exists_ne_and_isConjRoot`: Let `L / K` be a field extension. If `x` is a separable
  element over `K` and the minimal polynomial of `x` splits in `L`, then `x` is not in the `K` iff
  there exists a different conjugate root of `x` in `L` over `K`.

## TODO
* Move `IsConjRoot` to earlier files and refactor the theorems in field theory using `IsConjRoot`.

* Prove `IsConjRoot.smul`, if `x` and `y` are conjugate roots, then so are `r • x` and `r • y`.

## Tags
conjugate root, minimal polynomial
-/

@[expose] public section


open Polynomial minpoly Module IntermediateField

variable {R K L S A B : Type*} [CommRing R] [CommRing S] [Ring A] [Ring B] [Field K] [Field L]
variable [Algebra R S] [Algebra R A] [Algebra R B]
variable [Algebra K S] [Algebra K L] [Algebra K A] [Algebra L S]

variable (R) in
/--
Definition of `IsConjRoot` / `IsConjRoot` 的定义

English:
definition IsConjRoot
  signature: (x y : A)
  body: minpoly R x = minpoly R y

中文:
定义 IsConjRoot
  签名: (x y : A)
  定义体: minpoly R x = minpoly R y

Depends on / 依赖: minpoly
-/
def IsConjRoot (x y : A) : Prop := minpoly R x = minpoly R y

/--
theorem `isConjRoot_def` / 定理 `isConjRoot_def`

English:
theorem isConjRoot_def
  given: {x y : A}
  statement: IsConjRoot R x y ↔ minpoly R x = minpoly R y
  proof: Iff.rfl

中文:
定理 isConjRoot_def
  条件: {x y : A}
  结论: IsConjRoot R x y ↔ minpoly R x = minpoly R y
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem isConjRoot_def {x y : A} : IsConjRoot R x y ↔ minpoly R x = minpoly R y := Iff.rfl

namespace IsConjRoot

/--
theorem `refl` / 定理 `refl`

English:
theorem refl
  given: {x : A}
  statement: IsConjRoot R x x
  proof: rfl

中文:
定理 refl
  条件: {x : A}
  结论: IsConjRoot R x x
  证明: rfl
-/
@[refl] theorem refl {x : A} : IsConjRoot R x x := rfl

/--
theorem `symm` / 定理 `symm`

English:
theorem symm
  given: {x y : A} (h : IsConjRoot R x y)
  statement: IsConjRoot R y x
  proof: Eq.symm h

中文:
定理 symm
  条件: {x y : A} (h : IsConjRoot R x y)
  结论: IsConjRoot R y x
  证明: Eq.symm h
-/
@[symm] theorem symm {x y : A} (h : IsConjRoot R x y) : IsConjRoot R y x := Eq.symm h

/--
theorem `trans` / 定理 `trans`

English:
theorem trans
  given: {x y z : A} (h₁ : IsConjRoot R x y) (h₂ : IsConjRoot R y z)
  proof: Eq.trans h₁ h₂

中文:
定理 trans
  条件: {x y z : A} (h₁ : IsConjRoot R x y) (h₂ : IsConjRoot R y z)
  证明: Eq.trans h₁ h₂
-/
@[trans] theorem trans {x y z : A} (h₁ : IsConjRoot R x y) (h₂ : IsConjRoot R y z) :
    IsConjRoot R x z := Eq.trans h₁ h₂

variable (R A) in
/--
The setoid structure on `A` defined by the equivalence relation of `IsConjRoot R · ·`.
-/
@[instance_reducible]
/--
Definition of `setoid` / `setoid` 的定义

English:
definition setoid
  signature: : Setoid A where
  body: IsConjRoot R
  iseqv := ⟨fun _ => refl, symm, trans⟩

中文:
定义 setoid
  签名: : 集合等价关系 A where
  定义体: IsConjRoot R
  iseqv := ⟨fun _ => refl, symm, trans⟩

Depends on / 依赖: IsConjRoot
-/
def setoid : Setoid A where
  r := IsConjRoot R
  iseqv := ⟨fun _ => refl, symm, trans⟩

/--
theorem `comm` / 定理 `comm`

English:
theorem comm
  given: {x y : A}
  statement: IsConjRoot R x y ↔ IsConjRoot R y x
  proof: ⟨symm, symm⟩

中文:
定理 comm
  条件: {x y : A}
  结论: IsConjRoot R x y ↔ IsConjRoot R y x
  证明: ⟨symm, symm⟩
-/
theorem comm {x y : A} : IsConjRoot R x y ↔ IsConjRoot R y x :=
  ⟨symm, symm⟩

/--
theorem `aeval_eq_zero` / 定理 `aeval_eq_zero`

English:
theorem aeval_eq_zero
  given: {x y : A} (h : IsConjRoot R x y)
  statement: aeval y (minpoly R x) = 0
  proof: h ▸ minpoly.aeval R y

中文:
定理 aeval_eq_zero
  条件: {x y : A} (h : IsConjRoot R x y)
  结论: aeval y (minpoly R x) = 0
  证明: h ▸ minpoly.aeval R y

Depends on / 依赖: minpoly, minpoly.aeval
-/
theorem aeval_eq_zero {x y : A} (h : IsConjRoot R x y) : aeval y (minpoly R x) = 0 :=
  h ▸ minpoly.aeval R y

/--
theorem `add_algebraMap` / 定理 `add_algebraMap`

English:
theorem add_algebraMap
  given: {x y : S} (r : K) (h : IsConjRoot K x y)
  proof: by
  rw [isConjRoot_def]; rw [minpoly.add_algebraMap x r]; rw [minpoly.add_algebraMap y r]; rw [h]

中文:
定理 add_algebraMap
  条件: {x y : S} (r : K) (h : IsConjRoot K x y)
  证明: by
  rw [isConjRoot_def]; rw [minpoly.add_algebraMap x r]; rw [minpoly.add_algebraMap y r]; rw [h]

Depends on / 依赖: add_algebraMap, isConjRoot_def, minpoly, minpoly.add_algebraMap
-/
theorem add_algebraMap {x y : S} (r : K) (h : IsConjRoot K x y) :
    IsConjRoot K (x + algebraMap K S r) (y + algebraMap K S r) := by
  rw [isConjRoot_def]; rw [minpoly.add_algebraMap x r]; rw [minpoly.add_algebraMap y r]; rw [h]

/--
theorem `sub_algebraMap` / 定理 `sub_algebraMap`

English:
theorem sub_algebraMap
  given: {x y : S} (r : K) (h : IsConjRoot K x y)
  proof: by
  simpa only [sub_eq_add_neg, map_neg] using add_algebraMap (-r) h

中文:
定理 sub_algebraMap
  条件: {x y : S} (r : K) (h : IsConjRoot K x y)
  证明: by
  simpa only [sub_eq_add_neg, map_neg] using add_algebraMap (-r) h

Depends on / 依赖: add_algebraMap, map_neg, sub_eq_add_neg
-/
theorem sub_algebraMap {x y : S} (r : K) (h : IsConjRoot K x y) :
    IsConjRoot K (x - algebraMap K S r) (y - algebraMap K S r) := by
  simpa only [sub_eq_add_neg, map_neg] using add_algebraMap (-r) h

/--
theorem `neg` / 定理 `neg`

English:
theorem neg
  given: {x y : S} (h : IsConjRoot K x y)
  proof: by
  rw [isConjRoot_def]; rw [minpoly.neg x]; rw [minpoly.neg y]; rw [h]

中文:
定理 neg
  条件: {x y : S} (h : IsConjRoot K x y)
  证明: by
  rw [isConjRoot_def]; rw [minpoly.neg x]; rw [minpoly.neg y]; rw [h]

Depends on / 依赖: isConjRoot_def, minpoly, minpoly.neg
-/
theorem neg {x y : S} (h : IsConjRoot K x y) :
    IsConjRoot K (-x) (-y) := by
  rw [isConjRoot_def]; rw [minpoly.neg x]; rw [minpoly.neg y]; rw [h]

end IsConjRoot

open IsConjRoot

/--
theorem `isConjRoot_algHom_iff_of_injective` / 定理 `isConjRoot_algHom_iff_of_injective`

English:
theorem isConjRoot_algHom_iff_of_injective
  statement: {x y : A} {f : A ->ₐ[R] B}
  proof: by
  rw [isConjRoot_def]; rw [isConjRoot_def]; rw [algHom_eq f hf]; rw [algHom_eq f hf]

中文:
定理 isConjRoot_algHom_iff_of_injective
  结论: {x y : A} {f : A ->ₐ[R] B}
  证明: by
  rw [isConjRoot_def]; rw [isConjRoot_def]; rw [algHom_eq f hf]; rw [algHom_eq f hf]

Depends on / 依赖: algHom_eq, isConjRoot_def
-/
theorem isConjRoot_algHom_iff_of_injective {x y : A} {f : A ->ₐ[R] B}
    (hf : Function.Injective f) : IsConjRoot R (f x) (f y) ↔ IsConjRoot R x y := by
  rw [isConjRoot_def]; rw [isConjRoot_def]; rw [algHom_eq f hf]; rw [algHom_eq f hf]

/--
theorem `isConjRoot_algHom_iff` / 定理 `isConjRoot_algHom_iff`

English:
theorem isConjRoot_algHom_iff
  statement: {A} [DivisionRing A] [Algebra R A]
  proof: isConjRoot_algHom_iff_of_injective f.injective

中文:
定理 isConjRoot_algHom_iff
  结论: {A} [除环 A] [代数 R A]
  证明: isConjRoot_algHom_iff_of_injective f.injective

Depends on / 依赖: f.injective, injective, isConjRoot_algHom_iff_of_injective
-/
theorem isConjRoot_algHom_iff {A} [DivisionRing A] [Algebra R A]
    [Nontrivial B] {x y : A} (f : A ->ₐ[R] B) : IsConjRoot R (f x) (f y) ↔ IsConjRoot R x y :=
  isConjRoot_algHom_iff_of_injective f.injective

/--
theorem `isConjRoot_of_aeval_eq_zero` / 定理 `isConjRoot_of_aeval_eq_zero`

English:
theorem isConjRoot_of_aeval_eq_zero
  statement: [IsDomain A] {x y : A} (hx : IsIntegral K x)
  proof: minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hx) h (minpoly.monic hx)

中文:
定理 isConjRoot_of_aeval_eq_zero
  结论: [是整环 A] {x y : A} (hx : 是整 K x)
  证明: minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hx) h (minpoly.monic hx)

Depends on / 依赖: eq_of_irreducible_of_monic, irreducible, minpoly, minpoly.eq_of_irreducible_of_monic, minpoly.irreducible, minpoly.monic
-/
theorem isConjRoot_of_aeval_eq_zero [IsDomain A] {x y : A} (hx : IsIntegral K x)
    (h : aeval y (minpoly K x) = 0) : IsConjRoot K x y :=
  minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hx) h (minpoly.monic hx)

/--
theorem `isConjRoot_iff_aeval_eq_zero` / 定理 `isConjRoot_iff_aeval_eq_zero`

English:
theorem isConjRoot_iff_aeval_eq_zero
  statement: [IsDomain A] {x y : A}
  proof: ⟨IsConjRoot.aeval_eq_zero, isConjRoot_of_aeval_eq_zero h⟩

中文:
定理 isConjRoot_iff_aeval_eq_zero
  结论: [是整环 A] {x y : A}
  证明: ⟨IsConjRoot.aeval_eq_zero, isConjRoot_of_aeval_eq_zero h⟩

Depends on / 依赖: IsConjRoot, IsConjRoot.aeval_eq_zero, aeval_eq_zero, isConjRoot_of_aeval_eq_zero
-/
theorem isConjRoot_iff_aeval_eq_zero [IsDomain A] {x y : A}
    (h : IsIntegral K x) : IsConjRoot K x y ↔ aeval y (minpoly K x) = 0 :=
  ⟨IsConjRoot.aeval_eq_zero, isConjRoot_of_aeval_eq_zero h⟩

/--
Let `s` be an `R`-algebra isomorphism. Then `s x` is a conjugate root of `x`.
-/
@[simp]
/--
theorem `isConjRoot_of_algEquiv` / 定理 `isConjRoot_of_algEquiv`

English:
theorem isConjRoot_of_algEquiv
  given: (x : A) (s : A ≃ₐ[R] A)
  statement: IsConjRoot R x (s x)
  proof: Eq.symm (minpoly.algEquiv_eq s x)

中文:
定理 isConjRoot_of_algEquiv
  条件: (x : A) (s : A ≃ₐ[R] A)
  结论: IsConjRoot R x (s x)
  证明: Eq.symm (minpoly.algEquiv_eq s x)

Depends on / 依赖: Eq.symm, algEquiv_eq, minpoly, minpoly.algEquiv_eq
-/
theorem isConjRoot_of_algEquiv (x : A) (s : A ≃ₐ[R] A) : IsConjRoot R x (s x) :=
  Eq.symm (minpoly.algEquiv_eq s x)

/--
A variant of `isConjRoot_of_algEquiv`.
Let `s` be an `R`-algebra isomorphism. Then `x` is a conjugate root of `s x`.
-/
@[simp]
/--
theorem `isConjRoot_of_algEquiv'` / 定理 `isConjRoot_of_algEquiv'`

English:
theorem isConjRoot_of_algEquiv'
  given: (x : A) (s : A ≃ₐ[R] A)
  statement: IsConjRoot R (s x) x
  proof: (minpoly.algEquiv_eq s x)

中文:
定理 isConjRoot_of_algEquiv'
  条件: (x : A) (s : A ≃ₐ[R] A)
  结论: IsConjRoot R (s x) x
  证明: (minpoly.algEquiv_eq s x)

Depends on / 依赖: algEquiv_eq, minpoly, minpoly.algEquiv_eq
-/
theorem isConjRoot_of_algEquiv' (x : A) (s : A ≃ₐ[R] A) : IsConjRoot R (s x) x :=
  (minpoly.algEquiv_eq s x)

/--
Let `s₁` and `s₂` be two `R`-algebra isomorphisms. Then `s₂ x` is a conjugate root of `s₁ x`.
-/
@[simp]
/--
theorem `isConjRoot_of_algEquiv₂` / 定理 `isConjRoot_of_algEquiv₂`

English:
theorem isConjRoot_of_algEquiv₂
  given: (x : A) (s₁ s₂ : A ≃ₐ[R] A)
  statement: IsConjRoot R (s₁ x) (s₂ x)
  proof: isConjRoot_def.mpr (minpoly.algEquiv_eq s₂ x) ▸ (minpoly.algEquiv_eq s₁ x)

中文:
定理 isConjRoot_of_algEquiv₂
  条件: (x : A) (s₁ s₂ : A ≃ₐ[R] A)
  结论: IsConjRoot R (s₁ x) (s₂ x)
  证明: isConjRoot_def.mpr (minpoly.algEquiv_eq s₂ x) ▸ (minpoly.algEquiv_eq s₁ x)

Depends on / 依赖: algEquiv_eq, isConjRoot_def, isConjRoot_def.mpr, minpoly, minpoly.algEquiv_eq
-/
theorem isConjRoot_of_algEquiv₂ (x : A) (s₁ s₂ : A ≃ₐ[R] A) : IsConjRoot R (s₁ x) (s₂ x) :=
isConjRoot_def.mpr (minpoly.algEquiv_eq s₂ x) ▸ (minpoly.algEquiv_eq s₁ x)

/--
theorem `IsConjRoot.exists_algEquiv` / 定理 `IsConjRoot.exists_algEquiv`

English:
theorem IsConjRoot.exists_algEquiv
  given: [Normal K L] {x y : L} (h : IsConjRoot K x y)
  proof: by
  obtain ⟨σ, hσ⟩ :=
    exists_algHom_of_splits_of_aeval (normal_iff.mp inferInstance) (h ▸ minpoly.aeval K x)
  exact ⟨AlgEquiv.ofBijective σ (σ.normal_bijective _ _ _), hσ⟩

中文:
定理 IsConjRoot.存在_algEquiv
  条件: [正规 K L] {x y : L} (h : IsConjRoot K x y)
  证明: by
  obtain ⟨σ, hσ⟩ :=
    exists_algHom_of_splits_of_aeval (normal_iff.mp inferInstance) (h ▸ minpoly.aeval K x)
  exact ⟨AlgEquiv.ofBijective σ (σ.normal_bijective _ _ _), hσ⟩

Depends on / 依赖: AlgEquiv, AlgEquiv.ofBijective, exists_algHom_of_splits_of_aeval, minpoly, minpoly.aeval, normal_bijective, normal_iff, normal_iff.mp, ofBijective
-/
theorem IsConjRoot.exists_algEquiv [Normal K L] {x y : L} (h : IsConjRoot K x y) :
    exists σ : Gal(L/K), σ y = x := by
  obtain ⟨σ, hσ⟩ :=
    exists_algHom_of_splits_of_aeval (normal_iff.mp inferInstance) (h ▸ minpoly.aeval K x)
  exact ⟨AlgEquiv.ofBijective σ (σ.normal_bijective _ _ _), hσ⟩

/--
theorem `isConjRoot_iff_exists_algEquiv` / 定理 `isConjRoot_iff_exists_algEquiv`

English:
theorem isConjRoot_iff_exists_algEquiv
  given: [Normal K L] {x y : L}
  proof: ⟨exists_algEquiv, fun ⟨_, h⟩ => h ▸ (isConjRoot_of_algEquiv _ _).symm⟩

中文:
定理 isConjRoot_iff_存在_algEquiv
  条件: [正规 K L] {x y : L}
  证明: ⟨exists_algEquiv, fun ⟨_, h⟩ => h ▸ (isConjRoot_of_algEquiv _ _).symm⟩

Depends on / 依赖: exists_algEquiv, isConjRoot_of_algEquiv
-/
theorem isConjRoot_iff_exists_algEquiv [Normal K L] {x y : L} :
    IsConjRoot K x y ↔ exists σ : Gal(L/K), σ y = x :=
  ⟨exists_algEquiv, fun ⟨_, h⟩ => h ▸ (isConjRoot_of_algEquiv _ _).symm⟩

/--
theorem `isConjRoot_iff_orbitRel` / 定理 `isConjRoot_iff_orbitRel`

English:
theorem isConjRoot_iff_orbitRel
  given: [Normal K L] {x y : L}
  proof: (isConjRoot_iff_exists_algEquiv)

中文:
定理 isConjRoot_iff_orbitRel
  条件: [正规 K L] {x y : L}
  证明: (isConjRoot_iff_exists_algEquiv)

Depends on / 依赖: isConjRoot_iff_exists_algEquiv
-/
theorem isConjRoot_iff_orbitRel [Normal K L] {x y : L} :
    IsConjRoot K x y ↔ MulAction.orbitRel Gal(L/K) L x y :=
  (isConjRoot_iff_exists_algEquiv)

variable [IsDomain S]

/--
theorem `IsConjRoot.of_isScalarTower` / 定理 `IsConjRoot.of_isScalarTower`

English:
theorem IsConjRoot.of_isScalarTower
  statement: [IsScalarTower K L S] {x y : S} (hx : IsIntegral K x)
  proof: isConjRoot_of_aeval_eq_zero hx minpoly.aeval_of_isScalarTower K x y (aeval_eq_zero h)

中文:
定理 IsConjRoot.of_isScalarTower
  结论: [标量塔 K L S] {x y : S} (hx : 是整 K x)
  证明: isConjRoot_of_aeval_eq_zero hx minpoly.aeval_of_isScalarTower K x y (aeval_eq_zero h)

Depends on / 依赖: aeval_eq_zero, aeval_of_isScalarTower, i.val, isConjRoot_of_aeval_eq_zero, minpoly, minpoly.aeval_of_isScalarTower, toJson
-/
theorem IsConjRoot.of_isScalarTower [IsScalarTower K L S] {x y : S} (hx : IsIntegral K x)
    (h : IsConjRoot L x y) : IsConjRoot K x y :=
isConjRoot_of_aeval_eq_zero hx minpoly.aeval_of_isScalarTower K x y (aeval_eq_zero h)

/--
theorem `isConjRoot_iff_mem_minpoly_aroots` / 定理 `isConjRoot_iff_mem_minpoly_aroots`

English:
theorem isConjRoot_iff_mem_minpoly_aroots
  given: {x y : S} (h : IsIntegral K x)
  proof: by
  rw [Polynomial.mem_aroots]; rw [isConjRoot_iff_aeval_eq_zero h]
  simp only [iff_and_self]
  exact fun _ => minpoly.ne_zero h

中文:
定理 isConjRoot_iff_mem_minpoly_aroots
  条件: {x y : S} (h : 是整 K x)
  证明: by
  rw [Polynomial.mem_aroots]; rw [isConjRoot_iff_aeval_eq_zero h]
  simp only [iff_and_self]
  exact fun _ => minpoly.ne_zero h

Depends on / 依赖: Polynomial, Polynomial.mem_aroots, iff_and_self, isConjRoot_iff_aeval_eq_zero, mem_aroots, minpoly, minpoly.ne_zero, ne_zero
-/
theorem isConjRoot_iff_mem_minpoly_aroots {x y : S} (h : IsIntegral K x) :
    IsConjRoot K x y ↔ y in (minpoly K x).aroots S := by
  rw [Polynomial.mem_aroots]; rw [isConjRoot_iff_aeval_eq_zero h]
  simp only [iff_and_self]
  exact fun _ => minpoly.ne_zero h

/--
theorem `isConjRoot_iff_mem_minpoly_rootSet` / 定理 `isConjRoot_iff_mem_minpoly_rootSet`

English:
theorem isConjRoot_iff_mem_minpoly_rootSet
  statement: {x y : S}
  proof: (isConjRoot_iff_mem_minpoly_aroots h).trans (by simp [rootSet])

中文:
定理 isConjRoot_iff_mem_minpoly_rootSet
  结论: {x y : S}
  证明: (isConjRoot_iff_mem_minpoly_aroots h).trans (by simp [rootSet])

Depends on / 依赖: isConjRoot_iff_mem_minpoly_aroots, rootSet, toJson, x.val
-/
theorem isConjRoot_iff_mem_minpoly_rootSet {x y : S}
    (h : IsIntegral K x) : IsConjRoot K x y ↔ y in (minpoly K x).rootSet S :=
  (isConjRoot_iff_mem_minpoly_aroots h).trans (by simp [rootSet])

namespace IsConjRoot

/--
Instance `decidable` / 实例 `decidable`

English:
instance decidable
  signature: [Normal K L] [DecidableEq L] [Fintype Gal(L/K)] (x y : L)
  body: decidable_of_iff _ isConjRoot_iff_exists_algEquiv.symm

中文:
实例 decidable
  签名: [正规 K L] [DecidableEq L] [有限类型 Gal(L/K)] (x y : L)
  定义体: decidable_of_iff _ isConjRoot_iff_exists_algEquiv.symm

Depends on / 依赖: decidable_of_iff, isConjRoot_iff_exists_algEquiv, isConjRoot_iff_exists_algEquiv.symm
-/
instance decidable [Normal K L] [DecidableEq L] [Fintype Gal(L/K)] (x y : L) :
    Decidable (IsConjRoot K x y) :=
  decidable_of_iff _ isConjRoot_iff_exists_algEquiv.symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsEquiv A (IsConjRoot R)
  body: letI := IsConjRoot.setoid R A
inferInstanceAs IsEquiv A (· ≈ ·)

中文:
实例 :
  签名: Is等价 A (IsConjRoot R)
  定义体: letI := IsConjRoot.setoid R A
inferInstanceAs IsEquiv A (· ≈ ·)

Depends on / 依赖: IsConjRoot, IsConjRoot.setoid, IsEquiv, setoid
-/
instance : IsEquiv A (IsConjRoot R) :=
  letI := IsConjRoot.setoid R A
inferInstanceAs IsEquiv A (· ≈ ·)

/--
theorem `isIntegral` / 定理 `isIntegral`

English:
theorem isIntegral
  given: {x y : A} (hx : IsIntegral R x) (h : IsConjRoot R x y)
  proof: ⟨minpoly R x, minpoly.monic hx, h ▸ minpoly.aeval R y⟩

中文:
定理 is整数egral
  条件: {x y : A} (hx : 是整 R x) (h : IsConjRoot R x y)
  证明: ⟨minpoly R x, minpoly.monic hx, h ▸ minpoly.aeval R y⟩

Depends on / 依赖: linter, linter.myLinter, minpoly, minpoly.aeval, minpoly.monic, myLinter, whenLinterActivated
-/
theorem isIntegral {x y : A} (hx : IsIntegral R x) (h : IsConjRoot R x y) :
    IsIntegral R y :=
  ⟨minpoly R x, minpoly.monic hx, h ▸ minpoly.aeval R y⟩

/--
theorem `isIntegral_iff` / 定理 `isIntegral_iff`

English:
theorem isIntegral_iff
  given: {x y : A} (h : IsConjRoot R x y)
  statement: IsIntegral R x ↔ IsIntegral R y
  proof: ⟨fun hx => isIntegral hx h, fun hy => isIntegral hy h.symm⟩

中文:
定理 is整数egral_iff
  条件: {x y : A} (h : IsConjRoot R x y)
  结论: 是整 R x ↔ 是整 R y
  证明: ⟨fun hx => isIntegral hx h, fun hy => isIntegral hy h.symm⟩

Depends on / 依赖: h.symm, isIntegral
-/
theorem isIntegral_iff {x y : A} (h : IsConjRoot R x y) : IsIntegral R x ↔ IsIntegral R y :=
  ⟨fun hx => isIntegral hx h, fun hy => isIntegral hy h.symm⟩

/--
theorem `eq_algebraMap_of_injective` / 定理 `eq_algebraMap_of_injective`

English:
theorem eq_algebraMap_of_injective
  statement: [IsDomain R] [IsTorsionFree R S] {r : R} {x : S}
  proof: by
  rw [IsConjRoot]; rw [minpoly.eq_X_sub_C_of_algebraMap_inj _ hf] at h
  have : x in (X - C r).aroots S := by
    rw [mem_aroots]
    simp [X_sub_C_ne_zero, h ▸ minpoly.aeval R x]
  simpa [aroots_X_sub_C] using this

中文:
定理 eq_algebraMap_of_injective
  结论: [是整环 R] [是无挠 R S] {r : R} {x : S}
  证明: by
  rw [IsConjRoot]; rw [minpoly.eq_X_sub_C_of_algebraMap_inj _ hf] at h
  have : x in (X - C r).aroots S := by
    rw [mem_aroots]
    simp [X_sub_C_ne_zero, h ▸ minpoly.aeval R x]
  simpa [aroots_X_sub_C] using this

Depends on / 依赖: IsConjRoot, X_sub_C_ne_zero, aroots, aroots_X_sub_C, eq_X_sub_C_of_algebraMap_inj, mem_aroots, minpoly, minpoly.aeval, minpoly.eq_X_sub_C_of_algebraMap_inj
-/
theorem eq_algebraMap_of_injective [IsDomain R] [IsTorsionFree R S] {r : R} {x : S}
    (h : IsConjRoot R (algebraMap R S r) x) (hf : Function.Injective (algebraMap R S)) :
    x = algebraMap R S r := by
  rw [IsConjRoot]; rw [minpoly.eq_X_sub_C_of_algebraMap_inj _ hf] at h
  have : x in (X - C r).aroots S := by
    rw [mem_aroots]
    simp [X_sub_C_ne_zero, h ▸ minpoly.aeval R x]
  simpa [aroots_X_sub_C] using this

/--
theorem `eq_algebraMap` / 定理 `eq_algebraMap`

English:
theorem eq_algebraMap
  given: {r : K} {x : S} (h : IsConjRoot K (algebraMap K S r) x)
  proof: eq_algebraMap_of_injective h (algebraMap K S).injective

中文:
定理 eq_algebraMap
  条件: {r : K} {x : S} (h : IsConjRoot K (algebraMap K S r) x)
  证明: eq_algebraMap_of_injective h (algebraMap K S).injective

Depends on / 依赖: algebraMap, eq_algebraMap_of_injective, injective
-/
theorem eq_algebraMap {r : K} {x : S} (h : IsConjRoot K (algebraMap K S r) x) :
    x = algebraMap K S r :=
  eq_algebraMap_of_injective h (algebraMap K S).injective

/--
theorem `eq_zero_of_injective` / 定理 `eq_zero_of_injective`

English:
theorem eq_zero_of_injective
  statement: [IsDomain R] [IsTorsionFree R S] {x : S} (h : IsConjRoot R 0 x)
  proof: (algebraMap R S).map_zero ▸ (eq_algebraMap_of_injective ((algebraMap R S).map_zero ▸ h) hf)

中文:
定理 eq_zero_of_injective
  结论: [是整环 R] [是无挠 R S] {x : S} (h : IsConjRoot R 0 x)
  证明: (algebraMap R S).map_zero ▸ (eq_algebraMap_of_injective ((algebraMap R S).map_zero ▸ h) hf)

Depends on / 依赖: algebraMap, eq_algebraMap_of_injective, map_zero
-/
theorem eq_zero_of_injective [IsDomain R] [IsTorsionFree R S] {x : S} (h : IsConjRoot R 0 x)
    (hf : Function.Injective (algebraMap R S)) : x = 0 :=
  (algebraMap R S).map_zero ▸ (eq_algebraMap_of_injective ((algebraMap R S).map_zero ▸ h) hf)

/--
theorem `eq_zero` / 定理 `eq_zero`

English:
theorem eq_zero
  given: {x : S} (h : IsConjRoot K 0 x)
  statement: x = 0
  proof: eq_zero_of_injective h (algebraMap K S).injective

中文:
定理 eq_zero
  条件: {x : S} (h : IsConjRoot K 0 x)
  结论: x = 0
  证明: eq_zero_of_injective h (algebraMap K S).injective

Depends on / 依赖: algebraMap, eq_zero_of_injective, injective
-/
theorem eq_zero {x : S} (h : IsConjRoot K 0 x) : x = 0 :=
  eq_zero_of_injective h (algebraMap K S).injective

end IsConjRoot

/--
theorem `isConjRoot_iff_eq_algebraMap_of_injective` / 定理 `isConjRoot_iff_eq_algebraMap_of_injective`

English:
theorem isConjRoot_iff_eq_algebraMap_of_injective
  statement: [IsDomain R] [IsTorsionFree R S] {r : R}
  proof: ⟨fun h => eq_algebraMap_of_injective h hf, fun h => h.symm ▸ rfl⟩

中文:
定理 isConjRoot_iff_eq_algebraMap_of_injective
  结论: [是整环 R] [是无挠 R S] {r : R}
  证明: ⟨fun h => eq_algebraMap_of_injective h hf, fun h => h.symm ▸ rfl⟩

Depends on / 依赖: eq_algebraMap_of_injective, h.symm
-/
theorem isConjRoot_iff_eq_algebraMap_of_injective [IsDomain R] [IsTorsionFree R S] {r : R}
    {x : S} (hf : Function.Injective (algebraMap R S)) :
    IsConjRoot R (algebraMap R S r) x ↔ x = algebraMap R S r :=
  ⟨fun h => eq_algebraMap_of_injective h hf, fun h => h.symm ▸ rfl⟩

/--
An element `x` is a conjugate root of some element `algebraMap R S r` in the image of the base ring
if and only if `x = algebraMap R S r`.
-/
@[simp]
/--
theorem `isConjRoot_iff_eq_algebraMap` / 定理 `isConjRoot_iff_eq_algebraMap`

English:
theorem isConjRoot_iff_eq_algebraMap
  given: {r : K} {x : S}
  proof: isConjRoot_iff_eq_algebraMap_of_injective (algebraMap K S).injective

中文:
定理 isConjRoot_iff_eq_algebraMap
  条件: {r : K} {x : S}
  证明: isConjRoot_iff_eq_algebraMap_of_injective (algebraMap K S).injective

Depends on / 依赖: algebraMap, injective, isConjRoot_iff_eq_algebraMap_of_injective
-/
theorem isConjRoot_iff_eq_algebraMap {r : K} {x : S} :
    IsConjRoot K (algebraMap K S r) x ↔ x = algebraMap K S r :=
  isConjRoot_iff_eq_algebraMap_of_injective (algebraMap K S).injective

/--
A variant of `isConjRoot_iff_eq_algebraMap`.
an element `algebraMap R S r` in the image of the base ring is a conjugate root of an element `x`
if and only if `x = algebraMap R S r`.
-/
@[simp]
/--
theorem `isConjRoot_iff_eq_algebraMap'` / 定理 `isConjRoot_iff_eq_algebraMap'`

English:
theorem isConjRoot_iff_eq_algebraMap'
  given: {r : K} {x : S}
  proof: eq_comm.trans isConjRoot_iff_eq_algebraMap_of_injective (algebraMap K S).injective

中文:
定理 isConjRoot_iff_eq_algebraMap'
  条件: {r : K} {x : S}
  证明: eq_comm.trans isConjRoot_iff_eq_algebraMap_of_injective (algebraMap K S).injective

Depends on / 依赖: algebraMap, eq_comm, eq_comm.trans, injective, isConjRoot_iff_eq_algebraMap_of_injective
-/
theorem isConjRoot_iff_eq_algebraMap' {r : K} {x : S} :
    IsConjRoot K x (algebraMap K S r) ↔ x = algebraMap K S r :=
eq_comm.trans isConjRoot_iff_eq_algebraMap_of_injective (algebraMap K S).injective

/--
theorem `isConjRoot_zero_iff_eq_zero_of_injective` / 定理 `isConjRoot_zero_iff_eq_zero_of_injective`

English:
theorem isConjRoot_zero_iff_eq_zero_of_injective
  statement: [IsDomain R] {x : S} [IsTorsionFree R S]
  proof: ⟨fun h => eq_zero_of_injective h hf, fun h => h.symm ▸ rfl⟩

中文:
定理 isConjRoot_zero_iff_eq_zero_of_injective
  结论: [是整环 R] {x : S} [是无挠 R S]
  证明: ⟨fun h => eq_zero_of_injective h hf, fun h => h.symm ▸ rfl⟩

Depends on / 依赖: eq_zero_of_injective, h.symm
-/
theorem isConjRoot_zero_iff_eq_zero_of_injective [IsDomain R] {x : S} [IsTorsionFree R S]
    (hf : Function.Injective (algebraMap R S)) : IsConjRoot R 0 x ↔ x = 0 :=
  ⟨fun h => eq_zero_of_injective h hf, fun h => h.symm ▸ rfl⟩

/--
`x` is a conjugate root of `0` if and only if `x = 0`.
-/
@[simp]
/--
theorem `isConjRoot_zero_iff_eq_zero` / 定理 `isConjRoot_zero_iff_eq_zero`

English:
theorem isConjRoot_zero_iff_eq_zero
  given: {x : S}
  statement: IsConjRoot K 0 x ↔ x = 0
  proof: isConjRoot_zero_iff_eq_zero_of_injective (algebraMap K S).injective

中文:
定理 isConjRoot_zero_iff_eq_zero
  条件: {x : S}
  结论: IsConjRoot K 0 x ↔ x = 0
  证明: isConjRoot_zero_iff_eq_zero_of_injective (algebraMap K S).injective

Depends on / 依赖: algebraMap, injective, isConjRoot_zero_iff_eq_zero_of_injective
-/
theorem isConjRoot_zero_iff_eq_zero {x : S} : IsConjRoot K 0 x ↔ x = 0 :=
  isConjRoot_zero_iff_eq_zero_of_injective (algebraMap K S).injective

/--
A variant of `IsConjRoot.iff_eq_zero`. `0` is a conjugate root of `x` if and only if `x = 0`.
-/
@[simp]
/--
theorem `isConjRoot_zero_iff_eq_zero'` / 定理 `isConjRoot_zero_iff_eq_zero'`

English:
theorem isConjRoot_zero_iff_eq_zero'
  given: {x : S}
  statement: IsConjRoot K x 0 ↔ x = 0
  proof: eq_comm.trans isConjRoot_zero_iff_eq_zero_of_injective (algebraMap K S).injective

中文:
定理 isConjRoot_zero_iff_eq_zero'
  条件: {x : S}
  结论: IsConjRoot K x 0 ↔ x = 0
  证明: eq_comm.trans isConjRoot_zero_iff_eq_zero_of_injective (algebraMap K S).injective

Depends on / 依赖: algebraMap, eq_comm, eq_comm.trans, injective, isConjRoot_zero_iff_eq_zero_of_injective
-/
theorem isConjRoot_zero_iff_eq_zero' {x : S} : IsConjRoot K x 0 ↔ x = 0 :=
eq_comm.trans isConjRoot_zero_iff_eq_zero_of_injective (algebraMap K S).injective

namespace IsConjRoot

/--
theorem `ne_zero_of_injective` / 定理 `ne_zero_of_injective`

English:
theorem ne_zero_of_injective
  statement: [IsDomain R] [IsTorsionFree R S] {x y : S} (hx : x != 0)
  proof: fun g => hx (eq_zero_of_injective (g ▸ h.symm) hf)

中文:
定理 ne_zero_of_injective
  结论: [是整环 R] [是无挠 R S] {x y : S} (hx : x != 0)
  证明: fun g => hx (eq_zero_of_injective (g ▸ h.symm) hf)

Depends on / 依赖: eq_zero_of_injective, h.symm
-/
theorem ne_zero_of_injective [IsDomain R] [IsTorsionFree R S] {x y : S} (hx : x != 0)
    (h : IsConjRoot R x y) (hf : Function.Injective (algebraMap R S)) : y != 0 :=
  fun g => hx (eq_zero_of_injective (g ▸ h.symm) hf)

/--
theorem `ne_zero` / 定理 `ne_zero`

English:
theorem ne_zero
  given: {x y : S} (hx : x != 0) (h : IsConjRoot K x y)
  statement: y != 0
  proof: ne_zero_of_injective hx h (algebraMap K S).injective

中文:
定理 ne_zero
  条件: {x y : S} (hx : x != 0) (h : IsConjRoot K x y)
  结论: y != 0
  证明: ne_zero_of_injective hx h (algebraMap K S).injective

Depends on / 依赖: algebraMap, injective, ne_zero_of_injective
-/
theorem ne_zero {x y : S} (hx : x != 0) (h : IsConjRoot K x y) : y != 0 :=
  ne_zero_of_injective hx h (algebraMap K S).injective

end IsConjRoot

/--
theorem `notMem_iff_exists_ne_and_isConjRoot` / 定理 `notMem_iff_exists_ne_and_isConjRoot`

English:
theorem notMem_iff_exists_ne_and_isConjRoot
  statement: {x : L} (h : IsSeparable K x)
  proof: by
  calc
    _ ↔ 2 <= (minpoly K x).natDegree := (minpoly.two_le_natDegree_iff h.isIntegral).symm
    _ ↔ 2 <= Fintype.card ((minpoly K x).rootSet L) :=
      (Polynomial.card_rootSet_eq_natDegree h sp) ▸ Iff.rfl
    _ ↔ Nontrivial ((minpoly K x).rootSet L) := Fintype.one_lt_card_iff_nontrivial
    _ ↔ exists y : ((minpoly K x).rootSet L), ↑y != x :=
      (nontrivial_iff_exists_ne ⟨x, mem_rootSet.mpr ⟨minpoly.ne_zero h.isIntegral,
          minpoly.aeval K x⟩⟩).trans ⟨fun ⟨y, hy⟩ => ⟨y, Subtype.coe_ne_coe.mpr hy⟩,
          fun ⟨y, hy⟩ => ⟨y, Subtype.coe_ne_coe.mp hy⟩⟩
    _ ↔ _ :=
      ⟨fun ⟨⟨y, hy⟩, hne⟩ => ⟨y, ⟨hne.symm,
          (isConjRoot_iff_mem_minpoly_rootSet h.isIntegral).mpr hy⟩⟩,
          fun ⟨y, hne, hy⟩ => ⟨⟨y,
          (isConjRoot_iff_mem_minpoly_rootSet h.isIntegral).mp hy⟩, hne.symm⟩⟩

中文:
定理 notMem_iff_存在_ne_and_isConjRoot
  结论: {x : L} (h : 是可分 K x)
  证明: by
  calc
    _ ↔ 2 <= (minpoly K x).natDegree := (minpoly.two_le_natDegree_iff h.isIntegral).symm
    _ ↔ 2 <= Fintype.card ((minpoly K x).rootSet L) :=
      (Polynomial.card_rootSet_eq_natDegree h sp) ▸ Iff.rfl
    _ ↔ Nontrivial ((minpoly K x).rootSet L) := Fintype.one_lt_card_iff_nontrivial
    _ ↔ exists y : ((minpoly K x).rootSet L), ↑y != x :=
      (nontrivial_iff_exists_ne ⟨x, mem_rootSet.mpr ⟨minpoly.ne_zero h.isIntegral,
          minpoly.aeval K x⟩⟩).trans ⟨fun ⟨y, hy⟩ => ⟨y, Subtype.coe_ne_coe.mpr hy⟩,
          fun ⟨y, hy⟩ => ⟨y, Subtype.coe_ne_coe.mp hy⟩⟩
    _ ↔ _ :=
      ⟨fun ⟨⟨y, hy⟩, hne⟩ => ⟨y, ⟨hne.symm,
          (isConjRoot_iff_mem_minpoly_rootSet h.isIntegral).mpr hy⟩⟩,
          fun ⟨y, hne, hy⟩ => ⟨⟨y,
          (isConjRoot_iff_mem_minpoly_rootSet h.isIntegral).mp hy⟩, hne.symm⟩⟩

Depends on / 依赖: Fintype, Fintype.card, Fintype.one_lt_card_iff_nontrivial, Iff.rfl, Nontrivial, Polynomial, Polynomial.card_rootSet_eq_natDegree, Subtype, Subtype.coe_ne_coe.mpr, card_rootSet_eq_natDegree, coe_ne_coe, h.isIntegral, isIntegral, mem_rootSet, mem_rootSet.mpr, minpoly, minpoly.aeval, minpoly.ne_zero, minpoly.two_le_natDegree_iff, natDegree
-/
theorem notMem_iff_exists_ne_and_isConjRoot {x : L} (h : IsSeparable K x)
    (sp : ((minpoly K x).map (algebraMap K L)).Splits) :
    x ∉ (⊥ : Subalgebra K L) ↔ exists y : L, x != y ∧ IsConjRoot K x y := by
  calc
    _ ↔ 2 <= (minpoly K x).natDegree := (minpoly.two_le_natDegree_iff h.isIntegral).symm
    _ ↔ 2 <= Fintype.card ((minpoly K x).rootSet L) :=
      (Polynomial.card_rootSet_eq_natDegree h sp) ▸ Iff.rfl
    _ ↔ Nontrivial ((minpoly K x).rootSet L) := Fintype.one_lt_card_iff_nontrivial
    _ ↔ exists y : ((minpoly K x).rootSet L), ↑y != x :=
      (nontrivial_iff_exists_ne ⟨x, mem_rootSet.mpr ⟨minpoly.ne_zero h.isIntegral,
          minpoly.aeval K x⟩⟩).trans ⟨fun ⟨y, hy⟩ => ⟨y, Subtype.coe_ne_coe.mpr hy⟩,
          fun ⟨y, hy⟩ => ⟨y, Subtype.coe_ne_coe.mp hy⟩⟩
    _ ↔ _ :=
      ⟨fun ⟨⟨y, hy⟩, hne⟩ => ⟨y, ⟨hne.symm,
          (isConjRoot_iff_mem_minpoly_rootSet h.isIntegral).mpr hy⟩⟩,
          fun ⟨y, hne, hy⟩ => ⟨⟨y,
          (isConjRoot_iff_mem_minpoly_rootSet h.isIntegral).mp hy⟩, hne.symm⟩⟩
