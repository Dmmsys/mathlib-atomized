/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.Ideal
public import Mathlib.Algebra.Lie.Basic

/-!
# Direct sums of Lie algebras and Lie modules

Direct sums of Lie algebras and Lie modules carry natural algebra and module structures.

## Tags

lie algebra, lie module, direct sum
-/

@[expose] public section


universe u v w w₁

namespace DirectSum

open DFinsupp

open scoped DirectSum

variable {R : Type u} {ι : Type v} [CommRing R]

section Modules

/-! The direct sum of Lie modules over a fixed Lie algebra carries a natural Lie module
structure. -/


variable {L : Type w₁} {M : ι -> Type w}
variable [LieRing L] [LieAlgebra R L]
variable [forall i, AddCommGroup (M i)] [forall i, Module R (M i)]
variable [forall i, LieRingModule L (M i)] [forall i, LieModule R L (M i)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LieRingModule L (⨁ i, M i)
  body: m.mapRange (fun _ m' => ⁅x, m'⁆) fun _ => lie_zero x
  add_lie x y m := by
    ext
    simp only [mapRange_apply, add_apply, add_lie]
  lie_add x m n := by
    ext
    simp only [mapRange_apply, add_apply, lie_add]
  leibniz_lie x y m := by
    ext
    simp only [mapRange_apply, lie_lie, add_apply, 

中文:
实例 :
  签名: LieRingModule L (⨁ i, M i)
  定义体: m.mapRange (fun _ m' => ⁅x, m'⁆) fun _ => lie_zero x
  add_lie x y m := by
    ext
    simp only [mapRange_apply, add_apply, add_lie]
  lie_add x m n := by
    ext
    simp only [mapRange_apply, add_apply, lie_add]
  leibniz_lie x y m := by
    ext
    simp only [mapRange_apply, lie_lie, add_apply, 

Depends on / 依赖: lie_zero, m.mapRange, mapRange
-/
instance : LieRingModule L (⨁ i, M i) where
  bracket x m := m.mapRange (fun _ m' => ⁅x, m'⁆) fun _ => lie_zero x
  add_lie x y m := by
    ext
    simp only [mapRange_apply, add_apply, add_lie]
  lie_add x m n := by
    ext
    simp only [mapRange_apply, add_apply, lie_add]
  leibniz_lie x y m := by
    ext
    simp only [mapRange_apply, lie_lie, add_apply, sub_add_cancel]

@[simp]
/--
theorem `lie_module_bracket_apply` / 定理 `lie_module_bracket_apply`

English:
theorem lie_module_bracket_apply
  given: (x : L) (m : ⨁ i, M i) (i : ι)
  statement: ⁅x, m⁆ i = ⁅x, m i⁆
  proof: mapRange_apply _ _ m i

中文:
定理 lie_module_bracket_apply
  条件: (x : L) (m : ⨁ i, M i) (i : ι)
  结论: ⁅x, m⁆ i = ⁅x, m i⁆
  证明: mapRange_apply _ _ m i

Depends on / 依赖: mapRange_apply
-/
theorem lie_module_bracket_apply (x : L) (m : ⨁ i, M i) (i : ι) : ⁅x, m⁆ i = ⁅x, m i⁆ :=
  mapRange_apply _ _ m i

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LieModule R L (⨁ i, M i)
  body: by
    ext
    simp only [smul_lie, lie_module_bracket_apply, smul_apply]
  lie_smul t x m := by
    ext
    simp only [lie_smul, lie_module_bracket_apply, smul_apply]

中文:
实例 :
  签名: LieModule R L (⨁ i, M i)
  定义体: by
    ext
    simp only [smul_lie, lie_module_bracket_apply, smul_apply]
  lie_smul t x m := by
    ext
    simp only [lie_smul, lie_module_bracket_apply, smul_apply]

Depends on / 依赖: lie_module_bracket_apply, lie_smul, smul_apply, smul_lie
-/
instance : LieModule R L (⨁ i, M i) where
  smul_lie t x m := by
    ext
    simp only [smul_lie, lie_module_bracket_apply, smul_apply]
  lie_smul t x m := by
    ext
    simp only [lie_smul, lie_module_bracket_apply, smul_apply]

variable (R ι L M)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `lieModuleOf` / `lieModuleOf` 的定义

English:
definition lieModuleOf
  signature: [DecidableEq ι] (j : ι)
  body: { lof R ι M j with
    map_lie' := fun {x m} => by
      ext i
      by_cases h : j = i
      · rw [← h]; simp
      · -- This used to be the end of the proof before https://github.com/leanprover/lean4/pull/2644
        -- old proof `simp [lof, lsingle, h]`
        simp only [lof, lsingle, AddHom.to

中文:
定义 lieModuleOf
  签名: [DecidableEq ι] (j : ι)
  定义体: { lof R ι M j with
    map_lie' := fun {x m} => by
      ext i
      by_cases h : j = i
      · rw [← h]; simp
      · -- This used to be the end of the proof before https://github.com/leanprover/lean4/pull/2644
        -- old proof `simp [lof, lsingle, h]`
        simp only [lof, lsingle, AddHom.to

Depends on / 依赖: before, github, github.com, leanprover, map_lie
-/
def lieModuleOf [DecidableEq ι] (j : ι) : M j ->ₗ⁅R,L⁆ ⨁ i, M i :=
  { lof R ι M j with
    map_lie' := fun {x m} => by
      ext i
      by_cases h : j = i
      · rw [← h]; simp
      · -- This used to be the end of the proof before https://github.com/leanprover/lean4/pull/2644
        -- old proof `simp [lof, lsingle, h]`
        simp only [lof, lsingle, AddHom.toFun_eq_coe, lie_module_bracket_apply]
        -- The coercion in the goal is `DFunLike.coe (β := fun x ↦ Π₀ (i : ι), M i)`
        -- but the lemma is expecting `DFunLike.coe (β := fun x ↦ ⨁ (i : ι), M i)`
        erw [AddHom.coe_mk]
        simp [h] }

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `lieModuleComponent` / `lieModuleComponent` 的定义

English:
definition lieModuleComponent
  signature: (j : ι)
  body: { component R ι M j with
    map_lie' := fun {x m} => by simp [component, lapply] }

中文:
定义 lieModuleComponent
  签名: (j : ι)
  定义体: { component R ι M j with
    map_lie' := fun {x m} => by simp [component, lapply] }

Depends on / 依赖: component, lapply, map_lie
-/
def lieModuleComponent (j : ι) : (⨁ i, M i) ->ₗ⁅R,L⁆ M j :=
  { component R ι M j with
    map_lie' := fun {x m} => by simp [component, lapply] }

end Modules

section Algebras

/-! The direct sum of Lie algebras carries a natural Lie algebra structure. -/


variable (L : ι -> Type w)
variable [forall i, LieRing (L i)] [forall i, LieAlgebra R (L i)]

set_option backward.isDefEq.respectTransparency false in
/--
Instance `lieRing` / 实例 `lieRing`

English:
instance lieRing
  signature: : LieRing (⨁ i, L i)
  body: { (inferInstance : AddCommGroup _) with
    bracket := zipWith (fun _ => fun x y => ⁅x, y⁆) fun _ => lie_zero 0
    add_lie := fun x y z => by
      ext
      simp only [zipWith_apply, add_apply, add_lie]
    lie_add := fun x y z => by
      ext
      simp only [zipWith_apply, add_apply, lie_add]
  

中文:
实例 lieRing
  签名: : LieRing (⨁ i, L i)
  定义体: { (inferInstance : AddCommGroup _) with
    bracket := zipWith (fun _ => fun x y => ⁅x, y⁆) fun _ => lie_zero 0
    add_lie := fun x y z => by
      ext
      simp only [zipWith_apply, add_apply, add_lie]
    lie_add := fun x y z => by
      ext
      simp only [zipWith_apply, add_apply, lie_add]
  

Depends on / 依赖: AddCommGroup, add_apply, add_lie, bracket, leibniz_lie, lie_add, lie_self, lie_zero, zero_apply, zipWith, zipWith_apply
-/
instance lieRing : LieRing (⨁ i, L i) :=
  { (inferInstance : AddCommGroup _) with
    bracket := zipWith (fun _ => fun x y => ⁅x, y⁆) fun _ => lie_zero 0
    add_lie := fun x y z => by
      ext
      simp only [zipWith_apply, add_apply, add_lie]
    lie_add := fun x y z => by
      ext
      simp only [zipWith_apply, add_apply, lie_add]
    lie_self := fun x => by
      ext
      simp only [zipWith_apply, lie_self, zero_apply]
    leibniz_lie := fun x y z => by
      ext
      simp only [zipWith_apply, add_apply]
      apply leibniz_lie }

@[simp]
/--
theorem `bracket_apply` / 定理 `bracket_apply`

English:
theorem bracket_apply
  given: (x y : ⨁ i, L i) (i : ι)
  statement: ⁅x, y⁆ i = ⁅x i, y i⁆
  proof: zipWith_apply _ _ x y i

中文:
定理 bracket_apply
  条件: (x y : ⨁ i, L i) (i : ι)
  结论: ⁅x, y⁆ i = ⁅x i, y i⁆
  证明: zipWith_apply _ _ x y i

Depends on / 依赖: zipWith_apply
-/
theorem bracket_apply (x y : ⨁ i, L i) (i : ι) : ⁅x, y⁆ i = ⁅x i, y i⁆ :=
  zipWith_apply _ _ x y i

/--
theorem `lie_of_same` / 定理 `lie_of_same`

English:
theorem lie_of_same
  given: [DecidableEq ι] {i : ι} (x y : L i)
  proof: DFinsupp.zipWith_single_single _ _ _ _

中文:
定理 lie_of_same
  条件: [DecidableEq ι] {i : ι} (x y : L i)
  证明: DFinsupp.zipWith_single_single _ _ _ _

Depends on / 依赖: DFinsupp, DFinsupp.zipWith_single_single, zipWith_single_single
-/
theorem lie_of_same [DecidableEq ι] {i : ι} (x y : L i) :
    ⁅of L i x, of L i y⁆ = of L i ⁅x, y⁆ :=
  DFinsupp.zipWith_single_single _ _ _ _

/--
theorem `lie_of_of_ne` / 定理 `lie_of_of_ne`

English:
theorem lie_of_of_ne
  given: [DecidableEq ι] {i j : ι} (hij : i != j) (x : L i) (y : L j)
  proof: by
  ext k
  rw [bracket_apply]
  obtain rfl | hik := Decidable.eq_or_ne k i
  · rw [of_eq_of_ne _ _ _ hij, lie_zero, zero_apply]
  · rw [of_eq_of_ne _ _ _ hik, zero_lie, zero_apply]

@[simp]

中文:
定理 lie_of_of_ne
  条件: [DecidableEq ι] {i j : ι} (hij : i != j) (x : L i) (y : L j)
  证明: by
  ext k
  rw [bracket_apply]
  obtain rfl | hik := Decidable.eq_or_ne k i
  · rw [of_eq_of_ne _ _ _ hij, lie_zero, zero_apply]
  · rw [of_eq_of_ne _ _ _ hik, zero_lie, zero_apply]

@[simp]

Depends on / 依赖: Decidable, Decidable.eq_or_ne, bracket_apply, eq_or_ne, lie_zero, of_eq_of_ne, zero_apply, zero_lie
-/
theorem lie_of_of_ne [DecidableEq ι] {i j : ι} (hij : i != j) (x : L i) (y : L j) :
    ⁅of L i x, of L j y⁆ = 0 := by
  ext k
  rw [bracket_apply]
  obtain rfl | hik := Decidable.eq_or_ne k i
  · rw [of_eq_of_ne _ _ _ hij, lie_zero, zero_apply]
  · rw [of_eq_of_ne _ _ _ hik, zero_lie, zero_apply]

@[simp]
/--
theorem `lie_of` / 定理 `lie_of`

English:
theorem lie_of
  given: [DecidableEq ι] {i j : ι} (x : L i) (y : L j)
  proof: by
  obtain rfl | hij := Decidable.eq_or_ne i j
  · simp only [lie_of_same L x y, dif_pos]
  · simp only [lie_of_of_ne L hij x y, hij, dite_false]

中文:
定理 lie_of
  条件: [DecidableEq ι] {i j : ι} (x : L i) (y : L j)
  证明: by
  obtain rfl | hij := Decidable.eq_or_ne i j
  · simp only [lie_of_same L x y, dif_pos]
  · simp only [lie_of_of_ne L hij x y, hij, dite_false]

Depends on / 依赖: Decidable, Decidable.eq_or_ne, dif_pos, dite_false, eq_or_ne, lie_of_of_ne, lie_of_same
-/
theorem lie_of [DecidableEq ι] {i j : ι} (x : L i) (y : L j) :
    ⁅of L i x, of L j y⁆ = if hij : i = j then of L i ⁅x, hij.symm.recOn y⁆ else 0 := by
  obtain rfl | hij := Decidable.eq_or_ne i j
  · simp only [lie_of_same L x y, dif_pos]
  · simp only [lie_of_of_ne L hij x y, hij, dite_false]

/--
Instance `lieAlgebra` / 实例 `lieAlgebra`

English:
instance lieAlgebra
  signature: : LieAlgebra R (⨁ i, L i)
  body: { (inferInstance : Module R _) with
    lie_smul := fun c x y => by
      ext
      simp only [smul_apply, bracket_apply, lie_smul] }

中文:
实例 lieAlgebra
  签名: : LieAlgebra R (⨁ i, L i)
  定义体: { (inferInstance : Module R _) with
    lie_smul := fun c x y => by
      ext
      simp only [smul_apply, bracket_apply, lie_smul] }

Depends on / 依赖: Module, bracket_apply, lie_smul, smul_apply
-/
instance lieAlgebra : LieAlgebra R (⨁ i, L i) :=
  { (inferInstance : Module R _) with
    lie_smul := fun c x y => by
      ext
      simp only [smul_apply, bracket_apply, lie_smul] }

variable (R ι)

/-- The inclusion of each component into the direct sum as morphism of Lie algebras. -/
@[simps]
/--
Definition of `lieAlgebraOf` / `lieAlgebraOf` 的定义

English:
definition lieAlgebraOf
  signature: [DecidableEq ι] (j : ι)
  body: { lof R ι L j with
    toFun := of L j
    map_lie' := fun {x y} => (lie_of_same L x y).symm }

中文:
定义 lieAlgebraOf
  签名: [DecidableEq ι] (j : ι)
  定义体: { lof R ι L j with
    toFun := of L j
    map_lie' := fun {x y} => (lie_of_same L x y).symm }

Depends on / 依赖: lie_of_same, map_lie
-/
def lieAlgebraOf [DecidableEq ι] (j : ι) : L j ->ₗ⁅R⁆ ⨁ i, L i :=
  { lof R ι L j with
    toFun := of L j
    map_lie' := fun {x y} => (lie_of_same L x y).symm }

set_option backward.isDefEq.respectTransparency false in
/-- The projection map onto one component, as a morphism of Lie algebras. -/
@[simps]
/--
Definition of `lieAlgebraComponent` / `lieAlgebraComponent` 的定义

English:
definition lieAlgebraComponent
  signature: (j : ι)
  body: { component R ι L j with
    toFun := component R ι L j
    map_lie' := fun {x y} => by simp [component, lapply] }

中文:
定义 lieAlgebraComponent
  签名: (j : ι)
  定义体: { component R ι L j with
    toFun := component R ι L j
    map_lie' := fun {x y} => by simp [component, lapply] }

Depends on / 依赖: component, lapply, map_lie
-/
def lieAlgebraComponent (j : ι) : (⨁ i, L i) ->ₗ⁅R⁆ L j :=
  { component R ι L j with
    toFun := component R ι L j
    map_lie' := fun {x y} => by simp [component, lapply] }

-- Note(kmill): `ext` cannot generate an iff theorem here since `x` and `y` do not determine `R`.
@[ext (iff := false)]
/--
theorem `lieAlgebra_ext` / 定理 `lieAlgebra_ext`

English:
theorem lieAlgebra_ext
  statement: {x y : ⨁ i, L i}
  proof: DFinsupp.ext h

中文:
定理 lieAlgebra_ext
  结论: {x y : ⨁ i, L i}
  证明: DFinsupp.ext h

Depends on / 依赖: DFinsupp, DFinsupp.ext
-/
theorem lieAlgebra_ext {x y : ⨁ i, L i}
    (h : forall i, lieAlgebraComponent R ι L i x = lieAlgebraComponent R ι L i y) : x = y :=
  DFinsupp.ext h

variable {R L ι}

/-- Given a family of Lie algebras `L i`, together with a family of morphisms of Lie algebras
`f i : L i →ₗ⁅R⁆ L'` into a fixed Lie algebra `L'`, we have a natural linear map:
`(⨁ i, L i) →ₗ[R] L'`. If in addition `⁅f i x, f j y⁆ = 0` for any `x ∈ L i` and `y ∈ L j` (`i ≠ j`)
then this map is a morphism of Lie algebras. -/
@[simps]
/--
Definition of `toLieAlgebra` / `toLieAlgebra` 的定义

English:
definition toLieAlgebra
  signature: [DecidableEq ι] (L' : Type w₁) [LieRing L'] [LieAlgebra R L']
  body: { toModule R ι L' fun i => (f i : L i ->ₗ[R] L') with
    toFun := toModule R ι L' fun i => (f i : L i ->ₗ[R] L')
    map_lie' := fun {x y} => by
      let f' i := (f i : L i ->ₗ[R] L')
      /- The goal is linear in `y`. We can use this to reduce to the case that `y` has only one
        non-zero c

中文:
定义 toLieAlgebra
  签名: [DecidableEq ι] (L' : Type w₁) [LieRing L'] [LieAlgebra R L']
  定义体: { toModule R ι L' fun i => (f i : L i ->ₗ[R] L') with
    toFun := toModule R ι L' fun i => (f i : L i ->ₗ[R] L')
    map_lie' := fun {x y} => by
      let f' i := (f i : L i ->ₗ[R] L')
      /- The goal is linear in `y`. We can use this to reduce to the case that `y` has only one
        non-zero c

Depends on / 依赖: map_lie, toModule
-/
def toLieAlgebra [DecidableEq ι] (L' : Type w₁) [LieRing L'] [LieAlgebra R L']
    (f : forall i, L i ->ₗ⁅R⁆ L') (hf : Pairwise fun i j => forall (x : L i) (y : L j), ⁅f i x, f j y⁆ = 0) :
    (⨁ i, L i) ->ₗ⁅R⁆ L' :=
  { toModule R ι L' fun i => (f i : L i ->ₗ[R] L') with
    toFun := toModule R ι L' fun i => (f i : L i ->ₗ[R] L')
    map_lie' := fun {x y} => by
      let f' i := (f i : L i ->ₗ[R] L')
      /- The goal is linear in `y`. We can use this to reduce to the case that `y` has only one
        non-zero component. -/
      suffices forall (i : ι) (y : L i),
          toModule R ι L' f' ⁅x, of L i y⁆ =
            ⁅toModule R ι L' f' x, toModule R ι L' f' (of L i y)⁆ by
        simp only [← LieAlgebra.ad_apply R]
        rw [← LinearMap.comp_apply]; rw [← LinearMap.comp_apply]
        congr; clear y; ext i y; exact this i y
      -- Similarly, we can reduce to the case that `x` has only one non-zero component.
      suffices forall (i j) (y : L i) (x : L j),
          toModule R ι L' f' ⁅of L j x, of L i y⁆ =
            ⁅toModule R ι L' f' (of L j x), toModule R ι L' f' (of L i y)⁆ by
        intro i y
        rw [← lie_skew x]; rw [← lie_skew (toModule R ι L' f' x)]
        simp only [map_neg, neg_inj, ← LieAlgebra.ad_apply R]
        rw [← LinearMap.comp_apply]; rw [← LinearMap.comp_apply]
        congr; clear x; ext j x; exact this j i x y
      intro i j y x
      simp only [f', coe_toModule_eq_coe_toAddMonoid, toAddMonoid_of]
      -- And finish with trivial case analysis.
      obtain rfl | hij := Decidable.eq_or_ne i j
      · simp_rw [lie_of_same, toAddMonoid_of, LinearMap.toAddMonoidHom_coe, LieHom.coe_toLinearMap,
          LieHom.map_lie]
      · simp_rw [lie_of_of_ne _ hij.symm, map_zero, LinearMap.toAddMonoidHom_coe,
          LieHom.coe_toLinearMap, hf hij.symm x y] }

end Algebras

section Ideals

variable {L : Type w} [LieRing L] [LieAlgebra R L] (I : ι -> LieIdeal R L)

/--
Instance `lieRingOfIdeals` / 实例 `lieRingOfIdeals`

English:
instance lieRingOfIdeals
  signature: : LieRing (⨁ i, I i)
  body: DirectSum.lieRing fun i => ↥(I i)

中文:
实例 lieRingOfIdeals
  签名: : LieRing (⨁ i, I i)
  定义体: DirectSum.lieRing fun i => ↥(I i)

Depends on / 依赖: DirectSum, DirectSum.lieRing, lieRing
-/
instance lieRingOfIdeals : LieRing (⨁ i, I i) :=
  DirectSum.lieRing fun i => ↥(I i)

/--
Instance `lieAlgebraOfIdeals` / 实例 `lieAlgebraOfIdeals`

English:
instance lieAlgebraOfIdeals
  signature: : LieAlgebra R (⨁ i, I i)
  body: DirectSum.lieAlgebra fun i => ↥(I i)

中文:
实例 lieAlgebraOfIdeals
  签名: : LieAlgebra R (⨁ i, I i)
  定义体: DirectSum.lieAlgebra fun i => ↥(I i)

Depends on / 依赖: DirectSum, DirectSum.lieAlgebra, lieAlgebra
-/
instance lieAlgebraOfIdeals : LieAlgebra R (⨁ i, I i) :=
  DirectSum.lieAlgebra fun i => ↥(I i)

end Ideals

end DirectSum
