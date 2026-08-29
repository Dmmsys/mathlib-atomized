/-
Copyright (c) 2020 Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Lutz
-/
module

public import Mathlib.FieldTheory.Galois.Basic

/-!
# Galois Groups of Polynomials

In this file, we introduce the Galois group of a polynomial `p` over a field `F`,
defined as the automorphism group of its splitting field. We also provide
some results about some extension `E` above `p.SplittingField`.

## Main definitions

- `Polynomial.Gal p`: the Galois group of a polynomial p.
- `Polynomial.Gal.restrict p E`: the restriction homomorphism `Gal(E/F) → gal p`.
- `Polynomial.Gal.galAction p E`: the action of `gal p` on the roots of `p` in `E`.

## Main results

- `Polynomial.Gal.restrict_smul`: `restrict p E` is compatible with `gal_action p E`.
- `Polynomial.Gal.galActionHom_injective`: `gal p` acting on the roots of `p` in `E` is faithful.
- `Polynomial.Gal.restrictProd_injective`: `gal (p * q)` embeds as a subgroup of `gal p × gal q`.
- `Polynomial.Gal.card_of_separable`: For a separable polynomial, its Galois group has cardinality
  equal to the dimension of its splitting field over `F`.
- `Polynomial.Gal.galActionHom_bijective_of_prime_degree`:
  An irreducible polynomial of prime degree with two non-real roots has full Galois group.

## Other results
- `Polynomial.Gal.card_complex_roots_eq_card_real_add_card_not_gal_inv`: The number of complex roots
  equals the number of real roots plus the number of roots not fixed by complex conjugation
  (i.e. with some imaginary component).

-/

@[expose] public section

assert_not_exists Real

noncomputable section

open scoped Polynomial

open Module

namespace Polynomial

variable {F : Type*} [Field F] (p q : F[X]) (E : Type*) [Field E] [Algebra F E]

/--
Definition of `Gal` / `Gal` 的定义

English:
definition Gal
  body: p.SplittingField ≃ₐ[F] p.SplittingField
deriving Group, Fintype, EquivLike, AlgEquivClass, MulSemiringAction _ p.SplittingField

中文:
定义 Gal
  定义体: p.SplittingField ≃ₐ[F] p.SplittingField
deriving Group, Fintype, EquivLike, AlgEquivClass, MulSemiringAction _ p.SplittingField

Depends on / 依赖: SplittingField, p.SplittingField
-/
def Gal :=
  p.SplittingField ≃ₐ[F] p.SplittingField
deriving Group, Fintype, EquivLike, AlgEquivClass, MulSemiringAction _ p.SplittingField

namespace Gal

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {σ τ : p.Gal} (h : forall x in p.rootSet p.SplittingField, σ x = τ x)
  statement: σ = τ
  proof: by
  refine
    AlgEquiv.ext fun x =>
      (AlgHom.mem_equalizer σ.toAlgHom τ.toAlgHom x).mp
        ((SetLike.ext_iff.mp ?_ x).mpr Algebra.mem_top)
  rwa [eq_top_iff, ← SplittingField.adjoin_rootSet, Algebra.adjoin_le_iff]

中文:
定理 ext
  条件: {σ τ : p.Gal} (h : 对任意 x in p.rootSet p.分裂域, σ x = τ x)
  结论: σ = τ
  证明: by
  refine
    AlgEquiv.ext fun x =>
      (AlgHom.mem_equalizer σ.toAlgHom τ.toAlgHom x).mp
        ((SetLike.ext_iff.mp ?_ x).mpr Algebra.mem_top)
  rwa [eq_top_iff, ← SplittingField.adjoin_rootSet, Algebra.adjoin_le_iff]

Depends on / 依赖: AlgEquiv, AlgEquiv.ext, AlgHom, AlgHom.mem_equalizer, Algebra, Algebra.adjoin_le_iff, Algebra.mem_top, SetLike, SetLike.ext_iff.mp, SplittingField, SplittingField.adjoin_rootSet, adjoin_le_iff, adjoin_rootSet, eq_top_iff, ext_iff, mem_equalizer, mem_top, toAlgHom
-/
theorem ext {σ τ : p.Gal} (h : forall x in p.rootSet p.SplittingField, σ x = τ x) : σ = τ := by
  refine
    AlgEquiv.ext fun x =>
      (AlgHom.mem_equalizer σ.toAlgHom τ.toAlgHom x).mp
        ((SetLike.ext_iff.mp ?_ x).mpr Algebra.mem_top)
  rwa [eq_top_iff, ← SplittingField.adjoin_rootSet, Algebra.adjoin_le_iff]

set_option backward.isDefEq.respectTransparency.types false in
/-- If `p` splits in `F` then the `p.gal` is trivial. -/
@[instance_reducible]
/--
Definition of `uniqueGalOfSplits` / `uniqueGalOfSplits` 的定义

English:
definition uniqueGalOfSplits
  signature: (h : p.Splits)
  body: 1
  uniq f :=
    AlgEquiv.ext fun x => by
      obtain ⟨y, rfl⟩ :=
        Algebra.mem_bot.mp
          ((SetLike.ext_iff.mp ((IsSplittingField.splits_iff _ p).mp h) x).mp Algebra.mem_top)
      rw [AlgEquiv.commutes]; rw [AlgEquiv.commutes]

中文:
定义 uniqueGalOfSplits
  签名: (h : p.Splits)
  定义体: 1
  uniq f :=
    AlgEquiv.ext fun x => by
      obtain ⟨y, rfl⟩ :=
        Algebra.mem_bot.mp
          ((SetLike.ext_iff.mp ((IsSplittingField.splits_iff _ p).mp h) x).mp Algebra.mem_top)
      rw [AlgEquiv.commutes]; rw [AlgEquiv.commutes]
-/
def uniqueGalOfSplits (h : p.Splits) : Unique p.Gal where
  default := 1
  uniq f :=
    AlgEquiv.ext fun x => by
      obtain ⟨y, rfl⟩ :=
        Algebra.mem_bot.mp
          ((SetLike.ext_iff.mp ((IsSplittingField.splits_iff _ p).mp h) x).mp Algebra.mem_top)
      rw [AlgEquiv.commutes]; rw [AlgEquiv.commutes]

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [h
  signature: : Fact p.Splits] : Unique p.Gal
  body: uniqueGalOfSplits _ h.1

中文:
实例 [h
  签名: : Fact p.Splits] : 唯一 p.Gal
  定义体: uniqueGalOfSplits _ h.1

Depends on / 依赖: uniqueGalOfSplits
-/
instance [h : Fact p.Splits] : Unique p.Gal :=
  uniqueGalOfSplits _ h.1

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `uniqueGalZero` / 实例 `uniqueGalZero`

English:
instance uniqueGalZero
  signature: : Unique (0 : F[X]).Gal
  body: uniqueGalOfSplits _ (by simp)

中文:
实例 uniqueGalZero
  签名: : 唯一 (0 : F[X]).Gal
  定义体: uniqueGalOfSplits _ (by simp)

Depends on / 依赖: uniqueGalOfSplits
-/
instance uniqueGalZero : Unique (0 : F[X]).Gal :=
  uniqueGalOfSplits _ (by simp)

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `uniqueGalOne` / 实例 `uniqueGalOne`

English:
instance uniqueGalOne
  signature: : Unique (1 : F[X]).Gal
  body: uniqueGalOfSplits _ Splits.one

中文:
实例 uniqueGalOne
  签名: : 唯一 (1 : F[X]).Gal
  定义体: uniqueGalOfSplits _ Splits.one

Depends on / 依赖: Splits, Splits.one, uniqueGalOfSplits
-/
instance uniqueGalOne : Unique (1 : F[X]).Gal :=
  uniqueGalOfSplits _ Splits.one

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `uniqueGalC` / 实例 `uniqueGalC`

English:
instance uniqueGalC
  signature: (x : F)
  body: uniqueGalOfSplits _ (by simp)

中文:
实例 uniqueGalC
  签名: (x : F)
  定义体: uniqueGalOfSplits _ (by simp)

Depends on / 依赖: uniqueGalOfSplits
-/
instance uniqueGalC (x : F) : Unique (C x).Gal :=
  uniqueGalOfSplits _ (by simp)

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `uniqueGalX` / 实例 `uniqueGalX`

English:
instance uniqueGalX
  signature: : Unique (X : F[X]).Gal
  body: uniqueGalOfSplits _ Splits.X

中文:
实例 uniqueGalX
  签名: : 唯一 (X : F[X]).Gal
  定义体: uniqueGalOfSplits _ Splits.X

Depends on / 依赖: Splits, Splits.X, uniqueGalOfSplits
-/
instance uniqueGalX : Unique (X : F[X]).Gal :=
  uniqueGalOfSplits _ Splits.X

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `uniqueGalXSubC` / 实例 `uniqueGalXSubC`

English:
instance uniqueGalXSubC
  signature: (x : F)
  body: uniqueGalOfSplits _ (Splits.X_sub_C _)

中文:
实例 uniqueGalXSubC
  签名: (x : F)
  定义体: uniqueGalOfSplits _ (Splits.X_sub_C _)

Depends on / 依赖: Splits, Splits.X_sub_C, X_sub_C, uniqueGalOfSplits
-/
instance uniqueGalXSubC (x : F) : Unique (X - C x).Gal :=
  uniqueGalOfSplits _ (Splits.X_sub_C _)

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `uniqueGalXPow` / 实例 `uniqueGalXPow`

English:
instance uniqueGalXPow
  signature: (n : Nat)
  body: uniqueGalOfSplits _ (Splits.X_pow _)

中文:
实例 uniqueGalXPow
  签名: (n : 自然数)
  定义体: uniqueGalOfSplits _ (Splits.X_pow _)

Depends on / 依赖: Splits, Splits.X_pow, X_pow, uniqueGalOfSplits
-/
instance uniqueGalXPow (n : Nat) : Unique (X ^ n : F[X]).Gal :=
  uniqueGalOfSplits _ (Splits.X_pow _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [h
  signature: : Fact ((p.map (algebraMap F E)).Splits)] : Algebra p.SplittingField E
  body: (IsSplittingField.lift p.SplittingField p h.1).toRingHom.toAlgebra

中文:
实例 [h
  签名: : Fact ((p.map (algebraMap F E)).Splits)] : 代数 p.分裂域 E
  定义体: (IsSplittingField.lift p.SplittingField p h.1).toRingHom.toAlgebra

Depends on / 依赖: IsSplittingField, IsSplittingField.lift, SplittingField, p.SplittingField, toAlgebra, toRingHom, toRingHom.toAlgebra
-/
instance [h : Fact ((p.map (algebraMap F E)).Splits)] : Algebra p.SplittingField E :=
  (IsSplittingField.lift p.SplittingField p h.1).toRingHom.toAlgebra

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [h
  signature: : Fact ((p.map (algebraMap F E)).Splits)] : IsScalarTower F p.SplittingField E
  body: IsScalarTower.of_algebraMap_eq fun x =>
    ((IsSplittingField.lift p.SplittingField p h.1).commutes x).symm

中文:
实例 [h
  签名: : Fact ((p.map (algebraMap F E)).Splits)] : 标量塔 F p.分裂域 E
  定义体: IsScalarTower.of_algebraMap_eq fun x =>
    ((IsSplittingField.lift p.SplittingField p h.1).commutes x).symm

Depends on / 依赖: IsScalarTower, IsScalarTower.of_algebraMap_eq, IsSplittingField, IsSplittingField.lift, SplittingField, commutes, of_algebraMap_eq, p.SplittingField
-/
instance [h : Fact ((p.map (algebraMap F E)).Splits)] : IsScalarTower F p.SplittingField E :=
  IsScalarTower.of_algebraMap_eq fun x =>
    ((IsSplittingField.lift p.SplittingField p h.1).commutes x).symm

-- The `Algebra p.SplittingField E` instance above behaves badly when
-- `E := p.SplittingField`, since it may result in a unification problem
-- `IsSplittingField.lift.toRingHom.toAlgebra =?= Algebra.id`,
-- which takes an extremely long time to resolve, causing timeouts.
-- Since we don't really care about this definition, marking it as irreducible
-- causes that unification to error out early.
/--
Definition of `restrict` / `restrict` 的定义

English:
definition restrict
  signature: [Fact ((p.map (algebraMap F E)).Splits)]
  body: AlgEquiv.restrictNormalHom p.SplittingField

中文:
定义 restrict
  签名: [Fact ((p.map (algebraMap F E)).Splits)]
  定义体: AlgEquiv.restrictNormalHom p.SplittingField

Depends on / 依赖: AlgEquiv, AlgEquiv.restrictNormalHom, SplittingField, p.SplittingField, restrictNormalHom
-/
def restrict [Fact ((p.map (algebraMap F E)).Splits)] : Gal(E/F) ->* p.Gal :=
  AlgEquiv.restrictNormalHom p.SplittingField

/--
theorem `restrict_surjective` / 定理 `restrict_surjective`

English:
theorem restrict_surjective
  given: [Fact ((p.map (algebraMap F E)).Splits)] [Normal F E]
  proof: AlgEquiv.restrictNormalHom_surjective E

中文:
定理 restrict_surjective
  条件: [Fact ((p.map (algebraMap F E)).Splits)] [正规 F E]
  证明: AlgEquiv.restrictNormalHom_surjective E

Depends on / 依赖: AlgEquiv, AlgEquiv.restrictNormalHom_surjective, restrictNormalHom_surjective
-/
theorem restrict_surjective [Fact ((p.map (algebraMap F E)).Splits)] [Normal F E] :
    Function.Surjective (restrict p E) :=
  AlgEquiv.restrictNormalHom_surjective E

section RootsAction

/--
Definition of `mapRoots` / `mapRoots` 的定义

English:
definition mapRoots
  signature: [Fact ((p.map (algebraMap F E)).Splits)]
  body: Set.MapsTo.restrict (IsScalarTower.toAlgHom F p.SplittingField E) _ _ rootSet_mapsTo _

中文:
定义 mapRoots
  签名: [Fact ((p.map (algebraMap F E)).Splits)]
  定义体: Set.MapsTo.restrict (IsScalarTower.toAlgHom F p.SplittingField E) _ _ rootSet_mapsTo _

Depends on / 依赖: IsScalarTower, IsScalarTower.toAlgHom, MapsTo, Set.MapsTo.restrict, SplittingField, p.SplittingField, restrict, rootSet_mapsTo, toAlgHom
-/
def mapRoots [Fact ((p.map (algebraMap F E)).Splits)] : rootSet p p.SplittingField -> rootSet p E :=
Set.MapsTo.restrict (IsScalarTower.toAlgHom F p.SplittingField E) _ _ rootSet_mapsTo _

/--
theorem `mapRoots_bijective` / 定理 `mapRoots_bijective`

English:
theorem mapRoots_bijective
  given: [h : Fact ((p.map (algebraMap F E)).Splits)]
  proof: by
  constructor
  · exact fun _ _ h => Subtype.ext (RingHom.injective _ (Subtype.ext_iff.mp h))
  · intro y
    -- this is just an equality of two different ways to write the roots of `p` as an `E`-polynomial
    have key := (IsSplittingField.splits p.SplittingField p).roots_map
      (IsScalarTower.toAlgHom F p.SplittingField E : p.SplittingField ->+* E)
    rw [map_map]; rw [AlgHom.comp_algebraMap] at key
    have hy := Subtype.mem y
    simp only [rootSet, Finset.mem_coe, Multiset.mem_toFinset, key, Multiset.mem_map] at hy
    rcases hy with ⟨x, hx1, hx2⟩
    exact ⟨⟨x, (@Multiset.mem_toFinset _ (Classical.decEq _) _ _).mpr hx1⟩, Subtype.ext hx2⟩

中文:
定理 mapRoots_bijective
  条件: [h : Fact ((p.map (algebraMap F E)).Splits)]
  证明: by
  constructor
  · exact fun _ _ h => Subtype.ext (RingHom.injective _ (Subtype.ext_iff.mp h))
  · intro y
    -- this is just an equality of two different ways to write the roots of `p` as an `E`-polynomial
    have key := (IsSplittingField.splits p.SplittingField p).roots_map
      (IsScalarTower.toAlgHom F p.SplittingField E : p.SplittingField ->+* E)
    rw [map_map]; rw [AlgHom.comp_algebraMap] at key
    have hy := Subtype.mem y
    simp only [rootSet, Finset.mem_coe, Multiset.mem_toFinset, key, Multiset.mem_map] at hy
    rcases hy with ⟨x, hx1, hx2⟩
    exact ⟨⟨x, (@Multiset.mem_toFinset _ (Classical.decEq _) _ _).mpr hx1⟩, Subtype.ext hx2⟩

Depends on / 依赖: RingHom, RingHom.injective, Subtype, Subtype.ext, Subtype.ext_iff.mp, ext_iff, injective
-/
theorem mapRoots_bijective [h : Fact ((p.map (algebraMap F E)).Splits)] :
    Function.Bijective (mapRoots p E) := by
  constructor
  · exact fun _ _ h => Subtype.ext (RingHom.injective _ (Subtype.ext_iff.mp h))
  · intro y
    -- this is just an equality of two different ways to write the roots of `p` as an `E`-polynomial
    have key := (IsSplittingField.splits p.SplittingField p).roots_map
      (IsScalarTower.toAlgHom F p.SplittingField E : p.SplittingField ->+* E)
    rw [map_map]; rw [AlgHom.comp_algebraMap] at key
    have hy := Subtype.mem y
    simp only [rootSet, Finset.mem_coe, Multiset.mem_toFinset, key, Multiset.mem_map] at hy
    rcases hy with ⟨x, hx1, hx2⟩
    exact ⟨⟨x, (@Multiset.mem_toFinset _ (Classical.decEq _) _ _).mpr hx1⟩, Subtype.ext hx2⟩

/--
Definition of `rootsEquivRoots` / `rootsEquivRoots` 的定义

English:
definition rootsEquivRoots
  signature: [Fact ((p.map (algebraMap F E)).Splits)]
  body: Equiv.ofBijective (mapRoots p E) (mapRoots_bijective p E)

中文:
定义 rootsEquivRoots
  签名: [Fact ((p.map (algebraMap F E)).Splits)]
  定义体: Equiv.ofBijective (mapRoots p E) (mapRoots_bijective p E)

Depends on / 依赖: Equiv.ofBijective, mapRoots, mapRoots_bijective, ofBijective
-/
def rootsEquivRoots [Fact ((p.map (algebraMap F E)).Splits)] :
    rootSet p p.SplittingField ≃ rootSet p E :=
  Equiv.ofBijective (mapRoots p E) (mapRoots_bijective p E)

/--
Instance `galActionAux` / 实例 `galActionAux`

English:
instance galActionAux
  signature: : MulAction p.Gal (rootSet p p.SplittingField) where
  body: Set.MapsTo.restrict ϕ _ _ rootSet_mapsTo ϕ.toAlgHom
  one_smul _ := by ext; rfl
  mul_smul _ _ _ := by ext; rfl

中文:
实例 galActionAux
  签名: : 乘法作用 p.Gal (rootSet p p.分裂域) where
  定义体: Set.MapsTo.restrict ϕ _ _ rootSet_mapsTo ϕ.toAlgHom
  one_smul _ := by ext; rfl
  mul_smul _ _ _ := by ext; rfl

Depends on / 依赖: MapsTo, Set.MapsTo.restrict, restrict, rootSet_mapsTo, toAlgHom
-/
instance galActionAux : MulAction p.Gal (rootSet p p.SplittingField) where
smul ϕ := Set.MapsTo.restrict ϕ _ _ rootSet_mapsTo ϕ.toAlgHom
  one_smul _ := by ext; rfl
  mul_smul _ _ _ := by ext; rfl

/--
Instance `smul` / 实例 `smul`

English:
instance smul
  signature: [Fact ((p.map (algebraMap F E)).Splits)]
  body: rootsEquivRoots p E (ϕ • (rootsEquivRoots p E).symm x)

中文:
实例 smul
  签名: [Fact ((p.map (algebraMap F E)).Splits)]
  定义体: rootsEquivRoots p E (ϕ • (rootsEquivRoots p E).symm x)

Depends on / 依赖: rootsEquivRoots
-/
instance smul [Fact ((p.map (algebraMap F E)).Splits)] : SMul p.Gal (rootSet p E) where
  smul ϕ x := rootsEquivRoots p E (ϕ • (rootsEquivRoots p E).symm x)

/--
theorem `smul_def` / 定理 `smul_def`

English:
theorem smul_def
  given: [Fact ((p.map (algebraMap F E)).Splits)] (ϕ : p.Gal) (x : rootSet p E)
  proof: rfl

中文:
定理 smul_def
  条件: [Fact ((p.map (algebraMap F E)).Splits)] (ϕ : p.Gal) (x : rootSet p E)
  证明: rfl
-/
theorem smul_def [Fact ((p.map (algebraMap F E)).Splits)] (ϕ : p.Gal) (x : rootSet p E) :
    ϕ • x = rootsEquivRoots p E (ϕ • (rootsEquivRoots p E).symm x) :=
  rfl

/--
Instance `galAction` / 实例 `galAction`

English:
instance galAction
  signature: [Fact ((p.map (algebraMap F E)).Splits)]
  body: by simp only [smul_def, Equiv.apply_symm_apply, one_smul]
  mul_smul _ _ _ := by
    simp only [smul_def, Equiv.symm_apply_apply, mul_smul]

中文:
实例 galAction
  签名: [Fact ((p.map (algebraMap F E)).Splits)]
  定义体: by simp only [smul_def, Equiv.apply_symm_apply, one_smul]
  mul_smul _ _ _ := by
    simp only [smul_def, Equiv.symm_apply_apply, mul_smul]

Depends on / 依赖: Equiv.apply_symm_apply, Equiv.symm_apply_apply, apply_symm_apply, mul_smul, one_smul, smul_def, symm_apply_apply
-/
instance galAction [Fact ((p.map (algebraMap F E)).Splits)] : MulAction p.Gal (rootSet p E) where
  one_smul _ := by simp only [smul_def, Equiv.apply_symm_apply, one_smul]
  mul_smul _ _ _ := by
    simp only [smul_def, Equiv.symm_apply_apply, mul_smul]

/--
lemma `galAction_isPretransitive` / 引理 `galAction_isPretransitive`

English:
lemma galAction_isPretransitive
  given: [Fact ((p.map (algebraMap F E)).Splits)] (hp : Irreducible p)
  proof: by
  refine ⟨fun x y => ?_⟩
  have hx := minpoly.eq_of_irreducible hp (mem_rootSet.mp ((rootsEquivRoots p E).symm x).2).2
  have hy := minpoly.eq_of_irreducible hp (mem_rootSet.mp ((rootsEquivRoots p E).symm y).2).2
  obtain ⟨g, hg⟩ := (Normal.minpoly_eq_iff_mem_orbit p.SplittingField).mp (hy.symm.trans hx)
  exact ⟨g, (rootsEquivRoots p E).eq_symm_apply.mp (Subtype.ext hg)⟩

中文:
引理 galAction_isPretransitive
  条件: [Fact ((p.map (algebraMap F E)).Splits)] (hp : 不可约 p)
  证明: by
  refine ⟨fun x y => ?_⟩
  have hx := minpoly.eq_of_irreducible hp (mem_rootSet.mp ((rootsEquivRoots p E).symm x).2).2
  have hy := minpoly.eq_of_irreducible hp (mem_rootSet.mp ((rootsEquivRoots p E).symm y).2).2
  obtain ⟨g, hg⟩ := (Normal.minpoly_eq_iff_mem_orbit p.SplittingField).mp (hy.symm.trans hx)
  exact ⟨g, (rootsEquivRoots p E).eq_symm_apply.mp (Subtype.ext hg)⟩

Depends on / 依赖: Normal, Normal.minpoly_eq_iff_mem_orbit, SplittingField, Subtype, Subtype.ext, eq_of_irreducible, eq_symm_apply, eq_symm_apply.mp, hy.symm.trans, mem_rootSet, mem_rootSet.mp, minpoly, minpoly.eq_of_irreducible, minpoly_eq_iff_mem_orbit, p.SplittingField, rootsEquivRoots
-/
lemma galAction_isPretransitive [Fact ((p.map (algebraMap F E)).Splits)] (hp : Irreducible p) :
    MulAction.IsPretransitive p.Gal (p.rootSet E) := by
  refine ⟨fun x y => ?_⟩
  have hx := minpoly.eq_of_irreducible hp (mem_rootSet.mp ((rootsEquivRoots p E).symm x).2).2
  have hy := minpoly.eq_of_irreducible hp (mem_rootSet.mp ((rootsEquivRoots p E).symm y).2).2
  obtain ⟨g, hg⟩ := (Normal.minpoly_eq_iff_mem_orbit p.SplittingField).mp (hy.symm.trans hx)
  exact ⟨g, (rootsEquivRoots p E).eq_symm_apply.mp (Subtype.ext hg)⟩

variable {p E}

/-- `Polynomial.Gal.restrict p E` is compatible with `Polynomial.Gal.galAction p E`. -/
@[simp]
/--
theorem `restrict_smul` / 定理 `restrict_smul`

English:
theorem restrict_smul
  given: [Fact ((p.map (algebraMap F E)).Splits)] (ϕ : Gal(E/F)) (x : rootSet p E)
  proof: by
  let ψ := AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F p.SplittingField E)
  change ↑(ψ (ψ.symm _)) = ϕ x
  rw [AlgEquiv.apply_symm_apply ψ]
  change ϕ (rootsEquivRoots p E ((rootsEquivRoots p E).symm x)) = ϕ x
  rw [Equiv.apply_symm_apply (rootsEquivRoots p E)]

中文:
定理 restrict_smul
  条件: [Fact ((p.map (algebraMap F E)).Splits)] (ϕ : Gal(E/F)) (x : rootSet p E)
  证明: by
  let ψ := AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F p.SplittingField E)
  change ↑(ψ (ψ.symm _)) = ϕ x
  rw [AlgEquiv.apply_symm_apply ψ]
  change ϕ (rootsEquivRoots p E ((rootsEquivRoots p E).symm x)) = ϕ x
  rw [Equiv.apply_symm_apply (rootsEquivRoots p E)]

Depends on / 依赖: AlgEquiv, AlgEquiv.apply_symm_apply, AlgEquiv.ofInjectiveField, Equiv.apply_symm_apply, IsScalarTower, IsScalarTower.toAlgHom, SplittingField, apply_symm_apply, ofInjectiveField, p.SplittingField, rootsEquivRoots, toAlgHom
-/
theorem restrict_smul [Fact ((p.map (algebraMap F E)).Splits)] (ϕ : Gal(E/F)) (x : rootSet p E) :
    ↑(restrict p E ϕ • x) = ϕ x := by
  let ψ := AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F p.SplittingField E)
  change ↑(ψ (ψ.symm _)) = ϕ x
  rw [AlgEquiv.apply_symm_apply ψ]
  change ϕ (rootsEquivRoots p E ((rootsEquivRoots p E).symm x)) = ϕ x
  rw [Equiv.apply_symm_apply (rootsEquivRoots p E)]

variable (p E)

/--
Definition of `galActionHom` / `galActionHom` 的定义

English:
definition galActionHom
  signature: [Fact ((p.map (algebraMap F E)).Splits)]
  body: MulAction.toPermHom _ _

中文:
定义 galActionHom
  签名: [Fact ((p.map (algebraMap F E)).Splits)]
  定义体: MulAction.toPermHom _ _

Depends on / 依赖: MulAction, MulAction.toPermHom, toPermHom
-/
def galActionHom [Fact ((p.map (algebraMap F E)).Splits)] : p.Gal ->* Equiv.Perm (rootSet p E) :=
  MulAction.toPermHom _ _

/--
theorem `galActionHom_restrict` / 定理 `galActionHom_restrict`

English:
theorem galActionHom_restrict
  statement: [Fact ((p.map (algebraMap F E)).Splits)] (ϕ : Gal(E/F))
  proof: restrict_smul ϕ x

中文:
定理 galActionHom_restrict
  结论: [Fact ((p.map (algebraMap F E)).Splits)] (ϕ : Gal(E/F))
  证明: restrict_smul ϕ x

Depends on / 依赖: restrict_smul
-/
theorem galActionHom_restrict [Fact ((p.map (algebraMap F E)).Splits)] (ϕ : Gal(E/F))
    (x : rootSet p E) : ↑(galActionHom p E (restrict p E ϕ) x) = ϕ x :=
  restrict_smul ϕ x

/--
theorem `galActionHom_injective` / 定理 `galActionHom_injective`

English:
theorem galActionHom_injective
  given: [Fact ((p.map (algebraMap F E)).Splits)]
  proof: by
  rw [injective_iff_map_eq_one]
  intro ϕ hϕ
  ext (x hx)
  have key := Equiv.Perm.ext_iff.mp hϕ (rootsEquivRoots p E ⟨x, hx⟩)
  change
    rootsEquivRoots p E (ϕ • (rootsEquivRoots p E).symm (rootsEquivRoots p E ⟨x, hx⟩)) =
      rootsEquivRoots p E ⟨x, hx⟩
    at key
  rw [Equiv.symm_apply_apply] at key
  exact Subtype.ext_iff.mp (Equiv.injective (rootsEquivRoots p E) key)

中文:
定理 galActionHom_injective
  条件: [Fact ((p.map (algebraMap F E)).Splits)]
  证明: by
  rw [injective_iff_map_eq_one]
  intro ϕ hϕ
  ext (x hx)
  have key := Equiv.Perm.ext_iff.mp hϕ (rootsEquivRoots p E ⟨x, hx⟩)
  change
    rootsEquivRoots p E (ϕ • (rootsEquivRoots p E).symm (rootsEquivRoots p E ⟨x, hx⟩)) =
      rootsEquivRoots p E ⟨x, hx⟩
    at key
  rw [Equiv.symm_apply_apply] at key
  exact Subtype.ext_iff.mp (Equiv.injective (rootsEquivRoots p E) key)

Depends on / 依赖: Equiv.Perm.ext_iff.mp, Equiv.injective, Equiv.symm_apply_apply, Subtype, Subtype.ext_iff.mp, ext_iff, injective, injective_iff_map_eq_one, rootsEquivRoots, symm_apply_apply
-/
theorem galActionHom_injective [Fact ((p.map (algebraMap F E)).Splits)] :
    Function.Injective (galActionHom p E) := by
  rw [injective_iff_map_eq_one]
  intro ϕ hϕ
  ext (x hx)
  have key := Equiv.Perm.ext_iff.mp hϕ (rootsEquivRoots p E ⟨x, hx⟩)
  change
    rootsEquivRoots p E (ϕ • (rootsEquivRoots p E).symm (rootsEquivRoots p E ⟨x, hx⟩)) =
      rootsEquivRoots p E ⟨x, hx⟩
    at key
  rw [Equiv.symm_apply_apply] at key
  exact Subtype.ext_iff.mp (Equiv.injective (rootsEquivRoots p E) key)

end RootsAction

variable {p q}

/--
Definition of `restrictDvd` / `restrictDvd` 的定义

English:
definition restrictDvd
  signature: (hpq : p ∣ q)
  body: haveI := Classical.dec (q = 0)
  if hq : q = 0 then 1
  else
    @restrict F _ p _ _ _
      ⟨(SplittingField.splits q).of_dvd (map_ne_zero hq) ((map_dvd_map' _).mpr hpq)⟩

中文:
定义 restrictDvd
  签名: (hpq : p ∣ q)
  定义体: haveI := Classical.dec (q = 0)
  if hq : q = 0 then 1
  else
    @restrict F _ p _ _ _
      ⟨(SplittingField.splits q).of_dvd (map_ne_zero hq) ((map_dvd_map' _).mpr hpq)⟩

Depends on / 依赖: Classical, Classical.dec, SplittingField, SplittingField.splits, map_dvd_map, map_ne_zero, of_dvd, restrict, splits
-/
def restrictDvd (hpq : p ∣ q) : q.Gal ->* p.Gal :=
  haveI := Classical.dec (q = 0)
  if hq : q = 0 then 1
  else
    @restrict F _ p _ _ _
      ⟨(SplittingField.splits q).of_dvd (map_ne_zero hq) ((map_dvd_map' _).mpr hpq)⟩

/--
theorem `restrictDvd_def` / 定理 `restrictDvd_def`

English:
theorem restrictDvd_def
  given: [Decidable (q = 0)] (hpq : p ∣ q)
  proof: by
  unfold restrictDvd
  congr

中文:
定理 restrictDvd_def
  条件: [可判定 (q = 0)] (hpq : p ∣ q)
  证明: by
  unfold restrictDvd
  congr

Depends on / 依赖: restrictDvd
-/
theorem restrictDvd_def [Decidable (q = 0)] (hpq : p ∣ q) :
    restrictDvd hpq =
      if hq : q = 0 then 1
      else @restrict F _ p _ _ _
        ⟨(SplittingField.splits q).of_dvd (map_ne_zero hq) ((map_dvd_map' _).mpr hpq)⟩ := by
  unfold restrictDvd
  congr

/--
theorem `restrictDvd_surjective` / 定理 `restrictDvd_surjective`

English:
theorem restrictDvd_surjective
  given: (hpq : p ∣ q) (hq : q != 0)
  proof: by
  classical
have := Fact.mk
    (SplittingField.splits q).of_dvd (map_ne_zero hq) ((map_dvd_map' _).mpr hpq)
  simpa only [restrictDvd_def, dif_neg hq] using! restrict_surjective _ _

中文:
定理 restrictDvd_surjective
  条件: (hpq : p ∣ q) (hq : q != 0)
  证明: by
  classical
have := Fact.mk
    (SplittingField.splits q).of_dvd (map_ne_zero hq) ((map_dvd_map' _).mpr hpq)
  simpa only [restrictDvd_def, dif_neg hq] using! restrict_surjective _ _

Depends on / 依赖: Fact.mk, SplittingField, SplittingField.splits, classical, dif_neg, map_dvd_map, map_ne_zero, of_dvd, restrictDvd_def, restrict_surjective, splits
-/
theorem restrictDvd_surjective (hpq : p ∣ q) (hq : q != 0) :
    Function.Surjective (restrictDvd hpq) := by
  classical
have := Fact.mk
    (SplittingField.splits q).of_dvd (map_ne_zero hq) ((map_dvd_map' _).mpr hpq)
  simpa only [restrictDvd_def, dif_neg hq] using! restrict_surjective _ _

variable (p q)

/--
Definition of `restrictProd` / `restrictProd` 的定义

English:
definition restrictProd
  signature: : (p * q).Gal ->* p.Gal × q.Gal
  body: MonoidHom.prod (restrictDvd (dvd_mul_right p q)) (restrictDvd (dvd_mul_left q p))

中文:
定义 restrictProd
  签名: : (p * q).Gal ->* p.Gal × q.Gal
  定义体: MonoidHom.prod (restrictDvd (dvd_mul_right p q)) (restrictDvd (dvd_mul_left q p))

Depends on / 依赖: MonoidHom, MonoidHom.prod, dvd_mul_left, dvd_mul_right, restrictDvd
-/
def restrictProd : (p * q).Gal ->* p.Gal × q.Gal :=
  MonoidHom.prod (restrictDvd (dvd_mul_right p q)) (restrictDvd (dvd_mul_left q p))

set_option backward.isDefEq.respectTransparency false in
/--
theorem `restrictProd_injective` / 定理 `restrictProd_injective`

English:
theorem restrictProd_injective
  statement: Function.Injective (restrictProd p q)
  proof: by
  by_cases hpq : p * q = 0
  · have : Unique (p * q).Gal := by rw [hpq]; infer_instance
    exact fun f g _ => Eq.trans (Unique.eq_default f) (Unique.eq_default g).symm
  intro f g hfg
  classical
  simp only [restrictProd, restrictDvd_def] at hfg
  simp only [dif_neg hpq, MonoidHom.prod_apply, Prod.mk_inj] at hfg
  ext (x hx)
  rw [rootSet_def]; rw [aroots_mul hpq] at hx
  rcases Multiset.mem_add.mp (Multiset.mem_toFinset.mp hx) with h | h
  · have : Fact ((p.map (algebraMap F (p * q).SplittingField)).Splits) :=
      ⟨(SplittingField.splits (p * q)).of_dvd (map_ne_zero hpq)
        ((map_dvd_map' _).mpr (dvd_mul_right p q))⟩
    have key :
      x =
        algebraMap p.SplittingField (p * q).SplittingField
          ((rootsEquivRoots p _).invFun
            ⟨x, (@Multiset.mem_toFinset _ (Classical.decEq _) _ _).mpr h⟩) :=
      Subtype.ext_iff.mp (Equiv.apply_symm_apply (rootsEquivRoots p _) ⟨x, _⟩).symm
    rw [key]; rw [← AlgEquiv.restrictNormal_commutes]; rw [← AlgEquiv.restrictNormal_commutes]
    exact congr_arg _ (AlgEquiv.ext_iff.mp hfg.1 _)
  · have : Fact ((q.map (algebraMap F (p * q).SplittingField)).Splits) :=
      ⟨(SplittingField.splits (p * q)).of_dvd (map_ne_zero hpq)
        ((map_dvd_map' _).mpr (dvd_mul_left q p))⟩
    have key :
      x =
        algebraMap q.SplittingField (p * q).SplittingField
          ((rootsEquivRoots q _).invFun
            ⟨x, (@Multiset.mem_toFinset _ (Classical.decEq _) _ _).mpr h⟩) :=
      Subtype.ext_iff.mp (Equiv.apply_symm_apply (rootsEquivRoots q _) ⟨x, _⟩).symm
    rw [key]; rw [← AlgEquiv.restrictNormal_commutes]; rw [← AlgEquiv.restrictNormal_commutes]
    exact congr_arg _ (AlgEquiv.ext_iff.mp hfg.2 _)

中文:
定理 restrictProd_injective
  结论: 函数.单射 (restrictProd p q)
  证明: by
  by_cases hpq : p * q = 0
  · have : Unique (p * q).Gal := by rw [hpq]; infer_instance
    exact fun f g _ => Eq.trans (Unique.eq_default f) (Unique.eq_default g).symm
  intro f g hfg
  classical
  simp only [restrictProd, restrictDvd_def] at hfg
  simp only [dif_neg hpq, MonoidHom.prod_apply, Prod.mk_inj] at hfg
  ext (x hx)
  rw [rootSet_def]; rw [aroots_mul hpq] at hx
  rcases Multiset.mem_add.mp (Multiset.mem_toFinset.mp hx) with h | h
  · have : Fact ((p.map (algebraMap F (p * q).SplittingField)).Splits) :=
      ⟨(SplittingField.splits (p * q)).of_dvd (map_ne_zero hpq)
        ((map_dvd_map' _).mpr (dvd_mul_right p q))⟩
    have key :
      x =
        algebraMap p.SplittingField (p * q).SplittingField
          ((rootsEquivRoots p _).invFun
            ⟨x, (@Multiset.mem_toFinset _ (Classical.decEq _) _ _).mpr h⟩) :=
      Subtype.ext_iff.mp (Equiv.apply_symm_apply (rootsEquivRoots p _) ⟨x, _⟩).symm
    rw [key]; rw [← AlgEquiv.restrictNormal_commutes]; rw [← AlgEquiv.restrictNormal_commutes]
    exact congr_arg _ (AlgEquiv.ext_iff.mp hfg.1 _)
  · have : Fact ((q.map (algebraMap F (p * q).SplittingField)).Splits) :=
      ⟨(SplittingField.splits (p * q)).of_dvd (map_ne_zero hpq)
        ((map_dvd_map' _).mpr (dvd_mul_left q p))⟩
    have key :
      x =
        algebraMap q.SplittingField (p * q).SplittingField
          ((rootsEquivRoots q _).invFun
            ⟨x, (@Multiset.mem_toFinset _ (Classical.decEq _) _ _).mpr h⟩) :=
      Subtype.ext_iff.mp (Equiv.apply_symm_apply (rootsEquivRoots q _) ⟨x, _⟩).symm
    rw [key]; rw [← AlgEquiv.restrictNormal_commutes]; rw [← AlgEquiv.restrictNormal_commutes]
    exact congr_arg _ (AlgEquiv.ext_iff.mp hfg.2 _)

Depends on / 依赖: Eq.trans, MonoidHom, MonoidHom.prod_apply, Multiset, Multiset.mem_add.mp, Multiset.mem_toFinset.mp, Prod.mk_inj, Splits, SplittingField, Unique, Unique.eq_default, algebraMap, aroots_mul, classical, dif_neg, eq_default, infer_instance, mem_add, mem_toFinset, mk_inj
-/
theorem restrictProd_injective : Function.Injective (restrictProd p q) := by
  by_cases hpq : p * q = 0
  · have : Unique (p * q).Gal := by rw [hpq]; infer_instance
    exact fun f g _ => Eq.trans (Unique.eq_default f) (Unique.eq_default g).symm
  intro f g hfg
  classical
  simp only [restrictProd, restrictDvd_def] at hfg
  simp only [dif_neg hpq, MonoidHom.prod_apply, Prod.mk_inj] at hfg
  ext (x hx)
  rw [rootSet_def]; rw [aroots_mul hpq] at hx
  rcases Multiset.mem_add.mp (Multiset.mem_toFinset.mp hx) with h | h
  · have : Fact ((p.map (algebraMap F (p * q).SplittingField)).Splits) :=
      ⟨(SplittingField.splits (p * q)).of_dvd (map_ne_zero hpq)
        ((map_dvd_map' _).mpr (dvd_mul_right p q))⟩
    have key :
      x =
        algebraMap p.SplittingField (p * q).SplittingField
          ((rootsEquivRoots p _).invFun
            ⟨x, (@Multiset.mem_toFinset _ (Classical.decEq _) _ _).mpr h⟩) :=
      Subtype.ext_iff.mp (Equiv.apply_symm_apply (rootsEquivRoots p _) ⟨x, _⟩).symm
    rw [key]; rw [← AlgEquiv.restrictNormal_commutes]; rw [← AlgEquiv.restrictNormal_commutes]
    exact congr_arg _ (AlgEquiv.ext_iff.mp hfg.1 _)
  · have : Fact ((q.map (algebraMap F (p * q).SplittingField)).Splits) :=
      ⟨(SplittingField.splits (p * q)).of_dvd (map_ne_zero hpq)
        ((map_dvd_map' _).mpr (dvd_mul_left q p))⟩
    have key :
      x =
        algebraMap q.SplittingField (p * q).SplittingField
          ((rootsEquivRoots q _).invFun
            ⟨x, (@Multiset.mem_toFinset _ (Classical.decEq _) _ _).mpr h⟩) :=
      Subtype.ext_iff.mp (Equiv.apply_symm_apply (rootsEquivRoots q _) ⟨x, _⟩).symm
    rw [key]; rw [← AlgEquiv.restrictNormal_commutes]; rw [← AlgEquiv.restrictNormal_commutes]
    exact congr_arg _ (AlgEquiv.ext_iff.mp hfg.2 _)

/--
theorem `mul_splits_in_splittingField_of_mul` / 定理 `mul_splits_in_splittingField_of_mul`

English:
theorem mul_splits_in_splittingField_of_mul
  statement: {p₁ q₁ p₂ q₂ : F[X]} (hq₁ : q₁ != 0) (hq₂ : q₂ != 0)
  proof: by
  rw [Polynomial.map_mul]
  apply Splits.mul
  · rw [←
      (SplittingField.lift q₁
          ((SplittingField.splits _).of_dvd (map_ne_zero (mul_ne_zero hq₁ hq₂))
             ((map_dvd_map' _).mpr (dvd_mul_right q₁ q₂)))).comp_algebraMap, ← map_map]
    exact h₁.map _
  · rw [←
      (SplittingField.lift q₂
          ((SplittingField.splits _).of_dvd (map_ne_zero (mul_ne_zero hq₁ hq₂))
             ((map_dvd_map' _).mpr (dvd_mul_left q₂ q₁)))).comp_algebraMap, ← map_map]
    exact h₂.map _

中文:
定理 mul_splits_in_splittingField_of_mul
  结论: {p₁ q₁ p₂ q₂ : F[X]} (hq₁ : q₁ != 0) (hq₂ : q₂ != 0)
  证明: by
  rw [Polynomial.map_mul]
  apply Splits.mul
  · rw [←
      (SplittingField.lift q₁
          ((SplittingField.splits _).of_dvd (map_ne_zero (mul_ne_zero hq₁ hq₂))
             ((map_dvd_map' _).mpr (dvd_mul_right q₁ q₂)))).comp_algebraMap, ← map_map]
    exact h₁.map _
  · rw [←
      (SplittingField.lift q₂
          ((SplittingField.splits _).of_dvd (map_ne_zero (mul_ne_zero hq₁ hq₂))
             ((map_dvd_map' _).mpr (dvd_mul_left q₂ q₁)))).comp_algebraMap, ← map_map]
    exact h₂.map _

Depends on / 依赖: Polynomial, Polynomial.map_mul, Splits, Splits.mul, SplittingField, SplittingField.lift, SplittingField.splits, comp_algebraMap, dvd_mul_left, dvd_mul_right, map_dvd_map, map_map, map_mul, map_ne_zero, mul_ne_zero, of_dvd, splits
-/
theorem mul_splits_in_splittingField_of_mul {p₁ q₁ p₂ q₂ : F[X]} (hq₁ : q₁ != 0) (hq₂ : q₂ != 0)
    (h₁ : (p₁.map (algebraMap F q₁.SplittingField)).Splits)
    (h₂ : (p₂.map (algebraMap F q₂.SplittingField)).Splits) :
    ((p₁ * p₂).map (algebraMap F (q₁ * q₂).SplittingField)).Splits := by
  rw [Polynomial.map_mul]
  apply Splits.mul
  · rw [←
      (SplittingField.lift q₁
          ((SplittingField.splits _).of_dvd (map_ne_zero (mul_ne_zero hq₁ hq₂))
             ((map_dvd_map' _).mpr (dvd_mul_right q₁ q₂)))).comp_algebraMap, ← map_map]
    exact h₁.map _
  · rw [←
      (SplittingField.lift q₂
          ((SplittingField.splits _).of_dvd (map_ne_zero (mul_ne_zero hq₁ hq₂))
             ((map_dvd_map' _).mpr (dvd_mul_left q₂ q₁)))).comp_algebraMap, ← map_map]
    exact h₂.map _

/--
theorem `splits_in_splittingField_of_comp` / 定理 `splits_in_splittingField_of_comp`

English:
theorem splits_in_splittingField_of_comp
  given: (hq : q.natDegree != 0)
  proof: by
  let P : F[X] -> Prop := fun r => (r.map (algebraMap F (r.comp q).SplittingField)).Splits
  have key1 : forall {r : F[X]}, Irreducible r -> P r := by
    intro r hr
    by_cases hr' : natDegree r = 0
· exact Splits.of_natDegree_le_one natDegree_map_le.trans (hr'.trans_le zero_le_one)
    obtain ⟨x, hx⟩ :=
      Splits.exists_eval_eq_zero (SplittingField.splits (r.comp q)) fun h =>
        hr' ((mul_eq_zero.mp (natDegree_comp.symm.trans (natDegree_eq_of_degree_eq_some
          (by rwa [degree_map] at h)))).resolve_right hq)
    rw [eval_map_algebraMap]; rw [aeval_comp] at hx
    have h_normal : Normal F (r.comp q).SplittingField := SplittingField.instNormal (r.comp q)
    have qx_int := Normal.isIntegral h_normal (aeval x q)
    exact (h_normal.splits _).of_dvd (map_ne_zero (minpoly.ne_zero (h_normal.isIntegral _)))
      ((map_dvd_map' _).mpr ((minpoly.irreducible qx_int).dvd_symm hr (minpoly.dvd F _ hx)))
  have key2 : forall {p₁ p₂ : F[X]}, P p₁ -> P p₂ -> P (p₁ * p₂) := by
    intro p₁ p₂ hp₁ hp₂
    by_cases h₁ : p₁.comp q = 0
    · rcases comp_eq_zero_iff.mp h₁ with h | h
      · rw [h, zero_mul]
        simp [P]
      · exact False.elim (hq (by rw [h.2, natDegree_C]))
    by_cases h₂ : p₂.comp q = 0
    · rcases comp_eq_zero_iff.mp h₂ with h | h
      · simp [h, P]
      · exact False.elim (hq (by rw [h.2, natDegree_C]))
    have key := mul_splits_in_splittingField_of_mul h₁ h₂ hp₁ hp₂
    rwa [← mul_comp] at key
  exact
    WfDvdMonoid.induction_on_irreducible p (by simp) (fun _ hu => hu.splits.map _)
      fun _ _ _ h => key2 (key1 h)

中文:
定理 splits_in_splittingField_of_comp
  条件: (hq : q.natDegree != 0)
  证明: by
  let P : F[X] -> Prop := fun r => (r.map (algebraMap F (r.comp q).SplittingField)).Splits
  have key1 : forall {r : F[X]}, Irreducible r -> P r := by
    intro r hr
    by_cases hr' : natDegree r = 0
· exact Splits.of_natDegree_le_one natDegree_map_le.trans (hr'.trans_le zero_le_one)
    obtain ⟨x, hx⟩ :=
      Splits.exists_eval_eq_zero (SplittingField.splits (r.comp q)) fun h =>
        hr' ((mul_eq_zero.mp (natDegree_comp.symm.trans (natDegree_eq_of_degree_eq_some
          (by rwa [degree_map] at h)))).resolve_right hq)
    rw [eval_map_algebraMap]; rw [aeval_comp] at hx
    have h_normal : Normal F (r.comp q).SplittingField := SplittingField.instNormal (r.comp q)
    have qx_int := Normal.isIntegral h_normal (aeval x q)
    exact (h_normal.splits _).of_dvd (map_ne_zero (minpoly.ne_zero (h_normal.isIntegral _)))
      ((map_dvd_map' _).mpr ((minpoly.irreducible qx_int).dvd_symm hr (minpoly.dvd F _ hx)))
  have key2 : forall {p₁ p₂ : F[X]}, P p₁ -> P p₂ -> P (p₁ * p₂) := by
    intro p₁ p₂ hp₁ hp₂
    by_cases h₁ : p₁.comp q = 0
    · rcases comp_eq_zero_iff.mp h₁ with h | h
      · rw [h, zero_mul]
        simp [P]
      · exact False.elim (hq (by rw [h.2, natDegree_C]))
    by_cases h₂ : p₂.comp q = 0
    · rcases comp_eq_zero_iff.mp h₂ with h | h
      · simp [h, P]
      · exact False.elim (hq (by rw [h.2, natDegree_C]))
    have key := mul_splits_in_splittingField_of_mul h₁ h₂ hp₁ hp₂
    rwa [← mul_comp] at key
  exact
    WfDvdMonoid.induction_on_irreducible p (by simp) (fun _ hu => hu.splits.map _)
      fun _ _ _ h => key2 (key1 h)

Depends on / 依赖: Irreducible, Splits, Splits.exists_eval_eq_zero, Splits.of_natDegree_le_one, SplittingField, SplittingField.splits, algebraMap, degree_map, exists_eval_eq_zero, mul_eq_zero, mul_eq_zero.mp, natDegree, natDegree_comp, natDegree_comp.symm.trans, natDegree_eq_of_degree_eq_some, natDegree_map_le, natDegree_map_le.trans, of_natDegree_le_one, r.comp, r.map
-/
theorem splits_in_splittingField_of_comp (hq : q.natDegree != 0) :
    (p.map (algebraMap F (p.comp q).SplittingField)).Splits := by
  let P : F[X] -> Prop := fun r => (r.map (algebraMap F (r.comp q).SplittingField)).Splits
  have key1 : forall {r : F[X]}, Irreducible r -> P r := by
    intro r hr
    by_cases hr' : natDegree r = 0
· exact Splits.of_natDegree_le_one natDegree_map_le.trans (hr'.trans_le zero_le_one)
    obtain ⟨x, hx⟩ :=
      Splits.exists_eval_eq_zero (SplittingField.splits (r.comp q)) fun h =>
        hr' ((mul_eq_zero.mp (natDegree_comp.symm.trans (natDegree_eq_of_degree_eq_some
          (by rwa [degree_map] at h)))).resolve_right hq)
    rw [eval_map_algebraMap]; rw [aeval_comp] at hx
    have h_normal : Normal F (r.comp q).SplittingField := SplittingField.instNormal (r.comp q)
    have qx_int := Normal.isIntegral h_normal (aeval x q)
    exact (h_normal.splits _).of_dvd (map_ne_zero (minpoly.ne_zero (h_normal.isIntegral _)))
      ((map_dvd_map' _).mpr ((minpoly.irreducible qx_int).dvd_symm hr (minpoly.dvd F _ hx)))
  have key2 : forall {p₁ p₂ : F[X]}, P p₁ -> P p₂ -> P (p₁ * p₂) := by
    intro p₁ p₂ hp₁ hp₂
    by_cases h₁ : p₁.comp q = 0
    · rcases comp_eq_zero_iff.mp h₁ with h | h
      · rw [h, zero_mul]
        simp [P]
      · exact False.elim (hq (by rw [h.2, natDegree_C]))
    by_cases h₂ : p₂.comp q = 0
    · rcases comp_eq_zero_iff.mp h₂ with h | h
      · simp [h, P]
      · exact False.elim (hq (by rw [h.2, natDegree_C]))
    have key := mul_splits_in_splittingField_of_mul h₁ h₂ hp₁ hp₂
    rwa [← mul_comp] at key
  exact
    WfDvdMonoid.induction_on_irreducible p (by simp) (fun _ hu => hu.splits.map _)
      fun _ _ _ h => key2 (key1 h)

/--
Definition of `restrictComp` / `restrictComp` 的定义

English:
definition restrictComp
  signature: (hq : q.natDegree != 0)
  body: let h : Fact (Splits (p.map (algebraMap F (p.comp q).SplittingField))) :=
    ⟨splits_in_splittingField_of_comp p q hq⟩
  @restrict F _ p _ _ _ h

中文:
定义 restrictComp
  签名: (hq : q.natDegree != 0)
  定义体: let h : Fact (Splits (p.map (algebraMap F (p.comp q).SplittingField))) :=
    ⟨splits_in_splittingField_of_comp p q hq⟩
  @restrict F _ p _ _ _ h

Depends on / 依赖: Splits, SplittingField, algebraMap, p.comp, p.map, restrict, splits_in_splittingField_of_comp
-/
def restrictComp (hq : q.natDegree != 0) : (p.comp q).Gal ->* p.Gal :=
  let h : Fact (Splits (p.map (algebraMap F (p.comp q).SplittingField))) :=
    ⟨splits_in_splittingField_of_comp p q hq⟩
  @restrict F _ p _ _ _ h

/--
theorem `restrictComp_surjective` / 定理 `restrictComp_surjective`

English:
theorem restrictComp_surjective
  given: (hq : q.natDegree != 0)
  proof: by
  have : Fact (Splits (p.map (algebraMap F (SplittingField (comp p q))))) :=
    ⟨splits_in_splittingField_of_comp p q hq⟩
  simpa only [restrictComp] using! restrict_surjective _ _

中文:
定理 restrictComp_surjective
  条件: (hq : q.natDegree != 0)
  证明: by
  have : Fact (Splits (p.map (algebraMap F (SplittingField (comp p q))))) :=
    ⟨splits_in_splittingField_of_comp p q hq⟩
  simpa only [restrictComp] using! restrict_surjective _ _

Depends on / 依赖: Splits, SplittingField, algebraMap, p.map, restrictComp, restrict_surjective, splits_in_splittingField_of_comp
-/
theorem restrictComp_surjective (hq : q.natDegree != 0) :
    Function.Surjective (restrictComp p q hq) := by
  have : Fact (Splits (p.map (algebraMap F (SplittingField (comp p q))))) :=
    ⟨splits_in_splittingField_of_comp p q hq⟩
  simpa only [restrictComp] using! restrict_surjective _ _

variable {p q}

open scoped IntermediateField

/--
theorem `card_of_separable` / 定理 `card_of_separable`

English:
theorem card_of_separable
  given: (hp : p.Separable)
  statement: Nat.card p.Gal = finrank F p.SplittingField
  proof: haveI : IsGalois F p.SplittingField := IsGalois.of_separable_splitting_field hp
  IsGalois.card_aut_eq_finrank F p.SplittingField

中文:
定理 card_of_separable
  条件: (hp : p.可分)
  结论: 自然数.card p.Gal = finrank F p.分裂域
  证明: haveI : IsGalois F p.SplittingField := IsGalois.of_separable_splitting_field hp
  IsGalois.card_aut_eq_finrank F p.SplittingField

Depends on / 依赖: IsGalois, IsGalois.card_aut_eq_finrank, IsGalois.of_separable_splitting_field, SplittingField, card_aut_eq_finrank, of_separable_splitting_field, p.SplittingField
-/
theorem card_of_separable (hp : p.Separable) : Nat.card p.Gal = finrank F p.SplittingField :=
  haveI : IsGalois F p.SplittingField := IsGalois.of_separable_splitting_field hp
  IsGalois.card_aut_eq_finrank F p.SplittingField

/--
theorem `prime_degree_dvd_card` / 定理 `prime_degree_dvd_card`

English:
theorem prime_degree_dvd_card
  given: [CharZero F] (p_irr : Irreducible p) (p_deg : p.natDegree.Prime)
  proof: by
  rw [Gal.card_of_separable p_irr.separable]
  have hp : p.degree != 0 := fun h =>
    Nat.Prime.ne_zero p_deg (natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h))
  let α : p.SplittingField :=
    rootOfSplits (SplittingField.splits p) (by rwa [degree_map])
  have hα : IsIntegral F α := .of_finite F α
  use Module.finrank F⟮α⟯ p.SplittingField
  suffices (minpoly F α).natDegree = p.natDegree by
    let _ : AddCommGroup F⟮α⟯ := Ring.toAddCommGroup
    rw [← Module.finrank_mul_finrank F F⟮α⟯ p.SplittingField]; rw [IntermediateField.adjoin.finrank hα]; rw [this]
  suffices minpoly F α ∣ p by
    have key := (minpoly.irreducible hα).dvd_symm p_irr this
    apply le_antisymm
    · exact natDegree_le_of_dvd this p_irr.ne_zero
    · exact natDegree_le_of_dvd key (minpoly.ne_zero hα)
  apply minpoly.dvd F α
  rw [← eval_map_algebraMap]; rw [eval_rootOfSplits]

中文:
定理 prime_degree_dvd_card
  条件: [特征零 F] (p_irr : 不可约 p) (p_deg : p.natDegree.素)
  证明: by
  rw [Gal.card_of_separable p_irr.separable]
  have hp : p.degree != 0 := fun h =>
    Nat.Prime.ne_zero p_deg (natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h))
  let α : p.SplittingField :=
    rootOfSplits (SplittingField.splits p) (by rwa [degree_map])
  have hα : IsIntegral F α := .of_finite F α
  use Module.finrank F⟮α⟯ p.SplittingField
  suffices (minpoly F α).natDegree = p.natDegree by
    let _ : AddCommGroup F⟮α⟯ := Ring.toAddCommGroup
    rw [← Module.finrank_mul_finrank F F⟮α⟯ p.SplittingField]; rw [IntermediateField.adjoin.finrank hα]; rw [this]
  suffices minpoly F α ∣ p by
    have key := (minpoly.irreducible hα).dvd_symm p_irr this
    apply le_antisymm
    · exact natDegree_le_of_dvd this p_irr.ne_zero
    · exact natDegree_le_of_dvd key (minpoly.ne_zero hα)
  apply minpoly.dvd F α
  rw [← eval_map_algebraMap]; rw [eval_rootOfSplits]

Depends on / 依赖: AddCommGroup, Gal.card_of_separable, IsIntegral, Module, Module.finrank, Module.finrank_mul_finrank, Nat.Prime.ne_zero, Ring.toAddCommGroup, SplittingField, SplittingField.splits, card_of_separable, degree, degree_map, finrank, finrank_mul_finrank, le_of_eq, minpoly, natDegree, natDegree_eq_zero_iff_degree_le_zero, natDegree_eq_zero_iff_degree_le_zero.mpr
-/
theorem prime_degree_dvd_card [CharZero F] (p_irr : Irreducible p) (p_deg : p.natDegree.Prime) :
    p.natDegree ∣ Nat.card p.Gal := by
  rw [Gal.card_of_separable p_irr.separable]
  have hp : p.degree != 0 := fun h =>
    Nat.Prime.ne_zero p_deg (natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h))
  let α : p.SplittingField :=
    rootOfSplits (SplittingField.splits p) (by rwa [degree_map])
  have hα : IsIntegral F α := .of_finite F α
  use Module.finrank F⟮α⟯ p.SplittingField
  suffices (minpoly F α).natDegree = p.natDegree by
    let _ : AddCommGroup F⟮α⟯ := Ring.toAddCommGroup
    rw [← Module.finrank_mul_finrank F F⟮α⟯ p.SplittingField]; rw [IntermediateField.adjoin.finrank hα]; rw [this]
  suffices minpoly F α ∣ p by
    have key := (minpoly.irreducible hα).dvd_symm p_irr this
    apply le_antisymm
    · exact natDegree_le_of_dvd this p_irr.ne_zero
    · exact natDegree_le_of_dvd key (minpoly.ne_zero hα)
  apply minpoly.dvd F α
  rw [← eval_map_algebraMap]; rw [eval_rootOfSplits]

end Gal

end Polynomial
