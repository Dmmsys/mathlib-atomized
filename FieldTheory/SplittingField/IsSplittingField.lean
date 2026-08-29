/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Mathlib.RingTheory.Adjoin.Field

/-!
# Splitting fields

This file introduces the notion of a splitting field of a polynomial and provides an embedding from
a splitting field to any field that splits the polynomial. A polynomial `f : K[X]` splits
over a field extension `L` of `K` if it is zero or all of its irreducible factors over `L` have
degree `1`. A field extension of `K` of a polynomial `f : K[X]` is called a splitting field
if it is the smallest field extension of `K` such that `f` splits.

## Main definitions

* `Polynomial.IsSplittingField`: A predicate on a field to be a splitting field of a polynomial
  `f`.

## Main statements

* `Polynomial.IsSplittingField.lift`: An embedding of a splitting field of the polynomial `f` into
  another field such that `f` splits.

-/

@[expose] public section

noncomputable section

universe u v w

variable {F : Type u} (K : Type v) (L : Type w)

namespace Polynomial

variable [Field K] [Field L] [Field F] [Algebra K L]

/-- Typeclass characterising splitting fields. -/
@[stacks 09HV "Predicate version"]
/--
Definition of `IsSplittingField` / `IsSplittingField` 的定义

English:
class IsSplittingField
  parameters: (f : K[X])
  axioms and operations (2):
    - splits' : Splits (f.map (algebraMap K L))
    - adjoin_rootSet' : Algebra.adjoin K (f.rootSet L : Set L) = ⊤

中文:
类 是分裂域
  参数: (f : K[X])
  公理与运算 (2 个):
    - splits' : Splits (f.map (algebraMap K L))
    - adjoin_rootSet' : 代数.adjoin K (f.rootSet L : 集合 L) = ⊤
-/
class IsSplittingField (f : K[X]) : Prop where
  splits' : Splits (f.map (algebraMap K L))
  adjoin_rootSet' : Algebra.adjoin K (f.rootSet L : Set L) = ⊤

namespace IsSplittingField

variable {K}

/--
theorem `splits` / 定理 `splits`

English:
theorem splits
  given: (f : K[X]) [IsSplittingField K L f]
  statement: Splits (f.map (algebraMap K L))
  proof: splits'

中文:
定理 splits
  条件: (f : K[X]) [是分裂域 K L f]
  结论: Splits (f.map (algebraMap K L))
  证明: splits'

Depends on / 依赖: splits
-/
theorem splits (f : K[X]) [IsSplittingField K L f] : Splits (f.map (algebraMap K L)) :=
  splits'

/--
theorem `adjoin_rootSet` / 定理 `adjoin_rootSet`

English:
theorem adjoin_rootSet
  given: (f : K[X]) [IsSplittingField K L f]
  proof: adjoin_rootSet'

中文:
定理 adjoin_rootSet
  条件: (f : K[X]) [是分裂域 K L f]
  证明: adjoin_rootSet'

Depends on / 依赖: adjoin_rootSet
-/
theorem adjoin_rootSet (f : K[X]) [IsSplittingField K L f] :
    Algebra.adjoin K (f.rootSet L : Set L) = ⊤ :=
  adjoin_rootSet'

section ScalarTower

variable [Algebra F K] [Algebra F L] [IsScalarTower F K L]

/--
Instance `map` / 实例 `map`

English:
instance map
  signature: (f : F[X]) [IsSplittingField F L f]
  body: ⟨by rw [map_map, ← IsScalarTower.algebraMap_eq]; exact splits L f,
Subalgebra.restrictScalars_injective F by
      rw [rootSet]; rw [aroots]; rw [map_map]; rw [← IsScalarTower.algebraMap_eq]; rw [Subalgebra.restrictScalars_top]; rw [eq_top_iff]; rw [← adjoin_rootSet L f]; rw [Algebra.adjoin_le_iff]


中文:
实例 map
  签名: (f : F[X]) [是分裂域 F L f]
  定义体: ⟨by rw [map_map, ← IsScalarTower.algebraMap_eq]; exact splits L f,
Subalgebra.restrictScalars_injective F by
      rw [rootSet]; rw [aroots]; rw [map_map]; rw [← IsScalarTower.algebraMap_eq]; rw [Subalgebra.restrictScalars_top]; rw [eq_top_iff]; rw [← adjoin_rootSet L f]; rw [Algebra.adjoin_le_iff]


Depends on / 依赖: Algebra, Algebra.adjoin_le_iff, Algebra.subset_adjoin, IsScalarTower, IsScalarTower.algebraMap_eq, Subalgebra, Subalgebra.restrictScalars_injective, Subalgebra.restrictScalars_top, adjoin_le_iff, adjoin_rootSet, algebraMap_eq, aroots, eq_top_iff, map_map, restrictScalars_injective, restrictScalars_top, rootSet, splits, subset_adjoin
-/
instance map (f : F[X]) [IsSplittingField F L f] : IsSplittingField K L (f.map <| algebraMap F K) :=
  ⟨by rw [map_map, ← IsScalarTower.algebraMap_eq]; exact splits L f,
Subalgebra.restrictScalars_injective F by
      rw [rootSet]; rw [aroots]; rw [map_map]; rw [← IsScalarTower.algebraMap_eq]; rw [Subalgebra.restrictScalars_top]; rw [eq_top_iff]; rw [← adjoin_rootSet L f]; rw [Algebra.adjoin_le_iff]
      exact fun x hx => @Algebra.subset_adjoin K _ _ _ _ _ _ hx⟩

/--
theorem `splits_iff` / 定理 `splits_iff`

English:
theorem splits_iff
  given: (f : K[X]) [IsSplittingField K L f]
  proof: by
    rw [eq_bot_iff]; rw [← adjoin_rootSet L f]; rw [rootSet]; rw [aroots]; rw [h.roots_map]; rw [Algebra.adjoin_le_iff]
    intro y hy
    classical
    rw [Multiset.toFinset_map]; rw [Finset.mem_coe]; rw [Finset.mem_image] at hy
    obtain ⟨x : K, -, hxy : algebraMap K L x = y⟩ := hy
    rw [← h

中文:
定理 splits_iff
  条件: (f : K[X]) [是分裂域 K L f]
  证明: by
    rw [eq_bot_iff]; rw [← adjoin_rootSet L f]; rw [rootSet]; rw [aroots]; rw [h.roots_map]; rw [Algebra.adjoin_le_iff]
    intro y hy
    classical
    rw [Multiset.toFinset_map]; rw [Finset.mem_coe]; rw [Finset.mem_image] at hy
    obtain ⟨x : K, -, hxy : algebraMap K L x = y⟩ := hy
    rw [← h

Depends on / 依赖: Algebra, Algebra.adjoin_le_iff, Algebra.bijective_algebraM, Finset, Finset.mem_coe, Finset.mem_image, Multiset, Multiset.toFinset_map, Polynomial, Polynomial.map_id, RingEquiv, RingEquiv.ofBijective, RingEquiv.self_trans_symm, RingEquiv.toRingHom_refl, SetLike, SetLike.mem_coe, Subalgebra, Subalgebra.algebraMap_mem, adjoin_le_iff, adjoin_rootSet
-/
theorem splits_iff (f : K[X]) [IsSplittingField K L f] :
    Splits f ↔ (⊤ : Subalgebra K L) = ⊥ where
  mp h := by
    rw [eq_bot_iff]; rw [← adjoin_rootSet L f]; rw [rootSet]; rw [aroots]; rw [h.roots_map]; rw [Algebra.adjoin_le_iff]
    intro y hy
    classical
    rw [Multiset.toFinset_map]; rw [Finset.mem_coe]; rw [Finset.mem_image] at hy
    obtain ⟨x : K, -, hxy : algebraMap K L x = y⟩ := hy
    rw [← hxy]
exact SetLike.mem_coe.2 Subalgebra.algebraMap_mem _ _
  mpr h := by
    rw [← Polynomial.map_id (p := f)]; rw [← RingEquiv.toRingHom_refl]; rw [← RingEquiv.self_trans_symm
      (RingEquiv.ofBijective _ <| Algebra.bijective_algebraMap_iff.2 h)]; rw [RingEquiv.toRingHom_trans]; rw [← map_map]
    apply (splits L f).map

/--
theorem `IsScalarTower.splits` / 定理 `IsScalarTower.splits`

English:
theorem IsScalarTower.splits
  given: (f : F[X]) [IsSplittingField K L (mapAlg F K f)]
  proof: by
  rw [mapAlg_comp K L f]; rw [mapAlg_eq_map]
  apply IsSplittingField.splits

中文:
定理 标量塔.splits
  条件: (f : F[X]) [是分裂域 K L (mapAlg F K f)]
  证明: by
  rw [mapAlg_comp K L f]; rw [mapAlg_eq_map]
  apply IsSplittingField.splits

Depends on / 依赖: IsSplittingField, IsSplittingField.splits, mapAlg_comp, mapAlg_eq_map, splits
-/
theorem IsScalarTower.splits (f : F[X]) [IsSplittingField K L (mapAlg F K f)] :
    Splits (mapAlg F L f) := by
  rw [mapAlg_comp K L f]; rw [mapAlg_eq_map]
  apply IsSplittingField.splits

/--
theorem `mul` / 定理 `mul`

English:
theorem mul
  statement: (f g : F[X]) (hf : f != 0) (hg : g != 0) [IsSplittingField F K f]
  proof: by
  constructor
  · rw [Polynomial.map_mul, IsScalarTower.algebraMap_eq F K L, ← map_map, ← map_map]
    exact Splits.mul ((splits K f).map _) (splits L (g.map (algebraMap F K)))
  · classical
    rw [rootSet]; rw [aroots_mul (mul_ne_zero hf hg)]; rw [Multiset.toFinset_add]; rw [Finset.coe_union]; 

中文:
定理 mul
  结论: (f g : F[X]) (hf : f != 0) (hg : g != 0) [是分裂域 F K f]
  证明: by
  constructor
  · rw [Polynomial.map_mul, IsScalarTower.algebraMap_eq F K L, ← map_map, ← map_map]
    exact Splits.mul ((splits K f).map _) (splits L (g.map (algebraMap F K)))
  · classical
    rw [rootSet]; rw [aroots_mul (mul_ne_zero hf hg)]; rw [Multiset.toFinset_add]; rw [Finset.coe_union]; 

Depends on / 依赖: Algebra, Algebra.adjoin_union_eq_adjoin_adjoin, Finset, Finset.coe_image, Finset.coe_union, IsScalarTower, IsScalarTower.algebraMap_eq, Multiset, Multiset.toFinset_add, Multiset.toFinset_map, Polynomial, Polynomial.map_mul, Splits, Splits.mul, adjoin_union_eq_adjoin_adjoin, algebraMap, algebraMap_eq, aroots_def, aroots_mul, classical
-/
theorem mul (f g : F[X]) (hf : f != 0) (hg : g != 0) [IsSplittingField F K f]
    [IsSplittingField K L (g.map <| algebraMap F K)] : IsSplittingField F L (f * g) := by
  constructor
  · rw [Polynomial.map_mul, IsScalarTower.algebraMap_eq F K L, ← map_map, ← map_map]
    exact Splits.mul ((splits K f).map _) (splits L (g.map (algebraMap F K)))
  · classical
    rw [rootSet]; rw [aroots_mul (mul_ne_zero hf hg)]; rw [Multiset.toFinset_add]; rw [Finset.coe_union]; rw [Algebra.adjoin_union_eq_adjoin_adjoin]; rw [aroots_def]; rw [aroots_def]; rw [IsScalarTower.algebraMap_eq F K L]; rw [← map_map]; rw [(splits K f).roots_map]; rw [Multiset.toFinset_map]; rw [Finset.coe_image]; rw [Algebra.adjoin_algebraMap]; rw [← rootSet]; rw [adjoin_rootSet]; rw [Algebra.map_top]; rw [IsScalarTower.adjoin_range_toAlgHom]; rw [← map_map]; rw [← rootSet]; rw [adjoin_rootSet]; rw [Subalgebra.restrictScalars_top]

end ScalarTower

open scoped Classical in
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: [Algebra K F] (f : K[X]) [IsSplittingField K L f]
  body: if hf0 : f = 0 then
(Algebra.ofId K F).comp
(Algebra.botEquiv K L : (⊥ : Subalgebra K L) ->ₐ[K] K).comp by
        rw [← (splits_iff L f).1 (show f.Splits by simp [hf0])]
        exact Algebra.toTop
  else AlgHom.comp (by
    rw [← adjoin_rootSet L f]
    exact Classical.choice (lift_of_splits _ fun

中文:
定义 lift
  签名: [代数 K F] (f : K[X]) [是分裂域 K L f]
  定义体: if hf0 : f = 0 then
(Algebra.ofId K F).comp
(Algebra.botEquiv K L : (⊥ : Subalgebra K L) ->ₐ[K] K).comp by
        rw [← (splits_iff L f).1 (show f.Splits by simp [hf0])]
        exact Algebra.toTop
  else AlgHom.comp (by
    rw [← adjoin_rootSet L f]
    exact Classical.choice (lift_of_splits _ fun

Depends on / 依赖: AlgHom, AlgHom.comp, Algebra, Algebra.botEquiv, Algebra.ofId, Algebra.toTop, Classical, Classical.choice, IsAlgebraic, IsAlgebraic.isIntegral, Multiset, Multiset.mem_toFinset.mp, Splits, Subalgebra, adjoin_rootSet, botEquiv, choice, f.Splits, hf.of_dvd, isIntegral
-/
def lift [Algebra K F] (f : K[X]) [IsSplittingField K L f]
    (hf : Splits (f.map (algebraMap K F))) : L ->ₐ[K] F :=
  if hf0 : f = 0 then
(Algebra.ofId K F).comp
(Algebra.botEquiv K L : (⊥ : Subalgebra K L) ->ₐ[K] K).comp by
        rw [← (splits_iff L f).1 (show f.Splits by simp [hf0])]
        exact Algebra.toTop
  else AlgHom.comp (by
    rw [← adjoin_rootSet L f]
    exact Classical.choice (lift_of_splits _ fun y hy =>
have : aeval y f = 0 := (eval₂_eq_eval_map _).trans
        (mem_roots <| map_ne_zero hf0).1 (Multiset.mem_toFinset.mp hy)
    ⟨IsAlgebraic.isIntegral ⟨f, hf0, this⟩, hf.of_dvd (map_ne_zero hf0)
      ((map_dvd_map' _).mpr (minpoly.dvd K y this))⟩)) Algebra.toTop

/--
theorem `finiteDimensional` / 定理 `finiteDimensional`

English:
theorem finiteDimensional
  given: (f : K[X]) [IsSplittingField K L f]
  statement: FiniteDimensional K L
  proof: by
  classical
  exact ⟨@Algebra.top_toSubmodule K L _ _ _ ▸
    adjoin_rootSet L f ▸ fg_adjoin_of_finite (Finset.finite_toSet _) fun y hy =>
      if hf : f = 0 then by rw [hf, rootSet_zero] at hy; cases hy
      else IsAlgebraic.isIntegral ⟨f, hf, (mem_rootSet'.mp hy).2⟩⟩

中文:
定理 finiteDimensional
  条件: (f : K[X]) [是分裂域 K L f]
  结论: 有限维 K L
  证明: by
  classical
  exact ⟨@Algebra.top_toSubmodule K L _ _ _ ▸
    adjoin_rootSet L f ▸ fg_adjoin_of_finite (Finset.finite_toSet _) fun y hy =>
      if hf : f = 0 then by rw [hf, rootSet_zero] at hy; cases hy
      else IsAlgebraic.isIntegral ⟨f, hf, (mem_rootSet'.mp hy).2⟩⟩

Depends on / 依赖: Algebra, Algebra.top_toSubmodule, Finset, Finset.finite_toSet, IsAlgebraic, IsAlgebraic.isIntegral, adjoin_rootSet, classical, fg_adjoin_of_finite, finite_toSet, isIntegral, mem_rootSet, rootSet_zero, top_toSubmodule
-/
theorem finiteDimensional (f : K[X]) [IsSplittingField K L f] : FiniteDimensional K L := by
  classical
  exact ⟨@Algebra.top_toSubmodule K L _ _ _ ▸
    adjoin_rootSet L f ▸ fg_adjoin_of_finite (Finset.finite_toSet _) fun y hy =>
      if hf : f = 0 then by rw [hf, rootSet_zero] at hy; cases hy
      else IsAlgebraic.isIntegral ⟨f, hf, (mem_rootSet'.mp hy).2⟩⟩

/--
theorem `IsScalarTower.isAlgebraic` / 定理 `IsScalarTower.isAlgebraic`

English:
theorem IsScalarTower.isAlgebraic
  statement: [Algebra F K] [Algebra F L] [Algebra.IsAlgebraic F K]
  proof: by
  have : FiniteDimensional K L := IsSplittingField.finiteDimensional L f
  exact Algebra.IsAlgebraic.trans F K L

中文:
定理 标量塔.isAlgebraic
  结论: [代数 F K] [代数 F L] [代数.是代数 F K]
  证明: by
  have : FiniteDimensional K L := IsSplittingField.finiteDimensional L f
  exact Algebra.IsAlgebraic.trans F K L

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.trans, FiniteDimensional, IsAlgebraic, IsSplittingField, IsSplittingField.finiteDimensional, finiteDimensional
-/
theorem IsScalarTower.isAlgebraic [Algebra F K] [Algebra F L] [Algebra.IsAlgebraic F K]
    [IsScalarTower F K L] (f : K[X]) [IsSplittingField K L f] :
    Algebra.IsAlgebraic F L := by
  have : FiniteDimensional K L := IsSplittingField.finiteDimensional L f
  exact Algebra.IsAlgebraic.trans F K L

/--
theorem `of_algEquiv` / 定理 `of_algEquiv`

English:
theorem of_algEquiv
  given: [Algebra K F] (p : K[X]) (f : F ≃ₐ[K] L) [IsSplittingField K F p]
  proof: by
  constructor
  · rw [← f.toAlgHom.comp_algebraMap, ← map_map]
    exact (splits F p).map _
  · rw [← (AlgHom.range_eq_top f.toAlgHom).mpr f.surjective,
      (splits F p).adjoin_rootSet_eq_range, adjoin_rootSet F p]

中文:
定理 of_algEquiv
  条件: [代数 K F] (p : K[X]) (f : F ≃ₐ[K] L) [是分裂域 K F p]
  证明: by
  constructor
  · rw [← f.toAlgHom.comp_algebraMap, ← map_map]
    exact (splits F p).map _
  · rw [← (AlgHom.range_eq_top f.toAlgHom).mpr f.surjective,
      (splits F p).adjoin_rootSet_eq_range, adjoin_rootSet F p]

Depends on / 依赖: AlgHom, AlgHom.range_eq_top, adjoin_rootSet, adjoin_rootSet_eq_range, comp_algebraMap, f.surjective, f.toAlgHom, f.toAlgHom.comp_algebraMap, map_map, range_eq_top, splits, surjective, toAlgHom
-/
theorem of_algEquiv [Algebra K F] (p : K[X]) (f : F ≃ₐ[K] L) [IsSplittingField K F p] :
    IsSplittingField K L p := by
  constructor
  · rw [← f.toAlgHom.comp_algebraMap, ← map_map]
    exact (splits F p).map _
  · rw [← (AlgHom.range_eq_top f.toAlgHom).mpr f.surjective,
      (splits F p).adjoin_rootSet_eq_range, adjoin_rootSet F p]

/--
theorem `adjoin_rootSet_eq_range` / 定理 `adjoin_rootSet_eq_range`

English:
theorem adjoin_rootSet_eq_range
  given: [Algebra K F] (f : K[X]) [IsSplittingField K L f] (i : L ->ₐ[K] F)
  proof: ((splits L f).adjoin_rootSet_eq_range i).mpr (adjoin_rootSet L f)

中文:
定理 adjoin_rootSet_eq_range
  条件: [代数 K F] (f : K[X]) [是分裂域 K L f] (i : L ->ₐ[K] F)
  证明: ((splits L f).adjoin_rootSet_eq_range i).mpr (adjoin_rootSet L f)

Depends on / 依赖: adjoin_rootSet, adjoin_rootSet_eq_range, splits
-/
theorem adjoin_rootSet_eq_range [Algebra K F] (f : K[X]) [IsSplittingField K L f] (i : L ->ₐ[K] F) :
    Algebra.adjoin K (rootSet f F) = i.range :=
  ((splits L f).adjoin_rootSet_eq_range i).mpr (adjoin_rootSet L f)

end IsSplittingField

end Polynomial

open Polynomial

variable {K L} [Field K] [Field L] [Algebra K L] {p : K[X]} {F : IntermediateField K L}

/--
theorem `IntermediateField.splits_of_splits` / 定理 `IntermediateField.splits_of_splits`

English:
theorem IntermediateField.splits_of_splits
  statement: (h : (p.map (algebraMap K L)).Splits)
  proof: by
  classical
  have := Splits.of_splits_map (f := p.map (algebraMap K F)) (algebraMap F L)
  rw [Polynomial.map_map]; rw [← IsScalarTower.algebraMap_eq] at this
  exact this h (by simpa [rootSet_def] using hF)

中文:
定理 中间域.splits_of_splits
  结论: (h : (p.map (algebraMap K L)).Splits)
  证明: by
  classical
  have := Splits.of_splits_map (f := p.map (algebraMap K F)) (algebraMap F L)
  rw [Polynomial.map_map]; rw [← IsScalarTower.algebraMap_eq] at this
  exact this h (by simpa [rootSet_def] using hF)

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_eq, Polynomial, Polynomial.map_map, Splits, Splits.of_splits_map, algebraMap, algebraMap_eq, classical, map_map, of_splits_map, p.map, rootSet_def
-/
theorem IntermediateField.splits_of_splits (h : (p.map (algebraMap K L)).Splits)
    (hF : forall x in p.rootSet L, x in F) : (p.map (algebraMap K F)).Splits := by
  classical
  have := Splits.of_splits_map (f := p.map (algebraMap K F)) (algebraMap F L)
  rw [Polynomial.map_map]; rw [← IsScalarTower.algebraMap_eq] at this
  exact this h (by simpa [rootSet_def] using hF)

/--
theorem `IntermediateField.splits_iff_mem` / 定理 `IntermediateField.splits_iff_mem`

English:
theorem IntermediateField.splits_iff_mem
  given: (h : (p.map (algebraMap K L)).Splits)
  proof: by
  refine ⟨?_, IntermediateField.splits_of_splits h⟩
  intro hF
  rw [← hF.image_rootSet F.val]; rw [Set.forall_mem_image]
  exact fun x _ => x.2

中文:
定理 中间域.splits_iff_mem
  条件: (h : (p.map (algebraMap K L)).Splits)
  证明: by
  refine ⟨?_, IntermediateField.splits_of_splits h⟩
  intro hF
  rw [← hF.image_rootSet F.val]; rw [Set.forall_mem_image]
  exact fun x _ => x.2

Depends on / 依赖: F.val, IntermediateField, IntermediateField.splits_of_splits, Set.forall_mem_image, forall_mem_image, hF.image_rootSet, image_rootSet, splits_of_splits
-/
theorem IntermediateField.splits_iff_mem (h : (p.map (algebraMap K L)).Splits) :
    (p.map (algebraMap K F)).Splits ↔ forall x in p.rootSet L, x in F := by
  refine ⟨?_, IntermediateField.splits_of_splits h⟩
  intro hF
  rw [← hF.image_rootSet F.val]; rw [Set.forall_mem_image]
  exact fun x _ => x.2

/--
theorem `IsIntegral.mem_intermediateField_of_minpoly_splits` / 定理 `IsIntegral.mem_intermediateField_of_minpoly_splits`

English:
theorem IsIntegral.mem_intermediateField_of_minpoly_splits
  statement: {x : L} (int : IsIntegral K x)
  proof: by
  rw [← F.fieldRange_val]; exact int.mem_range_algebraMap_of_minpoly_splits h

中文:
定理 是整.mem_intermediateField_of_minpoly_splits
  结论: {x : L} (int : 是整 K x)
  证明: by
  rw [← F.fieldRange_val]; exact int.mem_range_algebraMap_of_minpoly_splits h

Depends on / 依赖: F.fieldRange_val, fieldRange_val, int.mem_range_algebraMap_of_minpoly_splits, mem_range_algebraMap_of_minpoly_splits
-/
theorem IsIntegral.mem_intermediateField_of_minpoly_splits {x : L} (int : IsIntegral K x)
    {F : IntermediateField K L} (h : Splits ((minpoly K x).map (algebraMap K F))) : x in F := by
  rw [← F.fieldRange_val]; exact int.mem_range_algebraMap_of_minpoly_splits h

/--
theorem `isSplittingField_iff_intermediateField` / 定理 `isSplittingField_iff_intermediateField`

English:
theorem isSplittingField_iff_intermediateField
  statement: p.IsSplittingField K L ↔
  proof: by
  rw [← IntermediateField.toSubalgebra_injective.eq_iff]; rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic fun _ => isAlgebraic_of_mem_rootSet]
  exact ⟨fun ⟨spl, adj⟩ => ⟨spl, adj⟩, fun ⟨spl, adj⟩ => ⟨spl, adj⟩⟩

中文:
定理 isSplittingField_iff_intermediateField
  结论: p.是分裂域 K L ↔
  证明: by
  rw [← IntermediateField.toSubalgebra_injective.eq_iff]; rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic fun _ => isAlgebraic_of_mem_rootSet]
  exact ⟨fun ⟨spl, adj⟩ => ⟨spl, adj⟩, fun ⟨spl, adj⟩ => ⟨spl, adj⟩⟩

Depends on / 依赖: IntermediateField, IntermediateField.adjoin_toSubalgebra_of_isAlgebraic, IntermediateField.toSubalgebra_injective.eq_iff, adjoin_toSubalgebra_of_isAlgebraic, eq_iff, isAlgebraic_of_mem_rootSet, toSubalgebra_injective
-/
theorem isSplittingField_iff_intermediateField : p.IsSplittingField K L ↔
    (p.map (algebraMap K L)).Splits ∧ IntermediateField.adjoin K (p.rootSet L) = ⊤ := by
  rw [← IntermediateField.toSubalgebra_injective.eq_iff]; rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic fun _ => isAlgebraic_of_mem_rootSet]
  exact ⟨fun ⟨spl, adj⟩ => ⟨spl, adj⟩, fun ⟨spl, adj⟩ => ⟨spl, adj⟩⟩

-- Note: p.Splits (algebraMap F E) also works
/--
theorem `IntermediateField.isSplittingField_iff` / 定理 `IntermediateField.isSplittingField_iff`

English:
theorem IntermediateField.isSplittingField_iff
  proof: by
  suffices _ -> (Algebra.adjoin K (p.rootSet F) = ⊤ ↔ F = adjoin K (p.rootSet L)) by
    exact ⟨fun h => ⟨h.1, (this h.1).mp h.2⟩, fun h => ⟨h.1, (this h.1).mpr h.2⟩⟩
  rw [← toSubalgebra_injective.eq_iff]; rw [adjoin_toSubalgebra_of_isAlgebraic fun x => isAlgebraic_of_mem_rootSet]
  refine fun h

中文:
定理 中间域.isSplittingField_iff
  证明: by
  suffices _ -> (Algebra.adjoin K (p.rootSet F) = ⊤ ↔ F = adjoin K (p.rootSet L)) by
    exact ⟨fun h => ⟨h.1, (this h.1).mp h.2⟩, fun h => ⟨h.1, (this h.1).mpr h.2⟩⟩
  rw [← toSubalgebra_injective.eq_iff]; rw [adjoin_toSubalgebra_of_isAlgebraic fun x => isAlgebraic_of_mem_rootSet]
  refine fun h

Depends on / 依赖: Algebra, Algebra.adjoin, F.range_val, F.val, adjoin, adjoin_rootSet_eq_range, adjoin_toSubalgebra_of_isAlgebraic, eq_comm, eq_iff, hp.adjoin_rootSet_eq_range, isAlgebraic_of_mem_rootSet, p.rootSet, range_val, rootSet, symm.trans, toSubalgebra_injective, toSubalgebra_injective.eq_iff
-/
theorem IntermediateField.isSplittingField_iff :
    p.IsSplittingField K F ↔ (p.map (algebraMap K F)).Splits ∧ F = adjoin K (p.rootSet L) := by
  suffices _ -> (Algebra.adjoin K (p.rootSet F) = ⊤ ↔ F = adjoin K (p.rootSet L)) by
    exact ⟨fun h => ⟨h.1, (this h.1).mp h.2⟩, fun h => ⟨h.1, (this h.1).mpr h.2⟩⟩
  rw [← toSubalgebra_injective.eq_iff]; rw [adjoin_toSubalgebra_of_isAlgebraic fun x => isAlgebraic_of_mem_rootSet]
  refine fun hp => (hp.adjoin_rootSet_eq_range F.val).symm.trans ?_
  rw [← F.range_val]; rw [eq_comm]

/--
theorem `IntermediateField.adjoin_rootSet_isSplittingField` / 定理 `IntermediateField.adjoin_rootSet_isSplittingField`

English:
theorem IntermediateField.adjoin_rootSet_isSplittingField
  given: (hp : (p.map (algebraMap K L)).Splits)
  proof: isSplittingField_iff.mpr ⟨splits_of_splits hp fun _ hx => subset_adjoin K (p.rootSet L) hx, rfl⟩

中文:
定理 中间域.adjoin_rootSet_isSplittingField
  条件: (hp : (p.map (algebraMap K L)).Splits)
  证明: isSplittingField_iff.mpr ⟨splits_of_splits hp fun _ hx => subset_adjoin K (p.rootSet L) hx, rfl⟩

Depends on / 依赖: isSplittingField_iff, isSplittingField_iff.mpr, p.rootSet, rootSet, splits_of_splits, subset_adjoin
-/
theorem IntermediateField.adjoin_rootSet_isSplittingField (hp : (p.map (algebraMap K L)).Splits) :
    p.IsSplittingField K (adjoin K (p.rootSet L)) :=
  isSplittingField_iff.mpr ⟨splits_of_splits hp fun _ hx => subset_adjoin K (p.rootSet L) hx, rfl⟩

/--
theorem `Polynomial.isSplittingField_C` / 定理 `Polynomial.isSplittingField_C`

English:
theorem Polynomial.isSplittingField_C
  given: (a : K)
  statement: Polynomial.IsSplittingField K K (C a) where
  proof: by simp
  adjoin_rootSet' := by simp

中文:
定理 多项式.isSplittingField_C
  条件: (a : K)
  结论: 多项式.是分裂域 K K (C a) where
  证明: by simp
  adjoin_rootSet' := by simp

Depends on / 依赖: adjoin_rootSet
-/
theorem Polynomial.isSplittingField_C (a : K) : Polynomial.IsSplittingField K K (C a) where
  splits' := by simp
  adjoin_rootSet' := by simp
