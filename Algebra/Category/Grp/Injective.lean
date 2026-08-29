/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.GroupTheory.Divisible
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Injective objects in the category of abelian groups

In this file we prove that divisible groups are injective objects in category of (additive) abelian
groups. The proof that the category of abelian groups has enough injective objects can be found
in `Mathlib/Algebra/Category/Grp/EnoughInjectives.lean`.

## Main results

- `AddCommGrpCat.injective_of_divisible` : a divisible group is also an injective object.

-/

public section

open CategoryTheory

universe u

variable (A : Type u) [AddCommGroup A]

/--
theorem `Module.Baer.of_divisible` / 定理 `Module.Baer.of_divisible`

English:
theorem Module.Baer.of_divisible
  given: [DivisibleBy A Int]
  statement: Module.Baer Int A
  proof: fun I g => by
  rcases IsPrincipalIdealRing.principal I with ⟨m, rfl⟩
  obtain rfl | h0 := eq_or_ne m 0
  · refine ⟨0, fun n hn => ?_⟩
    rw [Submodule.span_zero_singleton] at hn
    subst hn
    exact (map_zero g).symm
  let gₘ := g ⟨m, Submodule.subset_span (Set.mem_singleton _)⟩
  refine ⟨LinearMap.toSpanSingleton Int A (DivisibleBy.div gₘ m), fun n hn => ?_⟩
  rcases Submodule.mem_span_singleton.mp hn with ⟨n, rfl⟩
  rw [map_zsmul]; rw [LinearMap.toSpanSingleton_apply]; rw [DivisibleBy.div_cancel gₘ h0]; rw [← map_zsmul g]; rw [SetLike.mk_smul_mk]

中文:
定理 模.Baer.of_divisible
  条件: [DivisibleBy A 整数]
  结论: 模.Baer 整数 A
  证明: fun I g => by
  rcases IsPrincipalIdealRing.principal I with ⟨m, rfl⟩
  obtain rfl | h0 := eq_or_ne m 0
  · refine ⟨0, fun n hn => ?_⟩
    rw [Submodule.span_zero_singleton] at hn
    subst hn
    exact (map_zero g).symm
  let gₘ := g ⟨m, Submodule.subset_span (Set.mem_singleton _)⟩
  refine ⟨LinearMap.toSpanSingleton Int A (DivisibleBy.div gₘ m), fun n hn => ?_⟩
  rcases Submodule.mem_span_singleton.mp hn with ⟨n, rfl⟩
  rw [map_zsmul]; rw [LinearMap.toSpanSingleton_apply]; rw [DivisibleBy.div_cancel gₘ h0]; rw [← map_zsmul g]; rw [SetLike.mk_smul_mk]

Depends on / 依赖: DivisibleBy, DivisibleBy.div, DivisibleBy.div_cancel, IsPrincipalIdealRing, IsPrincipalIdealRing.principal, LinearMap, LinearMap.toSpanSingleton, LinearMap.toSpanSingleton_apply, Set.mem_singleton, Submodule, Submodule.mem_span_singleton.mp, Submodule.span_zero_singleton, Submodule.subset_span, div_cancel, eq_or_ne, map_z, map_zero, map_zsmul, mem_singleton, mem_span_singleton
-/
theorem Module.Baer.of_divisible [DivisibleBy A Int] : Module.Baer Int A := fun I g => by
  rcases IsPrincipalIdealRing.principal I with ⟨m, rfl⟩
  obtain rfl | h0 := eq_or_ne m 0
  · refine ⟨0, fun n hn => ?_⟩
    rw [Submodule.span_zero_singleton] at hn
    subst hn
    exact (map_zero g).symm
  let gₘ := g ⟨m, Submodule.subset_span (Set.mem_singleton _)⟩
  refine ⟨LinearMap.toSpanSingleton Int A (DivisibleBy.div gₘ m), fun n hn => ?_⟩
  rcases Submodule.mem_span_singleton.mp hn with ⟨n, rfl⟩
  rw [map_zsmul]; rw [LinearMap.toSpanSingleton_apply]; rw [DivisibleBy.div_cancel gₘ h0]; rw [← map_zsmul g]; rw [SetLike.mk_smul_mk]

namespace AddCommGrpCat

/--
theorem `injective_as_module_iff` / 定理 `injective_as_module_iff`

English:
theorem injective_as_module_iff
  statement: Injective (ModuleCat.of Int A) ↔
  proof: ((forget₂ (ModuleCat Int) AddCommGrpCat).asEquivalence.map_injective_iff (ModuleCat.of Int A)).symm

中文:
定理 injective_as_module_iff
  结论: 单射 (模范畴.of 整数 A) ↔
  证明: ((forget₂ (ModuleCat Int) AddCommGrpCat).asEquivalence.map_injective_iff (ModuleCat.of Int A)).symm

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.of
-/
theorem injective_as_module_iff : Injective (ModuleCat.of Int A) ↔
    Injective (C := AddCommGrpCat) (AddCommGrpCat.of A) :=
  ((forget₂ (ModuleCat Int) AddCommGrpCat).asEquivalence.map_injective_iff (ModuleCat.of Int A)).symm

/--
Instance `injective_of_divisible` / 实例 `injective_of_divisible`

English:
instance injective_of_divisible
  signature: [DivisibleBy A Int]
  body: (injective_as_module_iff A).mp
    Module.injective_object_of_injective_module (inj := (Module.Baer.of_divisible A).injective)

中文:
实例 injective_of_divisible
  签名: [DivisibleBy A 整数]
  定义体: (injective_as_module_iff A).mp
    Module.injective_object_of_injective_module (inj := (Module.Baer.of_divisible A).injective)

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.of
-/
instance injective_of_divisible [DivisibleBy A Int] :
    Injective (C := AddCommGrpCat) (AddCommGrpCat.of A) :=
(injective_as_module_iff A).mp
    Module.injective_object_of_injective_module (inj := (Module.Baer.of_divisible A).injective)

end AddCommGrpCat
