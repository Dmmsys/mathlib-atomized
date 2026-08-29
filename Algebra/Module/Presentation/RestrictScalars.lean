/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Module.Presentation.DirectSum
public import Mathlib.Algebra.Module.Presentation.Cokernel

/-!
# Presentation of the restriction of scalars of a module

Given a morphism of rings `A → B` and a `B`-module `M`, we obtain a presentation
of `M` as a `A`-module from a presentation of `M` as `B`-module,
a presentation of `B` as a `A`-module (and some additional data).

## TODO
* deduce that if `B` is a finitely presented as an `A`-module and `M` is
  finitely presented as an `B`-module, then `M` is finitely presented as an `A`-module

-/

@[expose] public section

namespace Module

variable {B : Type*} [Ring B] {M : Type*} [AddCommGroup M] [Module B M]
  [DecidableEq B]
  (presM : Presentation B M) [DecidableEq presM.G]
  {A : Type*} [CommRing A] [Algebra A B] [Module A M] [IsScalarTower A B M]
  (presB : Presentation A B)

namespace Presentation

/--
Definition of `RestrictScalarsData` / `RestrictScalarsData` 的定义

English:
abbreviation RestrictScalarsData
  signature: : Type _
  body: (presB.finsupp presM.G).CokernelData
    (LinearMap.restrictScalars A presM.map)
    (fun (⟨g, g'⟩ : presB.G × presM.R) => presB.var g • Finsupp.single g' (1 : B))

中文:
缩写 RestrictScalarsData
  签名: : 类型 _
  定义体: (presB.finsupp presM.G).CokernelData
    (LinearMap.restrictScalars A presM.map)
    (fun (⟨g, g'⟩ : presB.G × presM.R) => presB.var g • Finsupp.single g' (1 : B))

Depends on / 依赖: CokernelData, Finsupp, Finsupp.single, LinearMap, LinearMap.restrictScalars, finsupp, presB.G, presB.finsupp, presB.var, presM.G, presM.R, presM.map, restrictScalars, single
-/
abbrev RestrictScalarsData : Type _ :=
  (presB.finsupp presM.G).CokernelData
    (LinearMap.restrictScalars A presM.map)
    (fun (⟨g, g'⟩ : presB.G × presM.R) => presB.var g • Finsupp.single g' (1 : B))

variable (data : presM.RestrictScalarsData presB)

/--
Definition of `restrictScalars` / `restrictScalars` 的定义

English:
definition restrictScalars
  signature: : Presentation A M
  body: ofExact (g := LinearMap.restrictScalars A presM.π) (presB.finsupp presM.G) data
    presM.exact presM.surjective_π (by
      ext v
      dsimp
      simp only [Submodule.mem_top, iff_true]
      apply Finsupp.induction
      · simp
      · intro r b w _ _ hw
        refine Submodule.add_mem _ ?_ hw
        obtain ⟨β, rfl⟩ := presB.surjective_π b
        apply Finsupp.induction (motive := fun β => Finsupp.single r (presB.π β) in _)
        · simp
        · intro g a f _ _ hf
          rw [map_add]; rw [Finsupp.single_add]
          refine Submodule.add_mem _ ?_ hf
          rw [← Finsupp.smul_single_one]; rw [← Finsupp.smul_single_one]; rw [map_smul]; rw [Relations.Solution.π_single]; rw [smul_assoc]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨g, r⟩, rfl⟩))

中文:
定义 restrictScalars
  签名: : 呈现 A M
  定义体: ofExact (g := LinearMap.restrictScalars A presM.π) (presB.finsupp presM.G) data
    presM.exact presM.surjective_π (by
      ext v
      dsimp
      simp only [Submodule.mem_top, iff_true]
      apply Finsupp.induction
      · simp
      · intro r b w _ _ hw
        refine Submodule.add_mem _ ?_ hw
        obtain ⟨β, rfl⟩ := presB.surjective_π b
        apply Finsupp.induction (motive := fun β => Finsupp.single r (presB.π β) in _)
        · simp
        · intro g a f _ _ hf
          rw [map_add]; rw [Finsupp.single_add]
          refine Submodule.add_mem _ ?_ hf
          rw [← Finsupp.smul_single_one]; rw [← Finsupp.smul_single_one]; rw [map_smul]; rw [Relations.Solution.π_single]; rw [smul_assoc]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨g, r⟩, rfl⟩))

Depends on / 依赖: Finsupp, Finsupp.induction, Finsupp.single, Finsupp.single_add, Finsupp.smul_single_one, LinearMap, LinearMap.restrictScalars, Submodule, Submodule.add_mem, Submodule.mem_top, add_mem, finsupp, iff_true, map_add, mem_top, motive, ofExact, presB.finsupp, presB.surjective_, presM.G
-/
noncomputable def restrictScalars : Presentation A M :=
  ofExact (g := LinearMap.restrictScalars A presM.π) (presB.finsupp presM.G) data
    presM.exact presM.surjective_π (by
      ext v
      dsimp
      simp only [Submodule.mem_top, iff_true]
      apply Finsupp.induction
      · simp
      · intro r b w _ _ hw
        refine Submodule.add_mem _ ?_ hw
        obtain ⟨β, rfl⟩ := presB.surjective_π b
        apply Finsupp.induction (motive := fun β => Finsupp.single r (presB.π β) in _)
        · simp
        · intro g a f _ _ hf
          rw [map_add]; rw [Finsupp.single_add]
          refine Submodule.add_mem _ ?_ hf
          rw [← Finsupp.smul_single_one]; rw [← Finsupp.smul_single_one]; rw [map_smul]; rw [Relations.Solution.π_single]; rw [smul_assoc]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨g, r⟩, rfl⟩))

end Presentation

end Module
