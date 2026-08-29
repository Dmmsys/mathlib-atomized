/-
Copyright (c) 2025 Stepan Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stepan Nesterov
-/
module

public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic

/-!
# Irreducible representations

This file defines irreducible monoid representations.

-/

public section

namespace Representation

open scoped MonoidAlgebra

variable {G k V W : Type*} [Monoid G] [Field k] [AddCommGroup V] [Module k V] [AddCommGroup W]
    [Module k W] (ρ : Representation k G V) (σ : Representation k G W)

/--
Definition of `IsIrreducible` / `IsIrreducible` 的定义

English:
abbreviation IsIrreducible
  body: IsSimpleOrder (Subrepresentation ρ)

中文:
缩写 IsIrreducible
  定义体: IsSimpleOrder (Subrepresentation ρ)

Depends on / 依赖: IsSimpleOrder, Subrepresentation
-/
abbrev IsIrreducible :=
  IsSimpleOrder (Subrepresentation ρ)

/--
theorem `irreducible_iff_isSimpleModule_asModule` / 定理 `irreducible_iff_isSimpleModule_asModule`

English:
theorem irreducible_iff_isSimpleModule_asModule
  proof: by
  rw [isSimpleModule_iff]
  exact OrderIso.isSimpleOrder_iff Subrepresentation.subrepresentationSubmoduleOrderIso

中文:
定理 irreducible_iff_isSimpleModule_asModule
  证明: by
  rw [isSimpleModule_iff]
  exact OrderIso.isSimpleOrder_iff Subrepresentation.subrepresentationSubmoduleOrderIso

Depends on / 依赖: OrderIso, OrderIso.isSimpleOrder_iff, Subrepresentation, Subrepresentation.subrepresentationSubmoduleOrderIso, isSimpleModule_iff, isSimpleOrder_iff, subrepresentationSubmoduleOrderIso
-/
theorem irreducible_iff_isSimpleModule_asModule :
    IsIrreducible ρ ↔ IsSimpleModule k[G] ρ.asModule := by
  rw [isSimpleModule_iff]
  exact OrderIso.isSimpleOrder_iff Subrepresentation.subrepresentationSubmoduleOrderIso

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isSimpleModule_iff_irreducible_ofModule` / 定理 `isSimpleModule_iff_irreducible_ofModule`

English:
theorem isSimpleModule_iff_irreducible_ofModule
  given: (M : Type*) [AddCommGroup M] [Module k[G] M]
  proof: by
  rw [isSimpleModule_iff]
  exact OrderIso.isSimpleOrder_iff Subrepresentation.submoduleSubrepresentationOrderIso

@[deprecated (since := "2026-02-09")]
alias is_simple_module_iff_irreducible_ofModule := isSimpleModule_iff_irreducible_ofModule

中文:
定理 isSimpleModule_iff_irreducible_ofModule
  条件: (M : 类型) [AddCommGroup M] [Module k[G] M]
  证明: by
  rw [isSimpleModule_iff]
  exact OrderIso.isSimpleOrder_iff Subrepresentation.submoduleSubrepresentationOrderIso

@[deprecated (since := "2026-02-09")]
alias is_simple_module_iff_irreducible_ofModule := isSimpleModule_iff_irreducible_ofModule

Depends on / 依赖: OrderIso, OrderIso.isSimpleOrder_iff, Subrepresentation, Subrepresentation.submoduleSubrepresentationOrderIso, isSimpleModule_iff, isSimpleOrder_iff, submoduleSubrepresentationOrderIso
-/
theorem isSimpleModule_iff_irreducible_ofModule (M : Type*) [AddCommGroup M] [Module k[G] M] :
    IsSimpleModule k[G] M ↔ IsIrreducible (ofModule (k := k) (G := G) M) := by
  rw [isSimpleModule_iff]
  exact OrderIso.isSimpleOrder_iff Subrepresentation.submoduleSubrepresentationOrderIso

@[deprecated (since := "2026-02-09")]
alias is_simple_module_iff_irreducible_ofModule := isSimpleModule_iff_irreducible_ofModule

namespace IsIrreducible

variable {ρ σ} (f : IntertwiningMap ρ σ) [IsIrreducible ρ]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSimpleModule k[G] ρ.asModule
  body: (irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance

中文:
实例 :
  签名: IsSimpleModule k[G] ρ.asModule
  定义体: (irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance

Depends on / 依赖: irreducible_iff_isSimpleModule_asModule
-/
instance : IsSimpleModule k[G] ρ.asModule :=
  (irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance

open Function IntertwiningMap

/--
theorem `injective_or_eq_zero` / 定理 `injective_or_eq_zero`

English:
theorem injective_or_eq_zero
  statement: Injective f ∨ f = 0
  proof: by
  rw [← LinearEquiv.map_eq_zero_iff (equivLinearMapAsModule ρ σ)]
  exact LinearMap.injective_or_eq_zero (equivLinearMapAsModule ρ σ f)

中文:
定理 injective_or_eq_zero
  结论: Injective f ∨ f = 0
  证明: by
  rw [← LinearEquiv.map_eq_zero_iff (equivLinearMapAsModule ρ σ)]
  exact LinearMap.injective_or_eq_zero (equivLinearMapAsModule ρ σ f)

Depends on / 依赖: LinearEquiv, LinearEquiv.map_eq_zero_iff, LinearMap, LinearMap.injective_or_eq_zero, equivLinearMapAsModule, injective_or_eq_zero, map_eq_zero_iff
-/
theorem injective_or_eq_zero : Injective f ∨ f = 0 := by
  rw [← LinearEquiv.map_eq_zero_iff (equivLinearMapAsModule ρ σ)]
  exact LinearMap.injective_or_eq_zero (equivLinearMapAsModule ρ σ f)

/--
theorem `surjective_or_eq_zero` / 定理 `surjective_or_eq_zero`

English:
theorem surjective_or_eq_zero
  given: (g : IntertwiningMap σ ρ)
  statement: Surjective g ∨ g = 0
  proof: by
  rw [← LinearEquiv.map_eq_zero_iff (equivLinearMapAsModule σ ρ)]
  exact LinearMap.surjective_or_eq_zero (equivLinearMapAsModule σ ρ g)

中文:
定理 surjective_or_eq_zero
  条件: (g : 整数ertwiningMap σ ρ)
  结论: Surjective g ∨ g = 0
  证明: by
  rw [← LinearEquiv.map_eq_zero_iff (equivLinearMapAsModule σ ρ)]
  exact LinearMap.surjective_or_eq_zero (equivLinearMapAsModule σ ρ g)

Depends on / 依赖: LinearEquiv, LinearEquiv.map_eq_zero_iff, LinearMap, LinearMap.surjective_or_eq_zero, equivLinearMapAsModule, map_eq_zero_iff, surjective_or_eq_zero
-/
theorem surjective_or_eq_zero (g : IntertwiningMap σ ρ) : Surjective g ∨ g = 0 := by
  rw [← LinearEquiv.map_eq_zero_iff (equivLinearMapAsModule σ ρ)]
  exact LinearMap.surjective_or_eq_zero (equivLinearMapAsModule σ ρ g)

/--
theorem `bijective_or_eq_zero` / 定理 `bijective_or_eq_zero`

English:
theorem bijective_or_eq_zero
  given: [IsIrreducible σ]
  statement: Bijective f ∨ f = 0
  proof: by
  rw [← LinearEquiv.map_eq_zero_iff (equivLinearMapAsModule ρ σ)]
  exact LinearMap.bijective_or_eq_zero (equivLinearMapAsModule ρ σ f)

中文:
定理 bijective_or_eq_zero
  条件: [IsIrreducible σ]
  结论: Bijective f ∨ f = 0
  证明: by
  rw [← LinearEquiv.map_eq_zero_iff (equivLinearMapAsModule ρ σ)]
  exact LinearMap.bijective_or_eq_zero (equivLinearMapAsModule ρ σ f)

Depends on / 依赖: LinearEquiv, LinearEquiv.map_eq_zero_iff, LinearMap, LinearMap.bijective_or_eq_zero, bijective_or_eq_zero, equivLinearMapAsModule, map_eq_zero_iff
-/
theorem bijective_or_eq_zero [IsIrreducible σ] : Bijective f ∨ f = 0 := by
  rw [← LinearEquiv.map_eq_zero_iff (equivLinearMapAsModule ρ σ)]
  exact LinearMap.bijective_or_eq_zero (equivLinearMapAsModule ρ σ f)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsIrreducible
  signature: σ] [IsEmpty (Equiv ρ σ)] : Subsingleton (IntertwiningMap ρ σ)
  body: ⟨fun f g => sub_eq_zero.mp (bijective_or_eq_zero _).resolve_left
fun h => isEmpty_iff.mp inferInstance (f - g).ofBijective h⟩

中文:
实例 [IsIrreducible
  签名: σ] [IsEmpty (Equiv ρ σ)] : Subsingleton (整数ertwiningMap ρ σ)
  定义体: ⟨fun f g => sub_eq_zero.mp (bijective_or_eq_zero _).resolve_left
fun h => isEmpty_iff.mp inferInstance (f - g).ofBijective h⟩

Depends on / 依赖: FiniteDimensional, IsAlgClosed, bijective_or_eq_zero, isEmpty_iff, isEmpty_iff.mp, ofBijective, resolve_left, sub_eq_zero, sub_eq_zero.mp, variable
-/
instance [IsIrreducible σ] [IsEmpty (Equiv ρ σ)] : Subsingleton (IntertwiningMap ρ σ) :=
⟨fun f g => sub_eq_zero.mp (bijective_or_eq_zero _).resolve_left
fun h => isEmpty_iff.mp inferInstance (f - g).ofBijective h⟩
variable [FiniteDimensional k V] [IsAlgClosed k]

variable (f : IntertwiningMap ρ ρ) in
/--
theorem `algebraMap_intertwiningMap_bijective_of_isAlgClosed` / 定理 `algebraMap_intertwiningMap_bijective_of_isAlgClosed`

English:
theorem algebraMap_intertwiningMap_bijective_of_isAlgClosed
  proof: by
  have : Bijective (algebraMap k (Module.End k[G] ρ.asModule)) :=
    IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k
  exact (Bijective.of_comp_iff' (IntertwiningMap.equivAlgEnd (ρ := ρ)).bijective _).1 this

中文:
定理 algebraMap_intertwiningMap_bijective_of_isAlgClosed
  证明: by
  have : Bijective (algebraMap k (Module.End k[G] ρ.asModule)) :=
    IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k
  exact (Bijective.of_comp_iff' (IntertwiningMap.equivAlgEnd (ρ := ρ)).bijective _).1 this

Depends on / 依赖: Bijective, Bijective.of_comp_iff, IntertwiningMap, IntertwiningMap.equivAlgEnd, IsSimpleModule, IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed, Module, Module.End, algebraMap, algebraMap_end_bijective_of_isAlgClosed, asModule, bijective, equivAlgEnd, of_comp_iff
-/
theorem algebraMap_intertwiningMap_bijective_of_isAlgClosed :
    Bijective (algebraMap k (IntertwiningMap ρ ρ)) := by
  have : Bijective (algebraMap k (Module.End k[G] ρ.asModule)) :=
    IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k
  exact (Bijective.of_comp_iff' (IntertwiningMap.equivAlgEnd (ρ := ρ)).bijective _).1 this

variable (ρ) in
/--
theorem `finrank_intertwiningMap_self` / 定理 `finrank_intertwiningMap_self`

English:
theorem finrank_intertwiningMap_self
  statement: Module.finrank k (IntertwiningMap ρ ρ) = 1
  proof: by
  rw [LinearEquiv.finrank_eq (LinearEquiv.ofBijective (Algebra.linearMap k (IntertwiningMap ρ ρ))
      algebraMap_intertwiningMap_bijective_of_isAlgClosed).symm]
  exact CommSemiring.finrank_self k

中文:
定理 finrank_intertwiningMap_self
  结论: Module.finrank k (整数ertwiningMap ρ ρ) = 1
  证明: by
  rw [LinearEquiv.finrank_eq (LinearEquiv.ofBijective (Algebra.linearMap k (IntertwiningMap ρ ρ))
      algebraMap_intertwiningMap_bijective_of_isAlgClosed).symm]
  exact CommSemiring.finrank_self k
-/
@[simp] theorem finrank_intertwiningMap_self : Module.finrank k (IntertwiningMap ρ ρ) = 1 := by
  rw [LinearEquiv.finrank_eq (LinearEquiv.ofBijective (Algebra.linearMap k (IntertwiningMap ρ ρ))
      algebraMap_intertwiningMap_bijective_of_isAlgClosed).symm]
  exact CommSemiring.finrank_self k

open scoped IsMulCommutative in
include ρ in
variable (ρ) in
/--
theorem `finrank_eq_one_of_isMulCommutative` / 定理 `finrank_eq_one_of_isMulCommutative`

English:
theorem finrank_eq_one_of_isMulCommutative
  given: [IsMulCommutative G]
  statement: Module.finrank k V = 1
  proof: by
  exact IsSimpleModule.finrank_eq_one_of_isMulCommutative k[G] ρ.asModule k

中文:
定理 finrank_eq_one_of_isMulCommutative
  条件: [IsMulCommutative G]
  结论: Module.finrank k V = 1
  证明: by
  exact IsSimpleModule.finrank_eq_one_of_isMulCommutative k[G] ρ.asModule k

Depends on / 依赖: IsSimpleModule, IsSimpleModule.finrank_eq_one_of_isMulCommutative, asModule, finrank_eq_one_of_isMulCommutative
-/
theorem finrank_eq_one_of_isMulCommutative [IsMulCommutative G] : Module.finrank k V = 1 := by
  exact IsSimpleModule.finrank_eq_one_of_isMulCommutative k[G] ρ.asModule k

end IsIrreducible

end Representation
