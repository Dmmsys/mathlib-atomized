/-
Copyright (c) 2025 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
module

public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Pulling back a preadditive structure along a fully faithful functor

A preadditive structure on a category `D` transfers to a preadditive structure on `C` for a given
fully faithful functor `F : C ⥤ D`.
-/

@[expose] public section
namespace CategoryTheory

open Limits

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
variable {F : C ⥤ D} (hF : F.FullyFaithful)

namespace Preadditive


/-- If `D` is a preadditive category, any fully faithful functor `F : C ⥤ D` induces a preadditive
structure on `C`. -/
@[instance_reducible]
/--
Definition of `ofFullyFaithful` / `ofFullyFaithful` 的定义

English:
definition ofFullyFaithful
  signature: : Preadditive C where
  body: hF.homEquiv.addCommGroup
  add_comp P Q R f f' g := hF.map_injective (by simp [Equiv.add_def])
  comp_add P Q R f g g' := hF.map_injective (by simp [Equiv.add_def])

中文:
定义 ofFullyFaithful
  签名: : Preadditive C where
  定义体: hF.homEquiv.addCommGroup
  add_comp P Q R f f' g := hF.map_injective (by simp [Equiv.add_def])
  comp_add P Q R f g g' := hF.map_injective (by simp [Equiv.add_def])

Depends on / 依赖: addCommGroup, hF.homEquiv.addCommGroup, homEquiv
-/
def ofFullyFaithful : Preadditive C where
  homGroup P Q := hF.homEquiv.addCommGroup
  add_comp P Q R f f' g := hF.map_injective (by simp [Equiv.add_def])
  comp_add P Q R f g g' := hF.map_injective (by simp [Equiv.add_def])

end Preadditive

open Preadditive
namespace Functor.FullyFaithful

/--
lemma `additive_ofFullyFaithful` / 引理 `additive_ofFullyFaithful`

English:
lemma additive_ofFullyFaithful
  proof: Preadditive.ofFullyFaithful hF
    F.Additive :=
  letI : Preadditive C := Preadditive.ofFullyFaithful hF
  { map_add := by simp [Equiv.add_def] }

中文:
引理 additive_ofFullyFaithful
  证明: Preadditive.ofFullyFaithful hF
    F.Additive :=
  letI : Preadditive C := Preadditive.ofFullyFaithful hF
  { map_add := by simp [Equiv.add_def] }

Depends on / 依赖: Preadditive, Preadditive.ofFullyFaithful, ofFullyFaithful
-/
lemma additive_ofFullyFaithful :
    letI : Preadditive C := Preadditive.ofFullyFaithful hF
    F.Additive :=
  letI : Preadditive C := Preadditive.ofFullyFaithful hF
  { map_add := by simp [Equiv.add_def] }

end Functor.FullyFaithful

namespace Equivalence

/--
lemma `additive_inverse_of_FullyFaithful` / 引理 `additive_inverse_of_FullyFaithful`

English:
lemma additive_inverse_of_FullyFaithful
  given: (e : C ≌ D)
  proof: ofFullyFaithful e.fullyFaithfulFunctor
    e.inverse.Additive :=
  letI : Preadditive C := ofFullyFaithful e.fullyFaithfulFunctor
  letI : e.functor.Additive := e.fullyFaithfulFunctor.additive_ofFullyFaithful
  e.inverse_additive

中文:
引理 additive_inverse_of_FullyFaithful
  条件: (e : C ≌ D)
  证明: ofFullyFaithful e.fullyFaithfulFunctor
    e.inverse.Additive :=
  letI : Preadditive C := ofFullyFaithful e.fullyFaithfulFunctor
  letI : e.functor.Additive := e.fullyFaithfulFunctor.additive_ofFullyFaithful
  e.inverse_additive

Depends on / 依赖: e.fullyFaithfulFunctor, fullyFaithfulFunctor, ofFullyFaithful
-/
lemma additive_inverse_of_FullyFaithful (e : C ≌ D) :
    letI : Preadditive C := ofFullyFaithful e.fullyFaithfulFunctor
    e.inverse.Additive :=
  letI : Preadditive C := ofFullyFaithful e.fullyFaithfulFunctor
  letI : e.functor.Additive := e.fullyFaithfulFunctor.additive_ofFullyFaithful
  e.inverse_additive

end Equivalence

end CategoryTheory
