/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mon

/-!
# Monoid objects internal to monoidal opposites

In this file, we record the equivalence between `Mon C` and `Mon Cᴹᵒᵖ`.
-/

@[expose] public section

namespace MonObj

open CategoryTheory MonoidalCategory MonoidalOpposite

variable {C : Type*} [Category* C] [MonoidalCategory C]

section mop

variable (M : C) [MonObj M]

set_option backward.defeqAttrib.useBackward true in
/-- If `M : C` is a monoid object, then `mop M : Cᴹᵒᵖ` too. -/
@[simps!]
/--
Instance `mopMonObj` / 实例 `mopMonObj`

English:
instance mopMonObj
  signature: : MonObj (mop M) where
  body: MonObj.mul.mop
  one := MonObj.one.mop
  mul_one := by
.fullyFaithfulInverse.map_injective apply mopEquiv C
    simp
  one_mul := by
.fullyFaithfulInverse.map_injective apply mopEquiv C
    simp
  mul_assoc := by
.fullyFaithfulInverse.map_injective apply mopEquiv C
    simp

中文:
实例 mopMonObj
  签名: : MonObj (mop M) where
  定义体: MonObj.mul.mop
  one := MonObj.one.mop
  mul_one := by
.fullyFaithfulInverse.map_injective apply mopEquiv C
    simp
  one_mul := by
.fullyFaithfulInverse.map_injective apply mopEquiv C
    simp
  mul_assoc := by
.fullyFaithfulInverse.map_injective apply mopEquiv C
    simp

Depends on / 依赖: MonObj, MonObj.mul.mop, range_le_equalizer_iff
-/
instance mopMonObj : MonObj (mop M) where
  mul := MonObj.mul.mop
  one := MonObj.one.mop
  mul_one := by
.fullyFaithfulInverse.map_injective apply mopEquiv C
    simp
  one_mul := by
.fullyFaithfulInverse.map_injective apply mopEquiv C
    simp
  mul_assoc := by
.fullyFaithfulInverse.map_injective apply mopEquiv C
    simp

variable {M} in
/--
Instance `mop_isMonHom` / 实例 `mop_isMonHom`

English:
instance mop_isMonHom
  signature: {N : C} [MonObj N]
  body: by
.fullyFaithfulInverse.map_injective apply mopEquiv C
    simpa [-IsMonHom.mul_hom] using! IsMonHom.mul_hom f
  one_hom := by
.fullyFaithfulInverse.map_injective apply mopEquiv C
    simpa [-IsMonHom.one_hom] using! IsMonHom.one_hom f

中文:
实例 mop_isMonHom
  签名: {N : C} [MonObj N]
  定义体: by
.fullyFaithfulInverse.map_injective apply mopEquiv C
    simpa [-IsMonHom.mul_hom] using! IsMonHom.mul_hom f
  one_hom := by
.fullyFaithfulInverse.map_injective apply mopEquiv C
    simpa [-IsMonHom.one_hom] using! IsMonHom.one_hom f

Depends on / 依赖: IsMonHom, IsMonHom.mul_hom, IsMonHom.one_hom, Subfunctor, Subfunctor.lift, fullyFaithfulInverse, fullyFaithfulInverse.map_injective, map_injective, mopEquiv, mul_hom, one_hom, range_le_equalizer_iff
-/
instance mop_isMonHom {N : C} [MonObj N]
    (f : M ⟶ N) [IsMonHom f] : IsMonHom f.mop where
  mul_hom := by
.fullyFaithfulInverse.map_injective apply mopEquiv C
    simpa [-IsMonHom.mul_hom] using! IsMonHom.mul_hom f
  one_hom := by
.fullyFaithfulInverse.map_injective apply mopEquiv C
    simpa [-IsMonHom.one_hom] using! IsMonHom.one_hom f

end mop

section unmop

variable (M : Cᴹᵒᵖ) [MonObj M]

set_option backward.defeqAttrib.useBackward true in
/-- If `M : Cᴹᵒᵖ` is a monoid object, then `unmop M : C` too. -/
@[simps -isSimp] -- not making them simp because it causes a loop.
/--
Instance `unmopMonObj` / 实例 `unmopMonObj`

English:
instance unmopMonObj
  signature: : MonObj (unmop M) where
  body: MonObj.mul.unmop
  one := MonObj.one.unmop
  mul_one := by
.fullyFaithfulFunctor.map_injective apply mopEquiv C
    simp
  one_mul := by
.fullyFaithfulFunctor.map_injective apply mopEquiv C
    simp
  mul_assoc := by
.fullyFaithfulFunctor.map_injective apply mopEquiv C
    simp

中文:
实例 unmopMonObj
  签名: : MonObj (unmop M) where
  定义体: MonObj.mul.unmop
  one := MonObj.one.unmop
  mul_one := by
.fullyFaithfulFunctor.map_injective apply mopEquiv C
    simp
  one_mul := by
.fullyFaithfulFunctor.map_injective apply mopEquiv C
    simp
  mul_assoc := by
.fullyFaithfulFunctor.map_injective apply mopEquiv C
    simp

Depends on / 依赖: MonObj, MonObj.mul.unmop
-/
instance unmopMonObj : MonObj (unmop M) where
  mul := MonObj.mul.unmop
  one := MonObj.one.unmop
  mul_one := by
.fullyFaithfulFunctor.map_injective apply mopEquiv C
    simp
  one_mul := by
.fullyFaithfulFunctor.map_injective apply mopEquiv C
    simp
  mul_assoc := by
.fullyFaithfulFunctor.map_injective apply mopEquiv C
    simp

variable {M} in
/--
Instance `unmop_isMonHom` / 实例 `unmop_isMonHom`

English:
instance unmop_isMonHom
  signature: {N : Cᴹᵒᵖ} [MonObj N]
  body: by
.fullyFaithfulFunctor.map_injective apply mopEquiv C
    simpa [-IsMonHom.mul_hom] using! IsMonHom.mul_hom f
  one_hom := by
.fullyFaithfulFunctor.map_injective apply mopEquiv C
    simpa [-IsMonHom.one_hom] using! IsMonHom.one_hom f

中文:
实例 unmop_isMonHom
  签名: {N : Cᴹᵒᵖ} [MonObj N]
  定义体: by
.fullyFaithfulFunctor.map_injective apply mopEquiv C
    simpa [-IsMonHom.mul_hom] using! IsMonHom.mul_hom f
  one_hom := by
.fullyFaithfulFunctor.map_injective apply mopEquiv C
    simpa [-IsMonHom.one_hom] using! IsMonHom.one_hom f

Depends on / 依赖: IsMonHom, IsMonHom.mul_hom, IsMonHom.one_hom, fullyFaithfulFunctor, fullyFaithfulFunctor.map_injective, map_injective, mopEquiv, mul_hom, one_hom
-/
instance unmop_isMonHom {N : Cᴹᵒᵖ} [MonObj N]
    (f : M ⟶ N) [IsMonHom f] : IsMonHom f.unmop where
  mul_hom := by
.fullyFaithfulFunctor.map_injective apply mopEquiv C
    simpa [-IsMonHom.mul_hom] using! IsMonHom.mul_hom f
  one_hom := by
.fullyFaithfulFunctor.map_injective apply mopEquiv C
    simpa [-IsMonHom.one_hom] using! IsMonHom.one_hom f

end unmop

set_option backward.isDefEq.respectTransparency.types false in
variable (C) in
/-- The equivalence of categories between monoids internal to `C`
and monoids internal to the monoidal opposite of `C`. -/
@[simps!]
/--
Definition of `mopEquiv` / `mopEquiv` 的定义

English:
definition mopEquiv
  signature: : Mon C ≌ Mon Cᴹᵒᵖ where
  body: { obj M := ⟨mop M.X⟩
      map f := ⟨f.hom.mop⟩ }
  inverse :=
    { obj M := ⟨unmop M.X⟩
      map f := ⟨f.hom.unmop⟩ }
  unitIso := .refl _
  counitIso := .refl _

中文:
定义 mopEquiv
  签名: : Mon C ≌ Mon Cᴹᵒᵖ where
  定义体: { obj M := ⟨mop M.X⟩
      map f := ⟨f.hom.mop⟩ }
  inverse :=
    { obj M := ⟨unmop M.X⟩
      map f := ⟨f.hom.unmop⟩ }
  unitIso := .refl _
  counitIso := .refl _

Depends on / 依赖: Limits, Limits.Fork.of, condition, counitIso, equalizer, equalizer.condition, f.hom.mop, f.hom.unmop, inverse, unitIso
-/
def mopEquiv : Mon C ≌ Mon Cᴹᵒᵖ where
  functor :=
    { obj M := ⟨mop M.X⟩
      map f := ⟨f.hom.mop⟩ }
  inverse :=
    { obj M := ⟨unmop M.X⟩
      map f := ⟨f.hom.unmop⟩ }
  unitIso := .refl _
  counitIso := .refl _

set_option backward.isDefEq.respectTransparency.types false in
/-- The equivalence of categories between monoids internal to `C`
and monoids internal to the monoidal opposite of `C` lies over
the equivalence `C ≌ Cᴹᵒᵖ` via the forgetful functors. -/
@[simps!]
/--
Definition of `mopEquivCompForgetIso` / `mopEquivCompForgetIso` 的定义

English:
definition mopEquivCompForgetIso
  signature: :
  body: .refl _

中文:
定义 mopEquivCompForgetIso
  签名: :
  定义体: .refl _
-/
def mopEquivCompForgetIso :
    (mopEquiv C).functor ⋙ Mon.forget Cᴹᵒᵖ ≅
    Mon.forget C ⋙ (MonoidalOpposite.mopEquiv C).functor :=
  .refl _

end MonObj
