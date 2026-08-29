/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Ring.PUnit
public import Mathlib.CategoryTheory.Monoidal.Types.Basic

/-!
# Chosen finite products in `GrpCat` and friends
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory ConcreteCategory

universe u

namespace GrpCat

/-- Construct limit data for a binary product in `GrpCat`, using `GrpCat.of (G × H)` -/
@[simps! cone_pt isLimit_lift]
/--
Definition of `binaryProductLimitCone` / `binaryProductLimitCone` 的定义

English:
definition binaryProductLimitCone
  signature: (G H : GrpCat.{u})
  body: BinaryFan.mk (ofHom (MonoidHom.fst G H)) (ofHom (MonoidHom.snd G H))
  isLimit := BinaryFan.IsLimit.mk _ (fun l r => ofHom (MonoidHom.prod l.hom r.hom))
    (fun _ _ => rfl) (fun _ _ => rfl) (by cat_disch)

中文:
定义 binaryProductLimitCone
  签名: (G H : 群范畴.{u})
  定义体: BinaryFan.mk (ofHom (MonoidHom.fst G H)) (ofHom (MonoidHom.snd G H))
  isLimit := BinaryFan.IsLimit.mk _ (fun l r => ofHom (MonoidHom.prod l.hom r.hom))
    (fun _ _ => rfl) (fun _ _ => rfl) (by cat_disch)

Depends on / 依赖: BinaryFan, BinaryFan.mk, MonoidHom, MonoidHom.fst, MonoidHom.snd
-/
def binaryProductLimitCone (G H : GrpCat.{u}) : LimitCone (pair G H) where
  cone := BinaryFan.mk (ofHom (MonoidHom.fst G H)) (ofHom (MonoidHom.snd G H))
  isLimit := BinaryFan.IsLimit.mk _ (fun l r => ofHom (MonoidHom.prod l.hom r.hom))
    (fun _ _ => rfl) (fun _ _ => rfl) (by cat_disch)

/--
Instance `cartesianMonoidalCategoryGrp` / 实例 `cartesianMonoidalCategoryGrp`

English:
instance cartesianMonoidalCategoryGrp
  signature: : CartesianMonoidalCategory GrpCat.{u}
  body: .ofChosenFiniteProducts ⟨_, (isZero_of_subsingleton (GrpCat.of PUnit.{u + 1})).isTerminal⟩
    fun G H => binaryProductLimitCone G H

中文:
实例 cartesianMonoidalCategoryGrp
  签名: : CartesianMonoidal范畴 群范畴.{u}
  定义体: .ofChosenFiniteProducts ⟨_, (isZero_of_subsingleton (GrpCat.of PUnit.{u + 1})).isTerminal⟩
    fun G H => binaryProductLimitCone G H

Depends on / 依赖: GrpCat, GrpCat.of, binaryProductLimitCone, isTerminal, isZero_of_subsingleton, ofChosenFiniteProducts
-/
noncomputable instance cartesianMonoidalCategoryGrp : CartesianMonoidalCategory GrpCat.{u} :=
  .ofChosenFiniteProducts ⟨_, (isZero_of_subsingleton (GrpCat.of PUnit.{u + 1})).isTerminal⟩
    fun G H => binaryProductLimitCone G H

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BraidedCategory GrpCat.{u}
  body: .ofCartesianMonoidalCategory

中文:
实例 :
  签名: 辫范畴 群范畴.{u}
  定义体: .ofCartesianMonoidalCategory

Depends on / 依赖: ofCartesianMonoidalCategory
-/
noncomputable instance : BraidedCategory GrpCat.{u} := .ofCartesianMonoidalCategory

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget GrpCat.{u}).Braided
  body: .ofChosenFiniteProducts _

中文:
实例 :
  签名: (forget 群范畴.{u}).辫
  定义体: .ofChosenFiniteProducts _

Depends on / 依赖: ofChosenFiniteProducts
-/
noncomputable instance : (forget GrpCat.{u}).Braided := .ofChosenFiniteProducts _

/--
theorem `tensorObj_eq` / 定理 `tensorObj_eq`

English:
theorem tensorObj_eq
  given: (G H : GrpCat.{u})
  statement: (G otimes H) = of (G × H)
  proof: rfl

@[simp]

中文:
定理 tensorObj_eq
  条件: (G H : 群范畴.{u})
  结论: (G otimes H) = of (G × H)
  证明: rfl

@[simp]
-/
theorem tensorObj_eq (G H : GrpCat.{u}) : (G otimes H) = of (G × H) := rfl

@[simp]
/--
theorem `μ_forget_apply` / 定理 `μ_forget_apply`

English:
theorem μ_forget_apply
  given: {G H : GrpCat.{u}} (p : G) (q : H)
  proof: by
  apply Prod.ext
  · exact congr_hom (CC := fun X => X) (Functor.Monoidal.μ_fst (forget GrpCat.{u}) G H) (p, q)
  · exact congr_hom (CC := fun X => X) (Functor.Monoidal.μ_snd (forget GrpCat.{u}) G H) (p, q)

中文:
定理 μ_forget_apply
  条件: {G H : 群范畴.{u}} (p : G) (q : H)
  证明: by
  apply Prod.ext
  · exact congr_hom (CC := fun X => X) (Functor.Monoidal.μ_fst (forget GrpCat.{u}) G H) (p, q)
  · exact congr_hom (CC := fun X => X) (Functor.Monoidal.μ_snd (forget GrpCat.{u}) G H) (p, q)

Depends on / 依赖: Functor, Functor.Monoidal, GrpCat, Monoidal, Prod.ext, congr_hom, forget
-/
theorem μ_forget_apply {G H : GrpCat.{u}} (p : G) (q : H) :
    Functor.LaxMonoidal.μ (forget GrpCat.{u}) G H (p, q) = (p, q) := by
  apply Prod.ext
  · exact congr_hom (CC := fun X => X) (Functor.Monoidal.μ_fst (forget GrpCat.{u}) G H) (p, q)
  · exact congr_hom (CC := fun X => X) (Functor.Monoidal.μ_snd (forget GrpCat.{u}) G H) (p, q)

end GrpCat

namespace AddGrpCat

/-- Construct limit data for a binary product in `AddGrpCat`, using `AddGrpCat.of (G × H)` -/
@[simps! cone_pt isLimit_lift]
/--
Definition of `binaryProductLimitCone` / `binaryProductLimitCone` 的定义

English:
definition binaryProductLimitCone
  signature: (G H : AddGrpCat.{u})
  body: BinaryFan.mk (ofHom (AddMonoidHom.fst G H)) (ofHom (AddMonoidHom.snd G H))
  isLimit := BinaryFan.IsLimit.mk _ (fun l r => ofHom (AddMonoidHom.prod l.hom r.hom))
    (fun _ _ => rfl) (fun _ _ => rfl) (by cat_disch)

中文:
定义 binaryProductLimitCone
  签名: (G H : 加法群范畴.{u})
  定义体: BinaryFan.mk (ofHom (AddMonoidHom.fst G H)) (ofHom (AddMonoidHom.snd G H))
  isLimit := BinaryFan.IsLimit.mk _ (fun l r => ofHom (AddMonoidHom.prod l.hom r.hom))
    (fun _ _ => rfl) (fun _ _ => rfl) (by cat_disch)

Depends on / 依赖: AddMonoidHom, AddMonoidHom.fst, AddMonoidHom.snd, BinaryFan, BinaryFan.mk
-/
def binaryProductLimitCone (G H : AddGrpCat.{u}) : LimitCone (pair G H) where
  cone := BinaryFan.mk (ofHom (AddMonoidHom.fst G H)) (ofHom (AddMonoidHom.snd G H))
  isLimit := BinaryFan.IsLimit.mk _ (fun l r => ofHom (AddMonoidHom.prod l.hom r.hom))
    (fun _ _ => rfl) (fun _ _ => rfl) (by cat_disch)

/--
Instance `cartesianMonoidalCategoryAddGrp` / 实例 `cartesianMonoidalCategoryAddGrp`

English:
instance cartesianMonoidalCategoryAddGrp
  signature: : CartesianMonoidalCategory AddGrpCat.{u}
  body: .ofChosenFiniteProducts ⟨_, (isZero_of_subsingleton (AddGrpCat.of PUnit.{u + 1})).isTerminal⟩
    fun G H => binaryProductLimitCone G H

中文:
实例 cartesianMonoidalCategoryAddGrp
  签名: : CartesianMonoidal范畴 加法群范畴.{u}
  定义体: .ofChosenFiniteProducts ⟨_, (isZero_of_subsingleton (AddGrpCat.of PUnit.{u + 1})).isTerminal⟩
    fun G H => binaryProductLimitCone G H

Depends on / 依赖: AddGrpCat, AddGrpCat.of, binaryProductLimitCone, isTerminal, isZero_of_subsingleton, ofChosenFiniteProducts
-/
noncomputable instance cartesianMonoidalCategoryAddGrp : CartesianMonoidalCategory AddGrpCat.{u} :=
  .ofChosenFiniteProducts ⟨_, (isZero_of_subsingleton (AddGrpCat.of PUnit.{u + 1})).isTerminal⟩
    fun G H => binaryProductLimitCone G H

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BraidedCategory AddGrpCat.{u}
  body: .ofCartesianMonoidalCategory

中文:
实例 :
  签名: 辫范畴 加法群范畴.{u}
  定义体: .ofCartesianMonoidalCategory

Depends on / 依赖: ofCartesianMonoidalCategory
-/
noncomputable instance : BraidedCategory AddGrpCat.{u} := .ofCartesianMonoidalCategory

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget AddGrpCat.{u}).Braided
  body: .ofChosenFiniteProducts _

中文:
实例 :
  签名: (forget 加法群范畴.{u}).辫
  定义体: .ofChosenFiniteProducts _

Depends on / 依赖: ofChosenFiniteProducts
-/
noncomputable instance : (forget AddGrpCat.{u}).Braided := .ofChosenFiniteProducts _

/--
theorem `tensorObj_eq` / 定理 `tensorObj_eq`

English:
theorem tensorObj_eq
  given: (G H : AddGrpCat.{u})
  statement: (G otimes H) = of (G × H)
  proof: rfl

@[simp]

中文:
定理 tensorObj_eq
  条件: (G H : 加法群范畴.{u})
  结论: (G otimes H) = of (G × H)
  证明: rfl

@[simp]
-/
theorem tensorObj_eq (G H : AddGrpCat.{u}) : (G otimes H) = of (G × H) := rfl

@[simp]
/--
theorem `μ_forget_apply` / 定理 `μ_forget_apply`

English:
theorem μ_forget_apply
  given: {G H : AddGrpCat.{u}} (p : G) (q : H)
  proof: by
  apply Prod.ext
  · exact congr_hom (CC := fun X => X) (Functor.Monoidal.μ_fst (forget AddGrpCat.{u}) G H) (p, q)
  · exact congr_hom (CC := fun X => X) (Functor.Monoidal.μ_snd (forget AddGrpCat.{u}) G H) (p, q)

中文:
定理 μ_forget_apply
  条件: {G H : 加法群范畴.{u}} (p : G) (q : H)
  证明: by
  apply Prod.ext
  · exact congr_hom (CC := fun X => X) (Functor.Monoidal.μ_fst (forget AddGrpCat.{u}) G H) (p, q)
  · exact congr_hom (CC := fun X => X) (Functor.Monoidal.μ_snd (forget AddGrpCat.{u}) G H) (p, q)

Depends on / 依赖: AddGrpCat, Functor, Functor.Monoidal, Monoidal, Prod.ext, congr_hom, forget
-/
theorem μ_forget_apply {G H : AddGrpCat.{u}} (p : G) (q : H) :
    Functor.LaxMonoidal.μ (forget AddGrpCat.{u}) G H (p, q) = (p, q) := by
  apply Prod.ext
  · exact congr_hom (CC := fun X => X) (Functor.Monoidal.μ_fst (forget AddGrpCat.{u}) G H) (p, q)
  · exact congr_hom (CC := fun X => X) (Functor.Monoidal.μ_snd (forget AddGrpCat.{u}) G H) (p, q)

end AddGrpCat

namespace CommGrpCat

/-- Construct limit data for a binary product in `CommGrpCat`, using `CommGrpCat.of (G × H)` -/
@[simps! cone_pt isLimit_lift]
/--
Definition of `binaryProductLimitCone` / `binaryProductLimitCone` 的定义

English:
definition binaryProductLimitCone
  signature: (G H : CommGrpCat.{u})
  body: BinaryFan.mk (ofHom (MonoidHom.fst G H)) (ofHom (MonoidHom.snd G H))
  isLimit := BinaryFan.IsLimit.mk _ (fun l r => ofHom (MonoidHom.prod l.hom r.hom))
    (fun _ _ => rfl) (fun _ _ => rfl) (by cat_disch)

中文:
定义 binaryProductLimitCone
  签名: (G H : 交换群范畴.{u})
  定义体: BinaryFan.mk (ofHom (MonoidHom.fst G H)) (ofHom (MonoidHom.snd G H))
  isLimit := BinaryFan.IsLimit.mk _ (fun l r => ofHom (MonoidHom.prod l.hom r.hom))
    (fun _ _ => rfl) (fun _ _ => rfl) (by cat_disch)

Depends on / 依赖: BinaryFan, BinaryFan.mk, MonoidHom, MonoidHom.fst, MonoidHom.snd
-/
def binaryProductLimitCone (G H : CommGrpCat.{u}) : LimitCone (pair G H) where
  cone := BinaryFan.mk (ofHom (MonoidHom.fst G H)) (ofHom (MonoidHom.snd G H))
  isLimit := BinaryFan.IsLimit.mk _ (fun l r => ofHom (MonoidHom.prod l.hom r.hom))
    (fun _ _ => rfl) (fun _ _ => rfl) (by cat_disch)

/--
Instance `cartesianMonoidalCategory` / 实例 `cartesianMonoidalCategory`

English:
instance cartesianMonoidalCategory
  signature: : CartesianMonoidalCategory CommGrpCat.{u}
  body: .ofChosenFiniteProducts ⟨_, (isZero_of_subsingleton (CommGrpCat.of PUnit.{u + 1})).isTerminal⟩
    fun G H => binaryProductLimitCone G H

中文:
实例 cartesianMonoidalCategory
  签名: : CartesianMonoidal范畴 交换群范畴.{u}
  定义体: .ofChosenFiniteProducts ⟨_, (isZero_of_subsingleton (CommGrpCat.of PUnit.{u + 1})).isTerminal⟩
    fun G H => binaryProductLimitCone G H

Depends on / 依赖: CommGrpCat, CommGrpCat.of, binaryProductLimitCone, isTerminal, isZero_of_subsingleton, ofChosenFiniteProducts
-/
noncomputable instance cartesianMonoidalCategory : CartesianMonoidalCategory CommGrpCat.{u} :=
  .ofChosenFiniteProducts ⟨_, (isZero_of_subsingleton (CommGrpCat.of PUnit.{u + 1})).isTerminal⟩
    fun G H => binaryProductLimitCone G H

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BraidedCategory CommGrpCat.{u}
  body: .ofCartesianMonoidalCategory

中文:
实例 :
  签名: 辫范畴 交换群范畴.{u}
  定义体: .ofCartesianMonoidalCategory

Depends on / 依赖: ofCartesianMonoidalCategory
-/
noncomputable instance : BraidedCategory CommGrpCat.{u} := .ofCartesianMonoidalCategory

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget CommGrpCat.{u}).Braided
  body: .ofChosenFiniteProducts _

中文:
实例 :
  签名: (forget 交换群范畴.{u}).辫
  定义体: .ofChosenFiniteProducts _

Depends on / 依赖: ofChosenFiniteProducts
-/
noncomputable instance : (forget CommGrpCat.{u}).Braided := .ofChosenFiniteProducts _

/--
theorem `tensorObj_eq` / 定理 `tensorObj_eq`

English:
theorem tensorObj_eq
  given: (G H : CommGrpCat.{u})
  statement: (G otimes H) = of (G × H)
  proof: rfl

@[simp]

中文:
定理 tensorObj_eq
  条件: (G H : 交换群范畴.{u})
  结论: (G otimes H) = of (G × H)
  证明: rfl

@[simp]
-/
theorem tensorObj_eq (G H : CommGrpCat.{u}) : (G otimes H) = of (G × H) := rfl

@[simp]
/--
theorem `μ_forget_apply` / 定理 `μ_forget_apply`

English:
theorem μ_forget_apply
  given: {G H : CommGrpCat.{u}} (p : G) (q : H)
  proof: by
  apply Prod.ext
  · exact congr_hom (CC := fun X => X) (Functor.Monoidal.μ_fst (forget CommGrpCat.{u}) G H) (p, q)
  · exact congr_hom (CC := fun X => X) (Functor.Monoidal.μ_snd (forget CommGrpCat.{u}) G H) (p, q)

中文:
定理 μ_forget_apply
  条件: {G H : 交换群范畴.{u}} (p : G) (q : H)
  证明: by
  apply Prod.ext
  · exact congr_hom (CC := fun X => X) (Functor.Monoidal.μ_fst (forget CommGrpCat.{u}) G H) (p, q)
  · exact congr_hom (CC := fun X => X) (Functor.Monoidal.μ_snd (forget CommGrpCat.{u}) G H) (p, q)

Depends on / 依赖: CommGrpCat, Functor, Functor.Monoidal, Monoidal, Prod.ext, congr_hom, forget
-/
theorem μ_forget_apply {G H : CommGrpCat.{u}} (p : G) (q : H) :
    Functor.LaxMonoidal.μ (forget CommGrpCat.{u}) G H (p, q) = (p, q) := by
  apply Prod.ext
  · exact congr_hom (CC := fun X => X) (Functor.Monoidal.μ_fst (forget CommGrpCat.{u}) G H) (p, q)
  · exact congr_hom (CC := fun X => X) (Functor.Monoidal.μ_snd (forget CommGrpCat.{u}) G H) (p, q)

end CommGrpCat

namespace AddCommGrpCat

/-- We choose `AddCommGrpCat.of (G × H)` as the product of `G` and `H` and
`AddCommGrpCat.of PUnit` as the terminal object. -/
@[instance_reducible]
/--
Definition of `cartesianMonoidalCategory` / `cartesianMonoidalCategory` 的定义

English:
definition cartesianMonoidalCategory
  signature: : CartesianMonoidalCategory AddCommGrpCat.{u}
  body: .ofChosenFiniteProducts ⟨_, (isZero_of_subsingleton (AddCommGrpCat.of PUnit.{u + 1})).isTerminal⟩
    fun G H => binaryProductLimitCone G H

中文:
定义 cartesianMonoidalCategory
  签名: : CartesianMonoidal范畴 加法交换群范畴.{u}
  定义体: .ofChosenFiniteProducts ⟨_, (isZero_of_subsingleton (AddCommGrpCat.of PUnit.{u + 1})).isTerminal⟩
    fun G H => binaryProductLimitCone G H

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.of, binaryProductLimitCone, isTerminal, isZero_of_subsingleton, ofChosenFiniteProducts
-/
noncomputable def cartesianMonoidalCategory : CartesianMonoidalCategory AddCommGrpCat.{u} :=
  .ofChosenFiniteProducts ⟨_, (isZero_of_subsingleton (AddCommGrpCat.of PUnit.{u + 1})).isTerminal⟩
    fun G H => binaryProductLimitCone G H

attribute [local instance] cartesianMonoidalCategory

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BraidedCategory AddCommGrpCat.{u}
  body: .ofCartesianMonoidalCategory

中文:
实例 :
  签名: 辫范畴 加法交换群范畴.{u}
  定义体: .ofCartesianMonoidalCategory

Depends on / 依赖: ofCartesianMonoidalCategory
-/
noncomputable instance : BraidedCategory AddCommGrpCat.{u} := .ofCartesianMonoidalCategory

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget AddCommGrpCat.{u}).Braided
  body: .ofChosenFiniteProducts _

中文:
实例 :
  签名: (forget 加法交换群范畴.{u}).辫
  定义体: .ofChosenFiniteProducts _

Depends on / 依赖: ofChosenFiniteProducts
-/
noncomputable instance : (forget AddCommGrpCat.{u}).Braided := .ofChosenFiniteProducts _

/--
theorem `tensorObj_eq` / 定理 `tensorObj_eq`

English:
theorem tensorObj_eq
  given: (G H : AddCommGrpCat.{u})
  statement: (G otimes H) = of (G × H)
  proof: rfl

@[simp]

中文:
定理 tensorObj_eq
  条件: (G H : 加法交换群范畴.{u})
  结论: (G otimes H) = of (G × H)
  证明: rfl

@[simp]
-/
theorem tensorObj_eq (G H : AddCommGrpCat.{u}) : (G otimes H) = of (G × H) := rfl

@[simp]
/--
theorem `μ_forget_apply` / 定理 `μ_forget_apply`

English:
theorem μ_forget_apply
  given: {G H : AddCommGrpCat.{u}} (p : G) (q : H)
  proof: by
  apply Prod.ext
  · exact congr_hom (CC := fun X => X) (Functor.Monoidal.μ_fst (forget AddCommGrpCat.{u}) G H) (p, q)
  · exact congr_hom (CC := fun X => X) (Functor.Monoidal.μ_snd (forget AddCommGrpCat.{u}) G H) (p, q)

中文:
定理 μ_forget_apply
  条件: {G H : 加法交换群范畴.{u}} (p : G) (q : H)
  证明: by
  apply Prod.ext
  · exact congr_hom (CC := fun X => X) (Functor.Monoidal.μ_fst (forget AddCommGrpCat.{u}) G H) (p, q)
  · exact congr_hom (CC := fun X => X) (Functor.Monoidal.μ_snd (forget AddCommGrpCat.{u}) G H) (p, q)

Depends on / 依赖: AddCommGrpCat, Functor, Functor.Monoidal, Monoidal, Prod.ext, congr_hom, forget
-/
theorem μ_forget_apply {G H : AddCommGrpCat.{u}} (p : G) (q : H) :
    Functor.LaxMonoidal.μ (forget AddCommGrpCat.{u}) G H (p, q) = (p, q) := by
  apply Prod.ext
  · exact congr_hom (CC := fun X => X) (Functor.Monoidal.μ_fst (forget AddCommGrpCat.{u}) G H) (p, q)
  · exact congr_hom (CC := fun X => X) (Functor.Monoidal.μ_snd (forget AddCommGrpCat.{u}) G H) (p, q)

end AddCommGrpCat
