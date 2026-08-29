/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Preadditive structure on functor categories

If `C` and `D` are categories and `D` is preadditive,
then `C ⥤ D` is also preadditive.

-/

@[expose] public section

namespace CategoryTheory

open CategoryTheory.Limits Preadditive

variable {C D : Type*} [Category* C] [Category* D] [Preadditive D]

instance {F G : C ⥤ D} : Zero (F ⟶ G) where
  zero := { app := fun _ => 0 }

instance {F G : C ⥤ D} : Add (F ⟶ G) where
  add α β := { app := fun X => α.app X + β.app X }

instance {F G : C ⥤ D} : Neg (F ⟶ G) where
  neg α := { app := fun X => -α.app X }

/--
Instance `functorCategoryPreadditive` / 实例 `functorCategoryPreadditive`

English:
instance functorCategoryPreadditive
  signature: : Preadditive (C ⥤ D) where
  body: { nsmul n α :=
        { app := n • α.app
          naturality X Y f := by
            simp only [Pi.smul_apply, comp_nsmul, NatTrans.naturality, nsmul_comp] }
      zsmul n α :=
        { app := n • α.app
          naturality X Y f := by
            simp only [Pi.smul_apply, comp_zsmul, NatTrans.naturality, zsmul_comp] }
      sub α β := { app := fun X => α.app X - β.app X }
add_assoc _ _ _ := NatTrans.ext add_assoc _ _ _
zero_add _ := NatTrans.ext zero_add _
add_zero _ := NatTrans.ext add_zero _
nsmul_zero _ := NatTrans.ext zero_nsmul _
nsmul_succ _ _ := NatTrans.ext succ_nsmul _ _
sub_eq_add_neg _ _ := NatTrans.ext sub_eq_add_neg _ _
zsmul_zero' _ := NatTrans.ext zero_zsmul _
zsmul_succ' _ _ := NatTrans.ext SubNegMonoid.zsmul_succ' _ _
zsmul_neg' _ _ := NatTrans.ext SubNegMonoid.zsmul_neg' _ _
neg_add_cancel _ := NatTrans.ext neg_add_cancel _
add_comm _ _ := NatTrans.ext add_comm _ _ }
add_comp _ _ _ _ _ _ := NatTrans.ext funext fun _ => add_comp _ _ _ _ _ _
comp_add _ _ _ _ _ _ := NatTrans.ext funext fun _ => comp_add _ _ _ _ _ _

中文:
实例 functorCategoryPreadditive
  签名: : 预加性 (C ⥤ D) where
  定义体: { nsmul n α :=
        { app := n • α.app
          naturality X Y f := by
            simp only [Pi.smul_apply, comp_nsmul, NatTrans.naturality, nsmul_comp] }
      zsmul n α :=
        { app := n • α.app
          naturality X Y f := by
            simp only [Pi.smul_apply, comp_zsmul, NatTrans.naturality, zsmul_comp] }
      sub α β := { app := fun X => α.app X - β.app X }
add_assoc _ _ _ := NatTrans.ext add_assoc _ _ _
zero_add _ := NatTrans.ext zero_add _
add_zero _ := NatTrans.ext add_zero _
nsmul_zero _ := NatTrans.ext zero_nsmul _
nsmul_succ _ _ := NatTrans.ext succ_nsmul _ _
sub_eq_add_neg _ _ := NatTrans.ext sub_eq_add_neg _ _
zsmul_zero' _ := NatTrans.ext zero_zsmul _
zsmul_succ' _ _ := NatTrans.ext SubNegMonoid.zsmul_succ' _ _
zsmul_neg' _ _ := NatTrans.ext SubNegMonoid.zsmul_neg' _ _
neg_add_cancel _ := NatTrans.ext neg_add_cancel _
add_comm _ _ := NatTrans.ext add_comm _ _ }
add_comp _ _ _ _ _ _ := NatTrans.ext funext fun _ => add_comp _ _ _ _ _ _
comp_add _ _ _ _ _ _ := NatTrans.ext funext fun _ => comp_add _ _ _ _ _ _

Depends on / 依赖: NatTrans, NatTrans.ext, NatTrans.naturality, Pi.smul_apply, add_assoc, add_zero, comp_nsmul, comp_zsmul, naturality, nsmul_comp, nsmul_succ, nsmul_zero, smul_apply, zero_add, zero_nsmul, zsmul_comp
-/
instance functorCategoryPreadditive : Preadditive (C ⥤ D) where
  homGroup F G :=
    { nsmul n α :=
        { app := n • α.app
          naturality X Y f := by
            simp only [Pi.smul_apply, comp_nsmul, NatTrans.naturality, nsmul_comp] }
      zsmul n α :=
        { app := n • α.app
          naturality X Y f := by
            simp only [Pi.smul_apply, comp_zsmul, NatTrans.naturality, zsmul_comp] }
      sub α β := { app := fun X => α.app X - β.app X }
add_assoc _ _ _ := NatTrans.ext add_assoc _ _ _
zero_add _ := NatTrans.ext zero_add _
add_zero _ := NatTrans.ext add_zero _
nsmul_zero _ := NatTrans.ext zero_nsmul _
nsmul_succ _ _ := NatTrans.ext succ_nsmul _ _
sub_eq_add_neg _ _ := NatTrans.ext sub_eq_add_neg _ _
zsmul_zero' _ := NatTrans.ext zero_zsmul _
zsmul_succ' _ _ := NatTrans.ext SubNegMonoid.zsmul_succ' _ _
zsmul_neg' _ _ := NatTrans.ext SubNegMonoid.zsmul_neg' _ _
neg_add_cancel _ := NatTrans.ext neg_add_cancel _
add_comm _ _ := NatTrans.ext add_comm _ _ }
add_comp _ _ _ _ _ _ := NatTrans.ext funext fun _ => add_comp _ _ _ _ _ _
comp_add _ _ _ _ _ _ := NatTrans.ext funext fun _ => comp_add _ _ _ _ _ _

namespace NatTrans

variable {F G : C ⥤ D}

/-- Application of a natural transformation at a fixed object,
as group homomorphism -/
@[simps]
/--
Definition of `appHom` / `appHom` 的定义

English:
definition appHom
  signature: (X : C)
  body: α.app X
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]

中文:
定义 appHom
  签名: (X : C)
  定义体: α.app X
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
-/
def appHom (X : C) : (F ⟶ G) ->+ (F.obj X ⟶ G.obj X) where
  toFun α := α.app X
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
/--
theorem `app_zero` / 定理 `app_zero`

English:
theorem app_zero
  given: (X : C)
  statement: (0 : F ⟶ G).app X = 0
  proof: rfl

@[simp]

中文:
定理 app_zero
  条件: (X : C)
  结论: (0 : F ⟶ G).app X = 0
  证明: rfl

@[simp]
-/
theorem app_zero (X : C) : (0 : F ⟶ G).app X = 0 :=
  rfl

@[simp]
/--
theorem `app_add` / 定理 `app_add`

English:
theorem app_add
  given: (X : C) (α β : F ⟶ G)
  statement: (α + β).app X = α.app X + β.app X
  proof: rfl

@[simp]

中文:
定理 app_add
  条件: (X : C) (α β : F ⟶ G)
  结论: (α + β).app X = α.app X + β.app X
  证明: rfl

@[simp]
-/
theorem app_add (X : C) (α β : F ⟶ G) : (α + β).app X = α.app X + β.app X :=
  rfl

@[simp]
/--
theorem `app_sub` / 定理 `app_sub`

English:
theorem app_sub
  given: (X : C) (α β : F ⟶ G)
  statement: (α - β).app X = α.app X - β.app X
  proof: rfl

@[simp]

中文:
定理 app_sub
  条件: (X : C) (α β : F ⟶ G)
  结论: (α - β).app X = α.app X - β.app X
  证明: rfl

@[simp]
-/
theorem app_sub (X : C) (α β : F ⟶ G) : (α - β).app X = α.app X - β.app X :=
  rfl

@[simp]
/--
theorem `app_neg` / 定理 `app_neg`

English:
theorem app_neg
  given: (X : C) (α : F ⟶ G)
  statement: (-α).app X = -α.app X
  proof: rfl

@[simp]

中文:
定理 app_neg
  条件: (X : C) (α : F ⟶ G)
  结论: (-α).app X = -α.app X
  证明: rfl

@[simp]
-/
theorem app_neg (X : C) (α : F ⟶ G) : (-α).app X = -α.app X :=
  rfl

@[simp]
/--
theorem `app_nsmul` / 定理 `app_nsmul`

English:
theorem app_nsmul
  given: (X : C) (α : F ⟶ G) (n : Nat)
  statement: (n • α).app X = n • α.app X
  proof: rfl

@[simp]

中文:
定理 app_nsmul
  条件: (X : C) (α : F ⟶ G) (n : 自然数)
  结论: (n • α).app X = n • α.app X
  证明: rfl

@[simp]
-/
theorem app_nsmul (X : C) (α : F ⟶ G) (n : Nat) : (n • α).app X = n • α.app X :=
  rfl

@[simp]
/--
theorem `app_zsmul` / 定理 `app_zsmul`

English:
theorem app_zsmul
  given: (X : C) (α : F ⟶ G) (n : Int)
  statement: (n • α).app X = n • α.app X
  proof: rfl

@[simp]

中文:
定理 app_zsmul
  条件: (X : C) (α : F ⟶ G) (n : 整数)
  结论: (n • α).app X = n • α.app X
  证明: rfl

@[simp]
-/
theorem app_zsmul (X : C) (α : F ⟶ G) (n : Int) : (n • α).app X = n • α.app X :=
  rfl

@[simp]
/--
theorem `app_units_zsmul` / 定理 `app_units_zsmul`

English:
theorem app_units_zsmul
  given: (X : C) (α : F ⟶ G) (n : Intˣ)
  statement: (n • α).app X = n • α.app X
  proof: rfl

@[simp]

中文:
定理 app_units_zsmul
  条件: (X : C) (α : F ⟶ G) (n : 整数ˣ)
  结论: (n • α).app X = n • α.app X
  证明: rfl

@[simp]
-/
theorem app_units_zsmul (X : C) (α : F ⟶ G) (n : Intˣ) : (n • α).app X = n • α.app X :=
  rfl

@[simp]
/--
theorem `app_sum` / 定理 `app_sum`

English:
theorem app_sum
  given: {ι : Type*} (s : Finset ι) (X : C) (α : ι -> (F ⟶ G))
  proof: by
  simp only [← appHom_apply, map_sum]

中文:
定理 app_sum
  条件: {ι : 类型} (s : 有限集 ι) (X : C) (α : ι -> (F ⟶ G))
  证明: by
  simp only [← appHom_apply, map_sum]

Depends on / 依赖: appHom_apply, map_sum
-/
theorem app_sum {ι : Type*} (s : Finset ι) (X : C) (α : ι -> (F ⟶ G)) :
    (∑ i in s, α i).app X = ∑ i in s, (α i).app X := by
  simp only [← appHom_apply, map_sum]

end NatTrans

end CategoryTheory
