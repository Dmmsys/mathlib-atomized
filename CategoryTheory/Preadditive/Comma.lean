/-
Copyright (c) 2026 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# The comma category is preadditive

If we have additive functors `L : A ⥤ T` and `R : B ⥤ T` between preadditive categories,
then there is a structure of preadditive category on `Comma L R` such that addition commutes
with the left and right projections.

We then apply this to `Arrow T` for `T` a preadditive category.

## Tags

comma, arrow, preadditive
-/

@[expose] public section

namespace CategoryTheory

open Category

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {A : Type u₁} [Category.{v₁} A] [Preadditive A]
variable {B : Type u₂} [Category.{v₂} B] [Preadditive B]
variable {T : Type u₃} [Category.{v₃} T] [Preadditive T]
variable (L : A ⥤ T) [L.Additive] (R : B ⥤ T) [R.Additive]
variable {u v : Comma L R}

section Comma

namespace CommaMorphism

@[simps!]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (u ⟶ v)
  body: CommaMorphism.mk (α.left + β.left) (α.right + β.right) (by simp)

@[simps!]

中文:
实例 :
  签名: 加法 (u ⟶ v)
  定义体: CommaMorphism.mk (α.left + β.left) (α.right + β.right) (by simp)

@[simps!]

Depends on / 依赖: CommaMorphism, CommaMorphism.mk
-/
instance : Add (u ⟶ v) where
  add α β := CommaMorphism.mk (α.left + β.left) (α.right + β.right) (by simp)

@[simps!]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub (u ⟶ v)
  body: CommaMorphism.mk (α.left - β.left) (α.right - β.right) (by simp)

@[simps!]

中文:
实例 :
  签名: 减法 (u ⟶ v)
  定义体: CommaMorphism.mk (α.left - β.left) (α.right - β.right) (by simp)

@[simps!]

Depends on / 依赖: CommaMorphism, CommaMorphism.mk
-/
instance : Sub (u ⟶ v) where
  sub α β := CommaMorphism.mk (α.left - β.left) (α.right - β.right) (by simp)

@[simps!]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (u ⟶ v)
  body: CommaMorphism.mk 0 0

@[simps!]

中文:
实例 :
  签名: 零 (u ⟶ v)
  定义体: CommaMorphism.mk 0 0

@[simps!]

Depends on / 依赖: CommaMorphism, CommaMorphism.mk
-/
instance : Zero (u ⟶ v) where
  zero := CommaMorphism.mk 0 0

@[simps!]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (u ⟶ v)
  body: CommaMorphism.mk (-α.left) (-α.right)

中文:
实例 :
  签名: 取负 (u ⟶ v)
  定义体: CommaMorphism.mk (-α.left) (-α.right)

Depends on / 依赖: CommaMorphism, CommaMorphism.mk
-/
instance : Neg (u ⟶ v) where
  neg α := CommaMorphism.mk (-α.left) (-α.right)

end CommaMorphism

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (u ⟶ v)
  body: by ext <;> simp [add_assoc]
  zero_add _ := by cat_disch
  add_zero _ := by cat_disch
  add_comm _ _ := by ext <;> simp [add_comm]
  neg_add_cancel _ := by cat_disch
  sub_eq_add_neg _ _ := by ext <;> simp [sub_eq_add_neg]
  nsmul n α := CommaMorphism.mk (n • α.left) (n • α.right)
    (by simp [Functor.map_nsmul, Preadditive.comp_nsmul, Preadditive.nsmul_comp])
  zsmul n α := CommaMorphism.mk (n • α.left) (n • α.right)
    (by simp [Functor.map_zsmul, Preadditive.comp_zsmul, Preadditive.zsmul_comp])
  nsmul_zero := by simp_rw [HSMul.hSMul, SMul.smul]; cat_disch
  nsmul_succ _ _ := by simp_rw [HSMul.hSMul, SMul.smul]; ext <;> dsimp <;> simp [add_nsmul]
  zsmul_zero' := by simp_rw [HSMul.hSMul, SMul.smul]; cat_disch
  zsmul_succ' _ _ := by simp_rw [HSMul.hSMul, SMul.smul]; ext <;> dsimp <;> simp [add_zsmul]
  zsmul_neg' _ _ := by
    simp_rw [HSMul.hSMul, SMul.smul]
    ext <;> dsimp <;> simp [add_nsmul, add_zsmul]

中文:
实例 :
  签名: 加法交换群 (u ⟶ v)
  定义体: by ext <;> simp [add_assoc]
  zero_add _ := by cat_disch
  add_zero _ := by cat_disch
  add_comm _ _ := by ext <;> simp [add_comm]
  neg_add_cancel _ := by cat_disch
  sub_eq_add_neg _ _ := by ext <;> simp [sub_eq_add_neg]
  nsmul n α := CommaMorphism.mk (n • α.left) (n • α.right)
    (by simp [Functor.map_nsmul, Preadditive.comp_nsmul, Preadditive.nsmul_comp])
  zsmul n α := CommaMorphism.mk (n • α.left) (n • α.right)
    (by simp [Functor.map_zsmul, Preadditive.comp_zsmul, Preadditive.zsmul_comp])
  nsmul_zero := by simp_rw [HSMul.hSMul, SMul.smul]; cat_disch
  nsmul_succ _ _ := by simp_rw [HSMul.hSMul, SMul.smul]; ext <;> dsimp <;> simp [add_nsmul]
  zsmul_zero' := by simp_rw [HSMul.hSMul, SMul.smul]; cat_disch
  zsmul_succ' _ _ := by simp_rw [HSMul.hSMul, SMul.smul]; ext <;> dsimp <;> simp [add_zsmul]
  zsmul_neg' _ _ := by
    simp_rw [HSMul.hSMul, SMul.smul]
    ext <;> dsimp <;> simp [add_nsmul, add_zsmul]

Depends on / 依赖: CommaMorphism, CommaMorphism.mk, Functor, Functor.map_nsmul, Functor.map_zsmul, Preadditive, Preadditive.comp_nsmul, Preadditive.comp_zsmul, Preadditive.nsmul_comp, Preadditive.zsmul_comp, add_assoc, add_comm, add_zero, cat_disch, comp_nsmul, comp_zsmul, map_nsmul, map_zsmul, neg_add_cancel, nsmul_comp
-/
instance : AddCommGroup (u ⟶ v) where
  add_assoc _ _ _ := by ext <;> simp [add_assoc]
  zero_add _ := by cat_disch
  add_zero _ := by cat_disch
  add_comm _ _ := by ext <;> simp [add_comm]
  neg_add_cancel _ := by cat_disch
  sub_eq_add_neg _ _ := by ext <;> simp [sub_eq_add_neg]
  nsmul n α := CommaMorphism.mk (n • α.left) (n • α.right)
    (by simp [Functor.map_nsmul, Preadditive.comp_nsmul, Preadditive.nsmul_comp])
  zsmul n α := CommaMorphism.mk (n • α.left) (n • α.right)
    (by simp [Functor.map_zsmul, Preadditive.comp_zsmul, Preadditive.zsmul_comp])
  nsmul_zero := by simp_rw [HSMul.hSMul, SMul.smul]; cat_disch
  nsmul_succ _ _ := by simp_rw [HSMul.hSMul, SMul.smul]; ext <;> dsimp <;> simp [add_nsmul]
  zsmul_zero' := by simp_rw [HSMul.hSMul, SMul.smul]; cat_disch
  zsmul_succ' _ _ := by simp_rw [HSMul.hSMul, SMul.smul]; ext <;> dsimp <;> simp [add_zsmul]
  zsmul_neg' _ _ := by
    simp_rw [HSMul.hSMul, SMul.smul]
    ext <;> dsimp <;> simp [add_nsmul, add_zsmul]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preadditive (Comma L R)

中文:
实例 :
  签名: 预加性 (交换a L R)
-/
instance : Preadditive (Comma L R) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Comma.fst L R).Additive

中文:
实例 :
  签名: (交换a.fst L R).加性
-/
instance : (Comma.fst L R).Additive where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Comma.snd L R).Additive

中文:
实例 :
  签名: (交换a.snd L R).加性
-/
instance : (Comma.snd L R).Additive where

end Comma

section Arrow

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preadditive (Arrow T)
  body: inferInstanceAs (Preadditive (Comma (𝟭 T) (𝟭 T)))

中文:
实例 :
  签名: 预加性 (箭头 T)
  定义体: inferInstanceAs (Preadditive (Comma (𝟭 T) (𝟭 T)))

Depends on / 依赖: Preadditive
-/
instance : Preadditive (Arrow T) := inferInstanceAs (Preadditive (Comma (𝟭 T) (𝟭 T)))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Arrow.leftFunc (C := T)).Additive
  body: inferInstanceAs ((Comma.fst (𝟭 T) (𝟭 T))).Additive

中文:
实例 :
  签名: (箭头.leftFunc (C := T)).加性
  定义体: inferInstanceAs ((Comma.fst (𝟭 T) (𝟭 T))).Additive

Depends on / 依赖: Additive
-/
instance : (Arrow.leftFunc (C := T)).Additive :=
  inferInstanceAs ((Comma.fst (𝟭 T) (𝟭 T))).Additive

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Arrow.rightFunc (C := T)).Additive
  body: inferInstanceAs ((Comma.snd (𝟭 T) (𝟭 T))).Additive

中文:
实例 :
  签名: (箭头.rightFunc (C := T)).加性
  定义体: inferInstanceAs ((Comma.snd (𝟭 T) (𝟭 T))).Additive

Depends on / 依赖: Additive
-/
instance : (Arrow.rightFunc (C := T)).Additive :=
  inferInstanceAs ((Comma.snd (𝟭 T) (𝟭 T))).Additive

variable {u v : Arrow T}

@[simp]
/--
lemma `Arrow.Hom.add_left` / 引理 `Arrow.Hom.add_left`

English:
lemma Arrow.Hom.add_left
  given: (α β : u ⟶ v)
  statement: (α + β).left = α.left + β.left
  proof: rfl

@[simp]

中文:
引理 箭头.态射.add_left
  条件: (α β : u ⟶ v)
  结论: (α + β).left = α.left + β.left
  证明: rfl

@[simp]
-/
lemma Arrow.Hom.add_left (α β : u ⟶ v) : (α + β).left = α.left + β.left := rfl

@[simp]
/--
lemma `Arrow.Hom.add_right` / 引理 `Arrow.Hom.add_right`

English:
lemma Arrow.Hom.add_right
  given: (α β : u ⟶ v)
  statement: (α + β).right = α.right + β.right
  proof: rfl

@[simp]

中文:
引理 箭头.态射.add_right
  条件: (α β : u ⟶ v)
  结论: (α + β).right = α.right + β.right
  证明: rfl

@[simp]
-/
lemma Arrow.Hom.add_right (α β : u ⟶ v) : (α + β).right = α.right + β.right := rfl

@[simp]
/--
lemma `Arrow.Hom.sub_left` / 引理 `Arrow.Hom.sub_left`

English:
lemma Arrow.Hom.sub_left
  given: (α β : u ⟶ v)
  statement: (α - β).left = α.left - β.left
  proof: rfl

@[simp]

中文:
引理 箭头.态射.sub_left
  条件: (α β : u ⟶ v)
  结论: (α - β).left = α.left - β.left
  证明: rfl

@[simp]
-/
lemma Arrow.Hom.sub_left (α β : u ⟶ v) : (α - β).left = α.left - β.left := rfl

@[simp]
/--
lemma `Arrow.Hom.sub_right` / 引理 `Arrow.Hom.sub_right`

English:
lemma Arrow.Hom.sub_right
  given: (α β : u ⟶ v)
  statement: (α - β).right = α.right - β.right
  proof: rfl

@[simp]

中文:
引理 箭头.态射.sub_right
  条件: (α β : u ⟶ v)
  结论: (α - β).right = α.right - β.right
  证明: rfl

@[simp]
-/
lemma Arrow.Hom.sub_right (α β : u ⟶ v) : (α - β).right = α.right - β.right := rfl

@[simp]
/--
lemma `Arrow.Hom.zero_left` / 引理 `Arrow.Hom.zero_left`

English:
lemma Arrow.Hom.zero_left
  statement: (0 : u ⟶ v).left = 0
  proof: rfl

@[simp]

中文:
引理 箭头.态射.zero_left
  结论: (0 : u ⟶ v).left = 0
  证明: rfl

@[simp]
-/
lemma Arrow.Hom.zero_left : (0 : u ⟶ v).left = 0 := rfl

@[simp]
/--
lemma `Arrow.Hom.zero_right` / 引理 `Arrow.Hom.zero_right`

English:
lemma Arrow.Hom.zero_right
  statement: (0 : u ⟶ v).right = 0
  proof: rfl

@[simp]

中文:
引理 箭头.态射.zero_right
  结论: (0 : u ⟶ v).right = 0
  证明: rfl

@[simp]
-/
lemma Arrow.Hom.zero_right : (0 : u ⟶ v).right = 0 := rfl

@[simp]
/--
lemma `Arrow.Hom.neg_left` / 引理 `Arrow.Hom.neg_left`

English:
lemma Arrow.Hom.neg_left
  given: (α : u ⟶ v)
  statement: (-α).left = -α.left
  proof: rfl

@[simp]

中文:
引理 箭头.态射.neg_left
  条件: (α : u ⟶ v)
  结论: (-α).left = -α.left
  证明: rfl

@[simp]
-/
lemma Arrow.Hom.neg_left (α : u ⟶ v) : (-α).left = -α.left := rfl

@[simp]
/--
lemma `Arrow.Hom.neg_right` / 引理 `Arrow.Hom.neg_right`

English:
lemma Arrow.Hom.neg_right
  given: (α : u ⟶ v)
  statement: (-α).right = -α.right
  proof: rfl

中文:
引理 箭头.态射.neg_right
  条件: (α : u ⟶ v)
  结论: (-α).right = -α.right
  证明: rfl
-/
lemma Arrow.Hom.neg_right (α : u ⟶ v) : (-α).right = -α.right := rfl

end Arrow

end CategoryTheory
