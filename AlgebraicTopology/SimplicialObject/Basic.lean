/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison, Adam Topaz
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.Adjunction.Reflective
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.Util.Superscript

/-!
# Simplicial objects in a category.

A simplicial object in a category `C` is a `C`-valued presheaf on `SimplexCategory`.
(Similarly, a cosimplicial object is a functor `SimplexCategory ⥤ C`.)

## Notation

The following notations can be enabled via `open Simplicial`.

- `X _⦋n⦌` denotes the `n`-th term of a simplicial object `X`, where `n : ℕ`.
- `X ^⦋n⦌` denotes the `n`-th term of a cosimplicial object `X`, where `n : ℕ`.

The following notations can be enabled via
`open CategoryTheory.SimplicialObject.Truncated`.

- `X _⦋m⦌ₙ` denotes the `m`-th term of an `n`-truncated simplicial object `X`.
- `X ^⦋m⦌ₙ` denotes the `m`-th term of an `n`-truncated cosimplicial object `X`.
-/

@[expose] public section

open Opposite

open CategoryTheory

open CategoryTheory.Limits CategoryTheory.Functor

universe v u v' u'

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/--
Definition of `SimplicialObject` / `SimplicialObject` 的定义

English:
abbreviation SimplicialObject
  body: SimplexCategoryᵒᵖ ⥤ C

中文:
缩写 SimplicialObject
  定义体: SimplexCategoryᵒᵖ ⥤ C
-/
abbrev SimplicialObject :=
  SimplexCategoryᵒᵖ ⥤ C

namespace SimplicialObject

set_option quotPrecheck false in
/-- `X _⦋n⦌` denotes the `n`th-term of the simplicial object X -/
scoped[Simplicial]
  notation3:1000 X " _⦋" n "⦌" =>
      (X : CategoryTheory.SimplicialObject _).obj (Opposite.op (SimplexCategory.mk n))

open Simplicial

instance {J : Type v} [SmallCategory J] [HasLimitsOfShape J C] :
    HasLimitsOfShape J (SimplicialObject C) := by
  dsimp [SimplicialObject]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasLimits
  signature: C] : HasLimits (SimplicialObject C)
  body: ⟨inferInstance⟩

中文:
实例 [有极限
  签名: C] : 有极限 (SimplicialObject C)
  定义体: ⟨inferInstance⟩
-/
instance [HasLimits C] : HasLimits (SimplicialObject C) :=
  ⟨inferInstance⟩

instance {J : Type v} [SmallCategory J] [HasColimitsOfShape J C] :
    HasColimitsOfShape J (SimplicialObject C) := by
  dsimp [SimplicialObject]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasColimits
  signature: C] : HasColimits (SimplicialObject C)
  body: ⟨inferInstance⟩

中文:
实例 [有余极限
  签名: C] : 有余极限 (SimplicialObject C)
  定义体: ⟨inferInstance⟩
-/
instance [HasColimits C] : HasColimits (SimplicialObject C) :=
  ⟨inferInstance⟩

variable {C}

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  statement: {X Y : SimplicialObject C} (f g : X ⟶ Y)
  proof: NatTrans.ext (by ext; apply h)

中文:
引理 hom_ext
  结论: {X Y : SimplicialObject C} (f g : X ⟶ Y)
  证明: NatTrans.ext (by ext; apply h)

Depends on / 依赖: NatTrans, NatTrans.ext
-/
lemma hom_ext {X Y : SimplicialObject C} (f g : X ⟶ Y)
    (h : forall (n : SimplexCategoryᵒᵖ), f.app n = g.app n) : f = g :=
  NatTrans.ext (by ext; apply h)

variable (X : SimplicialObject C)

/--
Definition of `δ` / `δ` 的定义

English:
definition δ
  signature: {n} (i : Fin (n + 2))
  body: X.map (SimplexCategory.δ i).op

中文:
定义 δ
  签名: {n} (i : 有限集 (n + 2))
  定义体: X.map (SimplexCategory.δ i).op

Depends on / 依赖: SimplexCategory, X.map
-/
def δ {n} (i : Fin (n + 2)) : X _⦋n + 1⦌ ⟶ X _⦋n⦌ :=
  X.map (SimplexCategory.δ i).op

/--
lemma `δ_def` / 引理 `δ_def`

English:
lemma δ_def
  given: {n} (i : Fin (n + 2))
  statement: X.δ i = X.map (SimplexCategory.δ i).op
  proof: rfl

中文:
引理 δ_def
  条件: {n} (i : 有限集 (n + 2))
  结论: X.δ i = X.map (单纯形范畴.δ i).op
  证明: rfl
-/
lemma δ_def {n} (i : Fin (n + 2)) : X.δ i = X.map (SimplexCategory.δ i).op := rfl

/--
Definition of `σ` / `σ` 的定义

English:
definition σ
  signature: {n} (i : Fin (n + 1))
  body: X.map (SimplexCategory.σ i).op

中文:
定义 σ
  签名: {n} (i : 有限集 (n + 1))
  定义体: X.map (SimplexCategory.σ i).op

Depends on / 依赖: SimplexCategory, X.map
-/
def σ {n} (i : Fin (n + 1)) : X _⦋n⦌ ⟶ X _⦋n + 1⦌ :=
  X.map (SimplexCategory.σ i).op

/--
lemma `σ_def` / 引理 `σ_def`

English:
lemma σ_def
  given: {n} (i : Fin (n + 1))
  statement: X.σ i = X.map (SimplexCategory.σ i).op
  proof: rfl

中文:
引理 σ_def
  条件: {n} (i : 有限集 (n + 1))
  结论: X.σ i = X.map (单纯形范畴.σ i).op
  证明: rfl
-/
lemma σ_def {n} (i : Fin (n + 1)) : X.σ i = X.map (SimplexCategory.σ i).op := rfl

/--
Definition of `diagonal` / `diagonal` 的定义

English:
definition diagonal
  signature: {n : Nat}
  body: X.map ((SimplexCategory.diag n).op)

中文:
定义 diagonal
  签名: {n : 自然数}
  定义体: X.map ((SimplexCategory.diag n).op)

Depends on / 依赖: SimplexCategory, SimplexCategory.diag, X.map
-/
def diagonal {n : Nat} : X _⦋n⦌ ⟶ X _⦋1⦌ := X.map ((SimplexCategory.diag n).op)

/--
Definition of `eqToIso` / `eqToIso` 的定义

English:
definition eqToIso
  signature: {n m : Nat} (h : n = m)
  body: X.mapIso (CategoryTheory.eqToIso (by congr))

@[simp]

中文:
定义 eqToIso
  签名: {n m : 自然数} (h : n = m)
  定义体: X.mapIso (CategoryTheory.eqToIso (by congr))

@[simp]

Depends on / 依赖: CategoryTheory, CategoryTheory.eqToIso, X.mapIso, eqToIso, mapIso
-/
def eqToIso {n m : Nat} (h : n = m) : X _⦋n⦌ ≅ X _⦋m⦌ :=
  X.mapIso (CategoryTheory.eqToIso (by congr))

@[simp]
/--
theorem `eqToIso_refl` / 定理 `eqToIso_refl`

English:
theorem eqToIso_refl
  given: {n : Nat} (h : n = n)
  statement: X.eqToIso h = Iso.refl _
  proof: by
  simp [eqToIso]

中文:
定理 eqToIso_refl
  条件: {n : 自然数} (h : n = n)
  结论: X.eqToIso h = 同构.refl _
  证明: by
  simp [eqToIso]

Depends on / 依赖: eqToIso
-/
theorem eqToIso_refl {n : Nat} (h : n = n) : X.eqToIso h = Iso.refl _ := by
  simp [eqToIso]

/-- The generic case of the first simplicial identity -/
@[reassoc]
/--
theorem `δ_comp_δ` / 定理 `δ_comp_δ`

English:
theorem δ_comp_δ
  given: {n} {i j : Fin (n + 2)} (H : i <= j)
  proof: by
  dsimp [δ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ H]

@[reassoc]

中文:
定理 δ_comp_δ
  条件: {n} {i j : 有限集 (n + 2)} (H : i <= j)
  证明: by
  dsimp [δ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ H]

@[reassoc]

Depends on / 依赖: SimplexCategory, X.map_comp, map_comp, op_comp
-/
theorem δ_comp_δ {n} {i j : Fin (n + 2)} (H : i <= j) :
    X.δ j.succ ≫ X.δ i = X.δ (Fin.castSucc i) ≫ X.δ j := by
  dsimp [δ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ H]

@[reassoc]
/--
theorem `δ_comp_δ'` / 定理 `δ_comp_δ'`

English:
theorem δ_comp_δ'
  given: {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : Fin.castSucc i < j)
  proof: by
  dsimp [δ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ' H]
@[reassoc]

中文:
定理 δ_comp_δ'
  条件: {n} {i : 有限集 (n + 2)} {j : 有限集 (n + 3)} (H : 有限集.castSucc i < j)
  证明: by
  dsimp [δ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ' H]
@[reassoc]

Depends on / 依赖: SimplexCategory, X.map_comp, map_comp, op_comp, reassoc
-/
theorem δ_comp_δ' {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : Fin.castSucc i < j) :
    X.δ j ≫ X.δ i =
      X.δ (Fin.castSucc i) ≫
        X.δ (j.pred H.ne_zero) := by
  dsimp [δ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ' H]
@[reassoc]
/--
theorem `δ_comp_δ''` / 定理 `δ_comp_δ''`

English:
theorem δ_comp_δ''
  given: {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : i <= Fin.castSucc j)
  proof: by
  dsimp [δ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ'' H]

中文:
定理 δ_comp_δ''
  条件: {n} {i : 有限集 (n + 3)} {j : 有限集 (n + 2)} (H : i <= 有限集.castSucc j)
  证明: by
  dsimp [δ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ'' H]

Depends on / 依赖: SimplexCategory, X.map_comp, map_comp, op_comp
-/
theorem δ_comp_δ'' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : i <= Fin.castSucc j) :
    X.δ j.succ ≫ X.δ (i.castLT (Nat.lt_of_le_of_lt (Fin.le_iff_val_le_val.mp H) j.is_lt)) =
      X.δ i ≫ X.δ j := by
  dsimp [δ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ'' H]

/-- The special case of the first simplicial identity -/
@[reassoc]
/--
theorem `δ_comp_δ_self` / 定理 `δ_comp_δ_self`

English:
theorem δ_comp_δ_self
  given: {n} {i : Fin (n + 2)}
  proof: by
  dsimp [δ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ_self]

@[reassoc]

中文:
定理 δ_comp_δ_self
  条件: {n} {i : 有限集 (n + 2)}
  证明: by
  dsimp [δ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ_self]

@[reassoc]

Depends on / 依赖: SimplexCategory, X.map_comp, map_comp, op_comp
-/
theorem δ_comp_δ_self {n} {i : Fin (n + 2)} :
    X.δ (Fin.castSucc i) ≫ X.δ i = X.δ i.succ ≫ X.δ i := by
  dsimp [δ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ_self]

@[reassoc]
/--
theorem `δ_comp_δ_self'` / 定理 `δ_comp_δ_self'`

English:
theorem δ_comp_δ_self'
  given: {n} {j : Fin (n + 3)} {i : Fin (n + 2)} (H : j = Fin.castSucc i)
  proof: by
  subst H
  rw [δ_comp_δ_self]

中文:
定理 δ_comp_δ_self'
  条件: {n} {j : 有限集 (n + 3)} {i : 有限集 (n + 2)} (H : j = 有限集.castSucc i)
  证明: by
  subst H
  rw [δ_comp_δ_self]
-/
theorem δ_comp_δ_self' {n} {j : Fin (n + 3)} {i : Fin (n + 2)} (H : j = Fin.castSucc i) :
    X.δ j ≫ X.δ i = X.δ i.succ ≫ X.δ i := by
  subst H
  rw [δ_comp_δ_self]

/-- The second simplicial identity -/
@[reassoc]
/--
theorem `δ_comp_σ_of_le` / 定理 `δ_comp_σ_of_le`

English:
theorem δ_comp_σ_of_le
  given: {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i <= Fin.castSucc j)
  proof: by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_of_le H]

中文:
定理 δ_comp_σ_of_le
  条件: {n} {i : 有限集 (n + 2)} {j : 有限集 (n + 1)} (H : i <= 有限集.castSucc j)
  证明: by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_of_le H]

Depends on / 依赖: SimplexCategory, X.map_comp, map_comp, op_comp
-/
theorem δ_comp_σ_of_le {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i <= Fin.castSucc j) :
    X.σ j.succ ≫ X.δ (Fin.castSucc i) = X.δ i ≫ X.σ j := by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_of_le H]

/-- The first part of the third simplicial identity -/
@[reassoc]
/--
theorem `δ_comp_σ_self` / 定理 `δ_comp_σ_self`

English:
theorem δ_comp_σ_self
  given: {n} {i : Fin (n + 1)}
  statement: X.σ i ≫ X.δ (Fin.castSucc i) = 𝟙 _
  proof: by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_self, op_id, X.map_id]

@[reassoc]

中文:
定理 δ_comp_σ_self
  条件: {n} {i : 有限集 (n + 1)}
  结论: X.σ i ≫ X.δ (有限集.castSucc i) = 𝟙 _
  证明: by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_self, op_id, X.map_id]

@[reassoc]

Depends on / 依赖: SimplexCategory, X.map_comp, X.map_id, map_comp, map_id, op_comp, op_id
-/
theorem δ_comp_σ_self {n} {i : Fin (n + 1)} : X.σ i ≫ X.δ (Fin.castSucc i) = 𝟙 _ := by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_self, op_id, X.map_id]

@[reassoc]
/--
theorem `δ_comp_σ_self'` / 定理 `δ_comp_σ_self'`

English:
theorem δ_comp_σ_self'
  given: {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = Fin.castSucc i)
  proof: by
  subst H
  rw [δ_comp_σ_self]

中文:
定理 δ_comp_σ_self'
  条件: {n} {j : 有限集 (n + 2)} {i : 有限集 (n + 1)} (H : j = 有限集.castSucc i)
  证明: by
  subst H
  rw [δ_comp_σ_self]
-/
theorem δ_comp_σ_self' {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = Fin.castSucc i) :
    X.σ i ≫ X.δ j = 𝟙 _ := by
  subst H
  rw [δ_comp_σ_self]

/-- The second part of the third simplicial identity -/
@[reassoc]
/--
theorem `δ_comp_σ_succ` / 定理 `δ_comp_σ_succ`

English:
theorem δ_comp_σ_succ
  given: {n} {i : Fin (n + 1)}
  statement: X.σ i ≫ X.δ i.succ = 𝟙 _
  proof: by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_succ, op_id, X.map_id]

@[reassoc]

中文:
定理 δ_comp_σ_succ
  条件: {n} {i : 有限集 (n + 1)}
  结论: X.σ i ≫ X.δ i.succ = 𝟙 _
  证明: by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_succ, op_id, X.map_id]

@[reassoc]

Depends on / 依赖: SimplexCategory, X.map_comp, X.map_id, map_comp, map_id, op_comp, op_id
-/
theorem δ_comp_σ_succ {n} {i : Fin (n + 1)} : X.σ i ≫ X.δ i.succ = 𝟙 _ := by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_succ, op_id, X.map_id]

@[reassoc]
/--
theorem `δ_comp_σ_succ'` / 定理 `δ_comp_σ_succ'`

English:
theorem δ_comp_σ_succ'
  given: {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = i.succ)
  proof: by
  subst H
  rw [δ_comp_σ_succ]

中文:
定理 δ_comp_σ_succ'
  条件: {n} {j : 有限集 (n + 2)} {i : 有限集 (n + 1)} (H : j = i.succ)
  证明: by
  subst H
  rw [δ_comp_σ_succ]
-/
theorem δ_comp_σ_succ' {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = i.succ) :
    X.σ i ≫ X.δ j = 𝟙 _ := by
  subst H
  rw [δ_comp_σ_succ]

/-- The fourth simplicial identity -/
@[reassoc]
/--
theorem `δ_comp_σ_of_gt` / 定理 `δ_comp_σ_of_gt`

English:
theorem δ_comp_σ_of_gt
  given: {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : Fin.castSucc j < i)
  proof: by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_of_gt H]

@[reassoc]

中文:
定理 δ_comp_σ_of_gt
  条件: {n} {i : 有限集 (n + 2)} {j : 有限集 (n + 1)} (H : 有限集.castSucc j < i)
  证明: by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_of_gt H]

@[reassoc]

Depends on / 依赖: SimplexCategory, X.map_comp, map_comp, op_comp
-/
theorem δ_comp_σ_of_gt {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : Fin.castSucc j < i) :
    X.σ (Fin.castSucc j) ≫ X.δ i.succ = X.δ i ≫ X.σ j := by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_of_gt H]

@[reassoc]
/--
theorem `δ_comp_σ_of_gt'` / 定理 `δ_comp_σ_of_gt'`

English:
theorem δ_comp_σ_of_gt'
  given: {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : j.succ < i)
  proof: by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_of_gt' H]

中文:
定理 δ_comp_σ_of_gt'
  条件: {n} {i : 有限集 (n + 3)} {j : 有限集 (n + 2)} (H : j.succ < i)
  证明: by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_of_gt' H]

Depends on / 依赖: SimplexCategory, X.map_comp, map_comp, op_comp
-/
theorem δ_comp_σ_of_gt' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : j.succ < i) :
    X.σ j ≫ X.δ i =
      X.δ (i.pred H.ne_zero) ≫
        X.σ (j.castLT ((add_lt_add_iff_right 1).mp (lt_of_lt_of_le H i.is_le))) := by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_of_gt' H]

/-- The fifth simplicial identity -/
@[reassoc]
/--
theorem `σ_comp_σ` / 定理 `σ_comp_σ`

English:
theorem σ_comp_σ
  given: {n} {i j : Fin (n + 1)} (H : i <= j)
  proof: by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.σ_comp_σ H]

中文:
定理 σ_comp_σ
  条件: {n} {i j : 有限集 (n + 1)} (H : i <= j)
  证明: by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.σ_comp_σ H]

Depends on / 依赖: SimplexCategory, X.map_comp, map_comp, op_comp
-/
theorem σ_comp_σ {n} {i j : Fin (n + 1)} (H : i <= j) :
    X.σ j ≫ X.σ (Fin.castSucc i) = X.σ i ≫ X.σ j.succ := by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.σ_comp_σ H]

open Simplicial

@[reassoc (attr := simp)]
/--
theorem `δ_naturality` / 定理 `δ_naturality`

English:
theorem δ_naturality
  given: {X' X : SimplicialObject C} (f : X ⟶ X') {n : Nat} (i : Fin (n + 2))
  proof: f.naturality _

@[reassoc (attr := simp)]

中文:
定理 δ_naturality
  条件: {X' X : SimplicialObject C} (f : X ⟶ X') {n : 自然数} (i : 有限集 (n + 2))
  证明: f.naturality _

@[reassoc (attr := simp)]

Depends on / 依赖: f.naturality, naturality
-/
theorem δ_naturality {X' X : SimplicialObject C} (f : X ⟶ X') {n : Nat} (i : Fin (n + 2)) :
    X.δ i ≫ f.app (op ⦋n⦌) = f.app (op ⦋n + 1⦌) ≫ X'.δ i :=
  f.naturality _

@[reassoc (attr := simp)]
/--
theorem `σ_naturality` / 定理 `σ_naturality`

English:
theorem σ_naturality
  given: {X' X : SimplicialObject C} (f : X ⟶ X') {n : Nat} (i : Fin (n + 1))
  proof: f.naturality _

中文:
定理 σ_naturality
  条件: {X' X : SimplicialObject C} (f : X ⟶ X') {n : 自然数} (i : 有限集 (n + 1))
  证明: f.naturality _

Depends on / 依赖: f.naturality, naturality
-/
theorem σ_naturality {X' X : SimplicialObject C} (f : X ⟶ X') {n : Nat} (i : Fin (n + 1)) :
    X.σ i ≫ f.app (op ⦋n + 1⦌) = f.app (op ⦋n⦌) ≫ X'.σ i :=
  f.naturality _

variable (C)

section

variable {D : Type*} [Category* D]

variable (D) in
/-- Functor composition induces a functor on simplicial objects. -/
@[simps!]
/--
Definition of `whiskering` / `whiskering` 的定义

English:
definition whiskering
  signature: : (C ⥤ D) ⥤ SimplicialObject C ⥤ SimplicialObject D
  body: whiskeringRight _ _ _

中文:
定义 whiskering
  签名: : (C ⥤ D) ⥤ SimplicialObject C ⥤ SimplicialObject D
  定义体: whiskeringRight _ _ _

Depends on / 依赖: whiskeringRight
-/
def whiskering : (C ⥤ D) ⥤ SimplicialObject C ⥤ SimplicialObject D :=
  whiskeringRight _ _ _

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `whiskering_obj_obj_δ` / 引理 `whiskering_obj_obj_δ`

English:
lemma whiskering_obj_obj_δ
  given: (F : C ⥤ D) (X : SimplicialObject C) {n : Nat} (i : Fin (n + 2))
  proof: rfl

中文:
引理 whiskering_obj_obj_δ
  条件: (F : C ⥤ D) (X : SimplicialObject C) {n : 自然数} (i : 有限集 (n + 2))
  证明: rfl
-/
lemma whiskering_obj_obj_δ (F : C ⥤ D) (X : SimplicialObject C) {n : Nat} (i : Fin (n + 2)) :
    dsimp% (((whiskering C D).obj F).obj X).δ i = F.map (X.δ i) := rfl

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `whiskering_obj_obj_σ` / 引理 `whiskering_obj_obj_σ`

English:
lemma whiskering_obj_obj_σ
  given: (F : C ⥤ D) (X : SimplicialObject C) {n : Nat} (i : Fin (n + 1))
  proof: rfl

中文:
引理 whiskering_obj_obj_σ
  条件: (F : C ⥤ D) (X : SimplicialObject C) {n : 自然数} (i : 有限集 (n + 1))
  证明: rfl
-/
lemma whiskering_obj_obj_σ (F : C ⥤ D) (X : SimplicialObject C) {n : Nat} (i : Fin (n + 1)) :
    dsimp% (((whiskering C D).obj F).obj X).σ i = F.map (X.σ i) := rfl

end

/--
Definition of `Truncated` / `Truncated` 的定义

English:
abbreviation Truncated
  signature: (n : Nat)
  body: (SimplexCategory.Truncated n)ᵒᵖ ⥤ C

中文:
缩写 Truncated
  签名: (n : 自然数)
  定义体: (SimplexCategory.Truncated n)ᵒᵖ ⥤ C

Depends on / 依赖: SimplexCategory, SimplexCategory.Truncated, Truncated
-/
abbrev Truncated (n : Nat) := (SimplexCategory.Truncated n)ᵒᵖ ⥤ C

variable {C}

namespace Truncated

variable (C) in
/-- Functor composition induces a functor on truncated simplicial objects. -/
@[simps!]
/--
Definition of `whiskering` / `whiskering` 的定义

English:
definition whiskering
  signature: {n} (D : Type*) [Category* D]
  body: whiskeringRight _ _ _

中文:
定义 whiskering
  签名: {n} (D : 类型) [范畴* D]
  定义体: whiskeringRight _ _ _

Depends on / 依赖: whiskeringRight
-/
def whiskering {n} (D : Type*) [Category* D] : (C ⥤ D) ⥤ Truncated C n ⥤ Truncated D n :=
  whiskeringRight _ _ _

open Mathlib.Tactic (subscriptTerm) in
/-- For `X : Truncated C n` and `m ≤ n`, `X _⦋m⦌ₙ` is the `m`-th term of X. The
proof `p : m ≤ n` can also be provided using the syntax `X _⦋m, p⦌ₙ`. -/
scoped syntax:max (name := mkNotation)
  term " _⦋" term ("," term)? "⦌" noWs subscriptTerm : term

open scoped SimplexCategory.Truncated in
scoped macro_rules
  | `($X:term _⦋$m:term⦌$n:subscript) =>
    -- try `decide` before `get_elem_tactic` because it is faster for goals with literals.
    `(($X : CategoryTheory.SimplicialObject.Truncated _ $n).obj
      (Opposite.op ⟨SimplexCategory.mk $m, by first | decide | get_elem_tactic |
      fail "Failed to prove truncation property. Try writing `X _⦋m, by ...⦌ₙ`."⟩))
  | `($X:term _⦋$m:term, $p:term⦌$n:subscript) =>
    `(($X : CategoryTheory.SimplicialObject.Truncated _ $n).obj
      (Opposite.op ⟨SimplexCategory.mk $m, $p⟩))

variable (C) in
/-- Further truncation of truncated simplicial objects. -/
@[simps!]
/--
Definition of `trunc` / `trunc` 的定义

English:
definition trunc
  signature: (n m : Nat) (h : m <= n := by lia)
  body: (whiskeringLeft _ _ _).obj (SimplexCategory.Truncated.incl m n).op

中文:
定义 trunc
  签名: (n m : 自然数) (h : m <= n := by lia)
  定义体: (whiskeringLeft _ _ _).obj (SimplexCategory.Truncated.incl m n).op

Depends on / 依赖: SimplexCategory, SimplexCategory.Truncated.incl, Truncated, whiskeringLeft
-/
def trunc (n m : Nat) (h : m <= n := by lia) : Truncated C n ⥤ Truncated C m :=
  (whiskeringLeft _ _ _).obj (SimplexCategory.Truncated.incl m n).op

end Truncated

section Truncation

/--
Definition of `truncation` / `truncation` 的定义

English:
definition truncation
  signature: (n : Nat)
  body: (whiskeringLeft _ _ _).obj (SimplexCategory.Truncated.inclusion n).op

中文:
定义 truncation
  签名: (n : 自然数)
  定义体: (whiskeringLeft _ _ _).obj (SimplexCategory.Truncated.inclusion n).op

Depends on / 依赖: SimplexCategory, SimplexCategory.Truncated.inclusion, Truncated, inclusion, whiskeringLeft
-/
def truncation (n : Nat) : SimplicialObject C ⥤ SimplicialObject.Truncated C n :=
  (whiskeringLeft _ _ _).obj (SimplexCategory.Truncated.inclusion n).op

/--
Definition of `truncationCompTrunc` / `truncationCompTrunc` 的定义

English:
definition truncationCompTrunc
  signature: {n m : Nat} (h : m <= n)
  body: Iso.refl _

中文:
定义 truncationCompTrunc
  签名: {n m : 自然数} (h : m <= n)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def truncationCompTrunc {n m : Nat} (h : m <= n) :
    truncation n ⋙ Truncated.trunc C n m ≅ truncation m :=
  Iso.refl _

end Truncation


noncomputable section

/--
Definition of `Truncated.sk` / `Truncated.sk` 的定义

English:
abbreviation Truncated.sk
  signature: (n : Nat) [forall (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
  body: lan (SimplexCategory.Truncated.inclusion n).op

中文:
缩写 Truncated.sk
  签名: (n : 自然数) [对任意 (F : (单纯形范畴.Truncated n)ᵒᵖ ⥤ C),
  定义体: lan (SimplexCategory.Truncated.inclusion n).op
-/
protected abbrev Truncated.sk (n : Nat) [forall (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
    (SimplexCategory.Truncated.inclusion n).op.HasLeftKanExtension F] :
    SimplicialObject.Truncated C n ⥤ SimplicialObject C :=
  lan (SimplexCategory.Truncated.inclusion n).op

/--
Definition of `Truncated.cosk` / `Truncated.cosk` 的定义

English:
abbreviation Truncated.cosk
  signature: (n : Nat) [forall (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
  body: ran (SimplexCategory.Truncated.inclusion n).op

中文:
缩写 Truncated.cosk
  签名: (n : 自然数) [对任意 (F : (单纯形范畴.Truncated n)ᵒᵖ ⥤ C),
  定义体: ran (SimplexCategory.Truncated.inclusion n).op
-/
protected abbrev Truncated.cosk (n : Nat) [forall (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
    (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F] :
    SimplicialObject.Truncated C n ⥤ SimplicialObject C :=
  ran (SimplexCategory.Truncated.inclusion n).op

/--
Definition of `sk` / `sk` 的定义

English:
abbreviation sk
  signature: (n : Nat) [forall (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
  body: truncation n ⋙ Truncated.sk n

中文:
缩写 sk
  签名: (n : 自然数) [对任意 (F : (单纯形范畴.Truncated n)ᵒᵖ ⥤ C),
  定义体: truncation n ⋙ Truncated.sk n

Depends on / 依赖: Truncated, Truncated.sk, truncation
-/
abbrev sk (n : Nat) [forall (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
    (SimplexCategory.Truncated.inclusion n).op.HasLeftKanExtension F] :
    SimplicialObject C ⥤ SimplicialObject C := truncation n ⋙ Truncated.sk n

/--
Definition of `cosk` / `cosk` 的定义

English:
abbreviation cosk
  signature: (n : Nat) [forall (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
  body: truncation n ⋙ Truncated.cosk n

中文:
缩写 cosk
  签名: (n : 自然数) [对任意 (F : (单纯形范畴.Truncated n)ᵒᵖ ⥤ C),
  定义体: truncation n ⋙ Truncated.cosk n

Depends on / 依赖: Truncated, Truncated.cosk, truncation
-/
abbrev cosk (n : Nat) [forall (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
    (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F] :
    SimplicialObject C ⥤ SimplicialObject C := truncation n ⋙ Truncated.cosk n

end

section adjunctions
/- When the left and right Kan extensions exist, `Truncated.sk n` and `Truncated.cosk n`
respectively define left and right adjoints to `truncation n`. -/


variable (n : Nat)
variable [forall (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
    (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F]
variable [forall (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
    (SimplexCategory.Truncated.inclusion n).op.HasLeftKanExtension F]

/--
Definition of `skAdj` / `skAdj` 的定义

English:
definition skAdj
  signature: : Truncated.sk (C := C) n ⊣ truncation n
  body: lanAdjunction _ _

中文:
定义 skAdj
  签名: : Truncated.sk (C := C) n ⊣ truncation n
  定义体: lanAdjunction _ _

Depends on / 依赖: truncation
-/
noncomputable def skAdj : Truncated.sk (C := C) n ⊣ truncation n :=
  lanAdjunction _ _

/--
Definition of `coskAdj` / `coskAdj` 的定义

English:
definition coskAdj
  signature: : truncation (C := C) n ⊣ Truncated.cosk n
  body: ranAdjunction _ _

中文:
定义 coskAdj
  签名: : truncation (C := C) n ⊣ Truncated.cosk n
  定义体: ranAdjunction _ _

Depends on / 依赖: Truncated, Truncated.cosk
-/
noncomputable def coskAdj : truncation (C := C) n ⊣ Truncated.cosk n :=
  ranAdjunction _ _

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ((sk n).obj X).IsLeftKanExtension ((skAdj n).unit.app _)
  body: by
  dsimp [sk, skAdj]
  rw [lanAdjunction_unit]
  infer_instance

中文:
实例 :
  签名: ((sk n).obj X).是LeftKanExtension ((skAdj n).unit.app _)
  定义体: by
  dsimp [sk, skAdj]
  rw [lanAdjunction_unit]
  infer_instance

Depends on / 依赖: infer_instance, lanAdjunction_unit
-/
instance : ((sk n).obj X).IsLeftKanExtension ((skAdj n).unit.app _) := by
  dsimp [sk, skAdj]
  rw [lanAdjunction_unit]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ((cosk n).obj X).IsRightKanExtension ((coskAdj n).counit.app _)
  body: by
  dsimp [cosk, coskAdj]
  rw [ranAdjunction_counit]
  infer_instance

中文:
实例 :
  签名: ((cosk n).obj X).是RightKanExtension ((coskAdj n).counit.app _)
  定义体: by
  dsimp [cosk, coskAdj]
  rw [ranAdjunction_counit]
  infer_instance

Depends on / 依赖: coskAdj, infer_instance, ranAdjunction_counit
-/
instance : ((cosk n).obj X).IsRightKanExtension ((coskAdj n).counit.app _) := by
  dsimp [cosk, coskAdj]
  rw [ranAdjunction_counit]
  infer_instance

namespace Truncated
/- When the left and right Kan extensions exist and are pointwise Kan extensions,
`skAdj n` and `coskAdj n` are respectively coreflective and reflective. -/

variable [forall (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
    (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F]
variable [forall (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
    (SimplexCategory.Truncated.inclusion n).op.HasPointwiseLeftKanExtension F]

/--
Instance `cosk_reflective` / 实例 `cosk_reflective`

English:
instance cosk_reflective
  signature: : IsIso (coskAdj (C := C) n).counit
  body: reflective' (SimplexCategory.Truncated.inclusion n).op

中文:
实例 cosk_reflective
  签名: : 是同构 (coskAdj (C := C) n).counit
  定义体: reflective' (SimplexCategory.Truncated.inclusion n).op

Depends on / 依赖: counit
-/
instance cosk_reflective : IsIso (coskAdj (C := C) n).counit :=
  reflective' (SimplexCategory.Truncated.inclusion n).op

/--
Instance `sk_coreflective` / 实例 `sk_coreflective`

English:
instance sk_coreflective
  signature: : IsIso (skAdj (C := C) n).unit
  body: coreflective' (SimplexCategory.Truncated.inclusion n).op

中文:
实例 sk_coreflective
  签名: : 是同构 (skAdj (C := C) n).unit
  定义体: coreflective' (SimplexCategory.Truncated.inclusion n).op
-/
instance sk_coreflective : IsIso (skAdj (C := C) n).unit :=
  coreflective' (SimplexCategory.Truncated.inclusion n).op

/--
Definition of `cosk.fullyFaithful` / `cosk.fullyFaithful` 的定义

English:
definition cosk.fullyFaithful
  signature: :
  body: by
  apply Adjunction.fullyFaithfulROfIsIsoCounit (coskAdj n)

中文:
定义 cosk.fullyFaithful
  签名: :
  定义体: by
  apply Adjunction.fullyFaithfulROfIsIsoCounit (coskAdj n)

Depends on / 依赖: Adjunction, Adjunction.fullyFaithfulROfIsIsoCounit, FullyFaithful, coskAdj, fullyFaithfulROfIsIsoCounit
-/
noncomputable def cosk.fullyFaithful :
    (Truncated.cosk (C := C) n).FullyFaithful := by
  apply Adjunction.fullyFaithfulROfIsIsoCounit (coskAdj n)

/--
Instance `cosk.full` / 实例 `cosk.full`

English:
instance cosk.full
  signature: : (Truncated.cosk (C := C) n).Full
  body: FullyFaithful.full (cosk.fullyFaithful _)

中文:
实例 cosk.full
  签名: : (Truncated.cosk (C := C) n).满
  定义体: FullyFaithful.full (cosk.fullyFaithful _)

Depends on / 依赖: FullyFaithful, FullyFaithful.full, cosk.fullyFaithful, fullyFaithful
-/
instance cosk.full : (Truncated.cosk (C := C) n).Full := FullyFaithful.full (cosk.fullyFaithful _)

/--
Instance `cosk.faithful` / 实例 `cosk.faithful`

English:
instance cosk.faithful
  signature: : (Truncated.cosk (C := C) n).Faithful
  body: FullyFaithful.faithful (cosk.fullyFaithful _)

中文:
实例 cosk.faithful
  签名: : (Truncated.cosk (C := C) n).忠实
  定义体: FullyFaithful.faithful (cosk.fullyFaithful _)

Depends on / 依赖: Faithful
-/
instance cosk.faithful : (Truncated.cosk (C := C) n).Faithful :=
  FullyFaithful.faithful (cosk.fullyFaithful _)

/--
Instance `coskAdj.reflective` / 实例 `coskAdj.reflective`

English:
instance coskAdj.reflective
  signature: : Reflective (Truncated.cosk (C := C) n)
  body: Reflective.mk (truncation _) (coskAdj _)

中文:
实例 coskAdj.reflective
  签名: : 反射 (Truncated.cosk (C := C) n)
  定义体: Reflective.mk (truncation _) (coskAdj _)
-/
noncomputable instance coskAdj.reflective : Reflective (Truncated.cosk (C := C) n) :=
  Reflective.mk (truncation _) (coskAdj _)

/--
Definition of `sk.fullyFaithful` / `sk.fullyFaithful` 的定义

English:
definition sk.fullyFaithful
  signature: : (Truncated.sk (C := C) n).FullyFaithful
  body: Adjunction.fullyFaithfulLOfIsIsoUnit (skAdj n)

中文:
定义 sk.fullyFaithful
  签名: : (Truncated.sk (C := C) n).满忠实
  定义体: Adjunction.fullyFaithfulLOfIsIsoUnit (skAdj n)

Depends on / 依赖: FullyFaithful
-/
noncomputable def sk.fullyFaithful : (Truncated.sk (C := C) n).FullyFaithful :=
  Adjunction.fullyFaithfulLOfIsIsoUnit (skAdj n)

/--
Instance `sk.full` / 实例 `sk.full`

English:
instance sk.full
  signature: : (Truncated.sk (C := C) n).Full
  body: FullyFaithful.full (sk.fullyFaithful _)

中文:
实例 sk.full
  签名: : (Truncated.sk (C := C) n).满
  定义体: FullyFaithful.full (sk.fullyFaithful _)

Depends on / 依赖: FullyFaithful, FullyFaithful.full, fullyFaithful, sk.fullyFaithful
-/
instance sk.full : (Truncated.sk (C := C) n).Full := FullyFaithful.full (sk.fullyFaithful _)

/--
Instance `sk.faithful` / 实例 `sk.faithful`

English:
instance sk.faithful
  signature: : (Truncated.sk (C := C) n).Faithful
  body: FullyFaithful.faithful (sk.fullyFaithful _)

中文:
实例 sk.faithful
  签名: : (Truncated.sk (C := C) n).忠实
  定义体: FullyFaithful.faithful (sk.fullyFaithful _)

Depends on / 依赖: Faithful
-/
instance sk.faithful : (Truncated.sk (C := C) n).Faithful :=
  FullyFaithful.faithful (sk.fullyFaithful _)

/--
Instance `skAdj.coreflective` / 实例 `skAdj.coreflective`

English:
instance skAdj.coreflective
  signature: : Coreflective (Truncated.sk (C := C) n)
  body: Coreflective.mk (truncation _) (skAdj _)

中文:
实例 skAdj.coreflective
  签名: : 余反射 (Truncated.sk (C := C) n)
  定义体: Coreflective.mk (truncation _) (skAdj _)
-/
noncomputable instance skAdj.coreflective : Coreflective (Truncated.sk (C := C) n) :=
  Coreflective.mk (truncation _) (skAdj _)

end Truncated

end adjunctions

variable (C)

/--
Definition of `const` / `const` 的定义

English:
abbreviation const
  signature: : C ⥤ SimplicialObject C
  body: CategoryTheory.Functor.const _

中文:
缩写 const
  签名: : C ⥤ SimplicialObject C
  定义体: CategoryTheory.Functor.const _

Depends on / 依赖: CategoryTheory, CategoryTheory.Functor.const, Functor
-/
abbrev const : C ⥤ SimplicialObject C :=
  CategoryTheory.Functor.const _

/-- The category of augmented simplicial objects, defined as a comma category. -/
@[implicit_reducible]
/--
Definition of `Augmented` / `Augmented` 的定义

English:
definition Augmented
  body: Comma (𝟭 (SimplicialObject C)) (const C)

@[simps!]

中文:
定义 Augmented
  定义体: Comma (𝟭 (SimplicialObject C)) (const C)

@[simps!]

Depends on / 依赖: SimplicialObject
-/
def Augmented :=
  Comma (𝟭 (SimplicialObject C)) (const C)

@[simps!]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (Augmented C)
  body: inferInstanceAs Category (Comma _ _)

中文:
实例 :
  签名: 范畴 (Augmented C)
  定义体: inferInstanceAs Category (Comma _ _)

Depends on / 依赖: Category
-/
instance : Category (Augmented C) :=
inferInstanceAs Category (Comma _ _)

variable {C}

namespace Augmented

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {X Y : Augmented C} (f g : X ⟶ Y) (h₁ : f.left = g.left) (h₂ : f.right = g.right)
  proof: Comma.hom_ext _ _ h₁ h₂

中文:
引理 hom_ext
  条件: {X Y : Augmented C} (f g : X ⟶ Y) (h₁ : f.left = g.left) (h₂ : f.right = g.right)
  证明: Comma.hom_ext _ _ h₁ h₂

Depends on / 依赖: Comma.hom_ext, hom_ext
-/
lemma hom_ext {X Y : Augmented C} (f g : X ⟶ Y) (h₁ : f.left = g.left) (h₂ : f.right = g.right) :
    f = g :=
  Comma.hom_ext _ _ h₁ h₂

/-- Drop the augmentation. -/
@[simps!, implicit_reducible]
/--
Definition of `drop` / `drop` 的定义

English:
definition drop
  signature: : Augmented C ⥤ SimplicialObject C
  body: Comma.fst _ _

中文:
定义 drop
  签名: : Augmented C ⥤ SimplicialObject C
  定义体: Comma.fst _ _

Depends on / 依赖: Comma.fst
-/
def drop : Augmented C ⥤ SimplicialObject C :=
  Comma.fst _ _

/-- The point of the augmentation. -/
@[simps!, implicit_reducible]
/--
Definition of `point` / `point` 的定义

English:
definition point
  signature: : Augmented C ⥤ C
  body: Comma.snd _ _

#adaptation_note

中文:
定义 point
  签名: : Augmented C ⥤ C
  定义体: Comma.snd _ _

#adaptation_note

Depends on / 依赖: Comma.snd
-/
def point : Augmented C ⥤ C :=
  Comma.snd _ _

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `w_app` / 引理 `w_app`

English:
lemma w_app
  given: {X Y : Augmented C} (f : X ⟶ Y) (n : SimplexCategoryᵒᵖ)
  proof: congr_app f.w n

中文:
引理 w_app
  条件: {X Y : Augmented C} (f : X ⟶ Y) (n : SimplexCategoryᵒᵖ)
  证明: congr_app f.w n

Depends on / 依赖: congr_app
-/
lemma w_app {X Y : Augmented C} (f : X ⟶ Y) (n : SimplexCategoryᵒᵖ) :
    dsimp% f.left.app n ≫ Y.hom.app n = X.hom.app n ≫ f.right :=
  congr_app f.w n

set_option backward.isDefEq.respectTransparency false in
/-- The functor from augmented objects to arrows. -/
@[simps]
/--
Definition of `toArrow` / `toArrow` 的定义

English:
definition toArrow
  signature: : Augmented C ⥤ Arrow C where
  body: { left := drop.obj X _⦋0⦌
      right := point.obj X
      hom := X.hom.app _ }
  map η :=
    { left := (drop.map η).app _
      right := point.map η
      w := by simp [w_app] }

#adaptation_note

中文:
定义 toArrow
  签名: : Augmented C ⥤ 箭头 C where
  定义体: { left := drop.obj X _⦋0⦌
      right := point.obj X
      hom := X.hom.app _ }
  map η :=
    { left := (drop.map η).app _
      right := point.map η
      w := by simp [w_app] }

#adaptation_note

Depends on / 依赖: X.hom.app, drop.map, drop.obj, point.map, point.obj, w_app
-/
def toArrow : Augmented C ⥤ Arrow C where
  obj X :=
    { left := drop.obj X _⦋0⦌
      right := point.obj X
      hom := X.hom.app _ }
  map η :=
    { left := (drop.map η).app _
      right := point.map η
      w := by simp [w_app] }

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The compatibility of a morphism with the augmentation, on 0-simplices -/
@[reassoc]
/--
theorem `w₀` / 定理 `w₀`

English:
theorem w₀
  given: {X Y : Augmented C} (f : X ⟶ Y)
  proof: congr_app f.w (op ⦋0⦌)

中文:
定理 w₀
  条件: {X Y : Augmented C} (f : X ⟶ Y)
  证明: congr_app f.w (op ⦋0⦌)

Depends on / 依赖: congr_app
-/
theorem w₀ {X Y : Augmented C} (f : X ⟶ Y) :
    dsimp% (Augmented.drop.map f).app (op ⦋0⦌) ≫ Y.hom.app (op ⦋0⦌) =
      X.hom.app (op ⦋0⦌) ≫ Augmented.point.map f :=
  congr_app f.w (op ⦋0⦌)

variable (C)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Functor composition induces a functor on augmented simplicial objects. -/
@[simp]
/--
Definition of `whiskeringObj` / `whiskeringObj` 的定义

English:
definition whiskeringObj
  signature: (D : Type*) [Category* D] (F : C ⥤ D)
  body: { left := ((whiskering _ _).obj F).obj (drop.obj X)
      right := F.obj (point.obj X)
      hom := whiskerRight X.hom F ≫ (Functor.constComp _ _ _).hom }
  map η :=
    { left := whiskerRight η.left _
      right := F.map η.right
      w := by ext; simp [← Functor.map_comp, w_app] }

中文:
定义 whiskeringObj
  签名: (D : 类型) [范畴* D] (F : C ⥤ D)
  定义体: { left := ((whiskering _ _).obj F).obj (drop.obj X)
      right := F.obj (point.obj X)
      hom := whiskerRight X.hom F ≫ (Functor.constComp _ _ _).hom }
  map η :=
    { left := whiskerRight η.left _
      right := F.map η.right
      w := by ext; simp [← Functor.map_comp, w_app] }

Depends on / 依赖: F.map, F.obj, Functor, Functor.constComp, Functor.map_comp, X.hom, constComp, drop.obj, map_comp, point.obj, w_app, whiskerRight, whiskering
-/
def whiskeringObj (D : Type*) [Category* D] (F : C ⥤ D) : Augmented C ⥤ Augmented D where
  obj X :=
    { left := ((whiskering _ _).obj F).obj (drop.obj X)
      right := F.obj (point.obj X)
      hom := whiskerRight X.hom F ≫ (Functor.constComp _ _ _).hom }
  map η :=
    { left := whiskerRight η.left _
      right := F.map η.right
      w := by ext; simp [← Functor.map_comp, w_app] }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Functor composition induces a functor on augmented simplicial objects. -/
@[simps]
/--
Definition of `whiskering` / `whiskering` 的定义

English:
definition whiskering
  signature: (D : Type u') [Category.{v'} D]
  body: whiskeringObj _ _
  map η :=
    { app := fun A =>
        { left := whiskerLeft _ η
          right := η.app _
          w := by
            ext n
            dsimp
            rw [Category.comp_id]; rw [Category.comp_id]; rw [η.naturality] } }
  map_comp := fun _ _ => by ext <;> rfl

中文:
定义 whiskering
  签名: (D : 类型u') [范畴.{v'} D]
  定义体: whiskeringObj _ _
  map η :=
    { app := fun A =>
        { left := whiskerLeft _ η
          right := η.app _
          w := by
            ext n
            dsimp
            rw [Category.comp_id]; rw [Category.comp_id]; rw [η.naturality] } }
  map_comp := fun _ _ => by ext <;> rfl

Depends on / 依赖: whiskeringObj
-/
def whiskering (D : Type u') [Category.{v'} D] : (C ⥤ D) ⥤ Augmented C ⥤ Augmented D where
  obj := whiskeringObj _ _
  map η :=
    { app := fun A =>
        { left := whiskerLeft _ η
          right := η.app _
          w := by
            ext n
            dsimp
            rw [Category.comp_id]; rw [Category.comp_id]; rw [η.naturality] } }
  map_comp := fun _ _ => by ext <;> rfl

variable {C}

/-- The constant augmented simplicial object functor. -/
@[simps]
/--
Definition of `const` / `const` 的定义

English:
definition const
  signature: : C ⥤ Augmented C where
  body: { left := (SimplicialObject.const C).obj X
      right := X
      hom := 𝟙 _ }
  map f :=
    { left := (SimplicialObject.const C).map f
      right := f }

中文:
定义 const
  签名: : C ⥤ Augmented C where
  定义体: { left := (SimplicialObject.const C).obj X
      right := X
      hom := 𝟙 _ }
  map f :=
    { left := (SimplicialObject.const C).map f
      right := f }

Depends on / 依赖: SimplicialObject, SimplicialObject.const
-/
def const : C ⥤ Augmented C where
  obj X :=
    { left := (SimplicialObject.const C).obj X
      right := X
      hom := 𝟙 _ }
  map f :=
    { left := (SimplicialObject.const C).map f
      right := f }

end Augmented

set_option backward.defeqAttrib.useBackward true in
/-- Augment a simplicial object with an object. -/
@[simps]
/--
Definition of `augment` / `augment` 的定义

English:
definition augment
  signature: (X : SimplicialObject C) (X₀ : C) (f : X _⦋0⦌ ⟶ X₀)
  body: X
  right := X₀
  hom :=
    { app := fun _ => X.map (SimplexCategory.const _ _ 0).op ≫ f
      naturality := by
        intro i j g
        dsimp
        rw [← g.op_unop]
        simpa only [← X.map_comp, ← Category.assoc, Category.comp_id, ← op_comp] using w _ _ _ }

中文:
定义 augment
  签名: (X : SimplicialObject C) (X₀ : C) (f : X _⦋0⦌ ⟶ X₀)
  定义体: X
  right := X₀
  hom :=
    { app := fun _ => X.map (SimplexCategory.const _ _ 0).op ≫ f
      naturality := by
        intro i j g
        dsimp
        rw [← g.op_unop]
        simpa only [← X.map_comp, ← Category.assoc, Category.comp_id, ← op_comp] using w _ _ _ }
-/
def augment (X : SimplicialObject C) (X₀ : C) (f : X _⦋0⦌ ⟶ X₀)
    (w : forall (i : SimplexCategory) (g₁ g₂ : ⦋0⦌ ⟶ i),
      X.map g₁.op ≫ f = X.map g₂.op ≫ f) :
    SimplicialObject.Augmented C where
  left := X
  right := X₀
  hom :=
    { app := fun _ => X.map (SimplexCategory.const _ _ 0).op ≫ f
      naturality := by
        intro i j g
        dsimp
        rw [← g.op_unop]
        simpa only [← X.map_comp, ← Category.assoc, Category.comp_id, ← op_comp] using w _ _ _ }

-- Not `@[simp]` since `simp` can prove this.
set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `augment_hom_zero` / 定理 `augment_hom_zero`

English:
theorem augment_hom_zero
  given: (X : SimplicialObject C) (X₀ : C) (f : X _⦋0⦌ ⟶ X₀) (w)
  proof: by simp

中文:
定理 augment_hom_zero
  条件: (X : SimplicialObject C) (X₀ : C) (f : X _⦋0⦌ ⟶ X₀) (w)
  证明: by simp
-/
theorem augment_hom_zero (X : SimplicialObject C) (X₀ : C) (f : X _⦋0⦌ ⟶ X₀) (w) :
    (X.augment X₀ f w).hom.app (op ⦋0⦌) = f := by simp

set_option backward.defeqAttrib.useBackward true in
/-- The augmented simplicial object that is deduced from a simplicial object and
a terminal object. -/
@[simps!]
/--
Definition of `augmentOfIsTerminal` / `augmentOfIsTerminal` 的定义

English:
definition augmentOfIsTerminal
  signature: (X : SimplicialObject C) {T : C} (hT : IsTerminal T)
  body: X
  right := T
  hom := { app _ := hT.from _ }

中文:
定义 augmentOfIsTerminal
  签名: (X : SimplicialObject C) {T : C} (hT : 是终止 T)
  定义体: X
  right := T
  hom := { app _ := hT.from _ }

Depends on / 依赖: split_ifs
-/
def augmentOfIsTerminal (X : SimplicialObject C) {T : C} (hT : IsTerminal T) :
    Augmented C where
  left := X
  right := T
  hom := { app _ := hT.from _ }

end SimplicialObject

/--
Definition of `CosimplicialObject` / `CosimplicialObject` 的定义

English:
definition CosimplicialObject
  body: SimplexCategory ⥤ C

中文:
定义 CosimplicialObject
  定义体: SimplexCategory ⥤ C

Depends on / 依赖: SimplexCategory, split_ifs
-/
def CosimplicialObject :=
  SimplexCategory ⥤ C

namespace CosimplicialObject

@[simps!]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (CosimplicialObject C)
  body: by
  dsimp only [CosimplicialObject]
  infer_instance

中文:
实例 :
  签名: 范畴 (CosimplicialObject C)
  定义体: by
  dsimp only [CosimplicialObject]
  infer_instance

Depends on / 依赖: CosimplicialObject, infer_instance
-/
instance : Category (CosimplicialObject C) := by
  dsimp only [CosimplicialObject]
  infer_instance

/-- `X ^⦋n⦌` denotes the `n`th-term of the cosimplicial object X -/
scoped[Simplicial]
  notation3:1000 X " ^⦋" n "⦌" =>
    (X : CategoryTheory.CosimplicialObject _).obj (SimplexCategory.mk n)

set_option backward.isDefEq.respectTransparency false in
instance {J : Type v} [SmallCategory J] [HasLimitsOfShape J C] :
    HasLimitsOfShape J (CosimplicialObject C) := by
  dsimp [CosimplicialObject]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasLimits
  signature: C] : HasLimits (CosimplicialObject C)
  body: ⟨inferInstance⟩

中文:
实例 [有极限
  签名: C] : 有极限 (CosimplicialObject C)
  定义体: ⟨inferInstance⟩
-/
instance [HasLimits C] : HasLimits (CosimplicialObject C) :=
  ⟨inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
instance {J : Type v} [SmallCategory J] [HasColimitsOfShape J C] :
    HasColimitsOfShape J (CosimplicialObject C) := by
  dsimp [CosimplicialObject]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasColimits
  signature: C] : HasColimits (CosimplicialObject C)
  body: ⟨inferInstance⟩

中文:
实例 [有余极限
  签名: C] : 有余极限 (CosimplicialObject C)
  定义体: ⟨inferInstance⟩
-/
instance [HasColimits C] : HasColimits (CosimplicialObject C) :=
  ⟨inferInstance⟩

variable {C}

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  statement: {X Y : CosimplicialObject C} (f g : X ⟶ Y)
  proof: NatTrans.ext (by ext; apply h)

中文:
引理 hom_ext
  结论: {X Y : CosimplicialObject C} (f g : X ⟶ Y)
  证明: NatTrans.ext (by ext; apply h)

Depends on / 依赖: NatTrans, NatTrans.ext
-/
lemma hom_ext {X Y : CosimplicialObject C} (f g : X ⟶ Y)
    (h : forall (n : SimplexCategory), f.app n = g.app n) : f = g :=
  NatTrans.ext (by ext; apply h)

variable (X : CosimplicialObject C)

open Simplicial

/--
Definition of `δ` / `δ` 的定义

English:
definition δ
  signature: {n} (i : Fin (n + 2))
  body: X.map (SimplexCategory.δ i)

中文:
定义 δ
  签名: {n} (i : 有限集 (n + 2))
  定义体: X.map (SimplexCategory.δ i)

Depends on / 依赖: SimplexCategory, X.map
-/
def δ {n} (i : Fin (n + 2)) : X ^⦋n⦌ ⟶ X ^⦋n + 1⦌ :=
  X.map (SimplexCategory.δ i)

/--
Definition of `σ` / `σ` 的定义

English:
definition σ
  signature: {n} (i : Fin (n + 1))
  body: X.map (SimplexCategory.σ i)

中文:
定义 σ
  签名: {n} (i : 有限集 (n + 1))
  定义体: X.map (SimplexCategory.σ i)

Depends on / 依赖: SimplexCategory, X.map
-/
def σ {n} (i : Fin (n + 1)) : X ^⦋n + 1⦌ ⟶ X ^⦋n⦌ :=
  X.map (SimplexCategory.σ i)

/--
Definition of `eqToIso` / `eqToIso` 的定义

English:
definition eqToIso
  signature: {n m : Nat} (h : n = m)
  body: X.mapIso (CategoryTheory.eqToIso (by rw [h]))

中文:
定义 eqToIso
  签名: {n m : 自然数} (h : n = m)
  定义体: X.mapIso (CategoryTheory.eqToIso (by rw [h]))

Depends on / 依赖: CategoryTheory, CategoryTheory.eqToIso, X.mapIso, eqToIso, mapIso
-/
def eqToIso {n m : Nat} (h : n = m) : X ^⦋n⦌ ≅ X ^⦋m⦌ :=
  X.mapIso (CategoryTheory.eqToIso (by rw [h]))

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `eqToIso_refl` / 定理 `eqToIso_refl`

English:
theorem eqToIso_refl
  given: {n : Nat} (h : n = n)
  statement: X.eqToIso h = Iso.refl _
  proof: by
  simp [eqToIso]

中文:
定理 eqToIso_refl
  条件: {n : 自然数} (h : n = n)
  结论: X.eqToIso h = 同构.refl _
  证明: by
  simp [eqToIso]

Depends on / 依赖: eqToIso
-/
theorem eqToIso_refl {n : Nat} (h : n = n) : X.eqToIso h = Iso.refl _ := by
  simp [eqToIso]

/-- The generic case of the first cosimplicial identity -/
@[reassoc]
/--
theorem `δ_comp_δ` / 定理 `δ_comp_δ`

English:
theorem δ_comp_δ
  given: {n} {i j : Fin (n + 2)} (H : i <= j)
  proof: by
  dsimp [δ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_δ H]

@[reassoc]

中文:
定理 δ_comp_δ
  条件: {n} {i j : 有限集 (n + 2)} (H : i <= j)
  证明: by
  dsimp [δ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_δ H]

@[reassoc]

Depends on / 依赖: SimplexCategory, X.map_comp, map_comp
-/
theorem δ_comp_δ {n} {i j : Fin (n + 2)} (H : i <= j) :
    X.δ i ≫ X.δ j.succ = X.δ j ≫ X.δ (Fin.castSucc i) := by
  dsimp [δ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_δ H]

@[reassoc]
/--
theorem `δ_comp_δ'` / 定理 `δ_comp_δ'`

English:
theorem δ_comp_δ'
  given: {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : Fin.castSucc i < j)
  proof: by
  dsimp [δ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_δ' H]

@[reassoc]

中文:
定理 δ_comp_δ'
  条件: {n} {i : 有限集 (n + 2)} {j : 有限集 (n + 3)} (H : 有限集.castSucc i < j)
  证明: by
  dsimp [δ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_δ' H]

@[reassoc]

Depends on / 依赖: SimplexCategory, X.map_comp, map_comp
-/
theorem δ_comp_δ' {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : Fin.castSucc i < j) :
    X.δ i ≫ X.δ j =
      X.δ (j.pred H.ne_zero) ≫
        X.δ (Fin.castSucc i) := by
  dsimp [δ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_δ' H]

@[reassoc]
/--
theorem `δ_comp_δ''` / 定理 `δ_comp_δ''`

English:
theorem δ_comp_δ''
  given: {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : i <= Fin.castSucc j)
  proof: by
  dsimp [δ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_δ'' H]

中文:
定理 δ_comp_δ''
  条件: {n} {i : 有限集 (n + 3)} {j : 有限集 (n + 2)} (H : i <= 有限集.castSucc j)
  证明: by
  dsimp [δ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_δ'' H]

Depends on / 依赖: SimplexCategory, X.map_comp, map_comp
-/
theorem δ_comp_δ'' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : i <= Fin.castSucc j) :
    X.δ (i.castLT (Nat.lt_of_le_of_lt (Fin.le_iff_val_le_val.mp H) j.is_lt)) ≫ X.δ j.succ =
      X.δ j ≫ X.δ i := by
  dsimp [δ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_δ'' H]

/-- The special case of the first cosimplicial identity -/
@[reassoc]
/--
theorem `δ_comp_δ_self` / 定理 `δ_comp_δ_self`

English:
theorem δ_comp_δ_self
  given: {n} {i : Fin (n + 2)}
  proof: by
  dsimp [δ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_δ_self]

@[reassoc]

中文:
定理 δ_comp_δ_self
  条件: {n} {i : 有限集 (n + 2)}
  证明: by
  dsimp [δ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_δ_self]

@[reassoc]

Depends on / 依赖: SimplexCategory, X.map_comp, map_comp
-/
theorem δ_comp_δ_self {n} {i : Fin (n + 2)} :
    X.δ i ≫ X.δ (Fin.castSucc i) = X.δ i ≫ X.δ i.succ := by
  dsimp [δ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_δ_self]

@[reassoc]
/--
theorem `δ_comp_δ_self'` / 定理 `δ_comp_δ_self'`

English:
theorem δ_comp_δ_self'
  given: {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : j = Fin.castSucc i)
  proof: by
  subst H
  rw [δ_comp_δ_self]

中文:
定理 δ_comp_δ_self'
  条件: {n} {i : 有限集 (n + 2)} {j : 有限集 (n + 3)} (H : j = 有限集.castSucc i)
  证明: by
  subst H
  rw [δ_comp_δ_self]
-/
theorem δ_comp_δ_self' {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : j = Fin.castSucc i) :
    X.δ i ≫ X.δ j = X.δ i ≫ X.δ i.succ := by
  subst H
  rw [δ_comp_δ_self]

/-- The second cosimplicial identity -/
@[reassoc]
/--
theorem `δ_comp_σ_of_le` / 定理 `δ_comp_σ_of_le`

English:
theorem δ_comp_σ_of_le
  given: {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i <= Fin.castSucc j)
  proof: by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_of_le H]

中文:
定理 δ_comp_σ_of_le
  条件: {n} {i : 有限集 (n + 2)} {j : 有限集 (n + 1)} (H : i <= 有限集.castSucc j)
  证明: by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_of_le H]

Depends on / 依赖: SimplexCategory, X.map_comp, map_comp
-/
theorem δ_comp_σ_of_le {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i <= Fin.castSucc j) :
    X.δ (Fin.castSucc i) ≫ X.σ j.succ = X.σ j ≫ X.δ i := by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_of_le H]

/-- The first part of the third cosimplicial identity -/
@[reassoc]
/--
theorem `δ_comp_σ_self` / 定理 `δ_comp_σ_self`

English:
theorem δ_comp_σ_self
  given: {n} {i : Fin (n + 1)}
  statement: X.δ (Fin.castSucc i) ≫ X.σ i = 𝟙 _
  proof: by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_self, X.map_id]

@[reassoc]

中文:
定理 δ_comp_σ_self
  条件: {n} {i : 有限集 (n + 1)}
  结论: X.δ (有限集.castSucc i) ≫ X.σ i = 𝟙 _
  证明: by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_self, X.map_id]

@[reassoc]

Depends on / 依赖: SimplexCategory, X.map_comp, X.map_id, map_comp, map_id
-/
theorem δ_comp_σ_self {n} {i : Fin (n + 1)} : X.δ (Fin.castSucc i) ≫ X.σ i = 𝟙 _ := by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_self, X.map_id]

@[reassoc]
/--
theorem `δ_comp_σ_self'` / 定理 `δ_comp_σ_self'`

English:
theorem δ_comp_σ_self'
  given: {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = Fin.castSucc i)
  proof: by
  subst H
  rw [δ_comp_σ_self]

中文:
定理 δ_comp_σ_self'
  条件: {n} {j : 有限集 (n + 2)} {i : 有限集 (n + 1)} (H : j = 有限集.castSucc i)
  证明: by
  subst H
  rw [δ_comp_σ_self]
-/
theorem δ_comp_σ_self' {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = Fin.castSucc i) :
    X.δ j ≫ X.σ i = 𝟙 _ := by
  subst H
  rw [δ_comp_σ_self]

/-- The second part of the third cosimplicial identity -/
@[reassoc]
/--
theorem `δ_comp_σ_succ` / 定理 `δ_comp_σ_succ`

English:
theorem δ_comp_σ_succ
  given: {n} {i : Fin (n + 1)}
  statement: X.δ i.succ ≫ X.σ i = 𝟙 _
  proof: by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_succ, X.map_id]

@[reassoc]

中文:
定理 δ_comp_σ_succ
  条件: {n} {i : 有限集 (n + 1)}
  结论: X.δ i.succ ≫ X.σ i = 𝟙 _
  证明: by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_succ, X.map_id]

@[reassoc]

Depends on / 依赖: SimplexCategory, X.map_comp, X.map_id, map_comp, map_id
-/
theorem δ_comp_σ_succ {n} {i : Fin (n + 1)} : X.δ i.succ ≫ X.σ i = 𝟙 _ := by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_succ, X.map_id]

@[reassoc]
/--
theorem `δ_comp_σ_succ'` / 定理 `δ_comp_σ_succ'`

English:
theorem δ_comp_σ_succ'
  given: {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = i.succ)
  proof: by
  subst H
  rw [δ_comp_σ_succ]

中文:
定理 δ_comp_σ_succ'
  条件: {n} {j : 有限集 (n + 2)} {i : 有限集 (n + 1)} (H : j = i.succ)
  证明: by
  subst H
  rw [δ_comp_σ_succ]
-/
theorem δ_comp_σ_succ' {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = i.succ) :
    X.δ j ≫ X.σ i = 𝟙 _ := by
  subst H
  rw [δ_comp_σ_succ]

/-- The fourth cosimplicial identity -/
@[reassoc]
/--
theorem `δ_comp_σ_of_gt` / 定理 `δ_comp_σ_of_gt`

English:
theorem δ_comp_σ_of_gt
  given: {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : Fin.castSucc j < i)
  proof: by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_of_gt H]

@[reassoc]

中文:
定理 δ_comp_σ_of_gt
  条件: {n} {i : 有限集 (n + 2)} {j : 有限集 (n + 1)} (H : 有限集.castSucc j < i)
  证明: by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_of_gt H]

@[reassoc]

Depends on / 依赖: SimplexCategory, X.map_comp, map_comp
-/
theorem δ_comp_σ_of_gt {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : Fin.castSucc j < i) :
    X.δ i.succ ≫ X.σ (Fin.castSucc j) = X.σ j ≫ X.δ i := by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_of_gt H]

@[reassoc]
/--
theorem `δ_comp_σ_of_gt'` / 定理 `δ_comp_σ_of_gt'`

English:
theorem δ_comp_σ_of_gt'
  given: {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : j.succ < i)
  proof: by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_of_gt' H]

中文:
定理 δ_comp_σ_of_gt'
  条件: {n} {i : 有限集 (n + 3)} {j : 有限集 (n + 2)} (H : j.succ < i)
  证明: by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_of_gt' H]

Depends on / 依赖: SimplexCategory, X.map_comp, map_comp
-/
theorem δ_comp_σ_of_gt' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : j.succ < i) :
    X.δ i ≫ X.σ j =
      X.σ (j.castLT ((add_lt_add_iff_right 1).mp (lt_of_lt_of_le H i.is_le))) ≫
        X.δ (i.pred H.ne_zero) := by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_of_gt' H]

/-- The fifth cosimplicial identity -/
@[reassoc]
/--
theorem `σ_comp_σ` / 定理 `σ_comp_σ`

English:
theorem σ_comp_σ
  given: {n} {i j : Fin (n + 1)} (H : i <= j)
  proof: by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.σ_comp_σ H]

@[reassoc (attr := simp)]

中文:
定理 σ_comp_σ
  条件: {n} {i j : 有限集 (n + 1)} (H : i <= j)
  证明: by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.σ_comp_σ H]

@[reassoc (attr := simp)]

Depends on / 依赖: SimplexCategory, X.map_comp, map_comp
-/
theorem σ_comp_σ {n} {i j : Fin (n + 1)} (H : i <= j) :
    X.σ (Fin.castSucc i) ≫ X.σ j = X.σ j.succ ≫ X.σ i := by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.σ_comp_σ H]

@[reassoc (attr := simp)]
/--
theorem `δ_naturality` / 定理 `δ_naturality`

English:
theorem δ_naturality
  given: {X' X : CosimplicialObject C} (f : X ⟶ X') {n : Nat} (i : Fin (n + 2))
  proof: f.naturality _

@[reassoc (attr := simp)]

中文:
定理 δ_naturality
  条件: {X' X : CosimplicialObject C} (f : X ⟶ X') {n : 自然数} (i : 有限集 (n + 2))
  证明: f.naturality _

@[reassoc (attr := simp)]

Depends on / 依赖: f.naturality, naturality
-/
theorem δ_naturality {X' X : CosimplicialObject C} (f : X ⟶ X') {n : Nat} (i : Fin (n + 2)) :
    X.δ i ≫ f.app ⦋n + 1⦌ = f.app ⦋n⦌ ≫ X'.δ i :=
  f.naturality _

@[reassoc (attr := simp)]
/--
theorem `σ_naturality` / 定理 `σ_naturality`

English:
theorem σ_naturality
  given: {X' X : CosimplicialObject C} (f : X ⟶ X') {n : Nat} (i : Fin (n + 1))
  proof: f.naturality _

中文:
定理 σ_naturality
  条件: {X' X : CosimplicialObject C} (f : X ⟶ X') {n : 自然数} (i : 有限集 (n + 1))
  证明: f.naturality _

Depends on / 依赖: f.naturality, naturality
-/
theorem σ_naturality {X' X : CosimplicialObject C} (f : X ⟶ X') {n : Nat} (i : Fin (n + 1)) :
    X.σ i ≫ f.app ⦋n⦌ = f.app ⦋n + 1⦌ ≫ X'.σ i :=
  f.naturality _

variable (C)

/-- Functor composition induces a functor on cosimplicial objects. -/
@[simps!]
/--
Definition of `whiskering` / `whiskering` 的定义

English:
definition whiskering
  signature: (D : Type*) [Category* D]
  body: whiskeringRight _ _ _

中文:
定义 whiskering
  签名: (D : 类型) [范畴* D]
  定义体: whiskeringRight _ _ _

Depends on / 依赖: whiskeringRight
-/
def whiskering (D : Type*) [Category* D] : (C ⥤ D) ⥤ CosimplicialObject C ⥤ CosimplicialObject D :=
  whiskeringRight _ _ _

/--
Definition of `Truncated` / `Truncated` 的定义

English:
definition Truncated
  signature: (n : Nat)
  body: SimplexCategory.Truncated n ⥤ C
deriving Category

中文:
定义 Truncated
  签名: (n : 自然数)
  定义体: SimplexCategory.Truncated n ⥤ C
deriving Category

Depends on / 依赖: SimplexCategory, SimplexCategory.Truncated, Truncated
-/
def Truncated (n : Nat) :=
  SimplexCategory.Truncated n ⥤ C
deriving Category

variable {C}

namespace Truncated

set_option backward.isDefEq.respectTransparency false in
instance {n} {J : Type v} [SmallCategory J] [HasLimitsOfShape J C] :
    HasLimitsOfShape J (CosimplicialObject.Truncated C n) := by
  dsimp [Truncated]
  infer_instance

instance {n} [HasLimits C] : HasLimits (CosimplicialObject.Truncated C n) :=
  ⟨inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
instance {n} {J : Type v} [SmallCategory J] [HasColimitsOfShape J C] :
    HasColimitsOfShape J (CosimplicialObject.Truncated C n) := by
  dsimp [Truncated]
  infer_instance

instance {n} [HasColimits C] : HasColimits (CosimplicialObject.Truncated C n) :=
  ⟨inferInstance⟩

variable (C) in
/-- Functor composition induces a functor on truncated cosimplicial objects. -/
@[simps!]
/--
Definition of `whiskering` / `whiskering` 的定义

English:
definition whiskering
  signature: {n} (D : Type*) [Category* D]
  body: whiskeringRight _ _ _

中文:
定义 whiskering
  签名: {n} (D : 类型) [范畴* D]
  定义体: whiskeringRight _ _ _

Depends on / 依赖: whiskeringRight
-/
def whiskering {n} (D : Type*) [Category* D] : (C ⥤ D) ⥤ Truncated C n ⥤ Truncated D n :=
  whiskeringRight _ _ _

open Mathlib.Tactic (subscriptTerm) in
/-- For `X : Truncated C n` and `m ≤ n`, `X ^⦋m⦌ₙ` is the `m`-th term of X. The
proof `p : m ≤ n` can also be provided using the syntax `X ^⦋m, p⦌ₙ`. -/
scoped syntax:max (name := mkNotation)
  term " ^⦋" term ("," term)? "⦌" noWs subscriptTerm : term

open scoped SimplexCategory.Truncated in
scoped macro_rules
  | `($X:term ^⦋$m:term⦌$n:subscript) =>
    `(($X : CategoryTheory.CosimplicialObject.Truncated _ $n).obj
⟨SimplexCategory.mk m, by first | get_elem_tactic |
      fail "Failed to prove truncation property. Try writing `X ^⦋m, by ...⦌ₙ`."⟩)
  | `($X:term ^⦋$m:term, $p:term⦌$n:subscript) =>
    `(($X : CategoryTheory.CosimplicialObject.Truncated _ $n).obj
⟨SimplexCategory.mk m, p⟩)

variable (C) in
/--
Definition of `trunc` / `trunc` 的定义

English:
definition trunc
  signature: (n m : Nat) (h : m <= n := by lia)
  body: (whiskeringLeft _ _ _).obj SimplexCategory.Truncated.incl m n

中文:
定义 trunc
  签名: (n m : 自然数) (h : m <= n := by lia)
  定义体: (whiskeringLeft _ _ _).obj SimplexCategory.Truncated.incl m n

Depends on / 依赖: SimplexCategory, SimplexCategory.Truncated.incl, Truncated, whiskeringLeft
-/
def trunc (n m : Nat) (h : m <= n := by lia) : Truncated C n ⥤ Truncated C m :=
(whiskeringLeft _ _ _).obj SimplexCategory.Truncated.incl m n

end Truncated

section Truncation

/--
Definition of `truncation` / `truncation` 的定义

English:
definition truncation
  signature: (n : Nat)
  body: (whiskeringLeft _ _ _).obj (SimplexCategory.Truncated.inclusion n)

中文:
定义 truncation
  签名: (n : 自然数)
  定义体: (whiskeringLeft _ _ _).obj (SimplexCategory.Truncated.inclusion n)

Depends on / 依赖: SimplexCategory, SimplexCategory.Truncated.inclusion, Truncated, inclusion, whiskeringLeft
-/
def truncation (n : Nat) : CosimplicialObject C ⥤ CosimplicialObject.Truncated C n :=
  (whiskeringLeft _ _ _).obj (SimplexCategory.Truncated.inclusion n)

/--
Definition of `truncationCompTrunc` / `truncationCompTrunc` 的定义

English:
definition truncationCompTrunc
  signature: {n m : Nat} (h : m <= n)
  body: Iso.refl _

中文:
定义 truncationCompTrunc
  签名: {n m : 自然数} (h : m <= n)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def truncationCompTrunc {n m : Nat} (h : m <= n) :
    truncation n ⋙ Truncated.trunc C n m ≅ truncation m :=
  Iso.refl _

end Truncation

variable (C)

/--
Definition of `const` / `const` 的定义

English:
abbreviation const
  signature: : C ⥤ CosimplicialObject C
  body: CategoryTheory.Functor.const _

中文:
缩写 const
  签名: : C ⥤ CosimplicialObject C
  定义体: CategoryTheory.Functor.const _

Depends on / 依赖: CategoryTheory, CategoryTheory.Functor.const, Functor
-/
abbrev const : C ⥤ CosimplicialObject C :=
  CategoryTheory.Functor.const _

/--
Definition of `Augmented` / `Augmented` 的定义

English:
definition Augmented
  body: Comma (const C) (𝟭 (CosimplicialObject C))

@[simps!]

中文:
定义 Augmented
  定义体: Comma (const C) (𝟭 (CosimplicialObject C))

@[simps!]

Depends on / 依赖: CosimplicialObject
-/
def Augmented :=
  Comma (const C) (𝟭 (CosimplicialObject C))

@[simps!]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (Augmented C)
  body: inferInstanceAs Category (Comma _ _)

中文:
实例 :
  签名: 范畴 (Augmented C)
  定义体: inferInstanceAs Category (Comma _ _)

Depends on / 依赖: Category
-/
instance : Category (Augmented C) :=
inferInstanceAs Category (Comma _ _)

variable {C}

namespace Augmented

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {X Y : Augmented C} (f g : X ⟶ Y) (h₁ : f.left = g.left) (h₂ : f.right = g.right)
  proof: Comma.hom_ext _ _ h₁ h₂

中文:
引理 hom_ext
  条件: {X Y : Augmented C} (f g : X ⟶ Y) (h₁ : f.left = g.left) (h₂ : f.right = g.right)
  证明: Comma.hom_ext _ _ h₁ h₂

Depends on / 依赖: Comma.hom_ext, hom_ext
-/
lemma hom_ext {X Y : Augmented C} (f g : X ⟶ Y) (h₁ : f.left = g.left) (h₂ : f.right = g.right) :
    f = g :=
  Comma.hom_ext _ _ h₁ h₂

/-- Drop the augmentation. -/
@[simps!]
/--
Definition of `drop` / `drop` 的定义

English:
definition drop
  signature: : Augmented C ⥤ CosimplicialObject C
  body: Comma.snd _ _

中文:
定义 drop
  签名: : Augmented C ⥤ CosimplicialObject C
  定义体: Comma.snd _ _

Depends on / 依赖: Comma.snd
-/
def drop : Augmented C ⥤ CosimplicialObject C :=
  Comma.snd _ _

/-- The point of the augmentation. -/
@[simps!]
/--
Definition of `point` / `point` 的定义

English:
definition point
  signature: : Augmented C ⥤ C
  body: Comma.fst _ _

#adaptation_note

中文:
定义 point
  签名: : Augmented C ⥤ C
  定义体: Comma.fst _ _

#adaptation_note

Depends on / 依赖: Comma.fst
-/
def point : Augmented C ⥤ C :=
  Comma.fst _ _

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `w_app` / 引理 `w_app`

English:
lemma w_app
  given: {X Y : Augmented C} {η : X ⟶ Y} {n : SimplexCategory}
  proof: NatTrans.congr_app η.w n

中文:
引理 w_app
  条件: {X Y : Augmented C} {η : X ⟶ Y} {n : 单纯形范畴}
  证明: NatTrans.congr_app η.w n

Depends on / 依赖: NatTrans, NatTrans.congr_app, congr_app
-/
lemma w_app {X Y : Augmented C} {η : X ⟶ Y} {n : SimplexCategory} :
    dsimp% η.left ≫ Y.hom.app n = X.hom.app n ≫ η.right.app n :=
  NatTrans.congr_app η.w n

set_option backward.isDefEq.respectTransparency false in
/-- The functor from augmented objects to arrows. -/
@[simps!]
/--
Definition of `toArrow` / `toArrow` 的定义

English:
definition toArrow
  signature: : Augmented C ⥤ Arrow C where
  body: { left := point.obj X
      right := (drop.obj X) ^⦋0⦌
      hom := X.hom.app _ }
  map η :=
    { left := point.map η
      right := (drop.map η).app _
      w := by simp [w_app]}

中文:
定义 toArrow
  签名: : Augmented C ⥤ 箭头 C where
  定义体: { left := point.obj X
      right := (drop.obj X) ^⦋0⦌
      hom := X.hom.app _ }
  map η :=
    { left := point.map η
      right := (drop.map η).app _
      w := by simp [w_app]}

Depends on / 依赖: X.hom.app, drop.map, drop.obj, point.map, point.obj, w_app
-/
def toArrow : Augmented C ⥤ Arrow C where
  obj X :=
    { left := point.obj X
      right := (drop.obj X) ^⦋0⦌
      hom := X.hom.app _ }
  map η :=
    { left := point.map η
      right := (drop.map η).app _
      w := by simp [w_app]}

variable (C)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Functor composition induces a functor on augmented cosimplicial objects. -/
@[simp]
/--
Definition of `whiskeringObj` / `whiskeringObj` 的定义

English:
definition whiskeringObj
  signature: (D : Type*) [Category* D] (F : C ⥤ D)
  body: { left := F.obj (point.obj X)
      right := ((whiskering _ _).obj F).obj (drop.obj X)
      hom := (Functor.constComp _ _ _).inv ≫ whiskerRight X.hom F }
  map η :=
    { left := F.map η.left
      right := whiskerRight η.right _
      w := by
        ext
        dsimp
        rw [Category.id_comp]; rw [Category.id_comp]; rw [← F.map_comp]; rw [← F.map_comp]
        simp [w_app, map_comp] }

中文:
定义 whiskeringObj
  签名: (D : 类型) [范畴* D] (F : C ⥤ D)
  定义体: { left := F.obj (point.obj X)
      right := ((whiskering _ _).obj F).obj (drop.obj X)
      hom := (Functor.constComp _ _ _).inv ≫ whiskerRight X.hom F }
  map η :=
    { left := F.map η.left
      right := whiskerRight η.right _
      w := by
        ext
        dsimp
        rw [Category.id_comp]; rw [Category.id_comp]; rw [← F.map_comp]; rw [← F.map_comp]
        simp [w_app, map_comp] }

Depends on / 依赖: Category, Category.id_comp, F.map, F.map_comp, F.obj, Functor, Functor.constComp, X.hom, constComp, drop.obj, id_comp, map_comp, point.obj, w_app, whiskerRight, whiskering
-/
def whiskeringObj (D : Type*) [Category* D] (F : C ⥤ D) : Augmented C ⥤ Augmented D where
  obj X :=
    { left := F.obj (point.obj X)
      right := ((whiskering _ _).obj F).obj (drop.obj X)
      hom := (Functor.constComp _ _ _).inv ≫ whiskerRight X.hom F }
  map η :=
    { left := F.map η.left
      right := whiskerRight η.right _
      w := by
        ext
        dsimp
        rw [Category.id_comp]; rw [Category.id_comp]; rw [← F.map_comp]; rw [← F.map_comp]
        simp [w_app, map_comp] }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Functor composition induces a functor on augmented cosimplicial objects. -/
@[simps]
/--
Definition of `whiskering` / `whiskering` 的定义

English:
definition whiskering
  signature: (D : Type u') [Category.{v'} D]
  body: whiskeringObj _ _
  map η :=
    { app := fun A =>
        { left := η.app _
          right := whiskerLeft _ η
          w := by
            ext n
            dsimp
            rw [Category.id_comp]; rw [Category.id_comp]; rw [η.naturality] }
      naturality := fun _ _ f => by ext <;> simp }

中文:
定义 whiskering
  签名: (D : 类型u') [范畴.{v'} D]
  定义体: whiskeringObj _ _
  map η :=
    { app := fun A =>
        { left := η.app _
          right := whiskerLeft _ η
          w := by
            ext n
            dsimp
            rw [Category.id_comp]; rw [Category.id_comp]; rw [η.naturality] }
      naturality := fun _ _ f => by ext <;> simp }

Depends on / 依赖: whiskeringObj
-/
def whiskering (D : Type u') [Category.{v'} D] : (C ⥤ D) ⥤ Augmented C ⥤ Augmented D where
  obj := whiskeringObj _ _
  map η :=
    { app := fun A =>
        { left := η.app _
          right := whiskerLeft _ η
          w := by
            ext n
            dsimp
            rw [Category.id_comp]; rw [Category.id_comp]; rw [η.naturality] }
      naturality := fun _ _ f => by ext <;> simp }

variable {C}

/-- The constant augmented cosimplicial object functor. -/
@[simps]
/--
Definition of `const` / `const` 的定义

English:
definition const
  signature: : C ⥤ Augmented C where
  body: { left := X
      right := (CosimplicialObject.const C).obj X
      hom := 𝟙 _ }
  map f :=
    { left := f
      right := (CosimplicialObject.const C).map f }

中文:
定义 const
  签名: : C ⥤ Augmented C where
  定义体: { left := X
      right := (CosimplicialObject.const C).obj X
      hom := 𝟙 _ }
  map f :=
    { left := f
      right := (CosimplicialObject.const C).map f }

Depends on / 依赖: CosimplicialObject, CosimplicialObject.const
-/
def const : C ⥤ Augmented C where
  obj X :=
    { left := X
      right := (CosimplicialObject.const C).obj X
      hom := 𝟙 _ }
  map f :=
    { left := f
      right := (CosimplicialObject.const C).map f }

end Augmented

open Simplicial

set_option backward.defeqAttrib.useBackward true in
/-- Augment a cosimplicial object with an object. -/
@[simps]
/--
Definition of `augment` / `augment` 的定义

English:
definition augment
  signature: (X : CosimplicialObject C) (X₀ : C) (f : X₀ ⟶ X.obj ⦋0⦌)
  body: X₀
  right := X
  hom :=
    { app := fun _ => f ≫ X.map (SimplexCategory.const _ _ 0)
      naturality := by
        intro i j g
        dsimp
        rw [Category.id_comp]; rw [Category.assoc]; rw [← X.map_comp]; rw [w] }

中文:
定义 augment
  签名: (X : CosimplicialObject C) (X₀ : C) (f : X₀ ⟶ X.obj ⦋0⦌)
  定义体: X₀
  right := X
  hom :=
    { app := fun _ => f ≫ X.map (SimplexCategory.const _ _ 0)
      naturality := by
        intro i j g
        dsimp
        rw [Category.id_comp]; rw [Category.assoc]; rw [← X.map_comp]; rw [w] }
-/
def augment (X : CosimplicialObject C) (X₀ : C) (f : X₀ ⟶ X.obj ⦋0⦌)
    (w : forall (i : SimplexCategory) (g₁ g₂ : ⦋0⦌ ⟶ i),
      f ≫ X.map g₁ = f ≫ X.map g₂) : CosimplicialObject.Augmented C where
  left := X₀
  right := X
  hom :=
    { app := fun _ => f ≫ X.map (SimplexCategory.const _ _ 0)
      naturality := by
        intro i j g
        dsimp
        rw [Category.id_comp]; rw [Category.assoc]; rw [← X.map_comp]; rw [w] }

-- Not `@[simp]` since `simp` can prove this.
set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `augment_hom_zero` / 定理 `augment_hom_zero`

English:
theorem augment_hom_zero
  given: (X : CosimplicialObject C) (X₀ : C) (f : X₀ ⟶ X.obj ⦋0⦌) (w)
  proof: by simp

中文:
定理 augment_hom_zero
  条件: (X : CosimplicialObject C) (X₀ : C) (f : X₀ ⟶ X.obj ⦋0⦌) (w)
  证明: by simp

Depends on / 依赖: Pi.smul_apply, smul_apply, smul_sum, sum_partition_boxes
-/
theorem augment_hom_zero (X : CosimplicialObject C) (X₀ : C) (f : X₀ ⟶ X.obj ⦋0⦌) (w) :
    (X.augment X₀ f w).hom.app ⦋0⦌ = f := by simp

set_option backward.defeqAttrib.useBackward true in
/-- The coaugmented cosimplicial object that is deduced from a cosimplicial object and
an initial object. -/
@[simps!]
/--
Definition of `augmentOfIsInitial` / `augmentOfIsInitial` 的定义

English:
definition augmentOfIsInitial
  signature: (X : CosimplicialObject C) {T : C} (hT : IsInitial T)
  body: X
  left := T
  hom := { app _ := hT.to _ }

中文:
定义 augmentOfIsInitial
  签名: (X : CosimplicialObject C) {T : C} (hT : IsInitial T)
  定义体: X
  left := T
  hom := { app _ := hT.to _ }
-/
def augmentOfIsInitial (X : CosimplicialObject C) {T : C} (hT : IsInitial T) :
    Augmented C where
  right := X
  left := T
  hom := { app _ := hT.to _ }

end CosimplicialObject

/-- The anti-equivalence between simplicial objects and cosimplicial objects. -/
@[simps!]
/--
Definition of `simplicialCosimplicialEquiv` / `simplicialCosimplicialEquiv` 的定义

English:
definition simplicialCosimplicialEquiv
  signature: : (SimplicialObject C)ᵒᵖ ≌ CosimplicialObject Cᵒᵖ
  body: Functor.leftOpRightOpEquiv _ _

中文:
定义 simplicialCosimplicialEquiv
  签名: : (SimplicialObject C)ᵒᵖ ≌ CosimplicialObject Cᵒᵖ
  定义体: Functor.leftOpRightOpEquiv _ _

Depends on / 依赖: Functor, Functor.leftOpRightOpEquiv, leftOpRightOpEquiv
-/
def simplicialCosimplicialEquiv : (SimplicialObject C)ᵒᵖ ≌ CosimplicialObject Cᵒᵖ :=
  Functor.leftOpRightOpEquiv _ _

/-- The anti-equivalence between cosimplicial objects and simplicial objects. -/
@[simps!]
/--
Definition of `cosimplicialSimplicialEquiv` / `cosimplicialSimplicialEquiv` 的定义

English:
definition cosimplicialSimplicialEquiv
  signature: : (CosimplicialObject C)ᵒᵖ ≌ SimplicialObject Cᵒᵖ
  body: Functor.opUnopEquiv _ _

中文:
定义 cosimplicialSimplicialEquiv
  签名: : (CosimplicialObject C)ᵒᵖ ≌ SimplicialObject Cᵒᵖ
  定义体: Functor.opUnopEquiv _ _

Depends on / 依赖: Functor, Functor.opUnopEquiv, opUnopEquiv
-/
def cosimplicialSimplicialEquiv : (CosimplicialObject C)ᵒᵖ ≌ SimplicialObject Cᵒᵖ :=
  Functor.opUnopEquiv _ _

variable {C}

/-- Construct an augmented cosimplicial object in the opposite
category from an augmented simplicial object. -/
@[simps!]
/--
Definition of `SimplicialObject.Augmented.rightOp` / `SimplicialObject.Augmented.rightOp` 的定义

English:
definition SimplicialObject.Augmented.rightOp
  signature: (X : SimplicialObject.Augmented C)
  body: Opposite.op X.right
  right := X.left.rightOp
  hom := NatTrans.rightOp X.hom

中文:
定义 SimplicialObject.Augmented.rightOp
  签名: (X : SimplicialObject.Augmented C)
  定义体: Opposite.op X.right
  right := X.left.rightOp
  hom := NatTrans.rightOp X.hom

Depends on / 依赖: Opposite, Opposite.op, X.right
-/
def SimplicialObject.Augmented.rightOp (X : SimplicialObject.Augmented C) :
    CosimplicialObject.Augmented Cᵒᵖ where
  left := Opposite.op X.right
  right := X.left.rightOp
  hom := NatTrans.rightOp X.hom

/-- Construct an augmented simplicial object from an augmented cosimplicial
object in the opposite category. -/
@[simps!]
/--
Definition of `CosimplicialObject.Augmented.leftOp` / `CosimplicialObject.Augmented.leftOp` 的定义

English:
definition CosimplicialObject.Augmented.leftOp
  signature: (X : CosimplicialObject.Augmented Cᵒᵖ)
  body: X.right.leftOp
  right := X.left.unop
  hom := NatTrans.leftOp X.hom

中文:
定义 CosimplicialObject.Augmented.leftOp
  签名: (X : CosimplicialObject.Augmented Cᵒᵖ)
  定义体: X.right.leftOp
  right := X.left.unop
  hom := NatTrans.leftOp X.hom

Depends on / 依赖: X.right.leftOp, leftOp
-/
def CosimplicialObject.Augmented.leftOp (X : CosimplicialObject.Augmented Cᵒᵖ) :
    SimplicialObject.Augmented C where
  left := X.right.leftOp
  right := X.left.unop
  hom := NatTrans.leftOp X.hom

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Converting an augmented simplicial object to an augmented cosimplicial
object and back is isomorphic to the given object. -/
@[simps!]
/--
Definition of `SimplicialObject.Augmented.rightOpLeftOpIso` / `SimplicialObject.Augmented.rightOpLeftOpIso` 的定义

English:
definition SimplicialObject.Augmented.rightOpLeftOpIso
  signature: (X : SimplicialObject.Augmented C)
  body: Comma.isoMk X.left.rightOpLeftOpIso (CategoryTheory.eqToIso <| by simp)

中文:
定义 SimplicialObject.Augmented.rightOpLeftOpIso
  签名: (X : SimplicialObject.Augmented C)
  定义体: Comma.isoMk X.left.rightOpLeftOpIso (CategoryTheory.eqToIso <| by simp)

Depends on / 依赖: CategoryTheory, CategoryTheory.eqToIso, Comma.isoMk, X.left.rightOpLeftOpIso, eqToIso, rightOpLeftOpIso
-/
def SimplicialObject.Augmented.rightOpLeftOpIso (X : SimplicialObject.Augmented C) :
    X.rightOp.leftOp ≅ X :=
  Comma.isoMk X.left.rightOpLeftOpIso (CategoryTheory.eqToIso <| by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Converting an augmented cosimplicial object to an augmented simplicial
object and back is isomorphic to the given object. -/
@[simps!]
/--
Definition of `CosimplicialObject.Augmented.leftOpRightOpIso` / `CosimplicialObject.Augmented.leftOpRightOpIso` 的定义

English:
definition CosimplicialObject.Augmented.leftOpRightOpIso
  signature: (X : CosimplicialObject.Augmented Cᵒᵖ)
  body: Comma.isoMk (CategoryTheory.eqToIso <| by simp) X.right.leftOpRightOpIso

中文:
定义 CosimplicialObject.Augmented.leftOpRightOpIso
  签名: (X : CosimplicialObject.Augmented Cᵒᵖ)
  定义体: Comma.isoMk (CategoryTheory.eqToIso <| by simp) X.right.leftOpRightOpIso

Depends on / 依赖: CategoryTheory, CategoryTheory.eqToIso, Comma.isoMk, X.right.leftOpRightOpIso, eqToIso, leftOpRightOpIso
-/
def CosimplicialObject.Augmented.leftOpRightOpIso (X : CosimplicialObject.Augmented Cᵒᵖ) :
    X.leftOp.rightOp ≅ X :=
  Comma.isoMk (CategoryTheory.eqToIso <| by simp) X.right.leftOpRightOpIso

variable (C)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A functorial version of `SimplicialObject.Augmented.rightOp`. -/
@[simps]
/--
Definition of `simplicialToCosimplicialAugmented` / `simplicialToCosimplicialAugmented` 的定义

English:
definition simplicialToCosimplicialAugmented
  signature: :
  body: X.unop.rightOp
  map f :=
    { left := f.unop.right.op
      right := NatTrans.rightOp f.unop.left
      w := by
        ext x
        dsimp
        simp_rw [← op_comp]
        congr 1
        exact (congr_app f.unop.w (op x)).symm }

中文:
定义 simplicialToCosimplicialAugmented
  签名: :
  定义体: X.unop.rightOp
  map f :=
    { left := f.unop.right.op
      right := NatTrans.rightOp f.unop.left
      w := by
        ext x
        dsimp
        simp_rw [← op_comp]
        congr 1
        exact (congr_app f.unop.w (op x)).symm }

Depends on / 依赖: X.unop.rightOp, rightOp
-/
def simplicialToCosimplicialAugmented :
    (SimplicialObject.Augmented C)ᵒᵖ ⥤ CosimplicialObject.Augmented Cᵒᵖ where
  obj X := X.unop.rightOp
  map f :=
    { left := f.unop.right.op
      right := NatTrans.rightOp f.unop.left
      w := by
        ext x
        dsimp
        simp_rw [← op_comp]
        congr 1
        exact (congr_app f.unop.w (op x)).symm }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A functorial version of `Cosimplicial_object.Augmented.leftOp`. -/
@[simps]
/--
Definition of `cosimplicialToSimplicialAugmented` / `cosimplicialToSimplicialAugmented` 的定义

English:
definition cosimplicialToSimplicialAugmented
  signature: :
  body: Opposite.op X.leftOp
  map f :=
Quiver.Hom.op
      { left := NatTrans.leftOp f.right
        right := f.left.unop
        w := by
          ext x
          dsimp
          simp_rw [← unop_comp]
          congr 1
          exact (congr_app f.w (unop x)).symm }

中文:
定义 cosimplicialToSimplicialAugmented
  签名: :
  定义体: Opposite.op X.leftOp
  map f :=
Quiver.Hom.op
      { left := NatTrans.leftOp f.right
        right := f.left.unop
        w := by
          ext x
          dsimp
          simp_rw [← unop_comp]
          congr 1
          exact (congr_app f.w (unop x)).symm }

Depends on / 依赖: Opposite, Opposite.op, X.leftOp, leftOp
-/
def cosimplicialToSimplicialAugmented :
    CosimplicialObject.Augmented Cᵒᵖ ⥤ (SimplicialObject.Augmented C)ᵒᵖ where
  obj X := Opposite.op X.leftOp
  map f :=
Quiver.Hom.op
      { left := NatTrans.leftOp f.right
        right := f.left.unop
        w := by
          ext x
          dsimp
          simp_rw [← unop_comp]
          congr 1
          exact (congr_app f.w (unop x)).symm }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The contravariant categorical equivalence between augmented simplicial
objects and augmented cosimplicial objects in the opposite category. -/
@[simps! functor inverse]
/--
Definition of `simplicialCosimplicialAugmentedEquiv` / `simplicialCosimplicialAugmentedEquiv` 的定义

English:
definition simplicialCosimplicialAugmentedEquiv
  signature: :
  body: simplicialToCosimplicialAugmented _
  inverse := cosimplicialToSimplicialAugmented _
  unitIso := NatIso.ofComponents (fun X => X.unop.rightOpLeftOpIso.op) fun f => by
      dsimp
      rw [← f.op_unop]
      simp_rw [← op_comp]
      congr 1
      cat_disch
  counitIso := NatIso.ofComponents fun X => X.leftOpRightOpIso

中文:
定义 simplicialCosimplicialAugmentedEquiv
  签名: :
  定义体: simplicialToCosimplicialAugmented _
  inverse := cosimplicialToSimplicialAugmented _
  unitIso := NatIso.ofComponents (fun X => X.unop.rightOpLeftOpIso.op) fun f => by
      dsimp
      rw [← f.op_unop]
      simp_rw [← op_comp]
      congr 1
      cat_disch
  counitIso := NatIso.ofComponents fun X => X.leftOpRightOpIso

Depends on / 依赖: simplicialToCosimplicialAugmented
-/
def simplicialCosimplicialAugmentedEquiv :
    (SimplicialObject.Augmented C)ᵒᵖ ≌ CosimplicialObject.Augmented Cᵒᵖ where
  functor := simplicialToCosimplicialAugmented _
  inverse := cosimplicialToSimplicialAugmented _
  unitIso := NatIso.ofComponents (fun X => X.unop.rightOpLeftOpIso.op) fun f => by
      dsimp
      rw [← f.op_unop]
      simp_rw [← op_comp]
      congr 1
      cat_disch
  counitIso := NatIso.ofComponents fun X => X.leftOpRightOpIso

end CategoryTheory
