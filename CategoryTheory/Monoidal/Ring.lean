/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.Algebra.Ring.Basic

/-!
# Ring objects in cartesian monoidal categories

If `C` is a cartesian monoidal category and `X : C`, we introduce a typeclass `RingObj X`
which says that `X` is a ring object: it has a commutative additive group structure and
a multiplicative monoid structure that is distributive over the additive structure.
We also introduce a typeclass `CommRingObj X` which further requires that the multiplicative
law is commutative.

The categories of bundled ring objects and bundled commutative ring objects are
denoted `RingObjCat C` and `CommRingObjCat C` respectively.

## TODO
* develop the theory of bimonoidal categories and relate this with `Rig`-objects

-/

@[expose] public section

universe v u

namespace CategoryTheory

open MonoidalCategory CartesianMonoidalCategory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

open scoped MonObj AddMonObj

/--
lemma `mul_add_iff` / 引理 `mul_add_iff`

English:
lemma mul_add_iff
  given: (R : C) [MonObj R] [AddMonObj R]
  proof: by
  refine ⟨fun h _ a b c => ?_, fun h => ?_⟩
  · have := lift a (lift b c) ≫= h
    simp only [lift_whiskerLeft_assoc] at this
    simp only [Hom.add_def, Hom.mul_def, this, ← Category.assoc]
    cat_disch
  · replace h := h (fst R (R otimes R)) (snd _ _ ≫ fst _ _) (snd _ _ ≫ snd _ _)
    simp only [Hom.mul_def, Hom.add_def] at h
    convert! h using 2
    · cat_disch
    · ext
      · simp only [lift_fst]
        congr 1
        cat_disch
      · simp only [lift_snd]
        congr 1
        cat_disch

中文:
引理 mul_add_iff
  条件: (R : C) [MonObj R] [加法MonObj R]
  证明: by
  refine ⟨fun h _ a b c => ?_, fun h => ?_⟩
  · have := lift a (lift b c) ≫= h
    simp only [lift_whiskerLeft_assoc] at this
    simp only [Hom.add_def, Hom.mul_def, this, ← Category.assoc]
    cat_disch
  · replace h := h (fst R (R otimes R)) (snd _ _ ≫ fst _ _) (snd _ _ ≫ snd _ _)
    simp only [Hom.mul_def, Hom.add_def] at h
    convert! h using 2
    · cat_disch
    · ext
      · simp only [lift_fst]
        congr 1
        cat_disch
      · simp only [lift_snd]
        congr 1
        cat_disch

Depends on / 依赖: Category, Category.assoc, Hom.add_def, Hom.mul_def, add_def, cat_disch, convert, lift_fst, lift_snd, lift_whiskerLeft_assoc, mul_def, otimes, replace
-/
lemma mul_add_iff (R : C) [MonObj R] [AddMonObj R] :
    R ◁ σ ≫ μ = lift ((R ◁ fst _ _) ≫ μ) ((R ◁ snd _ _) ≫ μ) ≫ σ ↔
      forall ⦃X : C⦄ (a b c : X ⟶ R), a * (b + c) = a * b + a * c := by
  refine ⟨fun h _ a b c => ?_, fun h => ?_⟩
  · have := lift a (lift b c) ≫= h
    simp only [lift_whiskerLeft_assoc] at this
    simp only [Hom.add_def, Hom.mul_def, this, ← Category.assoc]
    cat_disch
  · replace h := h (fst R (R otimes R)) (snd _ _ ≫ fst _ _) (snd _ _ ≫ snd _ _)
    simp only [Hom.mul_def, Hom.add_def] at h
    convert! h using 2
    · cat_disch
    · ext
      · simp only [lift_fst]
        congr 1
        cat_disch
      · simp only [lift_snd]
        congr 1
        cat_disch

/--
lemma `add_mul_iff` / 引理 `add_mul_iff`

English:
lemma add_mul_iff
  given: (R : C) [MonObj R] [AddMonObj R]
  proof: by
  refine ⟨fun h _ a b c => ?_, fun h => ?_⟩
  · have := lift (lift a b) c ≫= h
    simp only [lift_whiskerRight_assoc] at this
    simp only [Hom.add_def, Hom.mul_def, this, ← Category.assoc]
    cat_disch
  · replace h := h (fst (R otimes R) R ≫ fst _ _) (fst _ _ ≫ snd _ _) (snd _ _)
    simp only [Hom.mul_def, Hom.add_def] at h
    convert! h using 2
    · cat_disch
    · ext
      · simp only [lift_fst]
        congr 1
        cat_disch
      · simp only [lift_snd]
        congr 1
        cat_disch

中文:
引理 add_mul_iff
  条件: (R : C) [MonObj R] [加法MonObj R]
  证明: by
  refine ⟨fun h _ a b c => ?_, fun h => ?_⟩
  · have := lift (lift a b) c ≫= h
    simp only [lift_whiskerRight_assoc] at this
    simp only [Hom.add_def, Hom.mul_def, this, ← Category.assoc]
    cat_disch
  · replace h := h (fst (R otimes R) R ≫ fst _ _) (fst _ _ ≫ snd _ _) (snd _ _)
    simp only [Hom.mul_def, Hom.add_def] at h
    convert! h using 2
    · cat_disch
    · ext
      · simp only [lift_fst]
        congr 1
        cat_disch
      · simp only [lift_snd]
        congr 1
        cat_disch

Depends on / 依赖: Category, Category.assoc, Hom.add_def, Hom.mul_def, add_def, cat_disch, convert, lift_fst, lift_snd, lift_whiskerRight_assoc, mul_def, otimes, replace
-/
lemma add_mul_iff (R : C) [MonObj R] [AddMonObj R] :
    σ ▷ R ≫ μ = lift (fst _ _ ▷ _ ≫ μ) (snd _ _ ▷ _ ≫ μ) ≫ σ ↔
      forall ⦃X : C⦄ (a b c : X ⟶ R), (a + b) * c = a * c + b * c := by
  refine ⟨fun h _ a b c => ?_, fun h => ?_⟩
  · have := lift (lift a b) c ≫= h
    simp only [lift_whiskerRight_assoc] at this
    simp only [Hom.add_def, Hom.mul_def, this, ← Category.assoc]
    cat_disch
  · replace h := h (fst (R otimes R) R ≫ fst _ _) (fst _ _ ≫ snd _ _) (snd _ _)
    simp only [Hom.mul_def, Hom.add_def] at h
    convert! h using 2
    · cat_disch
    · ext
      · simp only [lift_fst]
        congr 1
        cat_disch
      · simp only [lift_snd]
        congr 1
        cat_disch

variable [BraidedCategory C]

/--
Definition of `RingObj` / `RingObj` 的定义

English:
class RingObj
  parameters: (R : C)
  extends: AddGrpObj R, IsCommAddMonObj R, MonObj R
  axioms and operations (2):
    - mul_add((R)) : R ◁ σ ≫ μ = lift ((R ◁ fst _ _) ≫ μ) ((R ◁ snd _ _) ≫ μ) ≫ σ
    - add_mul((R)) : σ ▷ R ≫ μ = lift (fst _ _ ▷ _ ≫ μ) (snd _ _ ▷ _ ≫ μ) ≫ σ

中文:
类 RingObj
  参数: (R : C)
  继承: 加法GrpObj R, 是交换加法MonObj R, MonObj R
  公理与运算 (2 个):
    - mul_add((R)) : R ◁ σ ≫ μ = lift ((R ◁ fst _ _) ≫ μ) ((R ◁ snd _ _) ≫ μ) ≫ σ
    - add_mul((R)) : σ ▷ R ≫ μ = lift (fst _ _ ▷ _ ≫ μ) (snd _ _ ▷ _ ≫ μ) ≫ σ
-/
class RingObj (R : C) extends AddGrpObj R, IsCommAddMonObj R, MonObj R where
  mul_add (R) : R ◁ σ ≫ μ = lift ((R ◁ fst _ _) ≫ μ) ((R ◁ snd _ _) ≫ μ) ≫ σ
  add_mul (R) : σ ▷ R ≫ μ = lift (fst _ _ ▷ _ ≫ μ) (snd _ _ ▷ _ ≫ μ) ≫ σ

section

variable {R : C} [RingObj R] {X : C}

/--
lemma `Hom.mul_add` / 引理 `Hom.mul_add`

English:
lemma Hom.mul_add
  given: (a b c : X ⟶ R)
  statement: a * (b + c) = a * b + a * c
  proof: by
  revert X a b c
  rw [← mul_add_iff]; rw [RingObj.mul_add R]

中文:
引理 态射.mul_add
  条件: (a b c : X ⟶ R)
  结论: a * (b + c) = a * b + a * c
  证明: by
  revert X a b c
  rw [← mul_add_iff]; rw [RingObj.mul_add R]

Depends on / 依赖: RingObj, RingObj.mul_add, mul_add, mul_add_iff, revert
-/
lemma Hom.mul_add (a b c : X ⟶ R) : a * (b + c) = a * b + a * c := by
  revert X a b c
  rw [← mul_add_iff]; rw [RingObj.mul_add R]

/--
lemma `Hom.add_mul` / 引理 `Hom.add_mul`

English:
lemma Hom.add_mul
  given: (a b c : X ⟶ R)
  statement: (a + b) * c = a * c + b * c
  proof: by
  revert X a b c
  rw [← add_mul_iff]; rw [RingObj.add_mul R]

中文:
引理 态射.add_mul
  条件: (a b c : X ⟶ R)
  结论: (a + b) * c = a * c + b * c
  证明: by
  revert X a b c
  rw [← add_mul_iff]; rw [RingObj.add_mul R]

Depends on / 依赖: RingObj, RingObj.add_mul, add_mul, add_mul_iff, revert
-/
lemma Hom.add_mul (a b c : X ⟶ R) : (a + b) * c = a * c + b * c := by
  revert X a b c
  rw [← add_mul_iff]; rw [RingObj.add_mul R]

/--
Definition of `Hom.ring` / `Hom.ring` 的定义

English:
abbreviation Hom.ring
  signature: {X : C}
  body: Hom.mul_add
  right_distrib := Hom.add_mul
  mul_zero a := by simpa using mul_add a 0 0
  zero_mul a := by simpa using add_mul 0 0 a

scoped[CategoryTheory.RingObj] attribute [instance] Hom.ring

中文:
缩写 态射.ring
  签名: {X : C}
  定义体: Hom.mul_add
  right_distrib := Hom.add_mul
  mul_zero a := by simpa using mul_add a 0 0
  zero_mul a := by simpa using add_mul 0 0 a

scoped[CategoryTheory.RingObj] attribute [instance] Hom.ring

Depends on / 依赖: Hom.mul_add, mul_add
-/
abbrev Hom.ring {X : C} : Ring (X ⟶ R) where
  left_distrib := Hom.mul_add
  right_distrib := Hom.add_mul
  mul_zero a := by simpa using mul_add a 0 0
  zero_mul a := by simpa using add_mul 0 0 a

scoped[CategoryTheory.RingObj] attribute [instance] Hom.ring

end

open scoped RingObj

/--
Definition of `CommRingObj` / `CommRingObj` 的定义

English:
class CommRingObj
  parameters: (R : C)
  extends: RingObj R, IsCommMonObj R
  (no additional axioms)

中文:
类 交换RingObj
  参数: (R : C)
  继承: RingObj R, 是交换MonObj R
  (无附加公理)
-/
class CommRingObj (R : C) extends RingObj R, IsCommMonObj R where

/--
Definition of `Hom.commRing` / `Hom.commRing` 的定义

English:
abbreviation Hom.commRing
  signature: {R : C} {X : C} [CommRingObj R]

中文:
缩写 态射.commRing
  签名: {R : C} {X : C} [交换RingObj R]
-/
abbrev Hom.commRing {R : C} {X : C} [CommRingObj R] : CommRing (X ⟶ R) where

scoped[CategoryTheory.CommRingObj] attribute [instance] Hom.commRing

/--
Definition of `IsRingHom` / `IsRingHom` 的定义

English:
class IsRingHom
  parameters: {R₁ R₂ : C} [AddMonObj R₁] [AddMonObj R₂] [MonObj R₁] [MonObj R₂] (f : R₁ ⟶ R₂)
  extends: IsAddMonHom f, IsMonHom f
  (no additional axioms)

中文:
类 是环态射
  参数: {R₁ R₂ : C} [加法MonObj R₁] [加法MonObj R₂] [MonObj R₁] [MonObj R₂] (f : R₁ ⟶ R₂)
  继承: 是加法幺半群态射 f, 是幺半群态射 f
  (无附加公理)
-/
class IsRingHom {R₁ R₂ : C} [AddMonObj R₁] [AddMonObj R₂] [MonObj R₁] [MonObj R₂] (f : R₁ ⟶ R₂)
  extends IsAddMonHom f, IsMonHom f

/--
Instance `IsRingHom.id` / 实例 `IsRingHom.id`

English:
instance IsRingHom.id
  signature: (R : C) [AddMonObj R] [MonObj R]

中文:
实例 是环态射.id
  签名: (R : C) [加法MonObj R] [MonObj R]
-/
instance IsRingHom.id (R : C) [AddMonObj R] [MonObj R] : IsRingHom (𝟙 R) where

/--
Instance `IsRingHom.comp` / 实例 `IsRingHom.comp`

English:
instance IsRingHom.comp
  signature: {R₁ R₂ R₃ : C}

中文:
实例 是环态射.comp
  签名: {R₁ R₂ R₃ : C}

Depends on / 依赖: initial, initial.to
-/
instance IsRingHom.comp {R₁ R₂ R₃ : C}
    [AddMonObj R₁] [AddMonObj R₂] [AddMonObj R₃]
    [MonObj R₁] [MonObj R₂] [MonObj R₃]
    (f : R₁ ⟶ R₂) (g : R₂ ⟶ R₃) [IsRingHom f] [IsRingHom g] :
    IsRingHom (f ≫ g) where

variable (C) in
/--
Definition of `RingObjCat` / `RingObjCat` 的定义

English:
structure RingObjCat
  parameters: where
  axioms and operations (2):
    - X : C
    - [ringObj : RingObj X]

中文:
结构 RingObj范畴
  参数: where
  公理与运算 (2 个):
    - X : C
    - [ringObj : RingObj X]
-/
structure RingObjCat where
  /-- The underlying object in the ambient monoidal category -/
  X : C
  [ringObj : RingObj X]

initialize_simps_projections RingObjCat (-ringObj)

namespace RingObjCat

attribute [instance] ringObj

/-- A morphism of ring objects. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (R₁ R₂ : RingObjCat C)
  axioms and operations (2):
    - hom : R₁.X ⟶ R₂.X
    - [isRingHom : IsRingHom hom]

中文:
结构 态射
  参数: (R₁ R₂ : RingObj范畴 C)
  公理与运算 (2 个):
    - hom : R₁.X ⟶ R₂.X
    - [isRingHom : 是环态射 hom]
-/
structure Hom (R₁ R₂ : RingObjCat C) where
  /-- The underlying morphism -/
  hom : R₁.X ⟶ R₂.X
  [isRingHom : IsRingHom hom]

attribute [instance] Hom.isRingHom

@[simps]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (RingObjCat C)
  body: Hom R₁ R₂
  id X := { hom := 𝟙 _ }
  comp f g := { hom := f.hom ≫ g.hom }

@[ext]

中文:
实例 :
  签名: 范畴 (RingObj范畴 C)
  定义体: Hom R₁ R₂
  id X := { hom := 𝟙 _ }
  comp f g := { hom := f.hom ≫ g.hom }

@[ext]
-/
instance : Category (RingObjCat C) where
  Hom R₁ R₂ := Hom R₁ R₂
  id X := { hom := 𝟙 _ }
  comp f g := { hom := f.hom ≫ g.hom }

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {R₁ R₂ : RingObjCat C} {f g : R₁ ⟶ R₂} (h : f.hom = g.hom)
  statement: f = g
  proof: Hom.ext h

中文:
引理 hom_ext
  条件: {R₁ R₂ : RingObj范畴 C} {f g : R₁ ⟶ R₂} (h : f.hom = g.hom)
  结论: f = g
  证明: Hom.ext h

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {R₁ R₂ : RingObjCat C} {f g : R₁ ⟶ R₂} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

variable (C) in
/-- The forgetful functor from the category of ring objects in `C` to `C`. -/
@[simps]
/--
Definition of `forget` / `forget` 的定义

English:
definition forget
  signature: : RingObjCat C ⥤ C where
  body: R.X
  map f := f.hom

中文:
定义 forget
  签名: : RingObj范畴 C ⥤ C where
  定义体: R.X
  map f := f.hom
-/
def forget : RingObjCat C ⥤ C where
  obj R := R.X
  map f := f.hom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget C).Faithful

中文:
实例 :
  签名: (forget C).忠实
-/
instance : (forget C).Faithful where

variable (C) in
/-- The forgetful functor from the category of ring objects in `C`
to the category of monoid objects in `C`. -/
@[simps]
/--
Definition of `forget₂Mon` / `forget₂Mon` 的定义

English:
definition forget₂Mon
  signature: : RingObjCat C ⥤ Mon C where
  body: .mk R.X
  map f := .mk f.hom

中文:
定义 forget₂Mon
  签名: : RingObj范畴 C ⥤ 幺半群 C where
  定义体: .mk R.X
  map f := .mk f.hom
-/
def forget₂Mon : RingObjCat C ⥤ Mon C where
  obj R := .mk R.X
  map f := .mk f.hom

variable (C) in
/-- The forgetful functor from the category of ring objects in `C`
to the category of additive monoid objects in `C`. -/
@[simps]
/--
Definition of `forget₂AddMon` / `forget₂AddMon` 的定义

English:
definition forget₂AddMon
  signature: : RingObjCat C ⥤ AddMon C where
  body: .mk R.X
  map f := .mk f.hom

中文:
定义 forget₂AddMon
  签名: : RingObj范畴 C ⥤ 加法幺半群 C where
  定义体: .mk R.X
  map f := .mk f.hom
-/
def forget₂AddMon : RingObjCat C ⥤ AddMon C where
  obj R := .mk R.X
  map f := .mk f.hom

end RingObjCat

variable (C) in
/--
Definition of `CommRingObjCat` / `CommRingObjCat` 的定义

English:
structure CommRingObjCat
  parameters: where
  axioms and operations (2):
    - X : C
    - [commRingObj : CommRingObj X]

中文:
结构 交换RingObj范畴
  参数: where
  公理与运算 (2 个):
    - X : C
    - [commRingObj : 交换RingObj X]
-/
structure CommRingObjCat where
  /-- The underlying object in the ambient monoidal category -/
  X : C
  [commRingObj : CommRingObj X]

initialize_simps_projections CommRingObjCat (-commRingObj)

namespace CommRingObjCat

attribute [instance] commRingObj

/-- A morphism of commutative ring objects. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (R₁ R₂ : CommRingObjCat C)
  axioms and operations (2):
    - hom : R₁.X ⟶ R₂.X
    - [isRingHom : IsRingHom hom]

中文:
结构 态射
  参数: (R₁ R₂ : 交换RingObj范畴 C)
  公理与运算 (2 个):
    - hom : R₁.X ⟶ R₂.X
    - [isRingHom : 是环态射 hom]
-/
structure Hom (R₁ R₂ : CommRingObjCat C) where
  /-- The underlying morphism -/
  hom : R₁.X ⟶ R₂.X
  [isRingHom : IsRingHom hom]

attribute [instance] Hom.isRingHom

@[simps]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (CommRingObjCat C)
  body: Hom R₁ R₂
  id X := { hom := 𝟙 _ }
  comp f g := { hom := f.hom ≫ g.hom }

@[ext]

中文:
实例 :
  签名: 范畴 (交换RingObj范畴 C)
  定义体: Hom R₁ R₂
  id X := { hom := 𝟙 _ }
  comp f g := { hom := f.hom ≫ g.hom }

@[ext]
-/
instance : Category (CommRingObjCat C) where
  Hom R₁ R₂ := Hom R₁ R₂
  id X := { hom := 𝟙 _ }
  comp f g := { hom := f.hom ≫ g.hom }

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {R₁ R₂ : CommRingObjCat C} {f g : R₁ ⟶ R₂} (h : f.hom = g.hom)
  statement: f = g
  proof: Hom.ext h

中文:
引理 hom_ext
  条件: {R₁ R₂ : 交换RingObj范畴 C} {f g : R₁ ⟶ R₂} (h : f.hom = g.hom)
  结论: f = g
  证明: Hom.ext h

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {R₁ R₂ : CommRingObjCat C} {f g : R₁ ⟶ R₂} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

variable (C) in
/-- The forgetful functor from the category of ring objects in `C` to `C`. -/
@[simps]
/--
Definition of `forget` / `forget` 的定义

English:
definition forget
  signature: : CommRingObjCat C ⥤ C where
  body: R.X
  map f := f.hom

中文:
定义 forget
  签名: : 交换RingObj范畴 C ⥤ C where
  定义体: R.X
  map f := f.hom
-/
def forget : CommRingObjCat C ⥤ C where
  obj R := R.X
  map f := f.hom

variable (C) in
/-- The forgetful functor from the category of commutative ring objects
to the category of ring objects. -/
@[simps]
/--
Definition of `forget₂RingObjCat` / `forget₂RingObjCat` 的定义

English:
definition forget₂RingObjCat
  signature: : CommRingObjCat C ⥤ RingObjCat C where
  body: .mk R.X
  map f := { hom := f.hom }

中文:
定义 forget₂RingObjCat
  签名: : 交换RingObj范畴 C ⥤ RingObj范畴 C where
  定义体: .mk R.X
  map f := { hom := f.hom }
-/
def forget₂RingObjCat : CommRingObjCat C ⥤ RingObjCat C where
  obj R := .mk R.X
  map f := { hom := f.hom }

variable (C) in
/--
Definition of `fullyFaithfulForget₂RingObjCat` / `fullyFaithfulForget₂RingObjCat` 的定义

English:
definition fullyFaithfulForget₂RingObjCat
  signature: : (forget₂RingObjCat C).FullyFaithful where
  body: { hom := f.hom, isRingHom := f.isRingHom }

中文:
定义 fullyFaithfulForget₂RingObjCat
  签名: : (forget₂RingObjCat C).满忠实 where
  定义体: { hom := f.hom, isRingHom := f.isRingHom }

Depends on / 依赖: f.hom, f.isRingHom, isRingHom
-/
def fullyFaithfulForget₂RingObjCat : (forget₂RingObjCat C).FullyFaithful where
  preimage f := { hom := f.hom, isRingHom := f.isRingHom }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget₂RingObjCat C).Faithful
  body: (fullyFaithfulForget₂RingObjCat C).faithful

中文:
实例 :
  签名: (forget₂RingObjCat C).忠实
  定义体: (fullyFaithfulForget₂RingObjCat C).faithful

Depends on / 依赖: faithful
-/
instance : (forget₂RingObjCat C).Faithful :=
  (fullyFaithfulForget₂RingObjCat C).faithful

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget₂RingObjCat C).Full
  body: (fullyFaithfulForget₂RingObjCat C).full

中文:
实例 :
  签名: (forget₂RingObjCat C).满
  定义体: (fullyFaithfulForget₂RingObjCat C).full
-/
instance : (forget₂RingObjCat C).Full :=
  (fullyFaithfulForget₂RingObjCat C).full

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget C).Faithful

中文:
实例 :
  签名: (forget C).忠实
-/
instance : (forget C).Faithful where

end CommRingObjCat

end CategoryTheory
