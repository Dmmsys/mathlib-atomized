/-
Copyright (c) 2025 Markus Himmel, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Andrew Yang
-/
module

public import Mathlib.Algebra.Category.MonCat.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.ConcreteCategory.Representable

/-!
# Yoneda embedding of `Mon C`

We show that monoid objects in Cartesian monoidal categories are exactly those whose yoneda presheaf
is a presheaf of monoids, by constructing the yoneda embedding `Mon C ⥤ Cᵒᵖ ⥤ MonCat.{v}` and
showing that it is fully faithful and its (essential) image is the representable functors.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Limits Opposite CartesianMonoidalCategory MonObj

namespace CategoryTheory

section SemiCartesianMonoidalCategory

variable {D : Type*} [Category* D] [SemiCartesianMonoidalCategory D]

namespace MonObj

@[to_additive]
instance (M : D) [MonObj M] : IsMonHom (toUnit M) where

@[to_additive]
instance (M : D) [MonObj M] : IsMonHom η[M] where
  mul_hom := by simp [toUnit_unique (ρ_ (𝟙_ D)).hom (fun_ (𝟙_ D)).hom]

-- The general `(f : 𝟙_ C ⟶ X) : Mono f` instance has a bad discrimination tree key.
@[to_additive]
instance (M : D) [MonObj M] : Mono η[M] := Limits.IsTerminal.mono_from isTerminalTensorUnit _

end MonObj

set_option backward.defeqAttrib.useBackward true in
@[to_additive (attr := simps)]
/--
Instance `Mon.uniqueHomToTrivial` / 实例 `Mon.uniqueHomToTrivial`

English:
instance Mon.uniqueHomToTrivial
  signature: (A : Mon D)
  body: toUnit A.X
  default.isMonHom_hom.mul_hom := toUnit_unique _ _
  uniq f := Mon.Hom.ext (toUnit_unique _ _)

@[deprecated (since := "2026-03-20")] alias uniqueHomToTrivial := Mon.uniqueHomToTrivial

中文:
实例 幺半群.uniqueHomToTrivial
  签名: (A : 幺半群 D)
  定义体: toUnit A.X
  default.isMonHom_hom.mul_hom := toUnit_unique _ _
  uniq f := Mon.Hom.ext (toUnit_unique _ _)

@[deprecated (since := "2026-03-20")] alias uniqueHomToTrivial := Mon.uniqueHomToTrivial

Depends on / 依赖: toUnit
-/
instance Mon.uniqueHomToTrivial (A : Mon D) : Unique (A ⟶ Mon.trivial D) where
  default.hom := toUnit A.X
  default.isMonHom_hom.mul_hom := toUnit_unique _ _
  uniq f := Mon.Hom.ext (toUnit_unique _ _)

@[deprecated (since := "2026-03-20")] alias uniqueHomToTrivial := Mon.uniqueHomToTrivial

namespace Mon

variable (D) in
@[to_additive]
/--
lemma `isZero_trivial` / 引理 `isZero_trivial`

English:
lemma isZero_trivial
  statement: IsZero (Mon.trivial D) where
  proof: nonempty_unique (Mon.trivial D ⟶ A)
  unique_from A := nonempty_unique (A ⟶ Mon.trivial D)

@[to_additive]

中文:
引理 isZero_trivial
  结论: 是零 (幺半群.trivial D) where
  证明: nonempty_unique (Mon.trivial D ⟶ A)
  unique_from A := nonempty_unique (A ⟶ Mon.trivial D)

@[to_additive]

Depends on / 依赖: Mon.trivial, nonempty_unique
-/
lemma isZero_trivial : IsZero (Mon.trivial D) where
  unique_to A := nonempty_unique (Mon.trivial D ⟶ A)
  unique_from A := nonempty_unique (A ⟶ Mon.trivial D)

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasZeroObject (Mon D)
  body: ⟨Mon.trivial D, Mon.isZero_trivial D⟩

@[to_additive]

中文:
实例 :
  签名: 有ZeroObject (幺半群 D)
  定义体: ⟨Mon.trivial D, Mon.isZero_trivial D⟩

@[to_additive]

Depends on / 依赖: Mon.isZero_trivial, Mon.trivial, isZero_trivial
-/
instance : HasZeroObject (Mon D) where
  zero := ⟨Mon.trivial D, Mon.isZero_trivial D⟩

@[to_additive]
instance (M N : Mon D) : Zero (M ⟶ N) where
  zero := ⟨toUnit _ ≫ η⟩

@[to_additive (attr := simp)]
/--
lemma `zero_hom` / 引理 `zero_hom`

English:
lemma zero_hom
  given: (M N : Mon D)
  statement: (0 : M ⟶ N).hom = toUnit _ ≫ η
  proof: rfl

@[to_additive]

中文:
引理 zero_hom
  条件: (M N : 幺半群 D)
  结论: (0 : M ⟶ N).hom = toUnit _ ≫ η
  证明: rfl

@[to_additive]
-/
lemma zero_hom (M N : Mon D) : (0 : M ⟶ N).hom = toUnit _ ≫ η := rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasZeroMorphisms (Mon D)

中文:
实例 :
  签名: 有ZeroMorphisms (幺半群 D)
-/
noncomputable instance : HasZeroMorphisms (Mon D) where

end Mon

end SemiCartesianMonoidalCategory

universe w v u
variable {C D : Type*} [Category.{v} C] [CartesianMonoidalCategory C]
  [Category.{w} D] [CartesianMonoidalCategory D]
  {M N O X Y : C} [MonObj M] [MonObj N] [MonObj O]

namespace MonObj

@[to_additive]
/--
theorem `lift_lift_assoc` / 定理 `lift_lift_assoc`

English:
theorem lift_lift_assoc
  given: {A : C} {B : C} [MonObj B] (f g h : A ⟶ B)
  proof: by
  have := lift (lift f g) h ≫= mul_assoc B
  rwa [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc] at this

@[to_additive (attr := reassoc (attr := simp))]

中文:
定理 lift_lift_assoc
  条件: {A : C} {B : C} [MonObj B] (f g h : A ⟶ B)
  证明: by
  have := lift (lift f g) h ≫= mul_assoc B
  rwa [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc] at this

@[to_additive (attr := reassoc (attr := simp))]

Depends on / 依赖: lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc, lift_whiskerRight_assoc, mul_assoc
-/
theorem lift_lift_assoc {A : C} {B : C} [MonObj B] (f g h : A ⟶ B) :
    lift (lift f g ≫ μ) h ≫ μ = lift f (lift g h ≫ μ) ≫ μ := by
  have := lift (lift f g) h ≫= mul_assoc B
  rwa [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc] at this

@[to_additive (attr := reassoc (attr := simp))]
/--
theorem `lift_comp_one_left` / 定理 `lift_comp_one_left`

English:
theorem lift_comp_one_left
  given: {A : C} {B : C} [MonObj B] (f : A ⟶ 𝟙_ C) (g : A ⟶ B)
  proof: by
  have := lift f g ≫= one_mul B
  rwa [lift_whiskerRight_assoc, lift_leftUnitor_hom] at this

@[to_additive (attr := reassoc (attr := simp))]

中文:
定理 lift_comp_one_left
  条件: {A : C} {B : C} [MonObj B] (f : A ⟶ 𝟙_ C) (g : A ⟶ B)
  证明: by
  have := lift f g ≫= one_mul B
  rwa [lift_whiskerRight_assoc, lift_leftUnitor_hom] at this

@[to_additive (attr := reassoc (attr := simp))]

Depends on / 依赖: lift_leftUnitor_hom, lift_whiskerRight_assoc, one_mul
-/
theorem lift_comp_one_left {A : C} {B : C} [MonObj B] (f : A ⟶ 𝟙_ C) (g : A ⟶ B) :
    lift (f ≫ η) g ≫ μ = g := by
  have := lift f g ≫= one_mul B
  rwa [lift_whiskerRight_assoc, lift_leftUnitor_hom] at this

@[to_additive (attr := reassoc (attr := simp))]
/--
theorem `lift_comp_one_right` / 定理 `lift_comp_one_right`

English:
theorem lift_comp_one_right
  given: {A : C} {B : C} [MonObj B] (f : A ⟶ B) (g : A ⟶ 𝟙_ C)
  proof: by
  have := lift f g ≫= mul_one B
  rwa [lift_whiskerLeft_assoc, lift_rightUnitor_hom] at this

中文:
定理 lift_comp_one_right
  条件: {A : C} {B : C} [MonObj B] (f : A ⟶ B) (g : A ⟶ 𝟙_ C)
  证明: by
  have := lift f g ≫= mul_one B
  rwa [lift_whiskerLeft_assoc, lift_rightUnitor_hom] at this

Depends on / 依赖: lift_rightUnitor_hom, lift_whiskerLeft_assoc, mul_one
-/
theorem lift_comp_one_right {A : C} {B : C} [MonObj B] (f : A ⟶ B) (g : A ⟶ 𝟙_ C) :
    lift f (g ≫ η) ≫ μ = f := by
  have := lift f g ≫= mul_one B
  rwa [lift_whiskerLeft_assoc, lift_rightUnitor_hom] at this

variable [BraidedCategory C]

attribute [local simp] tensorObj.one_def tensorObj.mul_def

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsMonHom (fst M N)

中文:
实例 :
  签名: 是幺半群态射 (fst M N)
-/
instance : IsMonHom (fst M N) where

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsMonHom (snd M N)

中文:
实例 :
  签名: 是幺半群态射 (snd M N)
-/
instance : IsMonHom (snd M N) where

@[to_additive]
instance {f : M ⟶ N} {g : M ⟶ O} [IsMonHom f] [IsMonHom g] : IsMonHom (lift f g) where

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsCommMonObj
  signature: M] : IsMonHom μ[M] where
  body: by simp [toUnit_unique (ρ_ (𝟙_ C)).hom (fun_ (𝟙_ C)).hom]

中文:
实例 [是交换MonObj
  签名: M] : 是幺半群态射 μ[M] where
  定义体: by simp [toUnit_unique (ρ_ (𝟙_ C)).hom (fun_ (𝟙_ C)).hom]

Depends on / 依赖: fun_, toUnit_unique
-/
instance [IsCommMonObj M] : IsMonHom μ[M] where
  one_hom := by simp [toUnit_unique (ρ_ (𝟙_ C)).hom (fun_ (𝟙_ C)).hom]

end MonObj

namespace Mon
variable [BraidedCategory C]

set_option backward.isDefEq.respectTransparency false in
attribute [local simp] tensorObj.one_def tensorObj.mul_def in
@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CartesianMonoidalCategory (Mon C)
  body: .ofUniqueHom (fun M => ⟨toUnit _⟩) fun M f => by ext; exact toUnit_unique ..
  fst M N := .mk (fst M.X N.X)
  snd M N := .mk (snd M.X N.X)
  tensorProductIsBinaryProduct M N :=
    BinaryFan.IsLimit.mk _ (fun {T} f g => ⟨lift f.hom g.hom⟩)
      (by aesop_cat) (by aesop_cat) (by aesop_cat)
  fst_def

中文:
实例 :
  签名: CartesianMonoidal范畴 (幺半群 C)
  定义体: .ofUniqueHom (fun M => ⟨toUnit _⟩) fun M f => by ext; exact toUnit_unique ..
  fst M N := .mk (fst M.X N.X)
  snd M N := .mk (snd M.X N.X)
  tensorProductIsBinaryProduct M N :=
    BinaryFan.IsLimit.mk _ (fun {T} f g => ⟨lift f.hom g.hom⟩)
      (by aesop_cat) (by aesop_cat) (by aesop_cat)
  fst_def

Depends on / 依赖: ofUniqueHom, toUnit, toUnit_unique
-/
instance : CartesianMonoidalCategory (Mon C) where
  isTerminalTensorUnit := .ofUniqueHom (fun M => ⟨toUnit _⟩) fun M f => by ext; exact toUnit_unique ..
  fst M N := .mk (fst M.X N.X)
  snd M N := .mk (snd M.X N.X)
  tensorProductIsBinaryProduct M N :=
    BinaryFan.IsLimit.mk _ (fun {T} f g => ⟨lift f.hom g.hom⟩)
      (by aesop_cat) (by aesop_cat) (by aesop_cat)
  fst_def M N := by ext; simp [fst_def]; congr
  snd_def M N := by ext; simp [snd_def]; congr

variable {M N N₁ N₂ : Mon C}

@[to_additive (attr := simp)]
/--
lemma `lift_hom` / 引理 `lift_hom`

English:
lemma lift_hom
  given: (f : M ⟶ N₁) (g : M ⟶ N₂)
  statement: (lift f g).hom = lift f.hom g.hom
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 lift_hom
  条件: (f : M ⟶ N₁) (g : M ⟶ N₂)
  结论: (lift f g).hom = lift f.hom g.hom
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma lift_hom (f : M ⟶ N₁) (g : M ⟶ N₂) : (lift f g).hom = lift f.hom g.hom := rfl

@[to_additive (attr := simp)]
/--
lemma `fst_hom` / 引理 `fst_hom`

English:
lemma fst_hom
  given: (M N : Mon C)
  statement: (fst M N).hom = fst M.X N.X
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 fst_hom
  条件: (M N : 幺半群 C)
  结论: (fst M N).hom = fst M.X N.X
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma fst_hom (M N : Mon C) : (fst M N).hom = fst M.X N.X := rfl

@[to_additive (attr := simp)]
/--
lemma `snd_hom` / 引理 `snd_hom`

English:
lemma snd_hom
  given: (M N : Mon C)
  statement: (snd M N).hom = snd M.X N.X
  proof: rfl

中文:
引理 snd_hom
  条件: (M N : 幺半群 C)
  结论: (snd M N).hom = snd M.X N.X
  证明: rfl
-/
lemma snd_hom (M N : Mon C) : (snd M N).hom = snd M.X N.X := rfl

/-! ### Comm monoid objects are internal monoid objects -/

/-- A commutative monoid object is a monoid object in the category of monoid objects. -/
@[to_additive
/-- A commutative additive monoid object is an additive monoid object in the category
of additive monoid objects. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsCommMonObj
  signature: M.X] : MonObj M where
  body: .mk η[M.X]
  mul := .mk μ[M.X]

@[to_additive (attr := simp)]

中文:
实例 [是交换MonObj
  签名: M.X] : MonObj M where
  定义体: .mk η[M.X]
  mul := .mk μ[M.X]

@[to_additive (attr := simp)]
-/
instance [IsCommMonObj M.X] : MonObj M where
  one := .mk η[M.X]
  mul := .mk μ[M.X]

@[to_additive (attr := simp)]
/--
lemma `hom_one` / 引理 `hom_one`

English:
lemma hom_one
  given: (M : Mon C) [IsCommMonObj M.X]
  statement: η[M].hom = η[M.X]
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 hom_one
  条件: (M : 幺半群 C) [是交换MonObj M.X]
  结论: η[M].hom = η[M.X]
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma hom_one (M : Mon C) [IsCommMonObj M.X] : η[M].hom = η[M.X] := rfl

@[to_additive (attr := simp)]
/--
lemma `hom_mul` / 引理 `hom_mul`

English:
lemma hom_mul
  given: (M : Mon C) [IsCommMonObj M.X]
  statement: μ[M].hom = μ[M.X]
  proof: rfl

中文:
引理 hom_mul
  条件: (M : 幺半群 C) [是交换MonObj M.X]
  结论: μ[M].hom = μ[M.X]
  证明: rfl
-/
lemma hom_mul (M : Mon C) [IsCommMonObj M.X] : μ[M].hom = μ[M.X] := rfl

/-- A commutative monoid object is a commutative monoid object in the category of monoid objects. -/
@[to_additive
/-- A commutative additive monoid object is a commutative additive monoid object in the
category of additive monoid objects. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsCommMonObj
  signature: M.X] : IsCommMonObj M where

中文:
实例 [是交换MonObj
  签名: M.X] : 是交换MonObj M where
-/
instance [IsCommMonObj M.X] : IsCommMonObj M where

end Mon

variable (X) in
/-- If `X` represents a presheaf of monoids, then `X` is a monoid object. -/
@[to_additive (attr := simps, instance_reducible)
/-- If `X` represents a presheaf of additive monoids, then `X` is an additive monoid object. -/]
/--
Definition of `MonObj.ofRepresentableBy` / `MonObj.ofRepresentableBy` 的定义

English:
definition MonObj.ofRepresentableBy
  signature: (F : Cᵒᵖ ⥤ MonCat.{w}) (α : (F ⋙ forget _).RepresentableBy X)
  body: α.homEquiv'.symm 1
  mul := α.homEquiv'.symm (α.homEquiv' (fst X X) * α.homEquiv' (snd X X))
  one_mul := by
    apply α.homEquiv'.injective
    simp only [α.homEquiv'_comp, Equiv.apply_symm_apply, map_mul]
    simp only [← α.homEquiv'_comp]
    simp only [whiskerRight_fst, whiskerRight_snd, α.homEq

中文:
定义 MonObj.ofRepresentableBy
  签名: (F : Cᵒᵖ ⥤ 幺半群范畴.{w}) (α : (F ⋙ forget _).可表示 X)
  定义体: α.homEquiv'.symm 1
  mul := α.homEquiv'.symm (α.homEquiv' (fst X X) * α.homEquiv' (snd X X))
  one_mul := by
    apply α.homEquiv'.injective
    simp only [α.homEquiv'_comp, Equiv.apply_symm_apply, map_mul]
    simp only [← α.homEquiv'_comp]
    simp only [whiskerRight_fst, whiskerRight_snd, α.homEq

Depends on / 依赖: homEquiv
-/
def MonObj.ofRepresentableBy (F : Cᵒᵖ ⥤ MonCat.{w}) (α : (F ⋙ forget _).RepresentableBy X) :
    MonObj X where
  one := α.homEquiv'.symm 1
  mul := α.homEquiv'.symm (α.homEquiv' (fst X X) * α.homEquiv' (snd X X))
  one_mul := by
    apply α.homEquiv'.injective
    simp only [α.homEquiv'_comp, Equiv.apply_symm_apply, map_mul]
    simp only [← α.homEquiv'_comp]
    simp only [whiskerRight_fst, whiskerRight_snd, α.homEquiv'_comp, Equiv.apply_symm_apply]
    simp [leftUnitor_hom, -op_tensorObj, -op_whiskerRight, -op_tensorUnit]
  mul_one := by
    apply α.homEquiv'.injective
    simp only [α.homEquiv'_comp, Equiv.apply_symm_apply, map_mul]
    simp only [← α.homEquiv'_comp]
    simp only [whiskerLeft_fst, whiskerLeft_snd, α.homEquiv'_comp, Equiv.apply_symm_apply]
    simp [rightUnitor_hom, -op_tensorObj, -op_whiskerRight, -op_tensorUnit]
  mul_assoc := by
    apply α.homEquiv'.injective
    simp only [α.homEquiv'_comp, Equiv.apply_symm_apply, map_mul]
    simp only [← α.homEquiv'_comp]
    simp only [whiskerRight_fst, whiskerRight_snd, whiskerLeft_fst, associator_hom_fst,
      whiskerLeft_snd, α.homEquiv'_comp, Equiv.apply_symm_apply, map_mul, _root_.mul_assoc]
    simp only [← α.homEquiv'_comp]
    simp

/-- If `M` is a monoid object, then `Hom(X, M)` has a monoid structure. -/
@[to_additive
/-- If `M` is an additive monoid object, then `Hom(X, M)` has an additive monoid structure. -/]
/--
Definition of `Hom.monoid` / `Hom.monoid` 的定义

English:
abbreviation Hom.monoid
  signature: : Monoid (X ⟶ M) where
  body: lift f₁ f₂ ≫ μ
  mul_assoc f₁ f₂ f₃ := by
    change lift (lift f₁ f₂ ≫ μ) f₃ ≫ μ = lift f₁ (lift f₂ f₃ ≫ μ) ≫ μ
    trans lift (lift f₁ f₂) f₃ ≫ μ ▷ M ≫ μ
    · rw [← tensorHom_id, lift_map_assoc, Category.comp_id]
    trans lift f₁ (lift f₂ f₃) ≫ M ◁ μ ≫ μ
    · rw [MonObj.mul_assoc]
      simp_rw

中文:
缩写 态射.monoid
  签名: : 幺半群 (X ⟶ M) where
  定义体: lift f₁ f₂ ≫ μ
  mul_assoc f₁ f₂ f₃ := by
    change lift (lift f₁ f₂ ≫ μ) f₃ ≫ μ = lift f₁ (lift f₂ f₃ ≫ μ) ≫ μ
    trans lift (lift f₁ f₂) f₃ ≫ μ ▷ M ≫ μ
    · rw [← tensorHom_id, lift_map_assoc, Category.comp_id]
    trans lift f₁ (lift f₂ f₃) ≫ M ◁ μ ≫ μ
    · rw [MonObj.mul_assoc]
      simp_rw

Depends on / 依赖: NatIso, NatIso.ofComponents, Sheaf.homEquiv.toIso, homEquiv, ofComponents
-/
abbrev Hom.monoid : Monoid (X ⟶ M) where
  mul f₁ f₂ := lift f₁ f₂ ≫ μ
  mul_assoc f₁ f₂ f₃ := by
    change lift (lift f₁ f₂ ≫ μ) f₃ ≫ μ = lift f₁ (lift f₂ f₃ ≫ μ) ≫ μ
    trans lift (lift f₁ f₂) f₃ ≫ μ ▷ M ≫ μ
    · rw [← tensorHom_id, lift_map_assoc, Category.comp_id]
    trans lift f₁ (lift f₂ f₃) ≫ M ◁ μ ≫ μ
    · rw [MonObj.mul_assoc]
      simp_rw [← Category.assoc]
      congr 2
      ext <;> simp
    · rw [← id_tensorHom, lift_map_assoc, Category.comp_id]
  one := toUnit X ≫ η
  one_mul f := by
    change lift (toUnit _ ≫ η) f ≫ μ = f
    rw [← Category.comp_id f]; rw [← lift_map_assoc]; rw [tensorHom_id]; rw [MonObj.one_mul]; rw [Category.comp_id]; rw [leftUnitor_hom]
    exact lift_snd _ _
  mul_one f := by
    change lift f (toUnit _ ≫ η) ≫ μ = f
    rw [← Category.comp_id f]; rw [← lift_map_assoc]; rw [id_tensorHom]; rw [MonObj.mul_one]; rw [Category.comp_id]; rw [rightUnitor_hom]
    exact lift_fst _ _

scoped[CategoryTheory.MonObj] attribute [instance] Hom.monoid
scoped[CategoryTheory.AddMonObj] attribute [instance] Hom.addMonoid

@[to_additive]
/--
lemma `Hom.one_def` / 引理 `Hom.one_def`

English:
lemma Hom.one_def
  statement: (1 : X ⟶ M) = toUnit X ≫ η
  proof: rfl
@[to_additive]

中文:
引理 态射.one_def
  结论: (1 : X ⟶ M) = toUnit X ≫ η
  证明: rfl
@[to_additive]
-/
lemma Hom.one_def : (1 : X ⟶ M) = toUnit X ≫ η := rfl
@[to_additive]
/--
lemma `Hom.mul_def` / 引理 `Hom.mul_def`

English:
lemma Hom.mul_def
  given: (f₁ f₂ : X ⟶ M)
  statement: f₁ * f₂ = lift f₁ f₂ ≫ μ
  proof: rfl

中文:
引理 态射.mul_def
  条件: (f₁ f₂ : X ⟶ M)
  结论: f₁ * f₂ = lift f₁ f₂ ≫ μ
  证明: rfl
-/
lemma Hom.mul_def (f₁ f₂ : X ⟶ M) : f₁ * f₂ = lift f₁ f₂ ≫ μ := rfl

namespace Functor
variable (F : C ⥤ D) [F.Monoidal]

open scoped Obj

@[to_additive map_add']
/--
lemma `map_mul` / 引理 `map_mul`

English:
lemma map_mul
  given: (f g : X ⟶ M)
  statement: F.map (f * g) = F.map f * F.map g
  proof: by
  simp [Hom.mul_def]

@[to_additive (attr := simp) map_zero']

中文:
引理 map_mul
  条件: (f g : X ⟶ M)
  结论: F.map (f * g) = F.map f * F.map g
  证明: by
  simp [Hom.mul_def]

@[to_additive (attr := simp) map_zero']
-/
protected lemma map_mul (f g : X ⟶ M) : F.map (f * g) = F.map f * F.map g := by
  simp [Hom.mul_def]

@[to_additive (attr := simp) map_zero']
/--
lemma `map_one` / 引理 `map_one`

English:
lemma map_one
  statement: F.map (1 : X ⟶ M) = 1
  proof: by simp [Hom.one_def]

中文:
引理 map_one
  结论: F.map (1 : X ⟶ M) = 1
  证明: by simp [Hom.one_def]
-/
protected lemma map_one : F.map (1 : X ⟶ M) = 1 := by simp [Hom.one_def]

/-- `Functor.map` of a monoidal functor as a `MonoidHom`. -/
@[to_additive (attr := simps) /-- `Functor.map` of a monoidal functor as a `AddMonoidHom`. -/]
/--
Definition of `homMonoidHom` / `homMonoidHom` 的定义

English:
definition homMonoidHom
  signature: : (X ⟶ M) ->* (F.obj X ⟶ F.obj M) where
  body: F.map
  map_one' := F.map_one
  map_mul' := F.map_mul

中文:
定义 homMonoidHom
  签名: : (X ⟶ M) ->* (F.obj X ⟶ F.obj M) where
  定义体: F.map
  map_one' := F.map_one
  map_mul' := F.map_mul

Depends on / 依赖: F.map
-/
def homMonoidHom : (X ⟶ M) ->* (F.obj X ⟶ F.obj M) where
  toFun := F.map
  map_one' := F.map_one
  map_mul' := F.map_mul

/-- `Functor.map` of a fully faithful monoidal functor as a `MulEquiv`. -/
@[to_additive (attr := simps!)
/-- `Functor.map` of a fully faithful monoidal functor as a `AddEquiv`. -/]
/--
Definition of `FullyFaithful.homMulEquiv` / `FullyFaithful.homMulEquiv` 的定义

English:
definition FullyFaithful.homMulEquiv
  signature: (hF : F.FullyFaithful)
  body: hF.homEquiv
  __ := F.homMonoidHom

中文:
定义 满忠实.homMulEquiv
  签名: (hF : F.满忠实)
  定义体: hF.homEquiv
  __ := F.homMonoidHom

Depends on / 依赖: hF.homEquiv, homEquiv
-/
def FullyFaithful.homMulEquiv (hF : F.FullyFaithful) : (X ⟶ M) ≃* (F.obj X ⟶ F.obj M) where
  __ := hF.homEquiv
  __ := F.homMonoidHom

end Functor

section BraidedCategory
variable [BraidedCategory C]

/-- If `M` is a commutative monoid object, then `Hom(X, M)` has a commutative monoid structure. -/
@[to_additive
/-- If `M` is a commutative additive monoid object, then `Hom(X, M)` has a commutative additive
monoid structure. -/]
/--
Definition of `Hom.commMonoid` / `Hom.commMonoid` 的定义

English:
abbreviation Hom.commMonoid
  signature: [IsCommMonObj M]
  body: by simpa [-IsCommMonObj.mul_comm] using! lift g f ≫= IsCommMonObj.mul_comm M

中文:
缩写 态射.commMonoid
  签名: [是交换MonObj M]
  定义体: by simpa [-IsCommMonObj.mul_comm] using! lift g f ≫= IsCommMonObj.mul_comm M

Depends on / 依赖: IsCommMonObj, IsCommMonObj.mul_comm, mul_comm
-/
abbrev Hom.commMonoid [IsCommMonObj M] : CommMonoid (X ⟶ M) where
  mul_comm f g := by simpa [-IsCommMonObj.mul_comm] using! lift g f ≫= IsCommMonObj.mul_comm M

namespace Mon.Hom
variable {M N : Mon C} [IsCommMonObj N.X]

@[to_additive (attr := simp)]
/--
lemma `hom_one` / 引理 `hom_one`

English:
lemma hom_one
  statement: (1 : M ⟶ N).hom = 1
  proof: rfl
@[to_additive (attr := simp)]

中文:
引理 hom_one
  结论: (1 : M ⟶ N).hom = 1
  证明: rfl
@[to_additive (attr := simp)]
-/
lemma hom_one : (1 : M ⟶ N).hom = 1 := rfl
@[to_additive (attr := simp)]
/--
lemma `hom_mul` / 引理 `hom_mul`

English:
lemma hom_mul
  given: (f g : M ⟶ N)
  statement: (f * g).hom = f.hom * g.hom
  proof: rfl
@[to_additive (attr := simp)]

中文:
引理 hom_mul
  条件: (f g : M ⟶ N)
  结论: (f * g).hom = f.hom * g.hom
  证明: rfl
@[to_additive (attr := simp)]
-/
lemma hom_mul (f g : M ⟶ N) : (f * g).hom = f.hom * g.hom := rfl
@[to_additive (attr := simp)]
/--
lemma `hom_pow` / 引理 `hom_pow`

English:
lemma hom_pow
  given: (f : M ⟶ N) (n : Nat)
  statement: (f ^ n).hom = f.hom ^ n
  proof: by
  induction n <;> simp [pow_succ, *]

中文:
引理 hom_pow
  条件: (f : M ⟶ N) (n : 自然数)
  结论: (f ^ n).hom = f.hom ^ n
  证明: by
  induction n <;> simp [pow_succ, *]

Depends on / 依赖: pow_succ
-/
lemma hom_pow (f : M ⟶ N) (n : Nat) : (f ^ n).hom = f.hom ^ n := by
  induction n <;> simp [pow_succ, *]

end Mon.Hom

scoped[CategoryTheory.MonObj] attribute [instance] Hom.commMonoid Hom.addCommMonoid

end BraidedCategory

/-- A monoid morphism `f : M ⟶ N` induces a monoid homomorphism `M(X) →* N(X)` for every `X`. -/
@[to_additive (attr := simps!)
/-- An additive monoid morphism `f : M ⟶ N` induces an additive monoid homomorphism
`M(X) →+ N(X)` for every `X`. -/]
/--
Definition of `IsMonHom.monoidHom` / `IsMonHom.monoidHom` 的定义

English:
definition IsMonHom.monoidHom
  signature: (f : M ⟶ N) [IsMonHom f] (X : C)
  body: (· ≫ f)
  map_one' := by simp [Hom.one_def]
  map_mul' := by simp [Hom.mul_def]

@[to_additive (attr := simp)]

中文:
定义 是幺半群态射.monoidHom
  签名: (f : M ⟶ N) [是幺半群态射 f] (X : C)
  定义体: (· ≫ f)
  map_one' := by simp [Hom.one_def]
  map_mul' := by simp [Hom.mul_def]

@[to_additive (attr := simp)]
-/
def IsMonHom.monoidHom (f : M ⟶ N) [IsMonHom f] (X : C) : (X ⟶ M) ->* (X ⟶ N) where
  toFun := (· ≫ f)
  map_one' := by simp [Hom.one_def]
  map_mul' := by simp [Hom.mul_def]

@[to_additive (attr := simp)]
/--
lemma `IsMonHom.monoidHom_id` / 引理 `IsMonHom.monoidHom_id`

English:
lemma IsMonHom.monoidHom_id
  statement: IsMonHom.monoidHom (𝟙 M) X = MonoidHom.id _
  proof: by
  cat_disch

@[to_additive (attr := simp)]

中文:
引理 是幺半群态射.monoidHom_id
  结论: 是幺半群态射.monoidHom (𝟙 M) X = 幺半群态射.id _
  证明: by
  cat_disch

@[to_additive (attr := simp)]

Depends on / 依赖: cat_disch
-/
lemma IsMonHom.monoidHom_id : IsMonHom.monoidHom (𝟙 M) X = MonoidHom.id _ := by
  cat_disch

@[to_additive (attr := simp)]
/--
lemma `IsMonHom.monoidHom_comp` / 引理 `IsMonHom.monoidHom_comp`

English:
lemma IsMonHom.monoidHom_comp
  given: (f : M ⟶ N) (g : N ⟶ O) [IsMonHom f] [IsMonHom g]
  proof: by
  cat_disch

中文:
引理 是幺半群态射.monoidHom_comp
  条件: (f : M ⟶ N) (g : N ⟶ O) [是幺半群态射 f] [是幺半群态射 g]
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma IsMonHom.monoidHom_comp (f : M ⟶ N) (g : N ⟶ O) [IsMonHom f] [IsMonHom g] :
    IsMonHom.monoidHom (f ≫ g) X = MonoidHom.comp (monoidHom g X) (monoidHom f X) := by
  cat_disch

variable (M) in
/-- If `M` is a monoid object, then `Hom(-, M)` is a presheaf of monoids. -/
@[to_additive (attr := simps)
/-- If `M` is an additive monoid object, then `Hom(-, M)` is a presheaf of additive monoids. -/]
/--
Definition of `yonedaMonObj` / `yonedaMonObj` 的定义

English:
definition yonedaMonObj
  signature: : Cᵒᵖ ⥤ MonCat.{v} where
  body: MonCat.of (unop X ⟶ M)
  map {X Y₂} φ := MonCat.ofHom
    { toFun := (φ.unop ≫ ·)
      map_one' := by
        change φ.unop ≫ toUnit _ ≫ η = toUnit _ ≫ η
        rw [← Category.assoc]; rw [toUnit_unique (φ.unop ≫ toUnit _)]
      map_mul' f₁ f₂ := by
        change φ.unop ≫ lift f₁ f₂ ≫ μ = lift (φ

中文:
定义 yonedaMonObj
  签名: : Cᵒᵖ ⥤ 幺半群范畴.{v} where
  定义体: MonCat.of (unop X ⟶ M)
  map {X Y₂} φ := MonCat.ofHom
    { toFun := (φ.unop ≫ ·)
      map_one' := by
        change φ.unop ≫ toUnit _ ≫ η = toUnit _ ≫ η
        rw [← Category.assoc]; rw [toUnit_unique (φ.unop ≫ toUnit _)]
      map_mul' f₁ f₂ := by
        change φ.unop ≫ lift f₁ f₂ ≫ μ = lift (φ

Depends on / 依赖: MonCat, MonCat.of
-/
def yonedaMonObj : Cᵒᵖ ⥤ MonCat.{v} where
  obj X := MonCat.of (unop X ⟶ M)
  map {X Y₂} φ := MonCat.ofHom
    { toFun := (φ.unop ≫ ·)
      map_one' := by
        change φ.unop ≫ toUnit _ ≫ η = toUnit _ ≫ η
        rw [← Category.assoc]; rw [toUnit_unique (φ.unop ≫ toUnit _)]
      map_mul' f₁ f₂ := by
        change φ.unop ≫ lift f₁ f₂ ≫ μ = lift (φ.unop ≫ f₁) (φ.unop ≫ f₂) ≫ μ
        rw [← Category.assoc]
        cat_disch }
  map_id _ := MonCat.hom_ext (MonoidHom.ext Category.id_comp)
  map_comp _ _ := MonCat.hom_ext (MonoidHom.ext (Category.assoc _ _))

variable (X) in
/-- If `X` represents a presheaf of monoids `F`, then `Hom(-, X)` is isomorphic to `F` as
a presheaf of monoids. -/
@[to_additive (attr := simps!)
/-- If `X` represents a presheaf of additive monoids `F`, then `Hom(-, X)` is isomorphic
to `F` as a presheaf of additive monoids. -/]
/--
Definition of `yonedaMonObjIsoOfRepresentableBy` / `yonedaMonObjIsoOfRepresentableBy` 的定义

English:
definition yonedaMonObjIsoOfRepresentableBy
  body: MonObj.ofRepresentableBy X F α
    yonedaMonObj X ≅ F :=
  letI := MonObj.ofRepresentableBy X F α
  NatIso.ofComponents (fun Y => MulEquiv.toMonCatIso
    { toEquiv := α.homEquiv'
      map_mul' f₁ f₂ := by
        change α.homEquiv' (lift f₁ f₂ ≫ α.homEquiv'.symm (α.homEquiv' (fst X X) *
          

中文:
定义 yonedaMonObjIsoOfRepresentableBy
  定义体: MonObj.ofRepresentableBy X F α
    yonedaMonObj X ≅ F :=
  letI := MonObj.ofRepresentableBy X F α
  NatIso.ofComponents (fun Y => MulEquiv.toMonCatIso
    { toEquiv := α.homEquiv'
      map_mul' f₁ f₂ := by
        change α.homEquiv' (lift f₁ f₂ ≫ α.homEquiv'.symm (α.homEquiv' (fst X X) *
          

Depends on / 依赖: MonObj, MonObj.ofRepresentableBy, ofRepresentableBy
-/
def yonedaMonObjIsoOfRepresentableBy
    (F : Cᵒᵖ ⥤ MonCat.{v}) (α : (F ⋙ forget _).RepresentableBy X) :
    letI := MonObj.ofRepresentableBy X F α
    yonedaMonObj X ≅ F :=
  letI := MonObj.ofRepresentableBy X F α
  NatIso.ofComponents (fun Y => MulEquiv.toMonCatIso
    { toEquiv := α.homEquiv'
      map_mul' f₁ f₂ := by
        change α.homEquiv' (lift f₁ f₂ ≫ α.homEquiv'.symm (α.homEquiv' (fst X X) *
          α.homEquiv' (snd X X))) = α.homEquiv' f₁ * α.homEquiv' f₂
        simp only [α.homEquiv'_comp, Equiv.apply_symm_apply, map_mul]
        simp only [← α.homEquiv'_comp]
        simp }) (fun φ => MonCat.hom_ext (MonoidHom.ext (α.homEquiv'_comp φ.unop)))

/-- The yoneda embedding of `Mon C` into presheaves of monoids. -/
@[to_additive (attr := simps)
/-- The yoneda embedding of `AddMon C` into presheaves of additive monoids. -/]
/--
Definition of `yonedaMon` / `yonedaMon` 的定义

English:
definition yonedaMon
  signature: : Mon C ⥤ Cᵒᵖ ⥤ MonCat.{v} where
  body: yonedaMonObj M.X
  map ψ :=
  { app _ := MonCat.ofHom <| IsMonHom.monoidHom _ _
naturality {_ _} φ := MonCat.hom_ext MonoidHom.ext fun f => Category.assoc φ.unop f ψ.hom }
map_id _ := NatTrans.ext funext fun _ => MonCat.hom_ext IsMonHom.monoidHom_id
map_comp _ _ := NatTrans.ext funext fun _ => MonCa

中文:
定义 yonedaMon
  签名: : 幺半群 C ⥤ Cᵒᵖ ⥤ 幺半群范畴.{v} where
  定义体: yonedaMonObj M.X
  map ψ :=
  { app _ := MonCat.ofHom <| IsMonHom.monoidHom _ _
naturality {_ _} φ := MonCat.hom_ext MonoidHom.ext fun f => Category.assoc φ.unop f ψ.hom }
map_id _ := NatTrans.ext funext fun _ => MonCat.hom_ext IsMonHom.monoidHom_id
map_comp _ _ := NatTrans.ext funext fun _ => MonCa

Depends on / 依赖: yonedaMonObj
-/
def yonedaMon : Mon C ⥤ Cᵒᵖ ⥤ MonCat.{v} where
  obj M := yonedaMonObj M.X
  map ψ :=
  { app _ := MonCat.ofHom <| IsMonHom.monoidHom _ _
naturality {_ _} φ := MonCat.hom_ext MonoidHom.ext fun f => Category.assoc φ.unop f ψ.hom }
map_id _ := NatTrans.ext funext fun _ => MonCat.hom_ext IsMonHom.monoidHom_id
map_comp _ _ := NatTrans.ext funext fun _ => MonCat.hom_ext IsMonHom.monoidHom_comp _ _

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[to_additive (attr := reassoc)]
/--
lemma `yonedaMon_naturality` / 引理 `yonedaMon_naturality`

English:
lemma yonedaMon_naturality
  given: (α : yonedaMonObj M ⟶ yonedaMonObj N) (f : X ⟶ Y) (g : Y ⟶ M)
  proof: congr($(α.naturality f.op) g)

中文:
引理 yonedaMon_naturality
  条件: (α : yonedaMonObj M ⟶ yonedaMonObj N) (f : X ⟶ Y) (g : Y ⟶ M)
  证明: congr($(α.naturality f.op) g)

Depends on / 依赖: f.op, naturality
-/
lemma yonedaMon_naturality (α : yonedaMonObj M ⟶ yonedaMonObj N) (f : X ⟶ Y) (g : Y ⟶ M) :
      α.app _ (f ≫ g) = f ≫ α.app _ g := congr($(α.naturality f.op) g)

variable (M) in
/-- If `M` is a monoid object, then `Hom(-, M)` as a presheaf of monoids is represented by `M`. -/
@[to_additive
/-- If `M` is an additive monoid object, then `Hom(-, M)` as a presheaf of additive monoids
is represented by `M`. -/]
/--
Definition of `yonedaMonObjRepresentableBy` / `yonedaMonObjRepresentableBy` 的定义

English:
definition yonedaMonObjRepresentableBy
  signature: : (yonedaMonObj M ⋙ forget _).RepresentableBy M
  body: Functor.representableByEquiv.symm (.refl _)

中文:
定义 yonedaMonObjRepresentableBy
  签名: : (yonedaMonObj M ⋙ forget _).可表示 M
  定义体: Functor.representableByEquiv.symm (.refl _)

Depends on / 依赖: Functor, Functor.representableByEquiv.symm, representableByEquiv
-/
def yonedaMonObjRepresentableBy : (yonedaMonObj M ⋙ forget _).RepresentableBy M :=
  Functor.representableByEquiv.symm (.refl _)

variable (M) in
@[to_additive]
/--
lemma `MonObj.ofRepresentableBy_yonedaMonObjRepresentableBy` / 引理 `MonObj.ofRepresentableBy_yonedaMonObjRepresentableBy`

English:
lemma MonObj.ofRepresentableBy_yonedaMonObjRepresentableBy
  proof: by
  ext; change lift (fst M M) (snd M M) ≫ μ = μ; rw [lift_fst_snd, Category.id_comp]

中文:
引理 MonObj.ofRepresentableBy_yonedaMonObjRepresentableBy
  证明: by
  ext; change lift (fst M M) (snd M M) ≫ μ = μ; rw [lift_fst_snd, Category.id_comp]

Depends on / 依赖: Category, Category.id_comp, id_comp, lift_fst_snd
-/
lemma MonObj.ofRepresentableBy_yonedaMonObjRepresentableBy :
    ofRepresentableBy M _ (yonedaMonObjRepresentableBy M) = ‹_› := by
  ext; change lift (fst M M) (snd M M) ≫ μ = μ; rw [lift_fst_snd, Category.id_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The yoneda embedding for `Mon C` is fully faithful. -/
@[to_additive /-- The yoneda embedding for `AddMon C` is fully faithful. -/]
/--
Definition of `yonedaMonFullyFaithful` / `yonedaMonFullyFaithful` 的定义

English:
definition yonedaMonFullyFaithful
  signature: : yonedaMon (C := C).FullyFaithful where
  body: { hom := α.app (op M.X) (𝟙 M.X)
      isMonHom_hom.one_hom := by
          dsimp only [yonedaMon_obj] at α ⊢
          rw [← yonedaMon_naturality]; rw [Category.comp_id]; rw [← Category.id_comp η[M.X], toUnit_unique (𝟙 _) (toUnit _),
            ← Category.id_comp η[N.X], toUnit_unique (𝟙 _) (toUnit

中文:
定义 yonedaMonFullyFaithful
  签名: : yonedaMon (C := C).满忠实 where
  定义体: { hom := α.app (op M.X) (𝟙 M.X)
      isMonHom_hom.one_hom := by
          dsimp only [yonedaMon_obj] at α ⊢
          rw [← yonedaMon_naturality]; rw [Category.comp_id]; rw [← Category.id_comp η[M.X], toUnit_unique (𝟙 _) (toUnit _),
            ← Category.id_comp η[N.X], toUnit_unique (𝟙 _) (toUnit

Depends on / 依赖: FullyFaithful
-/
def yonedaMonFullyFaithful : yonedaMon (C := C).FullyFaithful where
  preimage {M N} α :=
    { hom := α.app (op M.X) (𝟙 M.X)
      isMonHom_hom.one_hom := by
          dsimp only [yonedaMon_obj] at α ⊢
          rw [← yonedaMon_naturality]; rw [Category.comp_id]; rw [← Category.id_comp η[M.X], toUnit_unique (𝟙 _) (toUnit _),
            ← Category.id_comp η[N.X], toUnit_unique (𝟙 _) (toUnit _)]
          exact (α.app _).hom.map_one
      isMonHom_hom.mul_hom := by
        dsimp only [yonedaMon_obj] at α ⊢
        rw [← yonedaMon_naturality]; rw [Category.comp_id]; rw [← Category.id_comp μ[M.X], ← lift_fst_snd]
        refine ((α.app _).hom.map_mul _ _).trans ?_
        change lift _ _ ≫ μ[N.X] = _
        congr 1
        ext <;> simp only [lift_fst, tensorHom_fst, lift_snd, tensorHom_snd,
          ← yonedaMon_naturality, Category.comp_id] }
  map_preimage {M N} α := by
    ext Y f
    simp [← dsimp% yonedaMon_naturality]
  preimage_map φ := Mon.Hom.ext (Category.id_comp φ.hom)

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: yonedaMon (C := C).Full
  body: yonedaMonFullyFaithful.full
@[to_additive]

中文:
实例 :
  签名: yonedaMon (C := C).满
  定义体: yonedaMonFullyFaithful.full
@[to_additive]

Depends on / 依赖: yonedaMonFullyFaithful, yonedaMonFullyFaithful.full
-/
instance : yonedaMon (C := C).Full := yonedaMonFullyFaithful.full
@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: yonedaMon (C := C).Faithful
  body: yonedaMonFullyFaithful.faithful

@[to_additive]

中文:
实例 :
  签名: yonedaMon (C := C).忠实
  定义体: yonedaMonFullyFaithful.faithful

@[to_additive]

Depends on / 依赖: Faithful, faithful, yonedaMonFullyFaithful, yonedaMonFullyFaithful.faithful
-/
instance : yonedaMon (C := C).Faithful := yonedaMonFullyFaithful.faithful

@[to_additive]
/--
lemma `essImage_yonedaMon` / 引理 `essImage_yonedaMon`

English:
lemma essImage_yonedaMon
  proof: by
  ext F
  constructor
  · rintro ⟨M, ⟨α⟩⟩
    exact ⟨M.X, ⟨Functor.representableByEquiv.symm (Functor.isoWhiskerRight α (forget _))⟩⟩
  · rintro ⟨X, ⟨e⟩⟩
    let := MonObj.ofRepresentableBy X F e
    exact ⟨Mon.mk X, ⟨yonedaMonObjIsoOfRepresentableBy X F e⟩⟩

@[to_additive (attr := reassoc (attr 

中文:
引理 essImage_yonedaMon
  证明: by
  ext F
  constructor
  · rintro ⟨M, ⟨α⟩⟩
    exact ⟨M.X, ⟨Functor.representableByEquiv.symm (Functor.isoWhiskerRight α (forget _))⟩⟩
  · rintro ⟨X, ⟨e⟩⟩
    let := MonObj.ofRepresentableBy X F e
    exact ⟨Mon.mk X, ⟨yonedaMonObjIsoOfRepresentableBy X F e⟩⟩

@[to_additive (attr := reassoc (attr 

Depends on / 依赖: Functor, Functor.isoWhiskerRight, Functor.representableByEquiv.symm, IsRepresentable, Mon.mk, MonObj, MonObj.ofRepresentableBy, essImage, forget, isoWhiskerRight, ofRepresentableBy, representableByEquiv, yonedaMonObjIsoOfRepresentableBy
-/
lemma essImage_yonedaMon :
    yonedaMon (C := C).essImage = fun F => (F ⋙ forget _).IsRepresentable := by
  ext F
  constructor
  · rintro ⟨M, ⟨α⟩⟩
    exact ⟨M.X, ⟨Functor.representableByEquiv.symm (Functor.isoWhiskerRight α (forget _))⟩⟩
  · rintro ⟨X, ⟨e⟩⟩
    let := MonObj.ofRepresentableBy X F e
    exact ⟨Mon.mk X, ⟨yonedaMonObjIsoOfRepresentableBy X F e⟩⟩

@[to_additive (attr := reassoc (attr := simp))]
/--
lemma `MonObj.one_comp` / 引理 `MonObj.one_comp`

English:
lemma MonObj.one_comp
  given: (f : M ⟶ N) [IsMonHom f]
  statement: (1 : X ⟶ M) ≫ f = 1
  proof: by simp [Hom.one_def]

@[to_additive (attr := reassoc)]

中文:
引理 MonObj.one_comp
  条件: (f : M ⟶ N) [是幺半群态射 f]
  结论: (1 : X ⟶ M) ≫ f = 1
  证明: by simp [Hom.one_def]

@[to_additive (attr := reassoc)]

Depends on / 依赖: Hom.one_def, one_def
-/
lemma MonObj.one_comp (f : M ⟶ N) [IsMonHom f] : (1 : X ⟶ M) ≫ f = 1 := by simp [Hom.one_def]

@[to_additive (attr := reassoc)]
/--
lemma `MonObj.mul_comp` / 引理 `MonObj.mul_comp`

English:
lemma MonObj.mul_comp
  given: (f₁ f₂ : X ⟶ M) (g : M ⟶ N) [IsMonHom g]
  proof: by simp [Hom.mul_def]

@[to_additive (attr := reassoc)]

中文:
引理 MonObj.mul_comp
  条件: (f₁ f₂ : X ⟶ M) (g : M ⟶ N) [是幺半群态射 g]
  证明: by simp [Hom.mul_def]

@[to_additive (attr := reassoc)]

Depends on / 依赖: Hom.mul_def, mul_def
-/
lemma MonObj.mul_comp (f₁ f₂ : X ⟶ M) (g : M ⟶ N) [IsMonHom g] :
    (f₁ * f₂) ≫ g = f₁ ≫ g * f₂ ≫ g := by simp [Hom.mul_def]

@[to_additive (attr := reassoc)]
/--
lemma `MonObj.pow_comp` / 引理 `MonObj.pow_comp`

English:
lemma MonObj.pow_comp
  given: (f : X ⟶ M) (n : Nat) (g : M ⟶ N) [IsMonHom g]
  proof: by
  induction n <;> simp [pow_succ, MonObj.mul_comp, *]

@[to_additive (attr := reassoc (attr := simp))]

中文:
引理 MonObj.pow_comp
  条件: (f : X ⟶ M) (n : 自然数) (g : M ⟶ N) [是幺半群态射 g]
  证明: by
  induction n <;> simp [pow_succ, MonObj.mul_comp, *]

@[to_additive (attr := reassoc (attr := simp))]

Depends on / 依赖: MonObj, MonObj.mul_comp, mul_comp, pow_succ
-/
lemma MonObj.pow_comp (f : X ⟶ M) (n : Nat) (g : M ⟶ N) [IsMonHom g] :
    (f ^ n) ≫ g = (f ≫ g) ^ n := by
  induction n <;> simp [pow_succ, MonObj.mul_comp, *]

@[to_additive (attr := reassoc (attr := simp))]
/--
lemma `MonObj.comp_one` / 引理 `MonObj.comp_one`

English:
lemma MonObj.comp_one
  given: (f : X ⟶ Y)
  statement: f ≫ (1 : Y ⟶ M) = 1
  proof: ((yonedaMon.obj <| .mk M).map f.op).hom.map_one

@[to_additive (attr := reassoc)]

中文:
引理 MonObj.comp_one
  条件: (f : X ⟶ Y)
  结论: f ≫ (1 : Y ⟶ M) = 1
  证明: ((yonedaMon.obj <| .mk M).map f.op).hom.map_one

@[to_additive (attr := reassoc)]

Depends on / 依赖: f.op, hom.map_one, map_one, yonedaMon, yonedaMon.obj
-/
lemma MonObj.comp_one (f : X ⟶ Y) : f ≫ (1 : Y ⟶ M) = 1 :=
  ((yonedaMon.obj <| .mk M).map f.op).hom.map_one

@[to_additive (attr := reassoc)]
/--
lemma `MonObj.comp_mul` / 引理 `MonObj.comp_mul`

English:
lemma MonObj.comp_mul
  given: (f : X ⟶ Y) (g₁ g₂ : Y ⟶ M)
  statement: f ≫ (g₁ * g₂) = f ≫ g₁ * f ≫ g₂
  proof: ((yonedaMon.obj <| .mk M).map f.op).hom.map_mul _ _

@[to_additive (attr := reassoc)]

中文:
引理 MonObj.comp_mul
  条件: (f : X ⟶ Y) (g₁ g₂ : Y ⟶ M)
  结论: f ≫ (g₁ * g₂) = f ≫ g₁ * f ≫ g₂
  证明: ((yonedaMon.obj <| .mk M).map f.op).hom.map_mul _ _

@[to_additive (attr := reassoc)]

Depends on / 依赖: f.op, hom.map_mul, map_mul, yonedaMon, yonedaMon.obj
-/
lemma MonObj.comp_mul (f : X ⟶ Y) (g₁ g₂ : Y ⟶ M) : f ≫ (g₁ * g₂) = f ≫ g₁ * f ≫ g₂ :=
  ((yonedaMon.obj <| .mk M).map f.op).hom.map_mul _ _

@[to_additive (attr := reassoc)]
/--
lemma `MonObj.comp_pow` / 引理 `MonObj.comp_pow`

English:
lemma MonObj.comp_pow
  given: (f : X ⟶ M) (n : Nat) (h : Y ⟶ X)
  statement: h ≫ f ^ n = (h ≫ f) ^ n
  proof: by
  induction n <;> simp [pow_succ, MonObj.comp_mul, *]

中文:
引理 MonObj.comp_pow
  条件: (f : X ⟶ M) (n : 自然数) (h : Y ⟶ X)
  结论: h ≫ f ^ n = (h ≫ f) ^ n
  证明: by
  induction n <;> simp [pow_succ, MonObj.comp_mul, *]

Depends on / 依赖: MonObj, MonObj.comp_mul, comp_mul, pow_succ
-/
lemma MonObj.comp_pow (f : X ⟶ M) (n : Nat) (h : Y ⟶ X) : h ≫ f ^ n = (h ≫ f) ^ n := by
  induction n <;> simp [pow_succ, MonObj.comp_mul, *]

variable (M) in
@[to_additive]
/--
lemma `MonObj.one_eq_one` / 引理 `MonObj.one_eq_one`

English:
lemma MonObj.one_eq_one
  statement: η = (1 : _ ⟶ M)
  proof: show _ = _ ≫ _ by rw [toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

中文:
引理 MonObj.one_eq_one
  结论: η = (1 : _ ⟶ M)
  证明: show _ = _ ≫ _ by rw [toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

Depends on / 依赖: Category, Category.id_comp, id_comp, sheafToPresheaf, toUnit, toUnit_unique
-/
lemma MonObj.one_eq_one : η = (1 : _ ⟶ M) :=
  show _ = _ ≫ _ by rw [toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

variable (M) in
@[to_additive]
/--
lemma `MonObj.mul_eq_mul` / 引理 `MonObj.mul_eq_mul`

English:
lemma MonObj.mul_eq_mul
  statement: μ = fst M M * snd _ _
  proof: show _ = _ ≫ _ by rw [lift_fst_snd, Category.id_comp]

中文:
引理 MonObj.mul_eq_mul
  结论: μ = fst M M * snd _ _
  证明: show _ = _ ≫ _ by rw [lift_fst_snd, Category.id_comp]

Depends on / 依赖: Category, Category.id_comp, id_comp, lift_fst_snd
-/
lemma MonObj.mul_eq_mul : μ = fst M M * snd _ _ :=
  show _ = _ ≫ _ by rw [lift_fst_snd, Category.id_comp]

namespace Hom

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- If `M` and `N` are isomorphic as monoid objects, then `X ⟶ M` and `X ⟶ N` are isomorphic
monoids. -/
@[to_additive (attr := simps!)
/-- If `M` and `N` are isomorphic as additive monoid objects, then `X ⟶ M` and `X ⟶ N`
are isomorphic additive monoids. -/]
/--
Definition of `mulEquivCongrRight` / `mulEquivCongrRight` 的定义

English:
definition mulEquivCongrRight
  signature: (e : M ≅ N) [IsMonHom e.hom] (X : C)
  body: ((yonedaMon.mapIso <| Mon.mkIso' e).app <| .op X).monCatIsoToMulEquiv

中文:
定义 mulEquivCongrRight
  签名: (e : M ≅ N) [是幺半群态射 e.hom] (X : C)
  定义体: ((yonedaMon.mapIso <| Mon.mkIso' e).app <| .op X).monCatIsoToMulEquiv

Depends on / 依赖: Mon.mkIso, mapIso, monCatIsoToMulEquiv, yonedaMon, yonedaMon.mapIso
-/
def mulEquivCongrRight (e : M ≅ N) [IsMonHom e.hom] (X : C) : (X ⟶ M) ≃* (X ⟶ N) :=
  ((yonedaMon.mapIso <| Mon.mkIso' e).app <| .op X).monCatIsoToMulEquiv

end Hom

open scoped IsMulCommutative in
/-- A monoid object `M` is commutative if and only if `X ⟶ M` is commutative for all `X`. -/
@[to_additive
/-- An additive monoid object `M` is commutative if and only if `X ⟶ M` is commutative for all
`X`. -/]
/--
lemma `isCommMonObj_iff_isMulCommutative` / 引理 `isCommMonObj_iff_isMulCommutative`

English:
lemma isCommMonObj_iff_isMulCommutative
  given: (M : C) [MonObj M] [BraidedCategory C]
  proof: by
  exact ⟨fun h X => ⟨⟨by simp [mul_comm]⟩⟩, fun h => ⟨by simp [mul_eq_mul, comp_mul, mul_comm]⟩⟩

中文:
引理 isCommMonObj_iff_isMulCommutative
  条件: (M : C) [MonObj M] [辫范畴 C]
  证明: by
  exact ⟨fun h X => ⟨⟨by simp [mul_comm]⟩⟩, fun h => ⟨by simp [mul_eq_mul, comp_mul, mul_comm]⟩⟩

Depends on / 依赖: comp_mul, mul_comm, mul_eq_mul
-/
lemma isCommMonObj_iff_isMulCommutative (M : C) [MonObj M] [BraidedCategory C] :
    IsCommMonObj M ↔ forall (X : C), IsMulCommutative (X ⟶ M) := by
  exact ⟨fun h X => ⟨⟨by simp [mul_comm]⟩⟩, fun h => ⟨by simp [mul_eq_mul, comp_mul, mul_comm]⟩⟩

end CategoryTheory
