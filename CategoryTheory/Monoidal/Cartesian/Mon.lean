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
/-
**CategoryTheory.MonObj.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.MonObj`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (M : D) [MonObj M] : IsMonHom (toUnit M) where

@[to_additive]
/-
**CategoryTheory.MonObj.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.MonObj`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (M : D) [MonObj M] : IsMonHom η[M] where
  mul_hom := by simp [toUnit_unique (ρ_ (𝟙_ D)).hom (λ_ (𝟙_ D)).hom]

-- The general `(f : 𝟙_ C ⟶ X) : Mono f` instance has a bad discrimination tree key.
@[to_additive]
/-
**CategoryTheory.MonObj.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.MonObj`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (M : D) [MonObj M] : Mono η[M] := Limits.IsTerminal.mono_from isTerminalTensorUnit _

end MonObj

set_option backward.defeqAttrib.useBackward true in
@[to_additive (attr := simps)]
/-
**CategoryTheory.Mon.uniqueHomToTrivial** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Mon`。
形式化陈述：{D : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} D] →     [in
st_1 : CategoryTheory.SemiCartesianMonoidalCategory D] →       (A : CategoryTheo
ry.Mon D) → Unique (A ⟶ CategoryTheory.Mon.trivial D)
参数：A : CategoryTheory.Mon D；A ⟶ CategoryTheory.Mon.trivial D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Mon.uniqueHomToTrivial (A : Mon D) : Unique (A ⟶ Mon.trivial D) where
  default.hom := toUnit A.X
  default.isMonHom_hom.mul_hom := toUnit_unique _ _
  uniq f := Mon.Hom.ext (toUnit_unique _ _)

@[deprecated (since := "2026-03-20")] alias uniqueHomToTrivial := Mon.uniqueHomToTrivial

namespace Mon

variable (D) in
@[to_additive]
/-
**CategoryTheory.Mon.isZero_trivial** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Mo
n`。
形式化陈述：isZero_trivial : IsZero (Mon.trivial D) where unique_to A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_unique`：nonempty_unique (α : Sort u) [Subsingleton α] [Nonempty
 α] : Nonempty (Unique α)
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma isZero_trivial : IsZero (Mon.trivial D) where
  unique_to A := nonempty_unique (Mon.trivial D ⟶ A)
  unique_from A := nonempty_unique (A ⟶ Mon.trivial D)

@[to_additive]
/-
**CategoryTheory.Mon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasZeroObject (Mon D) where
  zero := ⟨Mon.trivial D, Mon.isZero_trivial D⟩

@[to_additive]
/-
**CategoryTheory.Mon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (M N : Mon D) : Zero (M ⟶ N) where
  zero := ⟨toUnit _ ≫ η⟩

@[to_additive (attr := simp)]
/-
**CategoryTheory.Mon.zero_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Mon`。
形式化陈述：zero_hom (M N : Mon D) : (0 : M ⟶ N).hom = toUnit _ ≫ η
参数：M N : Mon D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zero_hom (M N : Mon D) : (0 : M ⟶ N).hom = toUnit _ ≫ η := rfl

@[to_additive]
/-
**CategoryTheory.Mon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**CategoryTheory.MonObj.lift_lift_assoc** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.MonObj`。
形式化陈述：lift_lift_assoc {A : C} {B : C} [MonObj B] (f g h : A ⟶ B) : lift (lift f 
g ≫ μ) h ≫ μ = lift f (lift g h ≫ μ) ≫ μ
参数：f g h : A ⟶ B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.whisker_eq`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {X Y Z : C} {f g : Y ⟶ X} (h : Z ⟶ Y),   f = g → CategoryTheory.Cate
goryStruct.comp…
· 使用定理 `CategoryTheory.MonObj.mul_assoc`：∀ {C : Type u₁} {inst : CategoryTheory.
Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} (X : C)   [sel
f : CategoryTheory.Mo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.lift_whiskerLeft_assoc`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Carte
sianMonoidalCategory C]   {X Y Z W : C} (f : X ⟶ Y) (…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.lift_lift_associator_hom_assoc`
：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheo
ry.CartesianMonoidalCategory C]   {X Y Z W : C} (f : X ⟶ Y) (…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.lift_whiskerRight_assoc`：∀ {C :
 Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Cart
esianMonoidalCategory C]   {X Y Z W : C} (f : X ⟶ Y) (…
-/
theorem lift_lift_assoc {A : C} {B : C} [MonObj B] (f g h : A ⟶ B) :
    lift (lift f g ≫ μ) h ≫ μ = lift f (lift g h ≫ μ) ≫ μ := by
  have := lift (lift f g) h ≫= mul_assoc B
  rwa [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc] at this

@[to_additive (attr := reassoc (attr := simp))]
/-
**CategoryTheory.MonObj.lift_comp_one_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.MonObj`。
形式化陈述：lift_comp_one_left {A : C} {B : C} [MonObj B] (f : A ⟶ 𝟙_ C) (g : A ⟶ B) :
 lift (f ≫ η) g ≫ μ = g
参数：f : A ⟶ 𝟙_ C；g : A ⟶ B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.whisker_eq`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {X Y Z : C} {f g : Y ⟶ X} (h : Z ⟶ Y),   f = g → CategoryTheory.Cate
goryStruct.comp…
· 使用定理 `CategoryTheory.MonObj.one_mul`：∀ {C : Type u₁} {inst : CategoryTheory.Ca
tegory.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} (X : C)   [self 
: CategoryTheory.Mo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_leftUnitor_hom`：lift_leftU
nitor_hom {X Y : C} (f : X ⟶ 𝟙_ C) (g : X ⟶ Y) : lift f g ≫ (fun_ Y).hom = g
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.lift_whiskerRight_assoc`：∀ {C :
 Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Cart
esianMonoidalCategory C]   {X Y Z W : C} (f : X ⟶ Y) (…
-/
theorem lift_comp_one_left {A : C} {B : C} [MonObj B] (f : A ⟶ 𝟙_ C) (g : A ⟶ B) :
    lift (f ≫ η) g ≫ μ = g := by
  have := lift f g ≫= one_mul B
  rwa [lift_whiskerRight_assoc, lift_leftUnitor_hom] at this

@[to_additive (attr := reassoc (attr := simp))]
/-
**CategoryTheory.MonObj.lift_comp_one_right** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.MonObj`。
形式化陈述：lift_comp_one_right {A : C} {B : C} [MonObj B] (f : A ⟶ B) (g : A ⟶ 𝟙_ C) 
: lift f (g ≫ η) ≫ μ = f
参数：f : A ⟶ B；g : A ⟶ 𝟙_ C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.whisker_eq`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {X Y Z : C} {f g : Y ⟶ X} (h : Z ⟶ Y),   f = g → CategoryTheory.Cate
goryStruct.comp…
· 使用定理 `CategoryTheory.MonObj.mul_one`：∀ {C : Type u₁} {inst : CategoryTheory.Ca
tegory.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} (X : C)   [self 
: CategoryTheory.Mo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_rightUnitor_hom`：lift_righ
tUnitor_hom {X Y : C} (f : X ⟶ Y) (g : X ⟶ 𝟙_ C) : lift f g ≫ (ρ_ Y).hom = f
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.lift_whiskerLeft_assoc`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Carte
sianMonoidalCategory C]   {X Y Z W : C} (f : X ⟶ Y) (…
-/
theorem lift_comp_one_right {A : C} {B : C} [MonObj B] (f : A ⟶ B) (g : A ⟶ 𝟙_ C) :
    lift f (g ≫ η) ≫ μ = f := by
  have := lift f g ≫= mul_one B
  rwa [lift_whiskerLeft_assoc, lift_rightUnitor_hom] at this

variable [BraidedCategory C]

attribute [local simp] tensorObj.one_def tensorObj.mul_def

@[to_additive]
/-
**CategoryTheory.MonObj.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.MonObj`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsMonHom (fst M N) where

@[to_additive]
/-
**CategoryTheory.MonObj.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.MonObj`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsMonHom (snd M N) where

@[to_additive]
/-
**CategoryTheory.MonObj.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.MonObj`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {f : M ⟶ N} {g : M ⟶ O} [IsMonHom f] [IsMonHom g] : IsMonHom (lift f g) where

@[to_additive]
/-
**CategoryTheory.MonObj.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.MonObj`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsCommMonObj M] : IsMonHom μ[M] where
  one_hom := by simp [toUnit_unique (ρ_ (𝟙_ C)).hom (λ_ (𝟙_ C)).hom]

end MonObj

namespace Mon
variable [BraidedCategory C]

set_option backward.isDefEq.respectTransparency false in
attribute [local simp] tensorObj.one_def tensorObj.mul_def in
@[to_additive]
/-
**CategoryTheory.Mon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CartesianMonoidalCategory (Mon C) where
  isTerminalTensorUnit := .ofUniqueHom (fun M ↦ ⟨toUnit _⟩) fun M f ↦ by ext; exact toUnit_unique ..
  fst M N := .mk (fst M.X N.X)
  snd M N := .mk (snd M.X N.X)
  tensorProductIsBinaryProduct M N :=
    BinaryFan.IsLimit.mk _ (fun {T} f g ↦ ⟨lift f.hom g.hom⟩)
      (by aesop_cat) (by aesop_cat) (by aesop_cat)
  fst_def M N := by ext; simp [fst_def]; congr
  snd_def M N := by ext; simp [snd_def]; congr

variable {M N N₁ N₂ : Mon C}

@[to_additive (attr := simp)]
/-
**CategoryTheory.Mon.lift_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Mon`。
形式化陈述：lift_hom (f : M ⟶ N₁) (g : M ⟶ N₂) : (lift f g).hom = lift f.hom g.hom
参数：f : M ⟶ N₁；g : M ⟶ N₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lift_hom (f : M ⟶ N₁) (g : M ⟶ N₂) : (lift f g).hom = lift f.hom g.hom := rfl

@[to_additive (attr := simp)]
/-
**CategoryTheory.Mon.fst_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Mon`。
形式化陈述：fst_hom (M N : Mon C) : (fst M N).hom = fst M.X N.X
参数：M N : Mon C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fst_hom (M N : Mon C) : (fst M N).hom = fst M.X N.X := rfl

@[to_additive (attr := simp)]
/-
**CategoryTheory.Mon.snd_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Mon`。
形式化陈述：snd_hom (M N : Mon C) : (snd M N).hom = snd M.X N.X
参数：M N : Mon C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma snd_hom (M N : Mon C) : (snd M N).hom = snd M.X N.X := rfl

/-! ### Comm monoid objects are internal monoid objects -/

/-- A commutative monoid object is a monoid object in the category of monoid objects. -/
@[to_additive
/-- A commutative additive monoid object is an additive monoid object in the category
of additive monoid objects. -/]
/-
**CategoryTheory.Mon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsCommMonObj M.X] : MonObj M where
  one := .mk η[M.X]
  mul := .mk μ[M.X]

@[to_additive (attr := simp)]
/-
**CategoryTheory.Mon.hom_one** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Mon`。
形式化陈述：hom_one (M : Mon C) [IsCommMonObj M.X] : η[M].hom = η[M.X]
参数：M : Mon C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_one (M : Mon C) [IsCommMonObj M.X] : η[M].hom = η[M.X] := rfl

@[to_additive (attr := simp)]
/-
**CategoryTheory.Mon.hom_mul** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Mon`。
形式化陈述：hom_mul (M : Mon C) [IsCommMonObj M.X] : μ[M].hom = μ[M.X]
参数：M : Mon C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_mul (M : Mon C) [IsCommMonObj M.X] : μ[M].hom = μ[M.X] := rfl

/-- A commutative monoid object is a commutative monoid object in the category of monoid objects. -/
@[to_additive
/-- A commutative additive monoid object is a commutative additive monoid object in the
category of additive monoid objects. -/]
/-
**CategoryTheory.Mon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsCommMonObj M.X] : IsCommMonObj M where

end Mon

variable (X) in
/-- If `X` represents a presheaf of monoids, then `X` is a monoid object. -/
@[to_additive (attr := simps, instance_reducible)
/-- If `X` represents a presheaf of additive monoids, then `X` is an additive monoid object. -/]
/-
**CategoryTheory.MonObj.ofRepresentableBy** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.MonObj`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v, u_1} C] →     [inst
_1 : CategoryTheory.CartesianMonoidalCategory C] →       (X : C) →         (F : 
CategoryTheory.Functor Cᵒᵖ MonCat) →           (F.comp (CategoryTheory.forget Mo
nCat)).RepresentableBy X → CategoryTheory.MonObj X
参数：X : C；F : CategoryTheory.Functor Cᵒᵖ MonCat；F.comp (CategoryTheory.forget Mon
Cat)。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
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
/-
**CategoryTheory.Hom.monoid** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Hom`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v, u_1} C] →     [inst
_1 : CategoryTheory.CartesianMonoidalCategory C] → {M X : C} → [CategoryTheory.M
onObj M] → Monoid (X ⟶ M)
参数：X ⟶ M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
    rw [← Category.comp_id f, ← lift_map_assoc, tensorHom_id, MonObj.one_mul,
      Category.comp_id, leftUnitor_hom]
    exact lift_snd _ _
  mul_one f := by
    change lift f (toUnit _ ≫ η) ≫ μ = f
    rw [← Category.comp_id f, ← lift_map_assoc, id_tensorHom, MonObj.mul_one,
      Category.comp_id, rightUnitor_hom]
    exact lift_fst _ _

scoped[CategoryTheory.MonObj] attribute [instance] Hom.monoid
scoped[CategoryTheory.AddMonObj] attribute [instance] Hom.addMonoid

@[to_additive]
/-
**CategoryTheory.Hom.one_def** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Hom`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : Cat
egoryTheory.CartesianMonoidalCategory C]   {M X : C} [inst_2 : CategoryTheory.Mo
nObj M],   1 =     CategoryTheory.CategoryStruct.comp (CategoryTheory.SemiCartes
ianMonoidalCategory.toUnit X) CategoryTheory.MonObj.one
参数：CategoryTheory.SemiCartesianMonoidalCategory.toUnit X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Hom.one_def : (1 : X ⟶ M) = toUnit X ≫ η := rfl
@[to_additive]
/-
**CategoryTheory.Hom.mul_def** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Hom`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : Cat
egoryTheory.CartesianMonoidalCategory C]   {M X : C} [inst_2 : CategoryTheory.Mo
nObj M] (f₁ f₂ : X ⟶ M),   f₁ * f₂ =     CategoryTheory.CategoryStruct.comp (Cat
egoryTheory.CartesianMonoidalCategory.lift f₁ f₂) CategoryTheory.MonObj.mul
参数：f₁ f₂ : X ⟶ M；CategoryTheory.CartesianMonoidalCategory.lift f₁ f₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Hom.mul_def (f₁ f₂ : X ⟶ M) : f₁ * f₂ = lift f₁ f₂ ≫ μ := rfl

namespace Functor
variable (F : C ⥤ D) [F.Monoidal]

open scoped Obj

@[to_additive map_add']
/-
**CategoryTheory.Functor.map_mul** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Funct
or`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v, u_1} C
]   [inst_1 : CategoryTheory.CartesianMonoidalCategory C] [inst_2 : CategoryTheo
ry.Category.{w, u_2} D]   [inst_3 : CategoryTheory.CartesianMonoidalCategory D] 
{M X : C} [inst_4 : CategoryTheory.MonObj M]   (F : CategoryTheory.Functor C D) 
[inst_5 : F.Monoidal] (f g : X ⟶ M), F.map (f * g) = F.map f * F.map g
参数：F : CategoryTheory.Functor C D；f g : X ⟶ M；f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.Monoidal.lift_μ_assoc`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.CartesianMonoidalCate
gory C]   {D : Type u₂} [inst_2 : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma map_mul (f g : X ⟶ M) : F.map (f * g) = F.map f * F.map g := by
  simp [Hom.mul_def]

@[to_additive (attr := simp) map_zero']
/-
**CategoryTheory.Functor.map_one** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Funct
or`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v, u_1} C
]   [inst_1 : CategoryTheory.CartesianMonoidalCategory C] [inst_2 : CategoryTheo
ry.Category.{w, u_2} D]   [inst_3 : CategoryTheory.CartesianMonoidalCategory D] 
{M X : C} [inst_4 : CategoryTheory.MonObj M]   (F : CategoryTheory.Functor C D) 
[inst_5 : F.Monoidal], F.map 1 = 1
参数：F : CategoryTheory.Functor C D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.Monoidal.toUnit_ε_assoc`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.CartesianMonoidalCa
tegory C]   {D : Type u₂} [inst_2 : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma map_one : F.map (1 : X ⟶ M) = 1 := by simp [Hom.one_def]

/-- `Functor.map` of a monoidal functor as a `MonoidHom`. -/
@[to_additive (attr := simps) /-- `Functor.map` of a monoidal functor as a `AddMonoidHom`. -/]
/-
**CategoryTheory.Functor.homMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Functor`。
形式化陈述：homMonoidHom : (X ⟶ M) ->* (F.obj X ⟶ F.obj M) where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_one`：∀ {C : Type u_1} {D : Type u_2} [inst : 
CategoryTheory.Category.{v, u_1} C]   [inst_1 : CategoryTheory.CartesianMonoidal
Category C] [inst_2 …
· 使用定理 `CategoryTheory.Functor.map_mul`：∀ {C : Type u_1} {D : Type u_2} [inst : 
CategoryTheory.Category.{v, u_1} C]   [inst_1 : CategoryTheory.CartesianMonoidal
Category C] [inst_2 …

--- 原说明 ---
`Functor.map` of a monoidal functor as a `MonoidHom`.
-/
def homMonoidHom : (X ⟶ M) →* (F.obj X ⟶ F.obj M) where
  toFun := F.map
  map_one' := F.map_one
  map_mul' := F.map_mul

/-- `Functor.map` of a fully faithful monoidal functor as a `MulEquiv`. -/
@[to_additive (attr := simps!)
/-- `Functor.map` of a fully faithful monoidal functor as a `AddEquiv`. -/]
/-
**CategoryTheory.Functor.FullyFaithful.homMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Functor.FullyFaithful`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
, u_1} C] →       [inst_1 : CategoryTheory.CartesianMonoidalCategory C] →       
  [inst_2 : CategoryTheory.Category.{w, u_2} D] →           [inst_3 : CategoryTh
eory.CartesianMonoidalCategory D] →             {M X : C} →               [inst_
4 : CategoryTheory.MonObj M] →                 (F : CategoryTheory.Functor C D) 
→                   [inst_5 : F.Monoidal] → F.FullyFaithful → (X ⟶ M) ≃* (F.obj 
X ⟶ F.obj M)
参数：F : CategoryTheory.Functor C D；X ⟶ M；F.obj X ⟶ F.obj M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**CategoryTheory.Hom.commMonoid** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Hom`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v, u_1} C] →     [inst
_1 : CategoryTheory.CartesianMonoidalCategory C] →       {M X : C} →         [in
st_2 : CategoryTheory.MonObj M] →           [inst_3 : CategoryTheory.BraidedCate
gory C] → [CategoryTheory.IsCommMonObj M] → CommMonoid (X ⟶ M)
参数：X ⟶ M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev Hom.commMonoid [IsCommMonObj M] : CommMonoid (X ⟶ M) where
  mul_comm f g := by simpa [-IsCommMonObj.mul_comm] using! lift g f ≫= IsCommMonObj.mul_comm M

namespace Mon.Hom
variable {M N : Mon C} [IsCommMonObj N.X]

@[to_additive (attr := simp)]
/-
**CategoryTheory.Mon.Hom.hom_one** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Mon.H
om`。
形式化陈述：hom_one : (1 : M ⟶ N).hom = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_one : (1 : M ⟶ N).hom = 1 := rfl
@[to_additive (attr := simp)]
/-
**CategoryTheory.Mon.Hom.hom_mul** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Mon.H
om`。
形式化陈述：hom_mul (f g : M ⟶ N) : (f * g).hom = f.hom * g.hom
参数：f g : M ⟶ N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_mul (f g : M ⟶ N) : (f * g).hom = f.hom * g.hom := rfl
@[to_additive (attr := simp)]
/-
**CategoryTheory.Mon.Hom.hom_pow** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Mon.H
om`。
形式化陈述：hom_pow (f : M ⟶ N) (n : Nat) : (f ^ n).hom = f.hom ^ n
参数：f : M ⟶ N；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma hom_pow (f : M ⟶ N) (n : ℕ) : (f ^ n).hom = f.hom ^ n := by
  induction n <;> simp [pow_succ, *]

end Mon.Hom

scoped[CategoryTheory.MonObj] attribute [instance] Hom.commMonoid Hom.addCommMonoid

end BraidedCategory

/-- A monoid morphism `f : M ⟶ N` induces a monoid homomorphism `M(X) →* N(X)` for every `X`. -/
@[to_additive (attr := simps!)
/-- An additive monoid morphism `f : M ⟶ N` induces an additive monoid homomorphism
`M(X) →+ N(X)` for every `X`. -/]
/-
**CategoryTheory.IsMonHom.monoidHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Is
MonHom`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v, u_1} C] →     [inst
_1 : CategoryTheory.CartesianMonoidalCategory C] →       {M N : C} →         [in
st_2 : CategoryTheory.MonObj M] →           [inst_3 : CategoryTheory.MonObj N] →
 (f : M ⟶ N) → [CategoryTheory.IsMonHom f] → (X : C) → (X ⟶ M) →* (X ⟶ N)
参数：f : M ⟶ N；X : C；X ⟶ M；X ⟶ N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def IsMonHom.monoidHom (f : M ⟶ N) [IsMonHom f] (X : C) : (X ⟶ M) →* (X ⟶ N) where
  toFun := (· ≫ f)
  map_one' := by simp [Hom.one_def]
  map_mul' := by simp [Hom.mul_def]

@[to_additive (attr := simp)]
/-
**CategoryTheory.IsMonHom.monoidHom_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.IsMonHom`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : Cat
egoryTheory.CartesianMonoidalCategory C]   {M X : C} [inst_2 : CategoryTheory.Mo
nObj M],   CategoryTheory.IsMonHom.monoidHom (CategoryTheory.CategoryStruct.id M
) X = MonoidHom.id (X ⟶ M)
参数：CategoryTheory.CategoryStruct.id M；X ⟶ M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `CategoryTheory.MonObj.instIsMonHomId`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C] {X : C}  
 [inst_2 : CategoryTheory.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsMonHom.monoidHom_apply`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheory.CartesianMonoidalCategory
 C]   {M N : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `MonoidHom.id_apply`：∀ (M : Type u_10) [inst : MulOne M] (x : M), (Monoid
Hom.id M) x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsMonHom.monoidHom_id : IsMonHom.monoidHom (𝟙 M) X = MonoidHom.id _ := by
  cat_disch

@[to_additive (attr := simp)]
/-
**CategoryTheory.IsMonHom.monoidHom_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.IsMonHom`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : Cat
egoryTheory.CartesianMonoidalCategory C]   {M N O X : C} [inst_2 : CategoryTheor
y.MonObj M] [inst_3 : CategoryTheory.MonObj N] [inst_4 : CategoryTheory.MonObj O
]   (f : M ⟶ N) (g : N ⟶ O) [inst_5 : CategoryTheory.IsMonHom f] [inst_6 : Categ
oryTheory.IsMonHom g],   CategoryTheory.IsMonHom.monoidHom (CategoryTheory.Categ
oryStruct.comp f g) X =     (CategoryTheory.IsMonHom.monoidHom g X).comp (Catego
ryTheory.IsMonHom.monoidHom f X)
参数：f : M ⟶ N；g : N ⟶ O；CategoryTheory.CategoryStruct.comp f g；CategoryTheory.IsM
onHom.monoidHom g X；CategoryTheory.IsMonHom.monoidHom f X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `CategoryTheory.instIsMonHomComp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C] {M N O : C}   
[inst_2 : CategoryThe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsMonHom.monoidHom_apply`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheory.CartesianMonoidalCategory
 C]   {M N : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsMonHom.monoidHom_comp (f : M ⟶ N) (g : N ⟶ O) [IsMonHom f] [IsMonHom g] :
    IsMonHom.monoidHom (f ≫ g) X = MonoidHom.comp (monoidHom g X) (monoidHom f X) := by
  cat_disch

variable (M) in
/-- If `M` is a monoid object, then `Hom(-, M)` is a presheaf of monoids. -/
@[to_additive (attr := simps)
/-- If `M` is an additive monoid object, then `Hom(-, M)` is a presheaf of additive monoids. -/]
/-
**CategoryTheory.yonedaMonObj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：yonedaMonObj : Cᵒᵖ ⥤ MonCat.{v} where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def yonedaMonObj : Cᵒᵖ ⥤ MonCat.{v} where
  obj X := MonCat.of (unop X ⟶ M)
  map {X Y₂} φ := MonCat.ofHom
    { toFun := (φ.unop ≫ ·)
      map_one' := by
        change φ.unop ≫ toUnit _ ≫ η = toUnit _ ≫ η
        rw [← Category.assoc, toUnit_unique (φ.unop ≫ toUnit _)]
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
/-
**CategoryTheory.yonedaMonObjIsoOfRepresentableBy** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory`。
形式化陈述：yonedaMonObjIsoOfRepresentableBy (F : Cᵒᵖ ⥤ MonCat.{v}) (α : (F ⋙ forget _
).RepresentableBy X) : letI
参数：F : Cᵒᵖ ⥤ MonCat.{v}；α : (F ⋙ forget _).RepresentableBy X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def yonedaMonObjIsoOfRepresentableBy
    (F : Cᵒᵖ ⥤ MonCat.{v}) (α : (F ⋙ forget _).RepresentableBy X) :
    letI := MonObj.ofRepresentableBy X F α
    yonedaMonObj X ≅ F :=
  letI := MonObj.ofRepresentableBy X F α
  NatIso.ofComponents (fun Y ↦ MulEquiv.toMonCatIso
    { toEquiv := α.homEquiv'
      map_mul' f₁ f₂ := by
        change α.homEquiv' (lift f₁ f₂ ≫ α.homEquiv'.symm (α.homEquiv' (fst X X) *
          α.homEquiv' (snd X X))) = α.homEquiv' f₁ * α.homEquiv' f₂
        simp only [α.homEquiv'_comp, Equiv.apply_symm_apply, map_mul]
        simp only [← α.homEquiv'_comp]
        simp }) (fun φ ↦ MonCat.hom_ext (MonoidHom.ext (α.homEquiv'_comp φ.unop)))

/-- The yoneda embedding of `Mon C` into presheaves of monoids. -/
@[to_additive (attr := simps)
/-- The yoneda embedding of `AddMon C` into presheaves of additive monoids. -/]
/-
**CategoryTheory.yonedaMon** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：yonedaMon : Mon C ⥤ Cᵒᵖ ⥤ MonCat.{v} where obj M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def yonedaMon : Mon C ⥤ Cᵒᵖ ⥤ MonCat.{v} where
  obj M := yonedaMonObj M.X
  map ψ :=
  { app _ := MonCat.ofHom <| IsMonHom.monoidHom _ _
    naturality {_ _} φ := MonCat.hom_ext <| MonoidHom.ext fun f ↦ Category.assoc φ.unop f ψ.hom }
  map_id _ := NatTrans.ext <| funext fun _ ↦ MonCat.hom_ext <| IsMonHom.monoidHom_id
  map_comp _ _ := NatTrans.ext <| funext fun _ ↦ MonCat.hom_ext <| IsMonHom.monoidHom_comp _ _

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[to_additive (attr := reassoc)]
/-
**CategoryTheory.yonedaMon_naturality** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`
。
形式化陈述：yonedaMon_naturality (α : yonedaMonObj M ⟶ yonedaMonObj N) (f : X ⟶ Y) (g 
: Y ⟶ M) : α.app _ (f ≫ g) = f ≫ α.app _ g
参数：α : yonedaMonObj M ⟶ yonedaMonObj N；f : X ⟶ Y；g : Y ⟶ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma yonedaMon_naturality (α : yonedaMonObj M ⟶ yonedaMonObj N) (f : X ⟶ Y) (g : Y ⟶ M) :
      α.app _ (f ≫ g) = f ≫ α.app _ g := congr($(α.naturality f.op) g)

variable (M) in
/-- If `M` is a monoid object, then `Hom(-, M)` as a presheaf of monoids is represented by `M`. -/
@[to_additive
/-- If `M` is an additive monoid object, then `Hom(-, M)` as a presheaf of additive monoids
is represented by `M`. -/]
/-
**CategoryTheory.yonedaMonObjRepresentableBy** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory`。
形式化陈述：yonedaMonObjRepresentableBy : (yonedaMonObj M ⋙ forget _).RepresentableBy 
M
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
def yonedaMonObjRepresentableBy : (yonedaMonObj M ⋙ forget _).RepresentableBy M :=
  Functor.representableByEquiv.symm (.refl _)

variable (M) in
@[to_additive]
/-
**CategoryTheory.MonObj.ofRepresentableBy_yonedaMonObjRepresentableBy** 是 Mathli
b 中的一个定理，位于命名空间 `CategoryTheory.MonObj`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : Cat
egoryTheory.CartesianMonoidalCategory C]   (M : C) [inst_2 : CategoryTheory.MonO
bj M],   CategoryTheory.MonObj.ofRepresentableBy M (CategoryTheory.yonedaMonObj 
M)       (CategoryTheory.yonedaMonObjRepresentableBy M) =     inst_2
参数：M : C；CategoryTheory.yonedaMonObj M；CategoryTheory.yonedaMonObjRepresentableB
y M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MonObj.ext`：ext {X : C} (h₁ h₂ : MonObj X) (H : h₁.mul = 
h₂.mul) : h₁ = h₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_fst_snd`：lift_fst_snd {X Y
 : C} : lift (fst X Y) (snd X Y) = 𝟙 (X otimes Y)
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma MonObj.ofRepresentableBy_yonedaMonObjRepresentableBy :
    ofRepresentableBy M _ (yonedaMonObjRepresentableBy M) = ‹_› := by
  ext; change lift (fst M M) (snd M M) ≫ μ = μ; rw [lift_fst_snd, Category.id_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The yoneda embedding for `Mon C` is fully faithful. -/
@[to_additive /-- The yoneda embedding for `AddMon C` is fully faithful. -/]
/-
**CategoryTheory.yonedaMonFullyFaithful** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y`。
形式化陈述：yonedaMonFullyFaithful : yonedaMon (C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The yoneda embedding for `Mon C` is fully faithful.
-/
def yonedaMonFullyFaithful : yonedaMon (C := C).FullyFaithful where
  preimage {M N} α :=
    { hom := α.app (op M.X) (𝟙 M.X)
      isMonHom_hom.one_hom := by
          dsimp only [yonedaMon_obj] at α ⊢
          rw [← yonedaMon_naturality, Category.comp_id,
            ← Category.id_comp η[M.X], toUnit_unique (𝟙 _) (toUnit _),
            ← Category.id_comp η[N.X], toUnit_unique (𝟙 _) (toUnit _)]
          exact (α.app _).hom.map_one
      isMonHom_hom.mul_hom := by
        dsimp only [yonedaMon_obj] at α ⊢
        rw [← yonedaMon_naturality, Category.comp_id, ← Category.id_comp μ[M.X], ← lift_fst_snd]
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
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : yonedaMon (C := C).Full := yonedaMonFullyFaithful.full
@[to_additive]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : yonedaMon (C := C).Faithful := yonedaMonFullyFaithful.faithful

@[to_additive]
/-
**CategoryTheory.essImage_yonedaMon** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：essImage_yonedaMon : yonedaMon (C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma essImage_yonedaMon :
    yonedaMon (C := C).essImage = fun F ↦ (F ⋙ forget _).IsRepresentable := by
  ext F
  constructor
  · rintro ⟨M, ⟨α⟩⟩
    exact ⟨M.X, ⟨Functor.representableByEquiv.symm (Functor.isoWhiskerRight α (forget _))⟩⟩
  · rintro ⟨X, ⟨e⟩⟩
    let := MonObj.ofRepresentableBy X F e
    exact ⟨Mon.mk X, ⟨yonedaMonObjIsoOfRepresentableBy X F e⟩⟩

@[to_additive (attr := reassoc (attr := simp))]
/-
**CategoryTheory.MonObj.one_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MonOb
j`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : Cat
egoryTheory.CartesianMonoidalCategory C]   {M N X : C} [inst_2 : CategoryTheory.
MonObj M] [inst_3 : CategoryTheory.MonObj N] (f : M ⟶ N)   [CategoryTheory.IsMon
Hom f], CategoryTheory.CategoryStruct.comp 1 f = 1
参数：f : M ⟶ N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsMonHom.one_hom`：∀ {C : Type u₁} {inst : CategoryTheory.
Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {M N : C}   {i
nst_2 : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma MonObj.one_comp (f : M ⟶ N) [IsMonHom f] : (1 : X ⟶ M) ≫ f = 1 := by simp [Hom.one_def]

@[to_additive (attr := reassoc)]
/-
**CategoryTheory.MonObj.mul_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MonOb
j`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : Cat
egoryTheory.CartesianMonoidalCategory C]   {M N X : C} [inst_2 : CategoryTheory.
MonObj M] [inst_3 : CategoryTheory.MonObj N] (f₁ f₂ : X ⟶ M) (g : M ⟶ N)   [Cate
goryTheory.IsMonHom g],   CategoryTheory.CategoryStruct.comp (f₁ * f₂) g =     C
ategoryTheory.CategoryStruct.comp f₁ g * CategoryTheory.CategoryStruct.comp f₂ g
参数：f₁ f₂ : X ⟶ M；g : M ⟶ N；f₁ * f₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsMonHom.mul_hom`：∀ {C : Type u₁} {inst : CategoryTheory.
Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {M N : C}   {i
nst_2 : CategoryTheor…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.lift_map_assoc`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.CartesianMono
idalCategory C]   {V W X Y Z : C} (f : V ⟶ W)…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma MonObj.mul_comp (f₁ f₂ : X ⟶ M) (g : M ⟶ N) [IsMonHom g] :
    (f₁ * f₂) ≫ g = f₁ ≫ g * f₂ ≫ g := by simp [Hom.mul_def]

@[to_additive (attr := reassoc)]
/-
**CategoryTheory.MonObj.pow_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MonOb
j`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : Cat
egoryTheory.CartesianMonoidalCategory C]   {M N X : C} [inst_2 : CategoryTheory.
MonObj M] [inst_3 : CategoryTheory.MonObj N] (f : X ⟶ M) (n : ℕ) (g : M ⟶ N)   [
CategoryTheory.IsMonHom g], CategoryTheory.CategoryStruct.comp (f ^ n) g = Categ
oryTheory.CategoryStruct.comp f g ^ n
参数：f : X ⟶ M；n : ℕ；g : M ⟶ N；f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `CategoryTheory.MonObj.one_comp`：∀ {C : Type u_1} [inst : CategoryTheory.
Category.{v, u_1} C] [inst_1 : CategoryTheory.CartesianMonoidalCategory C]   {M 
N X : C} [inst_2 : C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `CategoryTheory.MonObj.mul_comp`：∀ {C : Type u_1} [inst : CategoryTheory.
Category.{v, u_1} C] [inst_1 : CategoryTheory.CartesianMonoidalCategory C]   {M 
N X : C} [inst_2 : C…
-/
lemma MonObj.pow_comp (f : X ⟶ M) (n : ℕ) (g : M ⟶ N) [IsMonHom g] :
    (f ^ n) ≫ g = (f ≫ g) ^ n := by
  induction n <;> simp [pow_succ, MonObj.mul_comp, *]

@[to_additive (attr := reassoc (attr := simp))]
/-
**CategoryTheory.MonObj.comp_one** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MonOb
j`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : Cat
egoryTheory.CartesianMonoidalCategory C]   {M X Y : C} [inst_2 : CategoryTheory.
MonObj M] (f : X ⟶ Y), CategoryTheory.CategoryStruct.comp f 1 = 1
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_one`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N), f 1 = 1
-/
lemma MonObj.comp_one (f : X ⟶ Y) : f ≫ (1 : Y ⟶ M) = 1 :=
  ((yonedaMon.obj <| .mk M).map f.op).hom.map_one

@[to_additive (attr := reassoc)]
/-
**CategoryTheory.MonObj.comp_mul** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MonOb
j`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : Cat
egoryTheory.CartesianMonoidalCategory C]   {M X Y : C} [inst_2 : CategoryTheory.
MonObj M] (f : X ⟶ Y) (g₁ g₂ : Y ⟶ M),   CategoryTheory.CategoryStruct.comp f (g
₁ * g₂) =     CategoryTheory.CategoryStruct.comp f g₁ * CategoryTheory.CategoryS
truct.comp f g₂
参数：f : X ⟶ Y；g₁ g₂ : Y ⟶ M；g₁ * g₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_mul`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N) (a b : M), f (a * b) = f a * f b
-/
lemma MonObj.comp_mul (f : X ⟶ Y) (g₁ g₂ : Y ⟶ M) : f ≫ (g₁ * g₂) = f ≫ g₁ * f ≫ g₂ :=
  ((yonedaMon.obj <| .mk M).map f.op).hom.map_mul _ _

@[to_additive (attr := reassoc)]
/-
**CategoryTheory.MonObj.comp_pow** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MonOb
j`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : Cat
egoryTheory.CartesianMonoidalCategory C]   {M X Y : C} [inst_2 : CategoryTheory.
MonObj M] (f : X ⟶ M) (n : ℕ) (h : Y ⟶ X),   CategoryTheory.CategoryStruct.comp 
h (f ^ n) = CategoryTheory.CategoryStruct.comp h f ^ n
参数：f : X ⟶ M；n : ℕ；h : Y ⟶ X；f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `CategoryTheory.MonObj.comp_one`：∀ {C : Type u_1} [inst : CategoryTheory.
Category.{v, u_1} C] [inst_1 : CategoryTheory.CartesianMonoidalCategory C]   {M 
X Y : C} [inst_2 : C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `CategoryTheory.MonObj.comp_mul`：∀ {C : Type u_1} [inst : CategoryTheory.
Category.{v, u_1} C] [inst_1 : CategoryTheory.CartesianMonoidalCategory C]   {M 
X Y : C} [inst_2 : C…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma MonObj.comp_pow (f : X ⟶ M) (n : ℕ) (h : Y ⟶ X) : h ≫ f ^ n = (h ≫ f) ^ n := by
  induction n <;> simp [pow_succ, MonObj.comp_mul, *]

variable (M) in
@[to_additive]
/-
**CategoryTheory.MonObj.one_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Mon
Obj`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : Cat
egoryTheory.CartesianMonoidalCategory C]   (M : C) [inst_2 : CategoryTheory.MonO
bj M], CategoryTheory.MonObj.one = 1
参数：M : C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.SemiCartesianMonoidalCategory.toUnit_unique`：toUnit_uniqu
e {X : C} (f g : X ⟶ 𝟙_ _) : f = g
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma MonObj.one_eq_one : η = (1 : _ ⟶ M) :=
  show _ = _ ≫ _ by rw [toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

variable (M) in
@[to_additive]
/-
**CategoryTheory.MonObj.mul_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Mon
Obj`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : Cat
egoryTheory.CartesianMonoidalCategory C]   (M : C) [inst_2 : CategoryTheory.MonO
bj M],   CategoryTheory.MonObj.mul =     CategoryTheory.SemiCartesianMonoidalCat
egory.fst M M * CategoryTheory.SemiCartesianMonoidalCategory.snd M M
参数：M : C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_fst_snd`：lift_fst_snd {X Y
 : C} : lift (fst X Y) (snd X Y) = 𝟙 (X otimes Y)
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
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
/-
**CategoryTheory.Hom.mulEquivCongrRight** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Hom`。
形式化陈述：mulEquivCongrRight (e : M ≅ N) [IsMonHom e.hom] (X : C) : (X ⟶ M) ≃* (X ⟶ 
N)
参数：e : M ≅ N；X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mulEquivCongrRight (e : M ≅ N) [IsMonHom e.hom] (X : C) : (X ⟶ M) ≃* (X ⟶ N) :=
  ((yonedaMon.mapIso <| Mon.mkIso' e).app <| .op X).monCatIsoToMulEquiv

end Hom

open scoped IsMulCommutative in
/-- A monoid object `M` is commutative if and only if `X ⟶ M` is commutative for all `X`. -/
@[to_additive
/-- An additive monoid object `M` is commutative if and only if `X ⟶ M` is commutative for all
`X`. -/]
/-
**CategoryTheory.isCommMonObj_iff_isMulCommutative** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory`。
形式化陈述：isCommMonObj_iff_isMulCommutative (M : C) [MonObj M] [BraidedCategory C] :
 IsCommMonObj M ↔ forall (X : C), IsMulCommutative (X ⟶ M)
参数：M : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.MonObj.mul_eq_mul`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v, u_1} C] [inst_1 : CategoryTheory.CartesianMonoidalCategory C]   (
M : C) [inst_2 : Categ…
· 使用定理 `CategoryTheory.MonObj.comp_mul`：∀ {C : Type u_1} [inst : CategoryTheory.
Category.{v, u_1} C] [inst_1 : CategoryTheory.CartesianMonoidalCategory C]   {M 
X Y : C} [inst_2 : C…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.braiding_hom_fst`：braiding_hom_
fst (X Y : C) : (β_ X Y).hom ≫ fst _ _ = snd _ _
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.braiding_hom_snd`：braiding_hom_
snd (X Y : C) : (β_ X Y).hom ≫ snd _ _ = fst _ _
-/
lemma isCommMonObj_iff_isMulCommutative (M : C) [MonObj M] [BraidedCategory C] :
    IsCommMonObj M ↔ ∀ (X : C), IsMulCommutative (X ⟶ M) := by
  exact ⟨fun h X ↦ ⟨⟨by simp [mul_comm]⟩⟩, fun h ↦ ⟨by simp [mul_eq_mul, comp_mul, mul_comm]⟩⟩

end CategoryTheory

