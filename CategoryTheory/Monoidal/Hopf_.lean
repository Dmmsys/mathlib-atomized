/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.Bimon_
public import Mathlib.CategoryTheory.Monoidal.Conv

/-!
# The category of Hopf monoids in a braided monoidal category.


## TODO

* Show that in a Cartesian monoidal category Hopf monoids are exactly group objects.
* Show that `Hopf (ModuleCat R) ≌ HopfAlgCat R`.
-/

@[expose] public section

noncomputable section

universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory

namespace CategoryTheory
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C] [BraidedCategory C]

open scoped MonObj ComonObj

/--
A Hopf monoid in a braided category `C` is a bimonoid object in `C` equipped with an antipode.
-/
/-
**CategoryTheory.HopfObj** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：HopfObj (X : C) extends BimonObj X where /-- The antipode is an endomorphi
sm of the underlying object of the Hopf monoid. -/ antipode : X ⟶ X antipode_lef
t (X) : Δ ≫ antipode ▷ X ≫ μ = ε ≫ η
参数：X : C。
继承自：BimonObj X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Hopf monoid in a braided category `C` is a bimonoid object in `C` equipped wit
h an antipode.
-/
class HopfObj (X : C) extends BimonObj X where
  /-- The antipode is an endomorphism of the underlying object of the Hopf monoid. -/
  antipode : X ⟶ X
  antipode_left (X) : Δ ≫ antipode ▷ X ≫ μ = ε ≫ η := by cat_disch
  antipode_right (X) : Δ ≫ X ◁ antipode ≫ μ = ε ≫ η := by cat_disch

namespace HopfObj

@[inherit_doc] scoped notation "𝒮" => HopfObj.antipode
@[inherit_doc] scoped notation "𝒮[" M "]" => HopfObj.antipode (X := M)

attribute [reassoc (attr := simp)] antipode_left antipode_right


end HopfObj

variable (C)

/--
A Hopf monoid in a braided category `C` is a bimonoid object in `C` equipped with an antipode.
-/
/-
**CategoryTheory.Hopf** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u₁) →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] → [CategoryTheory.BraidedCategory C] → Ty
pe (max u₁ v₁)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Hopf monoid in a braided category `C` is a bimonoid object in `C` equipped wit
h an antipode.
-/
structure Hopf where
  /-- The underlying object in the ambient monoidal category -/
  X : C
  [hopf : HopfObj X]

attribute [instance] Hopf.hopf

namespace Hopf

variable {C}

/-- A Hopf monoid is a bimonoid. -/
/-
**CategoryTheory.Hopf.toBimon** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Hopf`。
形式化陈述：toBimon (A : Hopf C) : Bimon C
参数：A : Hopf C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Hopf monoid is a bimonoid.
-/
def toBimon (A : Hopf C) : Bimon C := .mk' A.X

/--
Morphisms of Hopf monoids are just morphisms of the underlying bimonoids.
In fact they automatically intertwine the antipodes, proved below.
-/
/-
**CategoryTheory.Hopf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Hopf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Morphisms of Hopf monoids are just morphisms of the underlying bimonoids.
In fact they automatically intertwine the antipodes, proved below.
-/
instance : Category (Hopf C) :=
  inferInstanceAs <| Category (InducedCategory (Bimon C) Hopf.toBimon)

end Hopf

namespace HopfObj

variable {C}

set_option backward.isDefEq.respectTransparency.types false in
/-- Morphisms of Hopf monoids intertwine the antipodes. -/
/-
**CategoryTheory.HopfObj.hom_antipode** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
HopfObj`。
形式化陈述：hom_antipode {A B : C} [HopfObj A] [HopfObj B] (f : A ⟶ B) [IsBimonHom f] 
: f ≫ 𝒮 = 𝒮 ≫ f
参数：f : A ⟶ B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `left_inv_eq_right_inv`：∀ {M : Type u_2} [inst : Monoid M] {a b c : M}, b
 * a = 1 → a * c = 1 → b = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Conv.mul_eq`：mul_eq (f g : Conv M N) : f * g = Δ[M] ≫ f ▷
 M ≫ N ◁ g ≫ μ[N]
· 使用定理 `CategoryTheory.Conv.one_eq`：one_eq : (1 : Conv M N) = ε[M] ≫ η[N]
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_exchange`：whisker_exchange {W X 
Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : W ◁ g ≫ f ▷ Z = f ▷ Y ≫ X ◁ g
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def`：∀ {C : Type u} {𝒞 : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X₁ Y₁ X
₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `CategoryTheory.IsComonHom.hom_comul`：∀ {C : Type u₁} {inst : CategoryThe
ory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {M N : C} 
  {inst_2 : CategoryTheor…
· 使用定理 `CategoryTheory.IsBimonHom.toIsComonHom`：∀ {C : Type u₁} {inst : Category
Theory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C}   {inst
_2 : CategoryTheory.BraidedC…
· 使用定理 `CategoryTheory.HopfObj.antipode_left`：∀ {C : Type u₁} {inst : CategoryTh
eory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C}   {inst_2
 : CategoryTheory.BraidedC…
· 使用定理 `CategoryTheory.IsComonHom.hom_counit`：∀ {C : Type u₁} {inst : CategoryTh
eory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {M N : C}
   {inst_2 : CategoryTheor…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `CategoryTheory.IsMonHom.mul_hom`：∀ {C : Type u₁} {inst : CategoryTheory.
Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {M N : C}   {i
nst_2 : CategoryTheor…
· 使用定理 `CategoryTheory.IsBimonHom.toIsMonHom`：∀ {C : Type u₁} {inst : CategoryTh
eory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C}   {inst_2
 : CategoryTheory.BraidedC…
· 使用定理 `CategoryTheory.HopfObj.antipode_right`：∀ {C : Type u₁} {inst : CategoryT
heory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C}   {inst_
2 : CategoryTheory.BraidedC…
· 使用定理 `CategoryTheory.IsMonHom.one_hom`：∀ {C : Type u₁} {inst : CategoryTheory.
Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {M N : C}   {i
nst_2 : CategoryTheor…

--- 原说明 ---
Morphisms of Hopf monoids intertwine the antipodes.
-/
theorem hom_antipode {A B : C} [HopfObj A] [HopfObj B] (f : A ⟶ B) [IsBimonHom f] :
    f ≫ 𝒮 = 𝒮 ≫ f := by
  -- We show these elements are equal by exhibiting an element in the convolution algebra
  -- between `A` (as a comonoid) and `B` (as a monoid),
  -- such that the LHS is a left inverse, and the RHS is a right inverse.
  apply left_inv_eq_right_inv
    (M := Conv A B)
    (a := f)
  · rw [Conv.mul_eq, Conv.one_eq]
    simp only [comp_whiskerRight, Category.assoc]
    slice_lhs 3 4 =>
      rw [← whisker_exchange]
    slice_lhs 2 3 =>
      rw [← tensorHom_def]
    slice_lhs 1 2 =>
      rw [← IsComonHom.hom_comul f]
    slice_lhs 2 4 =>
      rw [antipode_left]
    slice_lhs 1 2 =>
      rw [IsComonHom.hom_counit]
  · rw [Conv.mul_eq, Conv.one_eq]
    simp only [whiskerLeft_comp, Category.assoc]
    slice_lhs 2 3 =>
      rw [← whisker_exchange]
    slice_lhs 3 4 =>
      rw [← tensorHom_def]
    slice_lhs 3 4 =>
      rw [← IsMonHom.mul_hom]
    slice_lhs 1 3 =>
      rw [antipode_right]
    slice_lhs 2 3 =>
      rw [IsMonHom.one_hom]

@[reassoc (attr := simp)]
/-
**CategoryTheory.HopfObj.one_antipode** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
HopfObj`。
形式化陈述：one_antipode (A : C) [HopfObj A] : η[A] ≫ 𝒮[A] = η[A]
参数：A : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_id`：whiskerRight_id {X Y : 
C} (f : X ⟶ Y) : f ▷ 𝟙_ C = (ρ_ X).hom ≫ f ≫ (ρ_ Y).inv
· 使用定理 `CategoryTheory.MonObj.mul_one`：∀ {C : Type u₁} {inst : CategoryTheory.Ca
tegory.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} (X : C)   [self 
: CategoryTheory.Mo…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.BimonObj.one_counit_assoc`：∀ {C : Type u₁} {inst : Catego
ryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C}   {in
st_2 : CategoryTheory.BraidedC…
· 使用定理 `CategoryTheory.MonoidalCategory.rightUnitor_inv_naturality_assoc`：∀ {C :
 Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Mono
idalCategory C] {X X' : C}   (f : X ⟶ X') {Z : C}   (h…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_exchange_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C] {W X Y Z : C}   (f : W ⟶ X) (g : Y ⟶ Z…
· 使用定理 `CategoryTheory.MonoidalCategory.unitors_inv_equal`：unitors_inv_equal : (
fun_ (𝟙_ C)).inv = (ρ_ (𝟙_ C)).inv
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def_assoc`：∀ {C : Type u} {𝒞 :
 CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X
₁ Y₁ X₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `CategoryTheory.Bimon.one_comul_assoc`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C]   [inst_2
 : CategoryTheory.BraidedC…
· 使用定理 `CategoryTheory.HopfObj.antipode_left`：∀ {C : Type u₁} {inst : CategoryTh
eory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C}   {inst_2
 : CategoryTheory.BraidedC…
-/
theorem one_antipode (A : C) [HopfObj A] : η[A] ≫ 𝒮[A] = η[A] := by
  have := (rfl : η[A] ≫ Δ[A] ≫ (𝒮[A] ▷ A) ≫ μ[A] = _)
  conv at this =>
    rhs
    rw [antipode_left]
  rw [Bimon.one_comul_assoc, tensorHom_def_assoc, unitors_inv_equal,
    ← rightUnitor_inv_naturality_assoc, whisker_exchange_assoc, ← rightUnitor_inv_naturality_assoc,
    rightUnitor_inv_naturality_assoc] at this
  simpa

@[reassoc (attr := simp)]
/-
**CategoryTheory.HopfObj.antipode_counit** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.HopfObj`。
形式化陈述：antipode_counit (A : C) [HopfObj A] : 𝒮[A] ≫ ε[A] = ε[A]
参数：A : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_id`：whiskerRight_id {X Y : 
C} (f : X ⟶ Y) : f ▷ 𝟙_ C = (ρ_ X).hom ≫ f ≫ (ρ_ Y).inv
· 使用定理 `CategoryTheory.MonoidalCategory.unitors_equal`：unitors_equal : (fun_ (𝟙_
 C)).hom = (ρ_ (𝟙_ C)).hom
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.ComonObj.comul_counit_assoc`：∀ {C : Type u₁} {inst : Cate
goryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} (X 
: C)   [self : CategoryTheory.Co…
· 使用定理 `CategoryTheory.BimonObj.one_counit`：∀ {C : Type u₁} {inst : CategoryTheo
ry.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C}   {inst_2 :
 CategoryTheory.BraidedC…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_exchange_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C] {W X Y Z : C}   (f : W ⟶ X) (g : Y ⟶ Z…
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def'`：tensorHom_def' {X₁ Y₁ X₂
 Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : f otimesₘ g = X₁ ◁ g ≫ f ▷ Y₂
· 使用定理 `CategoryTheory.Bimon.mul_counit`：mul_counit (M : C) [BimonObj M] : μ[M] 
≫ ε[M] = (ε[M] otimesₘ ε[M]) ≫ (fun_ _).hom
· 使用定理 `CategoryTheory.HopfObj.antipode_left_assoc`：∀ {C : Type u₁} {inst : Cate
goryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C}   {
inst_2 : CategoryTheory.BraidedC…
-/
theorem antipode_counit (A : C) [HopfObj A] : 𝒮[A] ≫ ε[A] = ε[A] := by
  have := (rfl : Δ[A] ≫ (𝒮[A] ▷ A) ≫ μ[A] ≫ ε[A] = _)
  conv at this =>
    rhs
    rw [antipode_left_assoc]
  rw [Bimon.mul_counit, tensorHom_def', Category.assoc, ← whisker_exchange_assoc] at this
  simpa [unitors_equal]

/-!
## The antipode is an antihomomorphism with respect to both the monoid and comonoid structures.
-/

/-
**CategoryTheory.HopfObj.antipode_comul** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.HopfObj`。
形式化陈述：antipode_comul (A : C) [HopfObj A] : 𝒮[A] ≫ Δ[A] = Δ[A] ≫ (β_ _ _).hom ≫ (
𝒮[A] otimesₘ 𝒮[A])
参数：A : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `left_inv_eq_right_inv`：∀ {M : Type u_2} [inst : Monoid M] {a b c : M}, b
 * a = 1 → a * c = 1 → b = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Conv.mul_eq`：mul_eq (f g : Conv M N) : f * g = Δ[M] ≫ f ▷
 M ≫ N ◁ g ≫ μ[N]
· 使用定理 `CategoryTheory.Conv.one_eq`：one_eq : (1 : Conv M N) = ε[M] ≫ η[N]
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
· 使用定理 `CategoryTheory.MonoidalCategory.tensor_whiskerLeft`：tensor_whiskerLeft (
X Y : C) {Z Z' : C} (f : Z ⟶ Z') : (X otimes Y) ◁ f = (α_ X Y Z).hom ≫ X ◁ Y ◁ f
 ≫ (α_ X Y Z').inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.HopfObj.antipode_comul₁`：antipode_comul₁ (A : C) [HopfObj
 A] : Δ[A] ≫ 𝒮[A] ▷ A ≫ Δ[A] ▷ A ≫ (α_ A A A).hom ≫ A ◁ A ◁ Δ[A] ≫ A ◁ (α_ A A A
).inv ≫ A ◁ (β_ A A).hom ▷ A…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `CategoryTheory.HopfObj.antipode_comul₂`：antipode_comul₂ (A : C) [HopfObj
 A] : Δ[A] ≫ Δ[A] ▷ A ≫ (α_ A A A).hom ≫ A ◁ A ◁ Δ[A] ≫ A ◁ A ◁ (β_ A A).hom ≫ A
 ◁ A ◁ (𝒮[A] otimesₘ 𝒮[A]) ≫…

--- 原说明 ---
## The antipode is an antihomomorphism with respect to both the monoid and comon
oid structures.
-/
theorem antipode_comul₁ (A : C) [HopfObj A] :
    Δ[A] ≫
      𝒮[A] ▷ A ≫
      Δ[A] ▷ A ≫
      (α_ A A A).hom ≫
      A ◁ A ◁ Δ[A] ≫
      A ◁ (α_ A A A).inv ≫
      A ◁ (β_ A A).hom ▷ A ≫
      A ◁ (α_ A A A).hom ≫
      (α_ A A (A ⊗ A)).inv ≫
      (μ[A] ⊗ₘ μ[A]) =
    ε[A] ≫ (λ_ (𝟙_ C)).inv ≫ (η[A] ⊗ₘ η[A]) := by
  slice_lhs 3 5 =>
    rw [← associator_naturality_right, ← Category.assoc, ← tensorHom_def]
  slice_lhs 3 9 =>
    rw [Bimon.compatibility]
  slice_lhs 1 3 =>
    rw [antipode_left]
  simp [MonObj.tensorObj.one_def]

/--
Auxiliary calculation for `antipode_comul`.
This calculation calls for some ASCII art out of This Week's Finds.

```
   |   |
   n   n
  | \ / |
  |  /  |
  | / \ |
  | | S S
  | | \ /
  | |  /
  | | / \
  \ / \ /
   v   v
    \ /
     v
     |
```

We move the left antipode up through the crossing,
the right antipode down through the crossing,
the right multiplication down across the strand,
reassociate the comultiplications,
then use `antipode_right` then `antipode_left` to simplify.
-/
/-
**CategoryTheory.HopfObj.antipode_comul** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.HopfObj`。
形式化陈述：antipode_comul (A : C) [HopfObj A] : 𝒮[A] ≫ Δ[A] = Δ[A] ≫ (β_ _ _).hom ≫ (
𝒮[A] otimesₘ 𝒮[A])
参数：A : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `left_inv_eq_right_inv`：∀ {M : Type u_2} [inst : Monoid M] {a b c : M}, b
 * a = 1 → a * c = 1 → b = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Conv.mul_eq`：mul_eq (f g : Conv M N) : f * g = Δ[M] ≫ f ▷
 M ≫ N ◁ g ≫ μ[N]
· 使用定理 `CategoryTheory.Conv.one_eq`：one_eq : (1 : Conv M N) = ε[M] ≫ η[N]
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
· 使用定理 `CategoryTheory.MonoidalCategory.tensor_whiskerLeft`：tensor_whiskerLeft (
X Y : C) {Z Z' : C} (f : Z ⟶ Z') : (X otimes Y) ◁ f = (α_ X Y Z).hom ≫ X ◁ Y ◁ f
 ≫ (α_ X Y Z').inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.HopfObj.antipode_comul₁`：antipode_comul₁ (A : C) [HopfObj
 A] : Δ[A] ≫ 𝒮[A] ▷ A ≫ Δ[A] ▷ A ≫ (α_ A A A).hom ≫ A ◁ A ◁ Δ[A] ≫ A ◁ (α_ A A A
).inv ≫ A ◁ (β_ A A).hom ▷ A…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `CategoryTheory.HopfObj.antipode_comul₂`：antipode_comul₂ (A : C) [HopfObj
 A] : Δ[A] ≫ Δ[A] ▷ A ≫ (α_ A A A).hom ≫ A ◁ A ◁ Δ[A] ≫ A ◁ A ◁ (β_ A A).hom ≫ A
 ◁ A ◁ (𝒮[A] otimesₘ 𝒮[A]) ≫…

--- 原说明 ---
Auxiliary calculation for `antipode_comul`.
This calculation calls for some ASCII art out of This Week's Finds.

```
   |   |
   n   n
  | \ / |
  |  /  |
  | / \ |
  | | S S
  | | \ /
  | |  /
  | | / \
  \ / \ /
   v   v
    \ /
     v
     |
```

We move the left antipode up through the crossing,
the right antipode down through the crossing,
the right multiplication down across the strand,
reassociate the comultiplications,
then use `antipode_right` then `antipode_left` to simplify.
-/
theorem antipode_comul₂ (A : C) [HopfObj A] :
    Δ[A] ≫
      Δ[A] ▷ A ≫
      (α_ A A A).hom ≫
      A ◁ A ◁ Δ[A] ≫
      A ◁ A ◁ (β_ A A).hom ≫
      A ◁ A ◁ (𝒮[A] ⊗ₘ 𝒮[A]) ≫
      A ◁ (α_ A A A).inv ≫
      A ◁ (β_ A A).hom ▷ A ≫
      A ◁ (α_ A A A).hom ≫
      (α_ A A (A ⊗ A)).inv ≫
      (μ[A] ⊗ₘ μ[A]) =
    ε[A] ≫ (λ_ (𝟙_ C)).inv ≫ (η[A] ⊗ₘ η[A]) := by
  -- We should write a version of `slice_lhs` that zooms through whiskerings.
  slice_lhs 6 6 =>
    simp only [tensorHom_def', whiskerLeft_comp]
  slice_lhs 7 8 =>
    rw [← whiskerLeft_comp, associator_inv_naturality_middle, whiskerLeft_comp]
  slice_lhs 8 9 =>
    rw [← whiskerLeft_comp, ← comp_whiskerRight, BraidedCategory.braiding_naturality_right,
      comp_whiskerRight, whiskerLeft_comp]
  slice_lhs 9 10 =>
    rw [← whiskerLeft_comp, associator_naturality_left, whiskerLeft_comp]
  slice_lhs 5 6 =>
    rw [← whiskerLeft_comp, ← whiskerLeft_comp, ← BraidedCategory.braiding_naturality_left,
      whiskerLeft_comp, whiskerLeft_comp]
  slice_lhs 11 12 =>
    rw [tensorHom_def', ← Category.assoc, ← associator_inv_naturality_right]
  slice_lhs 10 11 =>
    rw [← whiskerLeft_comp, ← whisker_exchange, whiskerLeft_comp]
  slice_lhs 6 10 =>
    simp only [← whiskerLeft_comp]
    rw [← BraidedCategory.hexagon_reverse_assoc, Iso.inv_hom_id_assoc,
      ← BraidedCategory.braiding_naturality_left]
    simp only [whiskerLeft_comp]
  rw [ComonObj.comul_assoc_flip_assoc, Iso.inv_hom_id_assoc]
  slice_lhs 2 3 =>
    simp only [← whiskerLeft_comp]
    rw [ComonObj.comul_assoc]
    simp only [whiskerLeft_comp]
  slice_lhs 3 7 =>
    simp only [← whiskerLeft_comp]
    rw [← associator_naturality_middle_assoc, Iso.hom_inv_id_assoc]
    simp only [← comp_whiskerRight]
    rw [antipode_right]
    simp only [comp_whiskerRight]
    simp only [whiskerLeft_comp]
  slice_lhs 2 3 =>
    simp only [← whiskerLeft_comp]
    rw [ComonObj.counit_comul]
  slice_lhs 3 4 =>
    simp only [← whiskerLeft_comp]
    rw [BraidedCategory.braiding_naturality_left]
    simp only [whiskerLeft_comp]
  slice_lhs 4 5 =>
    simp only [← whiskerLeft_comp]
    rw [whisker_exchange]
    simp only [whiskerLeft_comp]
  slice_lhs 5 7 =>
    rw [associator_inv_naturality_right_assoc, whisker_exchange]
  simp only [braiding_tensorUnit_left,
    whiskerLeft_comp, whiskerLeft_rightUnitor_inv,
    whiskerRight_id, whiskerLeft_rightUnitor, Category.assoc, Iso.hom_inv_id_assoc,
    Iso.inv_hom_id_assoc, whiskerLeft_inv_hom_assoc, antipode_right_assoc]
  rw [rightUnitor_inv_naturality_assoc, tensorHom_def]
  monoidal

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.HopfObj.antipode_comul** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.HopfObj`。
形式化陈述：antipode_comul (A : C) [HopfObj A] : 𝒮[A] ≫ Δ[A] = Δ[A] ≫ (β_ _ _).hom ≫ (
𝒮[A] otimesₘ 𝒮[A])
参数：A : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `left_inv_eq_right_inv`：∀ {M : Type u_2} [inst : Monoid M] {a b c : M}, b
 * a = 1 → a * c = 1 → b = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Conv.mul_eq`：mul_eq (f g : Conv M N) : f * g = Δ[M] ≫ f ▷
 M ≫ N ◁ g ≫ μ[N]
· 使用定理 `CategoryTheory.Conv.one_eq`：one_eq : (1 : Conv M N) = ε[M] ≫ η[N]
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
· 使用定理 `CategoryTheory.MonoidalCategory.tensor_whiskerLeft`：tensor_whiskerLeft (
X Y : C) {Z Z' : C} (f : Z ⟶ Z') : (X otimes Y) ◁ f = (α_ X Y Z).hom ≫ X ◁ Y ◁ f
 ≫ (α_ X Y Z').inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.HopfObj.antipode_comul₁`：antipode_comul₁ (A : C) [HopfObj
 A] : Δ[A] ≫ 𝒮[A] ▷ A ≫ Δ[A] ▷ A ≫ (α_ A A A).hom ≫ A ◁ A ◁ Δ[A] ≫ A ◁ (α_ A A A
).inv ≫ A ◁ (β_ A A).hom ▷ A…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `CategoryTheory.HopfObj.antipode_comul₂`：antipode_comul₂ (A : C) [HopfObj
 A] : Δ[A] ≫ Δ[A] ▷ A ≫ (α_ A A A).hom ≫ A ◁ A ◁ Δ[A] ≫ A ◁ A ◁ (β_ A A).hom ≫ A
 ◁ A ◁ (𝒮[A] otimesₘ 𝒮[A]) ≫…
-/
theorem antipode_comul (A : C) [HopfObj A] :
    𝒮[A] ≫ Δ[A] = Δ[A] ≫ (β_ _ _).hom ≫ (𝒮[A] ⊗ₘ 𝒮[A]) := by
  -- Again, it is a "left inverse equals right inverse" argument in the convolution monoid.
  apply left_inv_eq_right_inv
    (M := Conv A (A ⊗ A))
    (a := Δ[A])
  · rw [Conv.mul_eq, Conv.one_eq]
    simp only [comp_whiskerRight, tensor_whiskerLeft, MonObj.tensorObj.mul_def, Category.assoc,
      MonObj.tensorObj.one_def]
    simp only [tensorμ]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact antipode_comul₁ A
  · rw [Conv.mul_eq, Conv.one_eq]
    simp only [whiskerLeft_comp, tensor_whiskerLeft, Category.assoc, Iso.inv_hom_id_assoc,
      MonObj.tensorObj.mul_def, MonObj.tensorObj.one_def]
    simp only [tensorμ]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact antipode_comul₂ A
/-
**CategoryTheory.HopfObj.mul_antipode** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
HopfObj`。
形式化陈述：mul_antipode (A : C) [HopfObj A] : μ[A] ≫ 𝒮[A] = (𝒮[A] otimesₘ 𝒮[A]) ≫ (β_
 _ _).hom ≫ μ[A]
参数：A : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `left_inv_eq_right_inv`：∀ {M : Type u_2} [inst : Monoid M] {a b c : M}, b
 * a = 1 → a * c = 1 → b = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Conv.mul_eq`：mul_eq (f g : Conv M N) : f * g = Δ[M] ≫ f ▷
 M ≫ N ◁ g ≫ μ[N]
· 使用定理 `CategoryTheory.Conv.one_eq`：one_eq : (1 : Conv M N) = ε[M] ≫ η[N]
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Comon.tensorObj_comul`：tensorObj_comul (A B : C) [ComonOb
j A] [ComonObj B] : Δ[A otimes B] = (Δ[A] otimesₘ Δ[B]) ≫ tensorμ A A B B
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_tensor`：whiskerRight_tensor
 {X X' : C} (f : X ⟶ X') (Y Z : C) : f ▷ (Y otimes Z) = (α_ X Y Z).inv ≫ f ▷ Y ▷
 Z ≫ (α_ X' Y Z).hom
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MonoidalCategory.pentagon_hom_inv_inv_inv_inv_assoc`：∀ {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Mo
noidalCategory C] {W X Y Z Z_1 : C}   (h :     CategoryT…
· 使用定理 `CategoryTheory.HopfObj.mul_antipode₁`：mul_antipode₁ (A : C) [HopfObj A] 
: (Δ[A] otimesₘ Δ[A]) ≫ (α_ A A (A otimes A)).hom ≫ A ◁ (α_ A A A).inv ≫ A ◁ (β_
 A A).hom ▷ A ≫ (α_ A (A o…
· 使用定理 `CategoryTheory.BraidedCategory.braiding_naturality_assoc`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCate
gory C]   [inst_2 : CategoryTheory.BraidedCate…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `CategoryTheory.HopfObj.mul_antipode₂`：mul_antipode₂ (A : C) [HopfObj A] 
: (Δ[A] otimesₘ Δ[A]) ≫ (α_ A A (A otimes A)).hom ≫ A ◁ (α_ A A A).inv ≫ A ◁ (β_
 A A).hom ▷ A ≫ (α_ A (A o…
-/
theorem mul_antipode₁ (A : C) [HopfObj A] :
    (Δ[A] ⊗ₘ Δ[A]) ≫
      (α_ A A (A ⊗ A)).hom ≫
      A ◁ (α_ A A A).inv ≫
      A ◁ (β_ A A).hom ▷ A ≫
      (α_ A (A ⊗ A) A).inv ≫
      (α_ A A A).inv ▷ A ≫
      μ[A] ▷ A ▷ A ≫
      𝒮[A] ▷ A ▷ A ≫
      (α_ A A A).hom ≫
      A ◁ μ[A] ≫
      μ[A] =
    (ε[A] ⊗ₘ ε[A]) ≫ (λ_ (𝟙_ C)).hom ≫ η[A] := by
  slice_lhs 8 9 =>
    rw [associator_naturality_left]
  slice_lhs 9 10 =>
    rw [← whisker_exchange]
  slice_lhs 7 8 =>
    rw [associator_naturality_left]
  slice_lhs 8 9 =>
    rw [← tensorHom_def]
  simp


/--
Auxiliary calculation for `mul_antipode`.

```
       |
       n
      /  \
     |   n
     |  / \
     |  S S
     |  \ /
     n   /
    / \ / \
    |  /  |
    \ / \ /
     v   v
     |   |
```

We move the leftmost multiplication up, so we can reassociate.
We then move the rightmost comultiplication under the strand,
and simplify using `antipode_right`.
-/
/-
**CategoryTheory.HopfObj.mul_antipode** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
HopfObj`。
形式化陈述：mul_antipode (A : C) [HopfObj A] : μ[A] ≫ 𝒮[A] = (𝒮[A] otimesₘ 𝒮[A]) ≫ (β_
 _ _).hom ≫ μ[A]
参数：A : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `left_inv_eq_right_inv`：∀ {M : Type u_2} [inst : Monoid M] {a b c : M}, b
 * a = 1 → a * c = 1 → b = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Conv.mul_eq`：mul_eq (f g : Conv M N) : f * g = Δ[M] ≫ f ▷
 M ≫ N ◁ g ≫ μ[N]
· 使用定理 `CategoryTheory.Conv.one_eq`：one_eq : (1 : Conv M N) = ε[M] ≫ η[N]
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Comon.tensorObj_comul`：tensorObj_comul (A B : C) [ComonOb
j A] [ComonObj B] : Δ[A otimes B] = (Δ[A] otimesₘ Δ[B]) ≫ tensorμ A A B B
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_tensor`：whiskerRight_tensor
 {X X' : C} (f : X ⟶ X') (Y Z : C) : f ▷ (Y otimes Z) = (α_ X Y Z).inv ≫ f ▷ Y ▷
 Z ≫ (α_ X' Y Z).hom
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MonoidalCategory.pentagon_hom_inv_inv_inv_inv_assoc`：∀ {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Mo
noidalCategory C] {W X Y Z Z_1 : C}   (h :     CategoryT…
· 使用定理 `CategoryTheory.HopfObj.mul_antipode₁`：mul_antipode₁ (A : C) [HopfObj A] 
: (Δ[A] otimesₘ Δ[A]) ≫ (α_ A A (A otimes A)).hom ≫ A ◁ (α_ A A A).inv ≫ A ◁ (β_
 A A).hom ▷ A ≫ (α_ A (A o…
· 使用定理 `CategoryTheory.BraidedCategory.braiding_naturality_assoc`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCate
gory C]   [inst_2 : CategoryTheory.BraidedCate…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `CategoryTheory.HopfObj.mul_antipode₂`：mul_antipode₂ (A : C) [HopfObj A] 
: (Δ[A] otimesₘ Δ[A]) ≫ (α_ A A (A otimes A)).hom ≫ A ◁ (α_ A A A).inv ≫ A ◁ (β_
 A A).hom ▷ A ≫ (α_ A (A o…

--- 原说明 ---
Auxiliary calculation for `mul_antipode`.

```
       |
       n
      /  \
     |   n
     |  / \
     |  S S
     |  \ /
     n   /
    / \ / \
    |  /  |
    \ / \ /
     v   v
     |   |
```

We move the leftmost multiplication up, so we can reassociate.
We then move the rightmost comultiplication under the strand,
and simplify using `antipode_right`.
-/
theorem mul_antipode₂ (A : C) [HopfObj A] :
    (Δ[A] ⊗ₘ Δ[A]) ≫
      (α_ A A (A ⊗ A)).hom ≫
      A ◁ (α_ A A A).inv ≫
      A ◁ (β_ A A).hom ▷ A ≫
      (α_ A (A ⊗ A) A).inv ≫
      (α_ A A A).inv ▷ A ≫
      μ[A] ▷ A ▷ A ≫
      (α_ A A A).hom ≫
      A ◁ (β_ A A).hom ≫
      A ◁ (𝒮[A] ⊗ₘ 𝒮[A]) ≫
      A ◁ μ[A] ≫ μ[A] =
    (ε[A] ⊗ₘ ε[A]) ≫ (λ_ (𝟙_ C)).hom ≫ η[A] := by
  slice_lhs 7 8 =>
    rw [associator_naturality_left]
  slice_lhs 8 9 =>
    rw [← whisker_exchange]
  slice_lhs 9 10 =>
    rw [← whisker_exchange]
  slice_lhs 11 12 =>
    rw [MonObj.mul_assoc_flip]
  slice_lhs 10 11 =>
    rw [associator_inv_naturality_left]
  slice_lhs 11 12 =>
    simp only [← comp_whiskerRight]
    rw [MonObj.mul_assoc]
    simp only [comp_whiskerRight]
  rw [tensorHom_def]
  rw [tensor_whiskerLeft _ _ (β_ A A).hom]
  rw [pentagon_inv_inv_hom_hom_inv_assoc]
  slice_lhs 7 8 =>
    rw [Iso.inv_hom_id]
  rw [Category.id_comp]
  slice_lhs 5 7 =>
    simp only [← whiskerLeft_comp]
    rw [← BraidedCategory.hexagon_forward]
    simp only [whiskerLeft_comp]
  simp only [tensor_whiskerLeft, Category.assoc, Iso.inv_hom_id_assoc, pentagon_inv_inv_hom_inv_inv,
    whisker_assoc, MonObj.mul_assoc, whiskerLeft_inv_hom_assoc]
  slice_lhs 3 4 =>
    simp only [← whiskerLeft_comp]
    rw [BraidedCategory.braiding_naturality_right]
    simp only [whiskerLeft_comp]
  rw [tensorHom_def']
  simp only [whiskerLeft_comp]
  slice_lhs 5 6 =>
    simp only [← whiskerLeft_comp]
    rw [← associator_naturality_right]
    simp only [whiskerLeft_comp]
  slice_lhs 4 5 =>
    simp only [← whiskerLeft_comp]
    rw [← whisker_exchange]
    simp only [whiskerLeft_comp]
  slice_lhs 5 9 =>
    simp only [← whiskerLeft_comp]
    rw [associator_inv_naturality_middle_assoc, Iso.hom_inv_id_assoc]
    simp only [← comp_whiskerRight]
    rw [antipode_right]
    simp only [comp_whiskerRight]
    simp only [whiskerLeft_comp]
  slice_lhs 6 7 =>
    simp only [← whiskerLeft_comp]
    rw [MonObj.one_mul]
  slice_lhs 3 4 =>
    simp only [← whiskerLeft_comp]
    rw [← BraidedCategory.braiding_naturality_left]
    simp only [whiskerLeft_comp]
  slice_lhs 4 5 =>
    simp only [← whiskerLeft_comp]
    rw [← BraidedCategory.braiding_naturality_right]
    simp only [whiskerLeft_comp]
  rw [← associator_naturality_middle_assoc]
  simp only [braiding_tensorUnit_right, whiskerLeft_comp]
  slice_lhs 6 7 =>
    simp only [← whiskerLeft_comp]
    rw [Iso.inv_hom_id]
  simp only [whiskerLeft_id, Category.id_comp]
  slice_lhs 5 6 =>
    rw [whiskerLeft_rightUnitor, Category.assoc, ← rightUnitor_naturality]
  rw [associator_inv_naturality_right_assoc, Iso.hom_inv_id_assoc]
  slice_lhs 3 4 =>
    rw [whisker_exchange]
  slice_lhs 1 3 =>
    simp only [← comp_whiskerRight]
    rw [antipode_right]
    simp only [comp_whiskerRight]
  slice_lhs 2 3 =>
    rw [← whisker_exchange]
  slice_lhs 1 2 =>
    rw [← tensorHom_def]
  slice_lhs 2 3 =>
    rw [rightUnitor_naturality]
  monoidal

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.HopfObj.mul_antipode** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
HopfObj`。
形式化陈述：mul_antipode (A : C) [HopfObj A] : μ[A] ≫ 𝒮[A] = (𝒮[A] otimesₘ 𝒮[A]) ≫ (β_
 _ _).hom ≫ μ[A]
参数：A : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `left_inv_eq_right_inv`：∀ {M : Type u_2} [inst : Monoid M] {a b c : M}, b
 * a = 1 → a * c = 1 → b = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Conv.mul_eq`：mul_eq (f g : Conv M N) : f * g = Δ[M] ≫ f ▷
 M ≫ N ◁ g ≫ μ[N]
· 使用定理 `CategoryTheory.Conv.one_eq`：one_eq : (1 : Conv M N) = ε[M] ≫ η[N]
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Comon.tensorObj_comul`：tensorObj_comul (A B : C) [ComonOb
j A] [ComonObj B] : Δ[A otimes B] = (Δ[A] otimesₘ Δ[B]) ≫ tensorμ A A B B
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_tensor`：whiskerRight_tensor
 {X X' : C} (f : X ⟶ X') (Y Z : C) : f ▷ (Y otimes Z) = (α_ X Y Z).inv ≫ f ▷ Y ▷
 Z ≫ (α_ X' Y Z).hom
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MonoidalCategory.pentagon_hom_inv_inv_inv_inv_assoc`：∀ {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Mo
noidalCategory C] {W X Y Z Z_1 : C}   (h :     CategoryT…
· 使用定理 `CategoryTheory.HopfObj.mul_antipode₁`：mul_antipode₁ (A : C) [HopfObj A] 
: (Δ[A] otimesₘ Δ[A]) ≫ (α_ A A (A otimes A)).hom ≫ A ◁ (α_ A A A).inv ≫ A ◁ (β_
 A A).hom ▷ A ≫ (α_ A (A o…
· 使用定理 `CategoryTheory.BraidedCategory.braiding_naturality_assoc`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCate
gory C]   [inst_2 : CategoryTheory.BraidedCate…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用定理 `CategoryTheory.HopfObj.mul_antipode₂`：mul_antipode₂ (A : C) [HopfObj A] 
: (Δ[A] otimesₘ Δ[A]) ≫ (α_ A A (A otimes A)).hom ≫ A ◁ (α_ A A A).inv ≫ A ◁ (β_
 A A).hom ▷ A ≫ (α_ A (A o…
-/
theorem mul_antipode (A : C) [HopfObj A] :
    μ[A] ≫ 𝒮[A] = (𝒮[A] ⊗ₘ 𝒮[A]) ≫ (β_ _ _).hom ≫ μ[A] := by
  -- Again, it is a "left inverse equals right inverse" argument in the convolution monoid.
  apply left_inv_eq_right_inv
    (M := Conv (A ⊗ A) A)
    (a := μ[A])
  · -- Unfold the algebra structure in the convolution monoid,
    -- then `simp?, simp only [tensor_μ], simp?`.
    rw [Conv.mul_eq, Conv.one_eq]
    simp only [Comon.tensorObj_comul, whiskerRight_tensor, comp_whiskerRight, Category.assoc,
      Comon.tensorObj_counit]
    simp only [tensorμ]
    simp only [Category.assoc, pentagon_hom_inv_inv_inv_inv_assoc]
    exact mul_antipode₁ A
  · rw [Conv.mul_eq, Conv.one_eq]
    simp only [Comon.tensorObj_comul, whiskerRight_tensor,
      BraidedCategory.braiding_naturality_assoc, whiskerLeft_comp, Category.assoc,
      Comon.tensorObj_counit]
    simp only [tensorμ]
    simp only [Category.assoc, pentagon_hom_inv_inv_inv_inv_assoc]
    exact mul_antipode₂ A

set_option backward.isDefEq.respectTransparency.types false in
/--
In a commutative Hopf algebra, the antipode squares to the identity.
-/
/-
**CategoryTheory.HopfObj.antipode_antipode** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.HopfObj`。
形式化陈述：antipode_antipode (A : C) [HopfObj A] (comm : (β_ _ _).hom ≫ μ[A] = μ[A]) 
: 𝒮[A] ≫ 𝒮[A] = 𝟙 A
参数：A : C；comm : (β_ _ _).hom ≫ μ[A] = μ[A]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `left_inv_eq_right_inv`：∀ {M : Type u_2} [inst : Monoid M] {a b c : M}, b
 * a = 1 → a * c = 1 → b = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Conv.mul_eq`：mul_eq (f g : Conv M N) : f * g = Δ[M] ≫ f ▷
 M ≫ N ◁ g ≫ μ[N]
· 使用定理 `CategoryTheory.Conv.one_eq`：one_eq : (1 : Conv M N) = ε[M] ≫ η[N]
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def_assoc`：∀ {C : Type u} {𝒞 :
 CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X
₁ Y₁ X₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `CategoryTheory.HopfObj.mul_antipode`：mul_antipode (A : C) [HopfObj A] : 
μ[A] ≫ 𝒮[A] = (𝒮[A] otimesₘ 𝒮[A]) ≫ (β_ _ _).hom ≫ μ[A]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.HopfObj.antipode_left_assoc`：∀ {C : Type u₁} {inst : Cate
goryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C}   {
inst_2 : CategoryTheory.BraidedC…
· 使用定理 `CategoryTheory.HopfObj.one_antipode`：one_antipode (A : C) [HopfObj A] : 
η[A] ≫ 𝒮[A] = η[A]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_id`：∀ {C : Type u} {𝒞 : Cate
goryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y : 
C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.HopfObj.antipode_left`：∀ {C : Type u₁} {inst : CategoryTh
eory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C}   {inst_2
 : CategoryTheory.BraidedC…

--- 原说明 ---
In a commutative Hopf algebra, the antipode squares to the identity.
-/
theorem antipode_antipode (A : C) [HopfObj A] (comm : (β_ _ _).hom ≫ μ[A] = μ[A]) :
    𝒮[A] ≫ 𝒮[A] = 𝟙 A := by
  -- Again, it is a "left inverse equals right inverse" argument in the convolution monoid.
  apply left_inv_eq_right_inv
    (M := Conv A A)
    (a := 𝒮[A])
  · -- Unfold the algebra structure in the convolution monoid,
    -- then `simp?`.
    rw [Conv.mul_eq, Conv.one_eq]
    simp only [comp_whiskerRight, Category.assoc]
    rw [← comm, ← tensorHom_def_assoc, ← mul_antipode]
    simp
  · rw [Conv.mul_eq, Conv.one_eq]
    simp

end HopfObj

end CategoryTheory

