/-
Copyright (c) 2026 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.CategoryTheory.Preadditive.FreydCategory.Homotopy
public import Mathlib.CategoryTheory.Quotient.Preadditive

/-!
# The right Freyd category

Let `V` be a preadditive category. The right Freyd category of `V` is the quotient of
`Arrow V` by the right homotopy relation. (This is simply called "Freyd category"
in the reference.) This is a preadditive category with a fully
faithful additive functor `RightFreyd.functor : V ⥤ RightFreyd V`.

We also show that, if `V` has binary biproducts, then `RightFreyd V` has cokernels. In fact
we construct, given a morphism `f : u ⟶ v` in `Arrow V`, a morphism
`Candidate.π f : v ⟶ Candidate.cokernel f` in `Arrow V` such that
`f ≫ Candidate.π f` is right homotopic to `0` (see `Candidate.condition`).
This allows us to define a cokernel cofork for `(quotient V).map f` (see
`Candidate.cokernelCofork`), and we show in `Candidate.isColimitCokernelCofork` that this is
a cokernel cofork.

## References
* [Posur, S., *A constructive approach to Freyd categories*][posur2021Freyd]

-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits Arrow

variable (V : Type*) [Category* V] [Preadditive V]

namespace CategoryTheory.Preadditive

/-- If `V` is a preadditive category, then `RightFreyd V` is the category of arrows in `V`,
with morphisms identified when they are right homotopic. -/
/-
**CategoryTheory.Preadditive.RightFreyd** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Preadditive`。
形式化陈述：RightFreyd
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `V` is a preadditive category, then `RightFreyd V` is the category of arrows 
in `V`,
with morphisms identified when they are right homotopic.
-/
def RightFreyd :=
  CategoryTheory.Quotient (rightHomotopic V)
/-
**CategoryTheory.Preadditive.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Preaddit
ive`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (RightFreyd V) :=
  inferInstanceAs <| Category (CategoryTheory.Quotient (rightHomotopic V))

/-- The category `RightFreyd V` is preadditive. -/
/-
**CategoryTheory.Preadditive.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Preaddit
ive`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category `RightFreyd V` is preadditive.
-/
instance : Preadditive (RightFreyd V) :=
  Quotient.preadditive _ (by
    rintro _ _ _ _ _ _ ⟨h⟩ ⟨h'⟩
    exact ⟨RightHomotopy.add h h'⟩)

namespace RightFreyd

/-- The quotient functor from `Arrow V` to `RightFreyd V`. -/
/-
**CategoryTheory.Preadditive.RightFreyd.quotient** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Preadditive.RightFreyd`。
形式化陈述：quotient : Arrow V ⥤ RightFreyd V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quotient functor from `Arrow V` to `RightFreyd V`.
-/
def quotient : Arrow V ⥤ RightFreyd V :=
  CategoryTheory.Quotient.functor _
/-
**CategoryTheory.Preadditive.RightFreyd.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Preadditive.RightFreyd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (quotient V).Full := Quotient.full_functor _
/-
**CategoryTheory.Preadditive.RightFreyd.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Preadditive.RightFreyd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (quotient V).EssSurj := Quotient.essSurj_functor _
/-
**CategoryTheory.Preadditive.RightFreyd.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Preadditive.RightFreyd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (quotient V).Additive where

variable {V}

/-- If two morphisms in `Arrow V` are right homotopic, then they become equal in the right
Freyd category. -/
/-
**CategoryTheory.Preadditive.RightFreyd.eq_of_rightHomotopy** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Preadditive.RightFreyd`。
形式化陈述：eq_of_rightHomotopy {u v : Arrow V} (f g : u ⟶ v) (h : RightHomotopy f g) 
: (quotient V).map f = (quotient V).map g
参数：f g : u ⟶ v；h : RightHomotopy f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Quotient.sound`：∀ {C : Type u_1} [inst : CategoryTheory.C
ategory.{v_1, u_1} C] (r : HomRel C) {a b : C} {f₁ f₂ : a ⟶ b},   r f₁ f₂ → (Cat
egoryTheory.Quotien…

--- 原说明 ---
If two morphisms in `Arrow V` are right homotopic, then they become equal in the
 right
Freyd category.
-/
theorem eq_of_rightHomotopy {u v : Arrow V} (f g : u ⟶ v) (h : RightHomotopy f g) :
    (quotient V).map f = (quotient V).map g :=
  CategoryTheory.Quotient.sound _ ⟨h⟩

/-- If two morphisms of `Arrow V` become equal in the right Freyd category,
then they are right homotopic. -/
/-
**CategoryTheory.Preadditive.RightFreyd.homotopyOfEq** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Preadditive.RightFreyd`。
形式化陈述：homotopyOfEq {u v : Arrow V} (f g : u ⟶ v) (w : (quotient V).map f = (quot
ient V).map g) : RightHomotopy f g
参数：f g : u ⟶ v；w : (quotient V).map f = (quotient V).map g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If two morphisms of `Arrow V` become equal in the right Freyd category,
then they are right homotopic.
-/
def homotopyOfEq {u v : Arrow V} (f g : u ⟶ v)
    (w : (quotient V).map f = (quotient V).map g) : RightHomotopy f g :=
  ((Quotient.functor_map_eq_iff _ _ _).mp w).some

variable {u v : Arrow V} (f g : u ⟶ v)

/-- Two morphisms in `Arrow V` have the same image in `RightFreyd V` if and only if there
exists a right homotopy between them. -/
/-
**CategoryTheory.Preadditive.RightFreyd.quotient_map_eq_iff** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Preadditive.RightFreyd`。
形式化陈述：quotient_map_eq_iff : (quotient V).map f = (quotient V).map g ↔ Nonempty (
RightHomotopy f g)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Preadditive.RightFreyd.eq_of_rightHomotopy`：eq_of_rightHo
motopy {u v : Arrow V} (f g : u ⟶ v) (h : RightHomotopy f g) : (quotient V).map 
f = (quotient V).map g

--- 原说明 ---
Two morphisms in `Arrow V` have the same image in `RightFreyd V` if and only if 
there
exists a right homotopy between them.
-/
lemma quotient_map_eq_iff :
    (quotient V).map f = (quotient V).map g ↔ Nonempty (RightHomotopy f g) :=
  ⟨fun h ↦ ⟨homotopyOfEq _ _ (by simpa using h)⟩,
    fun ⟨h⟩ ↦ by simpa using eq_of_rightHomotopy _ _ h⟩

/-- A morphism `f` in `Arrow V` is sent to `0` in `RightFreyd V` if and only if there
exists a right homotopy between `f` and `0`. -/
/-
**CategoryTheory.Preadditive.RightFreyd.quotient_map_eq_zero_iff** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.Preadditive.RightFreyd`。
形式化陈述：quotient_map_eq_zero_iff : (quotient V).map f = 0 ↔ Nonempty (RightHomotop
y f 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Preadditive.RightFreyd.instAdditiveArrowQuotient`：∀ (V : 
Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} V] [inst_1 : CategoryTheory
.Preadditive V],   (CategoryTheory.Preadditive.RightF…
· 使用定理 `CategoryTheory.Preadditive.RightFreyd.eq_of_rightHomotopy`：eq_of_rightHo
motopy {u v : Arrow V} (f g : u ⟶ v) (h : RightHomotopy f g) : (quotient V).map 
f = (quotient V).map g

--- 原说明 ---
A morphism `f` in `Arrow V` is sent to `0` in `RightFreyd V` if and only if ther
e
exists a right homotopy between `f` and `0`.
-/
lemma quotient_map_eq_zero_iff : (quotient V).map f = 0 ↔ Nonempty (RightHomotopy f 0) :=
  ⟨fun h ↦ ⟨homotopyOfEq _ _ (by simpa using h)⟩,
    fun ⟨h⟩ ↦ by simpa using eq_of_rightHomotopy _ _ h⟩

/-- If `f` is a morphism of `Arrow V` such that `f.right` is an isomorphism, then the image of `f`
in the right Freyd category is an epimorphism. -/
/-
**CategoryTheory.Preadditive.RightFreyd.epi_of_isIso_right** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Preadditive.RightFreyd`。
形式化陈述：epi_of_isIso_right [IsIso f.right] : Epi ((quotient V).map f) where left_c
ancellation g₁ g₂ eq
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_surjective`：map_surjective (F : C ⥤ D) [Full 
F] : Function.Surjective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `CategoryTheory.Preadditive.RightFreyd.instFullArrowQuotient`：∀ (V : Type
 u_1) [inst : CategoryTheory.Category.{v_1, u_1} V] [inst_1 : CategoryTheory.Pre
additive V],   (CategoryTheory.Preadditive.RightF…
· 使用定理 `CategoryTheory.Preadditive.RightFreyd.eq_of_rightHomotopy`：eq_of_rightHo
motopy {u v : Arrow V} (f g : u ⟶ v) (h : RightHomotopy f g) : (quotient V).map 
f = (quotient V).map g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Preadditive.comp_sub`：comp_sub : f ≫ (g - g') = f ≫ g - f
 ≫ g'
· 使用定理 `CategoryTheory.Arrow.RightHomotopy.comm`：∀ {V : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} V] [inst_1 : CategoryTheory.Preadditive V]   {u v :
 CategoryTheory.Arrow V} {f g…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `f` is a morphism of `Arrow V` such that `f.right` is an isomorphism, then th
e image of `f`
in the right Freyd category is an epimorphism.
-/
lemma epi_of_isIso_right [IsIso f.right] : Epi ((quotient V).map f) where
  left_cancellation g₁ g₂ eq := by
    obtain ⟨g₁, rfl⟩ := (quotient V).map_surjective g₁
    obtain ⟨g₂, rfl⟩ := (quotient V).map_surjective g₂
    set h : RightHomotopy (f ≫ g₁) (f ≫ g₂) := homotopyOfEq _ _ eq
    exact eq_of_rightHomotopy _ _ ⟨inv f.right ≫ h.hom, by simp [dsimp% h.comm]⟩

section Functor

variable [HasZeroObject V]

variable (V)

open ZeroObject in
set_option backward.defeqAttrib.useBackward true in
/-- If `V` has a zero object, this is the functor from `V` to `Arrow V`
that sends an object `X` to the arrow `0 ⟶ X`. -/
@[simps]
/-
**CategoryTheory.Preadditive.RightFreyd.rightFunctor** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Preadditive.RightFreyd`。
形式化陈述：rightFunctor : V ⥤ Arrow V where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `V` has a zero object, this is the functor from `V` to `Arrow V`
that sends an object `X` to the arrow `0 ⟶ X`.
-/
def rightFunctor : V ⥤ Arrow V where
  obj X := Arrow.mk (0 : 0 ⟶ X)
  map f := Arrow.homMk 0 f

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Preadditive.RightFreyd.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Preadditive.RightFreyd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (rightFunctor V).Additive where
  map_add {_ _ _ _} := by cat_disch

/-- The fully faithful additive functor from  `V` to `RightFreyd V` sending an object `X` of `V`
to the class of the arrow `0 ⟶ X`. -/
/-
**CategoryTheory.Preadditive.RightFreyd.functor** 是 Mathlib 中的一个缩写定义，位于命名空间 `Cat
egoryTheory.Preadditive.RightFreyd`。
形式化陈述：functor : V ⥤ RightFreyd V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fully faithful additive functor from  `V` to `RightFreyd V` sending an objec
t `X` of `V`
to the class of the arrow `0 ⟶ X`.
-/
abbrev functor : V ⥤ RightFreyd V := rightFunctor V ⋙ quotient V
/-
**CategoryTheory.Preadditive.RightFreyd.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Preadditive.RightFreyd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (functor V).Additive := by dsimp [functor]; infer_instance

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Preadditive.RightFreyd.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Preadditive.RightFreyd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (functor V).Full where
  map_surjective a := by
    obtain ⟨u, rfl⟩ := (quotient V).map_surjective a
    exact ⟨u.right, (quotient V).congr_map (by cat_disch)⟩

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Preadditive.RightFreyd.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Preadditive.RightFreyd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (functor V).Faithful where
  map_injective {_ _} f g eq := by
    dsimp at eq
    rw [quotient_map_eq_iff] at eq
    simpa [← sub_eq_zero] using! eq.some.comm

end Functor

variable [HasBinaryBiproducts V]

variable {u v : Arrow V} (f : u ⟶ v)

namespace Candidate

/-- If `f` is a morphism of `Arrow V`, this is a "candidate cokernel" of `f`, i.e. an object
in `Arrow V` whose image in `RightFreyd V` will be a cokernel of the image of `f`. -/
/-
**CategoryTheory.Preadditive.RightFreyd.Candidate.cokernel** 是 Mathlib 中的一个缩写定义，
位于命名空间 `CategoryTheory.Preadditive.RightFreyd.Candidate`。
形式化陈述：cokernel
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is a morphism of `Arrow V`, this is a "candidate cokernel" of `f`, i.e. a
n object
in `Arrow V` whose image in `RightFreyd V` will be a cokernel of the image of `f
`.
-/
abbrev cokernel := Arrow.mk (biprod.desc v.hom f.right)

set_option backward.isDefEq.respectTransparency false in
/-- For `f : u ⟶ v` a morphism in `Arrow V`, this is the morphism `v ⟶ cokernel f` from `v` to
the "candidate cokernel" of `f`, whose image in `RightFreyd V` will be the projection to
the cokernel of the image of `f`. -/
/-
**CategoryTheory.Preadditive.RightFreyd.Candidate.** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Preadditive.RightFreyd.Candidate`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `f : u ⟶ v` a morphism in `Arrow V`, this is the morphism `v ⟶ cokernel f` f
rom `v` to
the "candidate cokernel" of `f`, whose image in `RightFreyd V` will be the proje
ction to
the cokernel of the image of `f`.
-/
def π : v ⟶ cokernel f := Arrow.homMk biprod.inl (𝟙 v.right)

set_option backward.isDefEq.respectTransparency false in
/-- The right homotopy expressing that `f ≫ π f` is sent to `0` in `RightFreyd V`. -/
/-
**CategoryTheory.Preadditive.RightFreyd.Candidate.condition** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Preadditive.RightFreyd.Candidate`。
形式化陈述：condition : RightHomotopy (f ≫ π f) 0 where hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right homotopy expressing that `f ≫ π f` is sent to `0` in `RightFreyd V`.
-/
def condition : RightHomotopy (f ≫ π f) 0 where
  hom := biprod.inr
  comm := by simp [π]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Preadditive.RightFreyd.Candidate.** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory.Preadditive.RightFreyd.Candidate`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Epi ((quotient V).map (π f)) :=
  have : IsIso ((π f).right) := by simp only [π, homMk_right]; infer_instance
  epi_of_isIso_right _

variable {w : Arrow V} (g : v ⟶ w) (h : RightHomotopy (f ≫ g) 0)

set_option backward.isDefEq.respectTransparency false in
/-- If `f : u ⟶ v` and `g : v ⟶ w` are morphisms in `Arrow V` such that `f ≫ g` is right
homotopic to `0`, this is the morphism from the "candidate cokernel" of `f` to `w` defined
from the right homotopy. -/
/-
**CategoryTheory.Preadditive.RightFreyd.Candidate.desc** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Preadditive.RightFreyd.Candidate`。
形式化陈述：desc : cokernel f ⟶ w
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : u ⟶ v` and `g : v ⟶ w` are morphisms in `Arrow V` such that `f ≫ g` is r
ight
homotopic to `0`, this is the morphism from the "candidate cokernel" of `f` to `
w` defined
from the right homotopy.
-/
def desc : cokernel f ⟶ w :=
  Arrow.homMk (biprod.desc g.left h.hom) g.right (biprod.hom_ext' _ _ (by simp)
    (by simp [← h.comm]))

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Preadditive.RightFreyd.Candidate.** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Preadditive.RightFreyd.Candidate`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma π_desc : π f ≫ desc f g h = g := by ext <;> simp [π, desc]

/-- For `f` a morphism in `Arrow V`, this is a cokernel cofork of `(quotient V).map f`. -/
/-
**CategoryTheory.Preadditive.RightFreyd.Candidate.cokernelCofork** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.Preadditive.RightFreyd.Candidate`。
形式化陈述：cokernelCofork : CokernelCofork ((quotient V).map f)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `f` a morphism in `Arrow V`, this is a cokernel cofork of `(quotient V).map 
f`.
-/
def cokernelCofork : CokernelCofork ((quotient V).map f) :=
  CokernelCofork.ofπ ((quotient V).map (Candidate.π f))
    (eq_of_rightHomotopy _ _ (Candidate.condition f))

set_option backward.isDefEq.respectTransparency false in
/-- For `f` a morphism in `Arrow V`, the cokernel cofork of `(quotient V).map f` constructed
in `cokernelCofork` is a colimit cofork. -/
/-
**CategoryTheory.Preadditive.RightFreyd.Candidate.isColimitCokernelCofork** 是 Ma
thlib 中的一个定义，位于命名空间 `CategoryTheory.Preadditive.RightFreyd.Candidate`。
形式化陈述：isColimitCokernelCofork : IsColimit (cokernelCofork f)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Preadditive.RightFreyd.Candidate.instEpiMapArrowQuotientπ
`：∀ {V : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} V] [inst_1 : Categ
oryTheory.Preadditive V]   [inst_2 : CategoryTheory.Limits.Has…

--- 原说明 ---
For `f` a morphism in `Arrow V`, the cokernel cofork of `(quotient V).map f` con
structed
in `cokernelCofork` is a colimit cofork.
-/
def isColimitCokernelCofork : IsColimit (cokernelCofork f) :=
  CokernelCofork.IsColimit.ofπ' _
    (eq_of_rightHomotopy _ _ (Candidate.condition f))
    (fun g hg ↦ Nonempty.some (by
      obtain ⟨g, rfl⟩ := (quotient V).map_surjective g
      exact ⟨(quotient V).map (desc f g (homotopyOfEq _ _ hg)),
        by simp [← Functor.map_comp]⟩))

end Candidate

/-- The category `RightFreyd V` has all cokernels if `V` has binary biproducts. -/
/-
**CategoryTheory.Preadditive.RightFreyd.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Preadditive.RightFreyd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category `RightFreyd V` has all cokernels if `V` has binary biproducts.
-/
instance : HasCokernels (RightFreyd V) where
  has_colimit f := ⟨by
    obtain ⟨f, rfl⟩ := (quotient V).map_surjective f
    exact ⟨_, Candidate.isColimitCokernelCofork f⟩⟩

end RightFreyd

end CategoryTheory.Preadditive

