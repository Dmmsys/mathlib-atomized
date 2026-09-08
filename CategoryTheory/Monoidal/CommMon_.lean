/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Mon

/-!
# The category of commutative monoids in a braided monoidal category.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃ u

open CategoryTheory MonoidalCategory MonObj

namespace CategoryTheory
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C] [BraidedCategory.{v₁} C]

variable (C) in
/-- A commutative monoid object internal to a monoidal category.
-/
/-
**CategoryTheory.CommMon** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u₁) →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] → [CategoryTheory.BraidedCategory C] → Ty
pe (max u₁ v₁)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A commutative monoid object internal to a monoidal category.
-/
structure CommMon where
  /-- The underlying object in the ambient monoidal category -/
  X : C
  [mon : MonObj X]
  [comm : IsCommMonObj X]

attribute [instance] CommMon.mon CommMon.comm

namespace CommMon

/-- A commutative monoid object is a monoid object. -/
@[simps X]
/-
**CategoryTheory.CommMon.toMon** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CommMon
`。
形式化陈述：toMon (A : CommMon C) : Mon C
参数：A : CommMon C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A commutative monoid object is a monoid object.
-/
def toMon (A : CommMon C) : Mon C := ⟨A.X⟩

variable (C) in
/-- The trivial commutative monoid object. We later show this is initial in `CommMon C`.
-/
@[simps!]
/-
**CategoryTheory.CommMon.trivial** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CommM
on`。
形式化陈述：trivial : CommMon C
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsCommMonObj.instTensorUnit`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C]   [
inst_2 : CategoryTheory.BraidedC…

--- 原说明 ---
The trivial commutative monoid object. We later show this is initial in `CommMon
 C`.
-/
def trivial : CommMon C := { X := 𝟙_ C }
/-
**CategoryTheory.CommMon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.CommMon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (CommMon C) :=
  ⟨trivial C⟩

variable {M : CommMon C}
/-
**CategoryTheory.CommMon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.CommMon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (CommMon C) :=
  inferInstanceAs (Category (InducedCategory _ CommMon.toMon))

@[simp]
/-
**CategoryTheory.CommMon.id_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.CommMo
n`。
形式化陈述：id_hom (A : CommMon C) : Mon.Hom.hom (InducedCategory.Hom.hom (𝟙 A)) = 𝟙 A
.X
参数：A : CommMon C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_hom (A : CommMon C) : Mon.Hom.hom (InducedCategory.Hom.hom (𝟙 A)) = 𝟙 A.X :=
  rfl

@[simp]
/-
**CategoryTheory.CommMon.comp_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Comm
Mon`。
形式化陈述：comp_hom {R S T : CommMon C} (f : R ⟶ S) (g : S ⟶ T) : Mon.Hom.hom (f ≫ g)
.hom = f.hom.hom ≫ g.hom.hom
参数：f : R ⟶ S；g : S ⟶ T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_hom {R S T : CommMon C} (f : R ⟶ S) (g : S ⟶ T) :
    Mon.Hom.hom (f ≫ g).hom = f.hom.hom ≫ g.hom.hom :=
  rfl

@[ext]
/-
**CategoryTheory.CommMon.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.CommM
on`。
形式化陈述：hom_ext {A B : CommMon C} (f g : A ⟶ B) (h : f.hom.hom = g.hom.hom) : f = 
g
参数：f g : A ⟶ B；h : f.hom.hom = g.hom.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.InducedCategory.hom_ext`：hom_ext {X Y : InducedCategory D
 F} {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g
· 使用定理 `CategoryTheory.Mon.Hom.ext`：∀ {C : Type u₁} {inst : CategoryTheory.Categ
ory.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C}   {M N : CategoryTh
eory.Mon C} {x y…
-/
lemma hom_ext {A B : CommMon C} (f g : A ⟶ B) (h : f.hom.hom = g.hom.hom) : f = g :=
  InducedCategory.hom_ext (Mon.Hom.ext h)

/-- Constructor for morphisms in `CommMon C`. -/
@[simps]
/-
**CategoryTheory.CommMon.homMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CommMon
`。
形式化陈述：homMk {A B : CommMon C} (f : A.toMon ⟶ B.toMon) : A ⟶ B where hom
参数：f : A.toMon ⟶ B.toMon。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for morphisms in `CommMon C`.
-/
def homMk {A B : CommMon C} (f : A.toMon ⟶ B.toMon) : A ⟶ B where
  hom := f

section

variable (C)

/-- The forgetful functor from commutative monoid objects to monoid objects. -/
@[simps! obj_X]
/-
**CategoryTheory.CommMon.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CommMo
n`。
形式化陈述：forget : CommMon C ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from commutative monoid objects to monoid objects.
-/
def forget₂Mon : CommMon C ⥤ Mon C :=
  inducedFunctor CommMon.toMon

/-- The forgetful functor from commutative monoid objects to monoid objects
is fully faithful. -/
/-
**CategoryTheory.CommMon.fullyFaithfulForget** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.CommMon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from commutative monoid objects to monoid objects
is fully faithful.
-/
def fullyFaithfulForget₂Mon : (forget₂Mon C).FullyFaithful :=
  fullyFaithfulInducedFunctor _
-- The `Full, Faithful` instances should be constructed by a deriving handler.
-- https://github.com/leanprover-community/mathlib4/issues/380
/-
**CategoryTheory.CommMon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.CommMon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget₂Mon C).Full := InducedCategory.full _
/-
**CategoryTheory.CommMon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.CommMon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget₂Mon C).Faithful := InducedCategory.faithful _

@[simp]
/-
**CategoryTheory.CommMon.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CommMo
n`。
形式化陈述：forget : CommMon C ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget₂Mon_obj_one (A : CommMon C) : η[((forget₂Mon C).obj A).X] = η[A.X] :=
  rfl

@[simp]
/-
**CategoryTheory.CommMon.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CommMo
n`。
形式化陈述：forget : CommMon C ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget₂Mon_obj_mul (A : CommMon C) : μ[((forget₂Mon C).obj A).X] = μ[A.X] :=
  rfl

@[simp]
/-
**CategoryTheory.CommMon.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CommMo
n`。
形式化陈述：forget : CommMon C ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget₂Mon_map_hom {A B : CommMon C} (f : A ⟶ B) :
    ((forget₂Mon C).map f).hom = f.hom.hom :=
  rfl

/-- The forgetful functor from commutative monoid objects to the ambient category. -/
@[simps!]
/-
**CategoryTheory.CommMon.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CommMo
n`。
形式化陈述：forget : CommMon C ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from commutative monoid objects to the ambient category.
-/
def forget : CommMon C ⥤ C :=
  forget₂Mon C ⋙ Mon.forget C
/-
**CategoryTheory.CommMon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.CommMon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget C).Faithful where

@[simp]
/-
**CategoryTheory.CommMon.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CommMo
n`。
形式化陈述：forget : CommMon C ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget₂Mon_comp_forget : forget₂Mon C ⋙ Mon.forget C = forget C := rfl
/-
**CategoryTheory.CommMon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.CommMon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M N : CommMon C} {f : M ⟶ N} [IsIso f] : IsIso f.hom.hom :=
  inferInstanceAs <| IsIso <| (forget C).map f

end

/-- Construct an isomorphism of commutative monoid objects by giving a monoid isomorphism between
the underlying objects. -/
@[simps!]
/-
**CategoryTheory.CommMon.mkIso'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CommMo
n`。
形式化陈述：mkIso' {M N : C} (e : M ≅ N) [MonObj M] [IsCommMonObj M] [MonObj N] [IsCom
mMonObj N] [IsMonHom e.hom] : mk M ≅ mk N
参数：e : M ≅ N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an isomorphism of commutative monoid objects by giving a monoid isomor
phism between
the underlying objects.
-/
def mkIso' {M N : C} (e : M ≅ N) [MonObj M] [IsCommMonObj M] [MonObj N] [IsCommMonObj N]
    [IsMonHom e.hom] : mk M ≅ mk N :=
  (fullyFaithfulForget₂Mon C).preimageIso (Mon.mkIso' e)

/-- Construct an isomorphism of commutative monoid objects by giving an isomorphism between the
underlying objects and checking compatibility with unit and multiplication only in the forward
direction. -/
/-
**CategoryTheory.CommMon.mkIso** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.CommM
on`。
形式化陈述：mkIso {M N : CommMon C} (e : M.X ≅ N.X) (one_f : η[M.X] ≫ e.hom = η[N.X]
参数：e : M.X ≅ N.X。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommMon.comm`：∀ {C : Type u₁} [inst : CategoryTheory.Cate
gory.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C]   [inst_2 : Catego
ryTheory.BraidedC…

--- 原说明 ---
Construct an isomorphism of commutative monoid objects by giving an isomorphism 
between the
underlying objects and checking compatibility with unit and multiplication only 
in the forward
direction.
-/
abbrev mkIso {M N : CommMon C} (e : M.X ≅ N.X) (one_f : η[M.X] ≫ e.hom = η[N.X] := by cat_disch)
    (mul_f : μ[M.X] ≫ e.hom = (e.hom ⊗ₘ e.hom) ≫ μ[N.X] := by cat_disch) : M ≅ N :=
  have : IsMonHom e.hom := ⟨one_f, mul_f⟩
  mkIso' e
/-
**CategoryTheory.CommMon.uniqueHomFromTrivial** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.CommMon`。
形式化陈述：uniqueHomFromTrivial (A : CommMon C) : Unique (trivial C ⟶ A)
参数：A : CommMon C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance uniqueHomFromTrivial (A : CommMon C) : Unique (trivial C ⟶ A) :=
  Equiv.unique (show _ ≃ (Mon.trivial C ⟶ A.toMon) from
    InducedCategory.homEquiv)

open CategoryTheory.Limits
/-
**CategoryTheory.CommMon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.CommMon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasInitial (CommMon C) :=
  hasInitial_of_unique (trivial C)

end CommMon

variable
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E] [BraidedCategory E]
  {F F' : C ⥤ D} {G : D ⥤ E}

namespace Functor
section LaxBraided
variable [F.LaxBraided] [F'.LaxBraided] [G.LaxBraided]

open scoped Obj

/-
**CategoryTheory.Functor.isCommMonObj_obj** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：isCommMonObj_obj {M : C} [MonObj M] [IsCommMonObj M] : IsCommMonObj (F.obj
 M) where mul_comm
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.LaxBraided.braided_assoc`：∀ {C : Type u₁} {inst :
 CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C
}   {inst_2 : CategoryTheory.BraidedC…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.IsCommMonObj.mul_comm`：∀ {C : Type u₁} {inst : CategoryTh
eory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C}   {inst_2
 : CategoryTheory.BraidedC…
-/
instance isCommMonObj_obj {M : C} [MonObj M] [IsCommMonObj M] : IsCommMonObj (F.obj M) where
  mul_comm := by
    dsimp; rw [← Functor.LaxBraided.braided_assoc, ← Functor.map_comp, IsCommMonObj.mul_comm]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (F) in
/-- A lax braided functor takes commutative monoid objects to commutative monoid objects.

That is, a lax braided functor `F : C ⥤ D` induces a functor `CommMon C ⥤ CommMon D`.
-/
@[simps!]
/-
**CategoryTheory.Functor.mapCommMon** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Fu
nctor`。
形式化陈述：mapCommMon : CommMon C ⥤ CommMon D where obj A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A lax braided functor takes commutative monoid objects to commutative monoid obj
ects.

That is, a lax braided functor `F : C ⥤ D` induces a functor `CommMon C ⥤ CommMo
n D`.
-/
def mapCommMon : CommMon C ⥤ CommMon D where
  obj A :=
    { F.mapMon.obj A.toMon with
      comm :=
        { mul_comm := by
            dsimp
            rw [← Functor.LaxBraided.braided_assoc, ← Functor.map_comp, IsCommMonObj.mul_comm] } }
  map f := CommMon.homMk (F.mapMon.map f.hom)

@[simp]
/-
**CategoryTheory.Functor.mapCommMon_id_one** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：mapCommMon_id_one (A : CommMon C) : η[((𝟭 C).mapCommMon.obj A).X] = 𝟙 _ ≫ 
η[A.X]
参数：A : CommMon C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapCommMon_id_one (A : CommMon C) :
    η[((𝟭 C).mapCommMon.obj A).X] = 𝟙 _ ≫ η[A.X] :=
  rfl

@[simp]
/-
**CategoryTheory.Functor.mapCommMon_id_mul** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：mapCommMon_id_mul (A : CommMon C) : μ[((𝟭 C).mapCommMon.obj A).X] = 𝟙 _ ≫ 
μ[A.X]
参数：A : CommMon C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapCommMon_id_mul (A : CommMon C) :
    μ[((𝟭 C).mapCommMon.obj A).X] = 𝟙 _ ≫ μ[A.X] :=
  rfl

@[simp]
/-
**CategoryTheory.Functor.comp_mapCommMon_one** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Functor`。
形式化陈述：comp_mapCommMon_one (A : CommMon C) : η[((F ⋙ G).mapCommMon.obj A).X] = La
xMonoidal.ε (F ⋙ G) ≫ (F ⋙ G).map η[A.X]
参数：A : CommMon C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_mapCommMon_one (A : CommMon C) :
    η[((F ⋙ G).mapCommMon.obj A).X] = LaxMonoidal.ε (F ⋙ G) ≫ (F ⋙ G).map η[A.X] :=
  rfl

@[simp]
/-
**CategoryTheory.Functor.comp_mapCommMon_mul** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Functor`。
形式化陈述：comp_mapCommMon_mul (A : CommMon C) : μ[((F ⋙ G).mapCommMon.obj A).X] = La
xMonoidal.μ (F ⋙ G) _ _ ≫ (F ⋙ G).map μ[A.X]
参数：A : CommMon C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_mapCommMon_mul (A : CommMon C) :
    μ[((F ⋙ G).mapCommMon.obj A).X] = LaxMonoidal.μ (F ⋙ G) _ _ ≫ (F ⋙ G).map μ[A.X] :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The identity functor is also the identity on commutative monoid objects. -/
@[simps!]
/-
**CategoryTheory.Functor.mapCommMonIdIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：mapCommMonIdIso : mapCommMon (𝟭 C) ≅ 𝟭 (CommMon C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity functor is also the identity on commutative monoid objects.
-/
def mapCommMonIdIso : mapCommMon (𝟭 C) ≅ 𝟭 (CommMon C) :=
  NatIso.ofComponents fun X ↦ CommMon.mkIso (.refl _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The composition functor is also the composition on commutative monoid objects. -/
@[simps!]
/-
**CategoryTheory.Functor.mapCommMonCompIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：mapCommMonCompIso : (F ⋙ G).mapCommMon ≅ F.mapCommMon ⋙ G.mapCommMon
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition functor is also the composition on commutative monoid objects.
-/
def mapCommMonCompIso : (F ⋙ G).mapCommMon ≅ F.mapCommMon ⋙ G.mapCommMon :=
  NatIso.ofComponents fun X ↦ CommMon.mkIso (.refl _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (C D) in
/-- `mapCommMon` is functorial in the lax braided functor. -/
@[simps]
/-
**CategoryTheory.Functor.mapCommMonFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：mapCommMonFunctor : LaxBraidedFunctor C D ⥤ CommMon C ⥤ CommMon D where ob
j F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`mapCommMon` is functorial in the lax braided functor.
-/
def mapCommMonFunctor : LaxBraidedFunctor C D ⥤ CommMon C ⥤ CommMon D where
  obj F := F.mapCommMon
  map α := { app A := CommMon.homMk (.mk' (α.hom.hom.app A.X)) }
/-
**CategoryTheory.Functor.Faithful.mapCommMon** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Functor.Faithful`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C]   [inst_2 : CategoryTheory.BraidedCategory C] {D 
: Type u₂} [inst_3 : CategoryTheory.Category.{v₂, u₂} D]   [inst_4 : CategoryThe
ory.MonoidalCategory D] [inst_5 : CategoryTheory.BraidedCategory D]   {F : Categ
oryTheory.Functor C D} [inst_6 : F.LaxBraided] [F.Faithful], F.mapCommMon.Faithf
ul
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `CategoryTheory.Functor.Faithful.comp`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u
₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.CommMon.instFaithfulMonForget₂Mon`：∀ (C : Type u₁) [inst 
: CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory 
C]   [inst_2 : CategoryTheory.BraidedC…
· 使用定理 `CategoryTheory.Functor.Faithful.mapMon`：∀ {C : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C] {D : Ty
pe u₂}   [inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.congr_map`：congr_map (F : C ⥤ D) {X Y : C} {f g :
 X ⟶ Y} (h : f = g) : F.map f = F.map g
-/
protected instance Faithful.mapCommMon [F.Faithful] : F.mapCommMon.Faithful where
  map_injective hfg :=
    (CommMon.forget₂Mon _ ⋙ F.mapMon).map_injective ((CommMon.forget₂Mon _).congr_map hfg)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Natural transformations between functors lift to monoid objects. -/
@[simps!]
/-
**CategoryTheory.Functor.mapCommMonNatTrans** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Functor`。
形式化陈述：mapCommMonNatTrans (f : F ⟶ F') [NatTrans.IsMonoidal f] : F.mapCommMon ⟶ F
'.mapCommMon where app X
参数：f : F ⟶ F'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Natural transformations between functors lift to monoid objects.
-/
def mapCommMonNatTrans (f : F ⟶ F') [NatTrans.IsMonoidal f] :
    F.mapCommMon ⟶ F'.mapCommMon where
  app X := CommMon.homMk (.mk' (f.app _))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Natural isomorphisms between functors lift to monoid objects. -/
@[simps!]
/-
**CategoryTheory.Functor.mapCommMonNatIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：mapCommMonNatIso (e : F ≅ F') [NatTrans.IsMonoidal e.hom] : F.mapCommMon ≅
 F'.mapCommMon
参数：e : F ≅ F'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Natural isomorphisms between functors lift to monoid objects.
-/
def mapCommMonNatIso (e : F ≅ F') [NatTrans.IsMonoidal e.hom] : F.mapCommMon ≅ F'.mapCommMon :=
  NatIso.ofComponents fun X ↦ CommMon.mkIso (e.app _)

end LaxBraided

section Braided
variable [F.Braided]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `F : C ⥤ D` is a fully faithful monoidal functor, then
`CommMonCat(F) : CommMonCat C ⥤ CommMonCat D` is fully faithful too. -/
@[simps]
/-
**CategoryTheory.Functor.FullyFaithful.mapCommMon** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Functor.FullyFaithful`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] →       [inst_2 : CategoryTheory.BraidedC
ategory C] →         {D : Type u₂} →           [inst_3 : CategoryTheory.Category
.{v₂, u₂} D] →             [inst_4 : CategoryTheory.MonoidalCategory D] →       
        [inst_5 : CategoryTheory.BraidedCategory D] →                 {F : Categ
oryTheory.Functor C D} → [inst_6 : F.Braided] → F.FullyFaithful → F.mapCommMon.F
ullyFaithful
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ D` is a fully faithful monoidal functor, then
`CommMonCat(F) : CommMonCat C ⥤ CommMonCat D` is fully faithful too.
-/
protected def FullyFaithful.mapCommMon (hF : F.FullyFaithful) : F.mapCommMon.FullyFaithful where
  preimage f := CommMon.homMk (hF.mapMon.preimage f.hom)
/-
**CategoryTheory.Functor.Full.mapCommMon** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Functor.Full`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C]   [inst_2 : CategoryTheory.BraidedCategory C] {D 
: Type u₂} [inst_3 : CategoryTheory.Category.{v₂, u₂} D]   [inst_4 : CategoryThe
ory.MonoidalCategory D] [inst_5 : CategoryTheory.BraidedCategory D]   {F : Categ
oryTheory.Functor C D} [inst_6 : F.Braided] [F.Full] [F.Faithful], F.mapCommMon.
Full
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.FullyFaithful.full`：full : F.Full where map_surje
ctive
-/
protected instance Full.mapCommMon [F.Full] [F.Faithful] : F.mapCommMon.Full :=
    (FullyFaithful.ofFullyFaithful F).mapCommMon.full

end Braided

end Functor

open CategoryTheory.Functor

namespace Adjunction
variable {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) [F.Braided] [G.LaxBraided] [a.IsMonoidal]

set_option backward.defeqAttrib.useBackward true in
/-- An adjunction of braided functors lifts to an adjunction of their lifts to commutative monoid
objects. -/
/-
**CategoryTheory.Adjunction.mapCommMon** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Adjunction`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] →       [inst_2 : CategoryTheory.BraidedC
ategory C] →         {D : Type u₂} →           [inst_3 : CategoryTheory.Category
.{v₂, u₂} D] →             [inst_4 : CategoryTheory.MonoidalCategory D] →       
        [inst_5 : CategoryTheory.BraidedCategory D] →                 {F : Categ
oryTheory.Functor C D} →                   {G : CategoryTheory.Functor D C} →   
                  (a : F ⊣ G) →                       [inst_6 : F.Braided] → [in
st_7 : G.LaxBraided] → [a.IsMonoidal] → F.mapCommMon ⊣ G.mapCommMon
参数：a : F ⊣ G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An adjunction of braided functors lifts to an adjunction of their lifts to commu
tative monoid
objects.
-/
@[simps] def mapCommMon : F.mapCommMon ⊣ G.mapCommMon where
  unit := mapCommMonIdIso.inv ≫ mapCommMonNatTrans a.unit ≫ mapCommMonCompIso.hom
  counit := mapCommMonCompIso.inv ≫ mapCommMonNatTrans a.counit ≫ mapCommMonIdIso.hom

end Adjunction

namespace Equivalence

set_option backward.defeqAttrib.useBackward true in
/-- An equivalence of categories lifts to an equivalence of their commutative monoid objects. -/
@[simps]
/-
**CategoryTheory.Equivalence.mapCommMon** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Equivalence`。
形式化陈述：mapCommMon (e : C ≌ D) [e.functor.Braided] [e.inverse.Braided] [e.IsMonoid
al] : CommMon C ≌ CommMon D where functor
参数：e : C ≌ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence of categories lifts to an equivalence of their commutative monoid
 objects.
-/
def mapCommMon (e : C ≌ D) [e.functor.Braided] [e.inverse.Braided] [e.IsMonoidal] :
    CommMon C ≌ CommMon D where
  functor := e.functor.mapCommMon
  inverse := e.inverse.mapCommMon
  unitIso := mapCommMonIdIso.symm ≪≫ mapCommMonNatIso e.unitIso ≪≫ mapCommMonCompIso
  counitIso := mapCommMonCompIso.symm ≪≫ mapCommMonNatIso e.counitIso ≪≫ mapCommMonIdIso

end Equivalence

namespace CommMon

open LaxBraidedFunctor

namespace EquivLaxBraidedFunctorPUnit

variable (C) in
/-- Implementation of `CommMon.equivLaxBraidedFunctorPUnit`. -/
@[simps]
/-
**CategoryTheory.CommMon.EquivLaxBraidedFunctorPUnit.laxBraidedToCommMon** 是 Mat
hlib 中的一个定义，位于命名空间 `CategoryTheory.CommMon.EquivLaxBraidedFunctorPUnit`。
形式化陈述：laxBraidedToCommMon : LaxBraidedFunctor (Discrete PUnit.{u + 1}) C ⥤ CommM
on C where obj F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implementation of `CommMon.equivLaxBraidedFunctorPUnit`.
-/
def laxBraidedToCommMon : LaxBraidedFunctor (Discrete PUnit.{u + 1}) C ⥤ CommMon C where
  obj F := (F.mapCommMon : CommMon _ ⥤ CommMon C).obj (trivial (Discrete PUnit.{u + 1}))
  map α := ((Functor.mapCommMonFunctor (Discrete PUnit) C).map α).app _

/-- Implementation of `CommMon.equivLaxBraidedFunctorPUnit`. -/
@[simps!]
/-
**CategoryTheory.CommMon.EquivLaxBraidedFunctorPUnit.commMonToLaxBraidedObj** 是 
Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CommMon.EquivLaxBraidedFunctorPUnit`。
形式化陈述：commMonToLaxBraidedObj (A : CommMon C) : Discrete PUnit.{u + 1} ⥤ C
参数：A : CommMon C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implementation of `CommMon.equivLaxBraidedFunctorPUnit`.
-/
def commMonToLaxBraidedObj (A : CommMon C) :
    Discrete PUnit.{u + 1} ⥤ C := (Functor.const _).obj A.X

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.CommMon.EquivLaxBraidedFunctorPUnit.** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.CommMon.EquivLaxBraidedFunctorPUnit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (A : CommMon C) : (commMonToLaxBraidedObj A).LaxMonoidal where
  ε := η[A.X]
  «μ» _ _ := μ[A.X]

open Functor.LaxMonoidal

@[simp]
/-
**CategoryTheory.CommMon.EquivLaxBraidedFunctorPUnit.commMonToLaxBraidedObj_** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.CommMon.EquivLaxBraidedFunctorPUnit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma commMonToLaxBraidedObj_ε (A : CommMon C) :
    ε (commMonToLaxBraidedObj A) = η[A.X] := rfl

@[simp]
/-
**CategoryTheory.CommMon.EquivLaxBraidedFunctorPUnit.commMonToLaxBraidedObj_** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.CommMon.EquivLaxBraidedFunctorPUnit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma commMonToLaxBraidedObj_μ (A : CommMon C) (X Y) :
    «μ» (commMonToLaxBraidedObj A) X Y = μ[A.X] := rfl

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.CommMon.EquivLaxBraidedFunctorPUnit.** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.CommMon.EquivLaxBraidedFunctorPUnit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (A : CommMon C) : (commMonToLaxBraidedObj A).LaxBraided where

variable (C)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Implementation of `CommMon.equivLaxBraidedFunctorPUnit`. -/
@[simps]
/-
**CategoryTheory.CommMon.EquivLaxBraidedFunctorPUnit.commMonToLaxBraided** 是 Mat
hlib 中的一个定义，位于命名空间 `CategoryTheory.CommMon.EquivLaxBraidedFunctorPUnit`。
形式化陈述：commMonToLaxBraided : CommMon C ⥤ LaxBraidedFunctor (Discrete PUnit.{u + 1
}) C where obj A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implementation of `CommMon.equivLaxBraidedFunctorPUnit`.
-/
def commMonToLaxBraided : CommMon C ⥤ LaxBraidedFunctor (Discrete PUnit.{u + 1}) C where
  obj A := LaxBraidedFunctor.of (commMonToLaxBraidedObj A)
  map f :=
    { hom :=
      { hom := { app _ := f.hom.hom }
        isMonoidal := { } } }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Implementation of `CommMon.equivLaxBraidedFunctorPUnit`. -/
@[simps!]
/-
**CategoryTheory.CommMon.EquivLaxBraidedFunctorPUnit.unitIso** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.CommMon.EquivLaxBraidedFunctorPUnit`。
形式化陈述：unitIso : 𝟭 (LaxBraidedFunctor (Discrete PUnit.{u + 1}) C) ≅ laxBraidedToC
ommMon C ⋙ commMonToLaxBraided C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implementation of `CommMon.equivLaxBraidedFunctorPUnit`.
-/
def unitIso :
    𝟭 (LaxBraidedFunctor (Discrete PUnit.{u + 1}) C) ≅
        laxBraidedToCommMon C ⋙ commMonToLaxBraided C :=
  NatIso.ofComponents
    (fun F ↦ LaxBraidedFunctor.isoOfComponents (fun _ ↦ F.mapIso (eqToIso (by ext))))
    (fun f ↦ by ext ⟨⟨⟩⟩; dsimp; simp)

@[simp]
/-
**CategoryTheory.CommMon.EquivLaxBraidedFunctorPUnit.counitIso_aux_one** 是 Mathl
ib 中的一个定理，位于命名空间 `CategoryTheory.CommMon.EquivLaxBraidedFunctorPUnit`。
形式化陈述：counitIso_aux_one (A : CommMon C) : η[((commMonToLaxBraided C ⋙ laxBraided
ToCommMon C).obj A).X] = η[A.X] ≫ 𝟙 _
参数：A : CommMon C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem counitIso_aux_one (A : CommMon C) :
    η[((commMonToLaxBraided C ⋙ laxBraidedToCommMon C).obj A).X] = η[A.X] ≫ 𝟙 _ :=
  rfl

@[simp]
/-
**CategoryTheory.CommMon.EquivLaxBraidedFunctorPUnit.counitIso_aux_mul** 是 Mathl
ib 中的一个定理，位于命名空间 `CategoryTheory.CommMon.EquivLaxBraidedFunctorPUnit`。
形式化陈述：counitIso_aux_mul (A : CommMon C) : μ[((commMonToLaxBraided C ⋙ laxBraided
ToCommMon C).obj A).X] = μ[A.X] ≫ 𝟙 _
参数：A : CommMon C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem counitIso_aux_mul (A : CommMon C) :
    μ[((commMonToLaxBraided C ⋙ laxBraidedToCommMon C).obj A).X] = μ[A.X] ≫ 𝟙 _ :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Implementation of `CommMon.equivLaxBraidedFunctorPUnit`. -/
@[simps!]
/-
**CategoryTheory.CommMon.EquivLaxBraidedFunctorPUnit.counitIso** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.CommMon.EquivLaxBraidedFunctorPUnit`。
形式化陈述：counitIso : commMonToLaxBraided C ⋙ laxBraidedToCommMon C ≅ 𝟭 (CommMon C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implementation of `CommMon.equivLaxBraidedFunctorPUnit`.
-/
def counitIso : commMonToLaxBraided C ⋙ laxBraidedToCommMon C ≅ 𝟭 (CommMon C) :=
  NatIso.ofComponents (fun F ↦ mkIso (Iso.refl _))

end EquivLaxBraidedFunctorPUnit

open EquivLaxBraidedFunctorPUnit

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Commutative monoid objects in `C` are "just" braided lax monoidal functors from the trivial
braided monoidal category to `C`.
-/
@[simps]
/-
**CategoryTheory.CommMon.equivLaxBraidedFunctorPUnit** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.CommMon`。
形式化陈述：equivLaxBraidedFunctorPUnit : LaxBraidedFunctor (Discrete PUnit.{u + 1}) C
 ≌ CommMon C where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Commutative monoid objects in `C` are "just" braided lax monoidal functors from 
the trivial
braided monoidal category to `C`.
-/
def equivLaxBraidedFunctorPUnit : LaxBraidedFunctor (Discrete PUnit.{u + 1}) C ≌ CommMon C where
  functor := laxBraidedToCommMon C
  inverse := commMonToLaxBraided C
  unitIso := unitIso C
  counitIso := counitIso C

end CommMon
end CategoryTheory

