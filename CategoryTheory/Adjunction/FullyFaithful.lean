/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.EpiMono

/-!
# Adjoints of fully faithful functors

A left adjoint is
* faithful, if and only if the unit is a monomorphism
* full, if and only if the unit is a split epimorphism
* fully faithful, if and only if the unit is an isomorphism

A right adjoint is
* faithful, if and only if the counit is an epimorphism
* full, if and only if the counit is a split monomorphism
* fully faithful, if and only if the counit is an isomorphism

This is Lemma 4.5.13 in Riehl's *Category Theory in Context* [riehl2017].
See also https://stacks.math.columbia.edu/tag/07RB for the statements about fully faithful functors.

In the file `Mathlib/CategoryTheory/Monad/Adjunction.lean`, we prove that in fact, if there exists
an isomorphism `L ⋙ R ≅ 𝟭 C`, then the unit is an isomorphism, and similarly for the counit.
See `CategoryTheory.Adjunction.isIso_unit_of_iso` and
`CategoryTheory.Adjunction.isIso_counit_of_iso`.
-/

@[expose] public section


open CategoryTheory

namespace CategoryTheory.Adjunction

universe v₁ v₂ u₁ u₂

open Category CategoryTheory.Functor

open Opposite

attribute [local simp] Adjunction.homEquiv_unit Adjunction.homEquiv_counit

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R)

attribute [local simp] homEquiv_unit homEquiv_counit

set_option backward.defeqAttrib.useBackward true in
/-- If the left adjoint is faithful, then each component of the unit is a monomorphism. -/
/-
**CategoryTheory.Adjunction.unit_mono_of_L_faithful** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.Adjunction`。
形式化陈述：unit_mono_of_L_faithful [L.Faithful] (X : C) : Mono (h.unit.app X) where r
ight_cancellation {Y} f g hfg
参数：X : C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Adjunction.homEquiv_unit`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.unit_naturality`：unit_naturality {X Y : C} (f 
: X ⟶ Y) : dsimp% adj.unit.app X ≫ G.map (F.map f) = f ≫ adj.unit.app Y

--- 原说明 ---
If the left adjoint is faithful, then each component of the unit is a monomorphi
sm.
-/
instance unit_mono_of_L_faithful [L.Faithful] (X : C) : Mono (h.unit.app X) where
  right_cancellation {Y} f g hfg :=
    L.map_injective <| (h.homEquiv Y (L.obj X)).injective <| by simpa using hfg

set_option backward.defeqAttrib.useBackward true in
/-- If the left adjoint is full, then each component of the unit is a split epimorphism. -/
/-
**CategoryTheory.Adjunction.unitSplitEpiOfLFull** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Adjunction`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {L : Cat
egoryTheory.Functor C D} →           {R : CategoryTheory.Functor D C} → (h : L ⊣
 R) → [L.Full] → (X : C) → CategoryTheory.SplitEpi (h.unit.app X)
参数：h : L ⊣ R；X : C；h.unit.app X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the left adjoint is full, then each component of the unit is a split epimorph
ism.
-/
noncomputable def unitSplitEpiOfLFull [L.Full] (X : C) : SplitEpi (h.unit.app X) where
  section_ := L.preimage (h.counit.app (L.obj X))
  id := by simp [← h.unit_naturality (L.preimage (h.counit.app (L.obj X)))]

/-- If the right adjoint is full, then each component of the counit is a split monomorphism. -/
/-
**CategoryTheory.Adjunction.unit_isSplitEpi_of_L_full** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.Adjunction`。
形式化陈述：unit_isSplitEpi_of_L_full [L.Full] (X : C) : IsSplitEpi (h.unit.app X)
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the right adjoint is full, then each component of the counit is a split monom
orphism.
-/
instance unit_isSplitEpi_of_L_full [L.Full] (X : C) : IsSplitEpi (h.unit.app X) :=
  ⟨⟨h.unitSplitEpiOfLFull X⟩⟩
/-
**CategoryTheory.Adjunction.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Adjunctio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [L.Full] [L.Faithful] (X : C) : IsIso (h.unit.app X) :=
  isIso_of_mono_of_isSplitEpi _

/-- If the left adjoint is fully faithful, then the unit is an isomorphism. -/
/-
**CategoryTheory.Adjunction.unit_isIso_of_L_fully_faithful** 是 Mathlib 中的一个实例，位于
命名空间 `CategoryTheory.Adjunction`。
形式化陈述：unit_isIso_of_L_fully_faithful [L.Full] [L.Faithful] : IsIso (Adjunction.u
nit h)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatIso.isIso_of_isIso_app`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Adjunction.instIsIsoAppUnitOfFullOfFaithful`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {L : CategoryTheor…

--- 原说明 ---
If the left adjoint is fully faithful, then the unit is an isomorphism.
-/
instance unit_isIso_of_L_fully_faithful [L.Full] [L.Faithful] : IsIso (Adjunction.unit h) :=
  NatIso.isIso_of_isIso_app _

/-- If the right adjoint is faithful, then each component of the counit is an epimorphism. -/
/-
**CategoryTheory.Adjunction.counit_epi_of_R_faithful** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.Adjunction`。
形式化陈述：counit_epi_of_R_faithful [R.Faithful] (X : D) : Epi (h.counit.app X) where
 left_cancellation {Y} f g hfg
参数：X : D。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Adjunction.homEquiv_counit`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.counit_naturality`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   {F : CategoryTheor…

--- 原说明 ---
If the right adjoint is faithful, then each component of the counit is an epimor
phism.
-/
instance counit_epi_of_R_faithful [R.Faithful] (X : D) : Epi (h.counit.app X) where
  left_cancellation {Y} f g hfg :=
    R.map_injective <| (h.homEquiv (R.obj X) Y).symm.injective <| by simpa using! hfg

set_option backward.defeqAttrib.useBackward true in
/-- If the right adjoint is full, then each component of the counit is a split monomorphism. -/
/-
**CategoryTheory.Adjunction.counitSplitMonoOfRFull** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Adjunction`。
形式化陈述：counitSplitMonoOfRFull [R.Full] (X : D) : SplitMono (h.counit.app X) where
 retraction
参数：X : D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the right adjoint is full, then each component of the counit is a split monom
orphism.
-/
noncomputable def counitSplitMonoOfRFull [R.Full] (X : D) : SplitMono (h.counit.app X) where
  retraction := R.preimage (h.unit.app (R.obj X))
  id := by simp [← h.counit_naturality (R.preimage (h.unit.app (R.obj X)))]

/-- If the right adjoint is full, then each component of the counit is a split monomorphism. -/
/-
**CategoryTheory.Adjunction.counit_isSplitMono_of_R_full** 是 Mathlib 中的一个实例，位于命名
空间 `CategoryTheory.Adjunction`。
形式化陈述：counit_isSplitMono_of_R_full [R.Full] (X : D) : IsSplitMono (h.counit.app 
X)
参数：X : D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the right adjoint is full, then each component of the counit is a split monom
orphism.
-/
instance counit_isSplitMono_of_R_full [R.Full] (X : D) : IsSplitMono (h.counit.app X) :=
  ⟨⟨h.counitSplitMonoOfRFull X⟩⟩
/-
**CategoryTheory.Adjunction.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Adjunctio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [R.Full] [R.Faithful] (X : D) : IsIso (h.counit.app X) :=
  isIso_of_epi_of_isSplitMono _

/-- If the right adjoint is fully faithful, then the counit is an isomorphism. -/
/-
**CategoryTheory.Adjunction.counit_isIso_of_R_fully_faithful** 是 Mathlib 中的一个实例，
位于命名空间 `CategoryTheory.Adjunction`。
形式化陈述：counit_isIso_of_R_fully_faithful [R.Full] [R.Faithful] : IsIso (Adjunction
.counit h)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatIso.isIso_of_isIso_app`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Adjunction.instIsIsoAppCounitOfFullOfFaithful`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   {L : CategoryTheor…

--- 原说明 ---
If the right adjoint is fully faithful, then the counit is an isomorphism.
-/
instance counit_isIso_of_R_fully_faithful [R.Full] [R.Faithful] : IsIso (Adjunction.counit h) :=
  NatIso.isIso_of_isIso_app _

/-- If the unit of an adjunction is an isomorphism, then its inverse on the image of L is given
by L whiskered with the counit. -/
@[simp]
/-
**CategoryTheory.Adjunction.inv_map_unit** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Adjunction`。
形式化陈述：inv_map_unit {X : C} [IsIso (h.unit.app X)] : inv (L.map (h.unit.app X)) =
 h.counit.app (L.obj X)
参数：h.unit.app X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsIso.inv_eq_of_hom_inv_id`：inv_eq_of_hom_inv_id {f : X ⟶
 Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) : inv f = g
· 使用定理 `CategoryTheory.Adjunction.left_triangle_components`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   {F : CategoryTheor…

--- 原说明 ---
If the unit of an adjunction is an isomorphism, then its inverse on the image of
 L is given
by L whiskered with the counit.
-/
theorem inv_map_unit {X : C} [IsIso (h.unit.app X)] :
    inv (L.map (h.unit.app X)) = h.counit.app (L.obj X) :=
  IsIso.inv_eq_of_hom_inv_id (h.left_triangle_components X)

/-- If the unit of an adjunction is an isomorphism, then one has an isomorphism `L ⋙ R ⋙ L ≅ L`. -/
@[simps!]
/-
**CategoryTheory.Adjunction.whiskerLeftLCounitIsoOfIsIsoUnit** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Adjunction`。
形式化陈述：whiskerLeftLCounitIsoOfIsIsoUnit [IsIso h.unit] : L ⋙ R ⋙ L ≅ L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the unit of an adjunction is an isomorphism, then one has an isomorphism `L ⋙
 R ⋙ L ≅ L`.
-/
noncomputable def whiskerLeftLCounitIsoOfIsIsoUnit [IsIso h.unit] : L ⋙ R ⋙ L ≅ L :=
  (L.associator R L).symm ≪≫ isoWhiskerRight (asIso h.unit).symm L ≪≫ Functor.leftUnitor _

/-- If the counit of an adjunction is an isomorphism, then its inverse on the image of R is given
by R whiskered with the unit. -/
@[simp]
/-
**CategoryTheory.Adjunction.inv_counit_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Adjunction`。
形式化陈述：inv_counit_map {X : D} [IsIso (h.counit.app X)] : inv (R.map (h.counit.app
 X)) = h.unit.app (R.obj X)
参数：h.counit.app X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsIso.inv_eq_of_inv_hom_id`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {X Y : C} {f : Y ⟶ X} [inst_1 : CategoryTheory.IsIso
 f]   {g : X ⟶ Y}, CategoryTheo…
· 使用定理 `CategoryTheory.Adjunction.right_triangle_components`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {F : CategoryTheor…

--- 原说明 ---
If the counit of an adjunction is an isomorphism, then its inverse on the image 
of R is given
by R whiskered with the unit.
-/
theorem inv_counit_map {X : D} [IsIso (h.counit.app X)] :
    inv (R.map (h.counit.app X)) = h.unit.app (R.obj X) :=
  IsIso.inv_eq_of_inv_hom_id (h.right_triangle_components X)

/-- If the counit of an adjunction is an isomorphism, then one has an isomorphism
`(R ⋙ L ⋙ R) ≅ R`. -/
@[simps!]
/-
**CategoryTheory.Adjunction.whiskerLeftRUnitIsoOfIsIsoCounit** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Adjunction`。
形式化陈述：whiskerLeftRUnitIsoOfIsIsoCounit [IsIso h.counit] : R ⋙ L ⋙ R ≅ R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the counit of an adjunction is an isomorphism, then one has an isomorphism
`(R ⋙ L ⋙ R) ≅ R`.
-/
noncomputable def whiskerLeftRUnitIsoOfIsIsoCounit [IsIso h.counit] : R ⋙ L ⋙ R ≅ R :=
  (R.associator L R).symm ≪≫ isoWhiskerRight (asIso h.counit) R ≪≫ Functor.leftUnitor _

set_option backward.defeqAttrib.useBackward true in
/-- If each component of the unit is a monomorphism, then the left adjoint is faithful. -/
/-
**CategoryTheory.Adjunction.faithful_L_of_mono_unit_app** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Adjunction`。
形式化陈述：faithful_L_of_mono_unit_app [forall X, Mono (h.unit.app X)] : L.Faithful w
here map_injective {X Y f g} hfg
参数：h.unit.app X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Mono.right_cancellation`：∀ {C : Type u} {inst : CategoryT
heory.Category.{v, u} C} {X Y : C} {f : X ⟶ Y} [self : CategoryTheory.Mono f] {Z
 : C}   (g h : Z ⟶ X), Categ…
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Adjunction.homEquiv_counit`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Adjunction.left_triangle_components`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…

--- 原说明 ---
If each component of the unit is a monomorphism, then the left adjoint is faithf
ul.
-/
lemma faithful_L_of_mono_unit_app [∀ X, Mono (h.unit.app X)] : L.Faithful where
  map_injective {X Y f g} hfg := by
    apply Mono.right_cancellation (f := h.unit.app Y)
    apply (h.homEquiv X (L.obj Y)).symm.injective
    simpa using hfg

/-- If each component of the unit is a split epimorphism, then the left adjoint is full. -/
/-
**CategoryTheory.Adjunction.full_L_of_isSplitEpi_unit_app** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Adjunction`。
形式化陈述：full_L_of_isSplitEpi_unit_app [forall X, IsSplitEpi (h.unit.app X)] : L.Fu
ll where map_surjective {X Y} f
参数：h.unit.app X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Adjunction.left_triangle_components`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.IsSplitEpi.id`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [hf : CategoryTheory.IsSplitEpi f],   Ca
tegoryTheory.Categ…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Adjunction.homEquiv_unit`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Adjunction.counit_naturality`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.left_triangle_components_assoc`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   {F : CategoryTheor…

--- 原说明 ---
If each component of the unit is a split epimorphism, then the left adjoint is f
ull.
-/
lemma full_L_of_isSplitEpi_unit_app [∀ X, IsSplitEpi (h.unit.app X)] : L.Full where
  map_surjective {X Y} f := by
    use ((h.homEquiv X (L.obj Y)) f ≫ section_ (h.unit.app Y))
    suffices L.map (section_ (h.unit.app Y)) = h.counit.app (L.obj Y) by simp [this]
    rw [← comp_id (L.map (section_ (h.unit.app Y)))]
    simp only [Functor.id_obj, ← h.left_triangle_components Y,
      ← assoc, ← Functor.map_comp, IsSplitEpi.id, Functor.map_id, id_comp]

/-- If the unit is an isomorphism, then the left adjoint is fully faithful. -/
/-
**CategoryTheory.Adjunction.fullyFaithfulLOfIsIsoUnit** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Adjunction`。
形式化陈述：fullyFaithfulLOfIsIsoUnit [IsIso h.unit] : L.FullyFaithful where preimage 
{_ Y} f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the unit is an isomorphism, then the left adjoint is fully faithful.
-/
noncomputable def fullyFaithfulLOfIsIsoUnit [IsIso h.unit] : L.FullyFaithful where
  preimage {_ Y} f := h.homEquiv _ (L.obj Y) f ≫ inv (h.unit.app Y)

set_option backward.defeqAttrib.useBackward true in
/-- If each component of the counit is an epimorphism, then the right adjoint is faithful. -/
/-
**CategoryTheory.Adjunction.faithful_R_of_epi_counit_app** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Adjunction`。
形式化陈述：faithful_R_of_epi_counit_app [forall X, Epi (h.counit.app X)] : R.Faithful
 where map_injective {X Y f g} hfg
参数：h.counit.app X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Epi.left_cancellation`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} {X Y : C} {f : X ⟶ Y} [self : CategoryTheory.Epi f] {Z : 
C}   (g h : Y ⟶ Z), Catego…
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Adjunction.homEquiv_unit`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Adjunction.right_triangle_components_assoc`：∀ {C : Type u
₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryT
heory.Category.{v₂, u₂} D]   {F : CategoryTheor…

--- 原说明 ---
If each component of the counit is an epimorphism, then the right adjoint is fai
thful.
-/
lemma faithful_R_of_epi_counit_app [∀ X, Epi (h.counit.app X)] : R.Faithful where
  map_injective {X Y f g} hfg := by
    apply Epi.left_cancellation (f := h.counit.app X)
    apply (h.homEquiv (R.obj X) Y).injective
    simpa using hfg

/-- If each component of the counit is a split monomorphism, then the right adjoint is full. -/
/-
**CategoryTheory.Adjunction.full_R_of_isSplitMono_counit_app** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Adjunction`。
形式化陈述：full_R_of_isSplitMono_counit_app [forall X, IsSplitMono (h.counit.app X)] 
: R.Full where map_surjective {X Y} f
参数：h.counit.app X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Adjunction.right_triangle_components`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsSplitMono.id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [hf : CategoryTheory.IsSplitMono f],   
CategoryTheory.Cate…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Adjunction.homEquiv_counit`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Adjunction.unit_naturality_assoc`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   {F : CategoryTheor…

--- 原说明 ---
If each component of the counit is a split monomorphism, then the right adjoint 
is full.
-/
lemma full_R_of_isSplitMono_counit_app [∀ X, IsSplitMono (h.counit.app X)] : R.Full where
  map_surjective {X Y} f := by
    use (retraction (h.counit.app X) ≫ (h.homEquiv (R.obj X) Y).symm f)
    suffices R.map (retraction (h.counit.app X)) = h.unit.app (R.obj X) by simp [this]
    rw [← id_comp (R.map (retraction (h.counit.app X)))]
    simp only [Functor.id_obj, ← h.right_triangle_components X,
      assoc, ← Functor.map_comp, IsSplitMono.id, Functor.map_id, comp_id]

/-- If the counit is an isomorphism, then the right adjoint is fully faithful. -/
/-
**CategoryTheory.Adjunction.fullyFaithfulROfIsIsoCounit** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Adjunction`。
形式化陈述：fullyFaithfulROfIsIsoCounit [IsIso h.counit] : R.FullyFaithful where preim
age {X Y} f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If the counit is an isomorphism, then the right adjoint is fully faithful.
-/
noncomputable def fullyFaithfulROfIsIsoCounit [IsIso h.counit] : R.FullyFaithful where
  preimage {X Y} f := inv (h.counit.app X) ≫ (h.homEquiv (R.obj X) Y).symm f
/-
**CategoryTheory.Adjunction.whiskerLeft_counit_iso_of_L_fully_faithful** 是 Mathl
ib 中的一个实例，位于命名空间 `CategoryTheory.Adjunction`。
形式化陈述：whiskerLeft_counit_iso_of_L_fully_faithful [L.Full] [L.Faithful] : IsIso (
whiskerLeft L h.counit)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.whisker_eq`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {X Y Z : C} {f g : Y ⟶ X} (h : Z ⟶ Y),   f = g → CategoryTheory.Cate
goryStruct.comp…
· 使用定理 `CategoryTheory.Adjunction.left_triangle`：left_triangle : whiskerRight ad
j.unit F ≫ (Functor.associator ..).hom ≫ whiskerLeft F adj.counit = F.leftUnitor
.hom ≫ F.rightUnitor.inv
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `CategoryTheory.Functor.whiskerRight_id'`：whiskerRight_id' {G : C ⥤ D} (F
 : D ⥤ E) : whiskerRight (𝟙 G) F = 𝟙 (G.comp F)
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance whiskerLeft_counit_iso_of_L_fully_faithful [L.Full] [L.Faithful] :
    IsIso (whiskerLeft L h.counit) := by
  have := ((Functor.associator ..).inv ≫ whiskerRight (inv h.unit) L) ≫= h.left_triangle
  simp only [assoc, ← whiskerRight_comp_assoc, IsIso.inv_hom_id, whiskerRight_id', id_comp,
    Iso.inv_hom_id_assoc] at this
  rw [this]
  infer_instance
/-
**CategoryTheory.Adjunction.whiskerRight_counit_iso_of_L_fully_faithful** 是 Math
lib 中的一个实例，位于命名空间 `CategoryTheory.Adjunction`。
形式化陈述：whiskerRight_counit_iso_of_L_fully_faithful [L.Full] [L.Faithful] : IsIso 
(whiskerRight h.counit R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.right_triangle`：right_triangle : whiskerLeft G
 adj.unit ≫ (Functor.associator ..).inv ≫ whiskerRight adj.counit G = G.rightUni
tor.hom ≫ G.leftUnitor.inv
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_comp_eq`：inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.IsIso.eq_inv_comp`：eq_inv_comp (α : X ⟶ Y) [IsIso α] {f :
 X ⟶ Z} {g : Y ⟶ Z} : g = inv α ≫ f ↔ α ≫ g = f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
-/
instance whiskerRight_counit_iso_of_L_fully_faithful [L.Full] [L.Faithful] :
    IsIso (whiskerRight h.counit R) := by
  have := h.right_triangle
  rw [← IsIso.eq_inv_comp, Iso.inv_comp_eq] at this
  rw [this]
  infer_instance
/-
**CategoryTheory.Adjunction.whiskerLeft_unit_iso_of_R_fully_faithful** 是 Mathlib
 中的一个实例，位于命名空间 `CategoryTheory.Adjunction`。
形式化陈述：whiskerLeft_unit_iso_of_R_fully_faithful [R.Full] [R.Faithful] : IsIso (wh
iskerLeft R h.unit)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.right_triangle`：right_triangle : whiskerLeft G
 adj.unit ≫ (Functor.associator ..).inv ≫ whiskerRight adj.counit G = G.rightUni
tor.hom ≫ G.leftUnitor.inv
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.IsIso.eq_comp_inv`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y Z : C} (α : Y ⟶ X) [inst_1 : CategoryTheory.IsIso α]   {
f : Z ⟶ X} {g : Z ⟶ Y}…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance whiskerLeft_unit_iso_of_R_fully_faithful [R.Full] [R.Faithful] :
    IsIso (whiskerLeft R h.unit) := by
  have := h.right_triangle
  rw [← IsIso.eq_comp_inv] at this
  rw [this]
  infer_instance
/-
**CategoryTheory.Adjunction.whiskerRight_unit_iso_of_R_fully_faithful** 是 Mathli
b 中的一个实例，位于命名空间 `CategoryTheory.Adjunction`。
形式化陈述：whiskerRight_unit_iso_of_R_fully_faithful [R.Full] [R.Faithful] : IsIso (w
hiskerRight h.unit L)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.left_triangle`：left_triangle : whiskerRight ad
j.unit F ≫ (Functor.associator ..).hom ≫ whiskerLeft F adj.counit = F.leftUnitor
.hom ≫ F.rightUnitor.inv
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.IsIso.eq_comp_inv`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y Z : C} (α : Y ⟶ X) [inst_1 : CategoryTheory.IsIso α]   {
f : Z ⟶ X} {g : Z ⟶ Y}…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
-/
instance whiskerRight_unit_iso_of_R_fully_faithful [R.Full] [R.Faithful] :
    IsIso (whiskerRight h.unit L) := by
  have := h.left_triangle
  rw [← IsIso.eq_comp_inv] at this
  rw [this]
  infer_instance
/-
**CategoryTheory.Adjunction.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Adjunctio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [L.Faithful] [L.Full] {Y : C} : IsIso (h.counit.app (L.obj Y)) :=
  isIso_of_hom_comp_eq_id _ (h.left_triangle_components Y)
/-
**CategoryTheory.Adjunction.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Adjunctio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [L.Faithful] [L.Full] {Y : D} : IsIso (R.map (h.counit.app Y)) :=
  isIso_of_hom_comp_eq_id _ (h.right_triangle_components Y)
/-
**CategoryTheory.Adjunction.isIso_counit_app_iff_mem_essImage** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Adjunction`。
形式化陈述：isIso_counit_app_iff_mem_essImage [L.Faithful] [L.Full] {X : D} : IsIso (h
.counit.app X) ↔ L.essImage X
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.NatTrans.isIso_app_iff_of_iso`：isIso_app_iff_of_iso {F G 
: C ⥤ D} (α : F ⟶ G) {X Y : C} (e : X ≅ Y) : IsIso (α.app X) ↔ IsIso (α.app Y)
· 使用定理 `CategoryTheory.Adjunction.instIsIsoAppCounitObjOfFaithfulOfFull`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   {L : CategoryTheor…
-/
lemma isIso_counit_app_iff_mem_essImage [L.Faithful] [L.Full] {X : D} :
    IsIso (h.counit.app X) ↔ L.essImage X := by
  constructor
  · intro
    exact ⟨R.obj X, ⟨asIso (h.counit.app X)⟩⟩
  · rintro ⟨_, ⟨i⟩⟩
    rw [NatTrans.isIso_app_iff_of_iso _ i.symm]
    infer_instance
/-
**CategoryTheory.Adjunction.mem_essImage_of_counit_isIso** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Adjunction`。
形式化陈述：mem_essImage_of_counit_isIso (A : D) [IsIso (h.counit.app A)] : L.essImage
 A
参数：A : D；h.counit.app A。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mem_essImage_of_counit_isIso (A : D)
    [IsIso (h.counit.app A)] : L.essImage A :=
  ⟨R.obj A, ⟨asIso (h.counit.app A)⟩⟩
/-
**CategoryTheory.Adjunction.isIso_counit_app_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Adjunction`。
形式化陈述：isIso_counit_app_of_iso [L.Faithful] [L.Full] {X : D} {Y : C} (e : X ≅ L.o
bj Y) : IsIso (h.counit.app X)
参数：e : X ≅ L.obj Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CategoryTheory.Adjunction.isIso_counit_app_iff_mem_essImage`：isIso_couni
t_app_iff_mem_essImage [L.Faithful] [L.Full] {X : D} : IsIso (h.counit.app X) ↔ 
L.essImage X
-/
lemma isIso_counit_app_of_iso [L.Faithful] [L.Full] {X : D} {Y : C} (e : X ≅ L.obj Y) :
    IsIso (h.counit.app X) :=
  (isIso_counit_app_iff_mem_essImage h).mpr ⟨Y, ⟨e.symm⟩⟩
/-
**CategoryTheory.Adjunction.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Adjunctio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [R.Faithful] [R.Full] {Y : D} : IsIso (h.unit.app (R.obj Y)) :=
  isIso_of_comp_hom_eq_id _ (h.right_triangle_components Y)
/-
**CategoryTheory.Adjunction.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Adjunctio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [R.Faithful] [R.Full] {X : C} : IsIso (L.map (h.unit.app X)) :=
  isIso_of_comp_hom_eq_id _ (h.left_triangle_components X)
/-
**CategoryTheory.Adjunction.isIso_unit_app_iff_mem_essImage** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Adjunction`。
形式化陈述：isIso_unit_app_iff_mem_essImage [R.Faithful] [R.Full] {Y : C} : IsIso (h.u
nit.app Y) ↔ R.essImage Y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.NatTrans.isIso_app_iff_of_iso`：isIso_app_iff_of_iso {F G 
: C ⥤ D} (α : F ⟶ G) {X Y : C} (e : X ≅ Y) : IsIso (α.app X) ↔ IsIso (α.app Y)
· 使用定理 `CategoryTheory.Adjunction.instIsIsoAppUnitObjOfFaithfulOfFull`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   {L : CategoryTheor…
-/
lemma isIso_unit_app_iff_mem_essImage [R.Faithful] [R.Full] {Y : C} :
    IsIso (h.unit.app Y) ↔ R.essImage Y := by
  constructor
  · intro
    exact ⟨L.obj Y, ⟨(asIso (h.unit.app Y)).symm⟩⟩
  · rintro ⟨_, ⟨i⟩⟩
    rw [NatTrans.isIso_app_iff_of_iso _ i.symm]
    infer_instance

/-- If `η_A` is an isomorphism, then `A` is in the essential image of `i`. -/
/-
**CategoryTheory.Adjunction.mem_essImage_of_unit_isIso** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Adjunction`。
形式化陈述：mem_essImage_of_unit_isIso (A : C) [IsIso (h.unit.app A)] : R.essImage A
参数：A : C；h.unit.app A。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `η_A` is an isomorphism, then `A` is in the essential image of `i`.
-/
theorem mem_essImage_of_unit_isIso (A : C)
    [IsIso (h.unit.app A)] : R.essImage A :=
  ⟨L.obj A, ⟨(asIso (h.unit.app A)).symm⟩⟩
/-
**CategoryTheory.Adjunction.isIso_unit_app_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Adjunction`。
形式化陈述：isIso_unit_app_of_iso [R.Faithful] [R.Full] {X : D} {Y : C} (e : Y ≅ R.obj
 X) : IsIso (h.unit.app Y)
参数：e : Y ≅ R.obj X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CategoryTheory.Adjunction.isIso_unit_app_iff_mem_essImage`：isIso_unit_ap
p_iff_mem_essImage [R.Faithful] [R.Full] {Y : C} : IsIso (h.unit.app Y) ↔ R.essI
mage Y
-/
lemma isIso_unit_app_of_iso [R.Faithful] [R.Full] {X : D} {Y : C} (e : Y ≅ R.obj X) :
    IsIso (h.unit.app Y) :=
  (isIso_unit_app_iff_mem_essImage h).mpr ⟨X, ⟨e.symm⟩⟩
/-
**CategoryTheory.Adjunction.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Adjunctio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [R.IsEquivalence] : IsIso h.unit := by
  have := fun Y => isIso_unit_app_of_iso h (R.objObjPreimageIso Y).symm
  apply NatIso.isIso_of_isIso_app
/-
**CategoryTheory.Adjunction.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Adjunctio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [L.IsEquivalence] : IsIso h.counit := by
  have := fun X => isIso_counit_app_of_iso h (L.objObjPreimageIso X).symm
  apply NatIso.isIso_of_isIso_app
/-
**CategoryTheory.Adjunction.isEquivalence_left_of_isEquivalence_right** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.Adjunction`。
形式化陈述：isEquivalence_left_of_isEquivalence_right (h : L ⊣ R) [R.IsEquivalence] : 
L.IsEquivalence
参数：h : L ⊣ R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Adjunction.instIsIsoFunctorUnitOfIsEquivalence`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   {L : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.instIsIsoAppCounitOfFullOfFaithful`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   {L : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.full`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{
v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.faithful`：∀ {C : Type u₁} {inst : C
ategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D}   {F : CategoryTheor…
-/
lemma isEquivalence_left_of_isEquivalence_right (h : L ⊣ R) [R.IsEquivalence] : L.IsEquivalence :=
  h.toEquivalence.isEquivalence_functor
/-
**CategoryTheory.Adjunction.isEquivalence_right_of_isEquivalence_left** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.Adjunction`。
形式化陈述：isEquivalence_right_of_isEquivalence_left (h : L ⊣ R) [L.IsEquivalence] : 
R.IsEquivalence
参数：h : L ⊣ R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用定理 `CategoryTheory.Adjunction.instIsIsoAppUnitOfFullOfFaithful`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {L : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.full`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{
v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.faithful`：∀ {C : Type u₁} {inst : C
ategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Adjunction.instIsIsoFunctorCounitOfIsEquivalence`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   {L : CategoryTheor…
-/
lemma isEquivalence_right_of_isEquivalence_left (h : L ⊣ R) [L.IsEquivalence] : R.IsEquivalence :=
  h.toEquivalence.isEquivalence_inverse
/-
**CategoryTheory.Adjunction.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Adjunctio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [L.IsEquivalence] : IsIso h.unit := by
  have := h.isEquivalence_right_of_isEquivalence_left
  infer_instance
/-
**CategoryTheory.Adjunction.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Adjunctio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [R.IsEquivalence] : IsIso h.counit := by
  have := h.isEquivalence_left_of_isEquivalence_right
  infer_instance

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Adjunction.isIso_map_unit_of_isLeftAdjoint_comp** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.Adjunction`。
形式化陈述：isIso_map_unit_of_isLeftAdjoint_comp {E : Type*} [Category* E] {T : C ⥤ E}
 {S : E ⥤ D} {X : C} (adj2 : T ⊣ S ⋙ R) [R.Faithful] [R.Full] : IsIso (T.map (h.
unit.app X))
参数：adj2 : T ⊣ S ⋙ R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.isIso_of_coyoneda_map_bijective`：isIso_of_coyoneda_map_bi
jective {X Y : C} (f : X ⟶ Y) (hf : forall (T : C), Function.Bijective (fun (x :
 Y ⟶ T) => f ≫ x)) : IsIso f
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Adjunction.counit_naturality`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.FullyFaithful.preimage_comp`：preimage_comp {X Y Z
 : C} (f : F.obj X ⟶ F.obj Y) (g : F.obj Y ⟶ F.obj Z) : hF.preimage (f ≫ g) = hF
.preimage f ≫ hF.preimage g
· 使用定理 `CategoryTheory.Functor.FullyFaithful.preimage_map`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.FullyFaithful.map_preimage`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Adjunction.left_triangle_components_assoc`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
theorem isIso_map_unit_of_isLeftAdjoint_comp {E : Type*} [Category* E]
    {T : C ⥤ E} {S : E ⥤ D} {X : C} (adj2 : T ⊣ S ⋙ R) [R.Faithful] [R.Full] :
    IsIso (T.map (h.unit.app X)) := by
  let FF := FullyFaithful.ofFullyFaithful R
  apply isIso_of_coyoneda_map_bijective
  intro Y
  convert!
    ((adj2.homEquiv (R.obj (L.obj X)) Y).trans <|
        FF.homEquiv.symm.trans <|
          (h.homEquiv X (S.obj Y)).trans (adj2.homEquiv X Y).symm).bijective using 1
  ext x
  have := adj2.counit_naturality x
  simp_all [Adjunction.homEquiv]

end CategoryTheory.Adjunction

