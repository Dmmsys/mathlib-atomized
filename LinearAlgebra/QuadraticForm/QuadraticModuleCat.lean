/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# The category of quadratic modules
-/

@[expose] public section

open CategoryTheory

universe v u

variable (R : Type u) [CommRing R]

/-- The category of quadratic modules; modules with an associated quadratic form -/
/-
**QuadraticModuleCat** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) → [CommRing R] → Type (max u (v + 1))
参数：v + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of quadratic modules; modules with an associated quadratic form
-/
structure QuadraticModuleCat extends ModuleCat.{v} R where
  /-- The quadratic form associated with the module. -/
  form : QuadraticForm R carrier

variable {R}

namespace QuadraticModuleCat

open QuadraticForm QuadraticMap

/-
**QuadraticModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort (QuadraticModuleCat.{v} R) (Type v) :=
  ⟨(·.carrier)⟩
/-
**QuadraticModuleCat.moduleCat_of_toModuleCat** 是 Mathlib 中的一个定理，位于命名空间 `Quadrat
icModuleCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] (X : QuadraticModuleCat R), ModuleCat.o
f R ↑X.toModuleCat = X.toModuleCat
参数：X : QuadraticModuleCat R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem moduleCat_of_toModuleCat (X : QuadraticModuleCat.{v} R) :
    ModuleCat.of R X.toModuleCat = X.toModuleCat :=
  rfl

/-- The object in the category of quadratic R-modules associated to a quadratic R-module. -/
/-
**QuadraticModuleCat.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `QuadraticModuleCat`。
形式化陈述：of {X : Type v} [AddCommGroup X] [Module R X] (Q : QuadraticForm R X) : Qu
adraticModuleCat R
参数：Q : QuadraticForm R X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The object in the category of quadratic R-modules associated to a quadratic R-mo
dule.
-/
abbrev of {X : Type v} [AddCommGroup X] [Module R X] (Q : QuadraticForm R X) :
    QuadraticModuleCat R :=
  { ModuleCat.of R X with
    form := Q }

/-- A type alias for `QuadraticForm.LinearIsometry` to avoid confusion between the categorical and
algebraic spellings of composition. -/
@[ext]
/-
**QuadraticModuleCat.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `QuadraticModuleCat`。
形式化陈述：{R : Type u} → [inst : CommRing R] → QuadraticModuleCat R → QuadraticModul
eCat R → Type v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type alias for `QuadraticForm.LinearIsometry` to avoid confusion between the c
ategorical and
algebraic spellings of composition.
-/
structure Hom (V W : QuadraticModuleCat.{v} R) where
  /-- The underlying isometry -/
  toIsometry' : V.form →qᵢ W.form
/-
**QuadraticModuleCat.category** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticModuleCat`。
形式化陈述：category : Category (QuadraticModuleCat.{v} R) where Hom M N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance category : Category (QuadraticModuleCat.{v} R) where
  Hom M N := Hom M N
  id M := ⟨Isometry.id M.form⟩
  comp f g := ⟨Isometry.comp g.toIsometry' f.toIsometry'⟩
/-
**QuadraticModuleCat.concreteCategory** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticModule
Cat`。
形式化陈述：concreteCategory : ConcreteCategory (QuadraticModuleCat.{v} R) fun V W => 
V.form ->qᵢ W.form where hom f
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance concreteCategory : ConcreteCategory (QuadraticModuleCat.{v} R)
    fun V W => V.form →qᵢ W.form where
  hom f := f.toIsometry'
  ofHom f := ⟨f⟩

/-- Turn a morphism in `QuadraticModuleCat` back into a `Isometry`. -/
/-
**QuadraticModuleCat.Hom.toIsometry** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticModuleCa
t.Hom`。
形式化陈述：{R : Type u} → [inst : CommRing R] → {X Y : QuadraticModuleCat R} → X.Hom 
Y → X.form →qᵢ Y.form
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a morphism in `QuadraticModuleCat` back into a `Isometry`.
-/
abbrev Hom.toIsometry {X Y : QuadraticModuleCat R} (f : Hom X Y) :=
  ConcreteCategory.hom (C := QuadraticModuleCat R) f

/-- Typecheck a `QuadraticForm.Isometry` as a morphism in `Module R`. -/
/-
**QuadraticModuleCat.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `QuadraticModuleCat`。
形式化陈述：ofHom {X Y : Type v} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Modul
e R Y] {Q₁ : QuadraticForm R X} {Q₂ : QuadraticForm R Y} (f : Q₁ ->qᵢ Q₂) : of Q
₁ ⟶ of Q₂
参数：f : Q₁ ->qᵢ Q₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck a `QuadraticForm.Isometry` as a morphism in `Module R`.
-/
abbrev ofHom {X Y : Type v} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    {Q₁ : QuadraticForm R X} {Q₂ : QuadraticForm R Y} (f : Q₁ →qᵢ Q₂) :
    of Q₁ ⟶ of Q₂ :=
  ConcreteCategory.ofHom f
/-
**QuadraticModuleCat.Hom.toIsometry_injective** 是 Mathlib 中的一个定理，位于命名空间 `Quadrat
icModuleCat.Hom`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] (V W : QuadraticModuleCat R), Function.
Injective QuadraticModuleCat.Hom.toIsometry
参数：V W : QuadraticModuleCat R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Hom.toIsometry_injective (V W : QuadraticModuleCat.{v} R) :
    Function.Injective (Hom.toIsometry : Hom V W → _) :=
  fun ⟨f⟩ ⟨g⟩ _ => by congr

@[ext]
/-
**QuadraticModuleCat.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `QuadraticModuleCat`。
形式化陈述：hom_ext {M N : QuadraticModuleCat.{v} R} (f g : M ⟶ N) (h : f.toIsometry =
 g.toIsometry) : f = g
参数：f g : M ⟶ N；h : f.toIsometry = g.toIsometry。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuadraticModuleCat.Hom.ext`：∀ {R : Type u} {inst : CommRing R} {V W : Qu
adraticModuleCat R} {x y : V.Hom W}, x.toIsometry' = y.toIsometry' → x = y
-/
lemma hom_ext {M N : QuadraticModuleCat.{v} R} (f g : M ⟶ N) (h : f.toIsometry = g.toIsometry) :
    f = g :=
  Hom.ext h
/-
**QuadraticModuleCat.toIsometry_comp** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticModuleC
at`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {M N U : QuadraticModuleCat R} (f : M ⟶
 N) (g : N ⟶ U),   QuadraticModuleCat.Hom.toIsometry (CategoryTheory.CategoryStr
uct.comp f g) =     (QuadraticModuleCat.Hom.toIsometry g).comp (QuadraticModuleC
at.Hom.toIsometry f)
参数：f : M ⟶ N；g : N ⟶ U；CategoryTheory.CategoryStruct.comp f g；QuadraticModuleCat
.Hom.toIsometry g；QuadraticModuleCat.Hom.toIsometry f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toIsometry_comp {M N U : QuadraticModuleCat.{v} R} (f : M ⟶ N) (g : N ⟶ U) :
    (f ≫ g).toIsometry = g.toIsometry.comp f.toIsometry :=
  rfl
/-
**QuadraticModuleCat.toIsometry_id** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticModuleCat
`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {M : QuadraticModuleCat R},   Quadratic
ModuleCat.Hom.toIsometry (CategoryTheory.CategoryStruct.id M) = QuadraticMap.Iso
metry.id M.form
参数：CategoryTheory.CategoryStruct.id M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toIsometry_id {M : QuadraticModuleCat.{v} R} :
    Hom.toIsometry (𝟙 M) = Isometry.id _ :=
  rfl
/-
**QuadraticModuleCat.hasForgetToModule** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticModul
eCat`。
形式化陈述：hasForgetToModule : HasForget₂ (QuadraticModuleCat R) (ModuleCat R) where 
forget₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToModule : HasForget₂ (QuadraticModuleCat R) (ModuleCat R) where
  forget₂ :=
    { obj := fun M => ModuleCat.of R M
      map := fun f => ModuleCat.ofHom f.toIsometry.toLinearMap }

@[simp]
/-
**QuadraticModuleCat.forget** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget₂_obj (X : QuadraticModuleCat R) :
    (forget₂ (QuadraticModuleCat R) (ModuleCat R)).obj X = ModuleCat.of R X :=
  rfl

@[simp]
/-
**QuadraticModuleCat.forget** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget₂_map (X Y : QuadraticModuleCat R) (f : X ⟶ Y) :
    (forget₂ (QuadraticModuleCat R) (ModuleCat R)).map f =
      ModuleCat.ofHom f.toIsometry.toLinearMap :=
  rfl

variable {X Y Z : Type v}
variable [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z]
variable {Q₁ : QuadraticForm R X} {Q₂ : QuadraticForm R Y} {Q₃ : QuadraticForm R Z}

/-- Build an isomorphism in the category `QuadraticModuleCat R` from a
`QuadraticForm.IsometryEquiv`. -/
@[simps]
/-
**QuadraticModuleCat.ofIso** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticModuleCat`。
形式化陈述：ofIso (e : Q₁.IsometryEquiv Q₂) : QuadraticModuleCat.of Q₁ ≅ QuadraticModu
leCat.of Q₂ where hom
参数：e : Q₁.IsometryEquiv Q₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build an isomorphism in the category `QuadraticModuleCat R` from a
`QuadraticForm.IsometryEquiv`.
-/
def ofIso (e : Q₁.IsometryEquiv Q₂) : QuadraticModuleCat.of Q₁ ≅ QuadraticModuleCat.of Q₂ where
  hom := ofHom e.toIsometry
  inv := ofHom e.symm.toIsometry
  hom_inv_id := Hom.ext <| DFunLike.ext _ _ e.left_inv
  inv_hom_id := Hom.ext <| DFunLike.ext _ _ e.right_inv
/-
**QuadraticModuleCat.ofIso_refl** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticModuleCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {X : Type v} [inst_1 : AddCommGroup X] 
[inst_2 : _root_.Module R X]   {Q₁ : QuadraticForm R X},   QuadraticModuleCat.of
Iso (QuadraticMap.IsometryEquiv.refl Q₁) = CategoryTheory.Iso.refl (QuadraticMod
uleCat.of Q₁)
参数：QuadraticMap.IsometryEquiv.refl Q₁；QuadraticModuleCat.of Q₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem ofIso_refl : ofIso (IsometryEquiv.refl Q₁) = .refl _ :=
  rfl
/-
**QuadraticModuleCat.ofIso_symm** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticModuleCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {X Y : Type v} [inst_1 : AddCommGroup X
] [inst_2 : _root_.Module R X]   [inst_3 : AddCommGroup Y] [inst_4 : _root_.Modu
le R Y] {Q₁ : QuadraticForm R X} {Q₂ : QuadraticForm R Y}   (e : QuadraticMap.Is
ometryEquiv Q₁ Q₂), QuadraticModuleCat.ofIso e.symm = (QuadraticModuleCat.ofIso 
e).symm
参数：e : QuadraticMap.IsometryEquiv Q₁ Q₂；QuadraticModuleCat.ofIso e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem ofIso_symm (e : Q₁.IsometryEquiv Q₂) : ofIso e.symm = (ofIso e).symm :=
  rfl
/-
**QuadraticModuleCat.ofIso_trans** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticModuleCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {X Y Z : Type v} [inst_1 : AddCommGroup
 X] [inst_2 : _root_.Module R X]   [inst_3 : AddCommGroup Y] [inst_4 : _root_.Mo
dule R Y] [inst_5 : AddCommGroup Z] [inst_6 : _root_.Module R Z]   {Q₁ : Quadrat
icForm R X} {Q₂ : QuadraticForm R Y} {Q₃ : QuadraticForm R Z} (e : QuadraticMap.
IsometryEquiv Q₁ Q₂)   (f : QuadraticMap.IsometryEquiv Q₂ Q₃),   QuadraticModule
Cat.ofIso (e.trans f) = QuadraticModuleCat.ofIso e ≪≫ QuadraticModuleCat.ofIso f
参数：e : QuadraticMap.IsometryEquiv Q₁ Q₂；f : QuadraticMap.IsometryEquiv Q₂ Q₃；e.t
rans f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem ofIso_trans (e : Q₁.IsometryEquiv Q₂) (f : Q₂.IsometryEquiv Q₃) :
    ofIso (e.trans f) = ofIso e ≪≫ ofIso f :=
  rfl

end QuadraticModuleCat

namespace CategoryTheory.Iso

open QuadraticForm

variable {X Y Z : QuadraticModuleCat.{v} R}

/-- Build a `QuadraticForm.IsometryEquiv` from an isomorphism in the category
`QuadraticModuleCat R`. -/
@[simps]
/-
**CategoryTheory.Iso.toIsometryEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.I
so`。
形式化陈述：toIsometryEquiv (i : X ≅ Y) : X.form.IsometryEquiv Y.form where toFun
参数：i : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build a `QuadraticForm.IsometryEquiv` from an isomorphism in the category
`QuadraticModuleCat R`.
-/
def toIsometryEquiv (i : X ≅ Y) : X.form.IsometryEquiv Y.form where
  toFun := i.hom.toIsometry
  invFun := i.inv.toIsometry
  left_inv x := by
    change (i.hom ≫ i.inv).toIsometry x = x
    simp
  right_inv x := by
    change (i.inv ≫ i.hom).toIsometry x = x
    simp
  map_add' := map_add _
  map_smul' := map_smul _
  map_app' := QuadraticMap.Isometry.map_app _
/-
**CategoryTheory.Iso.toIsometryEquiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Iso`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {X : QuadraticModuleCat R},   (Category
Theory.Iso.refl X).toIsometryEquiv = QuadraticMap.IsometryEquiv.refl X.form
参数：CategoryTheory.Iso.refl X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toIsometryEquiv_refl : toIsometryEquiv (.refl X) = .refl _ :=
  rfl
/-
**CategoryTheory.Iso.toIsometryEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Iso`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {X Y : QuadraticModuleCat R} (e : X ≅ Y
),   e.symm.toIsometryEquiv = e.toIsometryEquiv.symm
参数：e : X ≅ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toIsometryEquiv_symm (e : X ≅ Y) :
    toIsometryEquiv e.symm = (toIsometryEquiv e).symm :=
  rfl
/-
**CategoryTheory.Iso.toIsometryEquiv_trans** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Iso`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {X Y Z : QuadraticModuleCat R} (e : X ≅
 Y) (f : Y ≅ Z),   (e ≪≫ f).toIsometryEquiv = e.toIsometryEquiv.trans f.toIsomet
ryEquiv
参数：e : X ≅ Y；f : Y ≅ Z；e ≪≫ f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toIsometryEquiv_trans (e : X ≅ Y) (f : Y ≅ Z) :
    toIsometryEquiv (e ≪≫ f) = e.toIsometryEquiv.trans f.toIsometryEquiv :=
  rfl

end CategoryTheory.Iso

