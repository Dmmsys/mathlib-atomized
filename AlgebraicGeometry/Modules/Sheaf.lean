/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Andrew Yang
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.AlgebraicGeometry.Modules.Presheaf
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Adj
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Cat
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.Topology.Sheaves.Module

/-!
# The category of sheaves of modules over a scheme

In this file, we define the abelian category of sheaves of modules
`X.Modules` over a scheme `X`, and study its basic functoriality.

-/

@[expose] public section

universe t u

open CategoryTheory Limits TopologicalSpace SheafOfModules Bicategory

namespace AlgebraicGeometry.Scheme

variable {X Y Z T : Scheme.{u}}

variable (X) in
/-- The category of sheaves of modules over a scheme. -/
/-
**AlgebraicGeometry.Scheme.Modules** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.
Scheme`。
形式化陈述：Modules
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of sheaves of modules over a scheme.
-/
def Modules := SheafOfModules.{u} X.ringCatSheaf

namespace Modules

/-- Morphisms between `𝒪ₓ`-modules. Use `Hom.app` to act on sections. -/
/-
**AlgebraicGeometry.Scheme.Modules.Hom** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeome
try.Scheme.Modules`。
形式化陈述：Hom (M N : X.Modules) : Type u
参数：M N : X.Modules。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Morphisms between `𝒪ₓ`-modules. Use `Hom.app` to act on sections.
-/
def Hom (M N : X.Modules) : Type u := SheafOfModules.Hom M N
/-
**AlgebraicGeometry.Scheme.Modules.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry
.Scheme.Modules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category X.Modules where
  Hom := Modules.Hom
  __ := (inferInstance : Category (SheafOfModules.{u} X.ringCatSheaf))
/-
**AlgebraicGeometry.Scheme.Modules.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry
.Scheme.Modules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Abelian X.Modules :=
  inferInstanceAs <| Abelian (SheafOfModules.{u} X.ringCatSheaf)
/-
**AlgebraicGeometry.Scheme.Modules.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry
.Scheme.Modules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasLimits X.Modules := inferInstanceAs (HasLimits (SheafOfModules X.ringCatSheaf))
/-
**AlgebraicGeometry.Scheme.Modules.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry
.Scheme.Modules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasColimits X.Modules := inferInstanceAs (HasColimits (SheafOfModules X.ringCatSheaf))

section Functor

variable (X) in
/-- The forgetful functor from `𝒪ₓ`-modules to presheaves of modules.
This is mostly useful to transport results from (pre)sheaves of modules to `𝒪ₓ`-modules and
usually shouldn't be used directly when working with actual `𝒪ₓ`-modules. -/
/-
**AlgebraicGeometry.Scheme.Modules.toPresheafOfModules** 是 Mathlib 中的一个定义，位于命名空间
 `AlgebraicGeometry.Scheme.Modules`。
形式化陈述：toPresheafOfModules : X.Modules ⥤ X.PresheafOfModules
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from `𝒪ₓ`-modules to presheaves of modules.
This is mostly useful to transport results from (pre)sheaves of modules to `𝒪ₓ`-
modules and
usually shouldn't be used directly when working with actual `𝒪ₓ`-modules.
-/
def toPresheafOfModules : X.Modules ⥤ X.PresheafOfModules := SheafOfModules.forget _

/-- The forgetful functor from `𝒪ₓ`-modules to presheaves of modules is fully faithful. -/
/-
**AlgebraicGeometry.Scheme.Modules.fullyFaithfulToPresheafOfModules** 是 Mathlib 
中的一个定义，位于命名空间 `AlgebraicGeometry.Scheme.Modules`。
形式化陈述：fullyFaithfulToPresheafOfModules : (Modules.toPresheafOfModules X).FullyFa
ithful
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from `𝒪ₓ`-modules to presheaves of modules is fully faithf
ul.
-/
def fullyFaithfulToPresheafOfModules : (Modules.toPresheafOfModules X).FullyFaithful :=
  SheafOfModules.fullyFaithfulForget _
/-
**AlgebraicGeometry.Scheme.Modules.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry
.Scheme.Modules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (toPresheafOfModules X).Full := fullyFaithfulToPresheafOfModules.full
/-
**AlgebraicGeometry.Scheme.Modules.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry
.Scheme.Modules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (toPresheafOfModules X).Faithful := fullyFaithfulToPresheafOfModules.faithful
/-
**AlgebraicGeometry.Scheme.Modules.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry
.Scheme.Modules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (toPresheafOfModules X).IsRightAdjoint :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).isRightAdjoint

variable (X) in
/-- The forgetful functor from `𝒪ₓ`-modules to presheaves of abelian groups. -/
/-
**AlgebraicGeometry.Scheme.Modules.toPresheaf** 是 Mathlib 中的一个定义，位于命名空间 `Algebra
icGeometry.Scheme.Modules`。
形式化陈述：toPresheaf : X.Modules ⥤ TopCat.Presheaf Ab X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from `𝒪ₓ`-modules to presheaves of abelian groups.
-/
noncomputable def toPresheaf : X.Modules ⥤ TopCat.Presheaf Ab X :=
  toPresheafOfModules X ⋙ PresheafOfModules.toPresheaf _
/-
**AlgebraicGeometry.Scheme.Modules.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry
.Scheme.Modules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (toPresheaf X).Faithful := .comp _ (PresheafOfModules.toPresheaf _)
/-
**AlgebraicGeometry.Scheme.Modules.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry
.Scheme.Modules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesLimits (toPresheaf X) := comp_preservesLimits _ (PresheafOfModules.toPresheaf _)
/-
**AlgebraicGeometry.Scheme.Modules.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry
.Scheme.Modules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (toPresheaf X).ReflectsIsomorphisms :=
  reflectsIsomorphisms_comp _ (PresheafOfModules.toPresheaf _)

end Functor

variable {M N K : X.Modules} {φ : M ⟶ N} {U V : X.Opens}

section Presheaf

/-- The underlying abelian presheaf of an `𝒪ₓ`-module. -/
/-
**AlgebraicGeometry.Scheme.Modules.presheaf** 是 Mathlib 中的一个定义，位于命名空间 `Algebraic
Geometry.Scheme.Modules`。
形式化陈述：presheaf (M : X.Modules) : TopCat.Presheaf Ab X
参数：M : X.Modules。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying abelian presheaf of an `𝒪ₓ`-module.
-/
noncomputable def presheaf (M : X.Modules) : TopCat.Presheaf Ab X := M.1.presheaf

/-- Notation for sections of a presheaf of module. -/
scoped[AlgebraicGeometry] notation3 "Γ(" M ", " U ")" => (Scheme.Modules.presheaf M).obj (.op U)

/-
**AlgebraicGeometry.Scheme.Modules.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry
.Scheme.Modules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module Γ(X, U) Γ(M, U) := (M.val.obj (.op U)).isModule

variable (M) in
/-
**AlgebraicGeometry.Scheme.Modules.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `Algebraic
Geometry.Scheme.Modules`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} (M : X.Modules) {U V : X.Opens} (i : U ⟶ 
V) (r : ↑(X.presheaf.obj (Opposite.op V)))   (x : ↑(M.presheaf.obj (Opposite.op 
V))),   (CategoryTheory.ConcreteCategory.hom (M.presheaf.map i.op)) (r • x) =   
  (CategoryTheory.ConcreteCategory.hom (X.presheaf.map i.op)) r •       (Categor
yTheory.ConcreteCategory.hom (M.presheaf.map i.op)) x
参数：M : X.Modules；i : U ⟶ V；r : ↑(X.presheaf.obj (Opposite.op V))；x : ↑(M.preshea
f.obj (Opposite.op V))；CategoryTheory.ConcreteCategory.hom (M.presheaf.map i.op)
；r • x；CategoryTheory.ConcreteCategory.hom (X.presheaf.map i.op)；CategoryTheory.
ConcreteCategory.hom (M.presheaf.map i.op)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PresheafOfModules.map_smul`：∀ {C : Type u₁} [inst : CategoryTheory.Categ
ory.{v₁, u₁} C] {R : CategoryTheory.Functor Cᵒᵖ RingCat}   (M : PresheafOfModule
s R) {X Y : Cᵒᵖ}…
-/
@[simp] lemma map_smul (i : U ⟶ V) (r : Γ(X, V)) (x : Γ(M, V)) :
    M.presheaf.map i.op (r • x) = X.presheaf.map i.op r • M.presheaf.map i.op x :=
  M.val.map_smul _ _ _

/-- Scalar multiplication as an endomorphism of `Γ(M, U)`. -/
/-
**AlgebraicGeometry.Scheme.Modules.smul** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeom
etry.Scheme.Modules`。
形式化陈述：smul : Γ(X, U) ->+* End Γ(M, U)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Scalar multiplication as an endomorphism of `Γ(M, U)`.
-/
def smul : Γ(X, U) →+* End Γ(M, U) :=
  (M.val.obj (.op U)).smul

@[simp]
/-
**AlgebraicGeometry.Scheme.Modules.smul_apply** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
icGeometry.Scheme.Modules`。
形式化陈述：smul_apply (r : Γ(X, U)) (x : Γ(M, U)) : (M.smul r).hom x = r • x
参数：r : Γ(X, U)；x : Γ(M, U)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smul_apply (r : Γ(X, U)) (x : Γ(M, U)) : (M.smul r).hom x = r • x := rfl

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Modules.map_comp_smul** 是 Mathlib 中的一个引理，位于命名空间 `Alge
braicGeometry.Scheme.Modules`。
形式化陈述：map_comp_smul (i : U ⟶ V) (r : Γ(X, V)) : M.smul r ≫ M.presheaf.map i.op =
 M.presheaf.map i.op ≫ M.smul (X.presheaf.map i.op r)
参数：i : U ⟶ V；r : Γ(X, V)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGrpCat.hom_ext`：∀ {X Y : AddCommGrpCat} {f g : X ⟶ Y}, AddCommGrp
Cat.Hom.hom f = AddCommGrpCat.Hom.hom g → f = g
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Modules.map_smul`：∀ {X : AlgebraicGeometry.Sche
me} (M : X.Modules) {U V : X.Opens} (i : U ⟶ V) (r : ↑(X.presheaf.obj (Opposite.
op V)))   (x : ↑(M.presheaf.obj…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_comp_smul (i : U ⟶ V) (r : Γ(X, V)) :
    M.smul r ≫ M.presheaf.map i.op = M.presheaf.map i.op ≫ M.smul (X.presheaf.map i.op r) := by
  ext
  simp

/-- The underlying map between abelian presheaves of a morphism of `𝒪ₓ`-modules. -/
/-
**AlgebraicGeometry.Scheme.Modules.Hom.mapPresheaf** 是 Mathlib 中的一个定义，位于命名空间 `Al
gebraicGeometry.Scheme.Modules.Hom`。
形式化陈述：{X : AlgebraicGeometry.Scheme} → {M N : X.Modules} → (M ⟶ N) → (M.presheaf
 ⟶ N.presheaf)
参数：M ⟶ N；M.presheaf ⟶ N.presheaf。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying map between abelian presheaves of a morphism of `𝒪ₓ`-modules.
-/
noncomputable def Hom.mapPresheaf (φ : M ⟶ N) : M.presheaf ⟶ N.presheaf :=
  (toPresheaf X).map φ

/-- The application of a morphism of `𝒪ₓ`-modules to sections. -/
/-
**AlgebraicGeometry.Scheme.Modules.Hom.app** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicG
eometry.Scheme.Modules.Hom`。
形式化陈述：{X : AlgebraicGeometry.Scheme} →   {M N : X.Modules} → (M ⟶ N) → (U : X.Op
ens) → M.presheaf.obj (Opposite.op U) ⟶ N.presheaf.obj (Opposite.op U)
参数：M ⟶ N；U : X.Opens；Opposite.op U；Opposite.op U。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The application of a morphism of `𝒪ₓ`-modules to sections.
-/
def Hom.app (φ : M ⟶ N) (U : X.Opens) : Γ(M, U) ⟶ Γ(N, U) :=
  (forget₂ _ _).map (φ.val.app (.op U))
/-
**AlgebraicGeometry.Scheme.Modules.mapPresheaf_app** 是 Mathlib 中的一个定理，位于命名空间 `Al
gebraicGeometry.Scheme.Modules`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {M N : X.Modules} (φ : M ⟶ N) (U : (Topol
ogicalSpace.Opens ↥X)ᵒᵖ),   (AlgebraicGeometry.Scheme.Modules.Hom.mapPresheaf φ)
.app U =     AlgebraicGeometry.Scheme.Modules.Hom.app φ (Opposite.unop U)
参数：φ : M ⟶ N；U : (TopologicalSpace.Opens ↥X)ᵒᵖ；AlgebraicGeometry.Scheme.Modules.
Hom.mapPresheaf φ；Opposite.unop U。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mapPresheaf_app (φ : M ⟶ N) (U) : φ.mapPresheaf.app U = φ.app U.unop := rfl

@[simp]
/-
**AlgebraicGeometry.Scheme.Modules.Hom.app_smul** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
raicGeometry.Scheme.Modules.Hom`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {M N : X.Modules} {U : X.Opens} (φ : M ⟶ 
N) (r : ↑(X.presheaf.obj (Opposite.op U)))   (x : ↑(M.presheaf.obj (Opposite.op 
U))),   (CategoryTheory.ConcreteCategory.hom (AlgebraicGeometry.Scheme.Modules.H
om.app φ U)) (r • x) =     r • (CategoryTheory.ConcreteCategory.hom (AlgebraicGe
ometry.Scheme.Modules.Hom.app φ U)) x
参数：φ : M ⟶ N；r : ↑(X.presheaf.obj (Opposite.op U))；x : ↑(M.presheaf.obj (Opposit
e.op U))；CategoryTheory.ConcreteCategory.hom (AlgebraicGeometry.Scheme.Modules.H
om.app φ U)；r • x；CategoryTheory.ConcreteCategory.hom (AlgebraicGeometry.Scheme.
Modules.Hom.app φ U)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
-/
lemma Hom.app_smul (φ : M ⟶ N) (r : Γ(X, U)) (x : Γ(M, U)) :
    φ.app U (r • x) = r • φ.app U x :=
  (φ.val.app (.op U)).hom.map_smul r x
/-
**AlgebraicGeometry.Scheme.Modules.Hom.add_app** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
aicGeometry.Scheme.Modules.Hom`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {M N : X.Modules} {U : X.Opens} (φ ψ : M 
⟶ N),   AlgebraicGeometry.Scheme.Modules.Hom.app (φ + ψ) U =     AlgebraicGeomet
ry.Scheme.Modules.Hom.app φ U + AlgebraicGeometry.Scheme.Modules.Hom.app ψ U
参数：φ ψ : M ⟶ N；φ + ψ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma Hom.add_app (φ ψ : M ⟶ N) : (φ + ψ).app U = φ.app U + ψ.app U := rfl
/-
**AlgebraicGeometry.Scheme.Modules.Hom.sub_app** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
aicGeometry.Scheme.Modules.Hom`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {M N : X.Modules} {U : X.Opens} (φ ψ : M 
⟶ N),   AlgebraicGeometry.Scheme.Modules.Hom.app (φ - ψ) U =     AlgebraicGeomet
ry.Scheme.Modules.Hom.app φ U - AlgebraicGeometry.Scheme.Modules.Hom.app ψ U
参数：φ ψ : M ⟶ N；φ - ψ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma Hom.sub_app (φ ψ : M ⟶ N) : (φ - ψ).app U = φ.app U - ψ.app U := rfl
/-
**AlgebraicGeometry.Scheme.Modules.Hom.zero_app** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
raicGeometry.Scheme.Modules.Hom`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {M N : X.Modules} {U : X.Opens}, Algebrai
cGeometry.Scheme.Modules.Hom.app 0 U = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma Hom.zero_app : (0 : M ⟶ N).app U = 0 := rfl
/-
**AlgebraicGeometry.Scheme.Modules.Hom.id_app** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icGeometry.Scheme.Modules.Hom`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {U : X.Opens} (M : X.Modules),   Algebrai
cGeometry.Scheme.Modules.Hom.app (CategoryTheory.CategoryStruct.id M) U =     Ca
tegoryTheory.CategoryStruct.id (M.presheaf.obj (Opposite.op U))
参数：M : X.Modules；CategoryTheory.CategoryStruct.id M；M.presheaf.obj (Opposite.op 
U)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma Hom.id_app (M : X.Modules) : (𝟙 M :).app U = 𝟙 _ := rfl
/-
**AlgebraicGeometry.Scheme.Modules.Hom.comp_app** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
raicGeometry.Scheme.Modules.Hom`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {M N K : X.Modules} {U : X.Opens} (φ : M 
⟶ N) (ψ : N ⟶ K),   AlgebraicGeometry.Scheme.Modules.Hom.app (CategoryTheory.Cat
egoryStruct.comp φ ψ) U =     CategoryTheory.CategoryStruct.comp (AlgebraicGeome
try.Scheme.Modules.Hom.app φ U)       (AlgebraicGeometry.Scheme.Modules.Hom.app 
ψ U)
参数：φ : M ⟶ N；ψ : N ⟶ K；CategoryTheory.CategoryStruct.comp φ ψ；AlgebraicGeometry.
Scheme.Modules.Hom.app φ U；AlgebraicGeometry.Scheme.Modules.Hom.app ψ U。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma Hom.comp_app (φ : M ⟶ N) (ψ : N ⟶ K) : (φ ≫ ψ).app U = φ.app U ≫ ψ.app U := rfl

@[ext]
/-
**AlgebraicGeometry.Scheme.Modules.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicG
eometry.Scheme.Modules`。
形式化陈述：hom_ext (f g : M ⟶ N) (H : forall U, f.app U = g.app U) : f = g
参数：f g : M ⟶ N；H : forall U, f.app U = g.app U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SheafOfModules.hom_ext`：hom_ext {X Y : SheafOfModules.{v} R} {f g : X ⟶ 
Y} (h : f.val = g.val) : f = g
· 使用引理 `PresheafOfModules.hom_ext`：hom_ext {f g : M₁ ⟶ M₂} (h : forall (X : Cᵒᵖ)
, f.app X = g.app X) : f = g
· 使用引理 `ModuleCat.hom_ext`：hom_ext {M N : ModuleCat.{v} R} {f g : M ⟶ N} (hf : f
.hom = g.hom) : f = g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma hom_ext (f g : M ⟶ N) (H : ∀ U, f.app U = g.app U) : f = g := by
  apply SheafOfModules.hom_ext
  ext U x
  exact congr($(H U.unop) x)
/-
**AlgebraicGeometry.Scheme.Modules.isSheaf** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicG
eometry.Scheme.Modules`。
形式化陈述：isSheaf (M : X.Modules) : M.presheaf.IsSheaf
参数：M : X.Modules。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SheafOfModules.isSheaf`：∀ {C : Type u₁} [inst : CategoryTheory.Category.
{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C}   {R : CategoryTheory.Sh
eaf J RingCa…
-/
lemma isSheaf (M : X.Modules) : M.presheaf.IsSheaf := SheafOfModules.isSheaf M
/-
**AlgebraicGeometry.Scheme.Modules.toPresheaf_obj** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry.Scheme.Modules`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {M : X.Modules}, (AlgebraicGeometry.Schem
e.Modules.toPresheaf X).obj M = M.presheaf
参数：AlgebraicGeometry.Scheme.Modules.toPresheaf X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toPresheaf_obj : (toPresheaf X).obj M = M.presheaf := rfl
/-
**AlgebraicGeometry.Scheme.Modules.toPresheaf_map** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry.Scheme.Modules`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {M N : X.Modules} {φ : M ⟶ N},   (Algebra
icGeometry.Scheme.Modules.toPresheaf X).map φ = AlgebraicGeometry.Scheme.Modules
.Hom.mapPresheaf φ
参数：AlgebraicGeometry.Scheme.Modules.toPresheaf X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toPresheaf_map : (toPresheaf X).map φ = φ.mapPresheaf := rfl

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.Modules.Hom.isIso_iff_isIso_app** 是 Mathlib 中的一个定理，位于
命名空间 `AlgebraicGeometry.Scheme.Modules.Hom`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {M N : X.Modules} {φ : M ⟶ N},   Category
Theory.IsIso φ ↔ ∀ (U : X.Opens), CategoryTheory.IsIso (AlgebraicGeometry.Scheme
.Modules.Hom.app φ U)
参数：U : X.Opens；AlgebraicGeometry.Scheme.Modules.Hom.app φ U。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.isIso_iff_of_reflects_iso`：isIso_iff_of_reflects_iso {A B
 : C} (f : A ⟶ B) (F : C ⥤ D) [F.ReflectsIsomorphisms] : IsIso (F.map f) ↔ IsIso
 f
· 使用定理 `AlgebraicGeometry.Scheme.Modules.instReflectsIsomorphismsPresheafAbCarri
erCommRingCatToPresheaf`：∀ {X : AlgebraicGeometry.Scheme}, (AlgebraicGeometry.Sc
heme.Modules.toPresheaf X).ReflectsIsomorphisms
· 使用定理 `CategoryTheory.NatTrans.isIso_iff_isIso_app`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Opposite.op_surjective`：op_surjective : Function.Surjective (op : α -> α
ᵒᵖ)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Hom.isIso_iff_isIso_app {M N : X.Modules} {φ : M ⟶ N} :
    IsIso φ ↔ ∀ U, IsIso (φ.app U) := by
  rw [← isIso_iff_of_reflects_iso _ (toPresheaf X), NatTrans.isIso_iff_isIso_app]
  simp [Opposite.op_surjective.forall]
/-
**AlgebraicGeometry.Scheme.Modules.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry
.Scheme.Modules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsIso φ] : IsIso (φ.app U) := Hom.isIso_iff_isIso_app.mp ‹_› _

@[simp, push ←]
/-
**AlgebraicGeometry.Scheme.Modules.inv_app** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicG
eometry.Scheme.Modules`。
形式化陈述：inv_app [IsIso φ] : (inv φ).app U = inv (φ.app U)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsIso.eq_inv_of_hom_inv_id`：eq_inv_of_hom_inv_id {f : X ⟶
 Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) : g = inv f
· 使用定理 `AlgebraicGeometry.Scheme.Modules.instIsIsoAbApp`：∀ {X : AlgebraicGeometr
y.Scheme} {M N : X.Modules} {φ : M ⟶ N} {U : X.Opens} [CategoryTheory.IsIso φ], 
  CategoryTheory.IsIso (AlgebraicGeom…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_app [IsIso φ] : (inv φ).app U = inv (φ.app U) := by
  apply IsIso.eq_inv_of_hom_inv_id
  simp [← Hom.comp_app]

end Presheaf

noncomputable section Functorial

variable (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)

/-- The pushforward functor for categories of sheaves of modules over schemes. -/
/-
**AlgebraicGeometry.Scheme.Modules.pushforward** 是 Mathlib 中的一个定义，位于命名空间 `Algebr
aicGeometry.Scheme.Modules`。
形式化陈述：pushforward : X.Modules ⥤ Y.Modules
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pushforward functor for categories of sheaves of modules over schemes.
-/
def pushforward : X.Modules ⥤ Y.Modules :=
  SheafOfModules.pushforward f.toRingCatSheafHom

@[simp]
/-
**AlgebraicGeometry.Scheme.Modules.pushforward_obj_obj** 是 Mathlib 中的一个引理，位于命名空间
 `AlgebraicGeometry.Scheme.Modules`。
形式化陈述：pushforward_obj_obj (M : X.Modules) (U : Y.Opens) : Γ((pushforward f).obj 
M, U) = Γ(M, f ⁻¹ᵁ U)
参数：M : X.Modules；U : Y.Opens。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pushforward_obj_obj (M : X.Modules) (U : Y.Opens) :
    Γ((pushforward f).obj M, U) = Γ(M, f ⁻¹ᵁ U) := rfl

@[simp]
/-
**AlgebraicGeometry.Scheme.Modules.pushforward_obj_presheaf_map** 是 Mathlib 中的一个
引理，位于命名空间 `AlgebraicGeometry.Scheme.Modules`。
形式化陈述：pushforward_obj_presheaf_map {U V : Y.Opens} (i : U ⟶ V) : ((pushforward f
).obj M).presheaf.map i.op = M.presheaf.map ((Opens.map f.base).map i).op
参数：i : U ⟶ V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pushforward_obj_presheaf_map {U V : Y.Opens} (i : U ⟶ V) :
    ((pushforward f).obj M).presheaf.map i.op = M.presheaf.map ((Opens.map f.base).map i).op := rfl

@[simp]
/-
**AlgebraicGeometry.Scheme.Modules.pushforward_map_app** 是 Mathlib 中的一个引理，位于命名空间
 `AlgebraicGeometry.Scheme.Modules`。
形式化陈述：pushforward_map_app (φ : M ⟶ N) (U : Y.Opens) : ((pushforward f).map φ).ap
p U = φ.app (f ⁻¹ᵁ U)
参数：φ : M ⟶ N；U : Y.Opens。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pushforward_map_app (φ : M ⟶ N) (U : Y.Opens) :
    ((pushforward f).map φ).app U = φ.app (f ⁻¹ᵁ U) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The pullback functor for categories of sheaves of modules over schemes. -/
/-
**AlgebraicGeometry.Scheme.Modules.pullback** 是 Mathlib 中的一个定义，位于命名空间 `Algebraic
Geometry.Scheme.Modules`。
形式化陈述：pullback : Y.Modules ⥤ X.Modules
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback functor for categories of sheaves of modules over schemes.
-/
def pullback : Y.Modules ⥤ X.Modules :=
  SheafOfModules.pullback f.toRingCatSheafHom

set_option backward.isDefEq.respectTransparency.types false in
/-- The pullback functor for categories of sheaves of modules over schemes
is left adjoint to the pushforward functor. -/
/-
**AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction** 是 Mathlib 中的一
个定义，位于命名空间 `AlgebraicGeometry.Scheme.Modules`。
形式化陈述：pullbackPushforwardAdjunction : pullback f ⊣ pushforward f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback functor for categories of sheaves of modules over schemes
is left adjoint to the pushforward functor.
-/
def pullbackPushforwardAdjunction : pullback f ⊣ pushforward f :=
  SheafOfModules.pullbackPushforwardAdjunction _

section

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryCoproducts
  preservesBinaryBiproducts_of_preservesBinaryProducts

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.Modules.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry
.Scheme.Modules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (pullback f).IsLeftAdjoint := (pullbackPushforwardAdjunction f).isLeftAdjoint
/-
**AlgebraicGeometry.Scheme.Modules.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry
.Scheme.Modules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (pushforward f).IsRightAdjoint := (pullbackPushforwardAdjunction f).isRightAdjoint
/-
**AlgebraicGeometry.Scheme.Modules.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry
.Scheme.Modules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (pushforward f).Additive := Functor.additive_of_preservesBinaryBiproducts _
set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.Modules.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry
.Scheme.Modules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (pullback f).Additive := Functor.additive_of_preservesBinaryBiproducts _

end

variable (X) in
/-- The pushforward of sheaves of modules by the identity morphism identifies
to the identity functor. -/
/-
**AlgebraicGeometry.Scheme.Modules.pushforwardId** 是 Mathlib 中的一个定义，位于命名空间 `Alge
braicGeometry.Scheme.Modules`。
形式化陈述：pushforwardId : pushforward (𝟙 X) ≅ 𝟭 _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pushforward of sheaves of modules by the identity morphism identifies
to the identity functor.
-/
def pushforwardId : pushforward (𝟙 X) ≅ 𝟭 _ :=
  SheafOfModules.pushforwardId _
/-
**AlgebraicGeometry.Scheme.Modules.pushforwardId_hom_app_app** 是 Mathlib 中的一个定理，
位于命名空间 `AlgebraicGeometry.Scheme.Modules`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {M : X.Modules} {U : X.Opens},   Algebrai
cGeometry.Scheme.Modules.Hom.app ((AlgebraicGeometry.Scheme.Modules.pushforwardI
d X).hom.app M) U =     CategoryTheory.CategoryStruct.id       (((AlgebraicGeome
try.Scheme.Modules.pushforward (CategoryTheory.CategoryStruct.id X)).obj M).pres
heaf.obj         (Opposite.op U))
参数：(AlgebraicGeometry.Scheme.Modules.pushforwardId X).hom.app M；((AlgebraicGeome
try.Scheme.Modules.pushforward (CategoryTheory.CategoryStruct.id X)).obj M).pres
heaf.obj         (Opposite.op U)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma pushforwardId_hom_app_app : ((pushforwardId X).hom.app M).app U = 𝟙 _ := rfl
/-
**AlgebraicGeometry.Scheme.Modules.pushforwardId_inv_app_app** 是 Mathlib 中的一个定理，
位于命名空间 `AlgebraicGeometry.Scheme.Modules`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {M : X.Modules} {U : X.Opens},   Algebrai
cGeometry.Scheme.Modules.Hom.app ((AlgebraicGeometry.Scheme.Modules.pushforwardI
d X).inv.app M) U =     CategoryTheory.CategoryStruct.id (((CategoryTheory.Funct
or.id X.Modules).obj M).presheaf.obj (Opposite.op U))
参数：(AlgebraicGeometry.Scheme.Modules.pushforwardId X).inv.app M；((CategoryTheory
.Functor.id X.Modules).obj M).presheaf.obj (Opposite.op U)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma pushforwardId_inv_app_app : ((pushforwardId X).inv.app M).app U = 𝟙 _ := rfl

set_option backward.isDefEq.respectTransparency.types false in
variable (X) in
/-- The pullback of sheaves of modules by the identity morphism identifies
to the identity functor. -/
/-
**AlgebraicGeometry.Scheme.Modules.pullbackId** 是 Mathlib 中的一个定义，位于命名空间 `Algebra
icGeometry.Scheme.Modules`。
形式化陈述：pullbackId : pullback (𝟙 X) ≅ 𝟭 _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of sheaves of modules by the identity morphism identifies
to the identity functor.
-/
def pullbackId : pullback (𝟙 X) ≅ 𝟭 _ :=
  SheafOfModules.pullbackId _

set_option backward.isDefEq.respectTransparency.types false in
variable (X) in
/-
**AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackId_hom** 是 Mathlib 中的一
个引理，位于命名空间 `AlgebraicGeometry.Scheme.Modules`。
形式化陈述：conjugateEquiv_pullbackId_hom : conjugateEquiv .id (pullbackPushforwardAdj
unction (𝟙 X)) (pullbackId X).hom = (pushforwardId X).inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SheafOfModules.conjugateEquiv_pullbackId_hom`：conjugateEquiv_pullbackId_
hom : conjugateEquiv .id (pullbackPushforwardAdjunction.{v} _) (pullbackId S).ho
m = (pushforwardId S).inv
-/
lemma conjugateEquiv_pullbackId_hom :
    conjugateEquiv .id (pullbackPushforwardAdjunction (𝟙 X)) (pullbackId X).hom =
      (pushforwardId X).inv :=
  SheafOfModules.conjugateEquiv_pullbackId_hom _

/-- The composition of two pushforward functors for sheaves of modules on schemes
identify to the pushforward for the composition. -/
/-
**AlgebraicGeometry.Scheme.Modules.pushforwardComp** 是 Mathlib 中的一个定义，位于命名空间 `Al
gebraicGeometry.Scheme.Modules`。
形式化陈述：pushforwardComp : pushforward f ⋙ pushforward g ≅ pushforward (f ≫ g)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of two pushforward functors for sheaves of modules on schemes
identify to the pushforward for the composition.
-/
def pushforwardComp :
    pushforward f ⋙ pushforward g ≅ pushforward (f ≫ g) :=
  SheafOfModules.pushforwardComp _ _
/-
**AlgebraicGeometry.Scheme.Modules.pushforwardComp_hom_app_app** 是 Mathlib 中的一个定
理，位于命名空间 `AlgebraicGeometry.Scheme.Modules`。
形式化陈述：∀ {X Y Z : AlgebraicGeometry.Scheme} {M : X.Modules} (f : X ⟶ Y) (g : Y ⟶ 
Z) (U : Z.Opens),   AlgebraicGeometry.Scheme.Modules.Hom.app ((AlgebraicGeometry
.Scheme.Modules.pushforwardComp f g).hom.app M) U =     CategoryTheory.CategoryS
truct.id       ((((AlgebraicGeometry.Scheme.Modules.pushforward f).comp (Algebra
icGeometry.Scheme.Modules.pushforward g)).obj               M).presheaf.obj     
    (Opposite.op U))
参数：f : X ⟶ Y；g : Y ⟶ Z；U : Z.Opens；(AlgebraicGeometry.Scheme.Modules.pushforward
Comp f g).hom.app M；(((AlgebraicGeometry.Scheme.Modules.pushforward f).comp (Alg
ebraicGeometry.Scheme.Modules.pushforward g)).obj               M).presheaf.obj 
        (Opposite.op U)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma pushforwardComp_hom_app_app (U) : ((pushforwardComp f g).hom.app M).app U = 𝟙 _ := rfl
/-
**AlgebraicGeometry.Scheme.Modules.pushforwardComp_inv_app_app** 是 Mathlib 中的一个定
理，位于命名空间 `AlgebraicGeometry.Scheme.Modules`。
形式化陈述：∀ {X Y Z : AlgebraicGeometry.Scheme} {M : X.Modules} (f : X ⟶ Y) (g : Y ⟶ 
Z) (U : Z.Opens),   AlgebraicGeometry.Scheme.Modules.Hom.app ((AlgebraicGeometry
.Scheme.Modules.pushforwardComp f g).inv.app M) U =     CategoryTheory.CategoryS
truct.id       (((AlgebraicGeometry.Scheme.Modules.pushforward (CategoryTheory.C
ategoryStruct.comp f g)).obj M).presheaf.obj         (Opposite.op U))
参数：f : X ⟶ Y；g : Y ⟶ Z；U : Z.Opens；(AlgebraicGeometry.Scheme.Modules.pushforward
Comp f g).inv.app M；((AlgebraicGeometry.Scheme.Modules.pushforward (CategoryTheo
ry.CategoryStruct.comp f g)).obj M).presheaf.obj         (Opposite.op U)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma pushforwardComp_inv_app_app (U) : ((pushforwardComp f g).inv.app M).app U = 𝟙 _ := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The composition of two pullback functors for sheaves of modules on schemes
identify to the pullback for the composition. -/
/-
**AlgebraicGeometry.Scheme.Modules.pullbackComp** 是 Mathlib 中的一个定义，位于命名空间 `Algeb
raicGeometry.Scheme.Modules`。
形式化陈述：pullbackComp : pullback g ⋙ pullback f ≅ pullback (f ≫ g)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of two pullback functors for sheaves of modules on schemes
identify to the pullback for the composition.
-/
def pullbackComp :
    pullback g ⋙ pullback f ≅ pullback (f ≫ g) :=
  SheafOfModules.pullbackComp _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- Pushforwards along equal morphisms are isomorphic. -/
/-
**AlgebraicGeometry.Scheme.Modules.pushforwardCongr** 是 Mathlib 中的一个定义，位于命名空间 `A
lgebraicGeometry.Scheme.Modules`。
形式化陈述：pushforwardCongr {f g : X ⟶ Y} (hf : f = g) : pushforward f ≅ pushforward 
g
参数：hf : f = g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pushforwards along equal morphisms are isomorphic.
-/
def pushforwardCongr {f g : X ⟶ Y} (hf : f = g) : pushforward f ≅ pushforward g :=
    pushforwardNatIso _ (Opens.mapIso _ _ (hf ▸ rfl)) ≪≫
      SheafOfModules.pushforwardCongr (by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.Modules.pushforwardCongr_hom_app_app** 是 Mathlib 中的一个
定理，位于命名空间 `AlgebraicGeometry.Scheme.Modules`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} {M : X.Modules} {f g : X ⟶ Y} (hf : f =
 g) (U : Y.Opens),   AlgebraicGeometry.Scheme.Modules.Hom.app ((AlgebraicGeometr
y.Scheme.Modules.pushforwardCongr hf).hom.app M) U =     M.presheaf.map (Categor
yTheory.eqToHom ⋯).op
参数：hf : f = g；U : Y.Opens；(AlgebraicGeometry.Scheme.Modules.pushforwardCongr hf)
.hom.app M；CategoryTheory.eqToHom ⋯。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma pushforwardCongr_hom_app_app {f g : X ⟶ Y} (hf : f = g) (U : Y.Opens) :
    ((pushforwardCongr hf).hom.app M).app U = M.presheaf.map (eqToHom (hf ▸ rfl)).op := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.Modules.pushforwardCongr_inv_app_app** 是 Mathlib 中的一个
定理，位于命名空间 `AlgebraicGeometry.Scheme.Modules`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} {M : X.Modules} {f g : X ⟶ Y} (hf : f =
 g) (U : Y.Opens),   AlgebraicGeometry.Scheme.Modules.Hom.app ((AlgebraicGeometr
y.Scheme.Modules.pushforwardCongr hf).inv.app M) U =     M.presheaf.map (Categor
yTheory.eqToHom ⋯).op
参数：hf : f = g；U : Y.Opens；(AlgebraicGeometry.Scheme.Modules.pushforwardCongr hf)
.inv.app M；CategoryTheory.eqToHom ⋯。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma pushforwardCongr_inv_app_app {f g : X ⟶ Y} (hf : f = g) (U : Y.Opens) :
    ((pushforwardCongr hf).inv.app M).app U = M.presheaf.map (eqToHom (hf ▸ rfl)).op := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Inverse images along equal morphisms are isomorphic. -/
/-
**AlgebraicGeometry.Scheme.Modules.pullbackCongr** 是 Mathlib 中的一个定义，位于命名空间 `Alge
braicGeometry.Scheme.Modules`。
形式化陈述：pullbackCongr {f g : X ⟶ Y} (hf : f = g) : pullback f ≅ pullback g
参数：hf : f = g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Inverse images along equal morphisms are isomorphic.
-/
def pullbackCongr {f g : X ⟶ Y} (hf : f = g) : pullback f ≅ pullback g :=
  eqToIso (hf ▸ rfl)

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackComp_inv** 是 Mathlib 中
的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.Modules`。
形式化陈述：conjugateEquiv_pullbackComp_inv : conjugateEquiv ((pullbackPushforwardAdju
nction g).comp (pullbackPushforwardAdjunction f)) (pullbackPushforwardAdjunction
 (f ≫ g)) (pullbackComp f g).inv = (pushforwardComp f g).hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SheafOfModules.conjugateEquiv_pullbackComp_inv`：conjugateEquiv_pullbackC
omp_inv : conjugateEquiv ((pullbackPushforwardAdjunction.{v} φ).comp (pullbackPu
shforwardAdjunction.{v} ψ)) (pullbac…
-/
lemma conjugateEquiv_pullbackComp_inv :
    conjugateEquiv ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
      (pullbackPushforwardAdjunction (f ≫ g)) (pullbackComp f g).inv =
    (pushforwardComp f g).hom :=
  SheafOfModules.conjugateEquiv_pullbackComp_inv _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**AlgebraicGeometry.Scheme.Modules.pseudofunctor_associativity** 是 Mathlib 中的一个引
理，位于命名空间 `AlgebraicGeometry.Scheme.Modules`。
形式化陈述：pseudofunctor_associativity : (pullbackComp f (g ≫ h)).inv ≫ Functor.whisk
erRight (pullbackComp g h).inv _ ≫ (Functor.associator _ _ _).hom ≫ Functor.whis
kerLeft _ (pullbackComp f g).hom ≫ (pullbackComp (f ≫ g) h).hom = eqToHom (by si
mp)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `instIsContinuousOpensCarrierMapGrothendieckTopology`：∀ {X Y : TopCat} (f
 : X ⟶ Y),   (TopologicalSpace.Opens.map f).IsContinuous (Opens.grothendieckTopo
logy ↑Y) (Opens.grothendieckTopology ↑X)
· 使用定理 `SheafOfModules.instIsRightAdjointPushforward`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   {J : CategoryTheor…
· 使用定理 `PresheafOfModules.instIsRightAdjointPushforward`：∀ {C D : Type u} [inst 
: CategoryTheory.SmallCategory C] [inst_1 : CategoryTheory.SmallCategory D]   {F
 : CategoryTheory.Functor C D} {R : C…
· 使用定理 `CategoryTheory.instHasWeakSheafifyOfHasSheafify`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C)
 (A : Type u₂)   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.instHasSheafifyOfPreservesLimitsForgetOfHasFiniteLimitsOf
SmallOppositeCover`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J 
: CategoryTheory.GrothendieckTopology C) (D : Type w)   [inst_1 : CategoryTheory
…
· 使用定理 `AddCommGrpCat.hasLimit`：∀ {J : Type v} [inst : CategoryTheory.Category.{
w, v} J] (F : CategoryTheory.Functor J AddCommGrpCat)   [Small.{u, max u v} ↑(F.
comp (Catego…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `AddCommGrpCat.hasColimitsOfShape`：∀ {J : Type u} [inst : CategoryTheory.
Category.{v, u} J] [Small.{w, u} J],   CategoryTheory.Limits.HasColimitsOfShape 
J AddCommGrpCat
· 使用定理 `CategoryTheory.Limits.PreservesFilteredColimitsOfSize.preserves_filtered
_colimits`：∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type
 u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits`：Categor
yTheory.Limits.PreservesFilteredColimits (CategoryTheory.forget AddCommGrpCat)
· 使用定理 `CategoryTheory.isCofiltered_of_directed_ge_nonempty`：∀ (α : Type u) [ins
t : Preorder α] [IsCodirectedOrder α] [Nonempty α], CategoryTheory.IsCofiltered 
α
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `AddCommGrpCat.forget_reflects_isos`：(CategoryTheory.forget AddCommGrpCat
).ReflectsIsomorphisms
· 使用定理 `AddCommGrpCat.forget_preservesLimitsOfShape`：∀ {J : Type v} [inst : Cate
goryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.Preserve
sLimitsOfShape J (CategoryTheory.…
· 使用定理 `AddCommGrpCat.forget_preservesLimits`：CategoryTheory.Limits.PreservesLim
its (CategoryTheory.forget AddCommGrpCat)
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `AddCommGrpCat.hasLimits`：CategoryTheory.Limits.HasLimits AddCommGrpCat
· 使用定理 `CategoryTheory.GrothendieckTopology.instWEqualsLocallyBijectiveOfHasWeak
SheafifyOfHasSheafComposeOfPreservesSheafificationOfReflectsIsomorphismsForget`：
∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Gro
thendieckTopology C) {D : Type w}   [inst_1 : CategoryTheory…
· 使用定理 `CategoryTheory.hasSheafCompose_of_preservesMulticospan`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} A]   {B : Type u₃} [ins…
· 使用定理 `CategoryTheory.preservesLimit_of_createsLimit_and_hasLimit`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.GrothendieckTopology.instPreservesSheafificationForgetOfP
reservesLimitsOfHasColimitsOfShapeOfPreservesColimitsOfShapeOppositeCoverOfHasLi
mitsOfShapeWalkingMulticospanOfReflectsIsomorphisms`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] (J : CategoryTheory.GrothendieckTopology C) {D : T
ype u_3}   [inst_1 : CategoryTheo…
· 使用定理 `AddCommGrpCat.hasLimitsOfShape`：∀ {J : Type v} [inst : CategoryTheory.Ca
tegory.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasLimitsOfShape J Ad
dCommGrpCat
· 使用定理 `TopologicalSpace.Opens.instIsContinuousCompGrothendieckTopology`：∀ {X : 
Type u_1} {Y : Type u_2} {Z : Type u_3} [inst : TopologicalSpace X] [inst_1 : To
pologicalSpace Y]   [inst_2 : TopologicalSpace Z] (F …
· 使用定理 `SheafOfModules.instIsRightAdjointPushforwardCompSheafRingCatMapSheafPush
forwardContinuous`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {
D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {D' : Type u₃} [in…
· 使用引理 `SheafOfModules.pullback_assoc`：pullback_assoc : isoWhiskerLeft _ (pullba
ckComp.{v} ψ ψ') ≪≫ pullbackComp.{v} (G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 35 条，此处仅展示前 30 条）
-/
lemma pseudofunctor_associativity :
    (pullbackComp f (g ≫ h)).inv ≫
      Functor.whiskerRight (pullbackComp g h).inv _ ≫ (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft _ (pullbackComp f g).hom ≫ (pullbackComp (f ≫ g) h).hom =
    eqToHom (by simp) := by
  let e₁ := pullbackComp f (g ≫ h)
  let e₂ := Functor.isoWhiskerRight (pullbackComp g h) (pullback f)
  let e₃ := Functor.isoWhiskerLeft (pullback h) (pullbackComp f g)
  let e₄ := pullbackComp (f ≫ g) h
  change e₁.inv ≫ e₂.inv ≫ (Functor.associator _ _ _).hom ≫ e₃.hom ≫ e₄.hom = _
  have : e₃.hom ≫ e₄.hom = (Functor.associator _ _ _).inv ≫ e₂.hom ≫ e₁.hom :=
    congr_arg Iso.hom (SheafOfModules.pullback_assoc.{u}
      h.toRingCatSheafHom g.toRingCatSheafHom f.toRingCatSheafHom)
  simp [this]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**AlgebraicGeometry.Scheme.Modules.pseudofunctor_left_unitality** 是 Mathlib 中的一个
引理，位于命名空间 `AlgebraicGeometry.Scheme.Modules`。
形式化陈述：pseudofunctor_left_unitality : (pullbackComp f (𝟙 Y)).inv ≫ Functor.whiske
rRight (pullbackId Y).hom (pullback f) ≫ (Functor.leftUnitor _).hom = eqToHom (b
y simp)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `SheafOfModules.instIsRightAdjointPushforwardIdSheafRingCat`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.Grothendieck
Topology C}   {S : CategoryTheory.Sheaf J RingCa…
· 使用定理 `instIsContinuousOpensCarrierMapGrothendieckTopology`：∀ {X Y : TopCat} (f
 : X ⟶ Y),   (TopologicalSpace.Opens.map f).IsContinuous (Opens.grothendieckTopo
logy ↑Y) (Opens.grothendieckTopology ↑X)
· 使用定理 `SheafOfModules.instIsRightAdjointPushforward`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   {J : CategoryTheor…
· 使用定理 `PresheafOfModules.instIsRightAdjointPushforward`：∀ {C D : Type u} [inst 
: CategoryTheory.SmallCategory C] [inst_1 : CategoryTheory.SmallCategory D]   {F
 : CategoryTheory.Functor C D} {R : C…
· 使用定理 `CategoryTheory.instHasWeakSheafifyOfHasSheafify`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C)
 (A : Type u₂)   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.instHasSheafifyOfPreservesLimitsForgetOfHasFiniteLimitsOf
SmallOppositeCover`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J 
: CategoryTheory.GrothendieckTopology C) (D : Type w)   [inst_1 : CategoryTheory
…
· 使用定理 `AddCommGrpCat.hasLimit`：∀ {J : Type v} [inst : CategoryTheory.Category.{
w, v} J] (F : CategoryTheory.Functor J AddCommGrpCat)   [Small.{u, max u v} ↑(F.
comp (Catego…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `AddCommGrpCat.hasColimitsOfShape`：∀ {J : Type u} [inst : CategoryTheory.
Category.{v, u} J] [Small.{w, u} J],   CategoryTheory.Limits.HasColimitsOfShape 
J AddCommGrpCat
· 使用定理 `CategoryTheory.Limits.PreservesFilteredColimitsOfSize.preserves_filtered
_colimits`：∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type
 u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits`：Categor
yTheory.Limits.PreservesFilteredColimits (CategoryTheory.forget AddCommGrpCat)
· 使用定理 `CategoryTheory.isCofiltered_of_directed_ge_nonempty`：∀ (α : Type u) [ins
t : Preorder α] [IsCodirectedOrder α] [Nonempty α], CategoryTheory.IsCofiltered 
α
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `AddCommGrpCat.forget_reflects_isos`：(CategoryTheory.forget AddCommGrpCat
).ReflectsIsomorphisms
· 使用定理 `AddCommGrpCat.forget_preservesLimitsOfShape`：∀ {J : Type v} [inst : Cate
goryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.Preserve
sLimitsOfShape J (CategoryTheory.…
· 使用定理 `AddCommGrpCat.forget_preservesLimits`：CategoryTheory.Limits.PreservesLim
its (CategoryTheory.forget AddCommGrpCat)
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `AddCommGrpCat.hasLimits`：CategoryTheory.Limits.HasLimits AddCommGrpCat
· 使用定理 `CategoryTheory.GrothendieckTopology.instWEqualsLocallyBijectiveOfHasWeak
SheafifyOfHasSheafComposeOfPreservesSheafificationOfReflectsIsomorphismsForget`：
∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Gro
thendieckTopology C) {D : Type w}   [inst_1 : CategoryTheory…
· 使用定理 `CategoryTheory.hasSheafCompose_of_preservesMulticospan`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} A]   {B : Type u₃} [ins…
· 使用定理 `CategoryTheory.preservesLimit_of_createsLimit_and_hasLimit`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.GrothendieckTopology.instPreservesSheafificationForgetOfP
reservesLimitsOfHasColimitsOfShapeOfPreservesColimitsOfShapeOppositeCoverOfHasLi
mitsOfShapeWalkingMulticospanOfReflectsIsomorphisms`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] (J : CategoryTheory.GrothendieckTopology C) {D : T
ype u_3}   [inst_1 : CategoryTheo…
· 使用定理 `AddCommGrpCat.hasLimitsOfShape`：∀ {J : Type v} [inst : CategoryTheory.Ca
tegory.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasLimitsOfShape J Ad
dCommGrpCat
· 使用定理 `CategoryTheory.Functor.instIsContinuousCompId_1`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `SheafOfModules.instIsRightAdjointPushforwardCompSheafRingCatMapSheafPush
forwardContinuous`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {
D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {D' : Type u₃} [in…
· 使用引理 `SheafOfModules.pullback_id_comp`：pullback_id_comp : pullbackComp.{v} (F
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 35 条，此处仅展示前 30 条）
-/
lemma pseudofunctor_left_unitality :
    (pullbackComp f (𝟙 Y)).inv ≫
      Functor.whiskerRight (pullbackId Y).hom (pullback f) ≫ (Functor.leftUnitor _).hom =
        eqToHom (by simp) := by
  let e₁ := pullbackComp f (𝟙 _)
  let e₂ := Functor.isoWhiskerRight (pullbackId Y) (pullback f)
  let e₃ := (pullback f).leftUnitor
  change e₁.inv ≫ e₂.hom ≫ e₃.hom = _
  have : e₁.hom = e₂.hom ≫ e₃.hom :=
    congr_arg Iso.hom (SheafOfModules.pullback_id_comp.{u} f.toRingCatSheafHom)
  simp [← this]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**AlgebraicGeometry.Scheme.Modules.pseudofunctor_right_unitality** 是 Mathlib 中的一
个引理，位于命名空间 `AlgebraicGeometry.Scheme.Modules`。
形式化陈述：pseudofunctor_right_unitality : (pullbackComp (𝟙 X) f).inv ≫ Functor.whisk
erLeft (pullback f) (pullbackId X).hom ≫ (Functor.rightUnitor _).hom = eqToHom (
by simp)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `instIsContinuousOpensCarrierMapGrothendieckTopology`：∀ {X Y : TopCat} (f
 : X ⟶ Y),   (TopologicalSpace.Opens.map f).IsContinuous (Opens.grothendieckTopo
logy ↑Y) (Opens.grothendieckTopology ↑X)
· 使用定理 `SheafOfModules.instIsRightAdjointPushforward`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   {J : CategoryTheor…
· 使用定理 `PresheafOfModules.instIsRightAdjointPushforward`：∀ {C D : Type u} [inst 
: CategoryTheory.SmallCategory C] [inst_1 : CategoryTheory.SmallCategory D]   {F
 : CategoryTheory.Functor C D} {R : C…
· 使用定理 `CategoryTheory.instHasWeakSheafifyOfHasSheafify`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C)
 (A : Type u₂)   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.instHasSheafifyOfPreservesLimitsForgetOfHasFiniteLimitsOf
SmallOppositeCover`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J 
: CategoryTheory.GrothendieckTopology C) (D : Type w)   [inst_1 : CategoryTheory
…
· 使用定理 `AddCommGrpCat.hasLimit`：∀ {J : Type v} [inst : CategoryTheory.Category.{
w, v} J] (F : CategoryTheory.Functor J AddCommGrpCat)   [Small.{u, max u v} ↑(F.
comp (Catego…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `AddCommGrpCat.hasColimitsOfShape`：∀ {J : Type u} [inst : CategoryTheory.
Category.{v, u} J] [Small.{w, u} J],   CategoryTheory.Limits.HasColimitsOfShape 
J AddCommGrpCat
· 使用定理 `CategoryTheory.Limits.PreservesFilteredColimitsOfSize.preserves_filtered
_colimits`：∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type
 u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits`：Categor
yTheory.Limits.PreservesFilteredColimits (CategoryTheory.forget AddCommGrpCat)
· 使用定理 `CategoryTheory.isCofiltered_of_directed_ge_nonempty`：∀ (α : Type u) [ins
t : Preorder α] [IsCodirectedOrder α] [Nonempty α], CategoryTheory.IsCofiltered 
α
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `AddCommGrpCat.forget_reflects_isos`：(CategoryTheory.forget AddCommGrpCat
).ReflectsIsomorphisms
· 使用定理 `AddCommGrpCat.forget_preservesLimitsOfShape`：∀ {J : Type v} [inst : Cate
goryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.Preserve
sLimitsOfShape J (CategoryTheory.…
· 使用定理 `AddCommGrpCat.forget_preservesLimits`：CategoryTheory.Limits.PreservesLim
its (CategoryTheory.forget AddCommGrpCat)
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `AddCommGrpCat.hasLimits`：CategoryTheory.Limits.HasLimits AddCommGrpCat
· 使用定理 `CategoryTheory.GrothendieckTopology.instWEqualsLocallyBijectiveOfHasWeak
SheafifyOfHasSheafComposeOfPreservesSheafificationOfReflectsIsomorphismsForget`：
∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Gro
thendieckTopology C) {D : Type w}   [inst_1 : CategoryTheory…
· 使用定理 `CategoryTheory.hasSheafCompose_of_preservesMulticospan`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} A]   {B : Type u₃} [ins…
· 使用定理 `CategoryTheory.preservesLimit_of_createsLimit_and_hasLimit`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.GrothendieckTopology.instPreservesSheafificationForgetOfP
reservesLimitsOfHasColimitsOfShapeOfPreservesColimitsOfShapeOppositeCoverOfHasLi
mitsOfShapeWalkingMulticospanOfReflectsIsomorphisms`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] (J : CategoryTheory.GrothendieckTopology C) {D : T
ype u_3}   [inst_1 : CategoryTheo…
· 使用定理 `AddCommGrpCat.hasLimitsOfShape`：∀ {J : Type v} [inst : CategoryTheory.Ca
tegory.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasLimitsOfShape J Ad
dCommGrpCat
· 使用定理 `SheafOfModules.instIsRightAdjointPushforwardIdSheafRingCat`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.Grothendieck
Topology C}   {S : CategoryTheory.Sheaf J RingCa…
· 使用定理 `CategoryTheory.Functor.instIsContinuousCompId`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `SheafOfModules.instIsRightAdjointPushforwardCompSheafRingCatMapSheafPush
forwardContinuous`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {
D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {D' : Type u₃} [in…
· 使用引理 `SheafOfModules.pullback_comp_id`：pullback_comp_id : pullbackComp.{v} (G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 35 条，此处仅展示前 30 条）
-/
lemma pseudofunctor_right_unitality :
    (pullbackComp (𝟙 X) f).inv ≫
      Functor.whiskerLeft (pullback f) (pullbackId X).hom ≫ (Functor.rightUnitor _).hom =
        eqToHom (by simp) := by
  let e₁ := pullbackComp (𝟙 _) f
  let e₂ := Functor.isoWhiskerLeft (pullback f) (pullbackId _)
  let e₃ := (pullback f).rightUnitor
  change e₁.inv ≫ e₂.hom ≫ e₃.hom = _
  have : e₁.hom = e₂.hom ≫ e₃.hom :=
    congr_arg Iso.hom (SheafOfModules.pullback_comp_id.{u} f.toRingCatSheafHom)
  simp [← this]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
attribute [local simp] pseudofunctor_associativity pseudofunctor_left_unitality
  pseudofunctor_right_unitality Bicategory.toNatTrans_conjugateEquiv
  conjugateEquiv_pullbackId_hom Adjunction.ofCat_comp conjugateEquiv_pullbackComp_inv in
/-- The pseudofunctor from `Schemeᵒᵖ` to the bicategory of adjunctions which sends
a scheme `X` to the category `X.Modules` of sheaves of modules over `X`.
(This contains both the covariant and the contravariant functorialities of
these categories.) -/
@[simps! obj_obj map_l map_r map_adj
  mapId_hom_τl mapId_hom_τr mapId_inv_τl mapId_inv_τr
  mapComp_hom_τl mapComp_hom_τr mapComp_inv_τl mapComp_inv_τr]
/-
**AlgebraicGeometry.Scheme.Modules.pseudofunctor** 是 Mathlib 中的一个定义，位于命名空间 `Alge
braicGeometry.Scheme.Modules`。
形式化陈述：pseudofunctor : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Adj Cat)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def pseudofunctor :
    Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Adj Cat) :=
  LocallyDiscrete.mkPseudofunctor
    (fun X ↦ Adj.mk (Cat.of X.unop.Modules))
    (fun f ↦ .mk (pullbackPushforwardAdjunction f.unop).toCat)
    (fun _ ↦ Adj.iso₂Mk (Cat.Hom.isoMk (pullbackId _))
        (Cat.Hom.isoMk (pushforwardId _).symm))
    (fun _ _ ↦ Adj.iso₂Mk (Cat.Hom.isoMk (pullbackComp _ _).symm)
        (Cat.Hom.isoMk (pushforwardComp _ _)))

end Functorial

noncomputable section Restriction

variable (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g]

set_option backward.defeqAttrib.useBackward true in
/-- Restriction of an `𝒪ₓ`-module along an open immersion.
This is isomorphic to the pullback functor (see `restrictFunctorIsoPullback`)
but has better defeqs. -/
/-
**AlgebraicGeometry.Scheme.Modules.restrictFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Al
gebraicGeometry.Scheme.Modules`。
形式化陈述：restrictFunctor : Y.Modules ⥤ X.Modules
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Hom.instIsContinuousOpensOpensFunctorGrothendie
ckTopologyCarrierCarrierCommRingCat`：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶
 Y) [H : AlgebraicGeometry.IsOpenImmersion f],   (AlgebraicGeometry.Scheme.Hom.o
pensFunctor f).Is…

--- 原说明 ---
Restriction of an `𝒪ₓ`-module along an open immersion.
This is isomorphic to the pullback functor (see `restrictFunctorIsoPullback`)
but has better defeqs.
-/
def restrictFunctor : Y.Modules ⥤ X.Modules :=
  letI α : X.presheaf ⟶ f.opensFunctor.op ⋙ Y.presheaf := { app U := (f.appIso U.unop).inv }
  SheafOfModules.pushforward (F := f.opensFunctor)
    ⟨Functor.whiskerRight α (forget₂ CommRingCat RingCat)⟩

/-- The restriction of a module along an open immersion. -/
/-
**AlgebraicGeometry.Scheme.Modules.restrict** 是 Mathlib 中的一个缩写定义，位于命名空间 `Algebra
icGeometry.Scheme.Modules`。
形式化陈述：restrict (M : Y.Modules) (f : X ⟶ Y) [IsOpenImmersion f] : X.Modules
参数：M : Y.Modules；f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of a module along an open immersion.
-/
abbrev restrict (M : Y.Modules) (f : X ⟶ Y) [IsOpenImmersion f] : X.Modules :=
  (restrictFunctor f).obj M

/-- The sections of the restriction of `M` over `U` are isomorphic to `Γ(M, f ''ᵁ U). -/
/-
**AlgebraicGeometry.Scheme.Modules.restrictAppIso** 是 Mathlib 中的一个定义，位于命名空间 `Alg
ebraicGeometry.Scheme.Modules`。
形式化陈述：restrictAppIso (M : Y.Modules) (U : X.Opens) : Γ(M.restrict f, U) ≅ Γ(M, f
 ''ᵁ U)
参数：M : Y.Modules；U : X.Opens。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sections of the restriction of `M` over `U` are isomorphic to `Γ(M, f ''ᵁ U)
.
-/
def restrictAppIso (M : Y.Modules) (U : X.Opens) : Γ(M.restrict f, U) ≅ Γ(M, f ''ᵁ U) :=
  Iso.refl _

@[elementwise (attr := simp), reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Modules.smul_restrictAppIso_hom** 是 Mathlib 中的一个引理，位于
命名空间 `AlgebraicGeometry.Scheme.Modules`。
形式化陈述：smul_restrictAppIso_hom (M : Y.Modules) (U : X.Opens) (r : Γ(X, U)) : dsim
p% (M.restrict f).smul r ≫ (M.restrictAppIso f U).hom = (M.restrictAppIso f U).h
om ≫ M.smul ((f.appIso U).inv r)
参数：M : Y.Modules；U : X.Opens；r : Γ(X, U)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smul_restrictAppIso_hom (M : Y.Modules) (U : X.Opens) (r : Γ(X, U)) :
    dsimp% (M.restrict f).smul r ≫ (M.restrictAppIso f U).hom =
      (M.restrictAppIso f U).hom ≫ M.smul ((f.appIso U).inv r) :=
  rfl

@[elementwise (attr := simp), reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Modules.smul_restrictAppIso_inv** 是 Mathlib 中的一个引理，位于
命名空间 `AlgebraicGeometry.Scheme.Modules`。
形式化陈述：smul_restrictAppIso_inv (M : Y.Modules) (U : X.Opens) (r : Γ(Y, f ''ᵁ U)) 
: M.smul r ≫ (M.restrictAppIso f U).inv = (M.restrictAppIso f U).inv ≫ (M.restri
ct f).smul ((f.appIso U).hom r)
参数：M : Y.Modules；U : X.Opens；r : Γ(Y, f ''ᵁ U)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_apply`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {F : C → C → Type uF}   {carrier 
: C → Type w} {instFunLik…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma smul_restrictAppIso_inv (M : Y.Modules) (U : X.Opens) (r : Γ(Y, f ''ᵁ U)) :
    M.smul r ≫ (M.restrictAppIso f U).inv =
      (M.restrictAppIso f U).inv ≫ (M.restrict f).smul ((f.appIso U).hom r) := by
  simp [← cancel_mono (M.restrictAppIso f U).hom]

@[elementwise (attr := simp), reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Modules.map_restrictAppIso_hom** 是 Mathlib 中的一个引理，位于命
名空间 `AlgebraicGeometry.Scheme.Modules`。
形式化陈述：map_restrictAppIso_hom (M : Y.Modules) {U V : X.Opens} (hUV : Opposite.op 
V ⟶ .op U) : (M.restrict f).presheaf.map hUV ≫ (M.restrictAppIso f U).hom = (M.r
estrictAppIso f V).hom ≫ M.presheaf.map (.op <| homOfLE <| Scheme.Hom.image_mono
 _ (leOfHom hUV.unop))
参数：M : Y.Modules；hUV : Opposite.op V ⟶ .op U。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_restrictAppIso_hom (M : Y.Modules) {U V : X.Opens}
    (hUV : Opposite.op V ⟶ .op U) :
    (M.restrict f).presheaf.map hUV ≫ (M.restrictAppIso f U).hom =
      (M.restrictAppIso f V).hom ≫
      M.presheaf.map (.op <| homOfLE <| Scheme.Hom.image_mono _ (leOfHom hUV.unop)) := by
  rfl

@[elementwise (attr := simp), reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Modules.restrictAppIso_inv_map** 是 Mathlib 中的一个引理，位于命
名空间 `AlgebraicGeometry.Scheme.Modules`。
形式化陈述：restrictAppIso_inv_map (M : Y.Modules) {U V : X.Opens} (hUV : .op V ⟶ .op 
U) : (M.restrictAppIso f V).inv ≫ (M.restrict f).presheaf.map hUV = M.presheaf.m
ap (.op <| homOfLE <| Scheme.Hom.image_mono _ (leOfHom hUV.unop)) ≫ (M.restrictA
ppIso f U).inv
参数：M : Y.Modules；hUV : .op V ⟶ .op U。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrictAppIso_inv_map (M : Y.Modules) {U V : X.Opens} (hUV : .op V ⟶ .op U) :
    (M.restrictAppIso f V).inv ≫ (M.restrict f).presheaf.map hUV =
      M.presheaf.map (.op <| homOfLE <| Scheme.Hom.image_mono _ (leOfHom hUV.unop)) ≫
      (M.restrictAppIso f U).inv :=
  rfl

/-- Avoid using this. Use the isomorphism `AlgebraicGeometry.Scheme.Modules.restrictAppIso`
instead. -/
/-
**AlgebraicGeometry.Scheme.Modules.restrict_obj** 是 Mathlib 中的一个引理，位于命名空间 `Algeb
raicGeometry.Scheme.Modules`。
形式化陈述：restrict_obj (M : Y.Modules) (f : X ⟶ Y) [IsOpenImmersion f] (U) : Γ(M.res
trict f, U) = Γ(M, f ''ᵁ U)
参数：M : Y.Modules；f : X ⟶ Y；U。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Avoid using this. Use the isomorphism `AlgebraicGeometry.Scheme.Modules.restrict
AppIso`
instead.
-/
lemma restrict_obj (M : Y.Modules) (f : X ⟶ Y) [IsOpenImmersion f] (U) :
    Γ(M.restrict f, U) = Γ(M, f ''ᵁ U) := rfl

/-- Avoid using this. Use the isomorphism `AlgebraicGeometry.Scheme.Modules.restrictAppIso`
instead. -/
/-
**AlgebraicGeometry.Scheme.Modules.restrict_map** 是 Mathlib 中的一个引理，位于命名空间 `Algeb
raicGeometry.Scheme.Modules`。
形式化陈述：restrict_map (M : Y.Modules) (f : X ⟶ Y) [IsOpenImmersion f] {U V} (i : U 
⟶ V) : (M.restrict f).presheaf.map i.op = M.presheaf.map (f.opensFunctor.map i).
op
参数：M : Y.Modules；f : X ⟶ Y；i : U ⟶ V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Avoid using this. Use the isomorphism `AlgebraicGeometry.Scheme.Modules.restrict
AppIso`
instead.
-/
lemma restrict_map (M : Y.Modules) (f : X ⟶ Y) [IsOpenImmersion f] {U V} (i : U ⟶ V) :
    (M.restrict f).presheaf.map i.op = M.presheaf.map (f.opensFunctor.map i).op := rfl

/-- `Scheme.Modules.restrict` along an open immersion `X ⟶ Y` sends `𝒪_Y` to `𝒪_X`. -/
/-
**AlgebraicGeometry.Scheme.Modules.restrictUnitIso** 是 Mathlib 中的一个定义，位于命名空间 `Al
gebraicGeometry.Scheme.Modules`。
形式化陈述：restrictUnitIso (f : X ⟶ Y) [IsOpenImmersion f] : restrict (.unit <| Y.rin
gCatSheaf) f ≅ .unit X.ringCatSheaf
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Scheme.Modules.restrict` along an open immersion `X ⟶ Y` sends `𝒪_Y` to `𝒪_X`.
-/
def restrictUnitIso (f : X ⟶ Y) [IsOpenImmersion f] :
    restrict (.unit <| Y.ringCatSheaf) f ≅ .unit X.ringCatSheaf := by
  refine (fullyFaithfulForget _).preimageIso <| PresheafOfModules.isoMk (fun U ↦ ?_) ?_
  · refine ModuleCat.isoMk
      ((forget₂ CommRingCat RingCat ⋙ forget₂ _ Ab).mapIso (f.appIso U.unop)) ?_
    intro (r : Γ(X, U.unop))
    ext (x : Γ(Y, f ''ᵁ U.unop))
    change r * (f.appIso U.unop).hom x = (f.appIso U.unop).hom ((f.appIso U.unop).inv r * x)
    simp
  · intro U V g
    have : Y.presheaf.map (homOfLE (by grw [leOfHom g.unop])).op ≫
        (f.appIso _).hom = (f.appIso U.unop).hom ≫ X.presheaf.map g := by
      simp [Hom.appIso_hom']
    ext x
    exact congr($(this) x)

/-- The restriction of a module along an open immersion. -/
/-
**AlgebraicGeometry.Scheme.Modules.restrictFunctorAdjCounitIso** 是 Mathlib 中的一个定
义，位于命名空间 `AlgebraicGeometry.Scheme.Modules`。
形式化陈述：restrictFunctorAdjCounitIso : pushforward f ⋙ restrictFunctor f ≅ 𝟭 _
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Hom.instIsContinuousOpensOpensFunctorGrothendie
ckTopologyCarrierCarrierCommRingCat`：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶
 Y) [H : AlgebraicGeometry.IsOpenImmersion f],   (AlgebraicGeometry.Scheme.Hom.o
pensFunctor f).Is…

--- 原说明 ---
The restriction of a module along an open immersion.
-/
def restrictFunctorAdjCounitIso : pushforward f ⋙ restrictFunctor f ≅ 𝟭 _ :=
  letI := CategoryTheory.Functor.isContinuous_comp.{u} f.opensFunctor (Opens.map f.base)
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
  (SheafOfModules.pushforwardComp _ _) ≪≫ pushforwardNatIso _ (NatIso.ofComponents
      (fun U ↦ eqToIso (f.preimage_image_eq U).symm) fun _ ↦ rfl) ≪≫
    SheafOfModules.pushforwardCongr (by ext U x; exact
      congr($(f.appIso_inv_app_presheafMap U.unop) x)) ≪≫ SheafOfModules.pushforwardId _

/-- Restriction is right adjoint to pushforward. -/
/-
**AlgebraicGeometry.Scheme.Modules.restrictAdjunction** 是 Mathlib 中的一个定义，位于命名空间 
`AlgebraicGeometry.Scheme.Modules`。
形式化陈述：restrictAdjunction : restrictFunctor f ⊣ pushforward f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Hom.instIsContinuousOpensOpensFunctorGrothendie
ckTopologyCarrierCarrierCommRingCat`：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶
 Y) [H : AlgebraicGeometry.IsOpenImmersion f],   (AlgebraicGeometry.Scheme.Hom.o
pensFunctor f).Is…

--- 原说明 ---
Restriction is right adjoint to pushforward.
-/
def restrictAdjunction : restrictFunctor f ⊣ pushforward f := by
  refine pushforwardPushforwardAdj (by exact f.isOpenEmbedding.isOpenMap.adjunction) _ _ ?_ ?_
  · ext U x; exact congr($((f.app_appIso_inv _).symm).hom x)
  · ext U x
    have : (f.appIso U.unop).inv ≫ f.app _ ≫
      X.presheaf.map (eqToHom (f.preimage_image_eq U.unop).symm).op = 𝟙 _ := by
      rw [Scheme.Hom.appIso_inv_app_assoc, ← Functor.map_comp, ← X.presheaf.map_id]; rfl
    exact congr($this x)
/-
**AlgebraicGeometry.Scheme.Modules.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry
.Scheme.Modules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (restrictAdjunction f).counit :=
  inferInstanceAs (IsIso <| (restrictFunctorAdjCounitIso f).hom)
/-
**AlgebraicGeometry.Scheme.Modules.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry
.Scheme.Modules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (restrictFunctor f).IsLeftAdjoint := (restrictAdjunction f).isLeftAdjoint
/-
**AlgebraicGeometry.Scheme.Modules.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry
.Scheme.Modules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (pushforward f).Full := (restrictAdjunction f).fullyFaithfulROfIsIsoCounit.full
/-
**AlgebraicGeometry.Scheme.Modules.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry
.Scheme.Modules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (pushforward f).Faithful := (restrictAdjunction f).fullyFaithfulROfIsIsoCounit.faithful

@[simp]
/-
**AlgebraicGeometry.Scheme.Modules.restrictAdjunction_unit_app_app** 是 Mathlib 中
的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.Modules`。
形式化陈述：restrictAdjunction_unit_app_app (M : Y.Modules) (U : Y.Opens) : ((restrict
Adjunction f).unit.app M).app U = M.presheaf.map (homOfLE (f.image_preimage_le U
)).op
参数：M : Y.Modules；U : Y.Opens。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrictAdjunction_unit_app_app (M : Y.Modules) (U : Y.Opens) :
    ((restrictAdjunction f).unit.app M).app U =
      M.presheaf.map (homOfLE (f.image_preimage_le U)).op := rfl

@[simp]
/-
**AlgebraicGeometry.Scheme.Modules.restrictAdjunction_counit_app_app** 是 Mathlib
 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.Modules`。
形式化陈述：restrictAdjunction_counit_app_app (M : X.Modules) (U : X.Opens) : ((restri
ctAdjunction f).counit.app M).app U = M.presheaf.map (eqToHom (f.preimage_image_
eq U).symm).op
参数：M : X.Modules；U : X.Opens。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrictAdjunction_counit_app_app (M : X.Modules) (U : X.Opens) :
    ((restrictAdjunction f).counit.app M).app U =
      M.presheaf.map (eqToHom (f.preimage_image_eq U).symm).op := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction is naturally isomorphic to the inverse image. -/
/-
**AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback** 是 Mathlib 中的一个定义
，位于命名空间 `AlgebraicGeometry.Scheme.Modules`。
形式化陈述：restrictFunctorIsoPullback : restrictFunctor f ≅ pullback f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restriction is naturally isomorphic to the inverse image.
-/
def restrictFunctorIsoPullback : restrictFunctor f ≅ pullback f :=
  (restrictAdjunction f).leftAdjointUniq (pullbackPushforwardAdjunction f)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Restriction along the identity is isomorphic to the identity. -/
/-
**AlgebraicGeometry.Scheme.Modules.restrictFunctorId** 是 Mathlib 中的一个定义，位于命名空间 `
AlgebraicGeometry.Scheme.Modules`。
形式化陈述：restrictFunctorId : restrictFunctor (𝟙 X) ≅ 𝟭 _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restriction along the identity is isomorphic to the identity.
-/
def restrictFunctorId : restrictFunctor (𝟙 X) ≅ 𝟭 _ :=
  SheafOfModules.pushforwardNatIso _ (NatIso.ofComponents (fun _ ↦ eqToIso (by simp))) ≪≫
    SheafOfModules.pushforwardCongr
      (by ext : 3; simp [← Functor.map_comp, SheafedSpace.sheaf]) ≪≫
    SheafOfModules.pushforwardId _

@[simp]
/-
**AlgebraicGeometry.Scheme.Modules.restrictFunctorId_hom_app_app** 是 Mathlib 中的一
个引理，位于命名空间 `AlgebraicGeometry.Scheme.Modules`。
形式化陈述：restrictFunctorId_hom_app_app : (restrictFunctorId.hom.app M).app U = M.pr
esheaf.map (eqToHom (show U = 𝟙 X ''ᵁ U by simp)).op
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
-/
lemma restrictFunctorId_hom_app_app :
    (restrictFunctorId.hom.app M).app U =
      M.presheaf.map (eqToHom (show U = 𝟙 X ''ᵁ U by simp)).op := rfl

@[simp]
/-
**AlgebraicGeometry.Scheme.Modules.restrictFunctorId_inv_app_app** 是 Mathlib 中的一
个引理，位于命名空间 `AlgebraicGeometry.Scheme.Modules`。
形式化陈述：restrictFunctorId_inv_app_app : (restrictFunctorId.inv.app M).app U = M.pr
esheaf.map (eqToHom (show 𝟙 X ''ᵁ U = U by simp)).op
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
-/
lemma restrictFunctorId_inv_app_app :
    (restrictFunctorId.inv.app M).app U =
      M.presheaf.map (eqToHom (show 𝟙 X ''ᵁ U = U by simp)).op := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Restriction along the composition is isomorphic to the composition of restrictions. -/
/-
**AlgebraicGeometry.Scheme.Modules.restrictFunctorComp** 是 Mathlib 中的一个定义，位于命名空间
 `AlgebraicGeometry.Scheme.Modules`。
形式化陈述：restrictFunctorComp : restrictFunctor (f ≫ g) ≅ restrictFunctor g ⋙ restri
ctFunctor f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.comp`：∀ {X Y Z : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.IsOpenImmersion f]   [AlgebraicG
eometry.IsOpenImmersion g], …
· 使用定理 `AlgebraicGeometry.Scheme.Hom.instIsContinuousOpensOpensFunctorGrothendie
ckTopologyCarrierCarrierCommRingCat`：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶
 Y) [H : AlgebraicGeometry.IsOpenImmersion f],   (AlgebraicGeometry.Scheme.Hom.o
pensFunctor f).Is…

--- 原说明 ---
Restriction along the composition is isomorphic to the composition of restrictio
ns.
-/
def restrictFunctorComp : restrictFunctor (f ≫ g) ≅ restrictFunctor g ⋙ restrictFunctor f :=
  SheafOfModules.pushforwardNatIso _ (NatIso.ofComponents fun _ ↦ eqToIso (by simp)) ≪≫
    SheafOfModules.pushforwardCongr (by ext : 3; simp [← Functor.map_comp, SheafedSpace.sheaf]) ≪≫
    (SheafOfModules.pushforwardComp _ _).symm

@[simp]
/-
**AlgebraicGeometry.Scheme.Modules.restrictFunctorComp_hom_app_app** 是 Mathlib 中
的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.Modules`。
形式化陈述：restrictFunctorComp_hom_app_app (M : Z.Modules) : ((restrictFunctorComp f 
g).hom.app M).app U = M.presheaf.map (eqToHom (by simp)).op
参数：M : Z.Modules。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.comp`：∀ {X Y Z : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.IsOpenImmersion f]   [AlgebraicG
eometry.IsOpenImmersion g], …
-/
lemma restrictFunctorComp_hom_app_app (M : Z.Modules) :
    ((restrictFunctorComp f g).hom.app M).app U = M.presheaf.map (eqToHom (by simp)).op := rfl

@[simp]
/-
**AlgebraicGeometry.Scheme.Modules.restrictFunctorComp_inv_app_app** 是 Mathlib 中
的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.Modules`。
形式化陈述：restrictFunctorComp_inv_app_app (M : Z.Modules) : ((restrictFunctorComp f 
g).inv.app M).app U = M.presheaf.map (eqToHom (by simp)).op
参数：M : Z.Modules。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.comp`：∀ {X Y Z : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.IsOpenImmersion f]   [AlgebraicG
eometry.IsOpenImmersion g], …
-/
lemma restrictFunctorComp_inv_app_app (M : Z.Modules) :
    ((restrictFunctorComp f g).inv.app M).app U = M.presheaf.map (eqToHom (by simp)).op := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Restriction along equal morphisms are isomorphic. -/
/-
**AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr** 是 Mathlib 中的一个定义，位于命名空
间 `AlgebraicGeometry.Scheme.Modules`。
形式化陈述：restrictFunctorCongr {f g : X ⟶ Y} (hf : f = g) [IsOpenImmersion f] [IsOpe
nImmersion g] : restrictFunctor f ≅ restrictFunctor g
参数：hf : f = g。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Hom.instIsContinuousOpensOpensFunctorGrothendie
ckTopologyCarrierCarrierCommRingCat`：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶
 Y) [H : AlgebraicGeometry.IsOpenImmersion f],   (AlgebraicGeometry.Scheme.Hom.o
pensFunctor f).Is…

--- 原说明 ---
Restriction along equal morphisms are isomorphic.
-/
def restrictFunctorCongr {f g : X ⟶ Y} (hf : f = g) [IsOpenImmersion f] [IsOpenImmersion g] :
    restrictFunctor f ≅ restrictFunctor g :=
  SheafOfModules.pushforwardNatIso _ (NatIso.ofComponents fun _ ↦ eqToIso (by simp [hf])) ≪≫
    SheafOfModules.pushforwardCongr (by ext : 3; subst hf; simp)

@[simp]
/-
**AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr_hom_app_app** 是 Mathlib 
中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.Modules`。
形式化陈述：restrictFunctorCongr_hom_app_app {f g : X ⟶ Y} (hf : f = g) [IsOpenImmersi
on f] [IsOpenImmersion g] (M : Y.Modules) : ((restrictFunctorCongr hf).hom.app M
).app U = M.presheaf.map (eqToHom (by simp [hf])).op
参数：hf : f = g；M : Y.Modules。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrictFunctorCongr_hom_app_app {f g : X ⟶ Y} (hf : f = g) [IsOpenImmersion f]
    [IsOpenImmersion g] (M : Y.Modules) :
    ((restrictFunctorCongr hf).hom.app M).app U = M.presheaf.map (eqToHom (by simp [hf])).op := rfl

@[simp]
/-
**AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr_inv_app_app** 是 Mathlib 
中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.Modules`。
形式化陈述：restrictFunctorCongr_inv_app_app {f g : X ⟶ Y} (hf : f = g) [IsOpenImmersi
on f] [IsOpenImmersion g] (M : Y.Modules) : ((restrictFunctorCongr hf).inv.app M
).app U = M.presheaf.map (eqToHom (by simp [hf])).op
参数：hf : f = g；M : Y.Modules。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrictFunctorCongr_inv_app_app {f g : X ⟶ Y} (hf : f = g) [IsOpenImmersion f]
    [IsOpenImmersion g] (M : Y.Modules) :
    ((restrictFunctorCongr hf).inv.app M).app U = M.presheaf.map (eqToHom (by simp [hf])).op := rfl

/-- Restriction along open immersions commutes with taking stalks. -/
/-
**AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso** 是 Mathlib 中的一个定义，位于命名空间
 `AlgebraicGeometry.Scheme.Modules`。
形式化陈述：restrictStalkNatIso (x : X) : restrictFunctor f ⋙ toPresheaf _ ⋙ TopCat.Pr
esheaf.stalkFunctor _ x ≅ toPresheaf _ ⋙ TopCat.Presheaf.stalkFunctor _ (f x)
参数：x : X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isOpenEmbedding`：isOpenEmbedding : IsOpenEm
bedding f

--- 原说明 ---
Restriction along open immersions commutes with taking stalks.
-/
def restrictStalkNatIso (x : X) :
    restrictFunctor f ⋙ toPresheaf _ ⋙ TopCat.Presheaf.stalkFunctor _ x ≅
    toPresheaf _ ⋙ TopCat.Presheaf.stalkFunctor _ (f x) :=
  haveI := Functor.initial_of_adjunction (f.isOpenEmbedding.adjunctionNhds x)
  (toPresheaf _ ⋙ (Functor.whiskeringLeft (OpenNhds (f x))ᵒᵖ Y.Opensᵒᵖ Ab).obj
      (OpenNhds.inclusion (f x)).op).isoWhiskerLeft
      (Functor.Final.colimIso (f.isOpenEmbedding.functorNhds x).op)

@[simp]
/-
**AlgebraicGeometry.Scheme.Modules.germ_restrictStalkNatIso_hom_app** 是 Mathlib 
中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.Modules`。
形式化陈述：germ_restrictStalkNatIso_hom_app (x : X) (M : Y.Modules) (hxU : x in U) : 
((restrictFunctor f).obj M).presheaf.germ U _ hxU ≫ (restrictStalkNatIso f x).ho
m.app M = M.presheaf.germ _ _ (by simpa)
参数：x : X；M : Y.Modules；hxU : x in U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Final.ι_colimitIso_hom`：ι_colimitIso_hom [HasColi
mit G] (X : C) : colimit.ι (F ⋙ G) X ≫ (colimitIso F G).hom = colimit.ι G (F.obj
 X)
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isOpenEmbedding`：isOpenEmbedding : IsOpenEm
bedding f
· 使用定理 `CategoryTheory.Functor.initial_of_adjunction`：initial_of_adjunction {L :
 C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) : Initial L
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} {f :
 X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.Is
OpenEmbedding f → IsOpen…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
lemma germ_restrictStalkNatIso_hom_app (x : X) (M : Y.Modules) (hxU : x ∈ U) :
    ((restrictFunctor f).obj M).presheaf.germ U _ hxU ≫
      (restrictStalkNatIso f x).hom.app M = M.presheaf.germ _ _ (by simpa) :=
  haveI := Functor.initial_of_adjunction (f.isOpenEmbedding.adjunctionNhds x)
  Functor.Final.ι_colimitIso_hom
    (f.isOpenEmbedding.functorNhds x).op
    ((OpenNhds.inclusion ((ConcreteCategory.hom f.base) x)).op ⋙ M.presheaf) _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AlgebraicGeometry.Scheme.Modules.germ_restrictStalkNatIso_inv_app** 是 Mathlib 
中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.Modules`。
形式化陈述：germ_restrictStalkNatIso_inv_app (x : X) (M : Y.Modules) (hxU : x in U) : 
M.presheaf.germ _ _ (by simpa) ≫ (restrictStalkNatIso f x).inv.app M = ((restric
tFunctor f).obj M).presheaf.germ U _ hxU
参数：x : X；M : Y.Modules；hxU : x in U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGrpCat.hasColimitsOfSize`：∀ [UnivLE.{u, w}], CategoryTheory.Limit
s.HasColimitsOfSize.{v, u, w, w + 1} AddCommGrpCat
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.Modules.germ_restrictStalkNatIso_hom_app`：germ_
restrictStalkNatIso_hom_app (x : X) (M : Y.Modules) (hxU : x in U) : ((restrictF
unctor f).obj M).presheaf.germ U _ hxU ≫ (restrictStalk…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.NatTrans.comp_app`：comp_app {F G H : C ⥤ D} (α : F ⟶ G) (
β : G ⟶ H) (X : C) : (α ≫ β).app X = α.app X ≫ β.app X
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma germ_restrictStalkNatIso_inv_app (x : X) (M : Y.Modules) (hxU : x ∈ U) :
    M.presheaf.germ _ _ (by simpa) ≫ (restrictStalkNatIso f x).inv.app M =
      ((restrictFunctor f).obj M).presheaf.germ U _ hxU := by
  rw [← germ_restrictStalkNatIso_hom_app f x M hxU, Category.assoc, ← NatTrans.comp_app,
    Iso.hom_inv_id]
  simp

end Restriction

/-- `sheafCompose` commutes with `pushforward` -/
/-
**AlgebraicGeometry.Scheme.Modules.sheafComposePushforwardComp** 是 Mathlib 中的一个定
义，位于命名空间 `AlgebraicGeometry.Scheme.Modules`。
形式化陈述：sheafComposePushforwardComp {R S : CommRingCat.{u}} (φ : R ⟶ S) : sheafCom
pose (Opens.grothendieckTopology (Spec S)) (ModuleCat.restrictScalars (Spec.map 
φ).appTop.hom) ⋙ TopCat.Sheaf.pushforward _ (Spec.map φ).base ⋙ sheafCompose _ (
ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom) ≅ sheafCompose _ (ModuleC
at.restrictScalars (Scheme.ΓSpecIso S).inv.hom) ⋙ TopCat.Sheaf.pushforward _ (Sp
ec.map φ).base ⋙ sheafCompose _ (ModuleCat.restrictScalars φ.hom)
参数：φ : R ⟶ S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`sheafCompose` commutes with `pushforward`
-/
noncomputable def sheafComposePushforwardComp {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    sheafCompose (Opens.grothendieckTopology (Spec S))
      (ModuleCat.restrictScalars (Spec.map φ).appTop.hom) ⋙
      TopCat.Sheaf.pushforward _ (Spec.map φ).base ⋙
      sheafCompose _ (ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom) ≅
    sheafCompose _ (ModuleCat.restrictScalars (Scheme.ΓSpecIso S).inv.hom) ⋙
      TopCat.Sheaf.pushforward _ (Spec.map φ).base ⋙
      sheafCompose _ (ModuleCat.restrictScalars φ.hom) := by
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _ ?_) ?_
  · refine NatIso.ofComponents (fun U ↦ ?_) ?_
    · refine (ModuleCat.restrictScalarsComp'App _ _ _ ?_ _).symm ≪≫
        (ModuleCat.restrictScalarsComp φ.hom ((Scheme.ΓSpecIso S).inv).hom).app _
      rw [← CommRingCat.hom_comp, Scheme.ΓSpecIso_inv_naturality, CommRingCat.hom_comp]
    · cat_disch
  · cat_disch

/-- Sheaves of modules on `𝒪_X` restricted to `U` are equivalent to sheaves of `𝒪_U`-modules. -/
noncomputable
/-
**AlgebraicGeometry.Scheme.Modules.overEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Algebrai
cGeometry.Scheme.Modules`。
形式化陈述：overEquiv {X : Scheme.{u}} (U : X.Opens) : SheafOfModules (X.ringCatSheaf.
over U) ≌ (U : Scheme.{u}).Modules
参数：U : X.Opens。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def overEquiv {X : Scheme.{u}} (U : X.Opens) :
    SheafOfModules (X.ringCatSheaf.over U) ≌ (U : Scheme.{u}).Modules :=
  TopologicalSpace.Opens.sheafOfModulesEquivOver _ _

set_option backward.isDefEq.respectTransparency false in
/-- Up to `Scheme.Modules.overEquiv`, `SheafOfModules.overMap` is isomorphic to
`Scheme.Modules.restrictFunctor`. -/
noncomputable
/-
**AlgebraicGeometry.Scheme.Modules.overMapCompOverEquiv** 是 Mathlib 中的一个定义，位于命名空
间 `AlgebraicGeometry.Scheme.Modules`。
形式化陈述：overMapCompOverEquiv {X : Scheme.{u}} {U V : X.Opens} (f : V ⟶ U) : overMa
p X.ringCatSheaf f ⋙ (overEquiv V).functor ≅ (overEquiv U).functor ⋙ restrictFun
ctor (X.homOfLE <| leOfHom f)
参数：f : V ⟶ U。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def overMapCompOverEquiv {X : Scheme.{u}} {U V : X.Opens} (f : V ⟶ U) :
    overMap X.ringCatSheaf f ⋙ (overEquiv V).functor ≅
      (overEquiv U).functor ⋙ restrictFunctor (X.homOfLE <| leOfHom f) := by
  haveI : (Hom.opensFunctor (X.homOfLE <| leOfHom f)).IsContinuous
      (Opens.grothendieckTopology V.toScheme) (Opens.grothendieckTopology U.carrier) :=
    inferInstanceAs <|
      (Hom.opensFunctor (X.homOfLE <| leOfHom f)).IsContinuous _
      (Opens.grothendieckTopology U.toScheme)
  haveI := U.instIsDenseSubsiteSubtypeMemOverGrothendieckTopologyOverInverseOverEquivalence
  haveI : (Hom.opensFunctor (X.homOfLE <| leOfHom f)).IsContinuous
      (Opens.grothendieckTopology ↥V) (Opens.grothendieckTopology U.toScheme) :=
    inferInstanceAs <| (X.homOfLE <| leOfHom f).opensFunctor.IsContinuous
      (Opens.grothendieckTopology V.toScheme) (Opens.grothendieckTopology U.toScheme)
  haveI : ((Opens.overEquivalence V).symm.functor ⋙ Over.map f).IsContinuous
      (Opens.grothendieckTopology ↥V) ((Opens.grothendieckTopology X).over U) :=
    Functor.isContinuous_comp _ _ _ (.over (Opens.grothendieckTopology _) _) _
  haveI : (Opens.overEquivalence U).symm.functor.IsContinuous (Opens.grothendieckTopology U)
      ((Opens.grothendieckTopology X).over U) :=
    inferInstanceAs <| U.overEquivalence.inverse.IsContinuous (Opens.grothendieckTopology U.carrier)
      ((Opens.grothendieckTopology X).over U)
  haveI : ((X.homOfLE (leOfHom f)).opensFunctor ⋙
        (Opens.overEquivalence U).symm.functor).IsContinuous (Opens.grothendieckTopology ↥V)
      ((Opens.grothendieckTopology ↥X).over U) :=
    Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology _) _
  refine (SheafOfModules.pushforwardComp _ _) ≪≫ ?_ ≪≫ (SheafOfModules.pushforwardComp _ _).symm
  refine SheafOfModules.pushforwardCongr₂ _ ?_ ?_
  · refine NatIso.ofComponents (fun W ↦ Over.isoMk (eqToIso ?_) ?_) ?_
    · suffices U.ι ''ᵁ ((X.homOfLE (leOfHom f)) ''ᵁ W) = V.ι ''ᵁ W by simpa
      simp [← Scheme.Hom.comp_image]
    · cat_disch
    · cat_disch
  · ext W x
    suffices X.presheaf.map _ x = ((X.homOfLE <| leOfHom f).appIso _).inv x by simpa
    rw [Scheme.Hom.appIso_homOfLE_inv]
    rfl

/-- Up to `Scheme.Modules.overEquiv`, `SheafOfModules.overFunctor` is isomorphic to
`Scheme.Modules.restrictFunctor`. -/
noncomputable
/-
**AlgebraicGeometry.Scheme.Modules.overFunctorEquiv** 是 Mathlib 中的一个定义，位于命名空间 `A
lgebraicGeometry.Scheme.Modules`。
形式化陈述：overFunctorEquiv {X : Scheme.{u}} (U : X.Opens) : overFunctor X.ringCatShe
af U ⋙ (overEquiv U).functor ≅ restrictFunctor U.ι
参数：U : X.Opens。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
-/
def overFunctorEquiv {X : Scheme.{u}} (U : X.Opens) :
    overFunctor X.ringCatSheaf U ⋙ (overEquiv U).functor ≅ restrictFunctor U.ι := by
  have : ((Opens.overEquivalence U).symm.functor ⋙ Over.forget U).IsContinuous
      (Opens.grothendieckTopology ↥U) (Opens.grothendieckTopology ↥X) :=
    Functor.isContinuous_comp _ _ _ (.over (Opens.grothendieckTopology _) U) _
  refine SheafOfModules.pushforwardComp _ _ ≪≫ SheafOfModules.pushforwardCongr ?_
  simp only [CategoryTheory.Functor.map_id, Opposite.op_unop, Opens.ι_appIso, Iso.refl_inv]
  rfl

end AlgebraicGeometry.Scheme.Modules

