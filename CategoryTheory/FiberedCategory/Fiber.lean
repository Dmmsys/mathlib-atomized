/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Paul Lezeau
-/
module

public import Mathlib.CategoryTheory.FiberedCategory.HomLift
public import Mathlib.CategoryTheory.Functor.Const

/-!

# Fibers of functors

In this file we define, for a functor `p : 𝒳 ⥤ 𝒴`, the fiber categories `Fiber p S` for every
`S : 𝒮` as follows
- An object in `Fiber p S` is a pair `(a, ha)` where `a : 𝒳` and `ha : p.obj a = S`.
- A morphism in `Fiber p S` is a morphism `φ : a ⟶ b` in 𝒳 such that `p.map φ = 𝟙 S`.

For any category `C` equipped with a functor `F : C ⥤ 𝒳` such that `F ⋙ p` is constant at `S`,
we define a functor `inducedFunctor : C ⥤ Fiber p S` that `F` factors through.
-/

@[expose] public section

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory

open IsHomLift

namespace Functor

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

/-- `Fiber p S` is the type of elements of `𝒳` mapping to `S` via `p`. -/
/-
**CategoryTheory.Functor.Fiber** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor
`。
形式化陈述：Fiber (p : 𝒳 ⥤ 𝒮) (S : 𝒮)
参数：p : 𝒳 ⥤ 𝒮；S : 𝒮。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Fiber p S` is the type of elements of `𝒳` mapping to `S` via `p`.
-/
def Fiber (p : 𝒳 ⥤ 𝒮) (S : 𝒮) := { a : 𝒳 // p.obj a = S }

namespace Fiber

variable {p : 𝒳 ⥤ 𝒮} {S : 𝒮}

/-- `Fiber p S` has the structure of a category with morphisms being those lying over `𝟙 S`. -/
/-
**CategoryTheory.Functor.Fiber.fiberCategory** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Functor.Fiber`。
形式化陈述：fiberCategory : Category (Fiber p S) where Hom a b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Fiber p S` has the structure of a category with morphisms being those lying ove
r `𝟙 S`.
-/
instance fiberCategory : Category (Fiber p S) where
  Hom a b := {φ : a.1 ⟶ b.1 // IsHomLift p (𝟙 S) φ}
  id a := ⟨𝟙 a.1, IsHomLift.id a.2⟩
  comp φ ψ := ⟨φ.val ≫ ψ.val, by have := φ.2; have := ψ.2; infer_instance⟩

/-- The functor including `Fiber p S` into `𝒳`. -/
/-
**CategoryTheory.Functor.Fiber.fiberInclusion** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Functor.Fiber`。
形式化陈述：fiberInclusion : Fiber p S ⥤ 𝒳 where obj a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor including `Fiber p S` into `𝒳`.
-/
def fiberInclusion : Fiber p S ⥤ 𝒳 where
  obj a := a.1
  map φ := φ.1
/-
**CategoryTheory.Functor.Fiber.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functo
r.Fiber`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {a b : Fiber p S} (φ : a ⟶ b) : IsHomLift p (𝟙 S) (fiberInclusion.map φ) := φ.2

@[ext]
/-
**CategoryTheory.Functor.Fiber.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Functor.Fiber`。
形式化陈述：hom_ext {a b : Fiber p S} {φ ψ : a ⟶ b} (h : fiberInclusion.map φ = fiberI
nclusion.map ψ) : φ = ψ
参数：h : fiberInclusion.map φ = fiberInclusion.map ψ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
lemma hom_ext {a b : Fiber p S} {φ ψ : a ⟶ b}
    (h : fiberInclusion.map φ = fiberInclusion.map ψ) : φ = ψ :=
  Subtype.ext h
/-
**CategoryTheory.Functor.Fiber.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functo
r.Fiber`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (fiberInclusion : Fiber p S ⥤ _).Faithful where
/-
**CategoryTheory.Functor.Fiber.fiberInclusion_obj_inj** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Functor.Fiber`。
形式化陈述：fiberInclusion_obj_inj : (fiberInclusion : Fiber p S ⥤ _).obj.Injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.val_inj`：val_inj {a b : Subtype p} : a.val = b.val ↔ a = b
-/
lemma fiberInclusion_obj_inj : (fiberInclusion : Fiber p S ⥤ _).obj.Injective :=
  fun _ _ f ↦ Subtype.val_inj.1 f

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- For fixed `S : 𝒮` this is the natural isomorphism between `fiberInclusion ⋙ p` and the constant
function valued at `S`. -/
@[simps!]
/-
**CategoryTheory.Functor.Fiber.fiberInclusionCompIsoConst** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Functor.Fiber`。
形式化陈述：fiberInclusionCompIsoConst : fiberInclusion ⋙ p ≅ (const (Fiber p S)).obj 
S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For fixed `S : 𝒮` this is the natural isomorphism between `fiberInclusion ⋙ p` a
nd the constant
function valued at `S`.
-/
def fiberInclusionCompIsoConst : fiberInclusion ⋙ p ≅ (const (Fiber p S)).obj S :=
  NatIso.ofComponents (fun X ↦ eqToIso X.2)
    (fun φ ↦ by simp [IsHomLift.fac' p (𝟙 S) (fiberInclusion.map φ)])
/-
**CategoryTheory.Functor.Fiber.fiberInclusion_comp_eq_const** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Functor.Fiber`。
形式化陈述：fiberInclusion_comp_eq_const : fiberInclusion ⋙ p = (const (Fiber p S)).ob
j S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.ext_of_iso`：ext_of_iso {F G : C ⥤ D} (e : F ≅ G) 
(hobj : forall X, F.obj X = G.obj X) (happ : forall X, e.hom.app X = eqToHom (ho
bj X)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma fiberInclusion_comp_eq_const : fiberInclusion ⋙ p = (const (Fiber p S)).obj S :=
  Functor.ext_of_iso fiberInclusionCompIsoConst (fun x ↦ x.2)

/-- The object of the fiber over `S` corresponding to a `a : 𝒳` such that `p(a) = S`. -/
/-
**CategoryTheory.Functor.Fiber.mk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Func
tor.Fiber`。
形式化陈述：mk {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {a : 𝒳} (ha : p.obj a = S) : Fiber p S
参数：ha : p.obj a = S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The object of the fiber over `S` corresponding to a `a : 𝒳` such that `p(a) = S`
.
-/
def mk {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {a : 𝒳} (ha : p.obj a = S) : Fiber p S := ⟨a, ha⟩

@[simp]
/-
**CategoryTheory.Functor.Fiber.fiberInclusion_mk** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Functor.Fiber`。
形式化陈述：fiberInclusion_mk {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {a : 𝒳} (ha : p.obj a = S) : fiberIn
clusion.obj (mk ha) = a
参数：ha : p.obj a = S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fiberInclusion_mk {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {a : 𝒳} (ha : p.obj a = S) :
    fiberInclusion.obj (mk ha) = a :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The morphism in the fiber over `S` corresponding to a morphism in `𝒳` lifting `𝟙 S`. -/
/-
**CategoryTheory.Functor.Fiber.homMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.F
unctor.Fiber`。
形式化陈述：homMk (p : 𝒳 ⥤ 𝒮) (S : 𝒮) {a b : 𝒳} (φ : a ⟶ b) [IsHomLift p (𝟙 S) φ] : mk
 (domain_eq p (𝟙 S) φ) ⟶ mk (codomain_eq p (𝟙 S) φ)
参数：p : 𝒳 ⥤ 𝒮；S : 𝒮；φ : a ⟶ b；𝟙 S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism in the fiber over `S` corresponding to a morphism in `𝒳` lifting `𝟙
 S`.
-/
def homMk (p : 𝒳 ⥤ 𝒮) (S : 𝒮) {a b : 𝒳} (φ : a ⟶ b) [IsHomLift p (𝟙 S) φ] :
    mk (domain_eq p (𝟙 S) φ) ⟶ mk (codomain_eq p (𝟙 S) φ) :=
  ⟨φ, inferInstance⟩

@[simp]
/-
**CategoryTheory.Functor.Fiber.fiberInclusion_homMk** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Functor.Fiber`。
形式化陈述：fiberInclusion_homMk (p : 𝒳 ⥤ 𝒮) (S : 𝒮) {a b : 𝒳} (φ : a ⟶ b) [IsHomLift 
p (𝟙 S) φ] : fiberInclusion.map (homMk p S φ) = φ
参数：p : 𝒳 ⥤ 𝒮；S : 𝒮；φ : a ⟶ b；𝟙 S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsHomLift.domain_eq`：domain_eq (f : R ⟶ S) (φ : a ⟶ b) [p
.IsHomLift f φ] : p.obj a = R
· 使用引理 `CategoryTheory.IsHomLift.codomain_eq`：codomain_eq (f : R ⟶ S) (φ : a ⟶ b
) [p.IsHomLift f φ] : p.obj b = S
-/
lemma fiberInclusion_homMk (p : 𝒳 ⥤ 𝒮) (S : 𝒮) {a b : 𝒳} (φ : a ⟶ b) [IsHomLift p (𝟙 S) φ] :
    fiberInclusion.map (homMk p S φ) = φ :=
  rfl

@[simp]
/-
**CategoryTheory.Functor.Fiber.homMk_id** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Functor.Fiber`。
形式化陈述：homMk_id (p : 𝒳 ⥤ 𝒮) (S : 𝒮) (a : 𝒳) [IsHomLift p (𝟙 S) (𝟙 a)] : homMk p S
 (𝟙 a) = 𝟙 (mk (domain_eq p (𝟙 S) (𝟙 a)))
参数：p : 𝒳 ⥤ 𝒮；S : 𝒮；a : 𝒳；𝟙 S；𝟙 a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsHomLift.domain_eq`：domain_eq (f : R ⟶ S) (φ : a ⟶ b) [p
.IsHomLift f φ] : p.obj a = R
· 使用引理 `CategoryTheory.IsHomLift.codomain_eq`：codomain_eq (f : R ⟶ S) (φ : a ⟶ b
) [p.IsHomLift f φ] : p.obj b = S
-/
lemma homMk_id (p : 𝒳 ⥤ 𝒮) (S : 𝒮) (a : 𝒳) [IsHomLift p (𝟙 S) (𝟙 a)] :
    homMk p S (𝟙 a) = 𝟙 (mk (domain_eq p (𝟙 S) (𝟙 a))) :=
  rfl

@[simp]
/-
**CategoryTheory.Functor.Fiber.homMk_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Functor.Fiber`。
形式化陈述：homMk_comp {a b c : 𝒳} (φ : a ⟶ b) (ψ : b ⟶ c) [IsHomLift p (𝟙 S) φ] [IsHo
mLift p (𝟙 S) ψ] : homMk p S φ ≫ homMk p S ψ = homMk p S (φ ≫ ψ)
参数：φ : a ⟶ b；ψ : b ⟶ c；𝟙 S；𝟙 S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsHomLift.domain_eq`：domain_eq (f : R ⟶ S) (φ : a ⟶ b) [p
.IsHomLift f φ] : p.obj a = R
· 使用引理 `CategoryTheory.IsHomLift.codomain_eq`：codomain_eq (f : R ⟶ S) (φ : a ⟶ b
) [p.IsHomLift f φ] : p.obj b = S
-/
lemma homMk_comp {a b c : 𝒳} (φ : a ⟶ b) (ψ : b ⟶ c) [IsHomLift p (𝟙 S) φ]
    [IsHomLift p (𝟙 S) ψ] : homMk p S φ ≫ homMk p S ψ = homMk p S (φ ≫ ψ) :=
  rfl

section

variable {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {C : Type u₃} [Category.{v₃} C] {F : C ⥤ 𝒳}
  (hF : F ⋙ p = (const C).obj S)

set_option backward.defeqAttrib.useBackward true in
/-- Given a functor `F : C ⥤ 𝒳` such that `F ⋙ p` is constant at some `S : 𝒮`, then
we get an induced functor `C ⥤ Fiber p S` that `F` factors through. -/
/-
**CategoryTheory.Functor.Fiber.inducedFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Functor.Fiber`。
形式化陈述：inducedFunctor : C ⥤ Fiber p S where obj x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `F : C ⥤ 𝒳` such that `F ⋙ p` is constant at some `S : 𝒮`, then
we get an induced functor `C ⥤ Fiber p S` that `F` factors through.
-/
def inducedFunctor : C ⥤ Fiber p S where
  obj x := ⟨F.obj x, by simp only [← comp_obj, hF, const_obj_obj]⟩
  map φ := ⟨F.map φ, of_commsq _ _ _ (congr_obj hF _) (congr_obj hF _) <|
    by simpa using (eqToIso hF).hom.naturality φ⟩

/-- Given a functor `F : C ⥤ 𝒳` such that `F ⋙ p` is constant at some `S : 𝒮`, then
we get a natural isomorphism between `inducedFunctor _ ⋙ fiberInclusion` and `F`. -/
@[simps!]
/-
**CategoryTheory.Functor.Fiber.inducedFunctorCompIsoSelf** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Functor.Fiber`。
形式化陈述：inducedFunctorCompIsoSelf : (inducedFunctor hF) ⋙ fiberInclusion ≅ F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `F : C ⥤ 𝒳` such that `F ⋙ p` is constant at some `S : 𝒮`, then
we get a natural isomorphism between `inducedFunctor _ ⋙ fiberInclusion` and `F`
.
-/
def inducedFunctorCompIsoSelf : (inducedFunctor hF) ⋙ fiberInclusion ≅ F := .refl _
/-
**CategoryTheory.Functor.Fiber.inducedFunctor_comp** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Functor.Fiber`。
形式化陈述：inducedFunctor_comp : (inducedFunctor hF) ⋙ fiberInclusion = F
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inducedFunctor_comp : (inducedFunctor hF) ⋙ fiberInclusion = F := rfl

@[simp]
/-
**CategoryTheory.Functor.Fiber.inducedFunctor_comp_obj** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Functor.Fiber`。
形式化陈述：inducedFunctor_comp_obj (X : C) : fiberInclusion.obj ((inducedFunctor hF).
obj X) = F.obj X
参数：X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inducedFunctor_comp_obj (X : C) :
    fiberInclusion.obj ((inducedFunctor hF).obj X) = F.obj X := rfl

@[simp]
/-
**CategoryTheory.Functor.Fiber.inducedFunctor_comp_map** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Functor.Fiber`。
形式化陈述：inducedFunctor_comp_map {X Y : C} (f : X ⟶ Y) : fiberInclusion.map ((induc
edFunctor hF).map f) = F.map f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inducedFunctor_comp_map {X Y : C} (f : X ⟶ Y) :
    fiberInclusion.map ((inducedFunctor hF).map f) = F.map f := rfl

end

end Fiber

end Functor

end CategoryTheory

