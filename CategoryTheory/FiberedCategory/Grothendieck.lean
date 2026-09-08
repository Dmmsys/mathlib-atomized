/-
Copyright (c) 2025 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Fernando Chu, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Bicategory.Grothendieck
public import Mathlib.CategoryTheory.FiberedCategory.HasFibers

/-!
# The Grothendieck construction gives a fibered category

In this file we show that the Grothendieck construction applied to a pseudofunctor `F`
gives a fibered category over the base category.

We also provide a `HasFibers` instance to `∫ᶜ F`, such that the fiber over `S` is the
category `F(S)`.

## References
[Vistoli2008] "Notes on Grothendieck Topologies, Fibered Categories and Descent Theory" by
Angelo Vistoli

-/

@[expose] public section

namespace CategoryTheory.Pseudofunctor.CoGrothendieck

open CategoryTheory.Functor Opposite Bicategory Fiber

variable {𝒮 : Type*} [Category* 𝒮] {F : LocallyDiscrete 𝒮ᵒᵖ ⥤ᵖ Cat}

section

variable {R S : 𝒮} (a : F.obj ⟨op S⟩) (f : R ⟶ S)

/-- The domain of the Cartesian lift of `f`. -/
/-
**CategoryTheory.Pseudofunctor.CoGrothendieck.domainCartesianLift** 是 Mathlib 中的
一个缩写定义，位于命名空间 `CategoryTheory.Pseudofunctor.CoGrothendieck`。
形式化陈述：domainCartesianLift : ∫ᶜ F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The domain of the Cartesian lift of `f`.
-/
abbrev domainCartesianLift : ∫ᶜ F := ⟨R, (F.map f.op.toLoc).toFunctor.obj a⟩

/-- The Cartesian lift of `f`. -/
/-
**CategoryTheory.Pseudofunctor.CoGrothendieck.cartesianLift** 是 Mathlib 中的一个缩写定义
，位于命名空间 `CategoryTheory.Pseudofunctor.CoGrothendieck`。
形式化陈述：cartesianLift : domainCartesianLift a f ⟶ ⟨S, a⟩
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Cartesian lift of `f`.
-/
abbrev cartesianLift : domainCartesianLift a f ⟶ ⟨S, a⟩ := ⟨f, 𝟙 _⟩
/-
**CategoryTheory.Pseudofunctor.CoGrothendieck.isHomLift_cartesianLift** 是 Mathli
b 中的一个实例，位于命名空间 `CategoryTheory.Pseudofunctor.CoGrothendieck`。
形式化陈述：isHomLift_cartesianLift : IsHomLift (forget F) f (cartesianLift a f)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isHomLift_cartesianLift : IsHomLift (forget F) f (cartesianLift a f) :=
  IsHomLift.map (forget F) (cartesianLift a f)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable {a} in
/-- Given some lift `φ'` of `g ≫ f`, the canonical map from the domain of `φ'` to the domain of
the Cartesian lift of `f`. -/
/-
**CategoryTheory.Pseudofunctor.CoGrothendieck.homCartesianLift** 是 Mathlib 中的一个缩
写定义，位于命名空间 `CategoryTheory.Pseudofunctor.CoGrothendieck`。
形式化陈述：homCartesianLift {a' : ∫ᶜ F} (g : a'.1 ⟶ R) (φ' : a' ⟶ ⟨S, a⟩) [IsHomLift 
(forget F) (g ≫ f) φ'] : a' ⟶ domainCartesianLift a f where base
参数：g : a'.1 ⟶ R；φ' : a' ⟶ ⟨S, a⟩；forget F；g ≫ f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given some lift `φ'` of `g ≫ f`, the canonical map from the domain of `φ'` to th
e domain of
the Cartesian lift of `f`.
-/
abbrev homCartesianLift {a' : ∫ᶜ F} (g : a'.1 ⟶ R) (φ' : a' ⟶ ⟨S, a⟩)
    [IsHomLift (forget F) (g ≫ f) φ'] : a' ⟶ domainCartesianLift a f where
  base := g
  fiber :=
    have : φ'.base = g ≫ f := by simpa using IsHomLift.fac' (forget F) (g ≫ f) φ'
    φ'.fiber ≫ eqToHom (by simp [this]) ≫ (F.mapComp f.op.toLoc g.op.toLoc).hom.toNatTrans.app a

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Pseudofunctor.CoGrothendieck.isHomLift_homCartesianLift** 是 Mat
hlib 中的一个实例，位于命名空间 `CategoryTheory.Pseudofunctor.CoGrothendieck`。
形式化陈述：isHomLift_homCartesianLift {a' : ∫ᶜ F} {φ' : a' ⟶ ⟨S, a⟩} {g : a'.1 ⟶ R} [
IsHomLift (forget F) (g ≫ f) φ'] : IsHomLift (forget F) g (homCartesianLift f g 
φ')
参数：forget F；g ≫ f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isHomLift_homCartesianLift {a' : ∫ᶜ F} {φ' : a' ⟶ ⟨S, a⟩} {g : a'.1 ⟶ R}
    [IsHomLift (forget F) (g ≫ f) φ'] : IsHomLift (forget F) g (homCartesianLift f g φ') :=
  IsHomLift.map (forget F) (homCartesianLift f g φ')

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Pseudofunctor.CoGrothendieck.isStronglyCartesian_homCartesianLi
ft** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Pseudofunctor.CoGrothendieck`。
形式化陈述：isStronglyCartesian_homCartesianLift : IsStronglyCartesian (forget F) f (c
artesianLift a f) where universal_property' {a'} g φ' hφ'
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Pseudofunctor.CoGrothendieck.Hom.ext`：∀ {𝒮 : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} 𝒮]   {F : CategoryTheory.Pseudofunctor (Ca
tegoryTheory.LocallyDiscrete 𝒮ᵒᵖ) Categor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.IsHomLift.domain_eq`：domain_eq (f : R ⟶ S) (φ : a ⟶ b) [p
.IsHomLift f φ] : p.obj a = R
· 使用引理 `CategoryTheory.IsHomLift.codomain_eq`：codomain_eq (f : R ⟶ S) (φ : a ⟶ b
) [p.IsHomLift f φ] : p.obj b = S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用引理 `CategoryTheory.IsHomLift.fac`：fac : f = eqToHom (domain_eq p f φ).symm ≫
 p.map φ ≫ eqToHom (codomain_eq p f φ)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
-/
lemma isStronglyCartesian_homCartesianLift :
    IsStronglyCartesian (forget F) f (cartesianLift a f) where
  universal_property' {a'} g φ' hφ' := by
    refine ⟨homCartesianLift f g φ', ⟨inferInstance, ?_⟩, ?_⟩
    · exact Hom.ext _ _ (by simpa using IsHomLift.fac (forget F) (g ≫ f) φ')
        (by simp [← Cat.Hom₂.comp_app])
    rintro χ' ⟨hχ'.symm, rfl⟩
    obtain ⟨rfl⟩ : g = χ'.1 := by simpa using IsHomLift.fac (forget F) g χ'
    ext <;> simp [← Cat.Hom₂.comp_app]

end

/-- `forget F : ∫ᶜ F ⥤ 𝒮` is a fibered category. -/
/-
**CategoryTheory.Pseudofunctor.CoGrothendieck.** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.Pseudofunctor.CoGrothendieck`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`forget F : ∫ᶜ F ⥤ 𝒮` is a fibered category.
-/
instance : IsFibered (forget F) :=
  IsFibered.of_exists_isStronglyCartesian (fun a _ f ↦
    ⟨domainCartesianLift a.2 f, cartesianLift a.2 f, isStronglyCartesian_homCartesianLift a.2 f⟩)

variable (F) (S : 𝒮)

set_option backward.isDefEq.respectTransparency false in
attribute [local simp] PrelaxFunctor.map₂_eqToHom in
/-- The inclusion map from `F(S)` into `∫ᶜ F`. -/
@[simps]
/-
**CategoryTheory.Pseudofunctor.CoGrothendieck.** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Pseudofunctor.CoGrothendieck`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion map from `F(S)` into `∫ᶜ F`.
-/
def ι : F.obj ⟨op S⟩ ⥤ ∫ᶜ F where
  obj a := { base := S, fiber := a }
  map {a b} φ := { base := 𝟙 S, fiber := φ ≫ (F.mapId ⟨op S⟩).inv.toNatTrans.app b }
  map_comp {a b c} φ ψ := by
    ext
    · simp
    · simp [← (F.mapId ⟨op S⟩).inv.toNatTrans.naturality_assoc ψ, F.whiskerRight_mapId_inv_app,
        Strict.leftUnitor_eqToIso, ← Cat.Hom₂.comp_app]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The natural isomorphism encoding `comp_const`. -/
@[simps!]
/-
**CategoryTheory.Pseudofunctor.CoGrothendieck.compIso** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Pseudofunctor.CoGrothendieck`。
形式化陈述：compIso : (ι F S) ⋙ forget F ≅ (const (F.obj ⟨op S⟩)).obj S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism encoding `comp_const`.
-/
def compIso : (ι F S) ⋙ forget F ≅ (const (F.obj ⟨op S⟩)).obj S :=
  NatIso.ofComponents (fun a => eqToIso rfl)
/-
**CategoryTheory.Pseudofunctor.CoGrothendieck.comp_const** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Pseudofunctor.CoGrothendieck`。
形式化陈述：comp_const : (ι F S) ⋙ forget F = (const (F.obj ⟨op S⟩)).obj S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.ext_of_iso`：ext_of_iso {F G : C ⥤ D} (e : F ≅ G) 
(hobj : forall X, F.obj X = G.obj X) (happ : forall X, e.hom.app X = eqToHom (ho
bj X)
-/
lemma comp_const : (ι F S) ⋙ forget F = (const (F.obj ⟨op S⟩)).obj S :=
  Functor.ext_of_iso (compIso F S) (fun _ ↦ rfl) (fun _ => rfl)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Pseudofunctor.CoGrothendieck.** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.Pseudofunctor.CoGrothendieck`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : (Fiber.inducedFunctor (comp_const F S)).Full where
  map_surjective {X Y} f := by
    have hf : (fiberInclusion.map f).base = 𝟙 S := by
      simpa using (IsHomLift.fac (forget F) (𝟙 S) (fiberInclusion.map f)).symm
    use (fiberInclusion.map f).fiber ≫ eqToHom (by simp [hf]) ≫
      (F.mapId ⟨op S⟩).hom.toNatTrans.app Y
    ext <;> simp [hf, ← Cat.Hom₂.comp_app]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Pseudofunctor.CoGrothendieck.** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.Pseudofunctor.CoGrothendieck`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Fiber.inducedFunctor (comp_const F S)).Faithful where
  map_injective {a b} := by
    intro f g heq
    replace heq := fiberInclusion.congr_map heq
    simpa [cancel_mono, ← Cat.Hom.toNatIso_hom,
      ← Cat.Hom.toNatIso_inv] using ((Hom.ext_iff _ _).mp heq).2

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Pseudofunctor.CoGrothendieck.** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.Pseudofunctor.CoGrothendieck`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : (Fiber.inducedFunctor (comp_const F S)).EssSurj := by
  apply essSurj_of_surj
  intro Y
  have hYS : (fiberInclusion.obj Y).base = S := by simpa using! Y.2
  use hYS ▸ (fiberInclusion.obj Y).fiber
  apply fiberInclusion_obj_inj
  ext <;> simp [hYS]
/-
**CategoryTheory.Pseudofunctor.CoGrothendieck.** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.Pseudofunctor.CoGrothendieck`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : (Fiber.inducedFunctor (comp_const F S)).IsEquivalence where

/-- `HasFibers` instance for `∫ᶜ F`, where the fiber over `S` is `F.obj ⟨op S⟩`. -/
/-
**CategoryTheory.Pseudofunctor.CoGrothendieck.** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.Pseudofunctor.CoGrothendieck`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HasFibers` instance for `∫ᶜ F`, where the fiber over `S` is `F.obj ⟨op S⟩`.
-/
noncomputable instance : HasFibers (forget F) where
  Fib S := F.obj ⟨op S⟩
  ι := ι F
  comp_const := comp_const F

end CategoryTheory.Pseudofunctor.CoGrothendieck

