/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# The associated sheaf of a presheaf of modules

In this file, given a presheaf of modules `M₀` over a presheaf of rings `R₀`,
we construct the associated sheaf of `M₀`. More precisely, if `R` is a sheaf of
rings and `α : R₀ ⟶ R.val` is locally bijective, and `A` is the sheafification
of the underlying presheaf of abelian groups of `M₀`, i.e. we have a locally bijective
map `φ : M₀.presheaf ⟶ A.val`, then we endow `A` with the structure of a
sheaf of modules over `R`: this is `PresheafOfModules.sheafify α φ`.

In many applications, the morphism `α` shall be the identity, but this more
general construction allows the sheafification of both the presheaf of rings
and the presheaf of modules.

-/

@[expose] public section

universe w v v₁ u₁ u

open CategoryTheory Functor

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}

namespace CategoryTheory

namespace Presieve.FamilyOfElements

section smul

variable {R : Cᵒᵖ ⥤ RingCat.{u}} {M : PresheafOfModules.{v} R} {X : C} {P : Presieve X}
  (r : FamilyOfElements (R ⋙ forget _) P) (m : FamilyOfElements (M.presheaf ⋙ forget _) P)

/-- The scalar multiplication of family of elements of a presheaf of modules `M` over `R`
by a family of elements of `R`. -/
/-
**CategoryTheory.Presieve.FamilyOfElements.smul** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Presieve.FamilyOfElements`。
形式化陈述：smul : FamilyOfElements (M.presheaf ⋙ forget _) P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The scalar multiplication of family of elements of a presheaf of modules `M` ove
r `R`
by a family of elements of `R`.
-/
def smul : FamilyOfElements (M.presheaf ⋙ forget _) P := fun Y f hf =>
  HSMul.hSMul (α := R.obj (Opposite.op Y)) (β := M.obj (Opposite.op Y)) (r f hf) (m f hf)

end smul

section

variable {R₀ R : Cᵒᵖ ⥤ RingCat.{u}} (α : R₀ ⟶ R) [Presheaf.IsLocallyInjective J α]
  {M₀ : PresheafOfModules.{v} R₀} {A : Cᵒᵖ ⥤ AddCommGrpCat.{v}} (φ : M₀.presheaf ⟶ A)
  [Presheaf.IsLocallyInjective J φ] (hA : Presheaf.IsSeparated J A)
  {X : C} (r : R.obj (Opposite.op X)) (m : A.obj (Opposite.op X)) {P : Presieve X}
  (r₀ : FamilyOfElements (R₀ ⋙ forget _) P) (m₀ : FamilyOfElements (M₀.presheaf ⋙ forget _) P)
include hA

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Presieve.FamilyOfElements._root_.PresheafOfModules.Sheafify.app
_eq_of_isLocallyInjective** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Presieve.Fam
ilyOfElements`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.PresheafOfModules.Sheafify.app_eq_of_isLocallyInjective
    {Y : C} (r₀ r₀' : R₀.obj (Opposite.op Y))
    (m₀ m₀' : M₀.obj (Opposite.op Y))
    (hr₀ : α.app _ r₀ = α.app _ r₀')
    (hm₀ : φ.app _ m₀ = φ.app _ m₀') :
    φ.app _ (r₀ • m₀) = φ.app _ (r₀' • m₀') := by
  apply hA _ (Presheaf.equalizerSieve r₀ r₀' ⊓
      Presheaf.equalizerSieve (F := M₀.presheaf) m₀ m₀')
  · apply J.intersection_covering
    · exact Presheaf.equalizerSieve_mem J α _ _ hr₀
    · exact Presheaf.equalizerSieve_mem J φ _ _ hm₀
  · intro Z g hg
    rw [← NatTrans.naturality_apply (D := Ab), ← NatTrans.naturality_apply (D := Ab)]
    erw [M₀.map_smul, M₀.map_smul, hg.1, hg.2]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Presieve.FamilyOfElements.isCompatible_map_smul_aux** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.Presieve.FamilyOfElements`。
形式化陈述：isCompatible_map_smul_aux {Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) (r₀ : R₀.obj (
Opposite.op Y)) (r₀' : R₀.obj (Opposite.op Z)) (m₀ : M₀.obj (Opposite.op Y)) (m₀
' : M₀.obj (Opposite.op Z)) (hr₀ : α.app _ r₀ = R.map f.op r) (hr₀' : α.app _ r₀
' = R.map (f.op ≫ g.op) r) (hm₀ : φ.app _ m₀ = A.map f.op m) (hm₀' : φ.app _ m₀'
 = A.map (f.op ≫ g.op) m) : φ.app _ (M₀.map g.op (r₀ • m₀)) = φ.app _ (r₀' • m₀'
)
参数：f : Y ⟶ X；g : Z ⟶ Y；r₀ : R₀.obj (Opposite.op Y)；r₀' : R₀.obj (Opposite.op Z)；
m₀ : M₀.obj (Opposite.op Y)；m₀' : M₀.obj (Opposite.op Z)；hr₀ : α.app _ r₀ = R.ma
p f.op r；hr₀' : α.app _ r₀' = R.map (f.op ≫ g.op) r；hm₀ : φ.app _ m₀ = A.map f.o
p m；hm₀' : φ.app _ m₀' = A.map (f.op ≫ g.op) m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PresheafOfModules.Sheafify.app_eq_of_isLocallyInjective`：∀ {C : Type u₁}
 [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTop
ology C}   {R₀ R : CategoryTheory.Functor Cᵒᵖ…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `RingCat.comp_apply`：comp_apply {R S T : RingCat} (f : R ⟶ S) (g : S ⟶ T)
 (r : R) : (f ≫ g) r = g (f r)
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `AddCommGrpCat.coe_comp`：∀ {X Y Z : AddCommGrpCat} {f : X ⟶ Y} {g : Y ⟶ Z
},   ⇑(CategoryTheory.ConcreteCategory.hom (CategoryTheory.CategoryStruct.comp f
 g)) =     ⇑…
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `CategoryTheory.NatTrans.naturality_apply`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1
, u_1} D]   {FD : outParam (D …
· 使用定理 `PresheafOfModules.map_smul`：∀ {C : Type u₁} [inst : CategoryTheory.Categ
ory.{v₁, u₁} C] {R : CategoryTheory.Functor Cᵒᵖ RingCat}   (M : PresheafOfModule
s R) {X Y : Cᵒᵖ}…
-/
lemma isCompatible_map_smul_aux {Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y)
    (r₀ : R₀.obj (Opposite.op Y)) (r₀' : R₀.obj (Opposite.op Z))
    (m₀ : M₀.obj (Opposite.op Y)) (m₀' : M₀.obj (Opposite.op Z))
    (hr₀ : α.app _ r₀ = R.map f.op r) (hr₀' : α.app _ r₀' = R.map (f.op ≫ g.op) r)
    (hm₀ : φ.app _ m₀ = A.map f.op m) (hm₀' : φ.app _ m₀' = A.map (f.op ≫ g.op) m) :
    φ.app _ (M₀.map g.op (r₀ • m₀)) = φ.app _ (r₀' • m₀') := by
  rw [← PresheafOfModules.Sheafify.app_eq_of_isLocallyInjective α φ hA (R₀.map g.op r₀) r₀'
    (M₀.map g.op m₀) m₀', M₀.map_smul]
  · rw [hr₀', R.map_comp, RingCat.comp_apply, ← hr₀, ← RingCat.comp_apply, NatTrans.naturality,
      RingCat.comp_apply]
  · rw [hm₀', A.map_comp, AddCommGrpCat.coe_comp, Function.comp_apply, ← hm₀]
    erw [NatTrans.naturality_apply φ]

variable (hr₀ : (r₀.map (whiskerRight α (forget _))).IsAmalgamation r)
  (hm₀ : (m₀.map (whiskerRight φ (forget _))).IsAmalgamation m)

include hr₀ hm₀ in
/-
**CategoryTheory.Presieve.FamilyOfElements.isCompatible_map_smul** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.Presieve.FamilyOfElements`。
形式化陈述：isCompatible_map_smul : ((r₀.smul m₀).map (whiskerRight φ (forget _))).Com
patible
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RingCat.comp_apply`：comp_apply {R S T : RingCat} (f : R ⟶ S) (g : S ⟶ T)
 (r : R) : (f ≫ g) r = g (f r)
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.NatTrans.naturality_apply`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1
, u_1} D]   {FD : outParam (D …
· 使用定理 `CategoryTheory.ConcreteCategory.comp_apply`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (
C → Type w)}   {inst_1 : outPara…
· 使用定理 `CategoryTheory.op_comp`：op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f
 ≫ g).op = g.op ≫ f.op
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.Presieve.FamilyOfElements.isCompatible_map_smul_aux`：isCo
mpatible_map_smul_aux {Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) (r₀ : R₀.obj (Opposite.o
p Y)) (r₀' : R₀.obj (Opposite.op Z)) (m₀ : M₀.obj (Oppos…
-/
lemma isCompatible_map_smul : ((r₀.smul m₀).map (whiskerRight φ (forget _))).Compatible := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ fac
  let a₁ := r₀ f₁ h₁
  let b₁ := m₀ f₁ h₁
  let a₂ := r₀ f₂ h₂
  let b₂ := m₀ f₂ h₂
  let a₀ := R₀.map g₁.op a₁
  let b₀ := M₀.map g₁.op b₁
  have ha₁ : (α.app (Opposite.op Y₁)) a₁ = (R.map f₁.op) r := (hr₀ f₁ h₁).symm
  have ha₂ : (α.app (Opposite.op Y₂)) a₂ = (R.map f₂.op) r := (hr₀ f₂ h₂).symm
  have hb₁ : (φ.app (Opposite.op Y₁)) b₁ = (A.map f₁.op) m := (hm₀ f₁ h₁).symm
  have hb₂ : (φ.app (Opposite.op Y₂)) b₂ = (A.map f₂.op) m := (hm₀ f₂ h₂).symm
  have ha₀ : (α.app (Opposite.op Z)) a₀ = (R.map (f₁.op ≫ g₁.op)) r := by
    rw [← RingCat.comp_apply, NatTrans.naturality, RingCat.comp_apply, ha₁, Functor.map_comp,
      RingCat.comp_apply]
  have hb₀ : (φ.app (Opposite.op Z)) b₀ = (A.map (f₁.op ≫ g₁.op)) m := by
    dsimp [b₀]
    erw [NatTrans.naturality_apply φ, hb₁, Functor.map_comp, ConcreteCategory.comp_apply]
  have ha₀' : (α.app (Opposite.op Z)) a₀ = (R.map (f₂.op ≫ g₂.op)) r := by
    rw [ha₀, ← op_comp, fac, op_comp]
  have hb₀' : (φ.app (Opposite.op Z)) b₀ = (A.map (f₂.op ≫ g₂.op)) m := by
    rw [hb₀, ← op_comp, fac, op_comp]
  dsimp
  erw [← NatTrans.naturality_apply φ, ← NatTrans.naturality_apply φ]
  exact (isCompatible_map_smul_aux α φ hA r m f₁ g₁ a₁ a₀ b₁ b₀ ha₁ ha₀ hb₁ hb₀).trans
    (isCompatible_map_smul_aux α φ hA r m f₂ g₂ a₂ a₀ b₂ b₀ ha₂ ha₀' hb₂ hb₀').symm

end

end Presieve.FamilyOfElements

end CategoryTheory

variable {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]

namespace PresheafOfModules

variable {M₀ : PresheafOfModules.{v} R₀} {A : Sheaf J AddCommGrpCat.{v}}
  (φ : M₀.presheaf ⟶ A.obj)
  [Presheaf.IsLocallyInjective J φ] [Presheaf.IsLocallySurjective J φ]

namespace Sheafify

variable {X Y : Cᵒᵖ} (π : X ⟶ Y) (r r' : R.obj.obj X) (m m' : A.obj.obj X)

/-- Assuming `α : R₀ ⟶ R.val` is the sheafification map of a presheaf of rings `R₀`
and `φ : M₀.presheaf ⟶ A.val` is the sheafification map of the underlying
sheaf of abelian groups of a presheaf of modules `M₀` over `R₀`, then given
`r : R.val.obj X` and `m : A.val.obj X`, this structure contains the data
of `x : A.val.obj X` along with the property which makes `x` a good candidate
for the definition of the scalar multiplication `r • m`. -/
/-
**PresheafOfModules.Sheafify.SMulCandidate** 是 Mathlib 中的一个归纳类型，位于命名空间 `Presheaf
OfModules.Sheafify`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {J : C
ategoryTheory.GrothendieckTopology C} →       {R₀ : CategoryTheory.Functor Cᵒᵖ R
ingCat} →         {R : CategoryTheory.Sheaf J RingCat} →           (R₀ ⟶ R.obj) 
→             {M₀ : PresheafOfModules R₀} →               {A : CategoryTheory.Sh
eaf J AddCommGrpCat} →                 (M₀.presheaf ⟶ A.obj) → {X : Cᵒᵖ} → ↑(R.o
bj.obj X) → ↑(A.obj.obj X) → Type v
参数：R₀ ⟶ R.obj；M₀.presheaf ⟶ A.obj；R.obj.obj X；A.obj.obj X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Assuming `α : R₀ ⟶ R.val` is the sheafification map of a presheaf of rings `R₀`
and `φ : M₀.presheaf ⟶ A.val` is the sheafification map of the underlying
sheaf of abelian groups of a presheaf of modules `M₀` over `R₀`, then given
`r : R.val.obj X` and `m : A.val.obj X`, this structure contains the data
of `x : A.val.obj X` along with the property which makes `x` a good candidate
for the definition of the scalar multiplication `r • m`.
-/
structure SMulCandidate where
  /-- The candidate for the scalar product `r • m`. -/
  x : A.obj.obj X
  h ⦃Y : Cᵒᵖ⦄ (f : X ⟶ Y) (r₀ : R₀.obj Y) (hr₀ : α.app Y r₀ = R.obj.map f r)
    (m₀ : M₀.obj Y) (hm₀ : φ.app Y m₀ = A.obj.map f m) : A.obj.map f x = φ.app Y (r₀ • m₀)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Constructor for `SMulCandidate`. -/
/-
**PresheafOfModules.Sheafify.SMulCandidate.mk'** 是 Mathlib 中的一个定义，位于命名空间 `Preshe
afOfModules.Sheafify.SMulCandidate`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {J : C
ategoryTheory.GrothendieckTopology C} →       {R₀ : CategoryTheory.Functor Cᵒᵖ R
ingCat} →         {R : CategoryTheory.Sheaf J RingCat} →           (α : R₀ ⟶ R.o
bj) →             [CategoryTheory.Presheaf.IsLocallyInjective J α] →            
   {M₀ : PresheafOfModules R₀} →                 {A : CategoryTheory.Sheaf J Add
CommGrpCat} →                   (φ : M₀.presheaf ⟶ A.obj) →                     
[CategoryTheory.Presheaf.IsLocallyInjective J φ] →                       {X : Cᵒ
ᵖ} →                         (r : ↑(R.obj.obj X)) →                           (m
 : ↑(A.obj.obj X)) →                             (S : CategoryTheory.Sieve (Oppo
site.unop X)) →                               S ∈ J (Opposite.unop X) →         
                        (r₀ :                                     CategoryTheory
.Presieve.FamilyOfElements (R₀.comp (CategoryTheory.forget RingCat))            
                           S.arrows) →                                   (m₀ :  
                                     CategoryTheory.Presieve.FamilyOfElements   
                                      (M₀.presheaf.comp (CategoryTheory.forget A
b)) S.arrows) →                                     (r₀.map                     
                        (CategoryTheory.Functor.whiskerRight α                  
                             (CategoryTheory.forget RingCat))).IsAmalgamation   
                                      r →                                       
(m₀.map                                               (CategoryTheory.Functor.wh
iskerRight φ                                                 (CategoryTheory.for
get Ab))).IsAmalgamation                                           m →          
                               (a : ↑(A.obj.obj X)) →                           
                ((r₀.smul m₀).map                                               
    (CategoryTheory.Functor.whiskerRight φ                                      
               (CategoryTheory.forget Ab))).IsAmalgamation                      
                         a →                                             Preshea
fOfModules.Sheafify.SMulCandidate α φ r m
参数：α : R₀ ⟶ R.obj；φ : M₀.presheaf ⟶ A.obj；r : ↑(R.obj.obj X)；m : ↑(A.obj.obj X)；
S : CategoryTheory.Sieve (Opposite.unop X)；Opposite.unop X；r₀ :                 
                    CategoryTheory.Presieve.FamilyOfElements (R₀.comp (CategoryT
heory.forget RingCat))                                       S.arrows；m₀ :      
                                 CategoryTheory.Presieve.FamilyOfElements       
                                  (M₀.presheaf.comp (CategoryTheory.forget Ab)) 
S.arrows；r₀.map                                             (CategoryTheory.Func
tor.whiskerRight α                                               (CategoryTheory
.forget RingCat))；m₀.map                                               (Category
Theory.Functor.whiskerRight φ                                                 (C
ategoryTheory.forget Ab))；a : ↑(A.obj.obj X)；(r₀.smul m₀).map                   
                                (CategoryTheory.Functor.whiskerRight φ          
                                           (CategoryTheory.forget Ab))。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for `SMulCandidate`.
-/
def SMulCandidate.mk' (S : Sieve X.unop) (hS : S ∈ J X.unop)
    (r₀ : Presieve.FamilyOfElements (R₀ ⋙ forget _) S.arrows)
    (m₀ : Presieve.FamilyOfElements (M₀.presheaf ⋙ forget _) S.arrows)
    (hr₀ : (r₀.map (whiskerRight α (forget _))).IsAmalgamation r)
    (hm₀ : (m₀.map (whiskerRight φ (forget _))).IsAmalgamation m)
    (a : A.obj.obj X)
    (ha : ((r₀.smul m₀).map (whiskerRight φ (forget _))).IsAmalgamation a) :
    SMulCandidate α φ r m where
  x := a
  h Y f a₀ ha₀ b₀ hb₀ := by
    apply A.isSeparated _ _ (J.pullback_stable f.unop hS)
    rintro Z g hg
    dsimp at hg
    rw [← ConcreteCategory.comp_apply, ← A.obj.map_comp, ← NatTrans.naturality_apply (D := Ab)]
    erw [M₀.map_smul] -- Mismatch between `M₀.map` and `M₀.presheaf.map`
    refine (ha _ hg).trans (app_eq_of_isLocallyInjective α φ A.isSeparated _ _ _ _ ?_ ?_)
    · rw [← RingCat.comp_apply, NatTrans.naturality, RingCat.comp_apply, ha₀]
      apply (hr₀ _ hg).symm.trans
      simp
    · erw [NatTrans.naturality_apply φ, hb₀]
      apply (hm₀ _ hg).symm.trans
      dsimp
      rw [Functor.map_comp]
      rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**PresheafOfModules.Sheafify.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules.Sheaf
ify`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Nonempty (SMulCandidate α φ r m) := ⟨by
  let S := (Presheaf.imageSieve α r ⊓ Presheaf.imageSieve φ m)
  have hS : S ∈ J _ := by
    apply J.intersection_covering
    all_goals apply Presheaf.imageSieve_mem
  have h₁ : S ≤ Presheaf.imageSieve α r := fun _ _ h => h.1
  have h₂ : S ≤ Presheaf.imageSieve φ m := fun _ _ h => h.2
  let r₀ := (Presieve.FamilyOfElements.localPreimage (whiskerRight α (forget _)) r).restrict h₁
  let m₀ := (Presieve.FamilyOfElements.localPreimage (whiskerRight φ (forget _)) m).restrict h₂
  have hr₀ : (r₀.map (whiskerRight α (forget _))).IsAmalgamation r := by
    rw [Presieve.FamilyOfElements.restrict_map]
    apply Presieve.isAmalgamation_restrict
    apply Presieve.FamilyOfElements.isAmalgamation_map_localPreimage
  have hm₀ : (m₀.map (whiskerRight φ (forget _))).IsAmalgamation m := by
    rw [Presieve.FamilyOfElements.restrict_map]
    apply Presieve.isAmalgamation_restrict
    apply Presieve.FamilyOfElements.isAmalgamation_map_localPreimage
  exact SMulCandidate.mk' α φ r m S hS r₀ m₀ hr₀ hm₀ _ (Presieve.IsSheafFor.isAmalgamation
    (((sheafCompose J (forget _)).obj A).2.isSheafFor S hS)
    (Presieve.FamilyOfElements.isCompatible_map_smul α φ A.isSeparated r m r₀ m₀ hr₀ hm₀))⟩
/-
**PresheafOfModules.Sheafify.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules.Sheaf
ify`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Subsingleton (SMulCandidate α φ r m) where
  allEq := by
    rintro ⟨x₁, h₁⟩ ⟨x₂, h₂⟩
    simp only [SMulCandidate.mk.injEq]
    let S := (Presheaf.imageSieve α r ⊓ Presheaf.imageSieve φ m)
    have hS : S ∈ J _ := by
      apply J.intersection_covering
      all_goals apply Presheaf.imageSieve_mem
    apply A.isSeparated _ _ hS
    intro Y f ⟨⟨r₀, hr₀⟩, ⟨m₀, hm₀⟩⟩
    rw [h₁ f.op r₀ hr₀ m₀ hm₀, h₂ f.op r₀ hr₀ m₀ hm₀]
/-
**PresheafOfModules.Sheafify.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules.Sheaf
ify`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Unique (SMulCandidate α φ r m) :=
  uniqueOfSubsingleton (Nonempty.some inferInstance)

/-- The (unique) element in `SMulCandidate α φ r m`. -/
/-
**PresheafOfModules.Sheafify.smulCandidate** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOf
Modules.Sheafify`。
形式化陈述：smulCandidate : SMulCandidate α φ r m
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (unique) element in `SMulCandidate α φ r m`.
-/
noncomputable def smulCandidate : SMulCandidate α φ r m := default

/-- The scalar multiplication on the sheafification of a presheaf of modules. -/
/-
**PresheafOfModules.Sheafify.smul** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOfModules.S
heafify`。
形式化陈述：smul : A.obj.obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The scalar multiplication on the sheafification of a presheaf of modules.
-/
noncomputable def smul : A.obj.obj X := (smulCandidate α φ r m).x
/-
**PresheafOfModules.Sheafify.map_smul_eq** 是 Mathlib 中的一个引理，位于命名空间 `PresheafOfMo
dules.Sheafify`。
形式化陈述：map_smul_eq {Y : Cᵒᵖ} (f : X ⟶ Y) (r₀ : R₀.obj Y) (hr₀ : α.app Y r₀ = R.ob
j.map f r) (m₀ : M₀.obj Y) (hm₀ : φ.app Y m₀ = A.obj.map f m) : A.obj.map f (smu
l α φ r m) = φ.app Y (r₀ • m₀)
参数：f : X ⟶ Y；r₀ : R₀.obj Y；hr₀ : α.app Y r₀ = R.obj.map f r；m₀ : M₀.obj Y；hm₀ : 
φ.app Y m₀ = A.obj.map f m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PresheafOfModules.Sheafify.SMulCandidate.h`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C}   {R
₀ : CategoryTheory.Functor Cᵒᵖ R…
-/
lemma map_smul_eq {Y : Cᵒᵖ} (f : X ⟶ Y) (r₀ : R₀.obj Y) (hr₀ : α.app Y r₀ = R.obj.map f r)
    (m₀ : M₀.obj Y) (hm₀ : φ.app Y m₀ = A.obj.map f m) :
    A.obj.map f (smul α φ r m) = φ.app Y (r₀ • m₀) :=
  (smulCandidate α φ r m).h f r₀ hr₀ m₀ hm₀

set_option backward.isDefEq.respectTransparency.types false in
/-
**PresheafOfModules.Sheafify.one_smul** 是 Mathlib 中的一个定理，位于命名空间 `PresheafOfModul
es.Sheafify`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryT
heory.GrothendieckTopology C}   {R₀ : CategoryTheory.Functor Cᵒᵖ RingCat} {R : C
ategoryTheory.Sheaf J RingCat} (α : R₀ ⟶ R.obj)   [inst_1 : CategoryTheory.Presh
eaf.IsLocallyInjective J α] [inst_2 : CategoryTheory.Presheaf.IsLocallySurjectiv
e J α]   {M₀ : PresheafOfModules R₀} {A : CategoryTheory.Sheaf J AddCommGrpCat} 
(φ : M₀.presheaf ⟶ A.obj)   [inst_3 : CategoryTheory.Presheaf.IsLocallyInjective
 J φ] [inst_4 : CategoryTheory.Presheaf.IsLocallySurjective J φ]   {X : Cᵒᵖ} (m 
: ↑(A.obj.obj X)), PresheafOfModules.Sheafify.smul α φ 1 m = m
参数：α : R₀ ⟶ R.obj；φ : M₀.presheaf ⟶ A.obj；m : ↑(A.obj.obj X)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sheaf.isSeparated`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} A
]   {J : CategoryTheor…
· 使用定理 `CategoryTheory.hasSheafCompose_of_preservesMulticospan`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} A]   {B : Type u₃} [ins…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `AddCommGrpCat.forget_preservesLimitsOfSize`：CategoryTheory.Limits.Preser
vesLimitsOfSize.{w, v, u, u, u + 1, u + 1} (CategoryTheory.forget AddCommGrpCat)
· 使用引理 `CategoryTheory.Presheaf.imageSieve_mem`：imageSieve_mem {F G : Cᵒᵖ ⥤ A} (
f : F ⟶ G) [IsLocallySurjective J f] {U : Cᵒᵖ} (s : ToType (G.obj U)) : imageSie
ve f s in J U.unop
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `PresheafOfModules.Sheafify.map_smul_eq`：map_smul_eq {Y : Cᵒᵖ} (f : X ⟶ Y
) (r₀ : R₀.obj Y) (hr₀ : α.app Y r₀ = R.obj.map f r) (m₀ : M₀.obj Y) (hm₀ : φ.ap
p Y m₀ = A.obj.map f m) : A.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
protected lemma one_smul : smul α φ 1 m = m := by
  apply A.isSeparated _ _ (Presheaf.imageSieve_mem J φ m)
  rintro Y f ⟨m₀, hm₀⟩
  rw [← hm₀, map_smul_eq α φ 1 m f.op 1 (by simp) m₀ hm₀, one_smul]

set_option backward.isDefEq.respectTransparency false in
/-
**PresheafOfModules.Sheafify.zero_smul** 是 Mathlib 中的一个定理，位于命名空间 `PresheafOfModu
les.Sheafify`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryT
heory.GrothendieckTopology C}   {R₀ : CategoryTheory.Functor Cᵒᵖ RingCat} {R : C
ategoryTheory.Sheaf J RingCat} (α : R₀ ⟶ R.obj)   [inst_1 : CategoryTheory.Presh
eaf.IsLocallyInjective J α] [inst_2 : CategoryTheory.Presheaf.IsLocallySurjectiv
e J α]   {M₀ : PresheafOfModules R₀} {A : CategoryTheory.Sheaf J AddCommGrpCat} 
(φ : M₀.presheaf ⟶ A.obj)   [inst_3 : CategoryTheory.Presheaf.IsLocallyInjective
 J φ] [inst_4 : CategoryTheory.Presheaf.IsLocallySurjective J φ]   {X : Cᵒᵖ} (m 
: ↑(A.obj.obj X)), PresheafOfModules.Sheafify.smul α φ 0 m = 0
参数：α : R₀ ⟶ R.obj；φ : M₀.presheaf ⟶ A.obj；m : ↑(A.obj.obj X)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sheaf.isSeparated`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} A
]   {J : CategoryTheor…
· 使用定理 `CategoryTheory.hasSheafCompose_of_preservesMulticospan`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} A]   {B : Type u₃} [ins…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `AddCommGrpCat.forget_preservesLimitsOfSize`：CategoryTheory.Limits.Preser
vesLimitsOfSize.{w, v, u, u, u + 1, u + 1} (CategoryTheory.forget AddCommGrpCat)
· 使用引理 `CategoryTheory.Presheaf.imageSieve_mem`：imageSieve_mem {F G : Cᵒᵖ ⥤ A} (
f : F ⟶ G) [IsLocallySurjective J f] {U : Cᵒᵖ} (s : ToType (G.obj U)) : imageSie
ve f s in J U.unop
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PresheafOfModules.Sheafify.map_smul_eq`：map_smul_eq {Y : Cᵒᵖ} (f : X ⟶ Y
) (r₀ : R₀.obj Y) (hr₀ : α.app Y r₀ = R.obj.map f r) (m₀ : M₀.obj Y) (hm₀ : φ.ap
p Y m₀ = A.obj.map f m) : A.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `AddMonoidHom.map_zero`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M
] [inst_1 : AddZero N] (f : M →+ N), f 0 = 0
-/
protected lemma zero_smul : smul α φ 0 m = 0 := by
  apply A.isSeparated _ _ (Presheaf.imageSieve_mem J φ m)
  rintro Y f ⟨m₀, hm₀⟩
  rw [map_smul_eq α φ 0 m f.op 0 (by simp) m₀ hm₀, zero_smul, map_zero,
    (A.obj.map f.op).hom.map_zero]

set_option backward.isDefEq.respectTransparency false in
/-
**PresheafOfModules.Sheafify.smul_zero** 是 Mathlib 中的一个定理，位于命名空间 `PresheafOfModu
les.Sheafify`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryT
heory.GrothendieckTopology C}   {R₀ : CategoryTheory.Functor Cᵒᵖ RingCat} {R : C
ategoryTheory.Sheaf J RingCat} (α : R₀ ⟶ R.obj)   [inst_1 : CategoryTheory.Presh
eaf.IsLocallyInjective J α] [inst_2 : CategoryTheory.Presheaf.IsLocallySurjectiv
e J α]   {M₀ : PresheafOfModules R₀} {A : CategoryTheory.Sheaf J AddCommGrpCat} 
(φ : M₀.presheaf ⟶ A.obj)   [inst_3 : CategoryTheory.Presheaf.IsLocallyInjective
 J φ] [inst_4 : CategoryTheory.Presheaf.IsLocallySurjective J φ]   {X : Cᵒᵖ} (r 
: ↑(R.obj.obj X)), PresheafOfModules.Sheafify.smul α φ r 0 = 0
参数：α : R₀ ⟶ R.obj；φ : M₀.presheaf ⟶ A.obj；r : ↑(R.obj.obj X)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sheaf.isSeparated`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} A
]   {J : CategoryTheor…
· 使用定理 `CategoryTheory.hasSheafCompose_of_preservesMulticospan`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} A]   {B : Type u₃} [ins…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `AddCommGrpCat.forget_preservesLimitsOfSize`：CategoryTheory.Limits.Preser
vesLimitsOfSize.{w, v, u, u, u + 1, u + 1} (CategoryTheory.forget AddCommGrpCat)
· 使用引理 `CategoryTheory.Presheaf.imageSieve_mem`：imageSieve_mem {F G : Cᵒᵖ ⥤ A} (
f : F ⟶ G) [IsLocallySurjective J f] {U : Cᵒᵖ} (s : ToType (G.obj U)) : imageSie
ve f s in J U.unop
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidHom.map_zero`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M
] [inst_1 : AddZero N] (f : M →+ N), f 0 = 0
· 使用引理 `PresheafOfModules.Sheafify.map_smul_eq`：map_smul_eq {Y : Cᵒᵖ} (f : X ⟶ Y
) (r₀ : R₀.obj Y) (hr₀ : α.app Y r₀ = R.obj.map f r) (m₀ : M₀.obj Y) (hm₀ : φ.ap
p Y m₀ = A.obj.map f m) : A.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
protected lemma smul_zero : smul α φ r 0 = 0 := by
  apply A.isSeparated _ _ (Presheaf.imageSieve_mem J α r)
  rintro Y f ⟨r₀, hr₀⟩
  rw [(A.obj.map f.op).hom.map_zero, map_smul_eq α φ r 0 f.op r₀ hr₀ 0 (by simp),
    smul_zero, map_zero]

set_option backward.isDefEq.respectTransparency false in
/-
**PresheafOfModules.Sheafify.smul_add** 是 Mathlib 中的一个定理，位于命名空间 `PresheafOfModul
es.Sheafify`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryT
heory.GrothendieckTopology C}   {R₀ : CategoryTheory.Functor Cᵒᵖ RingCat} {R : C
ategoryTheory.Sheaf J RingCat} (α : R₀ ⟶ R.obj)   [inst_1 : CategoryTheory.Presh
eaf.IsLocallyInjective J α] [inst_2 : CategoryTheory.Presheaf.IsLocallySurjectiv
e J α]   {M₀ : PresheafOfModules R₀} {A : CategoryTheory.Sheaf J AddCommGrpCat} 
(φ : M₀.presheaf ⟶ A.obj)   [inst_3 : CategoryTheory.Presheaf.IsLocallyInjective
 J φ] [inst_4 : CategoryTheory.Presheaf.IsLocallySurjective J φ]   {X : Cᵒᵖ} (r 
: ↑(R.obj.obj X)) (m m' : ↑(A.obj.obj X)),   PresheafOfModules.Sheafify.smul α φ
 r (m + m') =     PresheafOfModules.Sheafify.smul α φ r m + PresheafOfModules.Sh
eafify.smul α φ r m'
参数：α : R₀ ⟶ R.obj；φ : M₀.presheaf ⟶ A.obj；r : ↑(R.obj.obj X)；m m' : ↑(A.obj.obj 
X)；m + m'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.intersection_covering`：intersection_
covering (rj : R in J X) (sj : S in J X) : R ⊓ S in J X
· 使用引理 `CategoryTheory.Presheaf.imageSieve_mem`：imageSieve_mem {F G : Cᵒᵖ ⥤ A} (
f : F ⟶ G) [IsLocallySurjective J f] {U : Cᵒᵖ} (s : ToType (G.obj U)) : imageSie
ve f s in J U.unop
· 使用定理 `CategoryTheory.Sheaf.isSeparated`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} A
]   {J : CategoryTheor…
· 使用定理 `CategoryTheory.hasSheafCompose_of_preservesMulticospan`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} A]   {B : Type u₃} [ins…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `AddCommGrpCat.forget_preservesLimitsOfSize`：CategoryTheory.Limits.Preser
vesLimitsOfSize.{w, v, u, u, u + 1, u + 1} (CategoryTheory.forget AddCommGrpCat)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidHom.map_add`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M]
 [inst_1 : AddZero N] (f : M →+ N) (a b : M), f (a + b) = f a + f b
· 使用引理 `PresheafOfModules.Sheafify.map_smul_eq`：map_smul_eq {Y : Cᵒᵖ} (f : X ⟶ Y
) (r₀ : R₀.obj Y) (hr₀ : α.app Y r₀ = R.obj.map f r) (m₀ : M₀.obj Y) (hm₀ : φ.ap
p Y m₀ = A.obj.map f m) : A.…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
-/
protected lemma smul_add : smul α φ r (m + m') = smul α φ r m + smul α φ r m' := by
  let S := Presheaf.imageSieve α r ⊓ Presheaf.imageSieve φ m ⊓ Presheaf.imageSieve φ m'
  have hS : S ∈ J X.unop := by
    refine J.intersection_covering (J.intersection_covering ?_ ?_) ?_
    all_goals apply Presheaf.imageSieve_mem
  apply A.isSeparated _ _ hS
  rintro Y f ⟨⟨⟨r₀, hr₀⟩, ⟨m₀ : M₀.obj _, hm₀ : (φ.app _) _ = _⟩⟩,
    ⟨m₀' : M₀.obj _, hm₀' : (φ.app _) _ = _⟩⟩
  rw [(A.obj.map f.op).hom.map_add, map_smul_eq α φ r m f.op r₀ hr₀ m₀ hm₀,
    map_smul_eq α φ r m' f.op r₀ hr₀ m₀' hm₀',
    map_smul_eq α φ r (m + m') f.op r₀ hr₀ (m₀ + m₀')
      (by rw [_root_.map_add, _root_.map_add, hm₀, hm₀']),
    smul_add, _root_.map_add]

set_option backward.isDefEq.respectTransparency false in
/-
**PresheafOfModules.Sheafify.add_smul** 是 Mathlib 中的一个定理，位于命名空间 `PresheafOfModul
es.Sheafify`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryT
heory.GrothendieckTopology C}   {R₀ : CategoryTheory.Functor Cᵒᵖ RingCat} {R : C
ategoryTheory.Sheaf J RingCat} (α : R₀ ⟶ R.obj)   [inst_1 : CategoryTheory.Presh
eaf.IsLocallyInjective J α] [inst_2 : CategoryTheory.Presheaf.IsLocallySurjectiv
e J α]   {M₀ : PresheafOfModules R₀} {A : CategoryTheory.Sheaf J AddCommGrpCat} 
(φ : M₀.presheaf ⟶ A.obj)   [inst_3 : CategoryTheory.Presheaf.IsLocallyInjective
 J φ] [inst_4 : CategoryTheory.Presheaf.IsLocallySurjective J φ]   {X : Cᵒᵖ} (r 
r' : ↑(R.obj.obj X)) (m : ↑(A.obj.obj X)),   PresheafOfModules.Sheafify.smul α φ
 (r + r') m =     PresheafOfModules.Sheafify.smul α φ r m + PresheafOfModules.Sh
eafify.smul α φ r' m
参数：α : R₀ ⟶ R.obj；φ : M₀.presheaf ⟶ A.obj；r r' : ↑(R.obj.obj X)；m : ↑(A.obj.obj 
X)；r + r'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.intersection_covering`：intersection_
covering (rj : R in J X) (sj : S in J X) : R ⊓ S in J X
· 使用引理 `CategoryTheory.Presheaf.imageSieve_mem`：imageSieve_mem {F G : Cᵒᵖ ⥤ A} (
f : F ⟶ G) [IsLocallySurjective J f] {U : Cᵒᵖ} (s : ToType (G.obj U)) : imageSie
ve f s in J U.unop
· 使用定理 `CategoryTheory.Sheaf.isSeparated`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} A
]   {J : CategoryTheor…
· 使用定理 `CategoryTheory.hasSheafCompose_of_preservesMulticospan`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} A]   {B : Type u₃} [ins…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `AddCommGrpCat.forget_preservesLimitsOfSize`：CategoryTheory.Limits.Preser
vesLimitsOfSize.{w, v, u, u, u + 1, u + 1} (CategoryTheory.forget AddCommGrpCat)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidHom.map_add`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M]
 [inst_1 : AddZero N] (f : M →+ N) (a b : M), f (a + b) = f a + f b
· 使用引理 `PresheafOfModules.Sheafify.map_smul_eq`：map_smul_eq {Y : Cᵒᵖ} (f : X ⟶ Y
) (r₀ : R₀.obj Y) (hr₀ : α.app Y r₀ = R.obj.map f r) (m₀ : M₀.obj Y) (hm₀ : φ.ap
p Y m₀ = A.obj.map f m) : A.…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
protected lemma add_smul : smul α φ (r + r') m = smul α φ r m + smul α φ r' m := by
  let S := Presheaf.imageSieve α r ⊓ Presheaf.imageSieve α r' ⊓ Presheaf.imageSieve φ m
  have hS : S ∈ J X.unop := by
    refine J.intersection_covering (J.intersection_covering ?_ ?_) ?_
    all_goals apply Presheaf.imageSieve_mem
  apply A.isSeparated _ _ hS
  rintro Y f ⟨⟨⟨r₀ : R₀.obj _, (hr₀ : (α.app (Opposite.op Y)) r₀ = (R.obj.map f.op) r)⟩,
    ⟨r₀' : R₀.obj _, (hr₀' : (α.app (Opposite.op Y)) r₀' = (R.obj.map f.op) r')⟩⟩, ⟨m₀, hm₀⟩⟩
  rw [(A.obj.map f.op).hom.map_add, map_smul_eq α φ r m f.op r₀ hr₀ m₀ hm₀,
    map_smul_eq α φ r' m f.op r₀' hr₀' m₀ hm₀,
    map_smul_eq α φ (r + r') m f.op (r₀ + r₀') (by rw [_root_.map_add, _root_.map_add, hr₀, hr₀'])
      m₀ hm₀, add_smul, _root_.map_add]
/-
**PresheafOfModules.Sheafify.mul_smul** 是 Mathlib 中的一个定理，位于命名空间 `PresheafOfModul
es.Sheafify`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryT
heory.GrothendieckTopology C}   {R₀ : CategoryTheory.Functor Cᵒᵖ RingCat} {R : C
ategoryTheory.Sheaf J RingCat} (α : R₀ ⟶ R.obj)   [inst_1 : CategoryTheory.Presh
eaf.IsLocallyInjective J α] [inst_2 : CategoryTheory.Presheaf.IsLocallySurjectiv
e J α]   {M₀ : PresheafOfModules R₀} {A : CategoryTheory.Sheaf J AddCommGrpCat} 
(φ : M₀.presheaf ⟶ A.obj)   [inst_3 : CategoryTheory.Presheaf.IsLocallyInjective
 J φ] [inst_4 : CategoryTheory.Presheaf.IsLocallySurjective J φ]   {X : Cᵒᵖ} (r 
r' : ↑(R.obj.obj X)) (m : ↑(A.obj.obj X)),   PresheafOfModules.Sheafify.smul α φ
 (r * r') m =     PresheafOfModules.Sheafify.smul α φ r (PresheafOfModules.Sheaf
ify.smul α φ r' m)
参数：α : R₀ ⟶ R.obj；φ : M₀.presheaf ⟶ A.obj；r r' : ↑(R.obj.obj X)；m : ↑(A.obj.obj 
X)；r * r'；PresheafOfModules.Sheafify.smul α φ r' m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.intersection_covering`：intersection_
covering (rj : R in J X) (sj : S in J X) : R ⊓ S in J X
· 使用引理 `CategoryTheory.Presheaf.imageSieve_mem`：imageSieve_mem {F G : Cᵒᵖ ⥤ A} (
f : F ⟶ G) [IsLocallySurjective J f] {U : Cᵒᵖ} (s : ToType (G.obj U)) : imageSie
ve f s in J U.unop
· 使用定理 `CategoryTheory.Sheaf.isSeparated`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} A
]   {J : CategoryTheor…
· 使用定理 `CategoryTheory.hasSheafCompose_of_preservesMulticospan`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} A]   {B : Type u₃} [ins…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `AddCommGrpCat.forget_preservesLimitsOfSize`：CategoryTheory.Limits.Preser
vesLimitsOfSize.{w, v, u, u, u + 1, u + 1} (CategoryTheory.forget AddCommGrpCat)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PresheafOfModules.Sheafify.map_smul_eq`：map_smul_eq {Y : Cᵒᵖ} (f : X ⟶ Y
) (r₀ : R₀.obj Y) (hr₀ : α.app Y r₀ = R.obj.map f r) (m₀ : M₀.obj Y) (hm₀ : φ.ap
p Y m₀ = A.obj.map f m) : A.…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected lemma mul_smul : smul α φ (r * r') m = smul α φ r (smul α φ r' m) := by
  let S := Presheaf.imageSieve α r ⊓ Presheaf.imageSieve α r' ⊓ Presheaf.imageSieve φ m
  have hS : S ∈ J X.unop := by
    refine J.intersection_covering (J.intersection_covering ?_ ?_) ?_
    all_goals apply Presheaf.imageSieve_mem
  apply A.isSeparated _ _ hS
  rintro Y f ⟨⟨⟨r₀ : R₀.obj _, (hr₀ : (α.app (Opposite.op Y)) r₀ = (R.obj.map f.op) r)⟩,
    ⟨r₀' : R₀.obj _, (hr₀' : (α.app (Opposite.op Y)) r₀' = (R.obj.map f.op) r')⟩⟩,
    ⟨m₀ : M₀.obj _, hm₀⟩⟩
  rw [map_smul_eq α φ (r * r') m f.op (r₀ * r₀')
    (by rw [map_mul, map_mul, hr₀, hr₀']) m₀ hm₀, mul_smul,
    map_smul_eq α φ r (smul α φ r' m) f.op r₀ hr₀ (r₀' • m₀)
      (map_smul_eq α φ r' m f.op r₀' hr₀' m₀ hm₀).symm]

variable (X)

/-- The module structure on the sections of the sheafification of the underlying
presheaf of abelian groups of a presheaf of modules. -/
@[instance_reducible]
/-
**PresheafOfModules.Sheafify.module** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOfModules
.Sheafify`。
形式化陈述：module : Module (R.obj.obj X) (A.obj.obj X) where smul r m
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PresheafOfModules.Sheafify.mul_smul`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C}   {R₀ : Cat
egoryTheory.Functor Cᵒᵖ R…
· 使用定理 `PresheafOfModules.Sheafify.one_smul`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C}   {R₀ : Cat
egoryTheory.Functor Cᵒᵖ R…
· 使用定理 `PresheafOfModules.Sheafify.smul_zero`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C}   {R₀ : Ca
tegoryTheory.Functor Cᵒᵖ R…
· 使用定理 `PresheafOfModules.Sheafify.smul_add`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C}   {R₀ : Cat
egoryTheory.Functor Cᵒᵖ R…
· 使用定理 `PresheafOfModules.Sheafify.add_smul`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C}   {R₀ : Cat
egoryTheory.Functor Cᵒᵖ R…
· 使用定理 `PresheafOfModules.Sheafify.zero_smul`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C}   {R₀ : Ca
tegoryTheory.Functor Cᵒᵖ R…

--- 原说明 ---
The module structure on the sections of the sheafification of the underlying
presheaf of abelian groups of a presheaf of modules.
-/
noncomputable def module : Module (R.obj.obj X) (A.obj.obj X) where
  smul r m := smul α φ r m
  one_smul := Sheafify.one_smul α φ
  zero_smul := Sheafify.zero_smul α φ
  smul_zero := Sheafify.smul_zero α φ
  smul_add := Sheafify.smul_add α φ
  add_smul := Sheafify.add_smul α φ
  mul_smul := Sheafify.mul_smul α φ
/-
**PresheafOfModules.Sheafify.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `PresheafOfModul
es.Sheafify`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryT
heory.GrothendieckTopology C}   {R₀ : CategoryTheory.Functor Cᵒᵖ RingCat} {R : C
ategoryTheory.Sheaf J RingCat} (α : R₀ ⟶ R.obj)   [inst_1 : CategoryTheory.Presh
eaf.IsLocallyInjective J α] [inst_2 : CategoryTheory.Presheaf.IsLocallySurjectiv
e J α]   {M₀ : PresheafOfModules R₀} {A : CategoryTheory.Sheaf J AddCommGrpCat} 
(φ : M₀.presheaf ⟶ A.obj)   [inst_3 : CategoryTheory.Presheaf.IsLocallyInjective
 J φ] [inst_4 : CategoryTheory.Presheaf.IsLocallySurjective J φ]   (X : Cᵒᵖ) {Y 
: Cᵒᵖ} (π : X ⟶ Y) (r : ↑(R.obj.obj X)) (m : ↑(A.obj.obj X)),   (CategoryTheory.
ConcreteCategory.hom (A.obj.map π)) (PresheafOfModules.Sheafify.smul α φ r m) = 
    PresheafOfModules.Sheafify.smul α φ ((CategoryTheory.ConcreteCategory.hom (R
.obj.map π)) r)       ((CategoryTheory.ConcreteCategory.hom (A.obj.map π)) m)
参数：α : R₀ ⟶ R.obj；φ : M₀.presheaf ⟶ A.obj；X : Cᵒᵖ；π : X ⟶ Y；r : ↑(R.obj.obj X)；m
 : ↑(A.obj.obj X)；CategoryTheory.ConcreteCategory.hom (A.obj.map π)；PresheafOfMo
dules.Sheafify.smul α φ r m；(CategoryTheory.ConcreteCategory.hom (R.obj.map π)) 
r；(CategoryTheory.ConcreteCategory.hom (A.obj.map π)) m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.intersection_covering`：intersection_
covering (rj : R in J X) (sj : S in J X) : R ⊓ S in J X
· 使用引理 `CategoryTheory.Presheaf.imageSieve_mem`：imageSieve_mem {F G : Cᵒᵖ ⥤ A} (
f : F ⟶ G) [IsLocallySurjective J f] {U : Cᵒᵖ} (s : ToType (G.obj U)) : imageSie
ve f s in J U.unop
· 使用定理 `CategoryTheory.Sheaf.isSeparated`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} A
]   {J : CategoryTheor…
· 使用定理 `CategoryTheory.hasSheafCompose_of_preservesMulticospan`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} A]   {B : Type u₃} [ins…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `AddCommGrpCat.forget_preservesLimitsOfSize`：CategoryTheory.Limits.Preser
vesLimitsOfSize.{w, v, u, u, u + 1, u + 1} (CategoryTheory.forget AddCommGrpCat)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ConcreteCategory.comp_apply`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (
C → Type w)}   {inst_1 : outPara…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `PresheafOfModules.Sheafify.map_smul_eq`：map_smul_eq {Y : Cᵒᵖ} (f : X ⟶ Y
) (r₀ : R₀.obj Y) (hr₀ : α.app Y r₀ = R.obj.map f r) (m₀ : M₀.obj Y) (hm₀ : φ.ap
p Y m₀ = A.obj.map f m) : A.…
· 使用引理 `RingCat.comp_apply`：comp_apply {R S T : RingCat} (f : R ⟶ S) (g : S ⟶ T)
 (r : R) : (f ≫ g) r = g (f r)
-/
protected lemma map_smul :
    A.obj.map π (smul α φ r m) = smul α φ (R.obj.map π r) (A.obj.map π m) := by
  let S := Presheaf.imageSieve α (R.obj.map π r) ⊓ Presheaf.imageSieve φ (A.obj.map π m)
  have hS : S ∈ J Y.unop := by
    apply J.intersection_covering
    all_goals apply Presheaf.imageSieve_mem
  apply A.isSeparated _ _ hS
  rintro Y f ⟨⟨r₀,
    (hr₀ : (α.app (Opposite.op Y)).hom r₀ = (R.obj.map f.op).hom ((R.obj.map π).hom r))⟩,
    ⟨m₀, (hm₀ : (φ.app _) _ = _)⟩⟩
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
    map_smul_eq α φ r m (π ≫ f.op) r₀ (by rw [hr₀, Functor.map_comp, RingCat.comp_apply]) m₀
      (by rw [hm₀, Functor.map_comp, ConcreteCategory.comp_apply]),
    map_smul_eq α φ (R.obj.map π r) (A.obj.map π m) f.op r₀ hr₀ m₀ hm₀]

end Sheafify

/-- Assuming `α : R₀ ⟶ R.obj` is the sheafification map of a presheaf of rings `R₀`
and `φ : M₀.presheaf ⟶ A.obj` is the sheafification map of the underlying
sheaf of abelian groups of a presheaf of modules `M₀` over `R₀`, this is
the sheaf of modules over `R` which is obtained by endowing the sections of
`A.obj` with a scalar multiplication. -/
/-
**PresheafOfModules.sheafify** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOfModules`。
形式化陈述：sheafify : SheafOfModules.{v} R where val
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PresheafOfModules.Sheafify.map_smul`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C}   {R₀ : Cat
egoryTheory.Functor Cᵒᵖ R…

--- 原说明 ---
Assuming `α : R₀ ⟶ R.obj` is the sheafification map of a presheaf of rings `R₀`
and `φ : M₀.presheaf ⟶ A.obj` is the sheafification map of the underlying
sheaf of abelian groups of a presheaf of modules `M₀` over `R₀`, this is
the sheaf of modules over `R` which is obtained by endowing the sections of
`A.obj` with a scalar multiplication.
-/
noncomputable def sheafify : SheafOfModules.{v} R where
  val := letI := Sheafify.module α φ; ofPresheaf A.obj (Sheafify.map_smul _ _)
  isSheaf := A.property

/-- The canonical morphism from a presheaf of modules to its associated sheaf. -/
/-
**PresheafOfModules.toSheafify** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOfModules`。
形式化陈述：toSheafify : M₀ ⟶ (restrictScalars α).obj (sheafify α φ).val
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical morphism from a presheaf of modules to its associated sheaf.
-/
noncomputable def toSheafify : M₀ ⟶ (restrictScalars α).obj (sheafify α φ).val :=
  homMk φ (fun X r₀ m₀ ↦ by
    simpa using! (Sheafify.map_smul_eq α φ (α.app _ r₀) (φ.app _ m₀) (𝟙 _)
      r₀ (by simp) m₀ (by simp)).symm)
/-
**PresheafOfModules.toSheafify_app_apply** 是 Mathlib 中的一个引理，位于命名空间 `PresheafOfMo
dules`。
形式化陈述：toSheafify_app_apply (X : Cᵒᵖ) (x : M₀.obj X) : ((toSheafify α φ).app X).h
om x = φ.app X x
参数：X : Cᵒᵖ；x : M₀.obj X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toSheafify_app_apply (X : Cᵒᵖ) (x : M₀.obj X) :
    ((toSheafify α φ).app X).hom x = φ.app X x := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- `@[simp]`-normal form of `toSheafify_app_apply`. -/
@[simp]
/-
**PresheafOfModules.toSheafify_app_apply'** 是 Mathlib 中的一个引理，位于命名空间 `PresheafOfM
odules`。
形式化陈述：toSheafify_app_apply' (X : Cᵒᵖ) (x : M₀.obj X) : DFunLike.coe (F
参数：X : Cᵒᵖ；x : M₀.obj X。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`@[simp]`-normal form of `toSheafify_app_apply`.
-/
lemma toSheafify_app_apply' (X : Cᵒᵖ) (x : M₀.obj X) :
    DFunLike.coe (F := (_ →ₗ[_] ↑((ModuleCat.restrictScalars (α.app X).hom).obj _)))
    ((toSheafify α φ).app X).hom x = φ.app X x := rfl

@[simp]
/-
**PresheafOfModules.toPresheaf_map_toSheafify** 是 Mathlib 中的一个引理，位于命名空间 `Preshea
fOfModules`。
形式化陈述：toPresheaf_map_toSheafify : (toPresheaf R₀).map (toSheafify α φ) = φ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toPresheaf_map_toSheafify : (toPresheaf R₀).map (toSheafify α φ) = φ := rfl

set_option backward.isDefEq.respectTransparency false in
/-
**PresheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsLocallyInjective J (toSheafify α φ) := by
  dsimp [IsLocallyInjective]; infer_instance

set_option backward.isDefEq.respectTransparency false in
/-
**PresheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsLocallySurjective J (toSheafify α φ) := by
  dsimp [IsLocallySurjective]; infer_instance

variable [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- The bijection `((sheafify α φ).val ⟶ F) ≃ (M₀ ⟶ (restrictScalars α).obj F)` which
is part of the universal property of the sheafification of the presheaf of modules `M₀`,
when `F` is a presheaf of modules which is a sheaf. -/
/-
**PresheafOfModules.sheafifyHomEquiv'** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOfModul
es`。
形式化陈述：sheafifyHomEquiv' {F : PresheafOfModules.{v} R.obj} (hF : Presheaf.IsSheaf
 J F.presheaf) : ((sheafify α φ).val ⟶ F) ≃ (M₀ ⟶ (restrictScalars α).obj F)
参数：hF : Presheaf.IsSheaf J F.presheaf。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `PresheafOfModules.instIsLocallySurjectiveToSheafify`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopolog
y C}   {R₀ : CategoryTheory.Functor Cᵒᵖ R…
· 使用定理 `PresheafOfModules.instIsLocallyInjectiveToSheafify`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology
 C}   {R₀ : CategoryTheory.Functor Cᵒᵖ R…

--- 原说明 ---
The bijection `((sheafify α φ).val ⟶ F) ≃ (M₀ ⟶ (restrictScalars α).obj F)` whic
h
is part of the universal property of the sheafification of the presheaf of modul
es `M₀`,
when `F` is a presheaf of modules which is a sheaf.
-/
noncomputable def sheafifyHomEquiv' {F : PresheafOfModules.{v} R.obj}
    (hF : Presheaf.IsSheaf J F.presheaf) :
    ((sheafify α φ).val ⟶ F) ≃ (M₀ ⟶ (restrictScalars α).obj F) :=
  (restrictHomEquivOfIsLocallySurjective α hF).trans
    (homEquivOfIsLocallyBijective (f := toSheafify α φ)
      (N := (restrictScalars α).obj F) hF)
/-
**PresheafOfModules.comp_toPresheaf_map_sheafifyHomEquiv'_symm_hom** 是 Mathlib 中
的一个定理，位于命名空间 `PresheafOfModules`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryT
heory.GrothendieckTopology C}   {R₀ : CategoryTheory.Functor Cᵒᵖ RingCat} {R : C
ategoryTheory.Sheaf J RingCat} (α : R₀ ⟶ R.obj)   [inst_1 : CategoryTheory.Presh
eaf.IsLocallyInjective J α] [inst_2 : CategoryTheory.Presheaf.IsLocallySurjectiv
e J α]   {M₀ : PresheafOfModules R₀} {A : CategoryTheory.Sheaf J AddCommGrpCat} 
(φ : M₀.presheaf ⟶ A.obj)   [inst_3 : CategoryTheory.Presheaf.IsLocallyInjective
 J φ] [inst_4 : CategoryTheory.Presheaf.IsLocallySurjective J φ]   [inst_5 : J.W
EqualsLocallyBijective AddCommGrpCat] {F : PresheafOfModules R.obj}   (hF : Cate
goryTheory.Presheaf.IsSheaf J F.presheaf) (f : M₀ ⟶ (PresheafOfModules.restrictS
calars α).obj F),   CategoryTheory.CategoryStruct.comp φ       ((PresheafOfModul
es.toPresheaf R.obj).map ((PresheafOfModules.sheafifyHomEquiv' α φ hF).symm f)) 
=     (PresheafOfModules.toPresheaf R₀).map f
参数：α : R₀ ⟶ R.obj；φ : M₀.presheaf ⟶ A.obj；hF : CategoryTheory.Presheaf.IsSheaf J
 F.presheaf；f : M₀ ⟶ (PresheafOfModules.restrictScalars α).obj F；(PresheafOfModu
les.toPresheaf R.obj).map ((PresheafOfModules.sheafifyHomEquiv' α φ hF).symm f)；
PresheafOfModules.toPresheaf R₀。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.congr_map`：congr_map (F : C ⥤ D) {X Y : C} {f g :
 X ⟶ Y} (h : f = g) : F.map f = F.map g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
lemma comp_toPresheaf_map_sheafifyHomEquiv'_symm_hom {F : PresheafOfModules.{v} R.obj}
    (hF : Presheaf.IsSheaf J F.presheaf) (f : M₀ ⟶ (restrictScalars α).obj F) :
    φ ≫ (toPresheaf R.obj).map ((sheafifyHomEquiv' α φ hF).symm f) = (toPresheaf R₀).map f :=
  (toPresheaf _).congr_map ((sheafifyHomEquiv' α φ hF).apply_symm_apply f)

/-- The bijection
`(sheafify α φ ⟶ F) ≃ (M₀ ⟶ (restrictScalars α).obj ((SheafOfModules.forget _).obj F))`
which is part of the universal property of the sheafification of the presheaf of modules `M₀`,
for any sheaf of modules `F`, see `PresheafOfModules.sheafificationAdjunction` -/
/-
**PresheafOfModules.sheafifyHomEquiv** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOfModule
s`。
形式化陈述：sheafifyHomEquiv {F : SheafOfModules.{v} R} : (sheafify α φ ⟶ F) ≃ (M₀ ⟶ (
restrictScalars α).obj ((SheafOfModules.forget _).obj F))
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `SheafOfModules.isSheaf`：∀ {C : Type u₁} [inst : CategoryTheory.Category.
{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C}   {R : CategoryTheory.Sh
eaf J RingCa…

--- 原说明 ---
The bijection
`(sheafify α φ ⟶ F) ≃ (M₀ ⟶ (restrictScalars α).obj ((SheafOfModules.forget _).o
bj F))`
which is part of the universal property of the sheafification of the presheaf of
 modules `M₀`,
for any sheaf of modules `F`, see `PresheafOfModules.sheafificationAdjunction`
-/
noncomputable def sheafifyHomEquiv {F : SheafOfModules.{v} R} :
    (sheafify α φ ⟶ F) ≃
      (M₀ ⟶ (restrictScalars α).obj ((SheafOfModules.forget _).obj F)) :=
  (SheafOfModules.fullyFaithfulForget R).homEquiv.trans
    (sheafifyHomEquiv' α φ F.isSheaf)

section

variable {M₀' : PresheafOfModules.{v} R₀} {A' : Sheaf J AddCommGrpCat.{v}}
  (φ' : M₀'.presheaf ⟶ A'.obj)
  [Presheaf.IsLocallyInjective J φ'] [Presheaf.IsLocallySurjective J φ']
  (τ₀ : M₀ ⟶ M₀') (τ : A ⟶ A')

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The morphism of sheaves of modules `sheafify α φ ⟶ sheafify α φ'`
induced by morphisms `τ₀ : M₀ ⟶ M₀'` and `τ : A ⟶ A'`
which satisfy `τ₀.hom ≫ φ' = φ ≫ τ.val`. -/
@[simps]
/-
**PresheafOfModules.sheafifyMap** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOfModules`。
形式化陈述：sheafifyMap (fac : (toPresheaf R₀).map τ₀ ≫ φ' = φ ≫ τ.hom) : sheafify α φ
 ⟶ sheafify α φ' where val
参数：fac : (toPresheaf R₀).map τ₀ ≫ φ' = φ ≫ τ.hom。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism of sheaves of modules `sheafify α φ ⟶ sheafify α φ'`
induced by morphisms `τ₀ : M₀ ⟶ M₀'` and `τ : A ⟶ A'`
which satisfy `τ₀.hom ≫ φ' = φ ≫ τ.val`.
-/
noncomputable def sheafifyMap (fac : (toPresheaf R₀).map τ₀ ≫ φ' = φ ≫ τ.hom) :
    sheafify α φ ⟶ sheafify α φ' where
  val := homMk τ.hom (fun X r m ↦ by
    let f := (sheafifyHomEquiv' α φ (by exact A'.property)).symm (τ₀ ≫ toSheafify α φ')
    suffices τ.hom = (toPresheaf _).map f by simpa only [this] using! (f.app X).hom.map_smul r m
    apply ((J.W_of_isLocallyBijective φ).homEquiv _ A'.property).injective
    dsimp [f]
    erw [comp_toPresheaf_map_sheafifyHomEquiv'_symm_hom]
    rw [← fac, Functor.map_comp, toPresheaf_map_toSheafify])

end

end PresheafOfModules

