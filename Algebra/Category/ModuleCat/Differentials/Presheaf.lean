/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Basic

/-!
# The presheaf of differentials of a presheaf of modules

In this file, we define the type `M.Derivation φ` of derivations
with values in a presheaf of `R`-modules `M` relative to
a morphism of `φ : S ⟶ F.op ⋙ R` of presheaves of commutative rings
over categories `C` and `D` that are related by a functor `F : C ⥤ D`.
We formalize the notion of universal derivation.

Geometrically, if `f : X ⟶ S` is a morphism of schemes (or more generally
a morphism of commutative ringed spaces), we would like to apply
these definitions in the case where `F` is the pullback functor from
open subsets of `S` to open subsets of `X` and `φ` is the
morphism $O_S ⟶ f_* O_X$.

In order to prove that there exists a universal derivation, the target
of which shall be called the presheaf of relative differentials of `φ`,
we first study the case where `F` is the identity functor.
In this case where we have a morphism of presheaves of commutative
rings `φ' : S' ⟶ R`, we construct a derivation
`DifferentialsConstruction.derivation'` which is universal.
Then, the general case (TODO) shall be obtained by observing that
derivations for `S ⟶ F.op ⋙ R` identify to derivations
for `S' ⟶ R` where `S'` is the pullback by `F` of the presheaf of
commutative rings `S` (the data is the same: it suffices
to show that the two vanishing conditions `d_app` are equivalent).

-/

@[expose] public section

universe v u v₁ v₂ u₁ u₂

open CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace PresheafOfModules

variable {S : Cᵒᵖ ⥤ CommRingCat.{u}} {F : C ⥤ D} {S' R : Dᵒᵖ ⥤ CommRingCat.{u}}
  (M N : PresheafOfModules.{v} (R ⋙ forget₂ _ _))
  (φ : S ⟶ F.op ⋙ R) (φ' : S' ⟶ R)

/-- Given a morphism of presheaves of commutative rings `φ : S ⟶ F.op ⋙ R`,
this is the type of relative `φ`-derivation of a presheaf of `R`-modules `M`. -/
@[ext]
/-
**PresheafOfModules.Derivation** 是 Mathlib 中的一个结构，位于命名空间 `PresheafOfModules`。
形式化陈述：Derivation where /-- the underlying additive map `R.obj X →+ M.obj X` of a
 derivation -/ d {X : Dᵒᵖ} : R.obj X ->+ M.obj X d_mul {X : Dᵒᵖ} (a b : R.obj X)
 : d (a * b) = a • d b + b • d a
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a morphism of presheaves of commutative rings `φ : S ⟶ F.op ⋙ R`,
this is the type of relative `φ`-derivation of a presheaf of `R`-modules `M`.
-/
structure Derivation where
  /-- the underlying additive map `R.obj X →+ M.obj X` of a derivation -/
  d {X : Dᵒᵖ} : R.obj X →+ M.obj X
  d_mul {X : Dᵒᵖ} (a b : R.obj X) : d (a * b) = a • d b + b • d a := by cat_disch
  d_map {X Y : Dᵒᵖ} (f : X ⟶ Y) (x : R.obj X) :
    d (R.map f x) = M.map f (d x) := by cat_disch
  d_app {X : Cᵒᵖ} (a : S.obj X) : d (φ.app X a) = 0 := by cat_disch

namespace Derivation

-- Note: `d_app` cannot be a simp lemma because `dsimp` would
-- simplify the composition of functors `R ⋙ forget₂ _ _`
attribute [simp] d_mul d_map

variable {M N φ}

/-
**PresheafOfModules.Derivation.congr_d** 是 Mathlib 中的一个引理，位于命名空间 `PresheafOfModu
les.Derivation`。
形式化陈述：congr_d {d d' : M.Derivation φ} (h : d = d') {X : Dᵒᵖ} (b : R.obj X) : d.d
 b = d'.d b
参数：h : d = d'；b : R.obj X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma congr_d {d d' : M.Derivation φ} (h : d = d') {X : Dᵒᵖ} (b : R.obj X) :
    d.d b = d'.d b := by rw [h]

variable (d : M.Derivation φ)
/-
**PresheafOfModules.Derivation.d_one** 是 Mathlib 中的一个定理，位于命名空间 `PresheafOfModule
s.Derivation`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {S : CategoryTheory.Functor Cᵒᵖ 
CommRingCat} {F : CategoryTheory.Functor C D}   {R : CategoryTheory.Functor Dᵒᵖ 
CommRingCat}   {M : PresheafOfModules (R.comp (CategoryTheory.forget₂ CommRingCa
t RingCat))} {φ : S ⟶ F.op.comp R}   (d : M.Derivation φ) (X : Dᵒᵖ), d.d 1 = 0
参数：R.comp (CategoryTheory.forget₂ CommRingCat RingCat)；d : M.Derivation φ；X : Dᵒ
ᵖ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `PresheafOfModules.Derivation.d_mul`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {S : CategoryTheor…
-/
@[simp] lemma d_one (X : Dᵒᵖ) : d.d (X := X) 1 = 0 := by
  simpa using d.d_mul (X := X) 1 1

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The postcomposition of a derivation by a morphism of presheaves of modules. -/
@[simps! d_apply]
/-
**PresheafOfModules.Derivation.postcomp** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOfMod
ules.Derivation`。
形式化陈述：postcomp (f : M ⟶ N) : N.Derivation φ where d
参数：f : M ⟶ N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The postcomposition of a derivation by a morphism of presheaves of modules.
-/
def postcomp (f : M ⟶ N) : N.Derivation φ where
  d := (f.app _).hom.toAddMonoidHom.comp d.d
  d_map {X Y} g x := by simpa using naturality_apply f g (d.d x)
  d_app {X} a := by
    dsimp
    erw [d_app]
    rw [map_zero]

/-- The universal property that a derivation `d : M.Derivation φ` must
satisfy so that the presheaf of modules `M` can be considered as the presheaf of
(relative) differentials of a presheaf of commutative rings `φ : S ⟶ F.op ⋙ R`. -/
/-
**PresheafOfModules.Derivation.Universal** 是 Mathlib 中的一个结构，位于命名空间 `PresheafOfMo
dules.Derivation`。
形式化陈述：Universal where /-- An absolute derivation of `M'` descends as a morphism 
`M ⟶ M'`. -/ desc {M' : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)} (d'
 : M'.Derivation φ) : M ⟶ M' fac {M' : PresheafOfModules (R ⋙ forget₂ CommRingCa
t RingCat)} (d' : M'.Derivation φ) : d.postcomp (desc d') = d'
参数：R ⋙ forget₂ CommRingCat RingCat；d' : M'.Derivation φ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The universal property that a derivation `d : M.Derivation φ` must
satisfy so that the presheaf of modules `M` can be considered as the presheaf of
(relative) differentials of a presheaf of commutative rings `φ : S ⟶ F.op ⋙ R`.
-/
structure Universal where
  /-- An absolute derivation of `M'` descends as a morphism `M ⟶ M'`. -/
  desc {M' : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)}
    (d' : M'.Derivation φ) : M ⟶ M'
  fac {M' : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)}
    (d' : M'.Derivation φ) : d.postcomp (desc d') = d' := by cat_disch
  postcomp_injective {M' : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)}
    (φ φ' : M ⟶ M') (h : d.postcomp φ = d.postcomp φ') : φ = φ' := by cat_disch

attribute [simp] Universal.fac
/-
**PresheafOfModules.Derivation.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules.Der
ivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Subsingleton d.Universal where
  allEq h₁ h₂ := by
    suffices ∀ {M' : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)}
      (d' : M'.Derivation φ), h₁.desc d' = h₂.desc d' by
        cases h₁
        cases h₂
        simp only [Universal.mk.injEq]
        ext : 2
        apply this
    intro M' d'
    apply h₁.postcomp_injective
    simp

end Derivation

/-- The property that there exists a universal derivation for
a morphism of presheaves of commutative rings `S ⟶ F.op ⋙ R`. -/
/-
**PresheafOfModules.HasDifferentials** 是 Mathlib 中的一个归纳类型，位于命名空间 `PresheafOfModu
les`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {S : Cat
egoryTheory.Functor Cᵒᵖ CommRingCat} →           {F : CategoryTheory.Functor C D
} → {R : CategoryTheory.Functor Dᵒᵖ CommRingCat} → (S ⟶ F.op.comp R) → Prop
参数：S ⟶ F.op.comp R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property that there exists a universal derivation for
a morphism of presheaves of commutative rings `S ⟶ F.op ⋙ R`.
-/
class HasDifferentials : Prop where
  exists_universal_derivation : ∃ (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _))
      (d : M.Derivation φ), Nonempty d.Universal

/-- Given a morphism of presheaves of commutative rings `φ : S ⟶ R`,
this is the type of relative `φ`-derivation of a presheaf of `R`-modules `M`. -/
/-
**PresheafOfModules.Derivation'** 是 Mathlib 中的一个缩写定义，位于命名空间 `PresheafOfModules`。
形式化陈述：Derivation' : Type _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a morphism of presheaves of commutative rings `φ : S ⟶ R`,
this is the type of relative `φ`-derivation of a presheaf of `R`-modules `M`.
-/
abbrev Derivation' : Type _ := M.Derivation (F := 𝟭 D) φ'

namespace Derivation'

variable {M φ'}

@[simp]
/-
**PresheafOfModules.Derivation.d_app** 是 Mathlib 中的一个定理，位于命名空间 `PresheafOfModule
s.Derivation`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {S : CategoryTheory.Functor Cᵒᵖ 
CommRingCat} {F : CategoryTheory.Functor C D}   {R : CategoryTheory.Functor Dᵒᵖ 
CommRingCat}   {M : PresheafOfModules (R.comp (CategoryTheory.forget₂ CommRingCa
t RingCat))} {φ : S ⟶ F.op.comp R}   (self : M.Derivation φ) {X : Cᵒᵖ} (a : ↑(S.
obj X)), self.d ((CategoryTheory.ConcreteCategory.hom (φ.app X)) a) = 0
参数：R.comp (CategoryTheory.forget₂ CommRingCat RingCat)；self : M.Derivation φ；a :
 ↑(S.obj X)；(CategoryTheory.ConcreteCategory.hom (φ.app X)) a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma d_app (d : M.Derivation' φ') {X : Dᵒᵖ} (a : S'.obj X) :
    d.d (φ'.app X a) = 0 :=
  Derivation.d_app d _

set_option backward.isDefEq.respectTransparency.types false in
/-- The derivation relative to the morphism of commutative rings `φ'.app X` induced by
a derivation relative to a morphism of presheaves of commutative rings. -/
/-
**PresheafOfModules.Derivation.app** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOfModules.
Derivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The derivation relative to the morphism of commutative rings `φ'.app X` induced 
by
a derivation relative to a morphism of presheaves of commutative rings.
-/
noncomputable def app (d : M.Derivation' φ') (X : Dᵒᵖ) : (M.obj X).Derivation (φ'.app X) :=
  ModuleCat.Derivation.mk (fun b ↦ d.d b)

@[simp]
/-
**PresheafOfModules.Derivation.app_apply** 是 Mathlib 中的一个引理，位于命名空间 `PresheafOfMo
dules.Derivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma app_apply (d : M.Derivation' φ') {X : Dᵒᵖ} (b : R.obj X) :
    (d.app X).d b = d.d b := rfl

section

variable (d : ∀ (X : Dᵒᵖ), (M.obj X).Derivation (φ'.app X))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a morphism of presheaves of commutative rings `φ'`, this is the
in derivation `M.Derivation' φ'` that is given by a compatible family of derivations
with values in the modules `M.obj X` for all `X`. -/
/-
**PresheafOfModules.Derivation.mk** 是 Mathlib 中的一个ctor，位于命名空间 `PresheafOfModules
.Derivation`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {S : Cat
egoryTheory.Functor Cᵒᵖ CommRingCat} →           {F : CategoryTheory.Functor C D
} →             {R : CategoryTheory.Functor Dᵒᵖ CommRingCat} →               {M 
: PresheafOfModules (R.comp (CategoryTheory.forget₂ CommRingCat RingCat))} →    
             {φ : S ⟶ F.op.comp R} →                   (d : {X : Dᵒᵖ} → ↑(R.obj 
X) →+ ↑(M.obj X)) →                     autoParam (∀ {X : Dᵒᵖ} (a b : ↑(R.obj X)
), d (a * b) = a • d b + b • d a)                         PresheafOfModules.Deri
vation.d_mul._autoParam →                       autoParam                       
    (∀ {X Y : Dᵒᵖ} (f : X ⟶ Y) (x : ↑(R.obj X)),                             d (
(CategoryTheory.ConcreteCategory.hom (R.map f)) x) =                            
   (CategoryTheory.ConcreteCategory.hom (M.map f)) (d x))                       
    PresheafOfModules.Derivation.d_map._autoParam →                         auto
Param                             (∀ {X : Cᵒᵖ} (a : ↑(S.obj X)), d ((CategoryThe
ory.ConcreteCategory.hom (φ.app X)) a) = 0)                             Presheaf
OfModules.Derivation.d_app._autoParam →                           M.Derivation φ
参数：R.comp (CategoryTheory.forget₂ CommRingCat RingCat)；d : {X : Dᵒᵖ} → ↑(R.obj X
) →+ ↑(M.obj X)；∀ {X : Dᵒᵖ} (a b : ↑(R.obj X)), d (a * b) = a • d b + b • d a；∀ 
{X Y : Dᵒᵖ} (f : X ⟶ Y) (x : ↑(R.obj X)),                             d ((Catego
ryTheory.ConcreteCategory.hom (R.map f)) x) =                               (Cat
egoryTheory.ConcreteCategory.hom (M.map f)) (d x)；∀ {X : Cᵒᵖ} (a : ↑(S.obj X)), 
d ((CategoryTheory.ConcreteCategory.hom (φ.app X)) a) = 0。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a morphism of presheaves of commutative rings `φ'`, this is the
in derivation `M.Derivation' φ'` that is given by a compatible family of derivat
ions
with values in the modules `M.obj X` for all `X`.
-/
def mk (d_map : ∀ ⦃X Y : Dᵒᵖ⦄ (f : X ⟶ Y) (x : R.obj X),
    (d Y).d ((R.map f) x) = (M.map f) ((d X).d x)) : M.Derivation' φ' where
  d {X} := AddMonoidHom.mk' (d X).d (by simp)

variable (d_map : ∀ ⦃X Y : Dᵒᵖ⦄ (f : X ⟶ Y) (x : R.obj X),
      (d Y).d ((R.map f) x) = (M.map f) ((d X).d x))

@[simp]
/-
**PresheafOfModules.Derivation.mk_app** 是 Mathlib 中的一个引理，位于命名空间 `PresheafOfModul
es.Derivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_app (X : Dᵒᵖ) : (mk d d_map).app X = d X := rfl

/-- Constructor for `Derivation.Universal` in the case `F` is the identity functor. -/
/-
**PresheafOfModules.Derivation.Universal.mk** 是 Mathlib 中的一个ctor，位于命名空间 `Preshea
fOfModules.Derivation.Universal`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {S : Cat
egoryTheory.Functor Cᵒᵖ CommRingCat} →           {F : CategoryTheory.Functor C D
} →             {R : CategoryTheory.Functor Dᵒᵖ CommRingCat} →               {M 
: PresheafOfModules (R.comp (CategoryTheory.forget₂ CommRingCat RingCat))} →    
             {φ : S ⟶ F.op.comp R} →                   {d : M.Derivation φ} →   
                  (desc :                         {M' : PresheafOfModules (R.com
p (CategoryTheory.forget₂ CommRingCat RingCat))} →                           M'.
Derivation φ → (M ⟶ M')) →                       autoParam                      
     (∀ {M' : PresheafOfModules (R.comp (CategoryTheory.forget₂ CommRingCat Ring
Cat))}                             (d' : M'.Derivation φ), d.postcomp (desc d') 
= d')                           PresheafOfModules.Derivation.Universal.fac._auto
Param →                         autoParam                             (∀ {M' : P
resheafOfModules (R.comp (CategoryTheory.forget₂ CommRingCat RingCat))}         
                      (φ_1 φ' : M ⟶ M'), d.postcomp φ_1 = d.postcomp φ' → φ_1 = 
φ')                             PresheafOfModules.Derivation.Universal.postcomp_
injective._autoParam →                           d.Universal
参数：R.comp (CategoryTheory.forget₂ CommRingCat RingCat)；desc :                   
      {M' : PresheafOfModules (R.comp (CategoryTheory.forget₂ CommRingCat RingCa
t))} →                           M'.Derivation φ → (M ⟶ M')；∀ {M' : PresheafOfMo
dules (R.comp (CategoryTheory.forget₂ CommRingCat RingCat))}                    
         (d' : M'.Derivation φ), d.postcomp (desc d') = d'；∀ {M' : PresheafOfMod
ules (R.comp (CategoryTheory.forget₂ CommRingCat RingCat))}                     
          (φ_1 φ' : M ⟶ M'), d.postcomp φ_1 = d.postcomp φ' → φ_1 = φ'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for `Derivation.Universal` in the case `F` is the identity functor.
-/
def Universal.mk {d : M.Derivation' φ'}
    (desc : ∀ {M' : PresheafOfModules (R ⋙ forget₂ _ _)}
      (_ : M'.Derivation' φ'), M ⟶ M')
    (fac : ∀ {M' : PresheafOfModules (R ⋙ forget₂ _ _)}
      (d' : M'.Derivation' φ'), d.postcomp (desc d') = d')
    (postcomp_injective : ∀ {M' : PresheafOfModules (R ⋙ forget₂ _ _)}
      (α β : M ⟶ M'), d.postcomp α = d.postcomp β → α = β) : d.Universal where
  desc := desc
  fac := fac
  postcomp_injective := postcomp_injective

end

end Derivation'

namespace DifferentialsConstruction

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The presheaf of relative differentials of a morphism of presheaves of
commutative rings. -/
@[simps -isSimp]
/-
**PresheafOfModules.DifferentialsConstruction.relativeDifferentials'** 是 Mathlib
 中的一个定义，位于命名空间 `PresheafOfModules.DifferentialsConstruction`。
形式化陈述：relativeDifferentials' : PresheafOfModules.{u} (R ⋙ forget₂ _ _) where obj
 X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The presheaf of relative differentials of a morphism of presheaves of
commutative rings.
-/
noncomputable def relativeDifferentials' :
    PresheafOfModules.{u} (R ⋙ forget₂ _ _) where
  obj X := CommRingCat.KaehlerDifferential (φ'.app X)
  -- Have to hint `g' := R.map f` below, or it gets unfolded weirdly.
  map f := CommRingCat.KaehlerDifferential.map (g' := R.map f) (φ'.naturality f)
  -- Without `dsimp`, `ext` doesn't pick up the right lemmas.
  map_id _ := by dsimp; ext; simp
  map_comp _ _ := by dsimp; ext; simp

attribute [simp] relativeDifferentials'_obj

@[simp]
/-
**PresheafOfModules.DifferentialsConstruction.relativeDifferentials'_map_d** 是 M
athlib 中的一个定理，位于命名空间 `PresheafOfModules.DifferentialsConstruction`。
形式化陈述：∀ {D : Type u₂} [inst : CategoryTheory.Category.{v₂, u₂} D] {S' R : Catego
ryTheory.Functor Dᵒᵖ CommRingCat}   (φ' : S' ⟶ R) {X Y : Dᵒᵖ} (f : X ⟶ Y) (x : ↑
(R.obj X)),   (ModuleCat.Hom.hom ((PresheafOfModules.DifferentialsConstruction.r
elativeDifferentials' φ').map f))       (CommRingCat.KaehlerDifferential.d x) = 
    CommRingCat.KaehlerDifferential.d ((CategoryTheory.ConcreteCategory.hom (R.m
ap f)) x)
参数：φ' : S' ⟶ R；f : X ⟶ Y；x : ↑(R.obj X)；ModuleCat.Hom.hom ((PresheafOfModules.Di
fferentialsConstruction.relativeDifferentials' φ').map f)；CommRingCat.KaehlerDif
ferential.d x；(CategoryTheory.ConcreteCategory.hom (R.map f)) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CommRingCat.KaehlerDifferential.map_d`：map_d (b : B) : map fac (d b) = d
 (g' b)
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
lemma relativeDifferentials'_map_d {X Y : Dᵒᵖ} (f : X ⟶ Y) (x : R.obj X) :
    DFunLike.coe (α := CommRingCat.KaehlerDifferential (φ'.app X))
      (β := fun _ ↦ CommRingCat.KaehlerDifferential (φ'.app Y))
      (ModuleCat.Hom.hom (R := ↑(R.obj X)) ((relativeDifferentials' φ').map f))
        (CommRingCat.KaehlerDifferential.d x) =
        CommRingCat.KaehlerDifferential.d (R.map f x) :=
  CommRingCat.KaehlerDifferential.map_d (φ'.naturality f) _

/-- The universal derivation. -/
/-
**PresheafOfModules.DifferentialsConstruction.derivation'** 是 Mathlib 中的一个定义，位于命
名空间 `PresheafOfModules.DifferentialsConstruction`。
形式化陈述：derivation' : (relativeDifferentials' φ').Derivation' φ'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The universal derivation.
-/
noncomputable def derivation' : (relativeDifferentials' φ').Derivation' φ' :=
  Derivation'.mk (fun X ↦ CommRingCat.KaehlerDifferential.D (φ'.app X))
    (fun _ _ f x ↦ (relativeDifferentials'_map_d φ' f x).symm)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The derivation `Derivation' φ'` is universal. -/
/-
**PresheafOfModules.DifferentialsConstruction.isUniversal'** 是 Mathlib 中的一个定义，位于
命名空间 `PresheafOfModules.DifferentialsConstruction`。
形式化陈述：isUniversal' : (derivation' φ').Universal
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The derivation `Derivation' φ'` is universal.
-/
noncomputable def isUniversal' : (derivation' φ').Universal :=
  Derivation'.Universal.mk
    (fun {M'} d' ↦
      { app := fun X ↦ (d'.app X).desc
        naturality := fun {X Y} f ↦ CommRingCat.KaehlerDifferential.ext (fun b ↦ by
          dsimp
          rw [ModuleCat.Derivation.desc_d, Derivation'.app_apply]
          erw [relativeDifferentials'_map_d φ' f]
          simp) })
    (fun {M'} d' ↦ by
      ext X b
      apply ModuleCat.Derivation.desc_d)
    (fun {M} α β h ↦ by
      ext1 X
      exact CommRingCat.KaehlerDifferential.ext (Derivation.congr_d h))
/-
**PresheafOfModules.DifferentialsConstruction.** 是 Mathlib 中的一个实例，位于命名空间 `Preshe
afOfModules.DifferentialsConstruction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasDifferentials (F := 𝟭 D) φ' := ⟨_, _, ⟨isUniversal' φ'⟩⟩

end DifferentialsConstruction

end PresheafOfModules

