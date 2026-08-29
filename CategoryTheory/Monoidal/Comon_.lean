/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Monoidal.Braided.Opposite
public import Mathlib.CategoryTheory.Monoidal.Transport
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# The category of comonoids in a monoidal category.

We define comonoids in a monoidal category `C`,
and show that they are equivalently monoid objects in the opposite category.

We construct the monoidal structure on `Comon C`, when `C` is braided.

An oplax monoidal functor takes comonoid objects to comonoid objects.
That is, an oplax monoidal functor `F : C ⥤ D` induces a functor `Comon C ⥤ Comon D`.

## TODO
* Comonoid objects in `C` are "just"
  oplax monoidal functors from the trivial monoidal category to `C`.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory

namespace CategoryTheory
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]

/--
Definition of `ComonObj` / `ComonObj` 的定义

English:
class ComonObj
  parameters: (X : C)
  axioms and operations (5):
    - counit : X ⟶ 𝟙_ C
    - comul : X ⟶ X otimes X
    - counit_comul((X)) : comul ≫ counit ▷ X = (fun_ X).inv  [default: by cat_disch]
    - comul_counit((X)) : comul ≫ X ◁ counit = (ρ_ X).inv  [default: by cat_disch]
    - comul_assoc((X)) : comul ≫ X ◁ comul = comul ≫ (comul ▷ X) ≫ (α_ X X X).hom  [default: by cat_disch]

中文:
类 余monObj
  参数: (X : C)
  公理与运算 (5 个):
    - counit : X ⟶ 𝟙_ C
    - comul : X ⟶ X otimes X
    - counit_comul((X)) : comul ≫ counit ▷ X = (fun_ X).inv  [默认: by cat_disch]
    - comul_counit((X)) : comul ≫ X ◁ counit = (ρ_ X).inv  [默认: by cat_disch]
    - comul_assoc((X)) : comul ≫ X ◁ comul = comul ≫ (comul ▷ X) ≫ (α_ X X X).hom  [默认: by cat_disch]

Depends on / 依赖: cat_disch, comul_assoc, comul_counit, counit
-/
class ComonObj (X : C) where
  /-- The counit morphism of a comonoid object. -/
  counit : X ⟶ 𝟙_ C
  /-- The comultiplication morphism of a comonoid object. -/
  comul : X ⟶ X otimes X
  counit_comul (X) : comul ≫ counit ▷ X = (fun_ X).inv := by cat_disch
  comul_counit (X) : comul ≫ X ◁ counit = (ρ_ X).inv := by cat_disch
  comul_assoc (X) : comul ≫ X ◁ comul = comul ≫ (comul ▷ X) ≫ (α_ X X X).hom := by cat_disch

namespace ComonObj

@[inherit_doc] scoped notation "Δ" => ComonObj.comul
@[inherit_doc] scoped notation "Δ[" M "]" => ComonObj.comul (X := M)
@[inherit_doc] scoped notation "ε" => ComonObj.counit
@[inherit_doc] scoped notation "ε[" M "]" => ComonObj.counit (X := M)

attribute [reassoc (attr := simp)] counit_comul comul_counit comul_assoc

/-- The canonical comonoid structure on the monoidal unit.
This is not a global instance to avoid conflicts with other comonoid structures. -/
@[instance_reducible, simps]
/--
Definition of `instTensorUnit` / `instTensorUnit` 的定义

English:
definition instTensorUnit
  signature: (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C]
  body: 𝟙 _
  comul := (fun_ _).inv
  counit_comul := by simp
  comul_counit := by monoidal_coherence
  comul_assoc := by monoidal_coherence

中文:
定义 instTensorUnit
  签名: (C : 类型u₁) [范畴.{v₁} C] [幺半群范畴.{v₁} C]
  定义体: 𝟙 _
  comul := (fun_ _).inv
  counit_comul := by simp
  comul_counit := by monoidal_coherence
  comul_assoc := by monoidal_coherence
-/
def instTensorUnit (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C] : ComonObj (𝟙_ C) where
  counit := 𝟙 _
  comul := (fun_ _).inv
  counit_comul := by simp
  comul_counit := by monoidal_coherence
  comul_assoc := by monoidal_coherence

end ComonObj

open scoped ComonObj

variable {M N O : C} [ComonObj M] [ComonObj N] [ComonObj O]

/--
Definition of `IsComonHom` / `IsComonHom` 的定义

English:
class IsComonHom
  parameters: (f : M ⟶ N)
  axioms and operations (2):
    - hom_counit((f)) : f ≫ ε = ε  [default: by cat_disch]
    - hom_comul((f)) : f ≫ Δ = Δ ≫ (f otimesₘ f)  [default: by cat_disch]

中文:
类 是余mon态射
  参数: (f : M ⟶ N)
  公理与运算 (2 个):
    - hom_counit((f)) : f ≫ ε = ε  [默认: by cat_disch]
    - hom_comul((f)) : f ≫ Δ = Δ ≫ (f otimesₘ f)  [默认: by cat_disch]

Depends on / 依赖: cat_disch, hom_comul
-/
class IsComonHom (f : M ⟶ N) : Prop where
  hom_counit (f) : f ≫ ε = ε := by cat_disch
  hom_comul (f) : f ≫ Δ = Δ ≫ (f otimesₘ f) := by cat_disch

attribute [reassoc (attr := simp)] IsComonHom.hom_counit IsComonHom.hom_comul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsComonHom (𝟙 M)

中文:
实例 :
  签名: 是余mon态射 (𝟙 M)
-/
instance : IsComonHom (𝟙 M) where

instance (f : M ⟶ N) (g : N ⟶ O) [IsComonHom f] [IsComonHom g] : IsComonHom (f ≫ g) where

instance (f : M ≅ N) [IsComonHom f.hom] : IsComonHom f.inv where
  hom_counit := by simp [Iso.inv_comp_eq]
  hom_comul := by simp [Iso.inv_comp_eq]

instance (f : M ⟶ N) [IsComonHom f] [IsIso f] : IsComonHom (inv f) where

variable (C) in
/--
Definition of `Comon` / `Comon` 的定义

English:
structure Comon
  parameters: where
  axioms and operations (2):
    - X : C
    - [comon : ComonObj X]

中文:
结构 余mon
  参数: where
  公理与运算 (2 个):
    - X : C
    - [comon : 余monObj X]
-/
structure Comon where
  /-- The underlying object of a comonoid object. -/
  X : C
  [comon : ComonObj X]

attribute [instance] Comon.comon

namespace Comon

attribute [local instance] ComonObj.instTensorUnit in
variable (C) in
/-- The trivial comonoid object. We later show this is terminal in `Comon C`.
-/
@[simps!]
/--
Definition of `trivial` / `trivial` 的定义

English:
definition trivial
  signature: : Comon C
  body: mk (𝟙_ C)

中文:
定义 trivial
  签名: : 余mon C
  定义体: mk (𝟙_ C)
-/
def trivial : Comon C := mk (𝟙_ C)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Comon C)
  body: ⟨trivial C⟩

中文:
实例 :
  签名: 可居 (余mon C)
  定义体: ⟨trivial C⟩
-/
instance : Inhabited (Comon C) :=
  ⟨trivial C⟩

end Comon

namespace ComonObj

variable {M : C} [ComonObj M]

@[reassoc (attr := simp)]
/--
theorem `counit_comul_hom` / 定理 `counit_comul_hom`

English:
theorem counit_comul_hom
  given: {Z : C} (f : M ⟶ Z)
  statement: Δ[M] ≫ (ε[M] otimesₘ f) = f ≫ (fun_ Z).inv
  proof: by
  rw [leftUnitor_inv_naturality]; rw [tensorHom_def]; rw [counit_comul_assoc]

@[reassoc (attr := simp)]

中文:
定理 counit_comul_hom
  条件: {Z : C} (f : M ⟶ Z)
  结论: Δ[M] ≫ (ε[M] otimesₘ f) = f ≫ (fun_ Z).inv
  证明: by
  rw [leftUnitor_inv_naturality]; rw [tensorHom_def]; rw [counit_comul_assoc]

@[reassoc (attr := simp)]

Depends on / 依赖: counit_comul_assoc, leftUnitor_inv_naturality, tensorHom_def
-/
theorem counit_comul_hom {Z : C} (f : M ⟶ Z) : Δ[M] ≫ (ε[M] otimesₘ f) = f ≫ (fun_ Z).inv := by
  rw [leftUnitor_inv_naturality]; rw [tensorHom_def]; rw [counit_comul_assoc]

@[reassoc (attr := simp)]
/--
theorem `comul_counit_hom` / 定理 `comul_counit_hom`

English:
theorem comul_counit_hom
  given: {Z : C} (f : M ⟶ Z)
  statement: Δ[M] ≫ (f otimesₘ ε[M]) = f ≫ (ρ_ Z).inv
  proof: by
  rw [rightUnitor_inv_naturality]; rw [tensorHom_def']; rw [comul_counit_assoc]

@[reassoc]

中文:
定理 comul_counit_hom
  条件: {Z : C} (f : M ⟶ Z)
  结论: Δ[M] ≫ (f otimesₘ ε[M]) = f ≫ (ρ_ Z).inv
  证明: by
  rw [rightUnitor_inv_naturality]; rw [tensorHom_def']; rw [comul_counit_assoc]

@[reassoc]

Depends on / 依赖: G.IsCoverDense, IsCoverDense, comul_counit_assoc, locallyCoverDense_of_isCoverDense, rightUnitor_inv_naturality, tensorHom_def
-/
theorem comul_counit_hom {Z : C} (f : M ⟶ Z) : Δ[M] ≫ (f otimesₘ ε[M]) = f ≫ (ρ_ Z).inv := by
  rw [rightUnitor_inv_naturality]; rw [tensorHom_def']; rw [comul_counit_assoc]

@[reassoc]
/--
theorem `comul_assoc_flip` / 定理 `comul_assoc_flip`

English:
theorem comul_assoc_flip
  given: (X : C) [ComonObj X]
  proof: by
  simp

中文:
定理 comul_assoc_flip
  条件: (X : C) [余monObj X]
  证明: by
  simp

Depends on / 依赖: G.IsCoverDense, G.IsDenseSubsite, G.restrictedTopology, IsCoverDense, IsDenseSubsite, restrictedTopology
-/
theorem comul_assoc_flip (X : C) [ComonObj X] :
    Δ ≫ Δ ▷ X = Δ ≫ X ◁ Δ ≫ (α_ X X X).inv := by
  simp

end ComonObj

namespace Comon

open MonObj ComonObj

/-- A morphism of comonoid objects. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (M N : Comon C)
  axioms and operations (2):
    - hom : M.X ⟶ N.X
    - [isComonHom_hom : IsComonHom hom]

中文:
结构 态射
  参数: (M N : 余mon C)
  公理与运算 (2 个):
    - hom : M.X ⟶ N.X
    - [isComonHom_hom : 是余mon态射 hom]

Depends on / 依赖: G.IsCoverDense, G.IsDenseSubsite, G.inducedTopology, IsCoverDense, IsDenseSubsite, inducedTopology, infer_instance, restrictedTopology_eq_inducedTopology
-/
structure Hom (M N : Comon C) where
  /-- The underlying morphism of a morphism of comonoid objects. -/
  hom : M.X ⟶ N.X
  [isComonHom_hom : IsComonHom hom]

attribute [instance] Hom.isComonHom_hom

/--
Definition of `Hom.mk'` / `Hom.mk'` 的定义

English:
abbreviation Hom.mk'
  signature: {M N : Comon C} (f : M.X ⟶ N.X)
  body: have : IsComonHom f := ⟨f_counit, f_comul⟩
  .mk f

中文:
缩写 态射.mk'
  签名: {M N : 余mon C} (f : M.X ⟶ N.X)
  定义体: have : IsComonHom f := ⟨f_counit, f_comul⟩
  .mk f

Depends on / 依赖: IsComonHom, cat_disch, f_comul, f_counit
-/
abbrev Hom.mk' {M N : Comon C} (f : M.X ⟶ N.X)
    (f_counit : f ≫ ε[N.X] = ε[M.X] := by cat_disch)
    (f_comul : f ≫ Δ[N.X] = Δ[M.X] ≫ (f otimesₘ f) := by cat_disch) :
    Hom M N :=
  have : IsComonHom f := ⟨f_counit, f_comul⟩
  .mk f

/-- The identity morphism on a comonoid object. -/
@[simps]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (M : Comon C)
  body: 𝟙 M.X

中文:
定义 id
  签名: (M : 余mon C)
  定义体: 𝟙 M.X
-/
def id (M : Comon C) : Hom M M where
  hom := 𝟙 M.X

/--
Instance `homInhabited` / 实例 `homInhabited`

English:
instance homInhabited
  signature: (M : Comon C)
  body: ⟨id M⟩

中文:
实例 homInhabited
  签名: (M : 余mon C)
  定义体: ⟨id M⟩
-/
instance homInhabited (M : Comon C) : Inhabited (Hom M M) :=
  ⟨id M⟩

/-- Composition of morphisms of monoid objects. -/
@[simps]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {M N O : Comon C} (f : Hom M N) (g : Hom N O)
  body: f.hom ≫ g.hom

中文:
定义 comp
  签名: {M N O : 余mon C} (f : 态射 M N) (g : 态射 N O)
  定义体: f.hom ≫ g.hom

Depends on / 依赖: f.hom, g.hom
-/
def comp {M N O : Comon C} (f : Hom M N) (g : Hom N O) : Hom M O where
  hom := f.hom ≫ g.hom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (Comon C)
  body: Hom M N
  id := id
  comp f g := comp f g

中文:
实例 :
  签名: 范畴 (余mon C)
  定义体: Hom M N
  id := id
  comp f g := comp f g
-/
instance : Category (Comon C) where
  Hom M N := Hom M N
  id := id
  comp f g := comp f g

instance {M N : Comon C} (f : M ⟶ N) : IsComonHom f.hom := inferInstanceAs (IsComonHom f.hom)

/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {X Y : Comon C} {f g : X ⟶ Y} (w : f.hom = g.hom)
  statement: f = g
  proof: Hom.ext w

中文:
引理 ext
  条件: {X Y : 余mon C} {f g : X ⟶ Y} (w : f.hom = g.hom)
  结论: f = g
  证明: Hom.ext w
-/
@[ext] lemma ext {X Y : Comon C} {f g : X ⟶ Y} (w : f.hom = g.hom) : f = g := Hom.ext w

/--
theorem `id_hom'` / 定理 `id_hom'`

English:
theorem id_hom'
  given: (M : Comon C)
  statement: (𝟙 M : Hom M M).hom = 𝟙 M.X
  proof: rfl

@[simp]

中文:
定理 id_hom'
  条件: (M : 余mon C)
  结论: (𝟙 M : 态射 M M).hom = 𝟙 M.X
  证明: rfl

@[simp]
-/
@[simp] theorem id_hom' (M : Comon C) : (𝟙 M : Hom M M).hom = 𝟙 M.X := rfl

@[simp]
/--
theorem `comp_hom'` / 定理 `comp_hom'`

English:
theorem comp_hom'
  given: {M N K : Comon C} (f : M ⟶ N) (g : N ⟶ K)
  statement: (f ≫ g).hom = f.hom ≫ g.hom
  proof: rfl

中文:
定理 comp_hom'
  条件: {M N K : 余mon C} (f : M ⟶ N) (g : N ⟶ K)
  结论: (f ≫ g).hom = f.hom ≫ g.hom
  证明: rfl
-/
theorem comp_hom' {M N K : Comon C} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

section

variable (C)

/-- The forgetful functor from comonoid objects to the ambient category. -/
@[simps]
/--
Definition of `forget` / `forget` 的定义

English:
definition forget
  signature: : Comon C ⥤ C where
  body: A.X
  map f := f.hom

中文:
定义 forget
  签名: : 余mon C ⥤ C where
  定义体: A.X
  map f := f.hom
-/
def forget : Comon C ⥤ C where
  obj A := A.X
  map f := f.hom

end

/--
Instance `forget_faithful` / 实例 `forget_faithful`

English:
instance forget_faithful
  signature: : (@forget C _ _).Faithful where

中文:
实例 forget_faithful
  签名: : (@forget C _ _).忠实 where
-/
instance forget_faithful : (@forget C _ _).Faithful where

instance {A B : Comon C} (f : A ⟶ B) [e : IsIso ((forget C).map f)] : IsIso f.hom := e

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget C).ReflectsIsomorphisms
  body: ⟨⟨{ hom := inv f.hom }, by cat_disch⟩⟩

中文:
实例 :
  签名: (forget C).反映同构
  定义体: ⟨⟨{ hom := inv f.hom }, by cat_disch⟩⟩

Depends on / 依赖: cat_disch, f.hom
-/
instance : (forget C).ReflectsIsomorphisms where
  reflects f e :=
    ⟨⟨{ hom := inv f.hom }, by cat_disch⟩⟩

/-- Construct an isomorphism of comonoids by giving an isomorphism between the underlying objects
and checking compatibility with counit and comultiplication only in the forward direction.
-/
@[simps]
/--
Definition of `mkIso'` / `mkIso'` 的定义

English:
definition mkIso'
  signature: {M N : Comon C} (f : M.X ≅ N.X) [IsComonHom f.hom]
  body: Hom.mk f.hom
  inv := Hom.mk f.inv

中文:
定义 mkIso'
  签名: {M N : 余mon C} (f : M.X ≅ N.X) [是余mon态射 f.hom]
  定义体: Hom.mk f.hom
  inv := Hom.mk f.inv

Depends on / 依赖: Hom.mk, f.hom
-/
def mkIso' {M N : Comon C} (f : M.X ≅ N.X) [IsComonHom f.hom] : M ≅ N where
  hom := Hom.mk f.hom
  inv := Hom.mk f.inv

/-- Construct an isomorphism of comonoids by giving an isomorphism between the underlying objects
and checking compatibility with counit and comultiplication only in the forward direction.
-/
@[simps]
/--
Definition of `mkIso` / `mkIso` 的定义

English:
definition mkIso
  signature: {M N : Comon C} (f : M.X ≅ N.X) (f_counit : f.hom ≫ ε[N.X] = ε[M.X] := by cat_disch)
  body: have : IsComonHom f.hom := ⟨f_counit, f_comul⟩
  ⟨⟨f.hom⟩, ⟨f.inv⟩, by cat_disch, by cat_disch⟩

中文:
定义 mkIso
  签名: {M N : 余mon C} (f : M.X ≅ N.X) (f_counit : f.hom ≫ ε[N.X] = ε[M.X] := by cat_disch)
  定义体: have : IsComonHom f.hom := ⟨f_counit, f_comul⟩
  ⟨⟨f.hom⟩, ⟨f.inv⟩, by cat_disch, by cat_disch⟩

Depends on / 依赖: IsComonHom, cat_disch, f.hom, f.inv, f_comul, f_counit
-/
def mkIso {M N : Comon C} (f : M.X ≅ N.X) (f_counit : f.hom ≫ ε[N.X] = ε[M.X] := by cat_disch)
    (f_comul : f.hom ≫ Δ[N.X] = Δ[M.X] ≫ (f.hom otimesₘ f.hom) := by cat_disch) : M ≅ N :=
  have : IsComonHom f.hom := ⟨f_counit, f_comul⟩
  ⟨⟨f.hom⟩, ⟨f.inv⟩, by cat_disch, by cat_disch⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simps]
/--
Instance `uniqueHomToTrivial` / 实例 `uniqueHomToTrivial`

English:
instance uniqueHomToTrivial
  signature: (A : Comon C)
  body: ε[A.X]
  default.isComonHom_hom.hom_comul := by simp [unitors_inv_equal]
  uniq f := by
    ext
    rw [← Category.comp_id f.hom]
    dsimp only [trivial_X]
    rw [← trivial_comon_counit]; rw [IsComonHom.hom_counit]

中文:
实例 uniqueHomToTrivial
  签名: (A : 余mon C)
  定义体: ε[A.X]
  default.isComonHom_hom.hom_comul := by simp [unitors_inv_equal]
  uniq f := by
    ext
    rw [← Category.comp_id f.hom]
    dsimp only [trivial_X]
    rw [← trivial_comon_counit]; rw [IsComonHom.hom_counit]
-/
instance uniqueHomToTrivial (A : Comon C) : Unique (A ⟶ trivial C) where
  default.hom := ε[A.X]
  default.isComonHom_hom.hom_comul := by simp [unitors_inv_equal]
  uniq f := by
    ext
    rw [← Category.comp_id f.hom]
    dsimp only [trivial_X]
    rw [← trivial_comon_counit]; rw [IsComonHom.hom_counit]

open CategoryTheory.Limits

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasTerminal (Comon C)
  body: hasTerminal_of_unique (trivial C)

中文:
实例 :
  签名: 有终止 (余mon C)
  定义体: hasTerminal_of_unique (trivial C)

Depends on / 依赖: hasTerminal_of_unique
-/
instance : HasTerminal (Comon C) :=
  hasTerminal_of_unique (trivial C)

open Opposite

/--
Definition of `ComonToMonOpOpObjMon` / `ComonToMonOpOpObjMon` 的定义

English:
abbreviation ComonToMonOpOpObjMon
  signature: (A : Comon C)
  body: ε[A.X].op
  mul := Δ[A.X].op
  one_mul := by
    rw [← op_whiskerRight]; rw [← op_comp]; rw [counit_comul]
    rfl
  mul_one := by
    rw [← op_whiskerLeft]; rw [← op_comp]; rw [comul_counit]
    rfl
  mul_assoc := by
    rw [← op_inv_associator]; rw [← op_whiskerRight]; rw [← op_comp]; rw [← op_whiskerLeft]; rw [← op_comp]; rw [comul_assoc_flip]; rw [op_comp]; rw [op_comp_assoc]
    rfl

中文:
缩写 ComonToMonOpOpObjMon
  签名: (A : 余mon C)
  定义体: ε[A.X].op
  mul := Δ[A.X].op
  one_mul := by
    rw [← op_whiskerRight]; rw [← op_comp]; rw [counit_comul]
    rfl
  mul_one := by
    rw [← op_whiskerLeft]; rw [← op_comp]; rw [comul_counit]
    rfl
  mul_assoc := by
    rw [← op_inv_associator]; rw [← op_whiskerRight]; rw [← op_comp]; rw [← op_whiskerLeft]; rw [← op_comp]; rw [comul_assoc_flip]; rw [op_comp]; rw [op_comp_assoc]
    rfl
-/
abbrev ComonToMonOpOpObjMon (A : Comon C) : MonObj (op A.X) where
  one := ε[A.X].op
  mul := Δ[A.X].op
  one_mul := by
    rw [← op_whiskerRight]; rw [← op_comp]; rw [counit_comul]
    rfl
  mul_one := by
    rw [← op_whiskerLeft]; rw [← op_comp]; rw [comul_counit]
    rfl
  mul_assoc := by
    rw [← op_inv_associator]; rw [← op_whiskerRight]; rw [← op_comp]; rw [← op_whiskerLeft]; rw [← op_comp]; rw [comul_assoc_flip]; rw [op_comp]; rw [op_comp_assoc]
    rfl

/--
Definition of `ComonToMonOpOpObj` / `ComonToMonOpOpObj` 的定义

English:
definition ComonToMonOpOpObj
  signature: (A : Comon C)
  body: op A.X
  mon := ComonToMonOpOpObjMon A

中文:
定义 ComonToMonOpOpObj
  签名: (A : 余mon C)
  定义体: op A.X
  mon := ComonToMonOpOpObjMon A
-/
@[simps] def ComonToMonOpOpObj (A : Comon C) : Mon Cᵒᵖ where
  X := op A.X
  mon := ComonToMonOpOpObjMon A

set_option backward.defeqAttrib.useBackward true in
variable (C) in
/--
Definition of `ComonToMonOpOp` / `ComonToMonOpOp` 的定义

English:
definition ComonToMonOpOp
  signature: : Comon C ⥤ (Mon Cᵒᵖ)ᵒᵖ where
  body: op (ComonToMonOpOpObj A)
map := fun f => op
    { hom := f.hom.op
      isMonHom_hom.one_hom := by apply Quiver.Hom.unop_inj; simp
      isMonHom_hom.mul_hom := by apply Quiver.Hom.unop_inj; simp }

中文:
定义 ComonToMonOpOp
  签名: : 余mon C ⥤ (幺半群 Cᵒᵖ)ᵒᵖ where
  定义体: op (ComonToMonOpOpObj A)
map := fun f => op
    { hom := f.hom.op
      isMonHom_hom.one_hom := by apply Quiver.Hom.unop_inj; simp
      isMonHom_hom.mul_hom := by apply Quiver.Hom.unop_inj; simp }
-/
@[simps] def ComonToMonOpOp : Comon C ⥤ (Mon Cᵒᵖ)ᵒᵖ where
  obj A := op (ComonToMonOpOpObj A)
map := fun f => op
    { hom := f.hom.op
      isMonHom_hom.one_hom := by apply Quiver.Hom.unop_inj; simp
      isMonHom_hom.mul_hom := by apply Quiver.Hom.unop_inj; simp }

/--
Definition of `MonOpOpToComonObjComon` / `MonOpOpToComonObjComon` 的定义

English:
abbreviation MonOpOpToComonObjComon
  signature: (A : Mon Cᵒᵖ)
  body: η[A.X].unop
  comul := μ[A.X].unop
  counit_comul := by rw [← unop_whiskerRight, ← unop_comp, MonObj.one_mul]; rfl
  comul_counit := by rw [← unop_whiskerLeft, ← unop_comp, MonObj.mul_one]; rfl
  comul_assoc := by
    rw [← unop_whiskerRight]; rw [← unop_whiskerLeft]; rw [← unop_comp_assoc]; rw [← unop_comp]; rw [MonObj.mul_assoc_flip]
    rfl

中文:
缩写 MonOpOpToComonObjComon
  签名: (A : 幺半群 Cᵒᵖ)
  定义体: η[A.X].unop
  comul := μ[A.X].unop
  counit_comul := by rw [← unop_whiskerRight, ← unop_comp, MonObj.one_mul]; rfl
  comul_counit := by rw [← unop_whiskerLeft, ← unop_comp, MonObj.mul_one]; rfl
  comul_assoc := by
    rw [← unop_whiskerRight]; rw [← unop_whiskerLeft]; rw [← unop_comp_assoc]; rw [← unop_comp]; rw [MonObj.mul_assoc_flip]
    rfl
-/
abbrev MonOpOpToComonObjComon (A : Mon Cᵒᵖ) : ComonObj (unop A.X) where
  counit := η[A.X].unop
  comul := μ[A.X].unop
  counit_comul := by rw [← unop_whiskerRight, ← unop_comp, MonObj.one_mul]; rfl
  comul_counit := by rw [← unop_whiskerLeft, ← unop_comp, MonObj.mul_one]; rfl
  comul_assoc := by
    rw [← unop_whiskerRight]; rw [← unop_whiskerLeft]; rw [← unop_comp_assoc]; rw [← unop_comp]; rw [MonObj.mul_assoc_flip]
    rfl

/--
Definition of `MonOpOpToComonObj` / `MonOpOpToComonObj` 的定义

English:
definition MonOpOpToComonObj
  signature: (A : Mon Cᵒᵖ)
  body: unop A.X
  comon := MonOpOpToComonObjComon A

中文:
定义 MonOpOpToComonObj
  签名: (A : 幺半群 Cᵒᵖ)
  定义体: unop A.X
  comon := MonOpOpToComonObjComon A
-/
@[simps] def MonOpOpToComonObj (A : Mon Cᵒᵖ) : Comon C where
  X := unop A.X
  comon := MonOpOpToComonObjComon A

variable (C)

set_option backward.defeqAttrib.useBackward true in
/--
The contravariant functor turning monoid objects in the opposite category into comonoid objects.
-/
@[simps]
/--
Definition of `MonOpOpToComon` / `MonOpOpToComon` 的定义

English:
definition MonOpOpToComon
  signature: : (Mon Cᵒᵖ)ᵒᵖ ⥤ Comon C where
  body: MonOpOpToComonObj (unop A)
  map := fun f =>
    { hom := f.unop.hom.unop
      isComonHom_hom.hom_counit := by apply Quiver.Hom.op_inj; simp
      isComonHom_hom.hom_comul := by apply Quiver.Hom.op_inj; simp [op_tensorHom] }

中文:
定义 MonOpOpToComon
  签名: : (幺半群 Cᵒᵖ)ᵒᵖ ⥤ 余mon C where
  定义体: MonOpOpToComonObj (unop A)
  map := fun f =>
    { hom := f.unop.hom.unop
      isComonHom_hom.hom_counit := by apply Quiver.Hom.op_inj; simp
      isComonHom_hom.hom_comul := by apply Quiver.Hom.op_inj; simp [op_tensorHom] }

Depends on / 依赖: MonOpOpToComonObj
-/
def MonOpOpToComon : (Mon Cᵒᵖ)ᵒᵖ ⥤ Comon C where
  obj A := MonOpOpToComonObj (unop A)
  map := fun f =>
    { hom := f.unop.hom.unop
      isComonHom_hom.hom_counit := by apply Quiver.Hom.op_inj; simp
      isComonHom_hom.hom_comul := by apply Quiver.Hom.op_inj; simp [op_tensorHom] }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Comonoid objects are contravariantly equivalent to monoid objects in the opposite category.
-/
@[simps]
/--
Definition of `Comon_EquivMon_OpOp` / `Comon_EquivMon_OpOp` 的定义

English:
definition Comon_EquivMon_OpOp
  signature: : Comon C ≌ (Mon Cᵒᵖ)ᵒᵖ where
  body: ComonToMonOpOp C
  inverse := MonOpOpToComon C
  unitIso := NatIso.ofComponents fun _ => .refl _
  counitIso := NatIso.ofComponents fun _ => .refl _

#adaptation_note /-- After https://github.com/leanprover/lean4/pull/12179
the simpNF linter complains about `monoidal_tensorObj_comon_counit` being `@[simp]`.
So we spell out all the other ones.
-/
#adaptation_note

中文:
定义 Comon_EquivMon_OpOp
  签名: : 余mon C ≌ (幺半群 Cᵒᵖ)ᵒᵖ where
  定义体: ComonToMonOpOp C
  inverse := MonOpOpToComon C
  unitIso := NatIso.ofComponents fun _ => .refl _
  counitIso := NatIso.ofComponents fun _ => .refl _

#adaptation_note /-- After https://github.com/leanprover/lean4/pull/12179
the simpNF linter complains about `monoidal_tensorObj_comon_counit` being `@[simp]`.
So we spell out all the other ones.
-/
#adaptation_note

Depends on / 依赖: ComonToMonOpOp
-/
def Comon_EquivMon_OpOp : Comon C ≌ (Mon Cᵒᵖ)ᵒᵖ where
  functor := ComonToMonOpOp C
  inverse := MonOpOpToComon C
  unitIso := NatIso.ofComponents fun _ => .refl _
  counitIso := NatIso.ofComponents fun _ => .refl _

#adaptation_note /-- After https://github.com/leanprover/lean4/pull/12179
the simpNF linter complains about `monoidal_tensorObj_comon_counit` being `@[simp]`.
So we spell out all the other ones.
-/
#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/--
Comonoid objects in a braided category form a monoidal category.

This definition is via transporting back and forth to monoids in the opposite category.
-/
@[simps!
  tensorObj_X tensorObj_comon_comul
  whiskerLeft_hom whiskerRight_hom
  tensorHom_hom
  tensorUnit_X tensorUnit_comon_counit tensorUnit_comon_comul
  associator_hom_hom associator_inv_hom
  leftUnitor_hom_hom leftUnitor_inv_hom
  rightUnitor_hom_hom rightUnitor_inv_hom]
/--
Instance `monoidal` / 实例 `monoidal`

English:
instance monoidal
  signature: [BraidedCategory C]
  body: Monoidal.transport (Comon_EquivMon_OpOp C).symm

中文:
实例 monoidal
  签名: [辫范畴 C]
  定义体: Monoidal.transport (Comon_EquivMon_OpOp C).symm

Depends on / 依赖: Comon_EquivMon_OpOp, Monoidal, Monoidal.transport, transport
-/
instance monoidal [BraidedCategory C] : MonoidalCategory (Comon C) :=
  Monoidal.transport (Comon_EquivMon_OpOp C).symm

variable {C} [BraidedCategory C]

/--
theorem `tensorObj_X` / 定理 `tensorObj_X`

English:
theorem tensorObj_X
  given: (A B : Comon C)
  statement: (A otimes B).X = A.X otimes B.X
  proof: rfl

中文:
定理 tensorObj_X
  条件: (A B : 余mon C)
  结论: (A otimes B).X = A.X otimes B.X
  证明: rfl
-/
theorem tensorObj_X (A B : Comon C) : (A otimes B).X = A.X otimes B.X := rfl

instance (A B : C) [ComonObj A] [ComonObj B] : ComonObj (A otimes B) :=
inferInstanceAs ComonObj (Comon.mk A otimes Comon.mk B).X

@[simp]
/--
theorem `tensorObj_counit` / 定理 `tensorObj_counit`

English:
theorem tensorObj_counit
  given: (A B : C) [ComonObj A] [ComonObj B]
  proof: rfl

中文:
定理 tensorObj_counit
  条件: (A B : C) [余monObj A] [余monObj B]
  证明: rfl
-/
theorem tensorObj_counit (A B : C) [ComonObj A] [ComonObj B] :
    ε[A otimes B] = (ε[A] otimesₘ ε[B]) ≫ (fun_ _).hom :=
  rfl

/--
theorem `tensorObj_comul'` / 定理 `tensorObj_comul'`

English:
theorem tensorObj_comul'
  given: (A B : C) [ComonObj A] [ComonObj B]
  proof: by
  rfl

中文:
定理 tensorObj_comul'
  条件: (A B : C) [余monObj A] [余monObj B]
  证明: by
  rfl
-/
theorem tensorObj_comul' (A B : C) [ComonObj A] [ComonObj B] :
    Δ[A otimes B] =
      (Δ[A] otimesₘ Δ[B]) ≫ (tensorμ (op A) (op B) (op A) (op B)).unop := by
  rfl

/--
The comultiplication on the tensor product of two comonoids is
the tensor product of the comultiplications followed by the tensor strength
(to shuffle the factors back into order).
-/
@[simp]
/--
theorem `tensorObj_comul` / 定理 `tensorObj_comul`

English:
theorem tensorObj_comul
  given: (A B : C) [ComonObj A] [ComonObj B]
  proof: by
  simp [tensorObj_comul']

中文:
定理 tensorObj_comul
  条件: (A B : C) [余monObj A] [余monObj B]
  证明: by
  simp [tensorObj_comul']

Depends on / 依赖: tensorObj_comul
-/
theorem tensorObj_comul (A B : C) [ComonObj A] [ComonObj B] :
    Δ[A otimes B] = (Δ[A] otimesₘ Δ[B]) ≫ tensorμ A A B B := by
  simp [tensorObj_comul']

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget C).Monoidal
  body: Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ => Iso.refl _ }

中文:
实例 :
  签名: (forget C).幺半群
  定义体: Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ => Iso.refl _ }

Depends on / 依赖: CoreMonoidal, Functor, Functor.CoreMonoidal.toMonoidal, Iso.refl, toMonoidal
-/
instance : (forget C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ => Iso.refl _ }

open Functor.LaxMonoidal Functor.OplaxMonoidal

/--
theorem `forget_ε` / 定理 `forget_ε`

English:
theorem forget_ε
  statement: «ε» (forget C) = 𝟙 (𝟙_ C)
  proof: rfl

中文:
定理 forget_ε
  结论: «ε» (forget C) = 𝟙 (𝟙_ C)
  证明: rfl
-/
@[simp] theorem forget_ε : «ε» (forget C) = 𝟙 (𝟙_ C) := rfl
/--
theorem `forget_η` / 定理 `forget_η`

English:
theorem forget_η
  statement: «η» (forget C) = 𝟙 (𝟙_ C)
  proof: rfl

中文:
定理 forget_η
  结论: «η» (forget C) = 𝟙 (𝟙_ C)
  证明: rfl
-/
@[simp] theorem forget_η : «η» (forget C) = 𝟙 (𝟙_ C) := rfl
/--
theorem `forget_μ` / 定理 `forget_μ`

English:
theorem forget_μ
  given: (X Y : Comon C)
  statement: «μ» (forget C) X Y = 𝟙 (X.X otimes Y.X)
  proof: rfl

中文:
定理 forget_μ
  条件: (X Y : 余mon C)
  结论: «μ» (forget C) X Y = 𝟙 (X.X otimes Y.X)
  证明: rfl
-/
@[simp] theorem forget_μ (X Y : Comon C) : «μ» (forget C) X Y = 𝟙 (X.X otimes Y.X) := rfl
/--
theorem `forget_δ` / 定理 `forget_δ`

English:
theorem forget_δ
  given: (X Y : Comon C)
  statement: δ (forget C) X Y = 𝟙 (X.X otimes Y.X)
  proof: rfl

中文:
定理 forget_δ
  条件: (X Y : 余mon C)
  结论: δ (forget C) X Y = 𝟙 (X.X otimes Y.X)
  证明: rfl
-/
@[simp] theorem forget_δ (X Y : Comon C) : δ (forget C) X Y = 𝟙 (X.X otimes Y.X) := rfl

end Comon

namespace Functor

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D]

open OplaxMonoidal ComonObj IsComonHom

/--
Definition of `obj.instComonObj` / `obj.instComonObj` 的定义

English:
abbreviation obj.instComonObj
  signature: (A : C) [ComonObj A] (F : C ⥤ D) [F.OplaxMonoidal]
  body: F.map ε[A] ≫ η F
  comul := F.map Δ[A] ≫ δ F _ _
  counit_comul := by
    simp_rw [comp_whiskerRight, Category.assoc, δ_natural_left_assoc, left_unitality,
      ← F.map_comp_assoc, counit_comul]
  comul_counit := by
    simp_rw [MonoidalCategory.whiskerLeft_comp, Category.assoc, δ_natural_right_assoc,
      right_unitality, ← F.map_comp_assoc, comul_counit]
  comul_assoc := by
    simp_rw [comp_whiskerRight, Category.assoc, δ_natural_left_assoc,
      MonoidalCategory.whiskerLeft_comp, δ_natural_right_assoc,
      ← F.map_comp_assoc, comul_assoc, F.map_comp, Category.assoc, associativity]

中文:
缩写 obj.instComonObj
  签名: (A : C) [余monObj A] (F : C ⥤ D) [F.反松弛幺半群]
  定义体: F.map ε[A] ≫ η F
  comul := F.map Δ[A] ≫ δ F _ _
  counit_comul := by
    simp_rw [comp_whiskerRight, Category.assoc, δ_natural_left_assoc, left_unitality,
      ← F.map_comp_assoc, counit_comul]
  comul_counit := by
    simp_rw [MonoidalCategory.whiskerLeft_comp, Category.assoc, δ_natural_right_assoc,
      right_unitality, ← F.map_comp_assoc, comul_counit]
  comul_assoc := by
    simp_rw [comp_whiskerRight, Category.assoc, δ_natural_left_assoc,
      MonoidalCategory.whiskerLeft_comp, δ_natural_right_assoc,
      ← F.map_comp_assoc, comul_assoc, F.map_comp, Category.assoc, associativity]

Depends on / 依赖: F.map
-/
abbrev obj.instComonObj (A : C) [ComonObj A] (F : C ⥤ D) [F.OplaxMonoidal] :
    ComonObj (F.obj A) where
  counit := F.map ε[A] ≫ η F
  comul := F.map Δ[A] ≫ δ F _ _
  counit_comul := by
    simp_rw [comp_whiskerRight, Category.assoc, δ_natural_left_assoc, left_unitality,
      ← F.map_comp_assoc, counit_comul]
  comul_counit := by
    simp_rw [MonoidalCategory.whiskerLeft_comp, Category.assoc, δ_natural_right_assoc,
      right_unitality, ← F.map_comp_assoc, comul_counit]
  comul_assoc := by
    simp_rw [comp_whiskerRight, Category.assoc, δ_natural_left_assoc,
      MonoidalCategory.whiskerLeft_comp, δ_natural_right_assoc,
      ← F.map_comp_assoc, comul_assoc, F.map_comp, Category.assoc, associativity]

attribute [local instance] obj.instComonObj

/--
lemma `obj.ε_def` / 引理 `obj.ε_def`

English:
lemma obj.ε_def
  given: (F : C ⥤ D) [F.OplaxMonoidal] (X : C) [ComonObj X]
  proof: rfl

中文:
引理 obj.ε_def
  条件: (F : C ⥤ D) [F.反松弛幺半群] (X : C) [余monObj X]
  证明: rfl
-/
@[reassoc, simp] lemma obj.ε_def (F : C ⥤ D) [F.OplaxMonoidal] (X : C) [ComonObj X] :
    ε[F.obj X] = F.map ε ≫ η F :=
  rfl

/--
lemma `obj.Δ_def` / 引理 `obj.Δ_def`

English:
lemma obj.Δ_def
  given: (F : C ⥤ D) [F.OplaxMonoidal] (X : C) [ComonObj X]
  proof: rfl

中文:
引理 obj.Δ_def
  条件: (F : C ⥤ D) [F.反松弛幺半群] (X : C) [余monObj X]
  证明: rfl
-/
@[reassoc, simp] lemma obj.Δ_def (F : C ⥤ D) [F.OplaxMonoidal] (X : C) [ComonObj X] :
    Δ[F.obj X] = F.map Δ ≫ δ F _ _ :=
  rfl

/--
Instance `map.instIsComon_Hom` / 实例 `map.instIsComon_Hom`

English:
instance map.instIsComon_Hom
  body: by dsimp; rw [← F.map_comp_assoc, hom_counit]
  hom_comul := by
    dsimp
    rw [Category.assoc]; rw [δ_natural]; rw [← F.map_comp_assoc]; rw [← F.map_comp_assoc]; rw [hom_comul]

中文:
实例 map.instIsComon_Hom
  定义体: by dsimp; rw [← F.map_comp_assoc, hom_counit]
  hom_comul := by
    dsimp
    rw [Category.assoc]; rw [δ_natural]; rw [← F.map_comp_assoc]; rw [← F.map_comp_assoc]; rw [hom_comul]

Depends on / 依赖: Category, Category.assoc, F.map_comp_assoc, hom_comul, hom_counit, map_comp_assoc
-/
instance map.instIsComon_Hom
    (F : C ⥤ D) [F.OplaxMonoidal]
    {X Y : C} [ComonObj X] [ComonObj Y] (f : X ⟶ Y) [IsComonHom f] :
    IsComonHom (F.map f) where
  hom_counit := by dsimp; rw [← F.map_comp_assoc, hom_counit]
  hom_comul := by
    dsimp
    rw [Category.assoc]; rw [δ_natural]; rw [← F.map_comp_assoc]; rw [← F.map_comp_assoc]; rw [hom_comul]

/-- An oplax monoidal functor takes comonoid objects to comonoid objects.

That is, an oplax monoidal functor `F : C ⥤ D` induces a functor `Comon C ⥤ Comon D`.
-/
@[simps]
/--
Definition of `mapComon` / `mapComon` 的定义

English:
definition mapComon
  signature: (F : C ⥤ D) [F.OplaxMonoidal]
  body: { X := F.obj A.X }
  map f :=
    { hom := F.map f.hom }
  map_id A := by ext; simp
  map_comp f g := by ext; simp

中文:
定义 mapComon
  签名: (F : C ⥤ D) [F.反松弛幺半群]
  定义体: { X := F.obj A.X }
  map f :=
    { hom := F.map f.hom }
  map_id A := by ext; simp
  map_comp f g := by ext; simp

Depends on / 依赖: F.map, F.obj, f.hom, map_comp, map_id
-/
def mapComon (F : C ⥤ D) [F.OplaxMonoidal] : Comon C ⥤ Comon D where
  obj A :=
    { X := F.obj A.X }
  map f :=
    { hom := F.map f.hom }
  map_id A := by ext; simp
  map_comp f g := by ext; simp

-- TODO We haven't yet set up the category structure on `OplaxMonoidalFunctor C D`
-- and so can't state `mapComonFunctor : OplaxMonoidalFunctor C D ⥤ Comon C ⥤ Comon D`.

end Functor

variable [BraidedCategory.{v₁} C]

/--
Definition of `IsCommComonObj` / `IsCommComonObj` 的定义

English:
class IsCommComonObj
  parameters: (X : C) [ComonObj X]
  axioms and operations (1):
    - comul_comm((X)) : Δ ≫ (β_ X X).hom = Δ  [default: by cat_disch]

中文:
类 是交换余monObj
  参数: (X : C) [余monObj X]
  公理与运算 (1 个):
    - comul_comm((X)) : Δ ≫ (β_ X X).hom = Δ  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
class IsCommComonObj (X : C) [ComonObj X] where
  comul_comm (X) : Δ ≫ (β_ X X).hom = Δ := by cat_disch

open scoped ComonObj

attribute [reassoc (attr := simp)] IsCommComonObj.comul_comm

end CategoryTheory
