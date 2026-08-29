/-
Copyright (c) 2025 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
module

public import Mathlib.CategoryTheory.Monoidal.Comon_
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-!
# The category of commutative comonoids in a braided monoidal category.

We define the category of commutative comonoid objects in a braided monoidal category `C`.

## Main definitions

* `CommComon C` - The bundled structure of commutative comonoid objects

## Tags

comonoid, commutative, braided
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃ u

namespace CategoryTheory

open MonoidalCategory ComonObj

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C] [BraidedCategory.{v₁} C]

variable (C) in
/--
Definition of `CommComon` / `CommComon` 的定义

English:
structure CommComon
  parameters: where
  axioms and operations (3):
    - X : C
    - [comon : ComonObj X]
    - [comm : IsCommComonObj X]

中文:
结构 交换余mon
  参数: where
  公理与运算 (3 个):
    - X : C
    - [comon : 余monObj X]
    - [comm : 是交换余monObj X]
-/
structure CommComon where
  /-- The underlying object in the ambient monoidal category -/
  X : C
  [comon : ComonObj X]
  [comm : IsCommComonObj X]

attribute [instance] CommComon.comon CommComon.comm

namespace CommComon

/-- A commutative comonoid object is a comonoid object. -/
@[simps X]
/--
Definition of `toComon` / `toComon` 的定义

English:
definition toComon
  signature: (A : CommComon C)
  body: ⟨A.X⟩

中文:
定义 toComon
  签名: (A : 交换余mon C)
  定义体: ⟨A.X⟩
-/
def toComon (A : CommComon C) : Comon C := ⟨A.X⟩

section

attribute [local instance] ComonObj.instTensorUnit in
/--
Instance `instCommComonObjUnit` / 实例 `instCommComonObjUnit`

English:
instance instCommComonObjUnit
  signature: : IsCommComonObj (𝟙_ C) where
  body: by simp [← unitors_equal]

中文:
实例 instCommComonObjUnit
  签名: : 是交换余monObj (𝟙_ C) where
  定义体: by simp [← unitors_equal]

Depends on / 依赖: unitors_equal
-/
instance instCommComonObjUnit : IsCommComonObj (𝟙_ C) where
  comul_comm := by simp [← unitors_equal]

end

attribute [local instance] ComonObj.instTensorUnit in
variable (C) in
/-- The trivial commutative comonoid object. We later show this is initial in `CommComon C`. -/
@[simps!]
/--
Definition of `trivial` / `trivial` 的定义

English:
definition trivial
  signature: : CommComon C
  body: mk (𝟙_ C)

中文:
定义 trivial
  签名: : 交换余mon C
  定义体: mk (𝟙_ C)
-/
def trivial : CommComon C := mk (𝟙_ C)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (CommComon C)
  body: ⟨trivial C⟩

中文:
实例 :
  签名: 可居 (交换余mon C)
  定义体: ⟨trivial C⟩
-/
instance : Inhabited (CommComon C) :=
  ⟨trivial C⟩

variable {M : CommComon C}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (CommComon C)
  body: inferInstanceAs (Category (InducedCategory _ CommComon.toComon))

@[simp]

中文:
实例 :
  签名: 范畴 (交换余mon C)
  定义体: inferInstanceAs (Category (InducedCategory _ CommComon.toComon))

@[simp]

Depends on / 依赖: Category, CommComon, CommComon.toComon, InducedCategory, toComon
-/
instance : Category (CommComon C) :=
  inferInstanceAs (Category (InducedCategory _ CommComon.toComon))

@[simp]
/--
theorem `id_hom` / 定理 `id_hom`

English:
theorem id_hom
  given: (A : CommComon C)
  statement: Comon.Hom.hom (InducedCategory.Hom.hom (𝟙 A)) = 𝟙 A.X
  proof: rfl

@[simp]

中文:
定理 id_hom
  条件: (A : 交换余mon C)
  结论: 余mon.态射.hom (InducedCategory.态射.hom (𝟙 A)) = 𝟙 A.X
  证明: rfl

@[simp]
-/
theorem id_hom (A : CommComon C) : Comon.Hom.hom (InducedCategory.Hom.hom (𝟙 A)) = 𝟙 A.X :=
  rfl

@[simp]
/--
theorem `comp_hom` / 定理 `comp_hom`

English:
theorem comp_hom
  given: {R S T : CommComon C} (f : R ⟶ S) (g : S ⟶ T)
  proof: rfl

@[ext]

中文:
定理 comp_hom
  条件: {R S T : 交换余mon C} (f : R ⟶ S) (g : S ⟶ T)
  证明: rfl

@[ext]
-/
theorem comp_hom {R S T : CommComon C} (f : R ⟶ S) (g : S ⟶ T) :
    Comon.Hom.hom (f ≫ g).hom = f.hom.hom ≫ g.hom.hom :=
  rfl

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {A B : CommComon C} (f g : A ⟶ B) (h : f.hom.hom = g.hom.hom)
  statement: f = g
  proof: InducedCategory.hom_ext (Comon.Hom.ext h)

中文:
引理 hom_ext
  条件: {A B : 交换余mon C} (f g : A ⟶ B) (h : f.hom.hom = g.hom.hom)
  结论: f = g
  证明: InducedCategory.hom_ext (Comon.Hom.ext h)

Depends on / 依赖: Comon.Hom.ext, InducedCategory, InducedCategory.hom_ext, hom_ext
-/
lemma hom_ext {A B : CommComon C} (f g : A ⟶ B) (h : f.hom.hom = g.hom.hom) : f = g :=
  InducedCategory.hom_ext (Comon.Hom.ext h)

section

variable (C)

/-- The forgetful functor from commutative comonoid objects to comonoid objects. -/
@[simps!]
/--
Definition of `forget₂Comon` / `forget₂Comon` 的定义

English:
definition forget₂Comon
  signature: : CommComon C ⥤ Comon C
  body: inducedFunctor _

中文:
定义 forget₂Comon
  签名: : 交换余mon C ⥤ 余mon C
  定义体: inducedFunctor _

Depends on / 依赖: inducedFunctor
-/
def forget₂Comon : CommComon C ⥤ Comon C :=
  inducedFunctor _

end

end CommComon

instance {C : Type*} [Category* C] [MonoidalCategory C] [SymmetricCategory C]
    (A B : C) [ComonObj A] [ComonObj B]
    [IsCommComonObj A] [IsCommComonObj B] : IsCommComonObj (A otimes B) where
  comul_comm := by
    rw [Comon.tensorObj_comul]; rw [Category.assoc]; rw [SymmetricCategory.tensorμ_braid_swap]
    simp

end CategoryTheory
