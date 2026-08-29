/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.CategoryTheory.Monoidal.CommMon_

/-!
# The category of commutative groups in a Cartesian monoidal category
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory Category Limits MonoidalCategory CartesianMonoidalCategory Mon Grp CommMon
open MonObj

namespace CategoryTheory
variable (C : Type u₁) [Category.{v₁} C] [CartesianMonoidalCategory.{v₁} C] [BraidedCategory C]

/--
Definition of `CommGrp` / `CommGrp` 的定义

English:
structure CommGrp
  parameters: where
  axioms and operations (3):
    - X : C
    - [grp : GrpObj X]
    - [comm : IsCommMonObj X]

中文:
结构 CommGrp
  参数: where
  公理与运算 (3 个):
    - X : C
    - [grp : GrpObj X]
    - [comm : IsCommMonObj X]
-/
structure CommGrp where
  /-- The underlying object in the ambient monoidal category -/
  X : C
  [grp : GrpObj X]
  [comm : IsCommMonObj X]

attribute [instance] CommGrp.grp CommGrp.comm

namespace CommGrp

variable {C}

/-- A commutative group object is a group object. -/
@[simps -isSimp X]
/--
Definition of `toGrp` / `toGrp` 的定义

English:
abbreviation toGrp
  signature: (A : CommGrp C)
  body: ⟨A.X⟩

中文:
缩写 toGrp
  签名: (A : CommGrp C)
  定义体: ⟨A.X⟩
-/
abbrev toGrp (A : CommGrp C) : Grp C := ⟨A.X⟩

/-- A commutative group object is a commutative monoid object. -/
@[simps X]
/--
Definition of `toCommMon` / `toCommMon` 的定义

English:
definition toCommMon
  signature: (A : CommGrp C)
  body: ⟨A.X⟩

中文:
定义 toCommMon
  签名: (A : CommGrp C)
  定义体: ⟨A.X⟩
-/
def toCommMon (A : CommGrp C) : CommMon C := ⟨A.X⟩

/--
Definition of `toMon` / `toMon` 的定义

English:
abbreviation toMon
  signature: (A : CommGrp C)
  body: (toCommMon A).toMon

中文:
缩写 toMon
  签名: (A : CommGrp C)
  定义体: (toCommMon A).toMon

Depends on / 依赖: toCommMon
-/
abbrev toMon (A : CommGrp C) : Mon C := (toCommMon A).toMon

variable (C) in
/-- The trivial commutative group object. -/
@[simps!]
/--
Definition of `trivial` / `trivial` 的定义

English:
definition trivial
  signature: : CommGrp C
  body: { X := 𝟙_ C }

中文:
定义 trivial
  签名: : CommGrp C
  定义体: { X := 𝟙_ C }
-/
def trivial : CommGrp C := { X := 𝟙_ C }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (CommGrp C)
  body: trivial C

中文:
实例 :
  签名: Inhabited (CommGrp C)
  定义体: trivial C
-/
instance : Inhabited (CommGrp C) where
  default := trivial C

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (CommGrp C)
  body: inferInstanceAs (Category (InducedCategory _ CommGrp.toGrp))

@[simp]

中文:
实例 :
  签名: Category (CommGrp C)
  定义体: inferInstanceAs (Category (InducedCategory _ CommGrp.toGrp))

@[simp]

Depends on / 依赖: Category, CommGrp, CommGrp.toGrp, InducedCategory
-/
instance : Category (CommGrp C) :=
  inferInstanceAs (Category (InducedCategory _ CommGrp.toGrp))

@[simp]
/--
theorem `id_hom` / 定理 `id_hom`

English:
theorem id_hom
  given: (A : CommGrp C)
  statement: (InducedCategory.Hom.hom (𝟙 A)) = 𝟙 A.toGrp
  proof: rfl

@[simp]

中文:
定理 id_hom
  条件: (A : CommGrp C)
  结论: (InducedCategory.Hom.hom (𝟙 A)) = 𝟙 A.toGrp
  证明: rfl

@[simp]
-/
theorem id_hom (A : CommGrp C) : (InducedCategory.Hom.hom (𝟙 A)) = 𝟙 A.toGrp :=
  rfl

@[simp]
/--
theorem `comp_hom` / 定理 `comp_hom`

English:
theorem comp_hom
  given: {R S T : CommGrp C} (f : R ⟶ S) (g : S ⟶ T)
  proof: rfl

@[ext]

中文:
定理 comp_hom
  条件: {R S T : CommGrp C} (f : R ⟶ S) (g : S ⟶ T)
  证明: rfl

@[ext]
-/
theorem comp_hom {R S T : CommGrp C} (f : R ⟶ S) (g : S ⟶ T) :
    (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

@[ext]
/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  given: {A B : CommGrp C} (f g : A ⟶ B) (h : f.hom.hom.hom = g.hom.hom.hom)
  statement: f = g
  proof: InducedCategory.hom_ext (Grp.hom_ext _ _ h)

中文:
定理 hom_ext
  条件: {A B : CommGrp C} (f g : A ⟶ B) (h : f.hom.hom.hom = g.hom.hom.hom)
  结论: f = g
  证明: InducedCategory.hom_ext (Grp.hom_ext _ _ h)

Depends on / 依赖: Grp.hom_ext, InducedCategory, InducedCategory.hom_ext, hom_ext
-/
theorem hom_ext {A B : CommGrp C} (f g : A ⟶ B) (h : f.hom.hom.hom = g.hom.hom.hom) : f = g :=
  InducedCategory.hom_ext (Grp.hom_ext _ _ h)

section

variable (C)

/-- The forgetful functor from commutative group objects to group objects. -/
@[simps! obj_X]
/--
Definition of `forget₂Grp` / `forget₂Grp` 的定义

English:
definition forget₂Grp
  signature: : CommGrp C ⥤ Grp C
  body: inducedFunctor CommGrp.toGrp

中文:
定义 forget₂Grp
  签名: : CommGrp C ⥤ Grp C
  定义体: inducedFunctor CommGrp.toGrp

Depends on / 依赖: CommGrp, CommGrp.toGrp, inducedFunctor
-/
def forget₂Grp : CommGrp C ⥤ Grp C :=
  inducedFunctor CommGrp.toGrp

/--
Definition of `fullyFaithfulForget₂Grp` / `fullyFaithfulForget₂Grp` 的定义

English:
definition fullyFaithfulForget₂Grp
  signature: : (forget₂Grp C).FullyFaithful
  body: fullyFaithfulInducedFunctor _

中文:
定义 fullyFaithfulForget₂Grp
  签名: : (forget₂Grp C).FullyFaithful
  定义体: fullyFaithfulInducedFunctor _

Depends on / 依赖: fullyFaithfulInducedFunctor
-/
def fullyFaithfulForget₂Grp : (forget₂Grp C).FullyFaithful :=
  fullyFaithfulInducedFunctor _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget₂Grp C).Full
  body: InducedCategory.full _

中文:
实例 :
  签名: (forget₂Grp C).Full
  定义体: InducedCategory.full _

Depends on / 依赖: InducedCategory, InducedCategory.full
-/
instance : (forget₂Grp C).Full := InducedCategory.full _
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget₂Grp C).Faithful
  body: InducedCategory.faithful _

@[simp]

中文:
实例 :
  签名: (forget₂Grp C).Faithful
  定义体: InducedCategory.faithful _

@[simp]

Depends on / 依赖: InducedCategory, InducedCategory.faithful, faithful
-/
instance : (forget₂Grp C).Faithful := InducedCategory.faithful _

@[simp]
/--
theorem `forget₂Grp_obj_one` / 定理 `forget₂Grp_obj_one`

English:
theorem forget₂Grp_obj_one
  given: (A : CommGrp C)
  statement: η[((forget₂Grp C).obj A).X] = η[A.X]
  proof: rfl

@[simp]

中文:
定理 forget₂Grp_obj_one
  条件: (A : CommGrp C)
  结论: η[((forget₂Grp C).obj A).X] = η[A.X]
  证明: rfl

@[simp]
-/
theorem forget₂Grp_obj_one (A : CommGrp C) : η[((forget₂Grp C).obj A).X] = η[A.X] :=
  rfl

@[simp]
/--
theorem `forget₂Grp_obj_mul` / 定理 `forget₂Grp_obj_mul`

English:
theorem forget₂Grp_obj_mul
  given: (A : CommGrp C)
  statement: μ[((forget₂Grp C).obj A).X] = μ[A.X]
  proof: rfl

@[simp]

中文:
定理 forget₂Grp_obj_mul
  条件: (A : CommGrp C)
  结论: μ[((forget₂Grp C).obj A).X] = μ[A.X]
  证明: rfl

@[simp]
-/
theorem forget₂Grp_obj_mul (A : CommGrp C) : μ[((forget₂Grp C).obj A).X] = μ[A.X] :=
  rfl

@[simp]
/--
theorem `forget₂Grp_map_hom` / 定理 `forget₂Grp_map_hom`

English:
theorem forget₂Grp_map_hom
  given: {A B : CommGrp C} (f : A ⟶ B)
  proof: rfl

中文:
定理 forget₂Grp_map_hom
  条件: {A B : CommGrp C} (f : A ⟶ B)
  证明: rfl
-/
theorem forget₂Grp_map_hom {A B : CommGrp C} (f : A ⟶ B) :
    ((forget₂Grp C).map f).hom = f.hom.hom :=
  rfl

/--
Definition of `forget₂CommMon` / `forget₂CommMon` 的定义

English:
definition forget₂CommMon
  signature: : CommGrp C ⥤ CommMon C where
  body: CommMon.mk G.X
  map f := CommMon.homMk f.hom.hom

中文:
定义 forget₂CommMon
  签名: : CommGrp C ⥤ CommMon C where
  定义体: CommMon.mk G.X
  map f := CommMon.homMk f.hom.hom

Depends on / 依赖: CommMon, CommMon.mk
-/
def forget₂CommMon : CommGrp C ⥤ CommMon C where
  obj G := CommMon.mk G.X
  map f := CommMon.homMk f.hom.hom

/--
Definition of `fullyFaithfulForget₂CommMon` / `fullyFaithfulForget₂CommMon` 的定义

English:
definition fullyFaithfulForget₂CommMon
  signature: : (forget₂CommMon C).FullyFaithful where
  body: InducedCategory.homMk (Grp.homMk' f.hom)

中文:
定义 fullyFaithfulForget₂CommMon
  签名: : (forget₂CommMon C).FullyFaithful where
  定义体: InducedCategory.homMk (Grp.homMk' f.hom)

Depends on / 依赖: Grp.homMk, InducedCategory, InducedCategory.homMk, f.hom
-/
def fullyFaithfulForget₂CommMon : (forget₂CommMon C).FullyFaithful where
  preimage f := InducedCategory.homMk (Grp.homMk' f.hom)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget₂CommMon C).Full
  body: (fullyFaithfulForget₂CommMon _).full

中文:
实例 :
  签名: (forget₂CommMon C).Full
  定义体: (fullyFaithfulForget₂CommMon _).full
-/
instance : (forget₂CommMon C).Full := (fullyFaithfulForget₂CommMon _).full
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget₂CommMon C).Faithful
  body: (fullyFaithfulForget₂CommMon _).faithful

@[simp]

中文:
实例 :
  签名: (forget₂CommMon C).Faithful
  定义体: (fullyFaithfulForget₂CommMon _).faithful

@[simp]

Depends on / 依赖: faithful
-/
instance : (forget₂CommMon C).Faithful := (fullyFaithfulForget₂CommMon _).faithful

@[simp]
/--
theorem `forget₂CommMon_obj_one` / 定理 `forget₂CommMon_obj_one`

English:
theorem forget₂CommMon_obj_one
  given: (A : CommGrp C)
  statement: η[((forget₂CommMon C).obj A).X] = η[A.X]
  proof: rfl

@[simp]

中文:
定理 forget₂CommMon_obj_one
  条件: (A : CommGrp C)
  结论: η[((forget₂CommMon C).obj A).X] = η[A.X]
  证明: rfl

@[simp]
-/
theorem forget₂CommMon_obj_one (A : CommGrp C) : η[((forget₂CommMon C).obj A).X] = η[A.X] :=
  rfl

@[simp]
/--
theorem `forget₂CommMon_obj_mul` / 定理 `forget₂CommMon_obj_mul`

English:
theorem forget₂CommMon_obj_mul
  given: (A : CommGrp C)
  statement: μ[((forget₂CommMon C).obj A).X] = μ[A.X]
  proof: rfl

@[simp]

中文:
定理 forget₂CommMon_obj_mul
  条件: (A : CommGrp C)
  结论: μ[((forget₂CommMon C).obj A).X] = μ[A.X]
  证明: rfl

@[simp]
-/
theorem forget₂CommMon_obj_mul (A : CommGrp C) : μ[((forget₂CommMon C).obj A).X] = μ[A.X] :=
  rfl

@[simp]
/--
theorem `forget₂CommMon_map_hom` / 定理 `forget₂CommMon_map_hom`

English:
theorem forget₂CommMon_map_hom
  given: {A B : CommGrp C} (f : A ⟶ B)
  proof: rfl

中文:
定理 forget₂CommMon_map_hom
  条件: {A B : CommGrp C} (f : A ⟶ B)
  证明: rfl
-/
theorem forget₂CommMon_map_hom {A B : CommGrp C} (f : A ⟶ B) :
    ((forget₂CommMon C).map f).hom = f.hom.hom :=
  rfl

/-- The forgetful functor from commutative group objects to the ambient category. -/
@[simps!]
/--
Definition of `forget` / `forget` 的定义

English:
definition forget
  signature: : CommGrp C ⥤ C
  body: forget₂Grp C ⋙ Grp.forget C

中文:
定义 forget
  签名: : CommGrp C ⥤ C
  定义体: forget₂Grp C ⋙ Grp.forget C

Depends on / 依赖: Grp.forget, forget
-/
def forget : CommGrp C ⥤ C :=
  forget₂Grp C ⋙ Grp.forget C

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget C).Faithful

中文:
实例 :
  签名: (forget C).Faithful
-/
instance : (forget C).Faithful where

@[simp]
/--
theorem `forget₂Grp_comp_forget` / 定理 `forget₂Grp_comp_forget`

English:
theorem forget₂Grp_comp_forget
  statement: forget₂Grp C ⋙ Grp.forget C = forget C
  proof: rfl

@[simp]

中文:
定理 forget₂Grp_comp_forget
  结论: forget₂Grp C ⋙ Grp.forget C = forget C
  证明: rfl

@[simp]
-/
theorem forget₂Grp_comp_forget : forget₂Grp C ⋙ Grp.forget C = forget C := rfl

@[simp]
/--
theorem `forget₂CommMon_comp_forget` / 定理 `forget₂CommMon_comp_forget`

English:
theorem forget₂CommMon_comp_forget
  statement: forget₂CommMon C ⋙ CommMon.forget C = forget C
  proof: rfl

中文:
定理 forget₂CommMon_comp_forget
  结论: forget₂CommMon C ⋙ CommMon.forget C = forget C
  证明: rfl
-/
theorem forget₂CommMon_comp_forget : forget₂CommMon C ⋙ CommMon.forget C = forget C := rfl

instance {G H : CommGrp C} {f : G ⟶ H} [IsIso f] : IsIso f.hom :=
  inferInstanceAs (IsIso ((forget₂Grp C).map f))

instance {G H : CommGrp C} {f : G ⟶ H} [IsIso f] : IsIso f.hom.hom :=
  inferInstanceAs (IsIso ((forget₂Grp C ⋙ Grp.forget₂Mon C).map f))

end

/-- Construct an isomorphism of commutative group objects by giving a monoid isomorphism between the
underlying objects. -/
@[simps!]
/--
Definition of `mkIso'` / `mkIso'` 的定义

English:
definition mkIso'
  signature: {G H : C} (e : G ≅ H) [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H]
  body: (fullyFaithfulForget₂Grp C).preimageIso (Grp.mkIso' e)

中文:
定义 mkIso'
  签名: {G H : C} (e : G ≅ H) [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H]
  定义体: (fullyFaithfulForget₂Grp C).preimageIso (Grp.mkIso' e)

Depends on / 依赖: Grp.mkIso, preimageIso
-/
def mkIso' {G H : C} (e : G ≅ H) [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H]
    [IsMonHom e.hom] : mk G ≅ mk H :=
  (fullyFaithfulForget₂Grp C).preimageIso (Grp.mkIso' e)

section

variable {G H : CommGrp C} (e : G.X ≅ H.X) (one_f : η[G.X] ≫ e.hom = η[H.X] := by cat_disch)
  (mul_f : μ[G.X] ≫ e.hom = (e.hom otimesₘ e.hom) ≫ μ[H.X] := by cat_disch)

set_option backward.privateInPublic true in
/--
Definition of `mkIso` / `mkIso` 的定义

English:
abbreviation mkIso
  signature: : G ≅ H
  body: have : IsMonHom e.hom := ⟨one_f, mul_f⟩
  mkIso' e

中文:
缩写 mkIso
  签名: : G ≅ H
  定义体: have : IsMonHom e.hom := ⟨one_f, mul_f⟩
  mkIso' e

Depends on / 依赖: IsMonHom, e.hom, mul_f, one_f
-/
abbrev mkIso : G ≅ H :=
  have : IsMonHom e.hom := ⟨one_f, mul_f⟩
  mkIso' e

set_option backward.privateInPublic true in
/--
lemma `mkIso_hom_hom_hom_hom` / 引理 `mkIso_hom_hom_hom_hom`

English:
lemma mkIso_hom_hom_hom_hom
  statement: (mkIso e one_f mul_f).hom.hom.hom.hom = e.hom
  proof: rfl

中文:
引理 mkIso_hom_hom_hom_hom
  结论: (mkIso e one_f mul_f).hom.hom.hom.hom = e.hom
  证明: rfl
-/
@[simp] lemma mkIso_hom_hom_hom_hom : (mkIso e one_f mul_f).hom.hom.hom.hom = e.hom := rfl
set_option backward.privateInPublic true in
/--
lemma `mkIso_inv_hom_hom_hom` / 引理 `mkIso_inv_hom_hom_hom`

English:
lemma mkIso_inv_hom_hom_hom
  statement: (mkIso e one_f mul_f).inv.hom.hom.hom = e.inv
  proof: rfl

中文:
引理 mkIso_inv_hom_hom_hom
  结论: (mkIso e one_f mul_f).inv.hom.hom.hom = e.inv
  证明: rfl
-/
@[simp] lemma mkIso_inv_hom_hom_hom : (mkIso e one_f mul_f).inv.hom.hom.hom = e.inv := rfl

end

/--
Instance `uniqueHomFromTrivial` / 实例 `uniqueHomFromTrivial`

English:
instance uniqueHomFromTrivial
  signature: (A : CommGrp C)
  body: Equiv.unique (show _ ≃ (Grp.trivial C ⟶ A.toGrp) from
    InducedCategory.homEquiv)

中文:
实例 uniqueHomFromTrivial
  签名: (A : CommGrp C)
  定义体: Equiv.unique (show _ ≃ (Grp.trivial C ⟶ A.toGrp) from
    InducedCategory.homEquiv)

Depends on / 依赖: A.toGrp, Equiv.unique, Grp.trivial, InducedCategory, InducedCategory.homEquiv, homEquiv, unique
-/
instance uniqueHomFromTrivial (A : CommGrp C) : Unique (trivial C ⟶ A) :=
  Equiv.unique (show _ ≃ (Grp.trivial C ⟶ A.toGrp) from
    InducedCategory.homEquiv)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasInitial (CommGrp C)
  body: hasInitial_of_unique (trivial C)

中文:
实例 :
  签名: HasInitial (CommGrp C)
  定义体: hasInitial_of_unique (trivial C)

Depends on / 依赖: hasInitial_of_unique
-/
instance : HasInitial (CommGrp C) :=
  hasInitial_of_unique (trivial C)

end CommGrp

variable {C}
  {D : Type u₂} [Category.{v₂} D] [CartesianMonoidalCategory D] [BraidedCategory D]
  {E : Type u₃} [Category.{v₃} E] [CartesianMonoidalCategory E] [BraidedCategory E]

namespace Functor
variable {F F' : C ⥤ D} [F.Braided] [F'.Braided] {G : D ⥤ E} [G.Braided]

open Monoidal

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (F) in
/-- A finite-product-preserving functor takes commutative group objects to commutative group
objects. -/
@[simps!]
/--
Definition of `mapCommGrp` / `mapCommGrp` 的定义

English:
definition mapCommGrp
  signature: : CommGrp C ⥤ CommGrp D where
  body: { F.mapGrp.obj A.toGrp with
      comm :=
        { mul_comm := by
            dsimp
            rw [← Functor.LaxBraided.braided_assoc]; rw [← Functor.map_comp]; rw [IsCommMonObj.mul_comm] } }
  map f := InducedCategory.homMk (F.mapGrp.map f.hom)

中文:
定义 mapCommGrp
  签名: : CommGrp C ⥤ CommGrp D where
  定义体: { F.mapGrp.obj A.toGrp with
      comm :=
        { mul_comm := by
            dsimp
            rw [← Functor.LaxBraided.braided_assoc]; rw [← Functor.map_comp]; rw [IsCommMonObj.mul_comm] } }
  map f := InducedCategory.homMk (F.mapGrp.map f.hom)

Depends on / 依赖: A.toGrp, F.mapGrp.map, F.mapGrp.obj, Functor, Functor.LaxBraided.braided_assoc, Functor.map_comp, InducedCategory, InducedCategory.homMk, IsCommMonObj, IsCommMonObj.mul_comm, LaxBraided, braided_assoc, f.hom, mapGrp, map_comp, mul_comm
-/
def mapCommGrp : CommGrp C ⥤ CommGrp D where
  obj A :=
    { F.mapGrp.obj A.toGrp with
      comm :=
        { mul_comm := by
            dsimp
            rw [← Functor.LaxBraided.braided_assoc]; rw [← Functor.map_comp]; rw [IsCommMonObj.mul_comm] } }
  map f := InducedCategory.homMk (F.mapGrp.map f.hom)

/--
Instance `Faithful.mapCommGrp` / 实例 `Faithful.mapCommGrp`

English:
instance Faithful.mapCommGrp
  signature: [F.Faithful]
  body: (CommGrp.forget _ ⋙ F).map_injective ((CommGrp.forget _).congr_map hfg)

中文:
实例 Faithful.mapCommGrp
  签名: [F.Faithful]
  定义体: (CommGrp.forget _ ⋙ F).map_injective ((CommGrp.forget _).congr_map hfg)
-/
protected instance Faithful.mapCommGrp [F.Faithful] : F.mapCommGrp.Faithful where
  map_injective hfg :=
    (CommGrp.forget _ ⋙ F).map_injective ((CommGrp.forget _).congr_map hfg)

set_option backward.isDefEq.respectTransparency.types false in
/-- If `F : C ⥤ D` is a fully faithful monoidal functor, then
`CommGrpCat(F) : CommGrpCat C ⥤ CommGrpCat D` is fully faithful too. -/
@[simps]
/--
Definition of `FullyFaithful.mapCommGrp` / `FullyFaithful.mapCommGrp` 的定义

English:
definition FullyFaithful.mapCommGrp
  signature: (hF : F.FullyFaithful)
  body: InducedCategory.homMk (Grp.homMk' (hF.mapMon.preimage f.hom.hom))

中文:
定义 FullyFaithful.mapCommGrp
  签名: (hF : F.FullyFaithful)
  定义体: InducedCategory.homMk (Grp.homMk' (hF.mapMon.preimage f.hom.hom))
-/
protected def FullyFaithful.mapCommGrp (hF : F.FullyFaithful) : F.mapCommGrp.FullyFaithful where
  preimage f := InducedCategory.homMk (Grp.homMk' (hF.mapMon.preimage f.hom.hom))

/--
Instance `Full.mapCommGrp` / 实例 `Full.mapCommGrp`

English:
instance Full.mapCommGrp
  signature: [F.Full] [F.Faithful]
  body: (FullyFaithful.ofFullyFaithful F).mapCommGrp.full

@[simp]

中文:
实例 Full.mapCommGrp
  签名: [F.Full] [F.Faithful]
  定义体: (FullyFaithful.ofFullyFaithful F).mapCommGrp.full

@[simp]
-/
protected instance Full.mapCommGrp [F.Full] [F.Faithful] : F.mapCommGrp.Full :=
  (FullyFaithful.ofFullyFaithful F).mapCommGrp.full

@[simp]
/--
theorem `mapCommGrp_id_one` / 定理 `mapCommGrp_id_one`

English:
theorem mapCommGrp_id_one
  given: (A : CommGrp C)
  proof: rfl

@[simp]

中文:
定理 mapCommGrp_id_one
  条件: (A : CommGrp C)
  证明: rfl

@[simp]
-/
theorem mapCommGrp_id_one (A : CommGrp C) :
    η[((𝟭 C).mapCommGrp.obj A).X] = 𝟙 _ ≫ η[A.X] :=
  rfl

@[simp]
/--
theorem `mapCommpGrp_id_mul` / 定理 `mapCommpGrp_id_mul`

English:
theorem mapCommpGrp_id_mul
  given: (A : CommGrp C)
  proof: rfl

@[simp]

中文:
定理 mapCommpGrp_id_mul
  条件: (A : CommGrp C)
  证明: rfl

@[simp]
-/
theorem mapCommpGrp_id_mul (A : CommGrp C) :
    μ[((𝟭 C).mapCommGrp.obj A).X] = 𝟙 _ ≫ μ[A.X] :=
  rfl

@[simp]
/--
theorem `comp_mapCommGrp_one` / 定理 `comp_mapCommGrp_one`

English:
theorem comp_mapCommGrp_one
  given: (A : CommGrp C)
  proof: rfl

@[simp]

中文:
定理 comp_mapCommGrp_one
  条件: (A : CommGrp C)
  证明: rfl

@[simp]
-/
theorem comp_mapCommGrp_one (A : CommGrp C) :
    η[((F ⋙ G).mapCommGrp.obj A).X] = LaxMonoidal.ε (F ⋙ G) ≫ (F ⋙ G).map η[A.X] :=
  rfl

@[simp]
/--
theorem `comp_mapCommGrp_mul` / 定理 `comp_mapCommGrp_mul`

English:
theorem comp_mapCommGrp_mul
  given: (A : CommGrp C)
  proof: rfl

中文:
定理 comp_mapCommGrp_mul
  条件: (A : CommGrp C)
  证明: rfl
-/
theorem comp_mapCommGrp_mul (A : CommGrp C) :
    μ[((F ⋙ G).mapCommGrp.obj A).X] = LaxMonoidal.μ (F ⋙ G) _ _ ≫ (F ⋙ G).map μ[A.X] :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The identity functor is also the identity on commutative group objects. -/
@[simps!]
/--
Definition of `mapCommGrpIdIso` / `mapCommGrpIdIso` 的定义

English:
definition mapCommGrpIdIso
  signature: : mapCommGrp (𝟭 C) ≅ 𝟭 (CommGrp C)
  body: NatIso.ofComponents (fun X => CommGrp.mkIso (.refl _) (by simp)
    (by simp))

中文:
定义 mapCommGrpIdIso
  签名: : mapCommGrp (𝟭 C) ≅ 𝟭 (CommGrp C)
  定义体: NatIso.ofComponents (fun X => CommGrp.mkIso (.refl _) (by simp)
    (by simp))

Depends on / 依赖: CommGrp, CommGrp.mkIso, NatIso, NatIso.ofComponents, ofComponents
-/
def mapCommGrpIdIso : mapCommGrp (𝟭 C) ≅ 𝟭 (CommGrp C) :=
  NatIso.ofComponents (fun X => CommGrp.mkIso (.refl _) (by simp)
    (by simp))

set_option backward.isDefEq.respectTransparency false in
/-- The composition functor is also the composition on commutative group objects. -/
@[simps!]
/--
Definition of `mapCommGrpCompIso` / `mapCommGrpCompIso` 的定义

English:
definition mapCommGrpCompIso
  signature: : (F ⋙ G).mapCommGrp ≅ F.mapCommGrp ⋙ G.mapCommGrp
  body: NatIso.ofComponents fun X => CommGrp.mkIso (.refl _)

中文:
定义 mapCommGrpCompIso
  签名: : (F ⋙ G).mapCommGrp ≅ F.mapCommGrp ⋙ G.mapCommGrp
  定义体: NatIso.ofComponents fun X => CommGrp.mkIso (.refl _)

Depends on / 依赖: CommGrp, CommGrp.mkIso, NatIso, NatIso.ofComponents, ofComponents
-/
def mapCommGrpCompIso : (F ⋙ G).mapCommGrp ≅ F.mapCommGrp ⋙ G.mapCommGrp :=
  NatIso.ofComponents fun X => CommGrp.mkIso (.refl _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Natural transformations between functors lift to commutative group objects. -/
@[simps!]
/--
Definition of `mapCommGrpNatTrans` / `mapCommGrpNatTrans` 的定义

English:
definition mapCommGrpNatTrans
  signature: (f : F ⟶ F')
  body: InducedCategory.homMk ((mapGrpNatTrans f).app X.toGrp)

中文:
定义 mapCommGrpNatTrans
  签名: (f : F ⟶ F')
  定义体: InducedCategory.homMk ((mapGrpNatTrans f).app X.toGrp)

Depends on / 依赖: InducedCategory, InducedCategory.homMk, X.toGrp, mapGrpNatTrans
-/
def mapCommGrpNatTrans (f : F ⟶ F') : F.mapCommGrp ⟶ F'.mapCommGrp where
  app X := InducedCategory.homMk ((mapGrpNatTrans f).app X.toGrp)

set_option backward.isDefEq.respectTransparency false in
/-- Natural isomorphisms between functors lift to commutative group objects. -/
@[simps!]
/--
Definition of `mapCommGrpNatIso` / `mapCommGrpNatIso` 的定义

English:
definition mapCommGrpNatIso
  signature: (e : F ≅ F')
  body: NatIso.ofComponents fun X => CommGrp.mkIso (e.app _)

中文:
定义 mapCommGrpNatIso
  签名: (e : F ≅ F')
  定义体: NatIso.ofComponents fun X => CommGrp.mkIso (e.app _)

Depends on / 依赖: CommGrp, CommGrp.mkIso, NatIso, NatIso.ofComponents, e.app, ofComponents
-/
def mapCommGrpNatIso (e : F ≅ F') : F.mapCommGrp ≅ F'.mapCommGrp :=
  NatIso.ofComponents fun X => CommGrp.mkIso (e.app _)

attribute [local instance] Functor.Braided.ofChosenFiniteProducts in
/-- `mapCommGrp` is functorial in the left-exact functor. -/
@[simps]
/--
Definition of `mapCommGrpFunctor` / `mapCommGrpFunctor` 的定义

English:
definition mapCommGrpFunctor
  signature: : (C ⥤ₗ D) ⥤ CommGrp C ⥤ CommGrp D where
  body: F.1.mapCommGrp
  map α := mapCommGrpNatTrans α.hom

中文:
定义 mapCommGrpFunctor
  签名: : (C ⥤ₗ D) ⥤ CommGrp C ⥤ CommGrp D where
  定义体: F.1.mapCommGrp
  map α := mapCommGrpNatTrans α.hom

Depends on / 依赖: mapCommGrp
-/
noncomputable def mapCommGrpFunctor : (C ⥤ₗ D) ⥤ CommGrp C ⥤ CommGrp D where
  obj F := F.1.mapCommGrp
  map α := mapCommGrpNatTrans α.hom

end Functor

open CategoryTheory.Functor

namespace Adjunction
variable {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) [F.Braided] [G.Braided]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `mapCommGrp` / `mapCommGrp` 的定义

English:
definition mapCommGrp
  signature: : F.mapCommGrp ⊣ G.mapCommGrp where
  body: mapCommGrpIdIso.inv ≫ mapCommGrpNatTrans a.unit ≫ mapCommGrpCompIso.hom
  counit := mapCommGrpCompIso.inv ≫ mapCommGrpNatTrans a.counit ≫ mapCommGrpIdIso.hom

中文:
定义 mapCommGrp
  签名: : F.mapCommGrp ⊣ G.mapCommGrp where
  定义体: mapCommGrpIdIso.inv ≫ mapCommGrpNatTrans a.unit ≫ mapCommGrpCompIso.hom
  counit := mapCommGrpCompIso.inv ≫ mapCommGrpNatTrans a.counit ≫ mapCommGrpIdIso.hom
-/
@[simps] noncomputable def mapCommGrp : F.mapCommGrp ⊣ G.mapCommGrp where
  unit := mapCommGrpIdIso.inv ≫ mapCommGrpNatTrans a.unit ≫ mapCommGrpCompIso.hom
  counit := mapCommGrpCompIso.inv ≫ mapCommGrpNatTrans a.counit ≫ mapCommGrpIdIso.hom

end Adjunction

namespace Equivalence
variable (e : C ≌ D) [e.functor.Braided] [e.inverse.Braided]

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `mapCommGrp` / `mapCommGrp` 的定义

English:
definition mapCommGrp
  signature: : CommGrp C ≌ CommGrp D where
  body: e.functor.mapCommGrp
  inverse := e.inverse.mapCommGrp
  unitIso := mapCommGrpIdIso.symm ≪≫ mapCommGrpNatIso e.unitIso ≪≫ mapCommGrpCompIso
  counitIso := mapCommGrpCompIso.symm ≪≫ mapCommGrpNatIso e.counitIso ≪≫ mapCommGrpIdIso

中文:
定义 mapCommGrp
  签名: : CommGrp C ≌ CommGrp D where
  定义体: e.functor.mapCommGrp
  inverse := e.inverse.mapCommGrp
  unitIso := mapCommGrpIdIso.symm ≪≫ mapCommGrpNatIso e.unitIso ≪≫ mapCommGrpCompIso
  counitIso := mapCommGrpCompIso.symm ≪≫ mapCommGrpNatIso e.counitIso ≪≫ mapCommGrpIdIso
-/
@[simps] noncomputable def mapCommGrp : CommGrp C ≌ CommGrp D where
  functor := e.functor.mapCommGrp
  inverse := e.inverse.mapCommGrp
  unitIso := mapCommGrpIdIso.symm ≪≫ mapCommGrpNatIso e.unitIso ≪≫ mapCommGrpCompIso
  counitIso := mapCommGrpCompIso.symm ≪≫ mapCommGrpNatIso e.counitIso ≪≫ mapCommGrpIdIso

end CategoryTheory.Equivalence
