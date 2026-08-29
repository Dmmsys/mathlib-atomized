/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Mon

/-!
# The category of commutative monoids in a braided monoidal category.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃ u

open CategoryTheory MonoidalCategory MonObj

namespace CategoryTheory
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C] [BraidedCategory.{v₁} C]

variable (C) in
/--
Definition of `CommMon` / `CommMon` 的定义

English:
structure CommMon
  parameters: where
  axioms and operations (3):
    - X : C
    - [mon : MonObj X]
    - [comm : IsCommMonObj X]

中文:
结构 CommMon
  参数: where
  公理与运算 (3 个):
    - X : C
    - [mon : MonObj X]
    - [comm : IsCommMonObj X]
-/
structure CommMon where
  /-- The underlying object in the ambient monoidal category -/
  X : C
  [mon : MonObj X]
  [comm : IsCommMonObj X]

attribute [instance] CommMon.mon CommMon.comm

namespace CommMon

/-- A commutative monoid object is a monoid object. -/
@[simps X]
/--
Definition of `toMon` / `toMon` 的定义

English:
definition toMon
  signature: (A : CommMon C)
  body: ⟨A.X⟩

中文:
定义 toMon
  签名: (A : CommMon C)
  定义体: ⟨A.X⟩
-/
def toMon (A : CommMon C) : Mon C := ⟨A.X⟩

variable (C) in
/-- The trivial commutative monoid object. We later show this is initial in `CommMon C`.
-/
@[simps!]
/--
Definition of `trivial` / `trivial` 的定义

English:
definition trivial
  signature: : CommMon C
  body: { X := 𝟙_ C }

中文:
定义 trivial
  签名: : CommMon C
  定义体: { X := 𝟙_ C }
-/
def trivial : CommMon C := { X := 𝟙_ C }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (CommMon C)
  body: ⟨trivial C⟩

中文:
实例 :
  签名: Inhabited (CommMon C)
  定义体: ⟨trivial C⟩
-/
instance : Inhabited (CommMon C) :=
  ⟨trivial C⟩

variable {M : CommMon C}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (CommMon C)
  body: inferInstanceAs (Category (InducedCategory _ CommMon.toMon))

@[simp]

中文:
实例 :
  签名: Category (CommMon C)
  定义体: inferInstanceAs (Category (InducedCategory _ CommMon.toMon))

@[simp]

Depends on / 依赖: Category, CommMon, CommMon.toMon, InducedCategory
-/
instance : Category (CommMon C) :=
  inferInstanceAs (Category (InducedCategory _ CommMon.toMon))

@[simp]
/--
theorem `id_hom` / 定理 `id_hom`

English:
theorem id_hom
  given: (A : CommMon C)
  statement: Mon.Hom.hom (InducedCategory.Hom.hom (𝟙 A)) = 𝟙 A.X
  proof: rfl

@[simp]

中文:
定理 id_hom
  条件: (A : CommMon C)
  结论: Mon.Hom.hom (InducedCategory.Hom.hom (𝟙 A)) = 𝟙 A.X
  证明: rfl

@[simp]
-/
theorem id_hom (A : CommMon C) : Mon.Hom.hom (InducedCategory.Hom.hom (𝟙 A)) = 𝟙 A.X :=
  rfl

@[simp]
/--
theorem `comp_hom` / 定理 `comp_hom`

English:
theorem comp_hom
  given: {R S T : CommMon C} (f : R ⟶ S) (g : S ⟶ T)
  proof: rfl

@[ext]

中文:
定理 comp_hom
  条件: {R S T : CommMon C} (f : R ⟶ S) (g : S ⟶ T)
  证明: rfl

@[ext]
-/
theorem comp_hom {R S T : CommMon C} (f : R ⟶ S) (g : S ⟶ T) :
    Mon.Hom.hom (f ≫ g).hom = f.hom.hom ≫ g.hom.hom :=
  rfl

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {A B : CommMon C} (f g : A ⟶ B) (h : f.hom.hom = g.hom.hom)
  statement: f = g
  proof: InducedCategory.hom_ext (Mon.Hom.ext h)

中文:
引理 hom_ext
  条件: {A B : CommMon C} (f g : A ⟶ B) (h : f.hom.hom = g.hom.hom)
  结论: f = g
  证明: InducedCategory.hom_ext (Mon.Hom.ext h)

Depends on / 依赖: InducedCategory, InducedCategory.hom_ext, Mon.Hom.ext, hom_ext
-/
lemma hom_ext {A B : CommMon C} (f g : A ⟶ B) (h : f.hom.hom = g.hom.hom) : f = g :=
  InducedCategory.hom_ext (Mon.Hom.ext h)

/-- Constructor for morphisms in `CommMon C`. -/
@[simps]
/--
Definition of `homMk` / `homMk` 的定义

English:
definition homMk
  signature: {A B : CommMon C} (f : A.toMon ⟶ B.toMon)
  body: f

中文:
定义 homMk
  签名: {A B : CommMon C} (f : A.toMon ⟶ B.toMon)
  定义体: f
-/
def homMk {A B : CommMon C} (f : A.toMon ⟶ B.toMon) : A ⟶ B where
  hom := f

section

variable (C)

/-- The forgetful functor from commutative monoid objects to monoid objects. -/
@[simps! obj_X]
/--
Definition of `forget₂Mon` / `forget₂Mon` 的定义

English:
definition forget₂Mon
  signature: : CommMon C ⥤ Mon C
  body: inducedFunctor CommMon.toMon

中文:
定义 forget₂Mon
  签名: : CommMon C ⥤ Mon C
  定义体: inducedFunctor CommMon.toMon

Depends on / 依赖: CommMon, CommMon.toMon, inducedFunctor
-/
def forget₂Mon : CommMon C ⥤ Mon C :=
  inducedFunctor CommMon.toMon

/--
Definition of `fullyFaithfulForget₂Mon` / `fullyFaithfulForget₂Mon` 的定义

English:
definition fullyFaithfulForget₂Mon
  signature: : (forget₂Mon C).FullyFaithful
  body: fullyFaithfulInducedFunctor _

中文:
定义 fullyFaithfulForget₂Mon
  签名: : (forget₂Mon C).FullyFaithful
  定义体: fullyFaithfulInducedFunctor _

Depends on / 依赖: fullyFaithfulInducedFunctor
-/
def fullyFaithfulForget₂Mon : (forget₂Mon C).FullyFaithful :=
  fullyFaithfulInducedFunctor _
-- The `Full, Faithful` instances should be constructed by a deriving handler.
-- https://github.com/leanprover-community/mathlib4/issues/380

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget₂Mon C).Full
  body: InducedCategory.full _

中文:
实例 :
  签名: (forget₂Mon C).Full
  定义体: InducedCategory.full _

Depends on / 依赖: InducedCategory, InducedCategory.full
-/
instance : (forget₂Mon C).Full := InducedCategory.full _
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget₂Mon C).Faithful
  body: InducedCategory.faithful _

@[simp]

中文:
实例 :
  签名: (forget₂Mon C).Faithful
  定义体: InducedCategory.faithful _

@[simp]

Depends on / 依赖: InducedCategory, InducedCategory.faithful, faithful
-/
instance : (forget₂Mon C).Faithful := InducedCategory.faithful _

@[simp]
/--
theorem `forget₂Mon_obj_one` / 定理 `forget₂Mon_obj_one`

English:
theorem forget₂Mon_obj_one
  given: (A : CommMon C)
  statement: η[((forget₂Mon C).obj A).X] = η[A.X]
  proof: rfl

@[simp]

中文:
定理 forget₂Mon_obj_one
  条件: (A : CommMon C)
  结论: η[((forget₂Mon C).obj A).X] = η[A.X]
  证明: rfl

@[simp]
-/
theorem forget₂Mon_obj_one (A : CommMon C) : η[((forget₂Mon C).obj A).X] = η[A.X] :=
  rfl

@[simp]
/--
theorem `forget₂Mon_obj_mul` / 定理 `forget₂Mon_obj_mul`

English:
theorem forget₂Mon_obj_mul
  given: (A : CommMon C)
  statement: μ[((forget₂Mon C).obj A).X] = μ[A.X]
  proof: rfl

@[simp]

中文:
定理 forget₂Mon_obj_mul
  条件: (A : CommMon C)
  结论: μ[((forget₂Mon C).obj A).X] = μ[A.X]
  证明: rfl

@[simp]
-/
theorem forget₂Mon_obj_mul (A : CommMon C) : μ[((forget₂Mon C).obj A).X] = μ[A.X] :=
  rfl

@[simp]
/--
theorem `forget₂Mon_map_hom` / 定理 `forget₂Mon_map_hom`

English:
theorem forget₂Mon_map_hom
  given: {A B : CommMon C} (f : A ⟶ B)
  proof: rfl

中文:
定理 forget₂Mon_map_hom
  条件: {A B : CommMon C} (f : A ⟶ B)
  证明: rfl
-/
theorem forget₂Mon_map_hom {A B : CommMon C} (f : A ⟶ B) :
    ((forget₂Mon C).map f).hom = f.hom.hom :=
  rfl

/-- The forgetful functor from commutative monoid objects to the ambient category. -/
@[simps!]
/--
Definition of `forget` / `forget` 的定义

English:
definition forget
  signature: : CommMon C ⥤ C
  body: forget₂Mon C ⋙ Mon.forget C

中文:
定义 forget
  签名: : CommMon C ⥤ C
  定义体: forget₂Mon C ⋙ Mon.forget C

Depends on / 依赖: Mon.forget, forget
-/
def forget : CommMon C ⥤ C :=
  forget₂Mon C ⋙ Mon.forget C

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
theorem `forget₂Mon_comp_forget` / 定理 `forget₂Mon_comp_forget`

English:
theorem forget₂Mon_comp_forget
  statement: forget₂Mon C ⋙ Mon.forget C = forget C
  proof: rfl

中文:
定理 forget₂Mon_comp_forget
  结论: forget₂Mon C ⋙ Mon.forget C = forget C
  证明: rfl
-/
theorem forget₂Mon_comp_forget : forget₂Mon C ⋙ Mon.forget C = forget C := rfl

instance {M N : CommMon C} {f : M ⟶ N} [IsIso f] : IsIso f.hom.hom :=
inferInstanceAs IsIso (forget C).map f

end

/-- Construct an isomorphism of commutative monoid objects by giving a monoid isomorphism between
the underlying objects. -/
@[simps!]
/--
Definition of `mkIso'` / `mkIso'` 的定义

English:
definition mkIso'
  signature: {M N : C} (e : M ≅ N) [MonObj M] [IsCommMonObj M] [MonObj N] [IsCommMonObj N]
  body: (fullyFaithfulForget₂Mon C).preimageIso (Mon.mkIso' e)

中文:
定义 mkIso'
  签名: {M N : C} (e : M ≅ N) [MonObj M] [IsCommMonObj M] [MonObj N] [IsCommMonObj N]
  定义体: (fullyFaithfulForget₂Mon C).preimageIso (Mon.mkIso' e)

Depends on / 依赖: Mon.mkIso, preimageIso
-/
def mkIso' {M N : C} (e : M ≅ N) [MonObj M] [IsCommMonObj M] [MonObj N] [IsCommMonObj N]
    [IsMonHom e.hom] : mk M ≅ mk N :=
  (fullyFaithfulForget₂Mon C).preimageIso (Mon.mkIso' e)

/--
Definition of `mkIso` / `mkIso` 的定义

English:
abbreviation mkIso
  signature: {M N : CommMon C} (e : M.X ≅ N.X) (one_f : η[M.X] ≫ e.hom = η[N.X] := by cat_disch)
  body: have : IsMonHom e.hom := ⟨one_f, mul_f⟩
  mkIso' e

中文:
缩写 mkIso
  签名: {M N : CommMon C} (e : M.X ≅ N.X) (one_f : η[M.X] ≫ e.hom = η[N.X] := by cat_disch)
  定义体: have : IsMonHom e.hom := ⟨one_f, mul_f⟩
  mkIso' e

Depends on / 依赖: IsMonHom, cat_disch, e.hom, mul_f, one_f
-/
abbrev mkIso {M N : CommMon C} (e : M.X ≅ N.X) (one_f : η[M.X] ≫ e.hom = η[N.X] := by cat_disch)
    (mul_f : μ[M.X] ≫ e.hom = (e.hom otimesₘ e.hom) ≫ μ[N.X] := by cat_disch) : M ≅ N :=
  have : IsMonHom e.hom := ⟨one_f, mul_f⟩
  mkIso' e

/--
Instance `uniqueHomFromTrivial` / 实例 `uniqueHomFromTrivial`

English:
instance uniqueHomFromTrivial
  signature: (A : CommMon C)
  body: Equiv.unique (show _ ≃ (Mon.trivial C ⟶ A.toMon) from
    InducedCategory.homEquiv)

中文:
实例 uniqueHomFromTrivial
  签名: (A : CommMon C)
  定义体: Equiv.unique (show _ ≃ (Mon.trivial C ⟶ A.toMon) from
    InducedCategory.homEquiv)

Depends on / 依赖: A.toMon, Equiv.unique, InducedCategory, InducedCategory.homEquiv, Mon.trivial, homEquiv, unique
-/
instance uniqueHomFromTrivial (A : CommMon C) : Unique (trivial C ⟶ A) :=
  Equiv.unique (show _ ≃ (Mon.trivial C ⟶ A.toMon) from
    InducedCategory.homEquiv)

open CategoryTheory.Limits

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasInitial (CommMon C)
  body: hasInitial_of_unique (trivial C)

中文:
实例 :
  签名: HasInitial (CommMon C)
  定义体: hasInitial_of_unique (trivial C)

Depends on / 依赖: hasInitial_of_unique
-/
instance : HasInitial (CommMon C) :=
  hasInitial_of_unique (trivial C)

end CommMon

variable
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E] [BraidedCategory E]
  {F F' : C ⥤ D} {G : D ⥤ E}

namespace Functor
section LaxBraided
variable [F.LaxBraided] [F'.LaxBraided] [G.LaxBraided]

open scoped Obj

/--
Instance `isCommMonObj_obj` / 实例 `isCommMonObj_obj`

English:
instance isCommMonObj_obj
  signature: {M : C} [MonObj M] [IsCommMonObj M]
  body: by
    dsimp; rw [← Functor.LaxBraided.braided_assoc, ← Functor.map_comp, IsCommMonObj.mul_comm]

中文:
实例 isCommMonObj_obj
  签名: {M : C} [MonObj M] [IsCommMonObj M]
  定义体: by
    dsimp; rw [← Functor.LaxBraided.braided_assoc, ← Functor.map_comp, IsCommMonObj.mul_comm]

Depends on / 依赖: Functor, Functor.LaxBraided.braided_assoc, Functor.map_comp, IsCommMonObj, IsCommMonObj.mul_comm, LaxBraided, braided_assoc, map_comp, mul_comm
-/
instance isCommMonObj_obj {M : C} [MonObj M] [IsCommMonObj M] : IsCommMonObj (F.obj M) where
  mul_comm := by
    dsimp; rw [← Functor.LaxBraided.braided_assoc, ← Functor.map_comp, IsCommMonObj.mul_comm]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (F) in
/-- A lax braided functor takes commutative monoid objects to commutative monoid objects.

That is, a lax braided functor `F : C ⥤ D` induces a functor `CommMon C ⥤ CommMon D`.
-/
@[simps!]
/--
Definition of `mapCommMon` / `mapCommMon` 的定义

English:
definition mapCommMon
  signature: : CommMon C ⥤ CommMon D where
  body: { F.mapMon.obj A.toMon with
      comm :=
        { mul_comm := by
            dsimp
            rw [← Functor.LaxBraided.braided_assoc]; rw [← Functor.map_comp]; rw [IsCommMonObj.mul_comm] } }
  map f := CommMon.homMk (F.mapMon.map f.hom)

@[simp]

中文:
定义 mapCommMon
  签名: : CommMon C ⥤ CommMon D where
  定义体: { F.mapMon.obj A.toMon with
      comm :=
        { mul_comm := by
            dsimp
            rw [← Functor.LaxBraided.braided_assoc]; rw [← Functor.map_comp]; rw [IsCommMonObj.mul_comm] } }
  map f := CommMon.homMk (F.mapMon.map f.hom)

@[simp]

Depends on / 依赖: A.toMon, CommMon, CommMon.homMk, F.mapMon.map, F.mapMon.obj, Functor, Functor.LaxBraided.braided_assoc, Functor.map_comp, IsCommMonObj, IsCommMonObj.mul_comm, LaxBraided, braided_assoc, f.hom, mapMon, map_comp, mul_comm
-/
def mapCommMon : CommMon C ⥤ CommMon D where
  obj A :=
    { F.mapMon.obj A.toMon with
      comm :=
        { mul_comm := by
            dsimp
            rw [← Functor.LaxBraided.braided_assoc]; rw [← Functor.map_comp]; rw [IsCommMonObj.mul_comm] } }
  map f := CommMon.homMk (F.mapMon.map f.hom)

@[simp]
/--
theorem `mapCommMon_id_one` / 定理 `mapCommMon_id_one`

English:
theorem mapCommMon_id_one
  given: (A : CommMon C)
  proof: rfl

@[simp]

中文:
定理 mapCommMon_id_one
  条件: (A : CommMon C)
  证明: rfl

@[simp]
-/
theorem mapCommMon_id_one (A : CommMon C) :
    η[((𝟭 C).mapCommMon.obj A).X] = 𝟙 _ ≫ η[A.X] :=
  rfl

@[simp]
/--
theorem `mapCommMon_id_mul` / 定理 `mapCommMon_id_mul`

English:
theorem mapCommMon_id_mul
  given: (A : CommMon C)
  proof: rfl

@[simp]

中文:
定理 mapCommMon_id_mul
  条件: (A : CommMon C)
  证明: rfl

@[simp]
-/
theorem mapCommMon_id_mul (A : CommMon C) :
    μ[((𝟭 C).mapCommMon.obj A).X] = 𝟙 _ ≫ μ[A.X] :=
  rfl

@[simp]
/--
theorem `comp_mapCommMon_one` / 定理 `comp_mapCommMon_one`

English:
theorem comp_mapCommMon_one
  given: (A : CommMon C)
  proof: rfl

@[simp]

中文:
定理 comp_mapCommMon_one
  条件: (A : CommMon C)
  证明: rfl

@[simp]
-/
theorem comp_mapCommMon_one (A : CommMon C) :
    η[((F ⋙ G).mapCommMon.obj A).X] = LaxMonoidal.ε (F ⋙ G) ≫ (F ⋙ G).map η[A.X] :=
  rfl

@[simp]
/--
theorem `comp_mapCommMon_mul` / 定理 `comp_mapCommMon_mul`

English:
theorem comp_mapCommMon_mul
  given: (A : CommMon C)
  proof: rfl

中文:
定理 comp_mapCommMon_mul
  条件: (A : CommMon C)
  证明: rfl
-/
theorem comp_mapCommMon_mul (A : CommMon C) :
    μ[((F ⋙ G).mapCommMon.obj A).X] = LaxMonoidal.μ (F ⋙ G) _ _ ≫ (F ⋙ G).map μ[A.X] :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The identity functor is also the identity on commutative monoid objects. -/
@[simps!]
/--
Definition of `mapCommMonIdIso` / `mapCommMonIdIso` 的定义

English:
definition mapCommMonIdIso
  signature: : mapCommMon (𝟭 C) ≅ 𝟭 (CommMon C)
  body: NatIso.ofComponents fun X => CommMon.mkIso (.refl _)

中文:
定义 mapCommMonIdIso
  签名: : mapCommMon (𝟭 C) ≅ 𝟭 (CommMon C)
  定义体: NatIso.ofComponents fun X => CommMon.mkIso (.refl _)

Depends on / 依赖: CommMon, CommMon.mkIso, G.IsContinuous, IsContinuous, NatIso, NatIso.ofComponents, ofComponents
-/
def mapCommMonIdIso : mapCommMon (𝟭 C) ≅ 𝟭 (CommMon C) :=
  NatIso.ofComponents fun X => CommMon.mkIso (.refl _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The composition functor is also the composition on commutative monoid objects. -/
@[simps!]
/--
Definition of `mapCommMonCompIso` / `mapCommMonCompIso` 的定义

English:
definition mapCommMonCompIso
  signature: : (F ⋙ G).mapCommMon ≅ F.mapCommMon ⋙ G.mapCommMon
  body: NatIso.ofComponents fun X => CommMon.mkIso (.refl _)

中文:
定义 mapCommMonCompIso
  签名: : (F ⋙ G).mapCommMon ≅ F.mapCommMon ⋙ G.mapCommMon
  定义体: NatIso.ofComponents fun X => CommMon.mkIso (.refl _)

Depends on / 依赖: CommMon, CommMon.mkIso, G.IsCocontinuous, IsCocontinuous, NatIso, NatIso.ofComponents, ofComponents
-/
def mapCommMonCompIso : (F ⋙ G).mapCommMon ≅ F.mapCommMon ⋙ G.mapCommMon :=
  NatIso.ofComponents fun X => CommMon.mkIso (.refl _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (C D) in
/-- `mapCommMon` is functorial in the lax braided functor. -/
@[simps]
/--
Definition of `mapCommMonFunctor` / `mapCommMonFunctor` 的定义

English:
definition mapCommMonFunctor
  signature: : LaxBraidedFunctor C D ⥤ CommMon C ⥤ CommMon D where
  body: F.mapCommMon
  map α := { app A := CommMon.homMk (.mk' (α.hom.hom.app A.X)) }

中文:
定义 mapCommMonFunctor
  签名: : LaxBraidedFunctor C D ⥤ CommMon C ⥤ CommMon D where
  定义体: F.mapCommMon
  map α := { app A := CommMon.homMk (.mk' (α.hom.hom.app A.X)) }

Depends on / 依赖: F.mapCommMon, mapCommMon
-/
def mapCommMonFunctor : LaxBraidedFunctor C D ⥤ CommMon C ⥤ CommMon D where
  obj F := F.mapCommMon
  map α := { app A := CommMon.homMk (.mk' (α.hom.hom.app A.X)) }

/--
Instance `Faithful.mapCommMon` / 实例 `Faithful.mapCommMon`

English:
instance Faithful.mapCommMon
  signature: [F.Faithful]
  body: (CommMon.forget₂Mon _ ⋙ F.mapMon).map_injective ((CommMon.forget₂Mon _).congr_map hfg)

中文:
实例 Faithful.mapCommMon
  签名: [F.Faithful]
  定义体: (CommMon.forget₂Mon _ ⋙ F.mapMon).map_injective ((CommMon.forget₂Mon _).congr_map hfg)
-/
protected instance Faithful.mapCommMon [F.Faithful] : F.mapCommMon.Faithful where
  map_injective hfg :=
    (CommMon.forget₂Mon _ ⋙ F.mapMon).map_injective ((CommMon.forget₂Mon _).congr_map hfg)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Natural transformations between functors lift to monoid objects. -/
@[simps!]
/--
Definition of `mapCommMonNatTrans` / `mapCommMonNatTrans` 的定义

English:
definition mapCommMonNatTrans
  signature: (f : F ⟶ F') [NatTrans.IsMonoidal f]
  body: CommMon.homMk (.mk' (f.app _))

中文:
定义 mapCommMonNatTrans
  签名: (f : F ⟶ F') [自然数Trans.IsMonoidal f]
  定义体: CommMon.homMk (.mk' (f.app _))

Depends on / 依赖: CommMon, CommMon.homMk, f.app
-/
def mapCommMonNatTrans (f : F ⟶ F') [NatTrans.IsMonoidal f] :
    F.mapCommMon ⟶ F'.mapCommMon where
  app X := CommMon.homMk (.mk' (f.app _))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Natural isomorphisms between functors lift to monoid objects. -/
@[simps!]
/--
Definition of `mapCommMonNatIso` / `mapCommMonNatIso` 的定义

English:
definition mapCommMonNatIso
  signature: (e : F ≅ F') [NatTrans.IsMonoidal e.hom]
  body: NatIso.ofComponents fun X => CommMon.mkIso (e.app _)

中文:
定义 mapCommMonNatIso
  签名: (e : F ≅ F') [自然数Trans.IsMonoidal e.hom]
  定义体: NatIso.ofComponents fun X => CommMon.mkIso (e.app _)

Depends on / 依赖: CommMon, CommMon.mkIso, NatIso, NatIso.ofComponents, e.app, ofComponents
-/
def mapCommMonNatIso (e : F ≅ F') [NatTrans.IsMonoidal e.hom] : F.mapCommMon ≅ F'.mapCommMon :=
  NatIso.ofComponents fun X => CommMon.mkIso (e.app _)

end LaxBraided

section Braided
variable [F.Braided]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `F : C ⥤ D` is a fully faithful monoidal functor, then
`CommMonCat(F) : CommMonCat C ⥤ CommMonCat D` is fully faithful too. -/
@[simps]
/--
Definition of `FullyFaithful.mapCommMon` / `FullyFaithful.mapCommMon` 的定义

English:
definition FullyFaithful.mapCommMon
  signature: (hF : F.FullyFaithful)
  body: CommMon.homMk (hF.mapMon.preimage f.hom)

中文:
定义 FullyFaithful.mapCommMon
  签名: (hF : F.FullyFaithful)
  定义体: CommMon.homMk (hF.mapMon.preimage f.hom)
-/
protected def FullyFaithful.mapCommMon (hF : F.FullyFaithful) : F.mapCommMon.FullyFaithful where
  preimage f := CommMon.homMk (hF.mapMon.preimage f.hom)

/--
Instance `Full.mapCommMon` / 实例 `Full.mapCommMon`

English:
instance Full.mapCommMon
  signature: [F.Full] [F.Faithful]
  body: (FullyFaithful.ofFullyFaithful F).mapCommMon.full

中文:
实例 Full.mapCommMon
  签名: [F.Full] [F.Faithful]
  定义体: (FullyFaithful.ofFullyFaithful F).mapCommMon.full
-/
protected instance Full.mapCommMon [F.Full] [F.Faithful] : F.mapCommMon.Full :=
    (FullyFaithful.ofFullyFaithful F).mapCommMon.full

end Braided

end Functor

open CategoryTheory.Functor

namespace Adjunction
variable {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) [F.Braided] [G.LaxBraided] [a.IsMonoidal]

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `mapCommMon` / `mapCommMon` 的定义

English:
definition mapCommMon
  signature: : F.mapCommMon ⊣ G.mapCommMon where
  body: mapCommMonIdIso.inv ≫ mapCommMonNatTrans a.unit ≫ mapCommMonCompIso.hom
  counit := mapCommMonCompIso.inv ≫ mapCommMonNatTrans a.counit ≫ mapCommMonIdIso.hom

中文:
定义 mapCommMon
  签名: : F.mapCommMon ⊣ G.mapCommMon where
  定义体: mapCommMonIdIso.inv ≫ mapCommMonNatTrans a.unit ≫ mapCommMonCompIso.hom
  counit := mapCommMonCompIso.inv ≫ mapCommMonNatTrans a.counit ≫ mapCommMonIdIso.hom
-/
@[simps] def mapCommMon : F.mapCommMon ⊣ G.mapCommMon where
  unit := mapCommMonIdIso.inv ≫ mapCommMonNatTrans a.unit ≫ mapCommMonCompIso.hom
  counit := mapCommMonCompIso.inv ≫ mapCommMonNatTrans a.counit ≫ mapCommMonIdIso.hom

end Adjunction

namespace Equivalence

set_option backward.defeqAttrib.useBackward true in
/-- An equivalence of categories lifts to an equivalence of their commutative monoid objects. -/
@[simps]
/--
Definition of `mapCommMon` / `mapCommMon` 的定义

English:
definition mapCommMon
  signature: (e : C ≌ D) [e.functor.Braided] [e.inverse.Braided] [e.IsMonoidal]
  body: e.functor.mapCommMon
  inverse := e.inverse.mapCommMon
  unitIso := mapCommMonIdIso.symm ≪≫ mapCommMonNatIso e.unitIso ≪≫ mapCommMonCompIso
  counitIso := mapCommMonCompIso.symm ≪≫ mapCommMonNatIso e.counitIso ≪≫ mapCommMonIdIso

中文:
定义 mapCommMon
  签名: (e : C ≌ D) [e.functor.Braided] [e.inverse.Braided] [e.IsMonoidal]
  定义体: e.functor.mapCommMon
  inverse := e.inverse.mapCommMon
  unitIso := mapCommMonIdIso.symm ≪≫ mapCommMonNatIso e.unitIso ≪≫ mapCommMonCompIso
  counitIso := mapCommMonCompIso.symm ≪≫ mapCommMonNatIso e.counitIso ≪≫ mapCommMonIdIso

Depends on / 依赖: e.functor.mapCommMon, functor, mapCommMon
-/
def mapCommMon (e : C ≌ D) [e.functor.Braided] [e.inverse.Braided] [e.IsMonoidal] :
    CommMon C ≌ CommMon D where
  functor := e.functor.mapCommMon
  inverse := e.inverse.mapCommMon
  unitIso := mapCommMonIdIso.symm ≪≫ mapCommMonNatIso e.unitIso ≪≫ mapCommMonCompIso
  counitIso := mapCommMonCompIso.symm ≪≫ mapCommMonNatIso e.counitIso ≪≫ mapCommMonIdIso

end Equivalence

namespace CommMon

open LaxBraidedFunctor

namespace EquivLaxBraidedFunctorPUnit

variable (C) in
/-- Implementation of `CommMon.equivLaxBraidedFunctorPUnit`. -/
@[simps]
/--
Definition of `laxBraidedToCommMon` / `laxBraidedToCommMon` 的定义

English:
definition laxBraidedToCommMon
  signature: : LaxBraidedFunctor (Discrete PUnit.{u + 1}) C ⥤ CommMon C where
  body: (F.mapCommMon : CommMon _ ⥤ CommMon C).obj (trivial (Discrete PUnit.{u + 1}))
  map α := ((Functor.mapCommMonFunctor (Discrete PUnit) C).map α).app _

中文:
定义 laxBraidedToCommMon
  签名: : LaxBraidedFunctor (Discrete PUnit.{u + 1}) C ⥤ CommMon C where
  定义体: (F.mapCommMon : CommMon _ ⥤ CommMon C).obj (trivial (Discrete PUnit.{u + 1}))
  map α := ((Functor.mapCommMonFunctor (Discrete PUnit) C).map α).app _

Depends on / 依赖: CommMon, Discrete, F.mapCommMon, mapCommMon
-/
def laxBraidedToCommMon : LaxBraidedFunctor (Discrete PUnit.{u + 1}) C ⥤ CommMon C where
  obj F := (F.mapCommMon : CommMon _ ⥤ CommMon C).obj (trivial (Discrete PUnit.{u + 1}))
  map α := ((Functor.mapCommMonFunctor (Discrete PUnit) C).map α).app _

/-- Implementation of `CommMon.equivLaxBraidedFunctorPUnit`. -/
@[simps!]
/--
Definition of `commMonToLaxBraidedObj` / `commMonToLaxBraidedObj` 的定义

English:
definition commMonToLaxBraidedObj
  signature: (A : CommMon C)
  body: (Functor.const _).obj A.X

中文:
定义 commMonToLaxBraidedObj
  签名: (A : CommMon C)
  定义体: (Functor.const _).obj A.X

Depends on / 依赖: Functor, Functor.const
-/
def commMonToLaxBraidedObj (A : CommMon C) :
    Discrete PUnit.{u + 1} ⥤ C := (Functor.const _).obj A.X

set_option backward.defeqAttrib.useBackward true in
instance (A : CommMon C) : (commMonToLaxBraidedObj A).LaxMonoidal where
  ε := η[A.X]
  «μ» _ _ := μ[A.X]

open Functor.LaxMonoidal

@[simp]
/--
lemma `commMonToLaxBraidedObj_ε` / 引理 `commMonToLaxBraidedObj_ε`

English:
lemma commMonToLaxBraidedObj_ε
  given: (A : CommMon C)
  proof: rfl

@[simp]

中文:
引理 commMonToLaxBraidedObj_ε
  条件: (A : CommMon C)
  证明: rfl

@[simp]
-/
lemma commMonToLaxBraidedObj_ε (A : CommMon C) :
    ε (commMonToLaxBraidedObj A) = η[A.X] := rfl

@[simp]
/--
lemma `commMonToLaxBraidedObj_μ` / 引理 `commMonToLaxBraidedObj_μ`

English:
lemma commMonToLaxBraidedObj_μ
  given: (A : CommMon C) (X Y)
  proof: rfl

中文:
引理 commMonToLaxBraidedObj_μ
  条件: (A : CommMon C) (X Y)
  证明: rfl
-/
lemma commMonToLaxBraidedObj_μ (A : CommMon C) (X Y) :
    «μ» (commMonToLaxBraidedObj A) X Y = μ[A.X] := rfl

set_option backward.defeqAttrib.useBackward true in
instance (A : CommMon C) : (commMonToLaxBraidedObj A).LaxBraided where

variable (C)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Implementation of `CommMon.equivLaxBraidedFunctorPUnit`. -/
@[simps]
/--
Definition of `commMonToLaxBraided` / `commMonToLaxBraided` 的定义

English:
definition commMonToLaxBraided
  signature: : CommMon C ⥤ LaxBraidedFunctor (Discrete PUnit.{u + 1}) C where
  body: LaxBraidedFunctor.of (commMonToLaxBraidedObj A)
  map f :=
    { hom :=
      { hom := { app _ := f.hom.hom }
        isMonoidal := { } } }

中文:
定义 commMonToLaxBraided
  签名: : CommMon C ⥤ LaxBraidedFunctor (Discrete PUnit.{u + 1}) C where
  定义体: LaxBraidedFunctor.of (commMonToLaxBraidedObj A)
  map f :=
    { hom :=
      { hom := { app _ := f.hom.hom }
        isMonoidal := { } } }

Depends on / 依赖: LaxBraidedFunctor, LaxBraidedFunctor.of, commMonToLaxBraidedObj
-/
def commMonToLaxBraided : CommMon C ⥤ LaxBraidedFunctor (Discrete PUnit.{u + 1}) C where
  obj A := LaxBraidedFunctor.of (commMonToLaxBraidedObj A)
  map f :=
    { hom :=
      { hom := { app _ := f.hom.hom }
        isMonoidal := { } } }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Implementation of `CommMon.equivLaxBraidedFunctorPUnit`. -/
@[simps!]
/--
Definition of `unitIso` / `unitIso` 的定义

English:
definition unitIso
  signature: :
  body: NatIso.ofComponents
    (fun F => LaxBraidedFunctor.isoOfComponents (fun _ => F.mapIso (eqToIso (by ext))))
    (fun f => by ext ⟨⟨⟩⟩; dsimp; simp)

@[simp]

中文:
定义 unitIso
  签名: :
  定义体: NatIso.ofComponents
    (fun F => LaxBraidedFunctor.isoOfComponents (fun _ => F.mapIso (eqToIso (by ext))))
    (fun f => by ext ⟨⟨⟩⟩; dsimp; simp)

@[simp]

Depends on / 依赖: F.mapIso, LaxBraidedFunctor, LaxBraidedFunctor.isoOfComponents, NatIso, NatIso.ofComponents, eqToIso, isoOfComponents, mapIso, ofComponents
-/
def unitIso :
    𝟭 (LaxBraidedFunctor (Discrete PUnit.{u + 1}) C) ≅
        laxBraidedToCommMon C ⋙ commMonToLaxBraided C :=
  NatIso.ofComponents
    (fun F => LaxBraidedFunctor.isoOfComponents (fun _ => F.mapIso (eqToIso (by ext))))
    (fun f => by ext ⟨⟨⟩⟩; dsimp; simp)

@[simp]
/--
theorem `counitIso_aux_one` / 定理 `counitIso_aux_one`

English:
theorem counitIso_aux_one
  given: (A : CommMon C)
  proof: rfl

@[simp]

中文:
定理 counitIso_aux_one
  条件: (A : CommMon C)
  证明: rfl

@[simp]
-/
theorem counitIso_aux_one (A : CommMon C) :
    η[((commMonToLaxBraided C ⋙ laxBraidedToCommMon C).obj A).X] = η[A.X] ≫ 𝟙 _ :=
  rfl

@[simp]
/--
theorem `counitIso_aux_mul` / 定理 `counitIso_aux_mul`

English:
theorem counitIso_aux_mul
  given: (A : CommMon C)
  proof: rfl

中文:
定理 counitIso_aux_mul
  条件: (A : CommMon C)
  证明: rfl
-/
theorem counitIso_aux_mul (A : CommMon C) :
    μ[((commMonToLaxBraided C ⋙ laxBraidedToCommMon C).obj A).X] = μ[A.X] ≫ 𝟙 _ :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Implementation of `CommMon.equivLaxBraidedFunctorPUnit`. -/
@[simps!]
/--
Definition of `counitIso` / `counitIso` 的定义

English:
definition counitIso
  signature: : commMonToLaxBraided C ⋙ laxBraidedToCommMon C ≅ 𝟭 (CommMon C)
  body: NatIso.ofComponents (fun F => mkIso (Iso.refl _))

中文:
定义 counitIso
  签名: : commMonToLaxBraided C ⋙ laxBraidedToCommMon C ≅ 𝟭 (CommMon C)
  定义体: NatIso.ofComponents (fun F => mkIso (Iso.refl _))

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def counitIso : commMonToLaxBraided C ⋙ laxBraidedToCommMon C ≅ 𝟭 (CommMon C) :=
  NatIso.ofComponents (fun F => mkIso (Iso.refl _))

end EquivLaxBraidedFunctorPUnit

open EquivLaxBraidedFunctorPUnit

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Commutative monoid objects in `C` are "just" braided lax monoidal functors from the trivial
braided monoidal category to `C`.
-/
@[simps]
/--
Definition of `equivLaxBraidedFunctorPUnit` / `equivLaxBraidedFunctorPUnit` 的定义

English:
definition equivLaxBraidedFunctorPUnit
  signature: : LaxBraidedFunctor (Discrete PUnit.{u + 1}) C ≌ CommMon C where
  body: laxBraidedToCommMon C
  inverse := commMonToLaxBraided C
  unitIso := unitIso C
  counitIso := counitIso C

中文:
定义 equivLaxBraidedFunctorPUnit
  签名: : LaxBraidedFunctor (Discrete PUnit.{u + 1}) C ≌ CommMon C where
  定义体: laxBraidedToCommMon C
  inverse := commMonToLaxBraided C
  unitIso := unitIso C
  counitIso := counitIso C

Depends on / 依赖: laxBraidedToCommMon
-/
def equivLaxBraidedFunctorPUnit : LaxBraidedFunctor (Discrete PUnit.{u + 1}) C ≌ CommMon C where
  functor := laxBraidedToCommMon C
  inverse := commMonToLaxBraided C
  unitIso := unitIso C
  counitIso := counitIso C

end CommMon
end CategoryTheory
