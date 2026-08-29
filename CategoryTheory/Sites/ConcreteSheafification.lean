/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.CategoryTheory.Sites.Plus
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory

/-!

# Sheafification

We construct the sheafification of a presheaf over a site `C` with values in `D` whenever
`D` is a concrete category for which the forgetful functor preserves the appropriate (co)limits
and reflects isomorphisms.

We generally follow the approach of https://stacks.math.columbia.edu/tag/00W1

-/

@[expose] public section


namespace CategoryTheory

open CategoryTheory.Limits Opposite

universe t w' w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {D : Type w} [Category.{w'} D]

section

variable {FD : D -> D -> Type*} {CD : D -> Type t} [forall X Y, FunLike (FD X Y) (CD X) (CD Y)]
variable [ConcreteCategory.{t} D FD]

/--
Definition of `Meq` / `Meq` 的定义

English:
definition Meq
  signature: {X : C} (P : Cᵒᵖ ⥤ D) (S : J.Cover X)
  body: { x : forall I : S.Arrow, ToType (P.obj (op I.Y)) //
    forall I : S.Relation, P.map I.r.g₁.op (x I.fst) = P.map I.r.g₂.op (x I.snd) }

中文:
定义 Meq
  签名: {X : C} (P : Cᵒᵖ ⥤ D) (S : J.Cover X)
  定义体: { x : forall I : S.Arrow, ToType (P.obj (op I.Y)) //
    forall I : S.Relation, P.map I.r.g₁.op (x I.fst) = P.map I.r.g₂.op (x I.snd) }

Depends on / 依赖: I.fst, I.r.g, I.snd, P.map, P.obj, Relation, S.Arrow, S.Relation, ToType
-/
def Meq {X : C} (P : Cᵒᵖ ⥤ D) (S : J.Cover X) :=
  { x : forall I : S.Arrow, ToType (P.obj (op I.Y)) //
    forall I : S.Relation, P.map I.r.g₁.op (x I.fst) = P.map I.r.g₂.op (x I.snd) }

end

namespace Meq

variable {FD : D -> D -> Type*} {CD : D -> Type t} [forall X Y, FunLike (FD X Y) (CD X) (CD Y)]
variable [ConcreteCategory.{t} D FD]

instance {X} (P : Cᵒᵖ ⥤ D) (S : J.Cover X) :
    CoeFun (Meq P S) fun _ => forall I : S.Arrow, ToType (P.obj (op I.Y)) :=
  ⟨fun x => x.1⟩

/--
lemma `congr_apply` / 引理 `congr_apply`

English:
lemma congr_apply
  statement: {X} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x : Meq P S) {Y}
  proof: by
  subst h
  rfl

@[ext]

中文:
引理 congr_apply
  结论: {X} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x : Meq P S) {Y}
  证明: by
  subst h
  rfl

@[ext]
-/
lemma congr_apply {X} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x : Meq P S) {Y}
    {f g : Y ⟶ X} (h : f = g) (hf : S f) :
    x ⟨_, _, hf⟩ = x ⟨_, g, by simpa only [← h] using hf⟩ := by
  subst h
  rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {X} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x y : Meq P S) (h : forall I : S.Arrow, x I = y I)
  proof: Subtype.ext funext h

中文:
定理 ext
  条件: {X} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x y : Meq P S) (h : 对任意 I : S.箭头, x I = y I)
  证明: Subtype.ext funext h

Depends on / 依赖: Subtype, Subtype.ext, cardinalMk_sdiff_comm, hIX.isBasis_inter_ground.cardinalMk_sdiff_comm, hJX.isBasis_inter_ground, isBasis_inter_ground
-/
theorem ext {X} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x y : Meq P S) (h : forall I : S.Arrow, x I = y I) :
    x = y :=
Subtype.ext funext h

/--
theorem `condition` / 定理 `condition`

English:
theorem condition
  given: {X} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x : Meq P S) (I : S.Relation)
  proof: x.2 _

中文:
定理 condition
  条件: {X} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x : Meq P S) (I : S.关系)
  证明: x.2 _
-/
theorem condition {X} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x : Meq P S) (I : S.Relation) :
    P.map I.r.g₁.op (x (S.shape.fst I)) = P.map I.r.g₂.op (x (S.shape.snd I)) :=
  x.2 _

/--
Definition of `refine` / `refine` 的定义

English:
definition refine
  signature: {X : C} {P : Cᵒᵖ ⥤ D} {S T : J.Cover X} (x : Meq P T) (e : S ⟶ T)
  body: ⟨fun I => x ⟨I.Y, I.f, (leOfHom e) _ I.hf⟩, fun I =>
    x.condition (GrothendieckTopology.Cover.Relation.mk' (I.r.map e))⟩

@[simp]

中文:
定义 refine
  签名: {X : C} {P : Cᵒᵖ ⥤ D} {S T : J.Cover X} (x : Meq P T) (e : S ⟶ T)
  定义体: ⟨fun I => x ⟨I.Y, I.f, (leOfHom e) _ I.hf⟩, fun I =>
    x.condition (GrothendieckTopology.Cover.Relation.mk' (I.r.map e))⟩

@[simp]

Depends on / 依赖: GrothendieckTopology, GrothendieckTopology.Cover.Relation.mk, I.hf, I.r.map, Relation, condition, leOfHom, x.condition
-/
def refine {X : C} {P : Cᵒᵖ ⥤ D} {S T : J.Cover X} (x : Meq P T) (e : S ⟶ T) : Meq P S :=
  ⟨fun I => x ⟨I.Y, I.f, (leOfHom e) _ I.hf⟩, fun I =>
    x.condition (GrothendieckTopology.Cover.Relation.mk' (I.r.map e))⟩

@[simp]
/--
theorem `refine_apply` / 定理 `refine_apply`

English:
theorem refine_apply
  statement: {X : C} {P : Cᵒᵖ ⥤ D} {S T : J.Cover X} (x : Meq P T) (e : S ⟶ T)
  proof: rfl

中文:
定理 refine_apply
  结论: {X : C} {P : Cᵒᵖ ⥤ D} {S T : J.Cover X} (x : Meq P T) (e : S ⟶ T)
  证明: rfl

Depends on / 依赖: cardinalMk_eq, hIX.isBasis_inter_ground.cardinalMk_eq, hJX.isBasis_inter_ground, isBasis_inter_ground
-/
theorem refine_apply {X : C} {P : Cᵒᵖ ⥤ D} {S T : J.Cover X} (x : Meq P T) (e : S ⟶ T)
    (I : S.Arrow) : x.refine e I = x ⟨I.Y, I.f, (leOfHom e) _ I.hf⟩ :=
  rfl

/--
Definition of `pullback` / `pullback` 的定义

English:
definition pullback
  signature: {Y X : C} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x : Meq P S) (f : Y ⟶ X)
  body: ⟨fun I => x ⟨_, I.f ≫ f, I.hf⟩, fun I =>
    x.condition (GrothendieckTopology.Cover.Relation.mk' I.r.base)⟩

@[simp]

中文:
定义 pullback
  签名: {Y X : C} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x : Meq P S) (f : Y ⟶ X)
  定义体: ⟨fun I => x ⟨_, I.f ≫ f, I.hf⟩, fun I =>
    x.condition (GrothendieckTopology.Cover.Relation.mk' I.r.base)⟩

@[simp]

Depends on / 依赖: GrothendieckTopology, GrothendieckTopology.Cover.Relation.mk, I.hf, I.r.base, Relation, condition, x.condition
-/
def pullback {Y X : C} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x : Meq P S) (f : Y ⟶ X) :
    Meq P ((J.pullback f).obj S) :=
  ⟨fun I => x ⟨_, I.f ≫ f, I.hf⟩, fun I =>
    x.condition (GrothendieckTopology.Cover.Relation.mk' I.r.base)⟩

@[simp]
/--
theorem `pullback_apply` / 定理 `pullback_apply`

English:
theorem pullback_apply
  statement: {Y X : C} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x : Meq P S) (f : Y ⟶ X)
  proof: rfl

@[simp]

中文:
定理 pullback_apply
  结论: {Y X : C} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x : Meq P S) (f : Y ⟶ X)
  证明: rfl

@[simp]
-/
theorem pullback_apply {Y X : C} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x : Meq P S) (f : Y ⟶ X)
    (I : ((J.pullback f).obj S).Arrow) : x.pullback f I = x ⟨_, I.f ≫ f, I.hf⟩ :=
  rfl

@[simp]
/--
theorem `pullback_refine` / 定理 `pullback_refine`

English:
theorem pullback_refine
  statement: {Y X : C} {P : Cᵒᵖ ⥤ D} {S T : J.Cover X} (h : S ⟶ T) (f : Y ⟶ X)
  proof: rfl

中文:
定理 pullback_refine
  结论: {Y X : C} {P : Cᵒᵖ ⥤ D} {S T : J.Cover X} (h : S ⟶ T) (f : Y ⟶ X)
  证明: rfl
-/
theorem pullback_refine {Y X : C} {P : Cᵒᵖ ⥤ D} {S T : J.Cover X} (h : S ⟶ T) (f : Y ⟶ X)
    (x : Meq P T) : (x.pullback f).refine ((J.pullback f).map h) = (refine x h).pullback _ :=
  rfl

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: {X : C} {P : Cᵒᵖ ⥤ D} (S : J.Cover X) (x : ToType (P.obj (op X)))
  body: ⟨fun I => P.map I.f.op x, fun I => by
    simp only [← ConcreteCategory.comp_apply, ← P.map_comp, ← op_comp, I.r.w]⟩

中文:
定义 mk
  签名: {X : C} {P : Cᵒᵖ ⥤ D} (S : J.Cover X) (x : ToType (P.obj (op X)))
  定义体: ⟨fun I => P.map I.f.op x, fun I => by
    simp only [← ConcreteCategory.comp_apply, ← P.map_comp, ← op_comp, I.r.w]⟩

Depends on / 依赖: ConcreteCategory, ConcreteCategory.comp_apply, I.f.op, I.r.w, P.map, P.map_comp, comp_apply, map_comp, op_comp
-/
def mk {X : C} {P : Cᵒᵖ ⥤ D} (S : J.Cover X) (x : ToType (P.obj (op X))) : Meq P S :=
  ⟨fun I => P.map I.f.op x, fun I => by
    simp only [← ConcreteCategory.comp_apply, ← P.map_comp, ← op_comp, I.r.w]⟩

/--
theorem `mk_apply` / 定理 `mk_apply`

English:
theorem mk_apply
  given: {X : C} {P : Cᵒᵖ ⥤ D} (S : J.Cover X) (x : ToType (P.obj (op X))) (I : S.Arrow)
  proof: rfl

中文:
定理 mk_apply
  条件: {X : C} {P : Cᵒᵖ ⥤ D} (S : J.Cover X) (x : ToType (P.obj (op X))) (I : S.箭头)
  证明: rfl
-/
theorem mk_apply {X : C} {P : Cᵒᵖ ⥤ D} (S : J.Cover X) (x : ToType (P.obj (op X))) (I : S.Arrow) :
    mk S x I = P.map I.f.op x :=
  rfl

variable [forall {X : C} (S : J.Cover X),
  PreservesLimitsOfShape (WalkingMulticospan S.shape) (forget D)]

/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: {X : C} (P : Cᵒᵖ ⥤ D) (S : J.Cover X) [HasMultiequalizer (S.index P)]
  body: Limits.Concrete.multiequalizerEquiv.{t} (C := D) _

@[simp]

中文:
定义 equiv
  签名: {X : C} (P : Cᵒᵖ ⥤ D) (S : J.Cover X) [HasMultiequalizer (S.index P)]
  定义体: Limits.Concrete.multiequalizerEquiv.{t} (C := D) _

@[simp]

Depends on / 依赖: Concrete, Limits, Limits.Concrete.multiequalizerEquiv, multiequalizerEquiv
-/
noncomputable def equiv {X : C} (P : Cᵒᵖ ⥤ D) (S : J.Cover X) [HasMultiequalizer (S.index P)] :
    ToType (multiequalizer (S.index P)) ≃ Meq P S :=
  Limits.Concrete.multiequalizerEquiv.{t} (C := D) _

@[simp]
/--
theorem `equiv_apply` / 定理 `equiv_apply`

English:
theorem equiv_apply
  statement: {X : C} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} [HasMultiequalizer (S.index P)]
  proof: rfl

中文:
定理 equiv_apply
  结论: {X : C} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} [HasMultiequalizer (S.index P)]
  证明: rfl

Depends on / 依赖: cardinalMk_eq_cRank, isBase_restrict_iff
-/
theorem equiv_apply {X : C} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} [HasMultiequalizer (S.index P)]
    (x : ToType (multiequalizer (S.index P))) (I : S.Arrow) :
    equiv P S x I = Multiequalizer.ι (S.index P) I x :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `equiv_symm_eq_apply` / 定理 `equiv_symm_eq_apply`

English:
theorem equiv_symm_eq_apply
  statement: {X : C} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} [HasMultiequalizer (S.index P)]
  proof: by
  simp [-GrothendieckTopology.Cover.index_left, ← equiv_apply]

中文:
定理 equiv_symm_eq_apply
  结论: {X : C} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} [HasMultiequalizer (S.index P)]
  证明: by
  simp [-GrothendieckTopology.Cover.index_left, ← equiv_apply]

Depends on / 依赖: P.obj, normal
-/
theorem equiv_symm_eq_apply {X : C} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} [HasMultiequalizer (S.index P)]
    (x : Meq P S) (I : S.Arrow) :
    -- We can hint `ConcreteCategory.hom (Y := P.obj (op I.Y))` below to put it into `simp`-normal
    -- form, but that doesn't seem to fix the `erw`s below...
    (Multiequalizer.ι (S.index P) I) ((Meq.equiv P S).symm x) = x I := by
  simp [-GrothendieckTopology.Cover.index_left, ← equiv_apply]

end Meq

namespace GrothendieckTopology

namespace Plus

variable {FD : D -> D -> Type*} {CD : D -> Type t} [forall X Y, FunLike (FD X Y) (CD X) (CD Y)]
variable [instCC : ConcreteCategory.{t} D FD]

variable [forall {X : C} (S : J.Cover X),
  PreservesLimitsOfShape (WalkingMulticospan S.shape) (forget D)]
variable [forall X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]
variable [forall (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]

noncomputable section

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: {X : C} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x : Meq P S)
  body: colimit.ι (J.diagram P X) (op S) ((Meq.equiv P S).symm x)

中文:
定义 mk
  签名: {X : C} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x : Meq P S)
  定义体: colimit.ι (J.diagram P X) (op S) ((Meq.equiv P S).symm x)

Depends on / 依赖: J.diagram, Meq.equiv, colimit, diagram
-/
def mk {X : C} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x : Meq P S) : ToType ((J.plusObj P).obj (op X)) :=
  colimit.ι (J.diagram P X) (op S) ((Meq.equiv P S).symm x)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `res_mk_eq_mk_pullback` / 定理 `res_mk_eq_mk_pullback`

English:
theorem res_mk_eq_mk_pullback
  given: {Y X : C} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x : Meq P S) (f : Y ⟶ X)
  proof: by
  dsimp [mk, plusObj]
  rw [← CategoryTheory.comp_apply (x := (Meq.equiv P S).symm x)]; rw [ι_colimMap_assoc]; rw [colimit.ι_pre]; rw [CategoryTheory.comp_apply (x := (Meq.equiv P S).symm x)]
  apply congr_arg
  apply (Meq.equiv P _).injective
  dsimp
  simp only [Equiv.apply_symm_apply]
  ext i
  simp only [Meq.equiv_apply, Cover.index_left, ← ConcreteCategory.comp_apply, limit.lift_π,
    Multifork.ofι_pt, Multifork.ofι_π_app, Meq.pullback_apply, pullback_obj]
  rw [dsimp% Meq.equiv_symm_eq_apply x i.base]
  cases i; rfl

中文:
定理 res_mk_eq_mk_pullback
  条件: {Y X : C} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x : Meq P S) (f : Y ⟶ X)
  证明: by
  dsimp [mk, plusObj]
  rw [← CategoryTheory.comp_apply (x := (Meq.equiv P S).symm x)]; rw [ι_colimMap_assoc]; rw [colimit.ι_pre]; rw [CategoryTheory.comp_apply (x := (Meq.equiv P S).symm x)]
  apply congr_arg
  apply (Meq.equiv P _).injective
  dsimp
  simp only [Equiv.apply_symm_apply]
  ext i
  simp only [Meq.equiv_apply, Cover.index_left, ← ConcreteCategory.comp_apply, limit.lift_π,
    Multifork.ofι_pt, Multifork.ofι_π_app, Meq.pullback_apply, pullback_obj]
  rw [dsimp% Meq.equiv_symm_eq_apply x i.base]
  cases i; rfl

Depends on / 依赖: CategoryTheory, CategoryTheory.comp_apply, ConcreteCategory, ConcreteCategory.comp_apply, Cover.index_left, Equiv.apply_symm_apply, Meq.equiv, Meq.equiv_apply, Meq.equiv_symm_eq_apply, Meq.pullback_apply, Multifork, Multifork.of, apply_symm_apply, colimit, comp_apply, congr_arg, equiv_apply, equiv_symm_eq_apply, i.base, index_left
-/
theorem res_mk_eq_mk_pullback {Y X : C} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x : Meq P S) (f : Y ⟶ X) :
    (J.plusObj P).map f.op (mk x) = mk (x.pullback f) := by
  dsimp [mk, plusObj]
  rw [← CategoryTheory.comp_apply (x := (Meq.equiv P S).symm x)]; rw [ι_colimMap_assoc]; rw [colimit.ι_pre]; rw [CategoryTheory.comp_apply (x := (Meq.equiv P S).symm x)]
  apply congr_arg
  apply (Meq.equiv P _).injective
  dsimp
  simp only [Equiv.apply_symm_apply]
  ext i
  simp only [Meq.equiv_apply, Cover.index_left, ← ConcreteCategory.comp_apply, limit.lift_π,
    Multifork.ofι_pt, Multifork.ofι_π_app, Meq.pullback_apply, pullback_obj]
  rw [dsimp% Meq.equiv_symm_eq_apply x i.base]
  cases i; rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `toPlus_mk` / 定理 `toPlus_mk`

English:
theorem toPlus_mk
  given: {X : C} {P : Cᵒᵖ ⥤ D} (S : J.Cover X) (x : ToType (P.obj (op X)))
  proof: by
  dsimp [mk, toPlus]
  let e : S ⟶ ⊤ := homOfLE (OrderTop.le_top _)
  rw [← colimit.w _ e.op]
  delta Cover.toMultiequalizer
  rw [ConcreteCategory.comp_apply]; rw [ConcreteCategory.comp_apply]
  apply congr_arg
  dsimp [diagram]
  apply Concrete.multiequalizer_ext (C := D)
  intro i
  simp only [← ConcreteCategory.comp_apply, Category.assoc, Multiequalizer.lift_ι,
    Meq.equiv_symm_eq_apply]
  rfl

中文:
定理 toPlus_mk
  条件: {X : C} {P : Cᵒᵖ ⥤ D} (S : J.Cover X) (x : ToType (P.obj (op X)))
  证明: by
  dsimp [mk, toPlus]
  let e : S ⟶ ⊤ := homOfLE (OrderTop.le_top _)
  rw [← colimit.w _ e.op]
  delta Cover.toMultiequalizer
  rw [ConcreteCategory.comp_apply]; rw [ConcreteCategory.comp_apply]
  apply congr_arg
  dsimp [diagram]
  apply Concrete.multiequalizer_ext (C := D)
  intro i
  simp only [← ConcreteCategory.comp_apply, Category.assoc, Multiequalizer.lift_ι,
    Meq.equiv_symm_eq_apply]
  rfl

Depends on / 依赖: Category, Category.assoc, Concrete, Concrete.multiequalizer_ext, ConcreteCategory, ConcreteCategory.comp_apply, Cover.toMultiequalizer, Meq.equiv_symm_eq_apply, Multiequalizer, Multiequalizer.lift_, OrderTop, OrderTop.le_top, colimit, colimit.w, comp_apply, congr_arg, diagram, e.op, equiv_symm_eq_apply, homOfLE
-/
theorem toPlus_mk {X : C} {P : Cᵒᵖ ⥤ D} (S : J.Cover X) (x : ToType (P.obj (op X))) :
    (J.toPlus P).app _ x = mk (Meq.mk S x) := by
  dsimp [mk, toPlus]
  let e : S ⟶ ⊤ := homOfLE (OrderTop.le_top _)
  rw [← colimit.w _ e.op]
  delta Cover.toMultiequalizer
  rw [ConcreteCategory.comp_apply]; rw [ConcreteCategory.comp_apply]
  apply congr_arg
  dsimp [diagram]
  apply Concrete.multiequalizer_ext (C := D)
  intro i
  simp only [← ConcreteCategory.comp_apply, Category.assoc, Multiequalizer.lift_ι,
    Meq.equiv_symm_eq_apply]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `toPlus_apply` / 定理 `toPlus_apply`

English:
theorem toPlus_apply
  given: {X : C} {P : Cᵒᵖ ⥤ D} (S : J.Cover X) (x : Meq P S) (I : S.Arrow)
  proof: by
  dsimp only [toPlus, plusObj]
  delta Cover.toMultiequalizer
  dsimp [mk]
  rw [← ConcreteCategory.comp_apply]; rw [ι_colimMap_assoc]; rw [colimit.ι_pre]; rw [ConcreteCategory.comp_apply]; rw [ConcreteCategory.comp_apply]
  dsimp only [Functor.op]
  let e : (J.pullback I.f).obj (unop (op S)) ⟶ ⊤ := homOfLE (OrderTop.le_top _)
  rw [← colimit.w _ e.op]; rw [ConcreteCategory.comp_apply]
  apply congr_arg
  apply Concrete.multiequalizer_ext (C := D)
  intro i
  dsimp
  rw [← ConcreteCategory.comp_apply]; rw [← ConcreteCategory.comp_apply]; rw [← ConcreteCategory.comp_apply]; rw [Multiequalizer.lift_ι]; rw [Multiequalizer.lift_ι]; rw [Multiequalizer.lift_ι]
  rw [dsimp% Meq.equiv_symm_eq_apply x i.base]
  simpa using! (x.condition (Cover.Relation.mk' (I.precompRelation i.f))).symm

中文:
定理 toPlus_apply
  条件: {X : C} {P : Cᵒᵖ ⥤ D} (S : J.Cover X) (x : Meq P S) (I : S.箭头)
  证明: by
  dsimp only [toPlus, plusObj]
  delta Cover.toMultiequalizer
  dsimp [mk]
  rw [← ConcreteCategory.comp_apply]; rw [ι_colimMap_assoc]; rw [colimit.ι_pre]; rw [ConcreteCategory.comp_apply]; rw [ConcreteCategory.comp_apply]
  dsimp only [Functor.op]
  let e : (J.pullback I.f).obj (unop (op S)) ⟶ ⊤ := homOfLE (OrderTop.le_top _)
  rw [← colimit.w _ e.op]; rw [ConcreteCategory.comp_apply]
  apply congr_arg
  apply Concrete.multiequalizer_ext (C := D)
  intro i
  dsimp
  rw [← ConcreteCategory.comp_apply]; rw [← ConcreteCategory.comp_apply]; rw [← ConcreteCategory.comp_apply]; rw [Multiequalizer.lift_ι]; rw [Multiequalizer.lift_ι]; rw [Multiequalizer.lift_ι]
  rw [dsimp% Meq.equiv_symm_eq_apply x i.base]
  simpa using! (x.condition (Cover.Relation.mk' (I.precompRelation i.f))).symm

Depends on / 依赖: Concret, Concrete, Concrete.multiequalizer_ext, ConcreteCategory, ConcreteCategory.comp_apply, Cover.toMultiequalizer, Functor, Functor.op, J.pullback, OrderTop, OrderTop.le_top, colimit, colimit.w, comp_apply, congr_arg, e.op, homOfLE, le_top, multiequalizer_ext, plusObj
-/
theorem toPlus_apply {X : C} {P : Cᵒᵖ ⥤ D} (S : J.Cover X) (x : Meq P S) (I : S.Arrow) :
    (J.toPlus P).app _ (x I) = (J.plusObj P).map I.f.op (mk x) := by
  dsimp only [toPlus, plusObj]
  delta Cover.toMultiequalizer
  dsimp [mk]
  rw [← ConcreteCategory.comp_apply]; rw [ι_colimMap_assoc]; rw [colimit.ι_pre]; rw [ConcreteCategory.comp_apply]; rw [ConcreteCategory.comp_apply]
  dsimp only [Functor.op]
  let e : (J.pullback I.f).obj (unop (op S)) ⟶ ⊤ := homOfLE (OrderTop.le_top _)
  rw [← colimit.w _ e.op]; rw [ConcreteCategory.comp_apply]
  apply congr_arg
  apply Concrete.multiequalizer_ext (C := D)
  intro i
  dsimp
  rw [← ConcreteCategory.comp_apply]; rw [← ConcreteCategory.comp_apply]; rw [← ConcreteCategory.comp_apply]; rw [Multiequalizer.lift_ι]; rw [Multiequalizer.lift_ι]; rw [Multiequalizer.lift_ι]
  rw [dsimp% Meq.equiv_symm_eq_apply x i.base]
  simpa using! (x.condition (Cover.Relation.mk' (I.precompRelation i.f))).symm

/--
theorem `toPlus_eq_mk` / 定理 `toPlus_eq_mk`

English:
theorem toPlus_eq_mk
  given: {X : C} {P : Cᵒᵖ ⥤ D} (x : ToType (P.obj (op X)))
  proof: toPlus_mk ⊤ x

中文:
定理 toPlus_eq_mk
  条件: {X : C} {P : Cᵒᵖ ⥤ D} (x : ToType (P.obj (op X)))
  证明: toPlus_mk ⊤ x

Depends on / 依赖: toPlus_mk
-/
theorem toPlus_eq_mk {X : C} {P : Cᵒᵖ ⥤ D} (x : ToType (P.obj (op X))) :
    (J.toPlus P).app _ x = mk (Meq.mk ⊤ x) := toPlus_mk ⊤ x

variable [forall X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget D)]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `exists_rep` / 定理 `exists_rep`

English:
theorem exists_rep
  given: {X : C} {P : Cᵒᵖ ⥤ D} (x : ToType ((J.plusObj P).obj (op X)))
  proof: by
  obtain ⟨S, y, h⟩ := Concrete.colimit_exists_rep (J.diagram P X) x
  use S.unop, Meq.equiv _ _ y
  rw [← h]
  dsimp [mk]
  simp

中文:
定理 存在_rep
  条件: {X : C} {P : Cᵒᵖ ⥤ D} (x : ToType ((J.plusObj P).obj (op X)))
  证明: by
  obtain ⟨S, y, h⟩ := Concrete.colimit_exists_rep (J.diagram P X) x
  use S.unop, Meq.equiv _ _ y
  rw [← h]
  dsimp [mk]
  simp

Depends on / 依赖: Concrete, Concrete.colimit_exists_rep, J.diagram, Meq.equiv, S.unop, colimit_exists_rep, diagram
-/
theorem exists_rep {X : C} {P : Cᵒᵖ ⥤ D} (x : ToType ((J.plusObj P).obj (op X))) :
    exists (S : J.Cover X) (y : Meq P S), x = mk y := by
  obtain ⟨S, y, h⟩ := Concrete.colimit_exists_rep (J.diagram P X) x
  use S.unop, Meq.equiv _ _ y
  rw [← h]
  dsimp [mk]
  simp

set_option backward.isDefEq.respectTransparency false in
/--
theorem `eq_mk_iff_exists` / 定理 `eq_mk_iff_exists`

English:
theorem eq_mk_iff_exists
  given: {X : C} {P : Cᵒᵖ ⥤ D} {S T : J.Cover X} (x : Meq P S) (y : Meq P T)
  proof: by
  constructor
  · intro h
    obtain ⟨W, h1, h2, hh⟩ := Concrete.colimit_exists_of_rep_eq (C := D) _ _ _ h
    use W.unop, h1.unop, h2.unop
    ext I
    apply_fun Multiequalizer.ι (W.unop.index P) I at hh
    convert! hh
    all_goals
      dsimp [diagram]
      rw [← ConcreteCategory.comp_apply]; rw [Multiequalizer.lift_ι]
      erw [Meq.equiv_symm_eq_apply]
      cases I; rfl
  · rintro ⟨S, h1, h2, e⟩
    apply Concrete.colimit_rep_eq_of_exists (C := D)
    use op S, h1.op, h2.op
    apply Concrete.multiequalizer_ext
    intro i
    apply_fun fun ee => ee i at e
    convert! e using 1
    all_goals
      dsimp [diagram]
      rw [← ConcreteCategory.comp_apply]; rw [Multiequalizer.lift_ι]
      erw [Meq.equiv_symm_eq_apply]
      cases i; rfl

中文:
定理 eq_mk_iff_存在
  条件: {X : C} {P : Cᵒᵖ ⥤ D} {S T : J.Cover X} (x : Meq P S) (y : Meq P T)
  证明: by
  constructor
  · intro h
    obtain ⟨W, h1, h2, hh⟩ := Concrete.colimit_exists_of_rep_eq (C := D) _ _ _ h
    use W.unop, h1.unop, h2.unop
    ext I
    apply_fun Multiequalizer.ι (W.unop.index P) I at hh
    convert! hh
    all_goals
      dsimp [diagram]
      rw [← ConcreteCategory.comp_apply]; rw [Multiequalizer.lift_ι]
      erw [Meq.equiv_symm_eq_apply]
      cases I; rfl
  · rintro ⟨S, h1, h2, e⟩
    apply Concrete.colimit_rep_eq_of_exists (C := D)
    use op S, h1.op, h2.op
    apply Concrete.multiequalizer_ext
    intro i
    apply_fun fun ee => ee i at e
    convert! e using 1
    all_goals
      dsimp [diagram]
      rw [← ConcreteCategory.comp_apply]; rw [Multiequalizer.lift_ι]
      erw [Meq.equiv_symm_eq_apply]
      cases i; rfl

Depends on / 依赖: Concrete, Concrete.colimit_exists_of_rep_eq, Concrete.colimit_rep_eq_of_exists, Concrete.multiequalizer_ext, ConcreteCategory, ConcreteCategory.comp_apply, Meq.equiv_symm_eq_apply, Multiequalizer, Multiequalizer.lift_, W.unop, W.unop.index, all_goals, apply_fun, colimit_exists_of_rep_eq, colimit_rep_eq_of_exists, comp_apply, convert, diagram, equiv_symm_eq_apply, h1.op
-/
theorem eq_mk_iff_exists {X : C} {P : Cᵒᵖ ⥤ D} {S T : J.Cover X} (x : Meq P S) (y : Meq P T) :
    mk x = mk y ↔ exists (W : J.Cover X) (h1 : W ⟶ S) (h2 : W ⟶ T), x.refine h1 = y.refine h2 := by
  constructor
  · intro h
    obtain ⟨W, h1, h2, hh⟩ := Concrete.colimit_exists_of_rep_eq (C := D) _ _ _ h
    use W.unop, h1.unop, h2.unop
    ext I
    apply_fun Multiequalizer.ι (W.unop.index P) I at hh
    convert! hh
    all_goals
      dsimp [diagram]
      rw [← ConcreteCategory.comp_apply]; rw [Multiequalizer.lift_ι]
      erw [Meq.equiv_symm_eq_apply]
      cases I; rfl
  · rintro ⟨S, h1, h2, e⟩
    apply Concrete.colimit_rep_eq_of_exists (C := D)
    use op S, h1.op, h2.op
    apply Concrete.multiequalizer_ext
    intro i
    apply_fun fun ee => ee i at e
    convert! e using 1
    all_goals
      dsimp [diagram]
      rw [← ConcreteCategory.comp_apply]; rw [Multiequalizer.lift_ι]
      erw [Meq.equiv_symm_eq_apply]
      cases i; rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `sep` / 定理 `sep`

English:
theorem sep
  statement: {X : C} (P : Cᵒᵖ ⥤ D) (S : J.Cover X) (x y : ToType ((J.plusObj P).obj (op X)))
  proof: by
  -- First, we choose representatives for x and y.
  obtain ⟨Sx, x, rfl⟩ := exists_rep x
  obtain ⟨Sy, y, rfl⟩ := exists_rep y
  simp only [res_mk_eq_mk_pullback] at h
  -- Next, using our assumption,
  -- choose covers over which the pullbacks of these representatives become equal.
  choose W h1 h2 hh using fun I : S.Arrow => (eq_mk_iff_exists _ _).mp (h I)
  -- To prove equality, it suffices to prove that there exists a cover over which
  -- the representatives become equal.
  rw [eq_mk_iff_exists]
  -- Construct the cover over which the representatives become equal by combining the various
  -- covers chosen above.
  let B : J.Cover X := S.bind W
  use B
  -- Prove that this cover refines the two covers over which our representatives are defined
  -- and use these proofs.
  let ex : B ⟶ Sx :=
    homOfLE
      (by
        rintro Y f ⟨Z, e1, e2, he2, he1, hee⟩
        rw [← hee]
        apply leOfHom (h1 ⟨_, _, he2⟩)
        exact he1)
  let ey : B ⟶ Sy :=
    homOfLE
      (by
        rintro Y f ⟨Z, e1, e2, he2, he1, hee⟩
        rw [← hee]
        apply leOfHom (h2 ⟨_, _, he2⟩)
        exact he1)
  use ex, ey
  -- Now prove that indeed the representatives become equal over `B`.
  -- This will follow by using the fact that our representatives become
  -- equal over the chosen covers.
  ext1 I
  let IS : S.Arrow := I.fromMiddle
  specialize hh IS
  let IW : (W IS).Arrow := I.toMiddle
  apply_fun fun e => e IW at hh
  convert! hh using 1
  · exact x.congr_apply I.middle_spec.symm _
  · exact y.congr_apply I.middle_spec.symm _

中文:
定理 sep
  结论: {X : C} (P : Cᵒᵖ ⥤ D) (S : J.Cover X) (x y : ToType ((J.plusObj P).obj (op X)))
  证明: by
  -- First, we choose representatives for x and y.
  obtain ⟨Sx, x, rfl⟩ := exists_rep x
  obtain ⟨Sy, y, rfl⟩ := exists_rep y
  simp only [res_mk_eq_mk_pullback] at h
  -- Next, using our assumption,
  -- choose covers over which the pullbacks of these representatives become equal.
  choose W h1 h2 hh using fun I : S.Arrow => (eq_mk_iff_exists _ _).mp (h I)
  -- To prove equality, it suffices to prove that there exists a cover over which
  -- the representatives become equal.
  rw [eq_mk_iff_exists]
  -- Construct the cover over which the representatives become equal by combining the various
  -- covers chosen above.
  let B : J.Cover X := S.bind W
  use B
  -- Prove that this cover refines the two covers over which our representatives are defined
  -- and use these proofs.
  let ex : B ⟶ Sx :=
    homOfLE
      (by
        rintro Y f ⟨Z, e1, e2, he2, he1, hee⟩
        rw [← hee]
        apply leOfHom (h1 ⟨_, _, he2⟩)
        exact he1)
  let ey : B ⟶ Sy :=
    homOfLE
      (by
        rintro Y f ⟨Z, e1, e2, he2, he1, hee⟩
        rw [← hee]
        apply leOfHom (h2 ⟨_, _, he2⟩)
        exact he1)
  use ex, ey
  -- Now prove that indeed the representatives become equal over `B`.
  -- This will follow by using the fact that our representatives become
  -- equal over the chosen covers.
  ext1 I
  let IS : S.Arrow := I.fromMiddle
  specialize hh IS
  let IW : (W IS).Arrow := I.toMiddle
  apply_fun fun e => e IW at hh
  convert! hh using 1
  · exact x.congr_apply I.middle_spec.symm _
  · exact y.congr_apply I.middle_spec.symm _
-/
theorem sep {X : C} (P : Cᵒᵖ ⥤ D) (S : J.Cover X) (x y : ToType ((J.plusObj P).obj (op X)))
    (h : forall I : S.Arrow, (J.plusObj P).map I.f.op x = (J.plusObj P).map I.f.op y) : x = y := by
  -- First, we choose representatives for x and y.
  obtain ⟨Sx, x, rfl⟩ := exists_rep x
  obtain ⟨Sy, y, rfl⟩ := exists_rep y
  simp only [res_mk_eq_mk_pullback] at h
  -- Next, using our assumption,
  -- choose covers over which the pullbacks of these representatives become equal.
  choose W h1 h2 hh using fun I : S.Arrow => (eq_mk_iff_exists _ _).mp (h I)
  -- To prove equality, it suffices to prove that there exists a cover over which
  -- the representatives become equal.
  rw [eq_mk_iff_exists]
  -- Construct the cover over which the representatives become equal by combining the various
  -- covers chosen above.
  let B : J.Cover X := S.bind W
  use B
  -- Prove that this cover refines the two covers over which our representatives are defined
  -- and use these proofs.
  let ex : B ⟶ Sx :=
    homOfLE
      (by
        rintro Y f ⟨Z, e1, e2, he2, he1, hee⟩
        rw [← hee]
        apply leOfHom (h1 ⟨_, _, he2⟩)
        exact he1)
  let ey : B ⟶ Sy :=
    homOfLE
      (by
        rintro Y f ⟨Z, e1, e2, he2, he1, hee⟩
        rw [← hee]
        apply leOfHom (h2 ⟨_, _, he2⟩)
        exact he1)
  use ex, ey
  -- Now prove that indeed the representatives become equal over `B`.
  -- This will follow by using the fact that our representatives become
  -- equal over the chosen covers.
  ext1 I
  let IS : S.Arrow := I.fromMiddle
  specialize hh IS
  let IW : (W IS).Arrow := I.toMiddle
  apply_fun fun e => e IW at hh
  convert! hh using 1
  · exact x.congr_apply I.middle_spec.symm _
  · exact y.congr_apply I.middle_spec.symm _

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `inj_of_sep` / 定理 `inj_of_sep`

English:
theorem inj_of_sep
  statement: (P : Cᵒᵖ ⥤ D)
  proof: by
  intro x y h
  simp only [toPlus_eq_mk] at h
  rw [eq_mk_iff_exists] at h
  obtain ⟨W, h1, h2, hh⟩ := h
  apply hsep X W
  intro I
  apply_fun fun e => e I at hh
  exact hh

中文:
定理 inj_of_sep
  结论: (P : Cᵒᵖ ⥤ D)
  证明: by
  intro x y h
  simp only [toPlus_eq_mk] at h
  rw [eq_mk_iff_exists] at h
  obtain ⟨W, h1, h2, hh⟩ := h
  apply hsep X W
  intro I
  apply_fun fun e => e I at hh
  exact hh

Depends on / 依赖: apply_fun, eq_mk_iff_exists, toPlus_eq_mk
-/
theorem inj_of_sep (P : Cᵒᵖ ⥤ D)
    (hsep :
      forall (X : C) (S : J.Cover X) (x y : ToType (P.obj (op X))),
        (forall I : S.Arrow, P.map I.f.op x = P.map I.f.op y) -> x = y)
    (X : C) : Function.Injective ((J.toPlus P).app (op X)) := by
  intro x y h
  simp only [toPlus_eq_mk] at h
  rw [eq_mk_iff_exists] at h
  obtain ⟨W, h1, h2, hh⟩ := h
  apply hsep X W
  intro I
  apply_fun fun e => e I at hh
  exact hh

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `meqOfSep` / `meqOfSep` 的定义

English:
definition meqOfSep
  signature: (P : Cᵒᵖ ⥤ D)
  body: t I.fromMiddle I.toMiddle
  property := by
    intro II
    apply inj_of_sep P hsep
    rw [← ConcreteCategory.comp_apply]; rw [← ConcreteCategory.comp_apply]; rw [(J.toPlus P).naturality]; rw [(J.toPlus P).naturality]; rw [ConcreteCategory.comp_apply]; rw [ConcreteCategory.comp_apply]
    erw [toPlus_apply (T II.fst.fromMiddle) (t II.fst.fromMiddle) II.fst.toMiddle,
      toPlus_apply (T II.snd.fromMiddle) (t II.snd.fromMiddle) II.snd.toMiddle]
    rw [← ht]; rw [← ht]
    erw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply];
    rw [← (J.plusObj P).map_comp]; rw [← (J.plusObj P).map_comp]; rw [← op_comp]; rw [← op_comp]
    exact s.condition
      { fst.hf := II.fst.from_middle_condition
        snd.hf := II.snd.from_middle_condition
        r.g₁ := II.r.g₁ ≫ II.fst.toMiddleHom
        r.g₂ := II.r.g₂ ≫ II.snd.toMiddleHom
        r.w := by simpa only [Category.assoc, Cover.Arrow.middle_spec] using II.r.w
        .. }

中文:
定义 meqOfSep
  签名: (P : Cᵒᵖ ⥤ D)
  定义体: t I.fromMiddle I.toMiddle
  property := by
    intro II
    apply inj_of_sep P hsep
    rw [← ConcreteCategory.comp_apply]; rw [← ConcreteCategory.comp_apply]; rw [(J.toPlus P).naturality]; rw [(J.toPlus P).naturality]; rw [ConcreteCategory.comp_apply]; rw [ConcreteCategory.comp_apply]
    erw [toPlus_apply (T II.fst.fromMiddle) (t II.fst.fromMiddle) II.fst.toMiddle,
      toPlus_apply (T II.snd.fromMiddle) (t II.snd.fromMiddle) II.snd.toMiddle]
    rw [← ht]; rw [← ht]
    erw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply];
    rw [← (J.plusObj P).map_comp]; rw [← (J.plusObj P).map_comp]; rw [← op_comp]; rw [← op_comp]
    exact s.condition
      { fst.hf := II.fst.from_middle_condition
        snd.hf := II.snd.from_middle_condition
        r.g₁ := II.r.g₁ ≫ II.fst.toMiddleHom
        r.g₂ := II.r.g₂ ≫ II.snd.toMiddleHom
        r.w := by simpa only [Category.assoc, Cover.Arrow.middle_spec] using II.r.w
        .. }

Depends on / 依赖: I.fromMiddle, I.toMiddle, fromMiddle, toMiddle
-/
def meqOfSep (P : Cᵒᵖ ⥤ D)
    (hsep :
      forall (X : C) (S : J.Cover X) (x y : ToType (P.obj (op X))),
        (forall I : S.Arrow, P.map I.f.op x = P.map I.f.op y) -> x = y)
    (X : C) (S : J.Cover X) (s : Meq (J.plusObj P) S) (T : forall I : S.Arrow, J.Cover I.Y)
    (t : forall I : S.Arrow, Meq P (T I)) (ht : forall I : S.Arrow, s I = mk (t I)) : Meq P (S.bind T) where
  val I := t I.fromMiddle I.toMiddle
  property := by
    intro II
    apply inj_of_sep P hsep
    rw [← ConcreteCategory.comp_apply]; rw [← ConcreteCategory.comp_apply]; rw [(J.toPlus P).naturality]; rw [(J.toPlus P).naturality]; rw [ConcreteCategory.comp_apply]; rw [ConcreteCategory.comp_apply]
    erw [toPlus_apply (T II.fst.fromMiddle) (t II.fst.fromMiddle) II.fst.toMiddle,
      toPlus_apply (T II.snd.fromMiddle) (t II.snd.fromMiddle) II.snd.toMiddle]
    rw [← ht]; rw [← ht]
    erw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply];
    rw [← (J.plusObj P).map_comp]; rw [← (J.plusObj P).map_comp]; rw [← op_comp]; rw [← op_comp]
    exact s.condition
      { fst.hf := II.fst.from_middle_condition
        snd.hf := II.snd.from_middle_condition
        r.g₁ := II.r.g₁ ≫ II.fst.toMiddleHom
        r.g₂ := II.r.g₂ ≫ II.snd.toMiddleHom
        r.w := by simpa only [Category.assoc, Cover.Arrow.middle_spec] using II.r.w
        .. }

/--
theorem `exists_of_sep` / 定理 `exists_of_sep`

English:
theorem exists_of_sep
  statement: (P : Cᵒᵖ ⥤ D)
  proof: by
  have inj : forall X : C, Function.Injective ((J.toPlus P).app (op X)) := inj_of_sep _ hsep
  -- Choose representatives for the given local sections.
  choose T t ht using fun I => exists_rep (s I)
  -- Construct a large cover over which we will define a representative that will
  -- provide the gluing of the given local sections.
  let B : J.Cover X := S.bind T
  choose Z e1 e2 he2 _ _ using fun I : B.Arrow => I.hf
  -- Construct a compatible system of local sections over this large cover, using the chosen
  -- representatives of our local sections.
  -- The compatibility here follows from the separatedness assumption.
  let w : Meq P B := meqOfSep P hsep X S s T t ht
  -- The associated gluing will be the candidate section.
  use mk w
  ext I
  dsimp [Meq.mk]
  rw [ht]; rw [res_mk_eq_mk_pullback]
  -- Use the separatedness of `P⁺` to prove that this is indeed a gluing of our
  -- original local sections.
  apply sep P (T I)
  intro II
  simp only [res_mk_eq_mk_pullback, eq_mk_iff_exists]
  -- It suffices to prove equality for representatives over a
  -- convenient sufficiently large cover...
  use (J.pullback II.f).obj (T I)
  let e0 : (J.pullback II.f).obj (T I) ⟶ (J.pullback II.f).obj ((J.pullback I.f).obj B) :=
    homOfLE
      (by
        intro Y f hf
        apply Sieve.le_pullback_bind _ _ _ I.hf
        · cases I
          exact hf)
  use e0, 𝟙 _
  ext IV
  let IA : B.Arrow := ⟨_, (IV.f ≫ II.f) ≫ I.f,
    ⟨I.Y, _, _, I.hf, Sieve.downward_closed _ II.hf _, rfl⟩⟩
  let IB : S.Arrow := IA.fromMiddle
  let IC : (T IB).Arrow := IA.toMiddle
  let ID : (T I).Arrow := ⟨IV.Y, IV.f ≫ II.f, Sieve.downward_closed (T I).1 II.hf IV.f⟩
  change t IB IC = t I ID
  apply inj IV.Y
  rw [toPlus_apply (T I) (t I) ID]
  erw [toPlus_apply (T IB) (t IB) IC]
  rw [← ht]; rw [← ht]
  -- Conclude by constructing the relation showing equality...
  let IR : S.Relation := { fst.hf := IB.hf, snd.hf := I.hf, r.w := IA.middle_spec, .. }
  exact s.condition IR

中文:
定理 存在_of_sep
  结论: (P : Cᵒᵖ ⥤ D)
  证明: by
  have inj : forall X : C, Function.Injective ((J.toPlus P).app (op X)) := inj_of_sep _ hsep
  -- Choose representatives for the given local sections.
  choose T t ht using fun I => exists_rep (s I)
  -- Construct a large cover over which we will define a representative that will
  -- provide the gluing of the given local sections.
  let B : J.Cover X := S.bind T
  choose Z e1 e2 he2 _ _ using fun I : B.Arrow => I.hf
  -- Construct a compatible system of local sections over this large cover, using the chosen
  -- representatives of our local sections.
  -- The compatibility here follows from the separatedness assumption.
  let w : Meq P B := meqOfSep P hsep X S s T t ht
  -- The associated gluing will be the candidate section.
  use mk w
  ext I
  dsimp [Meq.mk]
  rw [ht]; rw [res_mk_eq_mk_pullback]
  -- Use the separatedness of `P⁺` to prove that this is indeed a gluing of our
  -- original local sections.
  apply sep P (T I)
  intro II
  simp only [res_mk_eq_mk_pullback, eq_mk_iff_exists]
  -- It suffices to prove equality for representatives over a
  -- convenient sufficiently large cover...
  use (J.pullback II.f).obj (T I)
  let e0 : (J.pullback II.f).obj (T I) ⟶ (J.pullback II.f).obj ((J.pullback I.f).obj B) :=
    homOfLE
      (by
        intro Y f hf
        apply Sieve.le_pullback_bind _ _ _ I.hf
        · cases I
          exact hf)
  use e0, 𝟙 _
  ext IV
  let IA : B.Arrow := ⟨_, (IV.f ≫ II.f) ≫ I.f,
    ⟨I.Y, _, _, I.hf, Sieve.downward_closed _ II.hf _, rfl⟩⟩
  let IB : S.Arrow := IA.fromMiddle
  let IC : (T IB).Arrow := IA.toMiddle
  let ID : (T I).Arrow := ⟨IV.Y, IV.f ≫ II.f, Sieve.downward_closed (T I).1 II.hf IV.f⟩
  change t IB IC = t I ID
  apply inj IV.Y
  rw [toPlus_apply (T I) (t I) ID]
  erw [toPlus_apply (T IB) (t IB) IC]
  rw [← ht]; rw [← ht]
  -- Conclude by constructing the relation showing equality...
  let IR : S.Relation := { fst.hf := IB.hf, snd.hf := I.hf, r.w := IA.middle_spec, .. }
  exact s.condition IR

Depends on / 依赖: Function, Function.Injective, Injective, J.toPlus, inj_of_sep, toPlus
-/
theorem exists_of_sep (P : Cᵒᵖ ⥤ D)
    (hsep :
      forall (X : C) (S : J.Cover X) (x y : ToType (P.obj (op X))),
        (forall I : S.Arrow, P.map I.f.op x = P.map I.f.op y) -> x = y)
    (X : C) (S : J.Cover X) (s : Meq (J.plusObj P) S) :
    exists t : ToType ((J.plusObj P).obj (op X)), Meq.mk S t = s := by
  have inj : forall X : C, Function.Injective ((J.toPlus P).app (op X)) := inj_of_sep _ hsep
  -- Choose representatives for the given local sections.
  choose T t ht using fun I => exists_rep (s I)
  -- Construct a large cover over which we will define a representative that will
  -- provide the gluing of the given local sections.
  let B : J.Cover X := S.bind T
  choose Z e1 e2 he2 _ _ using fun I : B.Arrow => I.hf
  -- Construct a compatible system of local sections over this large cover, using the chosen
  -- representatives of our local sections.
  -- The compatibility here follows from the separatedness assumption.
  let w : Meq P B := meqOfSep P hsep X S s T t ht
  -- The associated gluing will be the candidate section.
  use mk w
  ext I
  dsimp [Meq.mk]
  rw [ht]; rw [res_mk_eq_mk_pullback]
  -- Use the separatedness of `P⁺` to prove that this is indeed a gluing of our
  -- original local sections.
  apply sep P (T I)
  intro II
  simp only [res_mk_eq_mk_pullback, eq_mk_iff_exists]
  -- It suffices to prove equality for representatives over a
  -- convenient sufficiently large cover...
  use (J.pullback II.f).obj (T I)
  let e0 : (J.pullback II.f).obj (T I) ⟶ (J.pullback II.f).obj ((J.pullback I.f).obj B) :=
    homOfLE
      (by
        intro Y f hf
        apply Sieve.le_pullback_bind _ _ _ I.hf
        · cases I
          exact hf)
  use e0, 𝟙 _
  ext IV
  let IA : B.Arrow := ⟨_, (IV.f ≫ II.f) ≫ I.f,
    ⟨I.Y, _, _, I.hf, Sieve.downward_closed _ II.hf _, rfl⟩⟩
  let IB : S.Arrow := IA.fromMiddle
  let IC : (T IB).Arrow := IA.toMiddle
  let ID : (T I).Arrow := ⟨IV.Y, IV.f ≫ II.f, Sieve.downward_closed (T I).1 II.hf IV.f⟩
  change t IB IC = t I ID
  apply inj IV.Y
  rw [toPlus_apply (T I) (t I) ID]
  erw [toPlus_apply (T IB) (t IB) IC]
  rw [← ht]; rw [← ht]
  -- Conclude by constructing the relation showing equality...
  let IR : S.Relation := { fst.hf := IB.hf, snd.hf := I.hf, r.w := IA.middle_spec, .. }
  exact s.condition IR

variable [(forget D).ReflectsIsomorphisms]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isSheaf_of_sep` / 定理 `isSheaf_of_sep`

English:
theorem isSheaf_of_sep
  statement: (P : Cᵒᵖ ⥤ D)
  proof: by
  rw [Presheaf.isSheaf_iff_multiequalizer]
  intro X S
  apply @isIso_of_reflects_iso _ _ _ _ _ _ _ (forget D) ?_
  rw [isIso_iff_bijective]
  constructor
  · intro x y h
    apply sep P S _ _
    intro I
    apply_fun Meq.equiv (J.plusObj P) S at h
    apply_fun fun e => e I at h
    dsimp only [ConcreteCategory.forget_map_eq_ofHom] at h
    simpa [Meq.equiv_apply, ← comp_apply] using! h
  · rintro (x : ToType (multiequalizer (S.index _)))
    obtain ⟨t, ht⟩ := exists_of_sep P hsep X S (Meq.equiv _ _ x)
    use t
    apply (Meq.equiv (D := D) _ _).injective
    rw [← ht]
    ext i
    dsimp
    rw [← ConcreteCategory.comp_apply]; rw [Multiequalizer.lift_ι]
    rfl

中文:
定理 isSheaf_of_sep
  结论: (P : Cᵒᵖ ⥤ D)
  证明: by
  rw [Presheaf.isSheaf_iff_multiequalizer]
  intro X S
  apply @isIso_of_reflects_iso _ _ _ _ _ _ _ (forget D) ?_
  rw [isIso_iff_bijective]
  constructor
  · intro x y h
    apply sep P S _ _
    intro I
    apply_fun Meq.equiv (J.plusObj P) S at h
    apply_fun fun e => e I at h
    dsimp only [ConcreteCategory.forget_map_eq_ofHom] at h
    simpa [Meq.equiv_apply, ← comp_apply] using! h
  · rintro (x : ToType (multiequalizer (S.index _)))
    obtain ⟨t, ht⟩ := exists_of_sep P hsep X S (Meq.equiv _ _ x)
    use t
    apply (Meq.equiv (D := D) _ _).injective
    rw [← ht]
    ext i
    dsimp
    rw [← ConcreteCategory.comp_apply]; rw [Multiequalizer.lift_ι]
    rfl

Depends on / 依赖: ConcreteCategory, ConcreteCategory.forget_map_eq_ofHom, J.plusObj, Meq.equiv, Meq.equiv_apply, Presheaf, Presheaf.isSheaf_iff_multiequalizer, S.index, ToType, apply_fun, comp_apply, equiv_apply, exists_of_sep, forget, forget_map_eq_ofHom, isIso_iff_bijective, isIso_of_reflects_iso, isSheaf_iff_multiequalizer, multiequalizer, plusObj
-/
theorem isSheaf_of_sep (P : Cᵒᵖ ⥤ D)
    (hsep :
      forall (X : C) (S : J.Cover X) (x y : ToType (P.obj (op X))),
        (forall I : S.Arrow, P.map I.f.op x = P.map I.f.op y) -> x = y) :
    Presheaf.IsSheaf J (J.plusObj P) := by
  rw [Presheaf.isSheaf_iff_multiequalizer]
  intro X S
  apply @isIso_of_reflects_iso _ _ _ _ _ _ _ (forget D) ?_
  rw [isIso_iff_bijective]
  constructor
  · intro x y h
    apply sep P S _ _
    intro I
    apply_fun Meq.equiv (J.plusObj P) S at h
    apply_fun fun e => e I at h
    dsimp only [ConcreteCategory.forget_map_eq_ofHom] at h
    simpa [Meq.equiv_apply, ← comp_apply] using! h
  · rintro (x : ToType (multiequalizer (S.index _)))
    obtain ⟨t, ht⟩ := exists_of_sep P hsep X S (Meq.equiv _ _ x)
    use t
    apply (Meq.equiv (D := D) _ _).injective
    rw [← ht]
    ext i
    dsimp
    rw [← ConcreteCategory.comp_apply]; rw [Multiequalizer.lift_ι]
    rfl

variable (J)

include instCC

/--
theorem `isSheaf_plus_plus` / 定理 `isSheaf_plus_plus`

English:
theorem isSheaf_plus_plus
  given: (P : Cᵒᵖ ⥤ D)
  statement: Presheaf.IsSheaf J (J.plusObj (J.plusObj P))
  proof: by
  apply isSheaf_of_sep
  intro X S x y
  apply sep

中文:
定理 isSheaf_plus_plus
  条件: (P : Cᵒᵖ ⥤ D)
  结论: 预层.是层 J (J.plusObj (J.plusObj P))
  证明: by
  apply isSheaf_of_sep
  intro X S x y
  apply sep

Depends on / 依赖: isSheaf_of_sep
-/
theorem isSheaf_plus_plus (P : Cᵒᵖ ⥤ D) : Presheaf.IsSheaf J (J.plusObj (J.plusObj P)) := by
  apply isSheaf_of_sep
  intro X S x y
  apply sep

end

end Plus

variable (J)
variable [forall (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]
  [forall X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]

/--
Definition of `sheafify` / `sheafify` 的定义

English:
definition sheafify
  signature: (P : Cᵒᵖ ⥤ D)
  body: J.plusObj (J.plusObj P)

中文:
定义 sheafify
  签名: (P : Cᵒᵖ ⥤ D)
  定义体: J.plusObj (J.plusObj P)

Depends on / 依赖: J.plusObj, plusObj
-/
noncomputable def sheafify (P : Cᵒᵖ ⥤ D) : Cᵒᵖ ⥤ D :=
  J.plusObj (J.plusObj P)

/--
Definition of `toSheafify` / `toSheafify` 的定义

English:
definition toSheafify
  signature: (P : Cᵒᵖ ⥤ D)
  body: J.toPlus P ≫ J.plusMap (J.toPlus P)

中文:
定义 toSheafify
  签名: (P : Cᵒᵖ ⥤ D)
  定义体: J.toPlus P ≫ J.plusMap (J.toPlus P)

Depends on / 依赖: J.plusMap, J.toPlus, plusMap, toPlus
-/
noncomputable def toSheafify (P : Cᵒᵖ ⥤ D) : P ⟶ J.sheafify P :=
  J.toPlus P ≫ J.plusMap (J.toPlus P)

/--
Definition of `sheafifyMap` / `sheafifyMap` 的定义

English:
definition sheafifyMap
  signature: {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q)
  body: J.plusMap J.plusMap η

@[simp]

中文:
定义 sheafifyMap
  签名: {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q)
  定义体: J.plusMap J.plusMap η

@[simp]

Depends on / 依赖: J.plusMap, plusMap
-/
noncomputable def sheafifyMap {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) : J.sheafify P ⟶ J.sheafify Q :=
J.plusMap J.plusMap η

@[simp]
/--
theorem `sheafifyMap_id` / 定理 `sheafifyMap_id`

English:
theorem sheafifyMap_id
  given: (P : Cᵒᵖ ⥤ D)
  statement: J.sheafifyMap (𝟙 P) = 𝟙 (J.sheafify P)
  proof: by
  dsimp [sheafifyMap, sheafify]
  simp

@[simp]

中文:
定理 sheafifyMap_id
  条件: (P : Cᵒᵖ ⥤ D)
  结论: J.sheafifyMap (𝟙 P) = 𝟙 (J.sheafify P)
  证明: by
  dsimp [sheafifyMap, sheafify]
  simp

@[simp]

Depends on / 依赖: sheafify, sheafifyMap
-/
theorem sheafifyMap_id (P : Cᵒᵖ ⥤ D) : J.sheafifyMap (𝟙 P) = 𝟙 (J.sheafify P) := by
  dsimp [sheafifyMap, sheafify]
  simp

@[simp]
/--
theorem `sheafifyMap_comp` / 定理 `sheafifyMap_comp`

English:
theorem sheafifyMap_comp
  given: {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R)
  proof: by
  dsimp [sheafifyMap, sheafify]
  simp

@[reassoc (attr := simp)]

中文:
定理 sheafifyMap_comp
  条件: {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R)
  证明: by
  dsimp [sheafifyMap, sheafify]
  simp

@[reassoc (attr := simp)]

Depends on / 依赖: sheafify, sheafifyMap
-/
theorem sheafifyMap_comp {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) :
    J.sheafifyMap (η ≫ γ) = J.sheafifyMap η ≫ J.sheafifyMap γ := by
  dsimp [sheafifyMap, sheafify]
  simp

@[reassoc (attr := simp)]
/--
theorem `toSheafify_naturality` / 定理 `toSheafify_naturality`

English:
theorem toSheafify_naturality
  given: {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q)
  proof: by
  dsimp [sheafifyMap, sheafify, toSheafify]
  simp

中文:
定理 toSheafify_naturality
  条件: {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q)
  证明: by
  dsimp [sheafifyMap, sheafify, toSheafify]
  simp

Depends on / 依赖: sheafify, sheafifyMap, toSheafify
-/
theorem toSheafify_naturality {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) :
    η ≫ J.toSheafify _ = J.toSheafify _ ≫ J.sheafifyMap η := by
  dsimp [sheafifyMap, sheafify, toSheafify]
  simp

variable (D)

/--
Definition of `sheafification` / `sheafification` 的定义

English:
definition sheafification
  signature: : (Cᵒᵖ ⥤ D) ⥤ Cᵒᵖ ⥤ D
  body: J.plusFunctor D ⋙ J.plusFunctor D

@[simp]

中文:
定义 sheafification
  签名: : (Cᵒᵖ ⥤ D) ⥤ Cᵒᵖ ⥤ D
  定义体: J.plusFunctor D ⋙ J.plusFunctor D

@[simp]

Depends on / 依赖: J.plusFunctor, plusFunctor
-/
noncomputable def sheafification : (Cᵒᵖ ⥤ D) ⥤ Cᵒᵖ ⥤ D :=
  J.plusFunctor D ⋙ J.plusFunctor D

@[simp]
/--
theorem `sheafification_obj` / 定理 `sheafification_obj`

English:
theorem sheafification_obj
  given: (P : Cᵒᵖ ⥤ D)
  statement: (J.sheafification D).obj P = J.sheafify P
  proof: rfl

@[simp]

中文:
定理 sheafification_obj
  条件: (P : Cᵒᵖ ⥤ D)
  结论: (J.sheafification D).obj P = J.sheafify P
  证明: rfl

@[simp]
-/
theorem sheafification_obj (P : Cᵒᵖ ⥤ D) : (J.sheafification D).obj P = J.sheafify P :=
  rfl

@[simp]
/--
theorem `sheafification_map` / 定理 `sheafification_map`

English:
theorem sheafification_map
  given: {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q)
  proof: rfl

中文:
定理 sheafification_map
  条件: {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q)
  证明: rfl
-/
theorem sheafification_map {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) :
    (J.sheafification D).map η = J.sheafifyMap η :=
  rfl

/--
Definition of `toSheafification` / `toSheafification` 的定义

English:
definition toSheafification
  signature: : 𝟭 _ ⟶ sheafification J D
  body: J.toPlusNatTrans D ≫ Functor.whiskerRight (J.toPlusNatTrans D) (J.plusFunctor D)

@[simp]

中文:
定义 toSheafification
  签名: : 𝟭 _ ⟶ sheafification J D
  定义体: J.toPlusNatTrans D ≫ Functor.whiskerRight (J.toPlusNatTrans D) (J.plusFunctor D)

@[simp]

Depends on / 依赖: Functor, Functor.whiskerRight, J.plusFunctor, J.toPlusNatTrans, encard_eq_eRank, hI.isBase_restrict.encard_eq_eRank, isBase_restrict, plusFunctor, toPlusNatTrans, whiskerRight
-/
noncomputable def toSheafification : 𝟭 _ ⟶ sheafification J D :=
  J.toPlusNatTrans D ≫ Functor.whiskerRight (J.toPlusNatTrans D) (J.plusFunctor D)

@[simp]
/--
theorem `toSheafification_app` / 定理 `toSheafification_app`

English:
theorem toSheafification_app
  given: (P : Cᵒᵖ ⥤ D)
  proof: rfl

中文:
定理 toSheafification_app
  条件: (P : Cᵒᵖ ⥤ D)
  证明: rfl
-/
theorem toSheafification_app (P : Cᵒᵖ ⥤ D) :
    (J.toSheafification D).app P = J.toSheafify P :=
  rfl

variable {D}

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isIso_toSheafify` / 定理 `isIso_toSheafify`

English:
theorem isIso_toSheafify
  given: {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P)
  statement: IsIso (J.toSheafify P)
  proof: by
  dsimp [toSheafify]
  have := isIso_toPlus_of_isSheaf J P hP
  change (IsIso (toPlus J P ≫ (J.plusFunctor D).map (toPlus J P)))
  infer_instance

中文:
定理 isIso_toSheafify
  条件: {P : Cᵒᵖ ⥤ D} (hP : 预层.是层 J P)
  结论: 是同构 (J.toSheafify P)
  证明: by
  dsimp [toSheafify]
  have := isIso_toPlus_of_isSheaf J P hP
  change (IsIso (toPlus J P ≫ (J.plusFunctor D).map (toPlus J P)))
  infer_instance

Depends on / 依赖: J.plusFunctor, infer_instance, isIso_toPlus_of_isSheaf, plusFunctor, toPlus, toSheafify
-/
theorem isIso_toSheafify {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) : IsIso (J.toSheafify P) := by
  dsimp [toSheafify]
  have := isIso_toPlus_of_isSheaf J P hP
  change (IsIso (toPlus J P ≫ (J.plusFunctor D).map (toPlus J P)))
  infer_instance

/--
Definition of `isoSheafify` / `isoSheafify` 的定义

English:
definition isoSheafify
  signature: {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P)
  body: letI := isIso_toSheafify J hP
  asIso (J.toSheafify P)

@[simp]

中文:
定义 isoSheafify
  签名: {P : Cᵒᵖ ⥤ D} (hP : 预层.是层 J P)
  定义体: letI := isIso_toSheafify J hP
  asIso (J.toSheafify P)

@[simp]

Depends on / 依赖: J.toSheafify, isIso_toSheafify, toSheafify
-/
noncomputable def isoSheafify {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) : P ≅ J.sheafify P :=
  letI := isIso_toSheafify J hP
  asIso (J.toSheafify P)

@[simp]
/--
theorem `isoSheafify_hom` / 定理 `isoSheafify_hom`

English:
theorem isoSheafify_hom
  given: {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P)
  proof: rfl

中文:
定理 isoSheafify_hom
  条件: {P : Cᵒᵖ ⥤ D} (hP : 预层.是层 J P)
  证明: rfl

Depends on / 依赖: eRk_eq_encard, encard_eq_eRk, hIX.encard_eq_eRk, hIX.indep.eRk_eq_encard
-/
theorem isoSheafify_hom {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) :
    (J.isoSheafify hP).hom = J.toSheafify P :=
  rfl

/--
Definition of `sheafifyLift` / `sheafifyLift` 的定义

English:
definition sheafifyLift
  signature: {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
  body: J.plusLift (J.plusLift η hQ) hQ

中文:
定义 sheafifyLift
  签名: {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : 预层.是层 J Q)
  定义体: J.plusLift (J.plusLift η hQ) hQ

Depends on / 依赖: J.plusLift, plusLift
-/
noncomputable def sheafifyLift {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) :
    J.sheafify P ⟶ Q :=
  J.plusLift (J.plusLift η hQ) hQ

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `toSheafify_sheafifyLift` / 定理 `toSheafify_sheafifyLift`

English:
theorem toSheafify_sheafifyLift
  given: {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
  proof: by
  dsimp only [sheafifyLift, toSheafify]
  simp

中文:
定理 toSheafify_sheafifyLift
  条件: {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : 预层.是层 J Q)
  证明: by
  dsimp only [sheafifyLift, toSheafify]
  simp

Depends on / 依赖: eRk_eq_eRk, eRk_eq_encard, hIX.eRk_eq_eRk, hIX.indep.eRk_eq_encard, sheafifyLift, toSheafify
-/
theorem toSheafify_sheafifyLift {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) :
    J.toSheafify P ≫ sheafifyLift J η hQ = η := by
  dsimp only [sheafifyLift, toSheafify]
  simp

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `sheafifyLift_unique` / 定理 `sheafifyLift_unique`

English:
theorem sheafifyLift_unique
  statement: {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
  proof: by
  intro h
  apply plusLift_unique
  apply plusLift_unique
  rw [← Category.assoc]; rw [← plusMap_toPlus]
  exact h

@[simp]

中文:
定理 sheafifyLift_unique
  结论: {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : 预层.是层 J Q)
  证明: by
  intro h
  apply plusLift_unique
  apply plusLift_unique
  rw [← Category.assoc]; rw [← plusMap_toPlus]
  exact h

@[simp]

Depends on / 依赖: Category, Category.assoc, plusLift_unique, plusMap_toPlus
-/
theorem sheafifyLift_unique {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
    (γ : J.sheafify P ⟶ Q) : J.toSheafify P ≫ γ = η -> γ = sheafifyLift J η hQ := by
  intro h
  apply plusLift_unique
  apply plusLift_unique
  rw [← Category.assoc]; rw [← plusMap_toPlus]
  exact h

@[simp]
/--
theorem `isoSheafify_inv` / 定理 `isoSheafify_inv`

English:
theorem isoSheafify_inv
  given: {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P)
  proof: by
  apply J.sheafifyLift_unique
  simp [Iso.comp_inv_eq]

中文:
定理 isoSheafify_inv
  条件: {P : Cᵒᵖ ⥤ D} (hP : 预层.是层 J P)
  证明: by
  apply J.sheafifyLift_unique
  simp [Iso.comp_inv_eq]

Depends on / 依赖: Iso.comp_inv_eq, J.sheafifyLift_unique, comp_inv_eq, sheafifyLift_unique
-/
theorem isoSheafify_inv {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) :
    (J.isoSheafify hP).inv = J.sheafifyLift (𝟙 _) hP := by
  apply J.sheafifyLift_unique
  simp [Iso.comp_inv_eq]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `sheafify_hom_ext` / 定理 `sheafify_hom_ext`

English:
theorem sheafify_hom_ext
  statement: {P Q : Cᵒᵖ ⥤ D} (η γ : J.sheafify P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
  proof: by
  apply J.plus_hom_ext _ _ hQ
  apply J.plus_hom_ext _ _ hQ
  rw [← Category.assoc]; rw [← Category.assoc]; rw [← plusMap_toPlus]
  exact h

@[reassoc (attr := simp)]

中文:
定理 sheafify_hom_ext
  结论: {P Q : Cᵒᵖ ⥤ D} (η γ : J.sheafify P ⟶ Q) (hQ : 预层.是层 J Q)
  证明: by
  apply J.plus_hom_ext _ _ hQ
  apply J.plus_hom_ext _ _ hQ
  rw [← Category.assoc]; rw [← Category.assoc]; rw [← plusMap_toPlus]
  exact h

@[reassoc (attr := simp)]

Depends on / 依赖: Category, Category.assoc, J.plus_hom_ext, plusMap_toPlus, plus_hom_ext
-/
theorem sheafify_hom_ext {P Q : Cᵒᵖ ⥤ D} (η γ : J.sheafify P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
    (h : J.toSheafify P ≫ η = J.toSheafify P ≫ γ) : η = γ := by
  apply J.plus_hom_ext _ _ hQ
  apply J.plus_hom_ext _ _ hQ
  rw [← Category.assoc]; rw [← Category.assoc]; rw [← plusMap_toPlus]
  exact h

@[reassoc (attr := simp)]
/--
theorem `sheafifyMap_sheafifyLift` / 定理 `sheafifyMap_sheafifyLift`

English:
theorem sheafifyMap_sheafifyLift
  statement: {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R)
  proof: by
  apply J.sheafifyLift_unique
  rw [← Category.assoc]; rw [← J.toSheafify_naturality]; rw [Category.assoc]; rw [toSheafify_sheafifyLift]

中文:
定理 sheafifyMap_sheafifyLift
  结论: {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R)
  证明: by
  apply J.sheafifyLift_unique
  rw [← Category.assoc]; rw [← J.toSheafify_naturality]; rw [Category.assoc]; rw [toSheafify_sheafifyLift]

Depends on / 依赖: Category, Category.assoc, J.sheafifyLift_unique, J.toSheafify_naturality, sheafifyLift_unique, toSheafify_naturality, toSheafify_sheafifyLift
-/
theorem sheafifyMap_sheafifyLift {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R)
    (hR : Presheaf.IsSheaf J R) :
    J.sheafifyMap η ≫ J.sheafifyLift γ hR = J.sheafifyLift (η ≫ γ) hR := by
  apply J.sheafifyLift_unique
  rw [← Category.assoc]; rw [← J.toSheafify_naturality]; rw [Category.assoc]; rw [toSheafify_sheafifyLift]

end GrothendieckTopology

variable (J)
variable {FD : D -> D -> Type*} {CD : D -> Type t} [forall X Y, FunLike (FD X Y) (CD X) (CD Y)]
variable [instCC : ConcreteCategory.{t} D FD]
  [forall {X : C} (S : J.Cover X), PreservesLimitsOfShape (WalkingMulticospan S.shape) (forget D)]
  [forall (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]
  [forall X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]
  [forall X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget D)] [(forget D).ReflectsIsomorphisms]

include instCC in
/--
theorem `GrothendieckTopology.sheafify_isSheaf` / 定理 `GrothendieckTopology.sheafify_isSheaf`

English:
theorem GrothendieckTopology.sheafify_isSheaf
  given: (P : Cᵒᵖ ⥤ D)
  statement: Presheaf.IsSheaf J (J.sheafify P)
  proof: GrothendieckTopology.Plus.isSheaf_plus_plus _ _

中文:
定理 Grothendieck拓扑.sheafify_isSheaf
  条件: (P : Cᵒᵖ ⥤ D)
  结论: 预层.是层 J (J.sheafify P)
  证明: GrothendieckTopology.Plus.isSheaf_plus_plus _ _

Depends on / 依赖: GrothendieckTopology, GrothendieckTopology.Plus.isSheaf_plus_plus, isSheaf_plus_plus
-/
theorem GrothendieckTopology.sheafify_isSheaf (P : Cᵒᵖ ⥤ D) : Presheaf.IsSheaf J (J.sheafify P) :=
  GrothendieckTopology.Plus.isSheaf_plus_plus _ _

variable (D)

/-- The sheafification functor, as a functor taking values in `Sheaf`. -/
@[simps]
/--
Definition of `plusPlusSheaf` / `plusPlusSheaf` 的定义

English:
definition plusPlusSheaf
  signature: : (Cᵒᵖ ⥤ D) ⥤ Sheaf J D where
  body: ⟨J.sheafify P, J.sheafify_isSheaf P⟩
  map η := ⟨J.sheafifyMap η⟩

中文:
定义 plusPlusSheaf
  签名: : (Cᵒᵖ ⥤ D) ⥤ 层 J D where
  定义体: ⟨J.sheafify P, J.sheafify_isSheaf P⟩
  map η := ⟨J.sheafifyMap η⟩

Depends on / 依赖: J.sheafify, J.sheafify_isSheaf, sheafify, sheafify_isSheaf
-/
noncomputable def plusPlusSheaf : (Cᵒᵖ ⥤ D) ⥤ Sheaf J D where
  obj P := ⟨J.sheafify P, J.sheafify_isSheaf P⟩
  map η := ⟨J.sheafifyMap η⟩

set_option backward.isDefEq.respectTransparency false in
/--
Instance `plusPlusSheaf_preservesZeroMorphisms` / 实例 `plusPlusSheaf_preservesZeroMorphisms`

English:
instance plusPlusSheaf_preservesZeroMorphisms
  signature: [Preadditive D]
  body: by
    ext : 3
    refine colimit.hom_ext (fun j => ?_)
    erw [colimit.ι_map, comp_zero]
    simp

中文:
实例 plusPlusSheaf_preservesZeroMorphisms
  签名: [预加性 D]
  定义体: by
    ext : 3
    refine colimit.hom_ext (fun j => ?_)
    erw [colimit.ι_map, comp_zero]
    simp

Depends on / 依赖: colimit, colimit.hom_ext, comp_zero, hom_ext
-/
instance plusPlusSheaf_preservesZeroMorphisms [Preadditive D] :
    (plusPlusSheaf J D).PreservesZeroMorphisms where
  map_zero F G := by
    ext : 3
    refine colimit.hom_ext (fun j => ?_)
    erw [colimit.ι_map, comp_zero]
    simp

set_option backward.isDefEq.respectTransparency false in
--@[simps! unit_app counit_app_val]
/--
Definition of `plusPlusAdjunction` / `plusPlusAdjunction` 的定义

English:
definition plusPlusAdjunction
  signature: : plusPlusSheaf J D ⊣ sheafToPresheaf J D
  body: Adjunction.mkOfHomEquiv
    { homEquiv := fun P Q =>
        { toFun := fun e => J.toSheafify P ≫ e.hom
          invFun := fun e => ⟨J.sheafifyLift e Q.2⟩
left_inv := fun _ => Sheaf.hom_ext (J.sheafifyLift_unique _ _ _ rfl).symm
          right_inv := fun _ => J.toSheafify_sheafifyLift _ _ }
      homEquiv_naturality_left_symm := by
        intro P Q R η γ; ext1; dsimp; symm
        apply J.sheafifyMap_sheafifyLift
      homEquiv_naturality_right := fun η γ => by
        dsimp
        rw [Category.assoc] }

中文:
定义 plusPlusAdjunction
  签名: : plusPlusSheaf J D ⊣ sheafToPresheaf J D
  定义体: Adjunction.mkOfHomEquiv
    { homEquiv := fun P Q =>
        { toFun := fun e => J.toSheafify P ≫ e.hom
          invFun := fun e => ⟨J.sheafifyLift e Q.2⟩
left_inv := fun _ => Sheaf.hom_ext (J.sheafifyLift_unique _ _ _ rfl).symm
          right_inv := fun _ => J.toSheafify_sheafifyLift _ _ }
      homEquiv_naturality_left_symm := by
        intro P Q R η γ; ext1; dsimp; symm
        apply J.sheafifyMap_sheafifyLift
      homEquiv_naturality_right := fun η γ => by
        dsimp
        rw [Category.assoc] }

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, Category, Category.assoc, J.sheafifyLift, J.sheafifyLift_unique, J.sheafifyMap_sheafifyLift, J.toSheafify, J.toSheafify_sheafifyLift, Sheaf.hom_ext, e.hom, homEquiv, homEquiv_naturality_left_symm, homEquiv_naturality_right, hom_ext, invFun, left_inv, mkOfHomEquiv, right_inv, sheafifyLift
-/
noncomputable def plusPlusAdjunction : plusPlusSheaf J D ⊣ sheafToPresheaf J D :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun P Q =>
        { toFun := fun e => J.toSheafify P ≫ e.hom
          invFun := fun e => ⟨J.sheafifyLift e Q.2⟩
left_inv := fun _ => Sheaf.hom_ext (J.sheafifyLift_unique _ _ _ rfl).symm
          right_inv := fun _ => J.toSheafify_sheafifyLift _ _ }
      homEquiv_naturality_left_symm := by
        intro P Q R η γ; ext1; dsimp; symm
        apply J.sheafifyMap_sheafifyLift
      homEquiv_naturality_right := fun η γ => by
        dsimp
        rw [Category.assoc] }

/--
Instance `sheafToPresheaf_isRightAdjoint` / 实例 `sheafToPresheaf_isRightAdjoint`

English:
instance sheafToPresheaf_isRightAdjoint
  signature: : (sheafToPresheaf J D).IsRightAdjoint
  body: (plusPlusAdjunction J D).isRightAdjoint

中文:
实例 sheafToPresheaf_isRightAdjoint
  签名: : (sheafToPresheaf J D).是右伴随
  定义体: (plusPlusAdjunction J D).isRightAdjoint

Depends on / 依赖: isRightAdjoint, plusPlusAdjunction
-/
instance sheafToPresheaf_isRightAdjoint : (sheafToPresheaf J D).IsRightAdjoint :=
  (plusPlusAdjunction J D).isRightAdjoint

/--
Instance `presheaf_mono_of_mono` / 实例 `presheaf_mono_of_mono`

English:
instance presheaf_mono_of_mono
  signature: {F G : Sheaf J D} (f : F ⟶ G) [Mono f]
  body: (sheafToPresheaf J D).map_mono _

include instCC in

中文:
实例 presheaf_mono_of_mono
  签名: {F G : 层 J D} (f : F ⟶ G) [单态射 f]
  定义体: (sheafToPresheaf J D).map_mono _

include instCC in

Depends on / 依赖: map_mono, sheafToPresheaf
-/
instance presheaf_mono_of_mono {F G : Sheaf J D} (f : F ⟶ G) [Mono f] : Mono f.1 :=
  (sheafToPresheaf J D).map_mono _

include instCC in
/--
theorem `Sheaf.Hom.mono_iff_presheaf_mono` / 定理 `Sheaf.Hom.mono_iff_presheaf_mono`

English:
theorem Sheaf.Hom.mono_iff_presheaf_mono
  given: {F G : Sheaf J D} (f : F ⟶ G)
  statement: Mono f ↔ Mono f.1
  proof: ⟨fun m => by infer_instance, fun m => by exact Sheaf.Hom.mono_of_presheaf_mono J D f⟩

中文:
定理 层.态射.mono_iff_presheaf_mono
  条件: {F G : 层 J D} (f : F ⟶ G)
  结论: 单态射 f ↔ 单态射 f.1
  证明: ⟨fun m => by infer_instance, fun m => by exact Sheaf.Hom.mono_of_presheaf_mono J D f⟩

Depends on / 依赖: Sheaf.Hom.mono_of_presheaf_mono, infer_instance, mono_of_presheaf_mono
-/
theorem Sheaf.Hom.mono_iff_presheaf_mono {F G : Sheaf J D} (f : F ⟶ G) : Mono f ↔ Mono f.1 :=
  ⟨fun m => by infer_instance, fun m => by exact Sheaf.Hom.mono_of_presheaf_mono J D f⟩

end CategoryTheory
