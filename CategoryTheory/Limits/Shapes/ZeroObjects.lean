/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johan Commelin
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Zero objects

A category "has a zero object" if it has an object which is both initial and terminal. Having a
zero object provides zero morphisms, as the unique morphisms factoring through the zero object;
see `CategoryTheory.Limits.Shapes.ZeroMorphisms`.

## References

* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]
-/

@[expose] public section


noncomputable section

universe v u v' u'

open CategoryTheory

open CategoryTheory.Category

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D]

namespace CategoryTheory

namespace Limits

/--
Definition of `IsZero` / `IsZero` 的定义

English:
structure IsZero
  parameters: (X : C)
  axioms and operations (2):
    - unique_to : forall Y, Nonempty (Unique (X ⟶ Y))
    - unique_from : forall Y, Nonempty (Unique (Y ⟶ X))

中文:
结构 是零
  参数: (X : C)
  公理与运算 (2 个):
    - unique_to : 对任意 Y, 非空 (唯一 (X ⟶ Y))
    - unique_from : 对任意 Y, 非空 (唯一 (Y ⟶ X))
-/
structure IsZero (X : C) : Prop where
  /-- there are unique morphisms to the object -/
  unique_to : forall Y, Nonempty (Unique (X ⟶ Y))
  /-- there are unique morphisms from the object -/
  unique_from : forall Y, Nonempty (Unique (Y ⟶ X))

namespace IsZero

variable {X Y : C}

/--
Definition of `to_` / `to_` 的定义

English:
definition to_
  signature: (h : IsZero X) (Y : C)
  body: @default _ (h.unique_to Y).some.toInhabited

中文:
定义 to_
  签名: (h : 是零 X) (Y : C)
  定义体: @default _ (h.unique_to Y).some.toInhabited
-/
protected def to_ (h : IsZero X) (Y : C) : X ⟶ Y :=
@default _ (h.unique_to Y).some.toInhabited

/--
theorem `eq_to` / 定理 `eq_to`

English:
theorem eq_to
  given: (h : IsZero X) (f : X ⟶ Y)
  statement: f = h.to_ Y
  proof: @Unique.eq_default _ (id _) _

中文:
定理 eq_to
  条件: (h : 是零 X) (f : X ⟶ Y)
  结论: f = h.to_ Y
  证明: @Unique.eq_default _ (id _) _

Depends on / 依赖: Unique, Unique.eq_default, eq_default
-/
theorem eq_to (h : IsZero X) (f : X ⟶ Y) : f = h.to_ Y :=
  @Unique.eq_default _ (id _) _

/--
theorem `to_eq` / 定理 `to_eq`

English:
theorem to_eq
  given: (h : IsZero X) (f : X ⟶ Y)
  statement: h.to_ Y = f
  proof: (h.eq_to f).symm

中文:
定理 to_eq
  条件: (h : 是零 X) (f : X ⟶ Y)
  结论: h.to_ Y = f
  证明: (h.eq_to f).symm

Depends on / 依赖: eq_to, h.eq_to
-/
theorem to_eq (h : IsZero X) (f : X ⟶ Y) : h.to_ Y = f :=
  (h.eq_to f).symm

/--
Definition of `from_` / `from_` 的定义

English:
definition from_
  signature: (h : IsZero X) (Y : C)
  body: @default _ (h.unique_from Y).some.toInhabited

中文:
定义 from_
  签名: (h : 是零 X) (Y : C)
  定义体: @default _ (h.unique_from Y).some.toInhabited
-/
protected def from_ (h : IsZero X) (Y : C) : Y ⟶ X :=
@default _ (h.unique_from Y).some.toInhabited

/--
theorem `eq_from` / 定理 `eq_from`

English:
theorem eq_from
  given: (h : IsZero X) (f : Y ⟶ X)
  statement: f = h.from_ Y
  proof: @Unique.eq_default _ (id _) _

中文:
定理 eq_from
  条件: (h : 是零 X) (f : Y ⟶ X)
  结论: f = h.from_ Y
  证明: @Unique.eq_default _ (id _) _

Depends on / 依赖: Unique, Unique.eq_default, eq_default
-/
theorem eq_from (h : IsZero X) (f : Y ⟶ X) : f = h.from_ Y :=
  @Unique.eq_default _ (id _) _

/--
theorem `from_eq` / 定理 `from_eq`

English:
theorem from_eq
  given: (h : IsZero X) (f : Y ⟶ X)
  statement: h.from_ Y = f
  proof: (h.eq_from f).symm

中文:
定理 from_eq
  条件: (h : 是零 X) (f : Y ⟶ X)
  结论: h.from_ Y = f
  证明: (h.eq_from f).symm

Depends on / 依赖: eq_from, h.eq_from
-/
theorem from_eq (h : IsZero X) (f : Y ⟶ X) : h.from_ Y = f :=
  (h.eq_from f).symm

/--
theorem `eq_of_src` / 定理 `eq_of_src`

English:
theorem eq_of_src
  given: (hX : IsZero X) (f g : X ⟶ Y)
  statement: f = g
  proof: (hX.eq_to f).trans (hX.eq_to g).symm

中文:
定理 eq_of_src
  条件: (hX : 是零 X) (f g : X ⟶ Y)
  结论: f = g
  证明: (hX.eq_to f).trans (hX.eq_to g).symm

Depends on / 依赖: eq_to, hX.eq_to
-/
theorem eq_of_src (hX : IsZero X) (f g : X ⟶ Y) : f = g :=
  (hX.eq_to f).trans (hX.eq_to g).symm

/--
theorem `eq_of_tgt` / 定理 `eq_of_tgt`

English:
theorem eq_of_tgt
  given: (hX : IsZero X) (f g : Y ⟶ X)
  statement: f = g
  proof: (hX.eq_from f).trans (hX.eq_from g).symm

中文:
定理 eq_of_tgt
  条件: (hX : 是零 X) (f g : Y ⟶ X)
  结论: f = g
  证明: (hX.eq_from f).trans (hX.eq_from g).symm

Depends on / 依赖: eq_from, hX.eq_from
-/
theorem eq_of_tgt (hX : IsZero X) (f g : Y ⟶ X) : f = g :=
  (hX.eq_from f).trans (hX.eq_from g).symm

/--
lemma `epi` / 引理 `epi`

English:
lemma epi
  given: (h : IsZero X) {Y : C} (f : Y ⟶ X)
  statement: Epi f where
  proof: h.eq_of_src _ _

中文:
引理 epi
  条件: (h : 是零 X) {Y : C} (f : Y ⟶ X)
  结论: 满态射 f where
  证明: h.eq_of_src _ _

Depends on / 依赖: eq_of_src, h.eq_of_src
-/
lemma epi (h : IsZero X) {Y : C} (f : Y ⟶ X) : Epi f where
  left_cancellation _ _ _ := h.eq_of_src _ _

/--
lemma `mono` / 引理 `mono`

English:
lemma mono
  given: (h : IsZero X) {Y : C} (f : X ⟶ Y)
  statement: Mono f where
  proof: h.eq_of_tgt _ _

中文:
引理 mono
  条件: (h : 是零 X) {Y : C} (f : X ⟶ Y)
  结论: 单态射 f where
  证明: h.eq_of_tgt _ _

Depends on / 依赖: eq_of_tgt, h.eq_of_tgt
-/
lemma mono (h : IsZero X) {Y : C} (f : X ⟶ Y) : Mono f where
  right_cancellation _ _ _ := h.eq_of_tgt _ _

/--
Definition of `iso` / `iso` 的定义

English:
definition iso
  signature: (hX : IsZero X) (hY : IsZero Y)
  body: hX.to_ Y
  inv := hX.from_ Y
  hom_inv_id := hX.eq_of_src _ _
  inv_hom_id := hY.eq_of_src _ _

中文:
定义 iso
  签名: (hX : 是零 X) (hY : 是零 Y)
  定义体: hX.to_ Y
  inv := hX.from_ Y
  hom_inv_id := hX.eq_of_src _ _
  inv_hom_id := hY.eq_of_src _ _

Depends on / 依赖: hX.to_
-/
def iso (hX : IsZero X) (hY : IsZero Y) : X ≅ Y where
  hom := hX.to_ Y
  inv := hX.from_ Y
  hom_inv_id := hX.eq_of_src _ _
  inv_hom_id := hY.eq_of_src _ _

/--
lemma `isIso` / 引理 `isIso`

English:
lemma isIso
  given: (hX : IsZero X) (hY : IsZero Y) (f : X ⟶ Y)
  statement: IsIso f
  proof: ⟨hY.to_ _, hX.eq_of_src _ _, hY.eq_of_src _ _⟩

中文:
引理 isIso
  条件: (hX : 是零 X) (hY : 是零 Y) (f : X ⟶ Y)
  结论: 是同构 f
  证明: ⟨hY.to_ _, hX.eq_of_src _ _, hY.eq_of_src _ _⟩

Depends on / 依赖: eq_of_src, hX.eq_of_src, hY.eq_of_src, hY.to_
-/
lemma isIso (hX : IsZero X) (hY : IsZero Y) (f : X ⟶ Y) : IsIso f :=
  ⟨hY.to_ _, hX.eq_of_src _ _, hY.eq_of_src _ _⟩

/--
Definition of `isInitial` / `isInitial` 的定义

English:
definition isInitial
  signature: (hX : IsZero X)
  body: @IsInitial.ofUnique _ _ X fun Y => (hX.unique_to Y).some

中文:
定义 isInitial
  签名: (hX : 是零 X)
  定义体: @IsInitial.ofUnique _ _ X fun Y => (hX.unique_to Y).some
-/
protected def isInitial (hX : IsZero X) : IsInitial X :=
  @IsInitial.ofUnique _ _ X fun Y => (hX.unique_to Y).some

/--
Definition of `isTerminal` / `isTerminal` 的定义

English:
definition isTerminal
  signature: (hX : IsZero X)
  body: @IsTerminal.ofUnique _ _ X fun Y => (hX.unique_from Y).some

中文:
定义 isTerminal
  签名: (hX : 是零 X)
  定义体: @IsTerminal.ofUnique _ _ X fun Y => (hX.unique_from Y).some
-/
protected def isTerminal (hX : IsZero X) : IsTerminal X :=
  @IsTerminal.ofUnique _ _ X fun Y => (hX.unique_from Y).some

/--
Definition of `isoIsInitial` / `isoIsInitial` 的定义

English:
definition isoIsInitial
  signature: (hX : IsZero X) (hY : IsInitial Y)
  body: IsInitial.uniqueUpToIso hX.isInitial hY

中文:
定义 isoIsInitial
  签名: (hX : 是零 X) (hY : IsInitial Y)
  定义体: IsInitial.uniqueUpToIso hX.isInitial hY

Depends on / 依赖: IsInitial, IsInitial.uniqueUpToIso, hX.isInitial, isInitial, uniqueUpToIso
-/
def isoIsInitial (hX : IsZero X) (hY : IsInitial Y) : X ≅ Y :=
  IsInitial.uniqueUpToIso hX.isInitial hY

/--
Definition of `isoIsTerminal` / `isoIsTerminal` 的定义

English:
definition isoIsTerminal
  signature: (hX : IsZero X) (hY : IsTerminal Y)
  body: IsTerminal.uniqueUpToIso hX.isTerminal hY

中文:
定义 isoIsTerminal
  签名: (hX : 是零 X) (hY : 是终止 Y)
  定义体: IsTerminal.uniqueUpToIso hX.isTerminal hY

Depends on / 依赖: IsTerminal, IsTerminal.uniqueUpToIso, hX.isTerminal, isTerminal, uniqueUpToIso
-/
def isoIsTerminal (hX : IsZero X) (hY : IsTerminal Y) : X ≅ Y :=
  IsTerminal.uniqueUpToIso hX.isTerminal hY

/--
theorem `of_iso` / 定理 `of_iso`

English:
theorem of_iso
  given: (hY : IsZero Y) (e : X ≅ Y)
  statement: IsZero X
  proof: by
  refine ⟨fun Z => ⟨⟨⟨e.hom ≫ hY.to_ Z⟩, fun f => ?_⟩⟩,
    fun Z => ⟨⟨⟨hY.from_ Z ≫ e.inv⟩, fun f => ?_⟩⟩⟩
  · rw [← cancel_epi e.inv]
    apply hY.eq_of_src
  · rw [← cancel_mono e.hom]
    apply hY.eq_of_tgt

中文:
定理 of_iso
  条件: (hY : 是零 Y) (e : X ≅ Y)
  结论: 是零 X
  证明: by
  refine ⟨fun Z => ⟨⟨⟨e.hom ≫ hY.to_ Z⟩, fun f => ?_⟩⟩,
    fun Z => ⟨⟨⟨hY.from_ Z ≫ e.inv⟩, fun f => ?_⟩⟩⟩
  · rw [← cancel_epi e.inv]
    apply hY.eq_of_src
  · rw [← cancel_mono e.hom]
    apply hY.eq_of_tgt

Depends on / 依赖: cancel_epi, cancel_mono, e.hom, e.inv, eq_of_src, eq_of_tgt, from_, hY.eq_of_src, hY.eq_of_tgt, hY.from_, hY.to_
-/
theorem of_iso (hY : IsZero Y) (e : X ≅ Y) : IsZero X := by
  refine ⟨fun Z => ⟨⟨⟨e.hom ≫ hY.to_ Z⟩, fun f => ?_⟩⟩,
    fun Z => ⟨⟨⟨hY.from_ Z ≫ e.inv⟩, fun f => ?_⟩⟩⟩
  · rw [← cancel_epi e.inv]
    apply hY.eq_of_src
  · rw [← cancel_mono e.hom]
    apply hY.eq_of_tgt

/--
theorem `op` / 定理 `op`

English:
theorem op
  given: (h : IsZero X)
  statement: IsZero (Opposite.op X)
  proof: ⟨fun Y => ⟨⟨⟨(h.from_ (Opposite.unop Y)).op⟩, fun _ => Quiver.Hom.unop_inj (h.eq_of_tgt _ _)⟩⟩,
    fun Y => ⟨⟨⟨(h.to_ (Opposite.unop Y)).op⟩, fun _ => Quiver.Hom.unop_inj (h.eq_of_src _ _)⟩⟩⟩

中文:
定理 op
  条件: (h : 是零 X)
  结论: 是零 (对偶.op X)
  证明: ⟨fun Y => ⟨⟨⟨(h.from_ (Opposite.unop Y)).op⟩, fun _ => Quiver.Hom.unop_inj (h.eq_of_tgt _ _)⟩⟩,
    fun Y => ⟨⟨⟨(h.to_ (Opposite.unop Y)).op⟩, fun _ => Quiver.Hom.unop_inj (h.eq_of_src _ _)⟩⟩⟩

Depends on / 依赖: Opposite, Opposite.unop, Quiver, Quiver.Hom.unop_inj, eq_of_src, eq_of_tgt, from_, h.eq_of_src, h.eq_of_tgt, h.from_, h.to_, unop_inj
-/
theorem op (h : IsZero X) : IsZero (Opposite.op X) :=
  ⟨fun Y => ⟨⟨⟨(h.from_ (Opposite.unop Y)).op⟩, fun _ => Quiver.Hom.unop_inj (h.eq_of_tgt _ _)⟩⟩,
    fun Y => ⟨⟨⟨(h.to_ (Opposite.unop Y)).op⟩, fun _ => Quiver.Hom.unop_inj (h.eq_of_src _ _)⟩⟩⟩

/--
theorem `unop` / 定理 `unop`

English:
theorem unop
  given: {X : Cᵒᵖ} (h : IsZero X)
  statement: IsZero (Opposite.unop X)
  proof: ⟨fun Y => ⟨⟨⟨(h.from_ (Opposite.op Y)).unop⟩, fun _ => Quiver.Hom.op_inj (h.eq_of_tgt _ _)⟩⟩,
    fun Y => ⟨⟨⟨(h.to_ (Opposite.op Y)).unop⟩, fun _ => Quiver.Hom.op_inj (h.eq_of_src _ _)⟩⟩⟩

中文:
定理 unop
  条件: {X : Cᵒᵖ} (h : 是零 X)
  结论: 是零 (对偶.unop X)
  证明: ⟨fun Y => ⟨⟨⟨(h.from_ (Opposite.op Y)).unop⟩, fun _ => Quiver.Hom.op_inj (h.eq_of_tgt _ _)⟩⟩,
    fun Y => ⟨⟨⟨(h.to_ (Opposite.op Y)).unop⟩, fun _ => Quiver.Hom.op_inj (h.eq_of_src _ _)⟩⟩⟩

Depends on / 依赖: Opposite, Opposite.op, Quiver, Quiver.Hom.op_inj, eq_of_src, eq_of_tgt, from_, h.eq_of_src, h.eq_of_tgt, h.from_, h.to_, op_inj
-/
theorem unop {X : Cᵒᵖ} (h : IsZero X) : IsZero (Opposite.unop X) :=
  ⟨fun Y => ⟨⟨⟨(h.from_ (Opposite.op Y)).unop⟩, fun _ => Quiver.Hom.op_inj (h.eq_of_tgt _ _)⟩⟩,
    fun Y => ⟨⟨⟨(h.to_ (Opposite.op Y)).unop⟩, fun _ => Quiver.Hom.op_inj (h.eq_of_src _ _)⟩⟩⟩

variable (Y) in
/--
Definition of `retract` / `retract` 的定义

English:
definition retract
  signature: (h : IsZero X)
  body: h.to_ Y
  r := h.from_ Y
  retract := h.isInitial.hom_ext _ _

中文:
定义 retract
  签名: (h : 是零 X)
  定义体: h.to_ Y
  r := h.from_ Y
  retract := h.isInitial.hom_ext _ _

Depends on / 依赖: h.to_
-/
def retract (h : IsZero X) : Retract X Y where
  i := h.to_ Y
  r := h.from_ Y
  retract := h.isInitial.hom_ext _ _

end IsZero

end Limits

open CategoryTheory.Limits

/--
theorem `Iso.isZero_iff` / 定理 `Iso.isZero_iff`

English:
theorem Iso.isZero_iff
  given: {X Y : C} (e : X ≅ Y)
  statement: IsZero X ↔ IsZero Y
  proof: ⟨fun h => h.of_iso e.symm, fun h => h.of_iso e⟩

中文:
定理 同构.isZero_iff
  条件: {X Y : C} (e : X ≅ Y)
  结论: 是零 X ↔ 是零 Y
  证明: ⟨fun h => h.of_iso e.symm, fun h => h.of_iso e⟩

Depends on / 依赖: e.symm, h.of_iso, of_iso
-/
theorem Iso.isZero_iff {X Y : C} (e : X ≅ Y) : IsZero X ↔ IsZero Y :=
  ⟨fun h => h.of_iso e.symm, fun h => h.of_iso e⟩

/--
theorem `Functor.isZero` / 定理 `Functor.isZero`

English:
theorem Functor.isZero
  given: (F : C ⥤ D) (hF : forall X, IsZero (F.obj X))
  statement: IsZero F
  proof: by
  constructor <;> intro G <;> refine ⟨⟨⟨?_⟩, ?_⟩⟩
  · refine
      { app := fun X => (hF _).to_ _
        naturality := ?_ }
    intros
    exact (hF _).eq_of_src _ _
  · intro f
    ext
    apply (hF _).eq_of_src _ _
  · refine
      { app := fun X => (hF _).from_ _
        naturality := ?_ }
  

中文:
定理 函子.isZero
  条件: (F : C ⥤ D) (hF : 对任意 X, 是零 (F.obj X))
  结论: 是零 F
  证明: by
  constructor <;> intro G <;> refine ⟨⟨⟨?_⟩, ?_⟩⟩
  · refine
      { app := fun X => (hF _).to_ _
        naturality := ?_ }
    intros
    exact (hF _).eq_of_src _ _
  · intro f
    ext
    apply (hF _).eq_of_src _ _
  · refine
      { app := fun X => (hF _).from_ _
        naturality := ?_ }
  

Depends on / 依赖: eq_of_src, eq_of_tgt, from_, intros, naturality
-/
theorem Functor.isZero (F : C ⥤ D) (hF : forall X, IsZero (F.obj X)) : IsZero F := by
  constructor <;> intro G <;> refine ⟨⟨⟨?_⟩, ?_⟩⟩
  · refine
      { app := fun X => (hF _).to_ _
        naturality := ?_ }
    intros
    exact (hF _).eq_of_src _ _
  · intro f
    ext
    apply (hF _).eq_of_src _ _
  · refine
      { app := fun X => (hF _).from_ _
        naturality := ?_ }
    intros
    exact (hF _).eq_of_tgt _ _
  · intro f
    ext
    apply (hF _).eq_of_tgt _ _

namespace Limits

variable (C)

/--
Definition of `HasZeroObject` / `HasZeroObject` 的定义

English:
class HasZeroObject
  parameters: : Prop where
  axioms and operations (1):
    - zero : exists X : C, IsZero X

中文:
类 有ZeroObject
  参数: : 命题 where
  公理与运算 (1 个):
    - zero : 存在 X : C, 是零 X
-/
class HasZeroObject : Prop where
  /-- there exists a zero object -/
  zero : exists X : C, IsZero X

/--
Instance `hasZeroObject_pUnit` / 实例 `hasZeroObject_pUnit`

English:
instance hasZeroObject_pUnit
  signature: : HasZeroObject (Discrete PUnit) where zero
  body: ⟨⟨⟨⟩⟩,
    { unique_to := fun ⟨⟨⟩⟩ =>
      ⟨{ default := 𝟙 _,
          uniq := by subsingleton }⟩
      unique_from := fun ⟨⟨⟩⟩ =>
      ⟨{ default := 𝟙 _,
          uniq := by subsingleton }⟩}⟩

中文:
实例 hasZeroObject_pUnit
  签名: : 有ZeroObject (离散 命题单元) where zero
  定义体: ⟨⟨⟨⟩⟩,
    { unique_to := fun ⟨⟨⟩⟩ =>
      ⟨{ default := 𝟙 _,
          uniq := by subsingleton }⟩
      unique_from := fun ⟨⟨⟩⟩ =>
      ⟨{ default := 𝟙 _,
          uniq := by subsingleton }⟩}⟩

Depends on / 依赖: subsingleton, unique_from, unique_to
-/
instance hasZeroObject_pUnit : HasZeroObject (Discrete PUnit) where zero :=
  ⟨⟨⟨⟩⟩,
    { unique_to := fun ⟨⟨⟩⟩ =>
      ⟨{ default := 𝟙 _,
          uniq := by subsingleton }⟩
      unique_from := fun ⟨⟨⟩⟩ =>
      ⟨{ default := 𝟙 _,
          uniq := by subsingleton }⟩}⟩

section

variable [HasZeroObject C]

/-- Construct a `Zero C` for a category with a zero object.
This cannot be a global instance as it will trigger for every `Zero C` typeclass search.
-/
@[instance_reducible]
/--
Definition of `HasZeroObject.zero'` / `HasZeroObject.zero'` 的定义

English:
definition HasZeroObject.zero'
  signature: : Zero C where zero
  body: HasZeroObject.zero.choose

scoped[ZeroObject] attribute [instance] CategoryTheory.Limits.HasZeroObject.zero'

中文:
定义 有ZeroObject.zero'
  签名: : 零 C where zero
  定义体: HasZeroObject.zero.choose

scoped[ZeroObject] attribute [instance] CategoryTheory.Limits.HasZeroObject.zero'
-/
protected def HasZeroObject.zero' : Zero C where zero := HasZeroObject.zero.choose

scoped[ZeroObject] attribute [instance] CategoryTheory.Limits.HasZeroObject.zero'

open ZeroObject

/--
theorem `isZero_zero` / 定理 `isZero_zero`

English:
theorem isZero_zero
  statement: IsZero (0 : C)
  proof: HasZeroObject.zero.choose_spec

中文:
定理 isZero_zero
  结论: 是零 (0 : C)
  证明: HasZeroObject.zero.choose_spec

Depends on / 依赖: HasZeroObject, HasZeroObject.zero.choose_spec, choose_spec
-/
theorem isZero_zero : IsZero (0 : C) :=
  HasZeroObject.zero.choose_spec

/--
Instance `hasZeroObject_op` / 实例 `hasZeroObject_op`

English:
instance hasZeroObject_op
  signature: : HasZeroObject Cᵒᵖ
  body: ⟨⟨Opposite.op 0, IsZero.op (isZero_zero C)⟩⟩

中文:
实例 hasZeroObject_op
  签名: : 有ZeroObject Cᵒᵖ
  定义体: ⟨⟨Opposite.op 0, IsZero.op (isZero_zero C)⟩⟩

Depends on / 依赖: IsZero, IsZero.op, Opposite, Opposite.op, isZero_zero
-/
instance hasZeroObject_op : HasZeroObject Cᵒᵖ :=
  ⟨⟨Opposite.op 0, IsZero.op (isZero_zero C)⟩⟩

end

open ZeroObject

/--
theorem `hasZeroObject_unop` / 定理 `hasZeroObject_unop`

English:
theorem hasZeroObject_unop
  given: [HasZeroObject Cᵒᵖ]
  statement: HasZeroObject C
  proof: ⟨⟨Opposite.unop 0, IsZero.unop (isZero_zero Cᵒᵖ)⟩⟩

中文:
定理 hasZeroObject_unop
  条件: [有ZeroObject Cᵒᵖ]
  结论: 有ZeroObject C
  证明: ⟨⟨Opposite.unop 0, IsZero.unop (isZero_zero Cᵒᵖ)⟩⟩

Depends on / 依赖: IsZero, IsZero.unop, Opposite, Opposite.unop, isZero_zero
-/
theorem hasZeroObject_unop [HasZeroObject Cᵒᵖ] : HasZeroObject C :=
  ⟨⟨Opposite.unop 0, IsZero.unop (isZero_zero Cᵒᵖ)⟩⟩

variable {C}

/--
theorem `IsZero.hasZeroObject` / 定理 `IsZero.hasZeroObject`

English:
theorem IsZero.hasZeroObject
  given: {X : C} (hX : IsZero X)
  statement: HasZeroObject C
  proof: ⟨⟨X, hX⟩⟩

中文:
定理 是零.hasZeroObject
  条件: {X : C} (hX : 是零 X)
  结论: 有ZeroObject C
  证明: ⟨⟨X, hX⟩⟩
-/
theorem IsZero.hasZeroObject {X : C} (hX : IsZero X) : HasZeroObject C :=
  ⟨⟨X, hX⟩⟩

/--
Definition of `IsZero.isoZero` / `IsZero.isoZero` 的定义

English:
definition IsZero.isoZero
  signature: [HasZeroObject C] {X : C} (hX : IsZero X)
  body: hX.iso (isZero_zero C)

中文:
定义 是零.isoZero
  签名: [有ZeroObject C] {X : C} (hX : 是零 X)
  定义体: hX.iso (isZero_zero C)

Depends on / 依赖: hX.iso, isZero_zero
-/
def IsZero.isoZero [HasZeroObject C] {X : C} (hX : IsZero X) : X ≅ 0 :=
  hX.iso (isZero_zero C)

/--
theorem `IsZero.obj` / 定理 `IsZero.obj`

English:
theorem IsZero.obj
  given: [HasZeroObject D] {F : C ⥤ D} (hF : IsZero F) (X : C)
  statement: IsZero (F.obj X)
  proof: by
  let G : C ⥤ D := (CategoryTheory.Functor.const C).obj 0
  have hG : IsZero G := Functor.isZero _ fun _ => isZero_zero _
  let e : F ≅ G := hF.iso hG
  exact (isZero_zero _).of_iso (e.app X)

中文:
定理 是零.obj
  条件: [有ZeroObject D] {F : C ⥤ D} (hF : 是零 F) (X : C)
  结论: 是零 (F.obj X)
  证明: by
  let G : C ⥤ D := (CategoryTheory.Functor.const C).obj 0
  have hG : IsZero G := Functor.isZero _ fun _ => isZero_zero _
  let e : F ≅ G := hF.iso hG
  exact (isZero_zero _).of_iso (e.app X)

Depends on / 依赖: CategoryTheory, CategoryTheory.Functor.const, Functor, Functor.isZero, IsZero, e.app, hF.iso, isZero, isZero_zero, of_iso
-/
theorem IsZero.obj [HasZeroObject D] {F : C ⥤ D} (hF : IsZero F) (X : C) : IsZero (F.obj X) := by
  let G : C ⥤ D := (CategoryTheory.Functor.const C).obj 0
  have hG : IsZero G := Functor.isZero _ fun _ => isZero_zero _
  let e : F ≅ G := hF.iso hG
  exact (isZero_zero _).of_iso (e.app X)

/--
lemma `IsZero.of_full_of_faithful_of_isZero` / 引理 `IsZero.of_full_of_faithful_of_isZero`

English:
lemma IsZero.of_full_of_faithful_of_isZero
  proof: by
  have h : F.FullyFaithful := .ofFullyFaithful _
  have (Y : C) := (hX.unique_to (F.obj Y)).some
  have (Y : C) := (hX.unique_from (F.obj Y)).some
  exact ⟨fun Y => ⟨h.homEquiv.unique⟩, fun Y => ⟨h.homEquiv.unique⟩⟩

中文:
引理 是零.of_full_of_faithful_of_isZero
  证明: by
  have h : F.FullyFaithful := .ofFullyFaithful _
  have (Y : C) := (hX.unique_to (F.obj Y)).some
  have (Y : C) := (hX.unique_from (F.obj Y)).some
  exact ⟨fun Y => ⟨h.homEquiv.unique⟩, fun Y => ⟨h.homEquiv.unique⟩⟩

Depends on / 依赖: F.FullyFaithful, F.obj, FullyFaithful, h.homEquiv.unique, hX.unique_from, hX.unique_to, homEquiv, ofFullyFaithful, unique, unique_from, unique_to
-/
lemma IsZero.of_full_of_faithful_of_isZero
    (F : C ⥤ D) [F.Full] [F.Faithful] (X : C) (hX : IsZero (F.obj X)) :
    IsZero X := by
  have h : F.FullyFaithful := .ofFullyFaithful _
  have (Y : C) := (hX.unique_to (F.obj Y)).some
  have (Y : C) := (hX.unique_from (F.obj Y)).some
  exact ⟨fun Y => ⟨h.homEquiv.unique⟩, fun Y => ⟨h.homEquiv.unique⟩⟩

namespace HasZeroObject

variable [HasZeroObject C]

/-- There is a unique morphism from the zero object to any object `X`. -/
@[instance_reducible]
/--
Definition of `uniqueTo` / `uniqueTo` 的定义

English:
definition uniqueTo
  signature: (X : C)
  body: ((isZero_zero C).unique_to X).some

中文:
定义 uniqueTo
  签名: (X : C)
  定义体: ((isZero_zero C).unique_to X).some
-/
protected def uniqueTo (X : C) : Unique (0 ⟶ X) :=
  ((isZero_zero C).unique_to X).some

/-- There is a unique morphism from any object `X` to the zero object. -/
@[instance_reducible]
/--
Definition of `uniqueFrom` / `uniqueFrom` 的定义

English:
definition uniqueFrom
  signature: (X : C)
  body: ((isZero_zero C).unique_from X).some

scoped[ZeroObject] attribute [instance] CategoryTheory.Limits.HasZeroObject.uniqueTo

scoped[ZeroObject] attribute [instance] CategoryTheory.Limits.HasZeroObject.uniqueFrom

@[ext]

中文:
定义 uniqueFrom
  签名: (X : C)
  定义体: ((isZero_zero C).unique_from X).some

scoped[ZeroObject] attribute [instance] CategoryTheory.Limits.HasZeroObject.uniqueTo

scoped[ZeroObject] attribute [instance] CategoryTheory.Limits.HasZeroObject.uniqueFrom

@[ext]
-/
protected def uniqueFrom (X : C) : Unique (X ⟶ 0) :=
  ((isZero_zero C).unique_from X).some

scoped[ZeroObject] attribute [instance] CategoryTheory.Limits.HasZeroObject.uniqueTo

scoped[ZeroObject] attribute [instance] CategoryTheory.Limits.HasZeroObject.uniqueFrom

@[ext]
/--
theorem `to_zero_ext` / 定理 `to_zero_ext`

English:
theorem to_zero_ext
  given: {X : C} (f g : X ⟶ 0)
  statement: f = g
  proof: (isZero_zero C).eq_of_tgt _ _

@[ext]

中文:
定理 to_zero_ext
  条件: {X : C} (f g : X ⟶ 0)
  结论: f = g
  证明: (isZero_zero C).eq_of_tgt _ _

@[ext]

Depends on / 依赖: eq_of_tgt, isZero_zero
-/
theorem to_zero_ext {X : C} (f g : X ⟶ 0) : f = g :=
  (isZero_zero C).eq_of_tgt _ _

@[ext]
/--
theorem `from_zero_ext` / 定理 `from_zero_ext`

English:
theorem from_zero_ext
  given: {X : C} (f g : 0 ⟶ X)
  statement: f = g
  proof: (isZero_zero C).eq_of_src _ _

中文:
定理 from_zero_ext
  条件: {X : C} (f g : 0 ⟶ X)
  结论: f = g
  证明: (isZero_zero C).eq_of_src _ _

Depends on / 依赖: eq_of_src, isZero_zero
-/
theorem from_zero_ext {X : C} (f g : 0 ⟶ X) : f = g :=
  (isZero_zero C).eq_of_src _ _

instance (X : C) : Subsingleton (X ≅ 0) := ⟨fun f g => by ext⟩

instance {X : C} (f : 0 ⟶ X) : Mono f where right_cancellation g h _ := by ext

instance {X : C} (f : X ⟶ 0) : Epi f where left_cancellation g h _ := by ext

/--
Instance `zero_to_zero_isIso` / 实例 `zero_to_zero_isIso`

English:
instance zero_to_zero_isIso
  signature: (f : (0 : C) ⟶ 0)
  body: by
  convert! show IsIso (𝟙 (0 : C)) by infer_instance
  subsingleton

中文:
实例 zero_to_zero_isIso
  签名: (f : (0 : C) ⟶ 0)
  定义体: by
  convert! show IsIso (𝟙 (0 : C)) by infer_instance
  subsingleton

Depends on / 依赖: convert, infer_instance, subsingleton
-/
instance zero_to_zero_isIso (f : (0 : C) ⟶ 0) : IsIso f := by
  convert! show IsIso (𝟙 (0 : C)) by infer_instance
  subsingleton

/--
Definition of `zeroIsInitial` / `zeroIsInitial` 的定义

English:
definition zeroIsInitial
  signature: : IsInitial (0 : C)
  body: (isZero_zero C).isInitial

中文:
定义 zeroIsInitial
  签名: : IsInitial (0 : C)
  定义体: (isZero_zero C).isInitial

Depends on / 依赖: isInitial, isZero_zero
-/
def zeroIsInitial : IsInitial (0 : C) :=
  (isZero_zero C).isInitial

/--
Definition of `zeroIsTerminal` / `zeroIsTerminal` 的定义

English:
definition zeroIsTerminal
  signature: : IsTerminal (0 : C)
  body: (isZero_zero C).isTerminal

中文:
定义 zeroIsTerminal
  签名: : 是终止 (0 : C)
  定义体: (isZero_zero C).isTerminal

Depends on / 依赖: isTerminal, isZero_zero
-/
def zeroIsTerminal : IsTerminal (0 : C) :=
  (isZero_zero C).isTerminal

/-- A zero object is in particular initial. -/
instance (priority := 10) hasInitial : HasInitial C :=
  hasInitial_of_unique 0

/-- A zero object is in particular terminal. -/
instance (priority := 10) hasTerminal : HasTerminal C :=
  hasTerminal_of_unique 0

/--
Definition of `zeroIsoIsInitial` / `zeroIsoIsInitial` 的定义

English:
definition zeroIsoIsInitial
  signature: {X : C} (t : IsInitial X)
  body: zeroIsInitial.uniqueUpToIso t

中文:
定义 zeroIsoIsInitial
  签名: {X : C} (t : IsInitial X)
  定义体: zeroIsInitial.uniqueUpToIso t

Depends on / 依赖: uniqueUpToIso, zeroIsInitial, zeroIsInitial.uniqueUpToIso
-/
def zeroIsoIsInitial {X : C} (t : IsInitial X) : 0 ≅ X :=
  zeroIsInitial.uniqueUpToIso t

/--
Definition of `zeroIsoIsTerminal` / `zeroIsoIsTerminal` 的定义

English:
definition zeroIsoIsTerminal
  signature: {X : C} (t : IsTerminal X)
  body: zeroIsTerminal.uniqueUpToIso t

中文:
定义 zeroIsoIsTerminal
  签名: {X : C} (t : 是终止 X)
  定义体: zeroIsTerminal.uniqueUpToIso t

Depends on / 依赖: uniqueUpToIso, zeroIsTerminal, zeroIsTerminal.uniqueUpToIso
-/
def zeroIsoIsTerminal {X : C} (t : IsTerminal X) : 0 ≅ X :=
  zeroIsTerminal.uniqueUpToIso t

/--
Definition of `zeroIsoInitial` / `zeroIsoInitial` 的定义

English:
definition zeroIsoInitial
  signature: [HasInitial C]
  body: zeroIsInitial.uniqueUpToIso initialIsInitial

中文:
定义 zeroIsoInitial
  签名: [HasInitial C]
  定义体: zeroIsInitial.uniqueUpToIso initialIsInitial

Depends on / 依赖: initialIsInitial, uniqueUpToIso, zeroIsInitial, zeroIsInitial.uniqueUpToIso
-/
def zeroIsoInitial [HasInitial C] : 0 ≅ ⊥_ C :=
  zeroIsInitial.uniqueUpToIso initialIsInitial

/--
Definition of `zeroIsoTerminal` / `zeroIsoTerminal` 的定义

English:
definition zeroIsoTerminal
  signature: [HasTerminal C]
  body: zeroIsTerminal.uniqueUpToIso terminalIsTerminal

中文:
定义 zeroIsoTerminal
  签名: [有终止 C]
  定义体: zeroIsTerminal.uniqueUpToIso terminalIsTerminal

Depends on / 依赖: terminalIsTerminal, uniqueUpToIso, zeroIsTerminal, zeroIsTerminal.uniqueUpToIso
-/
def zeroIsoTerminal [HasTerminal C] : 0 ≅ ⊤_ C :=
  zeroIsTerminal.uniqueUpToIso terminalIsTerminal

instance (priority := 100) initialMonoClass : InitialMonoClass C :=
  InitialMonoClass.of_isInitial zeroIsInitial fun X => by infer_instance

end HasZeroObject

end Limits

open CategoryTheory.Limits

open ZeroObject

/--
theorem `Functor.isZero_iff` / 定理 `Functor.isZero_iff`

English:
theorem Functor.isZero_iff
  given: [HasZeroObject D] (F : C ⥤ D)
  statement: IsZero F ↔ forall X, IsZero (F.obj X)
  proof: ⟨fun hF X => hF.obj X, Functor.isZero _⟩

中文:
定理 函子.isZero_iff
  条件: [有ZeroObject D] (F : C ⥤ D)
  结论: 是零 F ↔ 对任意 X, 是零 (F.obj X)
  证明: ⟨fun hF X => hF.obj X, Functor.isZero _⟩

Depends on / 依赖: Functor, Functor.isZero, hF.obj, isZero
-/
theorem Functor.isZero_iff [HasZeroObject D] (F : C ⥤ D) : IsZero F ↔ forall X, IsZero (F.obj X) :=
  ⟨fun hF X => hF.obj X, Functor.isZero _⟩

instance {C : Type*} [Category* C] (A : C) [HasZeroObject C] : Epi (terminalIsTerminal.from A) :=
  (((isZero_zero C).of_iso HasZeroObject.zeroIsoTerminal.symm).epi _)

end CategoryTheory
