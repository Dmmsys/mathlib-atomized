/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.TransfiniteCompositionOfShape
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.Order.Interval.Set.SuccOrder
public import Mathlib.Order.Shrink
/-!
# Classes of morphisms that are stable under transfinite composition

Given a well-ordered type `J`, `W : MorphismProperty C` and
a morphism `f : X ⟶ Y`, we define a structure `W.TransfiniteCompositionOfShape J f`
which expresses that `f` is a transfinite composition of shape `J` of morphisms in `W`.
This structures extends `CategoryTheory.TransfiniteCompositionOfShape` which was
defined in the file `CategoryTheory.Limits.Shape.Preorder.TransfiniteCompositionOfShape`.
We use this structure in order to define the class of morphisms
`W.transfiniteCompositionsOfShape J : MorphismProperty C`, and the type class
`W.IsStableUnderTransfiniteCompositionOfShape J`.
In particular, if `J := ℕ`, we define `W.IsStableUnderInfiniteComposition`,

Finally, we introduce the class `W.IsStableUnderTransfiniteComposition`
which says that `W.IsStableUnderTransfiniteCompositionOfShape J`
holds for any well-ordered type `J` in a certain universe `w`.

-/

@[expose] public section

universe w w' v v' u u'

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

namespace MorphismProperty

variable (W : MorphismProperty C)

section

variable (J : Type w) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
  {J' : Type w'} [LinearOrder J'] [SuccOrder J'] [OrderBot J'] [WellFoundedLT J']

/--
Definition of `TransfiniteCompositionOfShape` / `TransfiniteCompositionOfShape` 的定义

English:
structure TransfiniteCompositionOfShape
  parameters: {X Y : C} (f : X ⟶ Y)
  axioms and operations (1):
    - map_mem((j : J) (hj : ¬IsMax j)) : W (F.map (homOfLE (Order.le_succ j)))

中文:
结构 TransfiniteCompositionOfShape
  参数: {X Y : C} (f : X ⟶ Y)
  公理与运算 (1 个):
    - map_mem((j : J) (hj : ¬IsMax j)) : W (F.map (homOfLE (Order.le_succ j)))
-/
structure TransfiniteCompositionOfShape {X Y : C} (f : X ⟶ Y) extends
    CategoryTheory.TransfiniteCompositionOfShape J f where
  map_mem (j : J) (hj : ¬IsMax j) : W (F.map (homOfLE (Order.le_succ j)))

namespace TransfiniteCompositionOfShape

section

variable {W J} {X Y : C} {f : X ⟶ Y} (h : W.TransfiniteCompositionOfShape J f)

/-- If `f` and `f'` are two isomorphic morphisms and `f` is a transfinite composition
of morphisms in `W : MorphismProperty C`, then so is `f'`. -/
@[simps toTransfiniteCompositionOfShape]
/--
Definition of `ofArrowIso` / `ofArrowIso` 的定义

English:
definition ofArrowIso
  signature: {X' Y' : C}
  body: h.toTransfiniteCompositionOfShape.ofArrowIso e
  map_mem := h.map_mem

中文:
定义 ofArrowIso
  签名: {X' Y' : C}
  定义体: h.toTransfiniteCompositionOfShape.ofArrowIso e
  map_mem := h.map_mem

Depends on / 依赖: h.toTransfiniteCompositionOfShape.ofArrowIso, ofArrowIso, toTransfiniteCompositionOfShape
-/
def ofArrowIso {X' Y' : C}
    {f' : X' ⟶ Y'} (e : Arrow.mk f ≅ Arrow.mk f') :
    W.TransfiniteCompositionOfShape J f' where
  __ := h.toTransfiniteCompositionOfShape.ofArrowIso e
  map_mem := h.map_mem

/-- If `W ≤ W'`, then transfinite compositions of shape `J` of morphisms in `W`
are also transfinite composition of shape `J` of morphisms in `W'`. -/
@[simps toTransfiniteCompositionOfShape]
/--
Definition of `ofLE` / `ofLE` 的定义

English:
definition ofLE
  signature: {W' : MorphismProperty C} (hW : W <= W')
  body: h.toTransfiniteCompositionOfShape
  map_mem j hj := hW _ (h.map_mem j hj)

中文:
定义 ofLE
  签名: {W' : MorphismProperty C} (hW : W <= W')
  定义体: h.toTransfiniteCompositionOfShape
  map_mem j hj := hW _ (h.map_mem j hj)

Depends on / 依赖: h.toTransfiniteCompositionOfShape, toTransfiniteCompositionOfShape
-/
def ofLE {W' : MorphismProperty C} (hW : W <= W') :
    W'.TransfiniteCompositionOfShape J f where
  __ := h.toTransfiniteCompositionOfShape
  map_mem j hj := hW _ (h.map_mem j hj)

/--
Definition of `ofOrderIso` / `ofOrderIso` 的定义

English:
definition ofOrderIso
  signature: {J' : Type w'} [LinearOrder J'] [OrderBot J']
  body: h.toTransfiniteCompositionOfShape.ofOrderIso e
  map_mem j hj := by
    have := h.map_mem (e j) (by simpa only [e.isMax_apply])
    rw [← W.arrow_mk_mem_toSet_iff] at this ⊢
    have eq : Arrow.mk (homOfLE (e.monotone (Order.le_succ j))) =
      Arrow.mk (homOfLE (Order.le_succ (e j))) :=
        Ar

中文:
定义 ofOrderIso
  签名: {J' : 类型 w'} [线性序 J'] [有底序 J']
  定义体: h.toTransfiniteCompositionOfShape.ofOrderIso e
  map_mem j hj := by
    have := h.map_mem (e j) (by simpa only [e.isMax_apply])
    rw [← W.arrow_mk_mem_toSet_iff] at this ⊢
    have eq : Arrow.mk (homOfLE (e.monotone (Order.le_succ j))) =
      Arrow.mk (homOfLE (Order.le_succ (e j))) :=
        Ar

Depends on / 依赖: h.toTransfiniteCompositionOfShape.ofOrderIso, ofOrderIso, toTransfiniteCompositionOfShape
-/
def ofOrderIso {J' : Type w'} [LinearOrder J'] [OrderBot J']
    [SuccOrder J'] [WellFoundedLT J'] (e : J' ≃o J) :
    W.TransfiniteCompositionOfShape J' f where
  __ := h.toTransfiniteCompositionOfShape.ofOrderIso e
  map_mem j hj := by
    have := h.map_mem (e j) (by simpa only [e.isMax_apply])
    rw [← W.arrow_mk_mem_toSet_iff] at this ⊢
    have eq : Arrow.mk (homOfLE (e.monotone (Order.le_succ j))) =
      Arrow.mk (homOfLE (Order.le_succ (e j))) :=
        Arrow.ext rfl (e.map_succ j) rfl
    replace eq := congr_arg h.F.mapArrow.obj eq
    convert! this using 1

/-- If `f` is a transfinite composition of shape `J` of morphisms
in `W.inverseImage F`, then `F` is a transfinite composition of shape `J`
of morphisms in `W` provided `F` preserves suitable colimits. -/
@[simps toTransfiniteCompositionOfShape]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {W : MorphismProperty D} {F : C ⥤ D}
  body: h.toTransfiniteCompositionOfShape.map F
  map_mem j hj := h.map_mem j hj

中文:
定义 map
  签名: {W : MorphismProperty D} {F : C ⥤ D}
  定义体: h.toTransfiniteCompositionOfShape.map F
  map_mem j hj := h.map_mem j hj

Depends on / 依赖: h.toTransfiniteCompositionOfShape.map, toTransfiniteCompositionOfShape
-/
noncomputable def map {W : MorphismProperty D} {F : C ⥤ D}
    [PreservesWellOrderContinuousOfShape J F]
    [PreservesColimitsOfShape J F]
    (h : (W.inverseImage F).TransfiniteCompositionOfShape J f) :
    W.TransfiniteCompositionOfShape J (F.map f) where
  __ := h.toTransfiniteCompositionOfShape.map F
  map_mem j hj := h.map_mem j hj

/--
Definition of `iic` / `iic` 的定义

English:
definition iic
  signature: (j : J)
  body: h.toTransfiniteCompositionOfShape.iic j
  map_mem i hi := by
    have := h.map_mem i.1 (by
      rw [not_isMax_iff] at hi ⊢
      obtain ⟨i', hi'⟩ := hi
      exact ⟨j, lt_of_lt_of_le hi' i'.2⟩)
    rw [← W.arrow_mk_mem_toSet_iff] at this ⊢
    have eq : Arrow.mk ((Subtype.mono_coe _).functor.map (h

中文:
定义 iic
  签名: (j : J)
  定义体: h.toTransfiniteCompositionOfShape.iic j
  map_mem i hi := by
    have := h.map_mem i.1 (by
      rw [not_isMax_iff] at hi ⊢
      obtain ⟨i', hi'⟩ := hi
      exact ⟨j, lt_of_lt_of_le hi' i'.2⟩)
    rw [← W.arrow_mk_mem_toSet_iff] at this ⊢
    have eq : Arrow.mk ((Subtype.mono_coe _).functor.map (h

Depends on / 依赖: h.toTransfiniteCompositionOfShape.iic, toTransfiniteCompositionOfShape
-/
noncomputable def iic (j : J) :
    W.TransfiniteCompositionOfShape (Set.Iic j) (h.F.map (homOfLE bot_le : ⊥ ⟶ j)) where
  __ := h.toTransfiniteCompositionOfShape.iic j
  map_mem i hi := by
    have := h.map_mem i.1 (by
      rw [not_isMax_iff] at hi ⊢
      obtain ⟨i', hi'⟩ := hi
      exact ⟨j, lt_of_lt_of_le hi' i'.2⟩)
    rw [← W.arrow_mk_mem_toSet_iff] at this ⊢
    have eq : Arrow.mk ((Subtype.mono_coe _).functor.map (homOfLE (Order.le_succ i))) =
      Arrow.mk (homOfLE (Order.le_succ i.1)) :=
        Arrow.ext rfl (Set.Iic.coe_succ_of_not_isMax hi) rfl
    replace eq := congr_arg h.F.mapArrow.obj eq
    convert! this using 1

/--
Definition of `ici` / `ici` 的定义

English:
definition ici
  signature: (j : J)
  body: h.toTransfiniteCompositionOfShape.ici j
  map_mem i hi := by
    have := h.map_mem i.1 (Set.not_isMax_coe _ hi)
    rw [← W.arrow_mk_mem_toSet_iff] at this ⊢
    have eq : Arrow.mk ((Subtype.mono_coe _).functor.map (homOfLE (Order.le_succ i))) =
      Arrow.mk (homOfLE (Order.le_succ i.1)) :=
      

中文:
定义 ici
  签名: (j : J)
  定义体: h.toTransfiniteCompositionOfShape.ici j
  map_mem i hi := by
    have := h.map_mem i.1 (Set.not_isMax_coe _ hi)
    rw [← W.arrow_mk_mem_toSet_iff] at this ⊢
    have eq : Arrow.mk ((Subtype.mono_coe _).functor.map (homOfLE (Order.le_succ i))) =
      Arrow.mk (homOfLE (Order.le_succ i.1)) :=
      

Depends on / 依赖: h.toTransfiniteCompositionOfShape.ici, toTransfiniteCompositionOfShape
-/
noncomputable def ici (j : J) :
    W.TransfiniteCompositionOfShape (Set.Ici j) (h.incl.app j) where
  __ := h.toTransfiniteCompositionOfShape.ici j
  map_mem i hi := by
    have := h.map_mem i.1 (Set.not_isMax_coe _ hi)
    rw [← W.arrow_mk_mem_toSet_iff] at this ⊢
    have eq : Arrow.mk ((Subtype.mono_coe _).functor.map (homOfLE (Order.le_succ i))) =
      Arrow.mk (homOfLE (Order.le_succ i.1)) :=
        Arrow.ext rfl (coe_succ_of_mem (i.2.trans (Order.le_succ _))) rfl
    replace eq := congr_arg h.F.mapArrow.obj eq
    convert! this using 1

end

/-- If `F : ComposableArrows C n` and all maps `F.obj i.castSucc ⟶ F.obj i.succ`
are in `W`, then `F.hom : F.left ⟶ F.right` is a transfinite composition of
shape `Fin (n + 1)` of morphisms in `W`. -/
@[simps!]
/--
Definition of `ofComposableArrows` / `ofComposableArrows` 的定义

English:
definition ofComposableArrows
  signature: {n : Nat} (F : ComposableArrows C n)
  body: .ofComposableArrows F
  map_mem j hj := by
    obtain ⟨j, rfl⟩ | rfl := j.eq_castSucc_or_eq_last
    · replace hF := hF j
      rw [← W.arrow_mk_mem_toSet_iff] at hF ⊢
      have eq : Arrow.mk (homOfLE (Order.le_succ j.castSucc)) =
        Arrow.mk (homOfLE j.castSucc_le_succ) :=
          Arrow.ext

中文:
定义 ofComposableArrows
  签名: {n : 自然数} (F : ComposableArrows C n)
  定义体: .ofComposableArrows F
  map_mem j hj := by
    obtain ⟨j, rfl⟩ | rfl := j.eq_castSucc_or_eq_last
    · replace hF := hF j
      rw [← W.arrow_mk_mem_toSet_iff] at hF ⊢
      have eq : Arrow.mk (homOfLE (Order.le_succ j.castSucc)) =
        Arrow.mk (homOfLE j.castSucc_le_succ) :=
          Arrow.ext

Depends on / 依赖: ofComposableArrows
-/
def ofComposableArrows {n : Nat} (F : ComposableArrows C n)
    (hF : forall (i : Fin n), W (F.map (homOfLE i.castSucc_le_succ))) :
    W.TransfiniteCompositionOfShape (Fin (n + 1)) F.hom where
  toTransfiniteCompositionOfShape := .ofComposableArrows F
  map_mem j hj := by
    obtain ⟨j, rfl⟩ | rfl := j.eq_castSucc_or_eq_last
    · replace hF := hF j
      rw [← W.arrow_mk_mem_toSet_iff] at hF ⊢
      have eq : Arrow.mk (homOfLE (Order.le_succ j.castSucc)) =
        Arrow.mk (homOfLE j.castSucc_le_succ) :=
          Arrow.ext rfl j.orderSucc_castSucc rfl
      replace eq := congr_arg F.mapArrow.obj eq
      convert! hF using 1
    · rw [isMax_iff_eq_top] at hj
      exact (hj rfl).elim

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (X : C)
  body: ofComposableArrows W (.mk₀ X) (by simp)

中文:
定义 id
  签名: (X : C)
  定义体: ofComposableArrows W (.mk₀ X) (by simp)

Depends on / 依赖: ofComposableArrows
-/
def id (X : C) : W.TransfiniteCompositionOfShape (Fin 1) (𝟙 X) :=
  ofComposableArrows W (.mk₀ X) (by simp)

variable {W}

/--
Definition of `ofMem` / `ofMem` 的定义

English:
definition ofMem
  signature: {X Y : C} (f : X ⟶ Y) (hf : W f)
  body: ofComposableArrows W (.mk₁ f) (fun i => by fin_cases i; assumption)

中文:
定义 ofMem
  签名: {X Y : C} (f : X ⟶ Y) (hf : W f)
  定义体: ofComposableArrows W (.mk₁ f) (fun i => by fin_cases i; assumption)

Depends on / 依赖: fin_cases, ofComposableArrows
-/
def ofMem {X Y : C} (f : X ⟶ Y) (hf : W f) :
    W.TransfiniteCompositionOfShape (Fin 2) f :=
  ofComposableArrows W (.mk₁ f) (fun i => by fin_cases i; assumption)

/--
Definition of `ofComp` / `ofComp` 的定义

English:
definition ofComp
  signature: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) (hg : W g)
  body: ofComposableArrows W (.mk₂ f g) (fun i => by fin_cases i <;> assumption)

中文:
定义 ofComp
  签名: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) (hg : W g)
  定义体: ofComposableArrows W (.mk₂ f g) (fun i => by fin_cases i <;> assumption)

Depends on / 依赖: fin_cases, ofComposableArrows
-/
def ofComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) (hg : W g) :
    W.TransfiniteCompositionOfShape (Fin 3) (f ≫ g) :=
  ofComposableArrows W (.mk₂ f g) (fun i => by fin_cases i <;> assumption)

end TransfiniteCompositionOfShape

/--
Definition of `transfiniteCompositionsOfShape` / `transfiniteCompositionsOfShape` 的定义

English:
definition transfiniteCompositionsOfShape
  signature: : MorphismProperty C
  body: fun _ _ f => Nonempty (W.TransfiniteCompositionOfShape J f)

中文:
定义 transfiniteCompositionsOfShape
  签名: : MorphismProperty C
  定义体: fun _ _ f => Nonempty (W.TransfiniteCompositionOfShape J f)

Depends on / 依赖: Nonempty, TransfiniteCompositionOfShape, W.TransfiniteCompositionOfShape
-/
def transfiniteCompositionsOfShape : MorphismProperty C :=
  fun _ _ f => Nonempty (W.TransfiniteCompositionOfShape J f)

/--
lemma `transfiniteCompositionsOfShape_monotone` / 引理 `transfiniteCompositionsOfShape_monotone`

English:
lemma transfiniteCompositionsOfShape_monotone
  proof: by
  rintro _ _ h _ _ _ ⟨t⟩
  exact ⟨t.ofLE h⟩

中文:
引理 transfiniteCompositionsOfShape_monotone
  证明: by
  rintro _ _ h _ _ _ ⟨t⟩
  exact ⟨t.ofLE h⟩

Depends on / 依赖: t.ofLE
-/
lemma transfiniteCompositionsOfShape_monotone :
    Monotone (transfiniteCompositionsOfShape (C := C) (J := J)) := by
  rintro _ _ h _ _ _ ⟨t⟩
  exact ⟨t.ofLE h⟩

variable {J} in
/--
lemma `transfiniteCompositionsOfShape_eq_of_orderIso` / 引理 `transfiniteCompositionsOfShape_eq_of_orderIso`

English:
lemma transfiniteCompositionsOfShape_eq_of_orderIso
  given: (e : J ≃o J')
  proof: by
  ext _ _ f
  exact ⟨fun ⟨h⟩ => ⟨h.ofOrderIso e.symm⟩, fun ⟨h⟩ => ⟨h.ofOrderIso e⟩⟩

中文:
引理 transfiniteCompositionsOfShape_eq_of_orderIso
  条件: (e : J ≃o J')
  证明: by
  ext _ _ f
  exact ⟨fun ⟨h⟩ => ⟨h.ofOrderIso e.symm⟩, fun ⟨h⟩ => ⟨h.ofOrderIso e⟩⟩

Depends on / 依赖: e.symm, h.ofOrderIso, ofOrderIso
-/
lemma transfiniteCompositionsOfShape_eq_of_orderIso (e : J ≃o J') :
    W.transfiniteCompositionsOfShape J =
      W.transfiniteCompositionsOfShape J' := by
  ext _ _ f
  exact ⟨fun ⟨h⟩ => ⟨h.ofOrderIso e.symm⟩, fun ⟨h⟩ => ⟨h.ofOrderIso e⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: RespectsIso (W.transfiniteCompositionsOfShape J)
  body: RespectsIso.of_respects_arrow_iso _ (fun _ _ e ⟨h⟩ => ⟨h.ofArrowIso e⟩)

中文:
实例 :
  签名: RespectsIso (W.transfiniteCompositionsOfShape J)
  定义体: RespectsIso.of_respects_arrow_iso _ (fun _ _ e ⟨h⟩ => ⟨h.ofArrowIso e⟩)

Depends on / 依赖: RespectsIso, RespectsIso.of_respects_arrow_iso, h.ofArrowIso, ofArrowIso, of_respects_arrow_iso
-/
instance : RespectsIso (W.transfiniteCompositionsOfShape J) :=
  RespectsIso.of_respects_arrow_iso _ (fun _ _ e ⟨h⟩ => ⟨h.ofArrowIso e⟩)

variable {W J} in
/--
lemma `TransfiniteCompositionOfShape.mem` / 引理 `TransfiniteCompositionOfShape.mem`

English:
lemma TransfiniteCompositionOfShape.mem
  statement: {X Y : C} (f : X ⟶ Y)
  proof: ⟨h⟩

中文:
引理 TransfiniteCompositionOfShape.mem
  结论: {X Y : C} (f : X ⟶ Y)
  证明: ⟨h⟩
-/
lemma TransfiniteCompositionOfShape.mem {X Y : C} (f : X ⟶ Y)
    (h : W.TransfiniteCompositionOfShape J f) :
    W.transfiniteCompositionsOfShape J f := ⟨h⟩

/--
lemma `transfiniteCompositionsOfShape_map_of_preserves` / 引理 `transfiniteCompositionsOfShape_map_of_preserves`

English:
lemma transfiniteCompositionsOfShape_map_of_preserves
  statement: (G : C ⥤ D)
  proof: h.some.map.mem

中文:
引理 transfiniteCompositionsOfShape_map_of_preserves
  结论: (G : C ⥤ D)
  证明: h.some.map.mem

Depends on / 依赖: h.some.map.mem
-/
lemma transfiniteCompositionsOfShape_map_of_preserves (G : C ⥤ D)
    [PreservesWellOrderContinuousOfShape J G]
    {X Y : C} (f : X ⟶ Y) {P : MorphismProperty D}
    [PreservesColimitsOfShape J G]
    (h : (P.inverseImage G).transfiniteCompositionsOfShape J f) :
    P.transfiniteCompositionsOfShape J (G.map f) :=
  h.some.map.mem

/-- A class of morphisms `W : MorphismProperty C` is stable under transfinite compositions
of shape `J` if for any well-order-continuous functor `F : J ⥤ C` such that
`F.obj j ⟶ F.obj (Order.succ j)` is in `W`, then `F.obj ⊥ ⟶ c.pt` is in `W`
for any colimit cocone `c : Cocone F`. -/
@[mk_iff]
/--
Definition of `IsStableUnderTransfiniteCompositionOfShape` / `IsStableUnderTransfiniteCompositionOfShape` 的定义

English:
class IsStableUnderTransfiniteCompositionOfShape
  parameters: : Prop where
  axioms and operations (1):
    - le : W.transfiniteCompositionsOfShape J <= W

中文:
类 是StableUnderTransfiniteCompositionOfShape
  参数: : 命题 where
  公理与运算 (1 个):
    - le : W.transfiniteCompositionsOfShape J <= W
-/
class IsStableUnderTransfiniteCompositionOfShape : Prop where
  le : W.transfiniteCompositionsOfShape J <= W

/--
lemma `transfiniteCompositionsOfShape_le` / 引理 `transfiniteCompositionsOfShape_le`

English:
lemma transfiniteCompositionsOfShape_le
  proof: IsStableUnderTransfiniteCompositionOfShape.le

中文:
引理 transfiniteCompositionsOfShape_le
  证明: IsStableUnderTransfiniteCompositionOfShape.le

Depends on / 依赖: IsStableUnderTransfiniteCompositionOfShape, IsStableUnderTransfiniteCompositionOfShape.le, WithBotTop, WithBotTop.rec, all_goals, infer_instance
-/
lemma transfiniteCompositionsOfShape_le
    [W.IsStableUnderTransfiniteCompositionOfShape J] :
    W.transfiniteCompositionsOfShape J <= W :=
  IsStableUnderTransfiniteCompositionOfShape.le

variable {J} in
/--
lemma `isStableUnderTransfiniteCompositionOfShape_iff_of_orderIso` / 引理 `isStableUnderTransfiniteCompositionOfShape_iff_of_orderIso`

English:
lemma isStableUnderTransfiniteCompositionOfShape_iff_of_orderIso
  given: (e : J ≃o J')
  proof: by
  simp only [isStableUnderTransfiniteCompositionOfShape_iff,
    W.transfiniteCompositionsOfShape_eq_of_orderIso e]

中文:
引理 isStableUnderTransfiniteCompositionOfShape_iff_of_orderIso
  条件: (e : J ≃o J')
  证明: by
  simp only [isStableUnderTransfiniteCompositionOfShape_iff,
    W.transfiniteCompositionsOfShape_eq_of_orderIso e]

Depends on / 依赖: W.transfiniteCompositionsOfShape_eq_of_orderIso, isStableUnderTransfiniteCompositionOfShape_iff, transfiniteCompositionsOfShape_eq_of_orderIso
-/
lemma isStableUnderTransfiniteCompositionOfShape_iff_of_orderIso (e : J ≃o J') :
    W.IsStableUnderTransfiniteCompositionOfShape J ↔
      W.IsStableUnderTransfiniteCompositionOfShape J' := by
  simp only [isStableUnderTransfiniteCompositionOfShape_iff,
    W.transfiniteCompositionsOfShape_eq_of_orderIso e]

end

section

variable (J : Type w) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]

namespace IsStableUnderTransfiniteCompositionOfShape.of_isStableUnderColimitsOfShape

variable {W J} {X Y : C} {f : X ⟶ Y} (hf : W.TransfiniteCompositionOfShape J f)
  [W.IsMultiplicative]
  (hJ : forall (J : Type w) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J],
    W.IsStableUnderColimitsOfShape J)

attribute [local instance] IsCofiltered.isConnected

include hJ in
/--
lemma `mem_map_bot_le` / 引理 `mem_map_bot_le`

English:
lemma mem_map_bot_le
  given: {j : J} (g : ⊥ ⟶ j)
  statement: W (hf.F.map g)
  proof: by
  obtain rfl : g = homOfLE bot_le := rfl
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    obtain rfl := hj.eq_bot
    simpa using W.id_mem _
  | succ j hj hj' =>
    rw [← homOfLE_comp bot_le (Order.le_succ j)]; rw [hf.F.map_comp]
    exact W.comp_mem _ _ hj' (hf.map_mem j hj)


中文:
引理 mem_map_bot_le
  条件: {j : J} (g : ⊥ ⟶ j)
  结论: W (hf.F.map g)
  证明: by
  obtain rfl : g = homOfLE bot_le := rfl
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    obtain rfl := hj.eq_bot
    simpa using W.id_mem _
  | succ j hj hj' =>
    rw [← homOfLE_comp bot_le (Order.le_succ j)]; rw [hf.F.map_comp]
    exact W.comp_mem _ _ hj' (hf.map_mem j hj)


Depends on / 依赖: IsSuccLimit, MorphismProperty, MorphismProperty.colimitsOfShape_le, Order.IsSuccLimit.bot_lt, Order.le_succ, OrderBot, Set.Iio, SuccOrder, SuccOrder.limitRecOn, W.comp_mem, W.id_mem, bot_le, bot_lt, colimitsOfShape_le, comp_mem, eq_bot, hf.F.isColimitOfIsWellOrderContinuous, hf.F.map_comp, hf.map_mem, hj.eq_bot
-/
lemma mem_map_bot_le {j : J} (g : ⊥ ⟶ j) : W (hf.F.map g) := by
  obtain rfl : g = homOfLE bot_le := rfl
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    obtain rfl := hj.eq_bot
    simpa using W.id_mem _
  | succ j hj hj' =>
    rw [← homOfLE_comp bot_le (Order.le_succ j)]; rw [hf.F.map_comp]
    exact W.comp_mem _ _ hj' (hf.map_mem j hj)
  | isSuccLimit j hj hj' =>
    let : OrderBot (Set.Iio j) :=
      { bot := ⟨⊥, Order.IsSuccLimit.bot_lt hj⟩
        bot_le j := bot_le }
    exact MorphismProperty.colimitsOfShape_le _
      (.of_isColimit (hf.F.isColimitOfIsWellOrderContinuous j hj) (fun k => hj' _ k.2))

set_option backward.isDefEq.respectTransparency false in
include hf hJ in
/--
lemma `mem` / 引理 `mem`

English:
lemma mem
  given: [W.RespectsIso]
  statement: W f
  proof: (MorphismProperty.arrow_mk_iso_iff _ (Arrow.isoMk hf.isoBot.symm (Iso.refl _))).2
    (MorphismProperty.colimitsOfShape_le _
      (.of_isColimit hf.isColimit (fun j => mem_map_bot_le _ hJ _)))

中文:
引理 mem
  条件: [W.RespectsIso]
  结论: W f
  证明: (MorphismProperty.arrow_mk_iso_iff _ (Arrow.isoMk hf.isoBot.symm (Iso.refl _))).2
    (MorphismProperty.colimitsOfShape_le _
      (.of_isColimit hf.isColimit (fun j => mem_map_bot_le _ hJ _)))

Depends on / 依赖: Arrow.isoMk, Iso.refl, MorphismProperty, MorphismProperty.arrow_mk_iso_iff, MorphismProperty.colimitsOfShape_le, arrow_mk_iso_iff, colimitsOfShape_le, hf.isColimit, hf.isoBot.symm, isColimit, isoBot, mem_map_bot_le, of_isColimit
-/
lemma mem [W.RespectsIso] : W f :=
  (MorphismProperty.arrow_mk_iso_iff _ (Arrow.isoMk hf.isoBot.symm (Iso.refl _))).2
    (MorphismProperty.colimitsOfShape_le _
      (.of_isColimit hf.isColimit (fun j => mem_map_bot_le _ hJ _)))

end IsStableUnderTransfiniteCompositionOfShape.of_isStableUnderColimitsOfShape

variable {W J} in
open IsStableUnderTransfiniteCompositionOfShape.of_isStableUnderColimitsOfShape in
/--
lemma `IsStableUnderTransfiniteCompositionOfShape.of_isStableUnderColimitsOfShape` / 引理 `IsStableUnderTransfiniteCompositionOfShape.of_isStableUnderColimitsOfShape`

English:
lemma IsStableUnderTransfiniteCompositionOfShape.of_isStableUnderColimitsOfShape

中文:
引理 是StableUnderTransfiniteCompositionOfShape.of_isStableUnderColimitsOfShape
-/
lemma IsStableUnderTransfiniteCompositionOfShape.of_isStableUnderColimitsOfShape
    [W.IsMultiplicative] [W.RespectsIso]
    (hJ : forall (J : Type w) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J],
      W.IsStableUnderColimitsOfShape J) :
    W.IsStableUnderTransfiniteCompositionOfShape J where
  le _ _ _ | ⟨hf⟩ => mem hf hJ

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [W.IsMultiplicative]
  signature: [W.RespectsIso]
  body: .of_isStableUnderColimitsOfShape (fun _ _ _ _ _ => by infer_instance)

中文:
实例 [W.是Multiplicative]
  签名: [W.RespectsIso]
  定义体: .of_isStableUnderColimitsOfShape (fun _ _ _ _ _ => by infer_instance)

Depends on / 依赖: WithBotTop, WithBotTop.rec, all_goals, infer_instance, of_isStableUnderColimitsOfShape
-/
instance [W.IsMultiplicative] [W.RespectsIso]
    [MorphismProperty.IsStableUnderFilteredColimits.{w, w} W] :
    W.IsStableUnderTransfiniteCompositionOfShape J :=
  .of_isStableUnderColimitsOfShape (fun _ _ _ _ _ => by infer_instance)

end

/--
Definition of `IsStableUnderInfiniteComposition` / `IsStableUnderInfiniteComposition` 的定义

English:
abbreviation IsStableUnderInfiniteComposition
  signature: : Prop
  body: W.IsStableUnderTransfiniteCompositionOfShape Nat

中文:
缩写 IsStableUnderInfiniteComposition
  签名: : 命题
  定义体: W.IsStableUnderTransfiniteCompositionOfShape Nat

Depends on / 依赖: IsStableUnderTransfiniteCompositionOfShape, W.IsStableUnderTransfiniteCompositionOfShape
-/
abbrev IsStableUnderInfiniteComposition : Prop :=
  W.IsStableUnderTransfiniteCompositionOfShape Nat

/--
Definition of `IsStableUnderTransfiniteComposition` / `IsStableUnderTransfiniteComposition` 的定义

English:
class IsStableUnderTransfiniteComposition
  parameters: : Prop where
  axioms and operations (1):
    - isStableUnderTransfiniteCompositionOfShape((J : Type w) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]) : W.IsStableUnderTransfiniteCompositionOfShape J  [default: by infer_instance]

中文:
类 是StableUnderTransfiniteComposition
  参数: : 命题 where
  公理与运算 (1 个):
    - isStableUnderTransfiniteCompositionOfShape((J : 类型 w) [线性序 J] [Succ序 J] [有底序 J] [WellFoundedLT J]) : W.是StableUnderTransfiniteCompositionOfShape J  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class IsStableUnderTransfiniteComposition : Prop where
  isStableUnderTransfiniteCompositionOfShape
    (J : Type w) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J] :
    W.IsStableUnderTransfiniteCompositionOfShape J := by infer_instance

namespace IsStableUnderTransfiniteComposition

attribute [instance] isStableUnderTransfiniteCompositionOfShape

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [W.IsMultiplicative]
  signature: [W.RespectsIso]
  body: inferInstance

中文:
实例 [W.是Multiplicative]
  签名: [W.RespectsIso]
  定义体: inferInstance
-/
instance [W.IsMultiplicative] [W.RespectsIso]
    [MorphismProperty.IsStableUnderFilteredColimits.{w, w} W] :
    IsStableUnderTransfiniteComposition.{w} W where

example : (isomorphisms C).IsStableUnderTransfiniteComposition := inferInstance

variable [IsStableUnderTransfiniteComposition.{w'} W]

/--
lemma `shrink` / 引理 `shrink`

English:
lemma shrink
  given: [UnivLE.{w, w'}]
  proof: by
    rw [isStableUnderTransfiniteCompositionOfShape_iff_of_orderIso W
      (orderIsoShrink.{w'} J)]
    infer_instance

中文:
引理 shrink
  条件: [UnivLE.{w, w'}]
  证明: by
    rw [isStableUnderTransfiniteCompositionOfShape_iff_of_orderIso W
      (orderIsoShrink.{w'} J)]
    infer_instance

Depends on / 依赖: infer_instance, isStableUnderTransfiniteCompositionOfShape_iff_of_orderIso, orderIsoShrink
-/
lemma shrink [UnivLE.{w, w'}] :
    IsStableUnderTransfiniteComposition.{w} W where
  isStableUnderTransfiniteCompositionOfShape J _ _ _ _ := by
    rw [isStableUnderTransfiniteCompositionOfShape_iff_of_orderIso W
      (orderIsoShrink.{w'} J)]
    infer_instance

/--
lemma `shrink₀` / 引理 `shrink₀`

English:
lemma shrink₀
  statement: IsStableUnderTransfiniteComposition.{0} W
  proof: shrink.{0, w'} W

中文:
引理 shrink₀
  结论: 是StableUnderTransfiniteComposition.{0} W
  证明: shrink.{0, w'} W

Depends on / 依赖: shrink
-/
lemma shrink₀ : IsStableUnderTransfiniteComposition.{0} W := shrink.{0, w'} W

attribute [local instance] shrink₀

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: W.IsMultiplicative
  body: transfiniteCompositionsOfShape_le _ _ _
      (TransfiniteCompositionOfShape.id W X).mem
  comp_mem f g hf hg :=
    transfiniteCompositionsOfShape_le _ _ _
      (TransfiniteCompositionOfShape.ofComp f g hf hg).mem

中文:
实例 :
  签名: W.是Multiplicative
  定义体: transfiniteCompositionsOfShape_le _ _ _
      (TransfiniteCompositionOfShape.id W X).mem
  comp_mem f g hf hg :=
    transfiniteCompositionsOfShape_le _ _ _
      (TransfiniteCompositionOfShape.ofComp f g hf hg).mem

Depends on / 依赖: TransfiniteCompositionOfShape, TransfiniteCompositionOfShape.id, TransfiniteCompositionOfShape.ofComp, comp_mem, ofComp, transfiniteCompositionsOfShape_le
-/
instance : W.IsMultiplicative where
  id_mem X :=
    transfiniteCompositionsOfShape_le _ _ _
      (TransfiniteCompositionOfShape.id W X).mem
  comp_mem f g hf hg :=
    transfiniteCompositionsOfShape_le _ _ _
      (TransfiniteCompositionOfShape.ofComp f g hf hg).mem

end IsStableUnderTransfiniteComposition

/-- The class of transfinite compositions (for arbitrary well-ordered types `J : Type w`)
of a class of morphisms `W`. -/
@[pp_with_univ]
/--
Definition of `transfiniteCompositions` / `transfiniteCompositions` 的定义

English:
definition transfiniteCompositions
  signature: : MorphismProperty C
  body: ⨆ (J : Type w) (_ : LinearOrder J) (_ : SuccOrder J) (_ : OrderBot J)
    (_ : WellFoundedLT J), W.transfiniteCompositionsOfShape J

中文:
定义 transfiniteCompositions
  签名: : MorphismProperty C
  定义体: ⨆ (J : Type w) (_ : LinearOrder J) (_ : SuccOrder J) (_ : OrderBot J)
    (_ : WellFoundedLT J), W.transfiniteCompositionsOfShape J

Depends on / 依赖: LinearOrder, OrderBot, SuccOrder, W.transfiniteCompositionsOfShape, WellFoundedLT, transfiniteCompositionsOfShape
-/
def transfiniteCompositions : MorphismProperty C :=
  ⨆ (J : Type w) (_ : LinearOrder J) (_ : SuccOrder J) (_ : OrderBot J)
    (_ : WellFoundedLT J), W.transfiniteCompositionsOfShape J

/--
lemma `transfiniteCompositions_iff` / 引理 `transfiniteCompositions_iff`

English:
lemma transfiniteCompositions_iff
  given: {X Y : C} (f : X ⟶ Y)
  proof: by
  simp only [transfiniteCompositions, iSup_iff]

中文:
引理 transfiniteCompositions_iff
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by
  simp only [transfiniteCompositions, iSup_iff]

Depends on / 依赖: iSup_iff, transfiniteCompositions
-/
lemma transfiniteCompositions_iff {X Y : C} (f : X ⟶ Y) :
    transfiniteCompositions.{w} W f ↔
      exists (J : Type w) (_ : LinearOrder J) (_ : SuccOrder J) (_ : OrderBot J)
        (_ : WellFoundedLT J), W.transfiniteCompositionsOfShape J f := by
  simp only [transfiniteCompositions, iSup_iff]

/--
lemma `transfiniteCompositionsOfShape_le_transfiniteCompositions` / 引理 `transfiniteCompositionsOfShape_le_transfiniteCompositions`

English:
lemma transfiniteCompositionsOfShape_le_transfiniteCompositions
  proof: by
  intro A B f hf
  rw [transfiniteCompositions_iff]
  exact ⟨_, _, _, _, _, hf⟩

中文:
引理 transfiniteCompositionsOfShape_le_transfiniteCompositions
  证明: by
  intro A B f hf
  rw [transfiniteCompositions_iff]
  exact ⟨_, _, _, _, _, hf⟩

Depends on / 依赖: transfiniteCompositions_iff
-/
lemma transfiniteCompositionsOfShape_le_transfiniteCompositions
    (J : Type w) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J] :
    W.transfiniteCompositionsOfShape J <= transfiniteCompositions.{w} W := by
  intro A B f hf
  rw [transfiniteCompositions_iff]
  exact ⟨_, _, _, _, _, hf⟩

/--
lemma `transfiniteCompositions_monotone` / 引理 `transfiniteCompositions_monotone`

English:
lemma transfiniteCompositions_monotone
  proof: by
  intro W₁ W₂ h X Y f hf
  rw [transfiniteCompositions_iff] at hf
  obtain ⟨J, _, _, _, _, hf⟩ := hf
  exact transfiniteCompositionsOfShape_le_transfiniteCompositions _ _ _
    (transfiniteCompositionsOfShape_monotone J h _ hf)

中文:
引理 transfiniteCompositions_monotone
  证明: by
  intro W₁ W₂ h X Y f hf
  rw [transfiniteCompositions_iff] at hf
  obtain ⟨J, _, _, _, _, hf⟩ := hf
  exact transfiniteCompositionsOfShape_le_transfiniteCompositions _ _ _
    (transfiniteCompositionsOfShape_monotone J h _ hf)

Depends on / 依赖: transfiniteCompositionsOfShape_le_transfiniteCompositions, transfiniteCompositionsOfShape_monotone, transfiniteCompositions_iff
-/
lemma transfiniteCompositions_monotone :
    Monotone (transfiniteCompositions.{w} (C := C)) := by
  intro W₁ W₂ h X Y f hf
  rw [transfiniteCompositions_iff] at hf
  obtain ⟨J, _, _, _, _, hf⟩ := hf
  exact transfiniteCompositionsOfShape_le_transfiniteCompositions _ _ _
    (transfiniteCompositionsOfShape_monotone J h _ hf)

/--
lemma `le_transfiniteCompositions` / 引理 `le_transfiniteCompositions`

English:
lemma le_transfiniteCompositions
  proof: le_trans (fun _ _ _ hf =>
    (MorphismProperty.TransfiniteCompositionOfShape.ofOrderIso (.ofMem _ hf)
      (orderIsoShrink.{w} (Fin 2)).symm).mem)
    (transfiniteCompositionsOfShape_le_transfiniteCompositions _ _)

中文:
引理 le_transfiniteCompositions
  证明: le_trans (fun _ _ _ hf =>
    (MorphismProperty.TransfiniteCompositionOfShape.ofOrderIso (.ofMem _ hf)
      (orderIsoShrink.{w} (Fin 2)).symm).mem)
    (transfiniteCompositionsOfShape_le_transfiniteCompositions _ _)

Depends on / 依赖: MorphismProperty, MorphismProperty.TransfiniteCompositionOfShape.ofOrderIso, TransfiniteCompositionOfShape, le_trans, ofOrderIso, orderIsoShrink, transfiniteCompositionsOfShape_le_transfiniteCompositions
-/
lemma le_transfiniteCompositions :
    W <= transfiniteCompositions.{w} W :=
  le_trans (fun _ _ _ hf =>
    (MorphismProperty.TransfiniteCompositionOfShape.ofOrderIso (.ofMem _ hf)
      (orderIsoShrink.{w} (Fin 2)).symm).mem)
    (transfiniteCompositionsOfShape_le_transfiniteCompositions _ _)

/--
lemma `transfiniteCompositions_le` / 引理 `transfiniteCompositions_le`

English:
lemma transfiniteCompositions_le
  given: [IsStableUnderTransfiniteComposition.{w} W]
  proof: by
  intro _ _ f hf
  rw [transfiniteCompositions_iff] at hf
  obtain ⟨J, _, _, _, _, hf⟩ := hf
  exact W.transfiniteCompositionsOfShape_le J _ hf

@[simp]

中文:
引理 transfiniteCompositions_le
  条件: [是StableUnderTransfiniteComposition.{w} W]
  证明: by
  intro _ _ f hf
  rw [transfiniteCompositions_iff] at hf
  obtain ⟨J, _, _, _, _, hf⟩ := hf
  exact W.transfiniteCompositionsOfShape_le J _ hf

@[simp]

Depends on / 依赖: W.transfiniteCompositionsOfShape_le, transfiniteCompositionsOfShape_le, transfiniteCompositions_iff
-/
lemma transfiniteCompositions_le [IsStableUnderTransfiniteComposition.{w} W] :
    transfiniteCompositions.{w} W <= W := by
  intro _ _ f hf
  rw [transfiniteCompositions_iff] at hf
  obtain ⟨J, _, _, _, _, hf⟩ := hf
  exact W.transfiniteCompositionsOfShape_le J _ hf

@[simp]
/--
lemma `transfiniteCompositions_le_iff` / 引理 `transfiniteCompositions_le_iff`

English:
lemma transfiniteCompositions_le_iff
  statement: {P Q : MorphismProperty C}
  proof: by
  constructor
  · exact (le_transfiniteCompositions P).trans
  · intro h
    exact (transfiniteCompositions_monotone.{w} h).trans Q.transfiniteCompositions_le

中文:
引理 transfiniteCompositions_le_iff
  结论: {P Q : MorphismProperty C}
  证明: by
  constructor
  · exact (le_transfiniteCompositions P).trans
  · intro h
    exact (transfiniteCompositions_monotone.{w} h).trans Q.transfiniteCompositions_le

Depends on / 依赖: Q.transfiniteCompositions_le, le_transfiniteCompositions, transfiniteCompositions_le, transfiniteCompositions_monotone
-/
lemma transfiniteCompositions_le_iff {P Q : MorphismProperty C}
    [IsStableUnderTransfiniteComposition.{w} Q] :
    transfiniteCompositions.{w} P <= Q ↔ P <= Q := by
  constructor
  · exact (le_transfiniteCompositions P).trans
  · intro h
    exact (transfiniteCompositions_monotone.{w} h).trans Q.transfiniteCompositions_le

namespace TransfiniteCompositionOfShape

variable {W} {J : Type w} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]

section

variable [IsStableUnderTransfiniteComposition.{w} W]
  {X Y : C} {f : X ⟶ Y} (h : W.TransfiniteCompositionOfShape J f)

/--
lemma `mem_map` / 引理 `mem_map`

English:
lemma mem_map
  given: {i j : J} (φ : i ⟶ j)
  proof: W.transfiniteCompositionsOfShape_le _ _ ((h.iic j).ici ⟨i, leOfHom φ⟩).mem

中文:
引理 mem_map
  条件: {i j : J} (φ : i ⟶ j)
  证明: W.transfiniteCompositionsOfShape_le _ _ ((h.iic j).ici ⟨i, leOfHom φ⟩).mem

Depends on / 依赖: W.transfiniteCompositionsOfShape_le, h.iic, leOfHom, transfiniteCompositionsOfShape_le
-/
lemma mem_map {i j : J} (φ : i ⟶ j) :
    W (h.F.map φ) :=
  W.transfiniteCompositionsOfShape_le _ _ ((h.iic j).ici ⟨i, leOfHom φ⟩).mem

/--
lemma `mem_incl_app` / 引理 `mem_incl_app`

English:
lemma mem_incl_app
  given: (j : J)
  proof: W.transfiniteCompositionsOfShape_le _ _ (h.ici j).mem

中文:
引理 mem_incl_app
  条件: (j : J)
  证明: W.transfiniteCompositionsOfShape_le _ _ (h.ici j).mem

Depends on / 依赖: W.transfiniteCompositionsOfShape_le, h.ici, transfiniteCompositionsOfShape_le
-/
lemma mem_incl_app (j : J) :
    W (h.incl.app j) :=
  W.transfiniteCompositionsOfShape_le _ _ (h.ici j).mem

end

section isomorphisms

example : (isomorphisms C).IsStableUnderTransfiniteCompositionOfShape J := inferInstance

variable {X Y : C} {f : X ⟶ Y} (h : (isomorphisms C).TransfiniteCompositionOfShape J f)

include h in
/--
lemma `isIso` / 引理 `isIso`

English:
lemma isIso
  statement: IsIso f
  proof: (isomorphisms C).transfiniteCompositionsOfShape_le _ _ h.mem

中文:
引理 isIso
  结论: 是同构 f
  证明: (isomorphisms C).transfiniteCompositionsOfShape_le _ _ h.mem

Depends on / 依赖: WithBotTop, WithBotTop.rec, h.mem, infer_instance, isLE_of_isZero, isomorphisms, transfiniteCompositionsOfShape_le
-/
lemma isIso : IsIso f :=
  (isomorphisms C).transfiniteCompositionsOfShape_le _ _ h.mem

instance {i j : J} (f : i ⟶ j) : IsIso (h.F.map f) := h.mem_map f

instance (j : J) : IsIso (h.incl.app j) := h.mem_incl_app j

end isomorphisms

end TransfiniteCompositionOfShape

end MorphismProperty

end CategoryTheory
