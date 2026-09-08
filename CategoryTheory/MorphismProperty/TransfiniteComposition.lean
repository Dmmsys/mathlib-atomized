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

/-- Structure expressing that a morphism `f : X ⟶ Y` in a category `C`
is a transfinite composition of shape `J` of morphisms in `W : MorphismProperty C`. -/
/-
**CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape** 是 Mathlib 中的一个
归纳类型，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     CategoryT
heory.MorphismProperty C →       (J : Type w) →         [inst_1 : LinearOrder J]
 →           [SuccOrder J] → [OrderBot J] → [WellFoundedLT J] → {X Y : C} → (X ⟶
 Y) → Type (max (max u v) w)
参数：J : Type w；X ⟶ Y；max (max u v) w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Structure expressing that a morphism `f : X ⟶ Y` in a category `C`
is a transfinite composition of shape `J` of morphisms in `W : MorphismProperty 
C`.
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
/-
**CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape.ofArrowIso** 是 M
athlib 中的一个定义，位于命名空间 `CategoryTheory.MorphismProperty.TransfiniteCompositionOfSh
ape`。
形式化陈述：ofArrowIso {X' Y' : C} {f' : X' ⟶ Y'} (e : Arrow.mk f ≅ Arrow.mk f') : W.T
ransfiniteCompositionOfShape J f' where __
参数：e : Arrow.mk f ≅ Arrow.mk f'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape.map_mem`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W : CategoryTheory.Morp
hismProperty C} {J : Type w}   [inst_1 : LinearOrder J] [in…

--- 原说明 ---
If `f` and `f'` are two isomorphic morphisms and `f` is a transfinite compositio
n
of morphisms in `W : MorphismProperty C`, then so is `f'`.
-/
def ofArrowIso {X' Y' : C}
    {f' : X' ⟶ Y'} (e : Arrow.mk f ≅ Arrow.mk f') :
    W.TransfiniteCompositionOfShape J f' where
  __ := h.toTransfiniteCompositionOfShape.ofArrowIso e
  map_mem := h.map_mem

/-- If `W ≤ W'`, then transfinite compositions of shape `J` of morphisms in `W`
are also transfinite composition of shape `J` of morphisms in `W'`. -/
@[simps toTransfiniteCompositionOfShape]
/-
**CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape.ofLE** 是 Mathlib
 中的一个定义，位于命名空间 `CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape`。
形式化陈述：ofLE {W' : MorphismProperty C} (hW : W <= W') : W'.TransfiniteCompositionO
fShape J f where __
参数：hW : W <= W'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `W ≤ W'`, then transfinite compositions of shape `J` of morphisms in `W`
are also transfinite composition of shape `J` of morphisms in `W'`.
-/
def ofLE {W' : MorphismProperty C} (hW : W ≤ W') :
    W'.TransfiniteCompositionOfShape J f where
  __ := h.toTransfiniteCompositionOfShape
  map_mem j hj := hW _ (h.map_mem j hj)

/-- If `f` is a transfinite composition of shape `J` of morphisms in `W`,
then it is also a transfinite composition of shape `J'` of morphisms in `W` if `J' ≃o J`. -/
/-
**CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape.ofOrderIso** 是 M
athlib 中的一个定义，位于命名空间 `CategoryTheory.MorphismProperty.TransfiniteCompositionOfSh
ape`。
形式化陈述：ofOrderIso {J' : Type w'} [LinearOrder J'] [OrderBot J'] [SuccOrder J'] [W
ellFoundedLT J'] (e : J' ≃o J) : W.TransfiniteCompositionOfShape J' f where __
参数：e : J' ≃o J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is a transfinite composition of shape `J` of morphisms in `W`,
then it is also a transfinite composition of shape `J'` of morphisms in `W` if `
J' ≃o J`.
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
/-
**CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape.map** 是 Mathlib 
中的一个定义，位于命名空间 `CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape`。
形式化陈述：map {W : MorphismProperty D} {F : C ⥤ D} [PreservesWellOrderContinuousOfSh
ape J F] [PreservesColimitsOfShape J F] (h : (W.inverseImage F).TransfiniteCompo
sitionOfShape J f) : W.TransfiniteCompositionOfShape J (F.map f) where __
参数：h : (W.inverseImage F).TransfiniteCompositionOfShape J f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is a transfinite composition of shape `J` of morphisms
in `W.inverseImage F`, then `F` is a transfinite composition of shape `J`
of morphisms in `W` provided `F` preserves suitable colimits.
-/
noncomputable def map {W : MorphismProperty D} {F : C ⥤ D}
    [PreservesWellOrderContinuousOfShape J F]
    [PreservesColimitsOfShape J F]
    (h : (W.inverseImage F).TransfiniteCompositionOfShape J f) :
    W.TransfiniteCompositionOfShape J (F.map f) where
  __ := h.toTransfiniteCompositionOfShape.map F
  map_mem j hj := h.map_mem j hj

/-- A transfinite composition of shape `J` of morphisms in `W` induces a transfinite
composition of shape `Set.Iic j` (for any `j : J`). -/
/-
**CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape.iic** 是 Mathlib 
中的一个定义，位于命名空间 `CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape`。
形式化陈述：iic (j : J) : W.TransfiniteCompositionOfShape (Set.Iic j) (h.F.map (homOfL
E bot_le : ⊥ ⟶ j)) where __
参数：j : J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A transfinite composition of shape `J` of morphisms in `W` induces a transfinite
composition of shape `Set.Iic j` (for any `j : J`).
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

/-- A transfinite composition of shape `J` of morphisms in `W` induces a transfinite
composition of shape `Set.Ici j` (for any `j : J`). -/
/-
**CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape.ici** 是 Mathlib 
中的一个定义，位于命名空间 `CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape`。
形式化陈述：ici (j : J) : W.TransfiniteCompositionOfShape (Set.Ici j) (h.incl.app j) w
here __
参数：j : J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A transfinite composition of shape `J` of morphisms in `W` induces a transfinite
composition of shape `Set.Ici j` (for any `j : J`).
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
/-
**CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape.ofComposableArro
ws** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.MorphismProperty.TransfiniteComposi
tionOfShape`。
形式化陈述：ofComposableArrows {n : Nat} (F : ComposableArrows C n) (hF : forall (i : 
Fin n), W (F.map (homOfLE i.castSucc_le_succ))) : W.TransfiniteCompositionOfShap
e (Fin (n + 1)) F.hom where toTransfiniteCompositionOfShape
参数：F : ComposableArrows C n；hF : forall (i : Fin n), W (F.map (homOfLE i.castSuc
c_le_succ))。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.castSucc_le_succ`：castSucc_le_succ {n} (i : Fin n) : i.castSucc <= i
.succ

--- 原说明 ---
If `F : ComposableArrows C n` and all maps `F.obj i.castSucc ⟶ F.obj i.succ`
are in `W`, then `F.hom : F.left ⟶ F.right` is a transfinite composition of
shape `Fin (n + 1)` of morphisms in `W`.
-/
def ofComposableArrows {n : ℕ} (F : ComposableArrows C n)
    (hF : ∀ (i : Fin n), W (F.map (homOfLE i.castSucc_le_succ))) :
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

/-- The identity of any object is a transfinite composition of shape `Fin 1`. -/
/-
**CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape.id** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape`。
形式化陈述：id (X : C) : W.TransfiniteCompositionOfShape (Fin 1) (𝟙 X)
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity of any object is a transfinite composition of shape `Fin 1`.
-/
def id (X : C) : W.TransfiniteCompositionOfShape (Fin 1) (𝟙 X) :=
  ofComposableArrows W (.mk₀ X) (by simp)

variable {W}

/-- If `f : X ⟶ Y` satisfies `W f`, then `f` is a transfinite composition of shape `Fin 2`
of morphisms in `W`. -/
/-
**CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape.ofMem** 是 Mathli
b 中的一个定义，位于命名空间 `CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape`。
形式化陈述：ofMem {X Y : C} (f : X ⟶ Y) (hf : W f) : W.TransfiniteCompositionOfShape (
Fin 2) f
参数：f : X ⟶ Y；hf : W f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : X ⟶ Y` satisfies `W f`, then `f` is a transfinite composition of shape `
Fin 2`
of morphisms in `W`.
-/
def ofMem {X Y : C} (f : X ⟶ Y) (hf : W f) :
    W.TransfiniteCompositionOfShape (Fin 2) f :=
  ofComposableArrows W (.mk₁ f) (fun i ↦ by fin_cases i; assumption)

/-- If `f : X ⟶ Y` and `g : Y ⟶ Z` satisfy `W f` and `W g`, then `f ≫ g` is a
transfinite composition of shape `Fin 3` of morphisms in `W`. -/
/-
**CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape.ofComp** 是 Mathl
ib 中的一个定义，位于命名空间 `CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape`
。
形式化陈述：ofComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) (hg : W g) : W.Trans
finiteCompositionOfShape (Fin 3) (f ≫ g)
参数：f : X ⟶ Y；g : Y ⟶ Z；hf : W f；hg : W g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : X ⟶ Y` and `g : Y ⟶ Z` satisfy `W f` and `W g`, then `f ≫ g` is a
transfinite composition of shape `Fin 3` of morphisms in `W`.
-/
def ofComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) (hg : W g) :
    W.TransfiniteCompositionOfShape (Fin 3) (f ≫ g) :=
  ofComposableArrows W (.mk₂ f g) (fun i ↦ by fin_cases i <;> assumption)

end TransfiniteCompositionOfShape

/-- Given `W : MorphismProperty C` and a well-ordered type `J`, this is
the class of morphisms that are transfinite composition of shape `J`
of morphisms in `W`. -/
/-
**CategoryTheory.MorphismProperty.transfiniteCompositionsOfShape** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：transfiniteCompositionsOfShape : MorphismProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `W : MorphismProperty C` and a well-ordered type `J`, this is
the class of morphisms that are transfinite composition of shape `J`
of morphisms in `W`.
-/
def transfiniteCompositionsOfShape : MorphismProperty C :=
  fun _ _ f ↦ Nonempty (W.TransfiniteCompositionOfShape J f)
/-
**CategoryTheory.MorphismProperty.transfiniteCompositionsOfShape_monotone** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：transfiniteCompositionsOfShape_monotone : Monotone (transfiniteComposition
sOfShape (C
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma transfiniteCompositionsOfShape_monotone :
    Monotone (transfiniteCompositionsOfShape (C := C) (J := J)) := by
  rintro _ _ h _ _ _ ⟨t⟩
  exact ⟨t.ofLE h⟩

variable {J} in
/-
**CategoryTheory.MorphismProperty.transfiniteCompositionsOfShape_eq_of_orderIso*
* 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：transfiniteCompositionsOfShape_eq_of_orderIso (e : J ≃o J') : W.transfinit
eCompositionsOfShape J = W.transfiniteCompositionsOfShape J'
参数：e : J ≃o J'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
-/
lemma transfiniteCompositionsOfShape_eq_of_orderIso (e : J ≃o J') :
    W.transfiniteCompositionsOfShape J =
      W.transfiniteCompositionsOfShape J' := by
  ext _ _ f
  exact ⟨fun ⟨h⟩ ↦ ⟨h.ofOrderIso e.symm⟩, fun ⟨h⟩ ↦ ⟨h.ofOrderIso e⟩⟩
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : RespectsIso (W.transfiniteCompositionsOfShape J) :=
  RespectsIso.of_respects_arrow_iso _ (fun _ _ e ⟨h⟩ ↦ ⟨h.ofArrowIso e⟩)

variable {W J} in
/-
**CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape.mem** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W : CategoryTheo
ry.MorphismProperty C} {J : Type w}   [inst_1 : LinearOrder J] [inst_2 : SuccOrd
er J] [inst_3 : OrderBot J] [inst_4 : WellFoundedLT J] {X Y : C} (f : X ⟶ Y)   (
h : W.TransfiniteCompositionOfShape J f), W.transfiniteCompositionsOfShape J f
参数：f : X ⟶ Y；h : W.TransfiniteCompositionOfShape J f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma TransfiniteCompositionOfShape.mem {X Y : C} (f : X ⟶ Y)
    (h : W.TransfiniteCompositionOfShape J f) :
    W.transfiniteCompositionsOfShape J f := ⟨h⟩
/-
**CategoryTheory.MorphismProperty.transfiniteCompositionsOfShape_map_of_preserve
s** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：transfiniteCompositionsOfShape_map_of_preserves (G : C ⥤ D) [PreservesWell
OrderContinuousOfShape J G] {X Y : C} (f : X ⟶ Y) {P : MorphismProperty D} [Pres
ervesColimitsOfShape J G] (h : (P.inverseImage G).transfiniteCompositionsOfShape
 J f) : P.transfiniteCompositionsOfShape J (G.map f)
参数：G : C ⥤ D；f : X ⟶ Y；h : (P.inverseImage G).transfiniteCompositionsOfShape J f
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape.mem`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] {W : CategoryTheory.Morphism
Property C} {J : Type w}   [inst_1 : LinearOrder J] [in…
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
/-
**CategoryTheory.MorphismProperty.IsStableUnderTransfiniteCompositionOfShape** 是
 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     CategoryT
heory.MorphismProperty C →       (J : Type w) → [inst : LinearOrder J] → [SuccOr
der J] → [OrderBot J] → [WellFoundedLT J] → Prop
参数：J : Type w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A class of morphisms `W : MorphismProperty C` is stable under transfinite compos
itions
of shape `J` if for any well-order-continuous functor `F : J ⥤ C` such that
`F.obj j ⟶ F.obj (Order.succ j)` is in `W`, then `F.obj ⊥ ⟶ c.pt` is in `W`
for any colimit cocone `c : Cocone F`.
-/
class IsStableUnderTransfiniteCompositionOfShape : Prop where
  le : W.transfiniteCompositionsOfShape J ≤ W
/-
**CategoryTheory.MorphismProperty.transfiniteCompositionsOfShape_le** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：transfiniteCompositionsOfShape_le [W.IsStableUnderTransfiniteCompositionOf
Shape J] : W.transfiniteCompositionsOfShape J <= W
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderTransfiniteCompositionOfSha
pe.le`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryThe
ory.MorphismProperty C} {J : Type w}   {inst_1 : LinearOrder J} {in…
-/
lemma transfiniteCompositionsOfShape_le
    [W.IsStableUnderTransfiniteCompositionOfShape J] :
    W.transfiniteCompositionsOfShape J ≤ W :=
  IsStableUnderTransfiniteCompositionOfShape.le

variable {J} in
/-
**CategoryTheory.MorphismProperty.isStableUnderTransfiniteCompositionOfShape_iff
_of_orderIso** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：isStableUnderTransfiniteCompositionOfShape_iff_of_orderIso (e : J ≃o J') :
 W.IsStableUnderTransfiniteCompositionOfShape J ↔ W.IsStableUnderTransfiniteComp
ositionOfShape J'
参数：e : J ≃o J'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.MorphismProperty.transfiniteCompositionsOfShape_eq_of_ord
erIso`：transfiniteCompositionsOfShape_eq_of_orderIso (e : J ≃o J') : W.transfini
teCompositionsOfShape J = W.transfiniteCompositionsOfShape J'
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
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
  (hJ : ∀ (J : Type w) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J],
    W.IsStableUnderColimitsOfShape J)

attribute [local instance] IsCofiltered.isConnected

include hJ in
/-
**CategoryTheory.MorphismProperty.IsStableUnderTransfiniteCompositionOfShape.of_
isStableUnderColimitsOfShape.mem_map_bot_le** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.MorphismProperty.IsStableUnderTransfiniteCompositionOfShape.of_isStableUnd
erColimitsOfShape`。
形式化陈述：mem_map_bot_le {j : J} (g : ⊥ ⟶ j) : W (hf.F.map g)
参数：g : ⊥ ⟶ j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用引理 `CategoryTheory.MorphismProperty.id_mem`：id_mem (W : MorphismProperty C) 
[W.ContainsIdentities] (X : C) : W (𝟙 X)
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsMin.eq_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot 
α] {a : α}, IsMin a → a = ⊥
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `CategoryTheory.homOfLE_comp`：homOfLE_comp {x y z : X} (h : x <= y) (k : 
y <= z) : homOfLE h ≫ homOfLE k = homOfLE (h.trans k)
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape.map_mem`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W : CategoryTheory.Morp
hismProperty C} {J : Type w}   [inst_1 : LinearOrder J] [in…
· 使用定理 `Order.IsSuccLimit.bot_lt`：∀ {α : Type u_1} {a : α} [inst : Preorder α] [
inst_1 : OrderBot α], Order.IsSuccLimit a → ⊥ < a
· 使用引理 `CategoryTheory.MorphismProperty.colimitsOfShape_le`：colimitsOfShape_le [
W.IsStableUnderColimitsOfShape J] : W.colimitsOfShape J <= W
· 使用定理 `Set.ordConnected_Iio`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, (Set
.Iio a).OrdConnected
· 使用定理 `CategoryTheory.MorphismProperty.colimitsOfShape.of_isColimit`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {W : CategoryTheory.MorphismPrope
rty C} {J : Type u_2}   [inst_1 : Preorder J] [ins…
· 使用定理 `PrincipalSeg.monotone`：monotone [PartialOrder α] (f : α <i β) : Monotone
 f
· 使用定理 `CategoryTheory.TransfiniteCompositionOfShape.isWellOrderContinuous`：∀ {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type w} [inst_1 : Line
arOrder J] [inst_2 : OrderBot J]   {X Y : C} {f : X ⟶ Y}…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma mem_map_bot_le {j : J} (g : ⊥ ⟶ j) : W (hf.F.map g) := by
  obtain rfl : g = homOfLE bot_le := rfl
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    obtain rfl := hj.eq_bot
    simpa using W.id_mem _
  | succ j hj hj' =>
    rw [← homOfLE_comp bot_le (Order.le_succ j), hf.F.map_comp]
    exact W.comp_mem _ _ hj' (hf.map_mem j hj)
  | isSuccLimit j hj hj' =>
    let : OrderBot (Set.Iio j) :=
      { bot := ⟨⊥, Order.IsSuccLimit.bot_lt hj⟩
        bot_le j := bot_le }
    exact MorphismProperty.colimitsOfShape_le _
      (.of_isColimit (hf.F.isColimitOfIsWellOrderContinuous j hj) (fun k ↦ hj' _ k.2))

set_option backward.isDefEq.respectTransparency false in
include hf hJ in
/-
**CategoryTheory.MorphismProperty.IsStableUnderTransfiniteCompositionOfShape.of_
isStableUnderColimitsOfShape.mem** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Morph
ismProperty.IsStableUnderTransfiniteCompositionOfShape.of_isStableUnderColimitsO
fShape`。
形式化陈述：mem [W.RespectsIso] : W f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.TransfiniteCompositionOfShape.fac`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {J : Type w} [inst_1 : LinearOrder J] [inst_2
 : OrderBot J]   {X Y : C} {f : X ⟶ Y}…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.MorphismProperty.colimitsOfShape_le`：colimitsOfShape_le [
W.IsStableUnderColimitsOfShape J] : W.colimitsOfShape J <= W
· 使用定理 `CategoryTheory.MorphismProperty.colimitsOfShape.of_isColimit`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {W : CategoryTheory.MorphismPrope
rty C} {J : Type u_2}   [inst_1 : Preorder J] [ins…
· 使用引理 `CategoryTheory.MorphismProperty.IsStableUnderTransfiniteCompositionOfSha
pe.of_isStableUnderColimitsOfShape.mem_map_bot_le`：mem_map_bot_le {j : J} (g : ⊥
 ⟶ j) : W (hf.F.map g)
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
lemma mem [W.RespectsIso] : W f :=
  (MorphismProperty.arrow_mk_iso_iff _ (Arrow.isoMk hf.isoBot.symm (Iso.refl _))).2
    (MorphismProperty.colimitsOfShape_le _
      (.of_isColimit hf.isColimit (fun j ↦ mem_map_bot_le _ hJ _)))

end IsStableUnderTransfiniteCompositionOfShape.of_isStableUnderColimitsOfShape

variable {W J} in
open IsStableUnderTransfiniteCompositionOfShape.of_isStableUnderColimitsOfShape in
/-
**CategoryTheory.MorphismProperty.IsStableUnderTransfiniteCompositionOfShape.of_
isStableUnderColimitsOfShape** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MorphismP
roperty.IsStableUnderTransfiniteCompositionOfShape`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W : CategoryTheo
ry.MorphismProperty C} {J : Type w}   [inst_1 : LinearOrder J] [inst_2 : SuccOrd
er J] [inst_3 : OrderBot J] [inst_4 : WellFoundedLT J] [W.IsMultiplicative]   [W
.RespectsIso],   (∀ (J : Type w) [inst_7 : LinearOrder J] [SuccOrder J] [OrderBo
t J] [WellFoundedLT J],       W.IsStableUnderColimitsOfShape J) →     W.IsStable
UnderTransfiniteCompositionOfShape J
参数：∀ (J : Type w) [inst_7 : LinearOrder J] [SuccOrder J] [OrderBot J] [WellFound
edLT J],       W.IsStableUnderColimitsOfShape J。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.IsStableUnderTransfiniteCompositionOfSha
pe.of_isStableUnderColimitsOfShape.mem`：mem [W.RespectsIso] : W f
-/
lemma IsStableUnderTransfiniteCompositionOfShape.of_isStableUnderColimitsOfShape
    [W.IsMultiplicative] [W.RespectsIso]
    (hJ : ∀ (J : Type w) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J],
      W.IsStableUnderColimitsOfShape J) :
    W.IsStableUnderTransfiniteCompositionOfShape J where
  le _ _ _ | ⟨hf⟩ => mem hf hJ
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [W.IsMultiplicative] [W.RespectsIso]
    [MorphismProperty.IsStableUnderFilteredColimits.{w, w} W] :
    W.IsStableUnderTransfiniteCompositionOfShape J :=
  .of_isStableUnderColimitsOfShape (fun _ _ _ _ _ ↦ by infer_instance)

end

/-- A class of morphisms `W : MorphismProperty C` is stable under infinite composition
if for any functor `F : ℕ ⥤ C` such that `F.obj n ⟶ F.obj (n + 1)` is in `W` for any `n : ℕ`,
the map `F.obj 0 ⟶ c.pt` is in `W` for any colimit cocone `c : Cocone F`. -/
/-
**CategoryTheory.MorphismProperty.IsStableUnderInfiniteComposition** 是 Mathlib 中
的一个缩写定义，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：IsStableUnderInfiniteComposition : Prop
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ

--- 原说明 ---
A class of morphisms `W : MorphismProperty C` is stable under infinite compositi
on
if for any functor `F : ℕ ⥤ C` such that `F.obj n ⟶ F.obj (n + 1)` is in `W` for
 any `n : ℕ`,
the map `F.obj 0 ⟶ c.pt` is in `W` for any colimit cocone `c : Cocone F`.
-/
abbrev IsStableUnderInfiniteComposition : Prop :=
  W.IsStableUnderTransfiniteCompositionOfShape ℕ

/-- A class of morphisms `W : MorphismProperty C` is stable under transfinite composition
if it is multiplicative and stable under transfinite composition of any shape
(in a certain universe). -/
/-
**CategoryTheory.MorphismProperty.IsStableUnderTransfiniteComposition** 是 Mathli
b 中的一个类，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：IsStableUnderTransfiniteComposition : Prop where isStableUnderTransfiniteC
ompositionOfShape (J : Type w) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellF
oundedLT J] : W.IsStableUnderTransfiniteCompositionOfShape J
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A class of morphisms `W : MorphismProperty C` is stable under transfinite compos
ition
if it is multiplicative and stable under transfinite composition of any shape
(in a certain universe).
-/
class IsStableUnderTransfiniteComposition : Prop where
  isStableUnderTransfiniteCompositionOfShape
    (J : Type w) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J] :
    W.IsStableUnderTransfiniteCompositionOfShape J := by infer_instance

namespace IsStableUnderTransfiniteComposition

attribute [instance] isStableUnderTransfiniteCompositionOfShape

/-
**CategoryTheory.MorphismProperty.IsStableUnderTransfiniteComposition.** 是 Mathl
ib 中的一个实例，位于命名空间 `CategoryTheory.MorphismProperty.IsStableUnderTransfiniteCompos
ition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [W.IsMultiplicative] [W.RespectsIso]
    [MorphismProperty.IsStableUnderFilteredColimits.{w, w} W] :
    IsStableUnderTransfiniteComposition.{w} W where
/-
**CategoryTheory.MorphismProperty.IsStableUnderTransfiniteComposition.** 是 Mathl
ib 中的一个示例，位于命名空间 `CategoryTheory.MorphismProperty.IsStableUnderTransfiniteCompos
ition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : (isomorphisms C).IsStableUnderTransfiniteComposition := inferInstance

variable [IsStableUnderTransfiniteComposition.{w'} W]
/-
**CategoryTheory.MorphismProperty.IsStableUnderTransfiniteComposition.shrink** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty.IsStableUnderTransfinite
Composition`。
形式化陈述：shrink [UnivLE.{w, w'}] : IsStableUnderTransfiniteComposition.{w} W where 
isStableUnderTransfiniteCompositionOfShape J _ _ _ _
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `instWellFoundedLTShrink`：∀ {α : Type u_1} [inst : Small.{u, u_1} α] [ins
t_1 : Preorder α] [WellFoundedLT α], WellFoundedLT (Shrink.{u, u_1} α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.isStableUnderTransfiniteCompositionOfSha
pe_iff_of_orderIso`：isStableUnderTransfiniteCompositionOfShape_iff_of_orderIso (
e : J ≃o J') : W.IsStableUnderTransfiniteCompositionOfShape J ↔ W.IsStableUnderT
…
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderTransfiniteComposition.isSt
ableUnderTransfiniteCompositionOfShape`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {W : CategoryTheory.MorphismProperty C}   [self : W.IsStableUnd
erTransfiniteComposi…
-/
lemma shrink [UnivLE.{w, w'}] :
    IsStableUnderTransfiniteComposition.{w} W where
  isStableUnderTransfiniteCompositionOfShape J _ _ _ _ := by
    rw [isStableUnderTransfiniteCompositionOfShape_iff_of_orderIso W
      (orderIsoShrink.{w'} J)]
    infer_instance
/-
**CategoryTheory.MorphismProperty.IsStableUnderTransfiniteComposition.shrink** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty.IsStableUnderTransfinite
Composition`。
形式化陈述：shrink [UnivLE.{w, w'}] : IsStableUnderTransfiniteComposition.{w} W where 
isStableUnderTransfiniteCompositionOfShape J _ _ _ _
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `instWellFoundedLTShrink`：∀ {α : Type u_1} [inst : Small.{u, u_1} α] [ins
t_1 : Preorder α] [WellFoundedLT α], WellFoundedLT (Shrink.{u, u_1} α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.isStableUnderTransfiniteCompositionOfSha
pe_iff_of_orderIso`：isStableUnderTransfiniteCompositionOfShape_iff_of_orderIso (
e : J ≃o J') : W.IsStableUnderTransfiniteCompositionOfShape J ↔ W.IsStableUnderT
…
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderTransfiniteComposition.isSt
ableUnderTransfiniteCompositionOfShape`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {W : CategoryTheory.MorphismProperty C}   [self : W.IsStableUnd
erTransfiniteComposi…
-/
lemma shrink₀ : IsStableUnderTransfiniteComposition.{0} W := shrink.{0, w'} W

attribute [local instance] shrink₀
/-
**CategoryTheory.MorphismProperty.IsStableUnderTransfiniteComposition.** 是 Mathl
ib 中的一个实例，位于命名空间 `CategoryTheory.MorphismProperty.IsStableUnderTransfiniteCompos
ition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**CategoryTheory.MorphismProperty.transfiniteCompositions** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：transfiniteCompositions : MorphismProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The class of transfinite compositions (for arbitrary well-ordered types `J : Typ
e w`)
of a class of morphisms `W`.
-/
def transfiniteCompositions : MorphismProperty C :=
  ⨆ (J : Type w) (_ : LinearOrder J) (_ : SuccOrder J) (_ : OrderBot J)
    (_ : WellFoundedLT J), W.transfiniteCompositionsOfShape J
/-
**CategoryTheory.MorphismProperty.transfiniteCompositions_iff** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：transfiniteCompositions_iff {X Y : C} (f : X ⟶ Y) : transfiniteComposition
s.{w} W f ↔ exists (J : Type w) (_ : LinearOrder J) (_ : SuccOrder J) (_ : Order
Bot J) (_ : WellFoundedLT J), W.transfiniteCompositionsOfShape J f
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma transfiniteCompositions_iff {X Y : C} (f : X ⟶ Y) :
    transfiniteCompositions.{w} W f ↔
      ∃ (J : Type w) (_ : LinearOrder J) (_ : SuccOrder J) (_ : OrderBot J)
        (_ : WellFoundedLT J), W.transfiniteCompositionsOfShape J f := by
  simp only [transfiniteCompositions, iSup_iff]
/-
**CategoryTheory.MorphismProperty.transfiniteCompositionsOfShape_le_transfiniteC
ompositions** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：transfiniteCompositionsOfShape_le_transfiniteCompositions (J : Type w) [Li
nearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J] : W.transfiniteComposi
tionsOfShape J <= transfiniteCompositions.{w} W
参数：J : Type w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.transfiniteCompositions_iff`：transfinite
Compositions_iff {X Y : C} (f : X ⟶ Y) : transfiniteCompositions.{w} W f ↔ exist
s (J : Type w) (_ : LinearOrder J) (_ : SuccOrder…
-/
lemma transfiniteCompositionsOfShape_le_transfiniteCompositions
    (J : Type w) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J] :
    W.transfiniteCompositionsOfShape J ≤ transfiniteCompositions.{w} W := by
  intro A B f hf
  rw [transfiniteCompositions_iff]
  exact ⟨_, _, _, _, _, hf⟩
/-
**CategoryTheory.MorphismProperty.transfiniteCompositions_monotone** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：transfiniteCompositions_monotone : Monotone (transfiniteCompositions.{w} (
C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.transfiniteCompositions_iff`：transfinite
Compositions_iff {X Y : C} (f : X ⟶ Y) : transfiniteCompositions.{w} W f ↔ exist
s (J : Type w) (_ : LinearOrder J) (_ : SuccOrder…
· 使用引理 `CategoryTheory.MorphismProperty.transfiniteCompositionsOfShape_le_transf
initeCompositions`：transfiniteCompositionsOfShape_le_transfiniteCompositions (J 
: Type w) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J] : W.tran…
· 使用引理 `CategoryTheory.MorphismProperty.transfiniteCompositionsOfShape_monotone`
：transfiniteCompositionsOfShape_monotone : Monotone (transfiniteCompositionsOfSh
ape (C
-/
lemma transfiniteCompositions_monotone :
    Monotone (transfiniteCompositions.{w} (C := C)) := by
  intro W₁ W₂ h X Y f hf
  rw [transfiniteCompositions_iff] at hf
  obtain ⟨J, _, _, _, _, hf⟩ := hf
  exact transfiniteCompositionsOfShape_le_transfiniteCompositions _ _ _
    (transfiniteCompositionsOfShape_monotone J h _ hf)
/-
**CategoryTheory.MorphismProperty.le_transfiniteCompositions** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：le_transfiniteCompositions : W <= transfiniteCompositions.{w} W
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instWellFoundedLTShrink`：∀ {α : Type u_1} [inst : Small.{u, u_1} α] [ins
t_1 : Preorder α] [WellFoundedLT α], WellFoundedLT (Shrink.{u, u_1} α)
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `Fin.Lt.isWellOrder`：∀ (n : ℕ), IsWellOrder (Fin n) fun x1 x2 => x1 < x2
· 使用定理 `CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape.mem`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] {W : CategoryTheory.Morphism
Property C} {J : Type w}   [inst_1 : LinearOrder J] [in…
· 使用引理 `CategoryTheory.MorphismProperty.transfiniteCompositionsOfShape_le_transf
initeCompositions`：transfiniteCompositionsOfShape_le_transfiniteCompositions (J 
: Type w) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J] : W.tran…
-/
lemma le_transfiniteCompositions :
    W ≤ transfiniteCompositions.{w} W :=
  le_trans (fun _ _ _ hf ↦
    (MorphismProperty.TransfiniteCompositionOfShape.ofOrderIso (.ofMem _ hf)
      (orderIsoShrink.{w} (Fin 2)).symm).mem)
    (transfiniteCompositionsOfShape_le_transfiniteCompositions _ _)
/-
**CategoryTheory.MorphismProperty.transfiniteCompositions_le** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：transfiniteCompositions_le [IsStableUnderTransfiniteComposition.{w} W] : t
ransfiniteCompositions.{w} W <= W
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.transfiniteCompositions_iff`：transfinite
Compositions_iff {X Y : C} (f : X ⟶ Y) : transfiniteCompositions.{w} W f ↔ exist
s (J : Type w) (_ : LinearOrder J) (_ : SuccOrder…
· 使用引理 `CategoryTheory.MorphismProperty.transfiniteCompositionsOfShape_le`：trans
finiteCompositionsOfShape_le [W.IsStableUnderTransfiniteCompositionOfShape J] : 
W.transfiniteCompositionsOfShape J <= W
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderTransfiniteComposition.isSt
ableUnderTransfiniteCompositionOfShape`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {W : CategoryTheory.MorphismProperty C}   [self : W.IsStableUnd
erTransfiniteComposi…
-/
lemma transfiniteCompositions_le [IsStableUnderTransfiniteComposition.{w} W] :
    transfiniteCompositions.{w} W ≤ W := by
  intro _ _ f hf
  rw [transfiniteCompositions_iff] at hf
  obtain ⟨J, _, _, _, _, hf⟩ := hf
  exact W.transfiniteCompositionsOfShape_le J _ hf

@[simp]
/-
**CategoryTheory.MorphismProperty.transfiniteCompositions_le_iff** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：transfiniteCompositions_le_iff {P Q : MorphismProperty C} [IsStableUnderTr
ansfiniteComposition.{w} Q] : transfiniteCompositions.{w} P <= Q ↔ P <= Q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `CategoryTheory.MorphismProperty.le_transfiniteCompositions`：le_transfini
teCompositions : W <= transfiniteCompositions.{w} W
· 使用引理 `CategoryTheory.MorphismProperty.transfiniteCompositions_monotone`：transf
initeCompositions_monotone : Monotone (transfiniteCompositions.{w} (C
· 使用引理 `CategoryTheory.MorphismProperty.transfiniteCompositions_le`：transfiniteC
ompositions_le [IsStableUnderTransfiniteComposition.{w} W] : transfiniteComposit
ions.{w} W <= W
-/
lemma transfiniteCompositions_le_iff {P Q : MorphismProperty C}
    [IsStableUnderTransfiniteComposition.{w} Q] :
    transfiniteCompositions.{w} P ≤ Q ↔ P ≤ Q := by
  constructor
  · exact (le_transfiniteCompositions P).trans
  · intro h
    exact (transfiniteCompositions_monotone.{w} h).trans Q.transfiniteCompositions_le

namespace TransfiniteCompositionOfShape

variable {W} {J : Type w} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]

section

variable [IsStableUnderTransfiniteComposition.{w} W]
  {X Y : C} {f : X ⟶ Y} (h : W.TransfiniteCompositionOfShape J f)

/-
**CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape.mem_map** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape
`。
形式化陈述：mem_map {i j : J} (φ : i ⟶ j) : W (h.F.map φ)
参数：φ : i ⟶ j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.transfiniteCompositionsOfShape_le`：trans
finiteCompositionsOfShape_le [W.IsStableUnderTransfiniteCompositionOfShape J] : 
W.transfiniteCompositionsOfShape J <= W
· 使用定理 `CategoryTheory.leOfHom`：leOfHom {x y : X} (h : x ⟶ y) : x <= y
· 使用定理 `Set.ordConnected_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, (Set
.Iic a).OrdConnected
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderTransfiniteComposition.isSt
ableUnderTransfiniteCompositionOfShape`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {W : CategoryTheory.MorphismProperty C}   [self : W.IsStableUnd
erTransfiniteComposi…
· 使用定理 `CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape.mem`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] {W : CategoryTheory.Morphism
Property C} {J : Type w}   [inst_1 : LinearOrder J] [in…
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
lemma mem_map {i j : J} (φ : i ⟶ j) :
    W (h.F.map φ) :=
  W.transfiniteCompositionsOfShape_le _ _ ((h.iic j).ici ⟨i, leOfHom φ⟩).mem
/-
**CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape.mem_incl_app** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty.TransfiniteCompositionOf
Shape`。
形式化陈述：mem_incl_app (j : J) : W (h.incl.app j)
参数：j : J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.transfiniteCompositionsOfShape_le`：trans
finiteCompositionsOfShape_le [W.IsStableUnderTransfiniteCompositionOfShape J] : 
W.transfiniteCompositionsOfShape J <= W
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderTransfiniteComposition.isSt
ableUnderTransfiniteCompositionOfShape`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {W : CategoryTheory.MorphismProperty C}   [self : W.IsStableUnd
erTransfiniteComposi…
· 使用定理 `CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape.mem`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] {W : CategoryTheory.Morphism
Property C} {J : Type w}   [inst_1 : LinearOrder J] [in…
-/
lemma mem_incl_app (j : J) :
    W (h.incl.app j) :=
  W.transfiniteCompositionsOfShape_le _ _ (h.ici j).mem

end

section isomorphisms

/-
**CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape.** 是 Mathlib 中的一
个示例，位于命名空间 `CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : (isomorphisms C).IsStableUnderTransfiniteCompositionOfShape J := inferInstance

variable {X Y : C} {f : X ⟶ Y} (h : (isomorphisms C).TransfiniteCompositionOfShape J f)

include h in
/-
**CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape.isIso** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape`。
形式化陈述：isIso : IsIso f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.transfiniteCompositionsOfShape_le`：trans
finiteCompositionsOfShape_le [W.IsStableUnderTransfiniteCompositionOfShape J] : 
W.transfiniteCompositionsOfShape J <= W
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderTransfiniteComposition.isSt
ableUnderTransfiniteCompositionOfShape`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {W : CategoryTheory.MorphismProperty C}   [self : W.IsStableUnd
erTransfiniteComposi…
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderTransfiniteComposition.inst
OfIsMultiplicativeOfRespectsIsoOfIsStableUnderFilteredColimits`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] (W : CategoryTheory.MorphismProperty C)
 [W.IsMultiplicative]   [W.RespectsIso] [Cat…
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instIsomorphisms`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C],   (CategoryTheory.MorphismP
roperty.isomorphisms C).IsMultiplicative
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.isomorphisms`：∀ (C : Type u)
 [inst : CategoryTheory.Category.{v, u} C], (CategoryTheory.MorphismProperty.iso
morphisms C).RespectsIso
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderFilteredColimitsIsomorp
hisms`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C],   CategoryTheor
y.MorphismProperty.IsStableUnderFilteredColimits.{w, w', v, u}     …
· 使用定理 `CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape.mem`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] {W : CategoryTheory.Morphism
Property C} {J : Type w}   [inst_1 : LinearOrder J] [in…
-/
lemma isIso : IsIso f :=
  (isomorphisms C).transfiniteCompositionsOfShape_le _ _ h.mem
/-
**CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape.** 是 Mathlib 中的一
个实例，位于命名空间 `CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {i j : J} (f : i ⟶ j) : IsIso (h.F.map f) := h.mem_map f
/-
**CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape.** 是 Mathlib 中的一
个实例，位于命名空间 `CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (j : J) : IsIso (h.incl.app j) := h.mem_incl_app j

end isomorphisms

end TransfiniteCompositionOfShape

end MorphismProperty

end CategoryTheory

