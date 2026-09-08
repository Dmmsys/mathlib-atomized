/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.Restriction
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Embedding.Boundary
public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Relations between `extend` and `restriction`

Given an embedding `e : Embedding c c'` of complex shapes satisfying `e.IsRelIff`,
we obtain a bijection `e.homEquiv` between the type of morphisms
`K ⟶ L.extend e` (with `K : HomologicalComplex C c'` and `L : HomologicalComplex C c`)
and the subtype of morphisms `φ : K.restriction e ⟶ L` which satisfy a certain
condition `e.HasLift φ`.

## TODO
* obtain dual results for morphisms `L.extend e ⟶ K`.

-/

@[expose] public section

open CategoryTheory Category Limits

namespace ComplexShape

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : Embedding c c')
  {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

namespace Embedding

open HomologicalComplex

variable {K K' : HomologicalComplex C c'} {L L' : HomologicalComplex C c}
  [e.IsRelIff]

section

/-- The condition on a morphism `K.restriction e ⟶ L` which allows to
extend it as a morphism `K ⟶ L.extend e`, see `Embedding.homEquiv`. -/
/-
**ComplexShape.Embedding.HasLift** 是 Mathlib 中的一个定义，位于命名空间 `ComplexShape.Embeddi
ng`。
形式化陈述：HasLift (φ : K.restriction e ⟶ L) : Prop
参数：φ : K.restriction e ⟶ L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condition on a morphism `K.restriction e ⟶ L` which allows to
extend it as a morphism `K ⟶ L.extend e`, see `Embedding.homEquiv`.
-/
def HasLift (φ : K.restriction e ⟶ L) : Prop :=
  ∀ (j : ι) (_ : e.BoundaryGE j) (i' : ι')
    (_ : c'.Rel i' (e.f j)), K.d i' _ ≫ φ.f j = 0

namespace liftExtend

variable (φ : K.restriction e ⟶ L)

variable {e}

open scoped Classical in
/-- Auxiliary definition for `liftExtend`. -/
/-
**ComplexShape.Embedding.liftExtend.f** 是 Mathlib 中的一个定义，位于命名空间 `ComplexShape.Em
bedding.liftExtend`。
形式化陈述：f (i' : ι') : K.X i' ⟶ (L.extend e).X i'
参数：i' : ι'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `liftExtend`.
-/
noncomputable def f (i' : ι') : K.X i' ⟶ (L.extend e).X i' :=
  if hi' : ∃ i, e.f i = i' then
    (K.restrictionXIso e hi'.choose_spec).inv ≫ φ.f hi'.choose ≫
      (L.extendXIso e hi'.choose_spec).inv
  else 0
/-
**ComplexShape.Embedding.liftExtend.f_eq** 是 Mathlib 中的一个引理，位于命名空间 `ComplexShape
.Embedding.liftExtend`。
形式化陈述：f_eq {i' : ι'} {i : ι} (hi : e.f i = i') : f φ i' = (K.restrictionXIso e h
i).inv ≫ φ.f i ≫ (L.extendXIso e hi).inv
参数：hi : e.f i = i'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.Embedding.injective_f`：∀ {ι : Type u_1} {ι' : Type u_2} {c 
: ComplexShape ι} {c' : ComplexShape ι'} (self : c.Embedding c'),   Function.Inj
ective self.f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma f_eq {i' : ι'} {i : ι} (hi : e.f i = i') :
    f φ i' = (K.restrictionXIso e hi).inv ≫ φ.f i ≫ (L.extendXIso e hi).inv := by
  have hi' : ∃ k, e.f k = i' := ⟨i, hi⟩
  have : hi'.choose = i := e.injective_f (by rw [hi'.choose_spec, hi])
  grind [f]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**ComplexShape.Embedding.liftExtend.comm** 是 Mathlib 中的一个引理，位于命名空间 `ComplexShape
.Embedding.liftExtend`。
形式化陈述：comm (hφ : e.HasLift φ) (i' j' : ι') : f φ i' ≫ (L.extend e).d i' j' = K.d
 i' j' ≫ f φ j'
参数：hφ : e.HasLift φ；i' j' : ι'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ComplexShape.Embedding.liftExtend.f_eq`：f_eq {i' : ι'} {i : ι} (hi : e.f
 i = i') : f φ i' = (K.restrictionXIso e hi).inv ≫ φ.f i ≫ (L.extendXIso e hi).i
nv
· 使用引理 `HomologicalComplex.extend_d_eq`：extend_d_eq {i' j' : ι'} {i j : ι} (hi :
 e.f i = i') (hj : e.f j = j') : (K.extend e).d i' j' = (K.extendXIso e hi).hom 
≫ K.d i j ≫ (K.exten…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `HomologicalComplex.Hom.comm_assoc`：∀ {ι : Type u_1} {V : Type u} [inst :
 CategoryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms V] {c : ComplexSh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_tgt`：eq_of_tgt (hX : IsZero X) (f g :
 Y ⟶ X) : f = g
· 使用引理 `HomologicalComplex.isZero_extend_X`：isZero_extend_X (i' : ι') (hi' : for
all i, e.f i != i') : IsZero ((K.extend e).X i')
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_src`：eq_of_src (hX : IsZero X) (f g :
 X ⟶ Y) : f = g
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用引理 `ComplexShape.Embedding.boundaryGE`：boundaryGE {i' : ι'} {j : ι} (hj : c'
.Rel i' (e.f j)) (hi' : forall i, e.f i != i') : e.BoundaryGE j
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `HomologicalComplex.shape`：∀ {ι : Type u_1} {V : Type u} [inst : Category
Theory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] 
{c : ComplexSh…
-/
lemma comm (hφ : e.HasLift φ) (i' j' : ι') :
    f φ i' ≫ (L.extend e).d i' j' = K.d i' j' ≫ f φ j' := by
  by_cases hij' : c'.Rel i' j'
  · by_cases hi' : ∃ i, e.f i = i'
    · obtain ⟨i, hi⟩ := hi'
      rw [f_eq φ hi]
      by_cases hj' : ∃ j, e.f j = j'
      · obtain ⟨j, hj⟩ := hj'
        rw [f_eq φ hj, L.extend_d_eq e hi hj]
        subst hi hj
        simp [HomologicalComplex.restrictionXIso]
      · apply (L.isZero_extend_X e j' (by simpa using hj')).eq_of_tgt
    · have : (L.extend e).d i' j' = 0 := by
        apply (L.isZero_extend_X e i' (by simpa using hi')).eq_of_src
      rw [this, comp_zero]
      by_cases hj' : ∃ j, e.f j = j'
      · obtain ⟨j, rfl⟩ := hj'
        rw [f_eq φ rfl]
        dsimp [restrictionXIso]
        rw [id_comp, reassoc_of% (hφ j (e.boundaryGE hij'
          (by simpa using hi')) i' hij'), zero_comp]
      · have : f φ j' = 0 := by
          apply (L.isZero_extend_X e j' (by simpa using hj')).eq_of_tgt
        rw [this, comp_zero]
  · simp [HomologicalComplex.shape _ _ _ hij']

end liftExtend

variable (φ : K.restriction e ⟶ L) (hφ : e.HasLift φ)

/-- The morphism  `K ⟶ L.extend e` given by a morphism `K.restriction e ⟶ L`
which satisfy `e.HasLift φ`. -/
/-
**ComplexShape.Embedding.liftExtend** 是 Mathlib 中的一个定义，位于命名空间 `ComplexShape.Embe
dding`。
形式化陈述：liftExtend : K ⟶ L.extend e where f i'
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `ComplexShape.Embedding.liftExtend.comm`：comm (hφ : e.HasLift φ) (i' j' :
 ι') : f φ i' ≫ (L.extend e).d i' j' = K.d i' j' ≫ f φ j'

--- 原说明 ---
The morphism  `K ⟶ L.extend e` given by a morphism `K.restriction e ⟶ L`
which satisfy `e.HasLift φ`.
-/
noncomputable def liftExtend :
    K ⟶ L.extend e where
  f i' := liftExtend.f φ i'
  comm' _ _ _ := liftExtend.comm φ hφ _ _

variable {i' : ι'} {i : ι} (hi : e.f i = i')
/-
**ComplexShape.Embedding.liftExtend_f** 是 Mathlib 中的一个引理，位于命名空间 `ComplexShape.Em
bedding`。
形式化陈述：liftExtend_f : (e.liftExtend φ hφ).f i' = (K.restrictionXIso e hi).inv ≫ φ
.f i ≫ (L.extendXIso e hi).inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ComplexShape.Embedding.liftExtend.f_eq`：f_eq {i' : ι'} {i : ι} (hi : e.f
 i = i') : f φ i' = (K.restrictionXIso e hi).inv ≫ φ.f i ≫ (L.extendXIso e hi).i
nv
-/
lemma liftExtend_f :
    (e.liftExtend φ hφ).f i' = (K.restrictionXIso e hi).inv ≫ φ.f i ≫
      (L.extendXIso e hi).inv := by
  apply liftExtend.f_eq

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Given `φ : K.restriction e ⟶ L` such that `hφ : e.HasLift φ`, this is
the isomorphisms in the category of arrows between the maps
`(e.liftExtend φ hφ).f i'` and `φ.f i` when `e.f i = i'`. -/
/-
**ComplexShape.Embedding.liftExtendfArrowIso** 是 Mathlib 中的一个定义，位于命名空间 `ComplexS
hape.Embedding`。
形式化陈述：liftExtendfArrowIso : Arrow.mk ((e.liftExtend φ hφ).f i') ≅ Arrow.mk (φ.f 
i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `φ : K.restriction e ⟶ L` such that `hφ : e.HasLift φ`, this is
the isomorphisms in the category of arrows between the maps
`(e.liftExtend φ hφ).f i'` and `φ.f i` when `e.f i = i'`.
-/
noncomputable def liftExtendfArrowIso :
    Arrow.mk ((e.liftExtend φ hφ).f i') ≅ Arrow.mk (φ.f i) :=
  Arrow.isoMk (K.restrictionXIso e hi).symm (L.extendXIso e hi)
    (by simp [e.liftExtend_f φ hφ hi])
/-
**ComplexShape.Embedding.isIso_liftExtend_f_iff** 是 Mathlib 中的一个引理，位于命名空间 `Compl
exShape.Embedding`。
形式化陈述：isIso_liftExtend_f_iff (hi : e.f i = i') : IsIso ((e.liftExtend φ hφ).f i'
) ↔ IsIso (φ.f i)
参数：hi : e.f i = i'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.isomorphisms`：∀ (C : Type u)
 [inst : CategoryTheory.Category.{v, u} C], (CategoryTheory.MorphismProperty.iso
morphisms C).RespectsIso
-/
lemma isIso_liftExtend_f_iff (hi : e.f i = i') :
    IsIso ((e.liftExtend φ hφ).f i') ↔ IsIso (φ.f i) :=
  (MorphismProperty.isomorphisms C).arrow_mk_iso_iff (e.liftExtendfArrowIso φ hφ hi)
/-
**ComplexShape.Embedding.mono_liftExtend_f_iff** 是 Mathlib 中的一个引理，位于命名空间 `Comple
xShape.Embedding`。
形式化陈述：mono_liftExtend_f_iff (hi : e.f i = i') : Mono ((e.liftExtend φ hφ).f i') 
↔ Mono (φ.f i)
参数：hi : e.f i = i'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.monomorphisms`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C], (CategoryTheory.MorphismProperty.mo
nomorphisms C).RespectsIso
-/
lemma mono_liftExtend_f_iff (hi : e.f i = i') :
    Mono ((e.liftExtend φ hφ).f i') ↔ Mono (φ.f i) :=
  (MorphismProperty.monomorphisms C).arrow_mk_iso_iff (e.liftExtendfArrowIso φ hφ hi)
/-
**ComplexShape.Embedding.epi_liftExtend_f_iff** 是 Mathlib 中的一个引理，位于命名空间 `Complex
Shape.Embedding`。
形式化陈述：epi_liftExtend_f_iff (hi : e.f i = i') : Epi ((e.liftExtend φ hφ).f i') ↔ 
Epi (φ.f i)
参数：hi : e.f i = i'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.epimorphisms`：∀ (C : Type u)
 [inst : CategoryTheory.Category.{v, u} C], (CategoryTheory.MorphismProperty.epi
morphisms C).RespectsIso
-/
lemma epi_liftExtend_f_iff (hi : e.f i = i') :
    Epi ((e.liftExtend φ hφ).f i') ↔ Epi (φ.f i) :=
  (MorphismProperty.epimorphisms C).arrow_mk_iso_iff (e.liftExtendfArrowIso φ hφ hi)

end

namespace homRestrict

variable {e}
variable (ψ : K ⟶ L.extend e)

/-- Auxiliary definition for `Embedding.homRestrict`. -/
/-
**ComplexShape.Embedding.homRestrict.f** 是 Mathlib 中的一个定义，位于命名空间 `ComplexShape.E
mbedding.homRestrict`。
形式化陈述：f (i : ι) : (K.restriction e).X i ⟶ L.X i
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `Embedding.homRestrict`.
-/
noncomputable def f (i : ι) : (K.restriction e).X i ⟶ L.X i :=
  ψ.f (e.f i) ≫ (L.extendXIso e rfl).hom

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**ComplexShape.Embedding.homRestrict.f_eq** 是 Mathlib 中的一个引理，位于命名空间 `ComplexShap
e.Embedding.homRestrict`。
形式化陈述：f_eq {i : ι} {i' : ι'} (h : e.f i = i') : f ψ i = (K.restrictionXIso e h).
hom ≫ ψ.f i' ≫ (L.extendXIso e h).hom
参数：h : e.f i = i'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma f_eq {i : ι} {i' : ι'} (h : e.f i = i') :
    f ψ i = (K.restrictionXIso e h).hom ≫ ψ.f i' ≫ (L.extendXIso e h).hom := by
  subst h
  simp [f, restrictionXIso]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**ComplexShape.Embedding.homRestrict.comm** 是 Mathlib 中的一个引理，位于命名空间 `ComplexShap
e.Embedding.homRestrict`。
形式化陈述：comm (i j : ι) : f ψ i ≫ L.d i j = K.d (e.f i) (e.f j) ≫ f ψ j
参数：i j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HomologicalComplex.Hom.comm_assoc`：∀ {ι : Type u_1} {V : Type u} [inst :
 CategoryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms V] {c : ComplexSh…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `HomologicalComplex.extend_d_eq`：extend_d_eq {i' j' : ι'} {i j : ι} (hi :
 e.f i = i') (hj : e.f j = j') : (K.extend e).d i' j' = (K.extendXIso e hi).hom 
≫ K.d i j ≫ (K.exten…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comm (i j : ι) :
    f ψ i ≫ L.d i j = K.d (e.f i) (e.f j) ≫ f ψ j := by
  dsimp [f]
  simp only [assoc, ← ψ.comm_assoc, L.extend_d_eq e rfl rfl, Iso.inv_hom_id, comp_id]

end homRestrict

/-- The morphism `K.restriction e ⟶ L` induced by a morphism `K ⟶ L.extend e`. -/
/-
**ComplexShape.Embedding.homRestrict** 是 Mathlib 中的一个定义，位于命名空间 `ComplexShape.Emb
edding`。
形式化陈述：homRestrict (ψ : K ⟶ L.extend e) : K.restriction e ⟶ L where f i
参数：ψ : K ⟶ L.extend e。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `K.restriction e ⟶ L` induced by a morphism `K ⟶ L.extend e`.
-/
noncomputable def homRestrict (ψ : K ⟶ L.extend e) : K.restriction e ⟶ L where
  f i := homRestrict.f ψ i
/-
**ComplexShape.Embedding.homRestrict_f** 是 Mathlib 中的一个引理，位于命名空间 `ComplexShape.E
mbedding`。
形式化陈述：homRestrict_f (ψ : K ⟶ L.extend e) {i : ι} {i' : ι'} (h : e.f i = i') : (e
.homRestrict ψ).f i = (K.restrictionXIso e h).hom ≫ ψ.f i' ≫ (L.extendXIso e h).
hom
参数：ψ : K ⟶ L.extend e；h : e.f i = i'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ComplexShape.Embedding.homRestrict.f_eq`：f_eq {i : ι} {i' : ι'} (h : e.f
 i = i') : f ψ i = (K.restrictionXIso e h).hom ≫ ψ.f i' ≫ (L.extendXIso e h).hom
-/
lemma homRestrict_f (ψ : K ⟶ L.extend e) {i : ι} {i' : ι'} (h : e.f i = i') :
    (e.homRestrict ψ).f i = (K.restrictionXIso e h).hom ≫ ψ.f i' ≫ (L.extendXIso e h).hom :=
  homRestrict.f_eq ψ h

set_option backward.isDefEq.respectTransparency false in
/-
**ComplexShape.Embedding.homRestrict_hasLift** 是 Mathlib 中的一个引理，位于命名空间 `ComplexS
hape.Embedding`。
形式化陈述：homRestrict_hasLift (ψ : K ⟶ L.extend e) : e.HasLift (e.homRestrict ψ)
参数：ψ : K ⟶ L.extend e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_src`：eq_of_src (hX : IsZero X) (f g :
 X ⟶ Y) : f = g
· 使用引理 `HomologicalComplex.isZero_extend_X`：isZero_extend_X (i' : ι') (hi' : for
all i, e.f i != i') : IsZero ((K.extend e).X i')
· 使用定理 `ComplexShape.Embedding.BoundaryGE.notMem`：∀ {ι : Type u_1} {ι' : Type u_
2} {c : ComplexShape ι} {c' : ComplexShape ι'} {e : c.Embedding c'} {j : ι},   e
.BoundaryGE j → ∀ {i' : ι'}, c…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ComplexShape.Embedding.homRestrict.f_eq`：f_eq {i : ι} {i' : ι'} (h : e.f
 i = i') : f ψ i = (K.restrictionXIso e h).hom ≫ ψ.f i' ≫ (L.extendXIso e h).hom
· 使用定理 `HomologicalComplex.restrictionXIso.eq_1`：∀ {ι : Type u_1} {ι' : Type u_2
} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst : CategoryT
heory.Category.{v_1, u_3} C] …
· 使用定理 `CategoryTheory.eqToIso_refl`：eqToIso_refl {X : C} (p : X = X) : eqToIso 
p = Iso.refl X
· 使用定理 `CategoryTheory.Iso.refl_hom`：∀ {C : Type u} [inst : CategoryTheory.Categ
ory.{v, u} C] (X : C),   (CategoryTheory.Iso.refl X).hom = CategoryTheory.Catego
ryStruct.id X
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HomologicalComplex.Hom.comm_assoc`：∀ {ι : Type u_1} {V : Type u} [inst :
 CategoryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms V] {c : ComplexSh…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
-/
lemma homRestrict_hasLift (ψ : K ⟶ L.extend e) :
    e.HasLift (e.homRestrict ψ) := by
  intro j hj i' hij'
  have : (L.extend e).d i' (e.f j) = 0 := by
    apply (L.isZero_extend_X e i' (hj.notMem hij')).eq_of_src
  dsimp [homRestrict]
  rw [homRestrict.f_eq ψ rfl, restrictionXIso, eqToIso_refl, Iso.refl_hom, id_comp,
    ← ψ.comm_assoc, this, zero_comp, comp_zero]

@[simp]
/-
**ComplexShape.Embedding.liftExtend_homRestrict** 是 Mathlib 中的一个引理，位于命名空间 `Compl
exShape.Embedding`。
形式化陈述：liftExtend_homRestrict (ψ : K ⟶ L.extend e) : e.liftExtend (e.homRestrict 
ψ) (e.homRestrict_hasLift ψ) = ψ
参数：ψ : K ⟶ L.extend e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用引理 `ComplexShape.Embedding.homRestrict_hasLift`：homRestrict_hasLift (ψ : K ⟶
 L.extend e) : e.HasLift (e.homRestrict ψ)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ComplexShape.Embedding.liftExtend_f`：liftExtend_f : (e.liftExtend φ hφ).
f i' = (K.restrictionXIso e hi).inv ≫ φ.f i ≫ (L.extendXIso e hi).inv
· 使用引理 `ComplexShape.Embedding.homRestrict_f`：homRestrict_f (ψ : K ⟶ L.extend e)
 {i : ι} {i' : ι'} (h : e.f i = i') : (e.homRestrict ψ).f i = (K.restrictionXIso
 e h).hom ≫ ψ.f i' ≫ (L.ex…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_tgt`：eq_of_tgt (hX : IsZero X) (f g :
 Y ⟶ X) : f = g
· 使用引理 `HomologicalComplex.isZero_extend_X`：isZero_extend_X (i' : ι') (hi' : for
all i, e.f i != i') : IsZero ((K.extend e).X i')
-/
lemma liftExtend_homRestrict (ψ : K ⟶ L.extend e) :
    e.liftExtend (e.homRestrict ψ) (e.homRestrict_hasLift ψ) = ψ := by
  ext i'
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, rfl⟩ := hi'
    simp [e.homRestrict_f _ rfl, e.liftExtend_f _ _ rfl]
  · apply (L.isZero_extend_X e i' (by simpa using hi')).eq_of_tgt

@[simp]
/-
**ComplexShape.Embedding.homRestrict_liftExtend** 是 Mathlib 中的一个引理，位于命名空间 `Compl
exShape.Embedding`。
形式化陈述：homRestrict_liftExtend (φ : K.restriction e ⟶ L) (hφ : e.HasLift φ) : e.ho
mRestrict (e.liftExtend φ hφ) = φ
参数：φ : K.restriction e ⟶ L；hφ : e.HasLift φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ComplexShape.Embedding.homRestrict_f`：homRestrict_f (ψ : K ⟶ L.extend e)
 {i : ι} {i' : ι'} (h : e.f i = i') : (e.homRestrict ψ).f i = (K.restrictionXIso
 e h).hom ≫ ψ.f i' ≫ (L.ex…
· 使用引理 `ComplexShape.Embedding.liftExtend_f`：liftExtend_f : (e.liftExtend φ hφ).
f i' = (K.restrictionXIso e hi).inv ≫ φ.f i ≫ (L.extendXIso e hi).inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homRestrict_liftExtend (φ : K.restriction e ⟶ L) (hφ : e.HasLift φ) :
    e.homRestrict (e.liftExtend φ hφ) = φ := by
  ext i
  simp [e.homRestrict_f _ rfl, e.liftExtend_f _ _ rfl]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**ComplexShape.Embedding.homRestrict_precomp** 是 Mathlib 中的一个引理，位于命名空间 `ComplexS
hape.Embedding`。
形式化陈述：homRestrict_precomp (α : K' ⟶ K) (ψ : K ⟶ L.extend e) : e.homRestrict (α ≫
 ψ) = restrictionMap α e ≫ e.homRestrict ψ
参数：α : K' ⟶ K；ψ : K ⟶ L.extend e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ComplexShape.Embedding.homRestrict_f`：homRestrict_f (ψ : K ⟶ L.extend e)
 {i : ι} {i' : ι'} (h : e.f i = i') : (e.homRestrict ψ).f i = (K.restrictionXIso
 e h).hom ≫ ψ.f i' ≫ (L.ex…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homRestrict_precomp (α : K' ⟶ K) (ψ : K ⟶ L.extend e) :
    e.homRestrict (α ≫ ψ) = restrictionMap α e ≫ e.homRestrict ψ := by
  ext i
  simp [homRestrict_f _ _ rfl, restrictionXIso]

@[reassoc]
/-
**ComplexShape.Embedding.homRestrict_comp_extendMap** 是 Mathlib 中的一个引理，位于命名空间 `C
omplexShape.Embedding`。
形式化陈述：homRestrict_comp_extendMap (ψ : K ⟶ L.extend e) (β : L ⟶ L') : e.homRestri
ct (ψ ≫ extendMap β e) = e.homRestrict ψ ≫ β
参数：ψ : K ⟶ L.extend e；β : L ⟶ L'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ComplexShape.Embedding.homRestrict_f`：homRestrict_f (ψ : K ⟶ L.extend e)
 {i : ι} {i' : ι'} (h : e.f i = i') : (e.homRestrict ψ).f i = (K.restrictionXIso
 e h).hom ≫ ψ.f i' ≫ (L.ex…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `HomologicalComplex.extendMap_f`：extendMap_f {i : ι} {i' : ι'} (h : e.f i
 = i') : (extendMap φ e).f i' = (extendXIso K e h).hom ≫ φ.f i ≫ (extendXIso L e
 h).inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homRestrict_comp_extendMap (ψ : K ⟶ L.extend e) (β : L ⟶ L') :
    e.homRestrict (ψ ≫ extendMap β e) =
      e.homRestrict ψ ≫ β := by
  ext i
  simp [homRestrict_f _ _ rfl, extendMap_f β e rfl]

variable (K L)

/-- The bijection between `K ⟶ L.extend e` and the subtype of `K.restriction e ⟶ L`
consisting of morphisms `φ` such that `e.HasLift φ`. -/
@[simps]
/-
**ComplexShape.Embedding.homEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ComplexShape.Embedd
ing`。
形式化陈述：homEquiv : (K ⟶ L.extend e) ≃ { φ : K.restriction e ⟶ L // e.HasLift φ } w
here toFun ψ
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `ComplexShape.Embedding.homRestrict_hasLift`：homRestrict_hasLift (ψ : K ⟶
 L.extend e) : e.HasLift (e.homRestrict ψ)

--- 原说明 ---
The bijection between `K ⟶ L.extend e` and the subtype of `K.restriction e ⟶ L`
consisting of morphisms `φ` such that `e.HasLift φ`.
-/
noncomputable def homEquiv :
    (K ⟶ L.extend e) ≃ { φ : K.restriction e ⟶ L // e.HasLift φ } where
  toFun ψ := ⟨e.homRestrict ψ, e.homRestrict_hasLift ψ⟩
  invFun φ := e.liftExtend φ.1 φ.2
  left_inv ψ := by simp
  right_inv φ := by simp

end Embedding

end ComplexShape

