/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# Bicomplexes

Given a category `C` with zero morphisms and two complex shapes
`c₁ : ComplexShape I₁` and `c₂ : ComplexShape I₂`, we define
the type of bicomplexes `HomologicalComplex₂ C c₁ c₂` as an
abbreviation for `HomologicalComplex (HomologicalComplex C c₂) c₁`.
In particular, if `K : HomologicalComplex₂ C c₁ c₂`, then
for each `i₁ : I₁`, `K.X i₁` is a column of `K`.

In this file, we obtain the equivalence of categories
`HomologicalComplex₂.flipEquivalence : HomologicalComplex₂ C c₁ c₂ ≌ HomologicalComplex₂ C c₂ c₁`
which is obtained by exchanging the horizontal and vertical directions.

-/

@[expose] public section


open CategoryTheory Limits

variable (C : Type*) [Category* C] [HasZeroMorphisms C]
  {I₁ I₂ : Type*} (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂)

/-- Given a category `C` and two complex shapes `c₁` and `c₂` on types `I₁` and `I₂`,
the associated type of bicomplexes `HomologicalComplex₂ C c₁ c₂` is
`K : HomologicalComplex (HomologicalComplex C c₂) c₁`. Then, the object in
position `⟨i₁, i₂⟩` can be obtained as `(K.X i₁).X i₂`. -/
/-
**HomologicalComplex** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：HomologicalComplex (c : ComplexShape ι) where X : ι -> V d : forall i j, X
 i ⟶ X j shape : forall i j, ¬c.Rel i j -> d i j = 0
参数：c : ComplexShape ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a category `C` and two complex shapes `c₁` and `c₂` on types `I₁` and `I₂`
,
the associated type of bicomplexes `HomologicalComplex₂ C c₁ c₂` is
`K : HomologicalComplex (HomologicalComplex C c₂) c₁`. Then, the object in
position `⟨i₁, i₂⟩` can be obtained as `(K.X i₁).X i₂`.
-/
abbrev HomologicalComplex₂ :=
  HomologicalComplex (HomologicalComplex C c₂) c₁

namespace HomologicalComplex₂

open HomologicalComplex

variable {C c₁ c₂}

/-- The graded object indexed by `I₁ × I₂` induced by a bicomplex. -/
/-
**HomologicalComplex₂.toGradedObject** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalCompl
ex₂`。
形式化陈述：toGradedObject (K : HomologicalComplex₂ C c₁ c₂) : GradedObject (I₁ × I₂) 
C
参数：K : HomologicalComplex₂ C c₁ c₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The graded object indexed by `I₁ × I₂` induced by a bicomplex.
-/
def toGradedObject (K : HomologicalComplex₂ C c₁ c₂) :
    GradedObject (I₁ × I₂) C :=
  fun ⟨i₁, i₂⟩ => (K.X i₁).X i₂

/-- The morphism of graded objects induced by a morphism of bicomplexes. -/
/-
**HomologicalComplex₂.toGradedObjectMap** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalCo
mplex₂`。
形式化陈述：toGradedObjectMap {K L : HomologicalComplex₂ C c₁ c₂} (φ : K ⟶ L) : K.toGr
adedObject ⟶ L.toGradedObject
参数：φ : K ⟶ L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism of graded objects induced by a morphism of bicomplexes.
-/
def toGradedObjectMap {K L : HomologicalComplex₂ C c₁ c₂} (φ : K ⟶ L) :
    K.toGradedObject ⟶ L.toGradedObject :=
  fun ⟨i₁, i₂⟩ => (φ.f i₁).f i₂

@[simp]
/-
**HomologicalComplex₂.toGradedObjectMap_apply** 是 Mathlib 中的一个引理，位于命名空间 `Homolog
icalComplex₂`。
形式化陈述：toGradedObjectMap_apply {K L : HomologicalComplex₂ C c₁ c₂} (φ : K ⟶ L) (i
₁ : I₁) (i₂ : I₂) : toGradedObjectMap φ ⟨i₁, i₂⟩ = (φ.f i₁).f i₂
参数：φ : K ⟶ L；i₁ : I₁；i₂ : I₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toGradedObjectMap_apply {K L : HomologicalComplex₂ C c₁ c₂} (φ : K ⟶ L) (i₁ : I₁) (i₂ : I₂) :
    toGradedObjectMap φ ⟨i₁, i₂⟩ = (φ.f i₁).f i₂ := rfl

variable (C c₁ c₂) in
/-- The functor which sends a bicomplex to its associated graded object. -/
@[simps]
/-
**HomologicalComplex₂.toGradedObjectFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Homologic
alComplex₂`。
形式化陈述：toGradedObjectFunctor : HomologicalComplex₂ C c₁ c₂ ⥤ GradedObject (I₁ × I
₂) C where obj K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor which sends a bicomplex to its associated graded object.
-/
def toGradedObjectFunctor : HomologicalComplex₂ C c₁ c₂ ⥤ GradedObject (I₁ × I₂) C where
  obj K := K.toGradedObject
  map φ := toGradedObjectMap φ
/-
**HomologicalComplex₂.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex₂`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (toGradedObjectFunctor C c₁ c₂).Faithful where
  map_injective {_ _ φ₁ φ₂} h := by
    ext i₁ i₂
    exact congr_fun h ⟨i₁, i₂⟩

section OfGradedObject

variable (c₁ c₂)
variable (X : GradedObject (I₁ × I₂) C)
    (d₁ : ∀ (i₁ i₁' : I₁) (i₂ : I₂), X ⟨i₁, i₂⟩ ⟶ X ⟨i₁', i₂⟩)
    (d₂ : ∀ (i₁ : I₁) (i₂ i₂' : I₂), X ⟨i₁, i₂⟩ ⟶ X ⟨i₁, i₂'⟩)
    (shape₁ : ∀ (i₁ i₁' : I₁) (_ : ¬c₁.Rel i₁ i₁') (i₂ : I₂), d₁ i₁ i₁' i₂ = 0)
    (shape₂ : ∀ (i₁ : I₁) (i₂ i₂' : I₂) (_ : ¬c₂.Rel i₂ i₂'), d₂ i₁ i₂ i₂' = 0)
    (d₁_comp_d₁ : ∀ (i₁ i₁' i₁'' : I₁) (i₂ : I₂), d₁ i₁ i₁' i₂ ≫ d₁ i₁' i₁'' i₂ = 0)
    (d₂_comp_d₂ : ∀ (i₁ : I₁) (i₂ i₂' i₂'' : I₂), d₂ i₁ i₂ i₂' ≫ d₂ i₁ i₂' i₂'' = 0)
    (comm : ∀ (i₁ i₁' : I₁) (i₂ i₂' : I₂), d₁ i₁ i₁' i₂ ≫ d₂ i₁' i₂ i₂' =
      d₂ i₁ i₂ i₂' ≫ d₁ i₁ i₁' i₂')

/-- Constructor for bicomplexes taking as inputs a graded object, horizontal differentials
and vertical differentials satisfying suitable relations. -/
@[simps]
/-
**HomologicalComplex₂.ofGradedObject** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalCompl
ex₂`。
形式化陈述：ofGradedObject : HomologicalComplex₂ C c₁ c₂ where X i₁
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for bicomplexes taking as inputs a graded object, horizontal differe
ntials
and vertical differentials satisfying suitable relations.
-/
def ofGradedObject :
    HomologicalComplex₂ C c₁ c₂ where
  X i₁ :=
    { X := fun i₂ => X ⟨i₁, i₂⟩
      d := fun i₂ i₂' => d₂ i₁ i₂ i₂'
      shape := shape₂ i₁
      d_comp_d' := by intros; apply d₂_comp_d₂ }
  d i₁ i₁' :=
    { f := fun i₂ => d₁ i₁ i₁' i₂
      comm' := by intros; apply comm }
  shape i₁ i₁' h := by
    ext i₂
    exact shape₁ i₁ i₁' h i₂
  d_comp_d' i₁ i₁' i₁'' _ _ := by ext i₂; apply d₁_comp_d₁

@[simp]
/-
**HomologicalComplex₂.ofGradedObject_toGradedObject** 是 Mathlib 中的一个引理，位于命名空间 `H
omologicalComplex₂`。
形式化陈述：ofGradedObject_toGradedObject : (ofGradedObject c₁ c₂ X d₁ d₂ shape₁ shape
₂ d₁_comp_d₁ d₂_comp_d₂ comm).toGradedObject = X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofGradedObject_toGradedObject :
    (ofGradedObject c₁ c₂ X d₁ d₂ shape₁ shape₂ d₁_comp_d₁ d₂_comp_d₂ comm).toGradedObject = X :=
  rfl

end OfGradedObject

/-- Constructor for a morphism `K ⟶ L` in the category `HomologicalComplex₂ C c₁ c₂` which
takes as inputs a morphism `f : K.toGradedObject ⟶ L.toGradedObject` and
the compatibilities with both horizontal and vertical differentials. -/
@[simps!]
/-
**HomologicalComplex₂.homMk** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex₂`。
形式化陈述：homMk {K L : HomologicalComplex₂ C c₁ c₂} (f : K.toGradedObject ⟶ L.toGrad
edObject) (comm₁ : forall i₁ i₁' i₂, c₁.Rel i₁ i₁' -> f ⟨i₁, i₂⟩ ≫ (L.d i₁ i₁').
f i₂ = (K.d i₁ i₁').f i₂ ≫ f ⟨i₁', i₂⟩) (comm₂ : forall i₁ i₂ i₂', c₂.Rel i₂ i₂'
 -> f ⟨i₁, i₂⟩ ≫ (L.X i₁).d i₂ i₂' = (K.X i₁).d i₂ i₂' ≫ f ⟨i₁, i₂'⟩) : K ⟶ L wh
ere f i₁
参数：f : K.toGradedObject ⟶ L.toGradedObject；comm₁ : forall i₁ i₁' i₂, c₁.Rel i₁ i
₁' -> f ⟨i₁, i₂⟩ ≫ (L.d i₁ i₁').f i₂ = (K.d i₁ i₁').f i₂ ≫ f ⟨i₁', i₂⟩；comm₂ : f
orall i₁ i₂ i₂', c₂.Rel i₂ i₂' -> f ⟨i₁, i₂⟩ ≫ (L.X i₁).d i₂ i₂' = (K.X i₁).d i₂
 i₂' ≫ f ⟨i₁, i₂'⟩。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for a morphism `K ⟶ L` in the category `HomologicalComplex₂ C c₁ c₂`
 which
takes as inputs a morphism `f : K.toGradedObject ⟶ L.toGradedObject` and
the compatibilities with both horizontal and vertical differentials.
-/
def homMk {K L : HomologicalComplex₂ C c₁ c₂}
    (f : K.toGradedObject ⟶ L.toGradedObject)
    (comm₁ : ∀ i₁ i₁' i₂, c₁.Rel i₁ i₁' →
      f ⟨i₁, i₂⟩ ≫ (L.d i₁ i₁').f i₂ = (K.d i₁ i₁').f i₂ ≫ f ⟨i₁', i₂⟩)
    (comm₂ : ∀ i₁ i₂ i₂', c₂.Rel i₂ i₂' →
      f ⟨i₁, i₂⟩ ≫ (L.X i₁).d i₂ i₂' = (K.X i₁).d i₂ i₂' ≫ f ⟨i₁, i₂'⟩) : K ⟶ L where
  f i₁ :=
    { f := fun i₂ => f ⟨i₁, i₂⟩
      comm' := comm₂ i₁ }
  comm' i₁ i₁' h₁ := by
    ext i₂
    exact comm₁ i₁ i₁' i₂ h₁
/-
**HomologicalComplex₂.shape_f** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex₂`。
形式化陈述：shape_f (K : HomologicalComplex₂ C c₁ c₂) (i₁ i₁' : I₁) (h : ¬ c₁.Rel i₁ i
₁') (i₂ : I₂) : (K.d i₁ i₁').f i₂ = 0
参数：K : HomologicalComplex₂ C c₁ c₂；i₁ i₁' : I₁；h : ¬ c₁.Rel i₁ i₁'；i₂ : I₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.shape`：∀ {ι : Type u_1} {V : Type u} [inst : Category
Theory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] 
{c : ComplexSh…
· 使用定理 `HomologicalComplex.zero_f`：zero_f (C D : HomologicalComplex V c) (i : ι)
 : (0 : C ⟶ D).f i = 0
-/
lemma shape_f (K : HomologicalComplex₂ C c₁ c₂) (i₁ i₁' : I₁) (h : ¬ c₁.Rel i₁ i₁') (i₂ : I₂) :
    (K.d i₁ i₁').f i₂ = 0 := by
  rw [K.shape _ _ h, zero_f]

@[reassoc (attr := simp)]
/-
**HomologicalComplex₂.d_f_comp_d_f** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex
₂`。
形式化陈述：d_f_comp_d_f (K : HomologicalComplex₂ C c₁ c₂) (i₁ i₁' i₁'' : I₁) (i₂ : I₂
) : (K.d i₁ i₁').f i₂ ≫ (K.d i₁' i₁'').f i₂ = 0
参数：K : HomologicalComplex₂ C c₁ c₂；i₁ i₁' i₁'' : I₁；i₂ : I₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HomologicalComplex.comp_f`：comp_f {C₁ C₂ C₃ : HomologicalComplex V c} (f
 : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i : ι) : (f ≫ g).f i = f.f i ≫ g.f i
· 使用定理 `HomologicalComplex.d_comp_d`：d_comp_d (C : HomologicalComplex V c) (i j 
k : ι) : C.d i j ≫ C.d j k = 0
· 使用定理 `HomologicalComplex.zero_f`：zero_f (C D : HomologicalComplex V c) (i : ι)
 : (0 : C ⟶ D).f i = 0
-/
lemma d_f_comp_d_f (K : HomologicalComplex₂ C c₁ c₂)
    (i₁ i₁' i₁'' : I₁) (i₂ : I₂) :
    (K.d i₁ i₁').f i₂ ≫ (K.d i₁' i₁'').f i₂ = 0 := by
  rw [← comp_f, d_comp_d, zero_f]

@[reassoc]
/-
**HomologicalComplex₂.d_comm** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex₂`。
形式化陈述：d_comm (K : HomologicalComplex₂ C c₁ c₂) (i₁ i₁' : I₁) (i₂ i₂' : I₂) : (K.
d i₁ i₁').f i₂ ≫ (K.X i₁').d i₂ i₂' = (K.X i₁).d i₂ i₂' ≫ (K.d i₁ i₁').f i₂'
参数：K : HomologicalComplex₂ C c₁ c₂；i₁ i₁' : I₁；i₂ i₂' : I₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.Hom.comm`：∀ {ι : Type u_1} {V : Type u} [inst : Categ
oryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
V] {c : ComplexSh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma d_comm (K : HomologicalComplex₂ C c₁ c₂) (i₁ i₁' : I₁) (i₂ i₂' : I₂) :
    (K.d i₁ i₁').f i₂ ≫ (K.X i₁').d i₂ i₂' = (K.X i₁).d i₂ i₂' ≫ (K.d i₁ i₁').f i₂' := by
  simp

@[reassoc (attr := simp)]
/-
**HomologicalComplex₂.comm_f** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex₂`。
形式化陈述：comm_f {K L : HomologicalComplex₂ C c₁ c₂} (f : K ⟶ L) (i₁ i₁' : I₁) (i₂ :
 I₂) : (f.f i₁).f i₂ ≫ (L.d i₁ i₁').f i₂ = (K.d i₁ i₁').f i₂ ≫ (f.f i₁').f i₂
参数：f : K ⟶ L；i₁ i₁' : I₁；i₂ : I₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.congr_hom`：congr_hom {C D : HomologicalComplex V c} {
f g : C ⟶ D} (w : f = g) (i : ι) : f.f i = g.f i
· 使用定理 `HomologicalComplex.Hom.comm`：∀ {ι : Type u_1} {V : Type u} [inst : Categ
oryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
V] {c : ComplexSh…
-/
lemma comm_f {K L : HomologicalComplex₂ C c₁ c₂} (f : K ⟶ L) (i₁ i₁' : I₁) (i₂ : I₂) :
    (f.f i₁).f i₂ ≫ (L.d i₁ i₁').f i₂ = (K.d i₁ i₁').f i₂ ≫ (f.f i₁').f i₂ :=
  congr_hom (f.comm i₁ i₁') i₂

/-- Flip a complex of complexes over the diagonal,
exchanging the horizontal and vertical directions.
-/
@[simps]
/-
**HomologicalComplex₂.flip** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex₂`。
形式化陈述：flip (K : HomologicalComplex₂ C c₁ c₂) : HomologicalComplex₂ C c₂ c₁ where
 X i
参数：K : HomologicalComplex₂ C c₁ c₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex₂.shape_f`：shape_f (K : HomologicalComplex₂ C c₁ c₂) (
i₁ i₁' : I₁) (h : ¬ c₁.Rel i₁ i₁') (i₂ : I₂) : (K.d i₁ i₁').f i₂ = 0

--- 原说明 ---
Flip a complex of complexes over the diagonal,
exchanging the horizontal and vertical directions.
-/
def flip (K : HomologicalComplex₂ C c₁ c₂) : HomologicalComplex₂ C c₂ c₁ where
  X i :=
    { X := fun j => (K.X j).X i
      d := fun j j' => (K.d j j').f i
      shape := fun _ _ w => K.shape_f _ _ w i }
  d i i' := { f := fun j => (K.X j).d i i' }
  shape i i' w := by
    ext j
    exact (K.X j).shape i i' w

@[simp]
/-
**HomologicalComplex₂.flip_flip** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex₂`。
形式化陈述：flip_flip (K : HomologicalComplex₂ C c₁ c₂) : K.flip.flip = K
参数：K : HomologicalComplex₂ C c₁ c₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma flip_flip (K : HomologicalComplex₂ C c₁ c₂) : K.flip.flip = K := rfl

variable (C c₁ c₂)

set_option backward.defeqAttrib.useBackward true in
/-- Flipping a complex of complexes over the diagonal, as a functor. -/
@[simps]
/-
**HomologicalComplex₂.flipFunctor** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex₂
`。
形式化陈述：flipFunctor : HomologicalComplex₂ C c₁ c₂ ⥤ HomologicalComplex₂ C c₂ c₁ wh
ere obj K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Flipping a complex of complexes over the diagonal, as a functor.
-/
def flipFunctor :
    HomologicalComplex₂ C c₁ c₂ ⥤ HomologicalComplex₂ C c₂ c₁ where
  obj K := K.flip
  map {K L} f :=
    { f := fun i =>
        { f := fun j => (f.f j).f i
          comm' := by intros; simp }
      comm' := by intros; ext; simp }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for `HomologicalComplex₂.flipEquivalence`. -/
@[simps!]
/-
**HomologicalComplex₂.flipEquivalenceUnitIso** 是 Mathlib 中的一个定义，位于命名空间 `Homologi
calComplex₂`。
形式化陈述：flipEquivalenceUnitIso : 𝟭 (HomologicalComplex₂ C c₁ c₂) ≅ flipFunctor C c
₁ c₂ ⋙ flipFunctor C c₂ c₁
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `HomologicalComplex₂.flipEquivalence`.
-/
def flipEquivalenceUnitIso :
    𝟭 (HomologicalComplex₂ C c₁ c₂) ≅ flipFunctor C c₁ c₂ ⋙ flipFunctor C c₂ c₁ :=
  NatIso.ofComponents (fun K => HomologicalComplex.Hom.isoOfComponents (fun i₁ =>
    HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
    (by simp)) (by cat_disch)) (by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for `HomologicalComplex₂.flipEquivalence`. -/
@[simps!]
/-
**HomologicalComplex₂.flipEquivalenceCounitIso** 是 Mathlib 中的一个定义，位于命名空间 `Homolo
gicalComplex₂`。
形式化陈述：flipEquivalenceCounitIso : flipFunctor C c₂ c₁ ⋙ flipFunctor C c₁ c₂ ≅ 𝟭 (
HomologicalComplex₂ C c₂ c₁)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `HomologicalComplex₂.flipEquivalence`.
-/
def flipEquivalenceCounitIso :
    flipFunctor C c₂ c₁ ⋙ flipFunctor C c₁ c₂ ≅ 𝟭 (HomologicalComplex₂ C c₂ c₁) :=
  NatIso.ofComponents (fun K => HomologicalComplex.Hom.isoOfComponents (fun i₂ =>
    HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
    (by simp)) (by cat_disch)) (by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Flipping a complex of complexes over the diagonal, as an equivalence of categories. -/
@[simps]
/-
**HomologicalComplex₂.flipEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComp
lex₂`。
形式化陈述：flipEquivalence : HomologicalComplex₂ C c₁ c₂ ≌ HomologicalComplex₂ C c₂ c
₁ where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Flipping a complex of complexes over the diagonal, as an equivalence of categori
es.
-/
def flipEquivalence :
    HomologicalComplex₂ C c₁ c₂ ≌ HomologicalComplex₂ C c₂ c₁ where
  functor := flipFunctor C c₁ c₂
  inverse := flipFunctor C c₂ c₁
  unitIso := flipEquivalenceUnitIso C c₁ c₂
  counitIso := flipEquivalenceCounitIso C c₁ c₂

variable (K : HomologicalComplex₂ C c₁ c₂)

/-- The obvious isomorphism `(K.X x₁).X x₂ ≅ (K.X y₁).X y₂` when `x₁ = y₁` and `x₂ = y₂`. -/
/-
**HomologicalComplex₂.XXIsoOfEq** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex₂`。
形式化陈述：XXIsoOfEq {x₁ y₁ : I₁} (h₁ : x₁ = y₁) {x₂ y₂ : I₂} (h₂ : x₂ = y₂) : (K.X x
₁).X x₂ ≅ (K.X y₁).X y₂
参数：h₁ : x₁ = y₁；h₂ : x₂ = y₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious isomorphism `(K.X x₁).X x₂ ≅ (K.X y₁).X y₂` when `x₁ = y₁` and `x₂ =
 y₂`.
-/
def XXIsoOfEq {x₁ y₁ : I₁} (h₁ : x₁ = y₁) {x₂ y₂ : I₂} (h₂ : x₂ = y₂) :
    (K.X x₁).X x₂ ≅ (K.X y₁).X y₂ :=
  eqToIso (by subst h₁ h₂; rfl)

@[simp]
/-
**HomologicalComplex₂.XXIsoOfEq_rfl** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComple
x₂`。
形式化陈述：XXIsoOfEq_rfl (i₁ : I₁) (i₂ : I₂) : K.XXIsoOfEq _ _ _ (rfl : i₁ = i₁) (rfl
 : i₂ = i₂) = Iso.refl _
参数：i₁ : I₁；i₂ : I₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma XXIsoOfEq_rfl (i₁ : I₁) (i₂ : I₂) :
    K.XXIsoOfEq _ _ _ (rfl : i₁ = i₁) (rfl : i₂ = i₂) = Iso.refl _ := rfl


end HomologicalComplex₂

