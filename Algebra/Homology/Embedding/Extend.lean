/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.IsSupported
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.Opposite

/-!
# The extension of a homological complex by an embedding of complex shapes

Given an embedding `e : Embedding c c'` of complex shapes,
and `K : HomologicalComplex C c`, we define `K.extend e : HomologicalComplex C c'`, and this
leads to a functor `e.extendFunctor C : HomologicalComplex C c ⥤ HomologicalComplex C c'`.

This construction first appeared in the Liquid Tensor Experiment.

-/

@[expose] public section

open CategoryTheory Category Limits ZeroObject

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

namespace HomologicalComplex

variable {C : Type*} [Category* C] [HasZeroObject C]

section

variable [HasZeroMorphisms C] (K L M : HomologicalComplex C c)
  (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

namespace extend

/-- Auxiliary definition for the `X` field of `HomologicalComplex.extend`. -/
/-
**HomologicalComplex.extend.X** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex.exte
nd`。
形式化陈述：{ι : Type u_1} →   {c : ComplexShape ι} →     {C : Type u_3} →       [inst
 : CategoryTheory.Category.{v_1, u_3} C] →         [CategoryTheory.Limits.HasZer
oObject C] →           [inst_2 : CategoryTheory.Limits.HasZeroMorphisms C] → Hom
ologicalComplex C c → Option ι → C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for the `X` field of `HomologicalComplex.extend`.
-/
noncomputable def X : Option ι → C
  | some x => K.X x
  | none => 0

/-- The isomorphism `X K i ≅ K.X j` when `i = some j`. -/
/-
**HomologicalComplex.extend.XIso** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex.e
xtend`。
形式化陈述：XIso {i : Option ι} {j : ι} (hj : i = some j) : X K i ≅ K.X j
参数：hj : i = some j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `X K i ≅ K.X j` when `i = some j`.
-/
noncomputable def XIso {i : Option ι} {j : ι} (hj : i = some j) :
    X K i ≅ K.X j := eqToIso (by subst hj; rfl)
/-
**HomologicalComplex.extend.isZero_X** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalCompl
ex.extend`。
形式化陈述：isZero_X {i : Option ι} (hi : i = none) : IsZero (X K i)
参数：hi : i = none。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.isZero_zero`：isZero_zero : IsZero (0 : C)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isZero_X {i : Option ι} (hi : i = none) :
    IsZero (X K i) := by
  subst hi
  exact Limits.isZero_zero _

/-- The canonical isomorphism `X K.op i ≅ Opposite.op (X K i)`. -/
/-
**HomologicalComplex.extend.XOpIso** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex
.extend`。
形式化陈述：XOpIso (i : Option ι) : X K.op i ≅ Opposite.op (X K i)
参数：i : Option ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `X K.op i ≅ Opposite.op (X K i)`.
-/
noncomputable def XOpIso (i : Option ι) : X K.op i ≅ Opposite.op (X K i) :=
  match i with
  | some _ => Iso.refl _
  | none => IsZero.iso (isZero_X _ rfl) (isZero_X K rfl).op

/-- Auxiliary definition for the `d` field of `HomologicalComplex.extend`. -/
/-
**HomologicalComplex.extend.d** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex.exte
nd`。
形式化陈述：{ι : Type u_1} →   {c : ComplexShape ι} →     {C : Type u_3} →       [inst
 : CategoryTheory.Category.{v_1, u_3} C] →         [inst_1 : CategoryTheory.Limi
ts.HasZeroObject C] →           [inst_2 : CategoryTheory.Limits.HasZeroMorphisms
 C] →             (K : HomologicalComplex C c) →               (i j : Option ι) 
→ HomologicalComplex.extend.X K i ⟶ HomologicalComplex.extend.X K j
参数：K : HomologicalComplex C c；i j : Option ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for the `d` field of `HomologicalComplex.extend`.
-/
noncomputable def d : ∀ (i j : Option ι), extend.X K i ⟶ extend.X K j
  | none, _ => 0
  | some i, some j => K.d i j
  | some _, none => 0
/-
**HomologicalComplex.extend.d_none_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Homologica
lComplex.extend`。
形式化陈述：d_none_eq_zero (i j : Option ι) (hi : i = none) : d K i j = 0
参数：i j : Option ι；hi : i = none。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma d_none_eq_zero (i j : Option ι) (hi : i = none) :
    d K i j = 0 := by subst hi; rfl
/-
**HomologicalComplex.extend.d_none_eq_zero'** 是 Mathlib 中的一个引理，位于命名空间 `Homologic
alComplex.extend`。
形式化陈述：d_none_eq_zero' (i j : Option ι) (hj : j = none) : d K i j = 0
参数：i j : Option ι；hj : j = none。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma d_none_eq_zero' (i j : Option ι) (hj : j = none) :
    d K i j = 0 := by subst hj; cases i <;> rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**HomologicalComplex.extend.d_eq** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex.e
xtend`。
形式化陈述：d_eq {i j : Option ι} {a b : ι} (hi : i = some a) (hj : j = some b) : d K 
i j = (XIso K hi).hom ≫ K.d a b ≫ (XIso K hj).inv
参数：hi : i = some a；hj : j = some b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma d_eq {i j : Option ι} {a b : ι} (hi : i = some a) (hj : j = some b) :
    d K i j = (XIso K hi).hom ≫ K.d a b ≫ (XIso K hj).inv := by
  subst hi hj
  simp [XIso, X, d]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**HomologicalComplex.extend.XOpIso_hom_d_op** 是 Mathlib 中的一个引理，位于命名空间 `Homologic
alComplex.extend`。
形式化陈述：XOpIso_hom_d_op (i j : Option ι) : (XOpIso K i).hom ≫ (d K j i).op = d K.o
p i j ≫ (XOpIso K j).hom
参数：i j : Option ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomologicalComplex.extend.d_none_eq_zero'`：d_none_eq_zero' (i j : Option
 ι) (hj : j = none) : d K i j = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `HomologicalComplex.extend.d_none_eq_zero`：d_none_eq_zero (i j : Option ι
) (hi : i = none) : d K i j = 0
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用引理 `HomologicalComplex.extend.d_eq`：d_eq {i j : Option ι} {a b : ι} (hi : i 
= some a) (hj : j = some b) : d K i j = (XIso K hi).hom ≫ K.d a b ≫ (XIso K hj).
inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma XOpIso_hom_d_op (i j : Option ι) :
    (XOpIso K i).hom ≫ (d K j i).op =
      d K.op i j ≫ (XOpIso K j).hom :=
  match i, j with
  | none, _ => by
      simp only [d_none_eq_zero, d_none_eq_zero', comp_zero, zero_comp, op_zero]
  | some i, some j => by
      dsimp [XOpIso]
      simp only [d_eq _ rfl rfl, op_comp, assoc, id_comp, comp_id]
      rfl
  | some _, none => by
      simp only [d_none_eq_zero, d_none_eq_zero', comp_zero, zero_comp, op_zero]

variable {K L}

/-- Auxiliary definition for `HomologicalComplex.extendMap`. -/
/-
**HomologicalComplex.extend.mapX** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex.e
xtend`。
形式化陈述：{ι : Type u_1} →   {c : ComplexShape ι} →     {C : Type u_3} →       [inst
 : CategoryTheory.Category.{v_1, u_3} C] →         [inst_1 : CategoryTheory.Limi
ts.HasZeroObject C] →           [inst_2 : CategoryTheory.Limits.HasZeroMorphisms
 C] →             {K L : HomologicalComplex C c} →               (K ⟶ L) → (i : 
Option ι) → HomologicalComplex.extend.X K i ⟶ HomologicalComplex.extend.X L i
参数：K ⟶ L；i : Option ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `HomologicalComplex.extendMap`.
-/
noncomputable def mapX : ∀ (i : Option ι), X K i ⟶ X L i
  | some i => φ.f i
  | none => 0

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**HomologicalComplex.extend.mapX_some** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComp
lex.extend`。
形式化陈述：mapX_some {i : Option ι} {a : ι} (hi : i = some a) : mapX φ i = (XIso K hi
).hom ≫ φ.f a ≫ (XIso L hi).inv
参数：hi : i = some a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma mapX_some {i : Option ι} {a : ι} (hi : i = some a) :
    mapX φ i = (XIso K hi).hom ≫ φ.f a ≫ (XIso L hi).inv := by
  subst hi
  dsimp [XIso, X]
  rw [id_comp, comp_id]
  rfl
/-
**HomologicalComplex.extend.mapX_none** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComp
lex.extend`。
形式化陈述：mapX_none {i : Option ι} (hi : i = none) : mapX φ i = 0
参数：hi : i = none。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma mapX_none {i : Option ι} (hi : i = none) :
    mapX φ i = 0 := by subst hi; rfl

end extend

/-- Given `K : HomologicalComplex C c` and `e : c.Embedding c'`,
this is the extension of `K` in `HomologicalComplex C c'`: it is
zero in the degrees that are not in the image of `e.f`. -/
/-
**HomologicalComplex.extend** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：extend : HomologicalComplex C c' where X i'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `K : HomologicalComplex C c` and `e : c.Embedding c'`,
this is the extension of `K` in `HomologicalComplex C c'`: it is
zero in the degrees that are not in the image of `e.f`.
-/
noncomputable def extend : HomologicalComplex C c' where
  X i' := extend.X K (e.r i')
  d i' j' := extend.d K (e.r i') (e.r j')
  shape i' j' h := by
    obtain hi' | ⟨i, hi⟩ := (e.r i').eq_none_or_eq_some
    · rw [extend.d_none_eq_zero K _ _ hi']
    · obtain hj' | ⟨j, hj⟩ := (e.r j').eq_none_or_eq_some
      · rw [extend.d_none_eq_zero' K _ _ hj']
      · rw [extend.d_eq K hi hj, K.shape, zero_comp, comp_zero]
        obtain rfl := e.f_eq_of_r_eq_some hi
        obtain rfl := e.f_eq_of_r_eq_some hj
        intro hij
        exact h (e.rel hij)
  d_comp_d' i' j' k' _ _ := by
    obtain hi' | ⟨i, hi⟩ := (e.r i').eq_none_or_eq_some
    · rw [extend.d_none_eq_zero K _ _ hi', zero_comp]
    · obtain hj' | ⟨j, hj⟩ := (e.r j').eq_none_or_eq_some
      · rw [extend.d_none_eq_zero K _ _ hj', comp_zero]
      · obtain hk' | ⟨k, hk⟩ := (e.r k').eq_none_or_eq_some
        · rw [extend.d_none_eq_zero' K _ _ hk', comp_zero]
        · rw [extend.d_eq K hi hj, extend.d_eq K hj hk, assoc, assoc,
            Iso.inv_hom_id_assoc, K.d_comp_d_assoc, zero_comp, comp_zero]

/-- The isomorphism `(K.extend e).X i' ≅ K.X i` when `e.f i = i'`. -/
/-
**HomologicalComplex.extendXIso** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：extendXIso {i' : ι'} {i : ι} (h : e.f i = i') : (K.extend e).X i' ≅ K.X i
参数：h : e.f i = i'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `ComplexShape.Embedding.r_eq_some`：r_eq_some {i : ι} {i' : ι'} (hi : e.f 
i = i') : e.r i' = some i

--- 原说明 ---
The isomorphism `(K.extend e).X i' ≅ K.X i` when `e.f i = i'`.
-/
noncomputable def extendXIso {i' : ι'} {i : ι} (h : e.f i = i') :
    (K.extend e).X i' ≅ K.X i :=
  extend.XIso K (e.r_eq_some h)
/-
**HomologicalComplex.isZero_extend_X'** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComp
lex`。
形式化陈述：isZero_extend_X' (i' : ι') (hi' : e.r i' = none) : IsZero ((K.extend e).X 
i')
参数：i' : ι'；hi' : e.r i' = none。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.extend.isZero_X`：isZero_X {i : Option ι} (hi : i = no
ne) : IsZero (X K i)
-/
lemma isZero_extend_X' (i' : ι') (hi' : e.r i' = none) :
    IsZero ((K.extend e).X i') :=
  extend.isZero_X K hi'
/-
**HomologicalComplex.isZero_extend_X** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalCompl
ex`。
形式化陈述：isZero_extend_X (i' : ι') (hi' : forall i, e.f i != i') : IsZero ((K.exten
d e).X i')
参数：i' : ι'；hi' : forall i, e.f i != i'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.isZero_extend_X'`：isZero_extend_X' (i' : ι') (hi' : e
.r i' = none) : IsZero ((K.extend e).X i')
· 使用引理 `ComplexShape.Embedding.r_eq_none`：r_eq_none (i' : ι') (hi : forall i, e.
f i != i') : e.r i' = none
-/
lemma isZero_extend_X (i' : ι') (hi' : ∀ i, e.f i ≠ i') :
    IsZero ((K.extend e).X i') :=
  K.isZero_extend_X' e i' (ComplexShape.Embedding.r_eq_none e i' hi')
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (K.extend e).IsStrictlySupported e where
  isZero i' hi' := K.isZero_extend_X e i' hi'
/-
**HomologicalComplex.extend_d_eq** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`。
形式化陈述：extend_d_eq {i' j' : ι'} {i j : ι} (hi : e.f i = i') (hj : e.f j = j') : (
K.extend e).d i' j' = (K.extendXIso e hi).hom ≫ K.d i j ≫ (K.extendXIso e hj).in
v
参数：hi : e.f i = i'；hj : e.f j = j'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.extend.d_eq`：d_eq {i j : Option ι} {a b : ι} (hi : i 
= some a) (hj : j = some b) : d K i j = (XIso K hi).hom ≫ K.d a b ≫ (XIso K hj).
inv
· 使用引理 `ComplexShape.Embedding.r_eq_some`：r_eq_some {i : ι} {i' : ι'} (hi : e.f 
i = i') : e.r i' = some i
-/
lemma extend_d_eq {i' j' : ι'} {i j : ι} (hi : e.f i = i') (hj : e.f j = j') :
    (K.extend e).d i' j' = (K.extendXIso e hi).hom ≫ K.d i j ≫
      (K.extendXIso e hj).inv := by
  apply extend.d_eq
/-
**HomologicalComplex.extend_d_from_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Homologica
lComplex`。
形式化陈述：extend_d_from_eq_zero (i' j' : ι') (i : ι) (hi : e.f i = i') (hi' : ¬ c.Re
l i (c.next i)) : (K.extend e).d i' j' = 0
参数：i' j' : ι'；i : ι；hi : e.f i = i'；hi' : ¬ c.Rel i (c.next i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Option.eq_none_or_eq_some`：∀ {α : Type u_1} (a : Option α), a = none ∨ ∃
 x, a = some x
· 使用引理 `HomologicalComplex.extend.d_none_eq_zero'`：d_none_eq_zero' (i j : Option
 ι) (hj : j = none) : d K i j = 0
· 使用引理 `ComplexShape.Embedding.f_eq_of_r_eq_some`：f_eq_of_r_eq_some {i : ι} {i' 
: ι'} (hi : e.r i' = some i) : e.f i = i'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomologicalComplex.extend_d_eq`：extend_d_eq {i' j' : ι'} {i j : ι} (hi :
 e.f i = i') (hj : e.f j = j') : (K.extend e).d i' j' = (K.extendXIso e hi).hom 
≫ K.d i j ≫ (K.exten…
· 使用定理 `HomologicalComplex.shape`：∀ {ι : Type u_1} {V : Type u} [inst : Category
Theory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] 
{c : ComplexSh…
· 使用定理 `ComplexShape.next_eq'`：next_eq' (c : ComplexShape ι) {i j : ι} (h : c.Re
l i j) : c.next i = j
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
-/
lemma extend_d_from_eq_zero (i' j' : ι') (i : ι) (hi : e.f i = i') (hi' : ¬ c.Rel i (c.next i)) :
    (K.extend e).d i' j' = 0 := by
  obtain hj' | ⟨j, hj⟩ := (e.r j').eq_none_or_eq_some
  · exact extend.d_none_eq_zero' _ _ _ hj'
  · rw [extend_d_eq K e hi (e.f_eq_of_r_eq_some hj), K.shape, zero_comp, comp_zero]
    intro hij
    obtain rfl := c.next_eq' hij
    exact hi' hij
/-
**HomologicalComplex.extend_d_to_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalC
omplex`。
形式化陈述：extend_d_to_eq_zero (i' j' : ι') (j : ι) (hj : e.f j = j') (hj' : ¬ c.Rel 
(c.prev j) j) : (K.extend e).d i' j' = 0
参数：i' j' : ι'；j : ι；hj : e.f j = j'；hj' : ¬ c.Rel (c.prev j) j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Option.eq_none_or_eq_some`：∀ {α : Type u_1} (a : Option α), a = none ∨ ∃
 x, a = some x
· 使用引理 `HomologicalComplex.extend.d_none_eq_zero`：d_none_eq_zero (i j : Option ι
) (hi : i = none) : d K i j = 0
· 使用引理 `ComplexShape.Embedding.f_eq_of_r_eq_some`：f_eq_of_r_eq_some {i : ι} {i' 
: ι'} (hi : e.r i' = some i) : e.f i = i'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomologicalComplex.extend_d_eq`：extend_d_eq {i' j' : ι'} {i j : ι} (hi :
 e.f i = i') (hj : e.f j = j') : (K.extend e).d i' j' = (K.extendXIso e hi).hom 
≫ K.d i j ≫ (K.exten…
· 使用定理 `HomologicalComplex.shape`：∀ {ι : Type u_1} {V : Type u} [inst : Category
Theory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] 
{c : ComplexSh…
· 使用定理 `ComplexShape.prev_eq'`：∀ {ι : Type u_1} (c : ComplexShape ι) {i j : ι}, 
c.Rel j i → c.prev i = j
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
-/
lemma extend_d_to_eq_zero (i' j' : ι') (j : ι) (hj : e.f j = j') (hj' : ¬ c.Rel (c.prev j) j) :
    (K.extend e).d i' j' = 0 := by
  obtain hi' | ⟨i, hi⟩ := (e.r i').eq_none_or_eq_some
  · exact extend.d_none_eq_zero _ _ _ hi'
  · rw [extend_d_eq K e (e.f_eq_of_r_eq_some hi) hj, K.shape, zero_comp, comp_zero]
    intro hij
    obtain rfl := c.prev_eq' hij
    exact hj' hij

variable {K L M}

set_option backward.isDefEq.respectTransparency false in
/-- Given an embedding `e : c.Embedding c'` of complexes shapes, this is the
morphism `K.extend e ⟶ L.extend e` induced by a morphism `K ⟶ L` in
`HomologicalComplex C c`. -/
/-
**HomologicalComplex.extendMap** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：extendMap : K.extend e ⟶ L.extend e where f _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an embedding `e : c.Embedding c'` of complexes shapes, this is the
morphism `K.extend e ⟶ L.extend e` induced by a morphism `K ⟶ L` in
`HomologicalComplex C c`.
-/
noncomputable def extendMap : K.extend e ⟶ L.extend e where
  f _ := extend.mapX φ _
  comm' i' j' _ := by
    by_cases hi : ∃ i, e.f i = i'
    · obtain ⟨i, hi⟩ := hi
      by_cases hj : ∃ j, e.f j = j'
      · obtain ⟨j, hj⟩ := hj
        rw [K.extend_d_eq e hi hj, L.extend_d_eq e hi hj,
          extend.mapX_some φ (e.r_eq_some hi),
          extend.mapX_some φ (e.r_eq_some hj)]
        simp only [extendXIso, assoc, Iso.inv_hom_id_assoc, Hom.comm_assoc]
      · have hj' := e.r_eq_none j' (fun j'' hj'' => hj ⟨j'', hj''⟩)
        dsimp [extend]
        rw [extend.d_none_eq_zero' _ _ _ hj', extend.d_none_eq_zero' _ _ _ hj',
          comp_zero, zero_comp]
    · have hi' := e.r_eq_none i' (fun i'' hi'' => hi ⟨i'', hi''⟩)
      dsimp [extend]
      rw [extend.d_none_eq_zero _ _ _ hi', extend.d_none_eq_zero _ _ _ hi',
        comp_zero, zero_comp]
/-
**HomologicalComplex.extendMap_f** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`。
形式化陈述：extendMap_f {i : ι} {i' : ι'} (h : e.f i = i') : (extendMap φ e).f i' = (e
xtendXIso K e h).hom ≫ φ.f i ≫ (extendXIso L e h).inv
参数：h : e.f i = i'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ComplexShape.Embedding.r_eq_some`：r_eq_some {i : ι} {i' : ι'} (hi : e.f 
i = i') : e.r i' = some i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomologicalComplex.extend.mapX_some`：mapX_some {i : Option ι} {a : ι} (h
i : i = some a) : mapX φ i = (XIso K hi).hom ≫ φ.f a ≫ (XIso L hi).inv
-/
lemma extendMap_f {i : ι} {i' : ι'} (h : e.f i = i') :
    (extendMap φ e).f i' =
      (extendXIso K e h).hom ≫ φ.f i ≫ (extendXIso L e h).inv := by
  dsimp [extendMap]
  rw [extend.mapX_some φ (e.r_eq_some h)]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**HomologicalComplex.extendMap_f_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalC
omplex`。
形式化陈述：extendMap_f_eq_zero (i' : ι') (hi' : forall i, e.f i != i') : (extendMap φ
 e).f i' = 0
参数：i' : ι'；hi' : forall i, e.f i != i'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomologicalComplex.extend.mapX_none`：mapX_none {i : Option ι} (hi : i = 
none) : mapX φ i = 0
· 使用引理 `ComplexShape.Embedding.r_eq_none`：r_eq_none (i' : ι') (hi : forall i, e.
f i != i') : e.r i' = none
-/
lemma extendMap_f_eq_zero (i' : ι') (hi' : ∀ i, e.f i ≠ i') :
    (extendMap φ e).f i' = 0 := by
  dsimp [extendMap]
  rw [extend.mapX_none φ (e.r_eq_none i' hi')]

@[reassoc, simp]
/-
**HomologicalComplex.extendMap_comp** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComple
x`。
形式化陈述：extendMap_comp : extendMap (φ ≫ φ') e = extendMap φ e ≫ extendMap φ' e
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
· 使用引理 `HomologicalComplex.extendMap_f`：extendMap_f {i : ι} {i' : ι'} (h : e.f i
 = i') : (extendMap φ e).f i' = (extendXIso K e h).hom ≫ φ.f i ≫ (extendXIso L e
 h).inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `HomologicalComplex.extendMap_f_eq_zero`：extendMap_f_eq_zero (i' : ι') (h
i' : forall i, e.f i != i') : (extendMap φ e).f i' = 0
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
-/
lemma extendMap_comp :
    extendMap (φ ≫ φ') e = extendMap φ e ≫ extendMap φ' e := by
  ext i'
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    simp [extendMap_f _ e hi]
  · simp [extendMap_f_eq_zero _ e i' (fun i hi => hi' ⟨i, hi⟩)]

variable (K L M)
/-
**HomologicalComplex.extendMap_id_f** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComple
x`。
形式化陈述：extendMap_id_f (i' : ι') : (extendMap (𝟙 K) e).f i' = 𝟙 _
参数：i' : ι'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomologicalComplex.extendMap_f`：extendMap_f {i : ι} {i' : ι'} (h : e.f i
 = i') : (extendMap φ e).f i' = (extendXIso K e h).hom ≫ φ.f i ≫ (extendXIso L e
 h).inv
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_src`：eq_of_src (hX : IsZero X) (f g :
 X ⟶ Y) : f = g
· 使用引理 `HomologicalComplex.isZero_extend_X`：isZero_extend_X (i' : ι') (hi' : for
all i, e.f i != i') : IsZero ((K.extend e).X i')
-/
lemma extendMap_id_f (i' : ι') : (extendMap (𝟙 K) e).f i' = 𝟙 _ := by
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    simp [extendMap_f _ e hi]
  · apply (K.isZero_extend_X e i' (fun i hi => hi' ⟨i, hi⟩)).eq_of_src

@[simp]
/-
**HomologicalComplex.extendMap_id** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`
。
形式化陈述：extendMap_id : extendMap (𝟙 K) e = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用引理 `HomologicalComplex.extendMap_id_f`：extendMap_id_f (i' : ι') : (extendMap
 (𝟙 K) e).f i' = 𝟙 _
-/
lemma extendMap_id : extendMap (𝟙 K) e = 𝟙 _ := by
  ext
  simpa using extendMap_id_f _ _ _

@[simp]
/-
**HomologicalComplex.extendMap_zero** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComple
x`。
形式化陈述：extendMap_zero : extendMap (0 : K ⟶ L) e = 0
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
· 使用引理 `HomologicalComplex.extendMap_f`：extendMap_f {i : ι} {i' : ι'} (h : e.f i
 = i') : (extendMap φ e).f i' = (extendXIso K e h).hom ≫ φ.f i ≫ (extendXIso L e
 h).inv
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_src`：eq_of_src (hX : IsZero X) (f g :
 X ⟶ Y) : f = g
· 使用引理 `HomologicalComplex.isZero_extend_X`：isZero_extend_X (i' : ι') (hi' : for
all i, e.f i != i') : IsZero ((K.extend e).X i')
-/
lemma extendMap_zero : extendMap (0 : K ⟶ L) e = 0 := by
  ext i'
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    simp [extendMap_f _ e hi]
  · apply (K.isZero_extend_X e i' (fun i hi => hi' ⟨i, hi⟩)).eq_of_src

/-- The canonical isomorphism `K.op.extend e.op ≅ (K.extend e).op`. -/
/-
**HomologicalComplex.extendOpIso** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：extendOpIso : K.op.extend e.op ≅ (K.extend e).op
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `K.op.extend e.op ≅ (K.extend e).op`.
-/
noncomputable def extendOpIso : K.op.extend e.op ≅ (K.extend e).op :=
  Hom.isoOfComponents (fun _ ↦ extend.XOpIso _ _) (fun _ _ _ ↦
    extend.XOpIso_hom_d_op _ _ _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**HomologicalComplex.extend_op_d** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`。
形式化陈述：extend_op_d (i' j' : ι') : (K.op.extend e.op).d i' j' = (K.extendOpIso e).
hom.f i' ≫ ((K.extend e).d j' i').op ≫ (K.extendOpIso e).inv.f j'
参数：i' j' : ι'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.Hom.comm`：∀ {ι : Type u_1} {V : Type u} [inst : Categ
oryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
V] {c : ComplexSh…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HomologicalComplex.comp_f_assoc`：∀ {ι : Type u_1} {V : Type u} [inst : C
ategoryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphi
sms V] {c : ComplexSh…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `HomologicalComplex.id_f`：id_f (C : HomologicalComplex V c) (i : ι) : Hom
.f (𝟙 C) i = 𝟙 (C.X i)
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma extend_op_d (i' j' : ι') :
    (K.op.extend e.op).d i' j' =
      (K.extendOpIso e).hom.f i' ≫ ((K.extend e).d j' i').op ≫
        (K.extendOpIso e).inv.f j' := by
  have := (K.extendOpIso e).inv.comm i' j'
  dsimp at this
  rw [← this, ← comp_f_assoc, Iso.hom_inv_id, id_f, id_comp]

end

@[simp]
/-
**HomologicalComplex.extendMap_add** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex
`。
形式化陈述：extendMap_add [Preadditive C] {K L : HomologicalComplex C c} (φ φ' : K ⟶ L
) (e : c.Embedding c') : extendMap (φ + φ' : K ⟶ L) e = extendMap φ e + extendMa
p φ' e
参数：φ φ' : K ⟶ L；e : c.Embedding c'。
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
· 使用引理 `HomologicalComplex.extendMap_f`：extendMap_f {i : ι} {i' : ι'} (h : e.f i
 = i') : (extendMap φ e).f i' = (extendXIso K e h).hom ≫ φ.f i ≫ (extendXIso L e
 h).inv
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_src`：eq_of_src (hX : IsZero X) (f g :
 X ⟶ Y) : f = g
· 使用引理 `HomologicalComplex.isZero_extend_X`：isZero_extend_X (i' : ι') (hi' : for
all i, e.f i != i') : IsZero ((K.extend e).X i')
-/
lemma extendMap_add [Preadditive C] {K L : HomologicalComplex C c} (φ φ' : K ⟶ L)
    (e : c.Embedding c') : extendMap (φ + φ' : K ⟶ L) e = extendMap φ e + extendMap φ' e := by
  ext i'
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    simp [extendMap_f _ e hi]
  · apply (K.isZero_extend_X e i' (fun i hi => hi' ⟨i, hi⟩)).eq_of_src

section

variable [HasZeroMorphisms C] [DecidableEq ι]
  (e : c.Embedding c') (X : C)

@[simp]
/-
**HomologicalComplex.extend_single_d** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalCompl
ex`。
形式化陈述：extend_single_d (i : ι) (j' k' : ι') : (((single C c i).obj X).extend e).d
 j' k' = 0
参数：i : ι；j' k' : ι'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomologicalComplex.extend_d_eq`：extend_d_eq {i' j' : ι'} {i j : ι} (hi :
 e.f i = i') (hj : e.f j = j') : (K.extend e).d i' j' = (K.extendXIso e hi).hom 
≫ K.d i j ≫ (K.exten…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_tgt`：eq_of_tgt (hX : IsZero X) (f g :
 Y ⟶ X) : f = g
· 使用引理 `HomologicalComplex.isZero_extend_X`：isZero_extend_X (i' : ι') (hi' : for
all i, e.f i != i') : IsZero ((K.extend e).X i')
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_src`：eq_of_src (hX : IsZero X) (f g :
 X ⟶ Y) : f = g
-/
lemma extend_single_d (i : ι) (j' k' : ι') :
    (((single C c i).obj X).extend e).d j' k' = 0 := by
  by_cases hj : ∃ j, e.f j = j'
  · obtain ⟨j, rfl⟩ := hj
    by_cases hk : ∃ k, e.f k = k'
    · obtain ⟨k, rfl⟩ := hk
      simp [extend_d_eq _ _ rfl rfl]
    · exact IsZero.eq_of_tgt (isZero_extend_X _ _ _ (by tauto)) _ _
  · exact IsZero.eq_of_src (isZero_extend_X _ _ _ (by tauto)) _ _

variable [DecidableEq ι'] (i : ι) (i' : ι')

/-- The extension of a single complex is a single complex. -/
/-
**HomologicalComplex.extendSingleIso** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalCompl
ex`。
形式化陈述：extendSingleIso (h : e.f i = i') : ((single C c i).obj X).extend e ≅ (sing
le C c' i').obj X where hom
参数：h : e.f i = i'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The extension of a single complex is a single complex.
-/
noncomputable def extendSingleIso (h : e.f i = i') :
    ((single C c i).obj X).extend e ≅ (single C c' i').obj X where
  hom :=
    mkHomToSingle
      ((((single C c i).obj X).extendXIso e h).hom ≫ (singleObjXSelf c i X).hom) (by simp)
  inv :=
    mkHomFromSingle
      ((singleObjXSelf c i X).inv ≫ (((single C c i).obj X).extendXIso e h).inv) (by simp)
  hom_inv_id := by
    ext j'
    by_cases hj : ∃ j, e.f j = j'
    · obtain ⟨j, hj⟩ := hj
      by_cases hij : j = i
      · obtain rfl : i' = j' := by rw [← hj, hij, h]
        simp
      · exact ((isZero_single_obj_X _ _ _ _ hij).of_iso
          (((single C c i).obj X).extendXIso e hj)).eq_of_src _ _
    · exact IsZero.eq_of_src (isZero_extend_X _ _ _ (by tauto)) _ _

@[reassoc]
/-
**HomologicalComplex.extendSingleIso_hom_f** 是 Mathlib 中的一个引理，位于命名空间 `Homologica
lComplex`。
形式化陈述：extendSingleIso_hom_f (h : e.f i = i') : (extendSingleIso e X i i' h).hom.
f i' = (((single C c i).obj X).extendXIso e h).hom ≫ (singleObjXSelf c i X).hom 
≫ (singleObjXSelf c' i' X).inv
参数：h : e.f i = i'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomologicalComplex.mkHomToSingle_f`：mkHomToSingle_f {K : HomologicalComp
lex V c} {j : ι} {A : V} (φ : K.X j ⟶ A) (hφ : forall (i : ι), c.Rel i j -> K.d 
i j ≫ φ = 0) : (mkHomToS…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma extendSingleIso_hom_f (h : e.f i = i') :
    (extendSingleIso e X i i' h).hom.f i' =
      (((single C c i).obj X).extendXIso e h).hom ≫ (singleObjXSelf c i X).hom ≫
        (singleObjXSelf c' i' X).inv := by
  simp [extendSingleIso]

@[reassoc]
/-
**HomologicalComplex.extendSingleIso_inv_f** 是 Mathlib 中的一个引理，位于命名空间 `Homologica
lComplex`。
形式化陈述：extendSingleIso_inv_f (h : e.f i = i') : (extendSingleIso e X i i' h).inv.
f i' = (singleObjXSelf c' i' X).hom ≫ (singleObjXSelf c i X).inv ≫ (((single C c
 i).obj X).extendXIso e h).inv
参数：h : e.f i = i'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomologicalComplex.mkHomFromSingle_f`：mkHomFromSingle_f {K : Homological
Complex V c} {j : ι} {A : V} (φ : A ⟶ K.X j) (hφ : forall (k : ι), c.Rel j k -> 
φ ≫ K.d j k = 0) : (mkHomF…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma extendSingleIso_inv_f (h : e.f i = i') :
    (extendSingleIso e X i i' h).inv.f i' =
      (singleObjXSelf c' i' X).hom ≫ (singleObjXSelf c i X).inv ≫
        (((single C c i).obj X).extendXIso e h).inv := by
  simp [extendSingleIso]

end

/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasZeroMorphisms C] (e : c.Embedding c') (K : HomologicalComplex C c)
    [∀ i, Projective (K.X i)] (i' : ι') : Projective ((K.extend e).X i') := by
  by_cases! hi' : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    exact Projective.of_iso (K.extendXIso e hi).symm inferInstance
  · exact (isZero_extend_X K e i' hi').projective
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasZeroMorphisms C] (e : c.Embedding c') (K : HomologicalComplex C c)
    [∀ i, Injective (K.X i)] (i' : ι') : Injective ((K.extend e).X i') := by
  by_cases! hi' : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    exact Injective.of_iso (K.extendXIso e hi).symm inferInstance
  · exact (isZero_extend_X K e i' hi').injective

end HomologicalComplex

namespace ComplexShape.Embedding

variable (e : Embedding c c') (C : Type*) [Category* C] [HasZeroObject C]

/-- Given an embedding `e : c.Embedding c'` of complex shapes, this is
the functor `HomologicalComplex C c ⥤ HomologicalComplex C c'` which
extend complexes along `e`: the extended complexes are zero
in the degrees that are not in the image of `e.f`. -/
@[simps]
/-
**ComplexShape.Embedding.extendFunctor** 是 Mathlib 中的一个定义，位于命名空间 `ComplexShape.E
mbedding`。
形式化陈述：extendFunctor [HasZeroMorphisms C] : HomologicalComplex C c ⥤ HomologicalC
omplex C c' where obj K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an embedding `e : c.Embedding c'` of complex shapes, this is
the functor `HomologicalComplex C c ⥤ HomologicalComplex C c'` which
extend complexes along `e`: the extended complexes are zero
in the degrees that are not in the image of `e.f`.
-/
noncomputable def extendFunctor [HasZeroMorphisms C] :
    HomologicalComplex C c ⥤ HomologicalComplex C c' where
  obj K := K.extend e
  map φ := HomologicalComplex.extendMap φ e
/-
**ComplexShape.Embedding.** 是 Mathlib 中的一个实例，位于命名空间 `ComplexShape.Embedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasZeroMorphisms C] : (e.extendFunctor C).PreservesZeroMorphisms where
/-
**ComplexShape.Embedding.** 是 Mathlib 中的一个实例，位于命名空间 `ComplexShape.Embedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preadditive C] : (e.extendFunctor C).Additive where

set_option backward.defeqAttrib.useBackward true in
/-- The extension functor attached to an embedding of complex shapes is fully faithful. -/
/-
**ComplexShape.Embedding.fullyFaithfulExtendFunctor** 是 Mathlib 中的一个定义，位于命名空间 `C
omplexShape.Embedding`。
形式化陈述：fullyFaithfulExtendFunctor [HasZeroMorphisms C] : (e.extendFunctor C).Full
yFaithful where preimage {K L} φ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The extension functor attached to an embedding of complex shapes is fully faithf
ul.
-/
noncomputable def fullyFaithfulExtendFunctor [HasZeroMorphisms C] :
    (e.extendFunctor C).FullyFaithful where
  preimage {K L} φ :=
    { f i := (K.extendXIso e rfl).inv ≫ φ.f (e.f i) ≫ (L.extendXIso e rfl).hom
      comm' i j h := by
        have := φ.comm (e.f i) (e.f j)
        simp only [extendFunctor_obj, K.extend_d_eq e rfl rfl, L.extend_d_eq e rfl rfl] at this
        simp [← cancel_mono (L.extendXIso e rfl).inv, Category.assoc, this] }
  map_preimage {K L} φ := by
    ext i'
    by_cases hi' : ∃ i, e.f i = i'
    · obtain ⟨i, rfl⟩ := hi'
      simp [HomologicalComplex.extendMap_f _ _ rfl]
    · exact (K.isZero_extend_X _ _ (by tauto)).eq_of_src _ _
  preimage_map {K L} f := by
    ext i
    simp [HomologicalComplex.extendMap_f _ _ rfl]
/-
**ComplexShape.Embedding.** 是 Mathlib 中的一个实例，位于命名空间 `ComplexShape.Embedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasZeroMorphisms C] : (e.extendFunctor C).Faithful :=
    (e.fullyFaithfulExtendFunctor C).faithful
/-
**ComplexShape.Embedding.** 是 Mathlib 中的一个实例，位于命名空间 `ComplexShape.Embedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasZeroMorphisms C] : (e.extendFunctor C).Full :=
    (e.fullyFaithfulExtendFunctor C).full

end ComplexShape.Embedding

