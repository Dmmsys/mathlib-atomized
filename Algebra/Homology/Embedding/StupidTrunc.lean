/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Embedding.IsSupported
public import Mathlib.Algebra.Homology.Embedding.Restriction

/-!
# The stupid truncation of homological complexes

Given an embedding `e : c.Embedding c'` of complex shapes, we define
a functor `stupidTruncFunctor : HomologicalComplex C c' ⥤ HomologicalComplex C c'`
which sends `K` to `K.stupidTrunc e` which is defined as `(K.restriction e).extend e`.

## TODO (@joelriou)
* define the inclusion `e.stupidTruncFunctor C ⟶ 𝟭 _` when `[e.IsTruncGE]`;
* define the projection `𝟭 _ ⟶ e.stupidTruncFunctor C` when `[e.IsTruncLE]`.

-/

@[expose] public section

open CategoryTheory Category Limits ZeroObject

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

namespace HomologicalComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

variable (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
  (e : c.Embedding c') [e.IsRelIff]

/-- The stupid truncation of a complex `K : HomologicalComplex C c'` relatively to
an embedding `e : c.Embedding c'` of complex shapes. -/
/-
**HomologicalComplex.stupidTrunc** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：stupidTrunc : HomologicalComplex C c'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The stupid truncation of a complex `K : HomologicalComplex C c'` relatively to
an embedding `e : c.Embedding c'` of complex shapes.
-/
noncomputable def stupidTrunc : HomologicalComplex C c' := ((K.restriction e).extend e)
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsStrictlySupported (K.stupidTrunc e) e := by
  dsimp [stupidTrunc]
  infer_instance

/-- The isomorphism `(K.stupidTrunc e).X i' ≅ K.X i'` when `i` is in the image of `e.f`. -/
/-
**HomologicalComplex.stupidTruncXIso** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalCompl
ex`。
形式化陈述：stupidTruncXIso {i : ι} {i' : ι'} (hi' : e.f i = i') : (K.stupidTrunc e).X
 i' ≅ K.X i'
参数：hi' : e.f i = i'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `(K.stupidTrunc e).X i' ≅ K.X i'` when `i` is in the image of `e
.f`.
-/
noncomputable def stupidTruncXIso {i : ι} {i' : ι'} (hi' : e.f i = i') :
    (K.stupidTrunc e).X i' ≅ K.X i' :=
  (K.restriction e).extendXIso e hi' ≪≫ eqToIso (by subst hi'; rfl)
/-
**HomologicalComplex.isZero_stupidTrunc_X** 是 Mathlib 中的一个引理，位于命名空间 `Homological
Complex`。
形式化陈述：isZero_stupidTrunc_X (i' : ι') (hi' : forall i, e.f i != i') : IsZero ((K.
stupidTrunc e).X i')
参数：i' : ι'；hi' : forall i, e.f i != i'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.isZero_extend_X`：isZero_extend_X (i' : ι') (hi' : for
all i, e.f i != i') : IsZero ((K.extend e).X i')
-/
lemma isZero_stupidTrunc_X (i' : ι') (hi' : ∀ i, e.f i ≠ i') :
    IsZero ((K.stupidTrunc e).X i') :=
  isZero_extend_X _ _ _ hi'
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι'' : Type*} {c'' : ComplexShape ι''} (e' : c''.Embedding c')
    [K.IsStrictlySupported e'] :
    IsStrictlySupported (K.stupidTrunc e) e' where
  isZero i' hi' := by
    by_cases hi'' : ∃ i, e.f i = i'
    · obtain ⟨i, hi⟩ := hi''
      exact (K.isZero_X_of_isStrictlySupported e' i' hi').of_iso (K.stupidTruncXIso e hi)
    · apply isZero_stupidTrunc_X
      simpa using hi''
/-
**HomologicalComplex.isZero_stupidTrunc_iff** 是 Mathlib 中的一个引理，位于命名空间 `Homologic
alComplex`。
形式化陈述：isZero_stupidTrunc_iff : IsZero (K.stupidTrunc e) ↔ K.IsStrictlySupportedO
utside e
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.of_iso`：of_iso (hY : IsZero Y) (e : X ≅ Y) 
: IsZero X
· 使用引理 `CategoryTheory.Functor.map_isZero`：map_isZero (F : C ⥤ D) [PreservesZero
Morphisms F] {X : C} (hX : IsZero X) : IsZero (F.obj X)
· 使用定理 `HomologicalComplex.instPreservesZeroMorphismsEval`：∀ {ι : Type u_1} (V :
 Type u) [inst : CategoryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms V] (c : ComplexSh…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomologicalComplex.isZero_iff_isStrictlySupported_and_isStrictlySupporte
dOutside`：isZero_iff_isStrictlySupported_and_isStrictlySupportedOutside : IsZero
 K ↔ K.IsStrictlySupported e ∧ K.IsStrictlySupportedOutside e
· 使用定理 `HomologicalComplex.instIsStrictlySupportedStupidTrunc`：∀ {ι : Type u_1} 
{ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [in
st : CategoryTheory.Category.{v_1, u_3} C] …
· 使用定理 `HomologicalComplex.IsStrictlySupportedOutside.isZero`：∀ {ι : Type u_1} {
ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [ins
t : CategoryTheory.Category.{v_1, u_3} C] …
-/
lemma isZero_stupidTrunc_iff :
    IsZero (K.stupidTrunc e) ↔ K.IsStrictlySupportedOutside e := by
  constructor
  · exact fun h ↦ ⟨fun i ↦
      ((eval _ _ (e.f i)).map_isZero h).of_iso (K.stupidTruncXIso e rfl).symm⟩
  · intro h
    rw [isZero_iff_isStrictlySupported_and_isStrictlySupportedOutside _ e]
    constructor
    · infer_instance
    · exact ⟨fun i ↦ (h.isZero i).of_iso (K.stupidTruncXIso e rfl)⟩

variable {K L M}

/-- The morphism `K.stupidTrunc e ⟶ L.stupidTrunc e` induced by a morphism `K ⟶ L`. -/
/-
**HomologicalComplex.stupidTruncMap** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComple
x`。
形式化陈述：stupidTruncMap : K.stupidTrunc e ⟶ L.stupidTrunc e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `K.stupidTrunc e ⟶ L.stupidTrunc e` induced by a morphism `K ⟶ L`.
-/
noncomputable def stupidTruncMap : K.stupidTrunc e ⟶ L.stupidTrunc e :=
  extendMap (restrictionMap φ e) e

variable (K) in
@[simp]
/-
**HomologicalComplex.stupidTruncMap_id** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalCom
plex`。
形式化陈述：stupidTruncMap_id : stupidTruncMap (𝟙 K) e = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomologicalComplex.extendMap_id`：extendMap_id : extendMap (𝟙 K) e = 𝟙 _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma stupidTruncMap_id : stupidTruncMap (𝟙 K) e = 𝟙 _ := by
  simp [stupidTruncMap, stupidTrunc]

@[simp, reassoc]
/-
**HomologicalComplex.stupidTruncMap_comp** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalC
omplex`。
形式化陈述：stupidTruncMap_comp : stupidTruncMap (φ ≫ φ') e = stupidTruncMap φ e ≫ stu
pidTruncMap φ' e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomologicalComplex.extendMap_comp`：extendMap_comp : extendMap (φ ≫ φ') e
 = extendMap φ e ≫ extendMap φ' e
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma stupidTruncMap_comp :
    stupidTruncMap (φ ≫ φ') e = stupidTruncMap φ e ≫ stupidTruncMap φ' e := by
  simp [stupidTruncMap, stupidTrunc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom** 是 Mathlib 中的一个引理，位于命名空
间 `HomologicalComplex`。
形式化陈述：stupidTruncMap_stupidTruncXIso_hom {i : ι} {i' : ι'} (hi : e.f i = i') : (
stupidTruncMap φ e).f i' ≫ (L.stupidTruncXIso e hi).hom = (K.stupidTruncXIso e h
i).hom ≫ φ.f i'
参数：hi : e.f i = i'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomologicalComplex.extendMap_f`：extendMap_f {i : ι} {i' : ι'} (h : e.f i
 = i') : (extendMap φ e).f i' = (extendXIso K e h).hom ≫ φ.f i ≫ (extendXIso L e
 h).inv
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HomologicalComplex.restrictionMap_f`：∀ {ι : Type u_1} {ι' : Type u_2} {c
 : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst : CategoryTheor
y.Category.{v_1, u_3} C] …
· 使用定理 `CategoryTheory.Iso.trans_refl`：trans_refl (α : X ≅ Y) : α ≪≫ Iso.refl Y 
= α
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
lemma stupidTruncMap_stupidTruncXIso_hom {i : ι} {i' : ι'} (hi : e.f i = i') :
    (stupidTruncMap φ e).f i' ≫ (L.stupidTruncXIso e hi).hom =
      (K.stupidTruncXIso e hi).hom ≫ φ.f i' := by
  subst hi
  simp [stupidTruncMap, stupidTruncXIso, extendMap_f _ _ rfl]

end HomologicalComplex

namespace ComplexShape.Embedding

variable (e : Embedding c c') (C : Type*) [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

/-- The stupid truncation functor `HomologicalComplex C c' ⥤ HomologicalComplex C c'`
given by an embedding `e : Embedding c c'` of complex shapes. -/
@[simps]
/-
**ComplexShape.Embedding.stupidTruncFunctor** 是 Mathlib 中的一个定义，位于命名空间 `ComplexSh
ape.Embedding`。
形式化陈述：stupidTruncFunctor [e.IsRelIff] : HomologicalComplex C c' ⥤ HomologicalCom
plex C c' where obj K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The stupid truncation functor `HomologicalComplex C c' ⥤ HomologicalComplex C c'
`
given by an embedding `e : Embedding c c'` of complex shapes.
-/
noncomputable def stupidTruncFunctor [e.IsRelIff] :
    HomologicalComplex C c' ⥤ HomologicalComplex C c' where
  obj K := K.stupidTrunc e
  map φ := HomologicalComplex.stupidTruncMap φ e

end ComplexShape.Embedding

