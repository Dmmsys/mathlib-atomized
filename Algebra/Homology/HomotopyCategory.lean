/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.CategoryTheory.MorphismProperty.IsInvertedBy
public import Mathlib.CategoryTheory.Quotient.Linear
public import Mathlib.CategoryTheory.Quotient.Preadditive

/-!
# The homotopy category

`HomotopyCategory V c` gives the category of chain complexes of shape `c` in `V`,
with chain maps identified when they are homotopic.
-/

@[expose] public section

universe v u

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable {R : Type*} [Semiring R]
  {ι : Type*} (V : Type u) [Category.{v} V] [Preadditive V] (c : ComplexShape ι)

/-- The congruence on `HomologicalComplex V c` given by the existence of a homotopy.
-/
/-
**homotopic** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：homotopic : HomRel (HomologicalComplex V c)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The congruence on `HomologicalComplex V c` given by the existence of a homotopy.
-/
def homotopic : HomRel (HomologicalComplex V c) := fun _ _ f g => Nonempty (Homotopy f g)
/-
**homotopy_congruence** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：homotopy_congruence : Congruence (homotopic V c) where equivalence
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance homotopy_congruence : Congruence (homotopic V c) where
  equivalence :=
    { refl := fun C => ⟨Homotopy.refl C⟩
      symm := fun ⟨w⟩ => ⟨w.symm⟩
      trans := fun ⟨w₁⟩ ⟨w₂⟩ => ⟨w₁.trans w₂⟩ }
  comp_left := fun _ _ _ ⟨i⟩ => ⟨i.compLeft _⟩
  comp_right := fun _ ⟨i⟩ => ⟨i.compRight _⟩

/-- `HomotopyCategory V c` is the category of chain complexes of shape `c` in `V`,
with chain maps identified when they are homotopic. -/
/-
**HomotopyCategory** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HomotopyCategory
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HomotopyCategory V c` is the category of chain complexes of shape `c` in `V`,
with chain maps identified when they are homotopic.
-/
def HomotopyCategory :=
  CategoryTheory.Quotient (homotopic V c)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (HomotopyCategory V c) :=
  inferInstanceAs <| Category (CategoryTheory.Quotient (homotopic V c))

namespace HomotopyCategory

/-
**HomotopyCategory.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Preadditive (CategoryTheory.Quotient (homotopic V c)) :=
  Quotient.preadditive _ (by
    rintro _ _ _ _ _ _ ⟨h⟩ ⟨h'⟩
    exact ⟨Homotopy.add h h'⟩)
/-
**HomotopyCategory.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Preadditive (HomotopyCategory V c) :=
  inferInstanceAs <| Preadditive (CategoryTheory.Quotient (homotopic V c))

/-- The quotient functor from complexes to the homotopy category. -/
/-
**HomotopyCategory.quotient** 是 Mathlib 中的一个定义，位于命名空间 `HomotopyCategory`。
形式化陈述：quotient : HomologicalComplex V c ⥤ HomotopyCategory V c
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quotient functor from complexes to the homotopy category.
-/
def quotient : HomologicalComplex V c ⥤ HomotopyCategory V c :=
  CategoryTheory.Quotient.functor _
/-
**HomotopyCategory.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (quotient V c).Full := Quotient.full_functor _
/-
**HomotopyCategory.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (quotient V c).EssSurj := Quotient.essSurj_functor _
/-
**HomotopyCategory.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (quotient V c).Additive where
/-
**HomotopyCategory.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Functor.Additive (Quotient.functor (homotopic V c)) where
/-
**HomotopyCategory.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Linear R V] : Linear R (HomotopyCategory V c) :=
  Quotient.linear R (homotopic V c) (fun _ _ _ _ _ h => ⟨h.some.smul _⟩)
/-
**HomotopyCategory.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Linear R V] : Functor.Linear R (quotient V c) :=
  Quotient.linear_functor _ (homotopic V c) _

open ZeroObject
/-
**HomotopyCategory.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasZeroObject V] : Inhabited (HomotopyCategory V c) :=
  ⟨(quotient V c).obj 0⟩
/-
**HomotopyCategory.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasZeroObject V] : HasZeroObject (HomotopyCategory V c) :=
  ⟨(quotient V c).obj 0, by
    rw [IsZero.iff_id_eq_zero, ← (quotient V c).map_id, id_zero, Functor.map_zero]⟩
/-
**HomotopyCategory.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {D : Type*} [Category* D] : ((Functor.whiskeringLeft _ _ D).obj (quotient V c)).Full :=
  Quotient.full_whiskeringLeft_functor _ _
/-
**HomotopyCategory.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {D : Type*} [Category* D] : ((Functor.whiskeringLeft _ _ D).obj (quotient V c)).Faithful :=
  Quotient.faithful_whiskeringLeft_functor _ _

variable {V c}
/-
**HomotopyCategory.quotient_obj_surjective** 是 Mathlib 中的一个引理，位于命名空间 `HomotopyCa
tegory`。
形式化陈述：quotient_obj_surjective (X : HomotopyCategory V c) : exists (K : Homologic
alComplex V c), (quotient _ _).obj K = X
参数：X : HomotopyCategory V c。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma quotient_obj_surjective (X : HomotopyCategory V c) :
    ∃ (K : HomologicalComplex V c), (quotient _ _).obj K = X :=
  ⟨_, rfl⟩

-- Not `@[simp]` because it hinders the automatic application of the more useful `quotient_map_out`
/-
**HomotopyCategory.quotient_obj_as** 是 Mathlib 中的一个定理，位于命名空间 `HomotopyCategory`。
形式化陈述：quotient_obj_as (C : HomologicalComplex V c) : ((quotient V c).obj C).as =
 C
参数：C : HomologicalComplex V c。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quotient_obj_as (C : HomologicalComplex V c) : ((quotient V c).obj C).as = C :=
  rfl

@[simp]
/-
**HomotopyCategory.quotient_map_out** 是 Mathlib 中的一个定理，位于命名空间 `HomotopyCategory`
。
形式化陈述：quotient_map_out {C D : HomotopyCategory V c} (f : C ⟶ D) : (quotient V c)
.map f.out = f
参数：f : C ⟶ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.out_eq`：Quot.out_eq {r : α -> α -> Prop} (q : Quot r) : Quot.mk r q
.out = q
-/
theorem quotient_map_out {C D : HomotopyCategory V c} (f : C ⟶ D) : (quotient V c).map f.out = f :=
  Quot.out_eq _
/-
**HomotopyCategory.quot_mk_eq_quotient_map** 是 Mathlib 中的一个定理，位于命名空间 `HomotopyCa
tegory`。
形式化陈述：quot_mk_eq_quotient_map {C D : HomologicalComplex V c} (f : C ⟶ D) : Quot.
mk _ f = (quotient V c).map f
参数：f : C ⟶ D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quot_mk_eq_quotient_map {C D : HomologicalComplex V c} (f : C ⟶ D) :
    Quot.mk _ f = (quotient V c).map f := rfl
/-
**HomotopyCategory.eq_of_homotopy** 是 Mathlib 中的一个定理，位于命名空间 `HomotopyCategory`。
形式化陈述：eq_of_homotopy {C D : HomologicalComplex V c} (f g : C ⟶ D) (h : Homotopy 
f g) : (quotient V c).map f = (quotient V c).map g
参数：f g : C ⟶ D；h : Homotopy f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Quotient.sound`：∀ {C : Type u_1} [inst : CategoryTheory.C
ategory.{v_1, u_1} C] (r : HomRel C) {a b : C} {f₁ f₂ : a ⟶ b},   r f₁ f₂ → (Cat
egoryTheory.Quotien…
-/
theorem eq_of_homotopy {C D : HomologicalComplex V c} (f g : C ⟶ D) (h : Homotopy f g) :
    (quotient V c).map f = (quotient V c).map g :=
  CategoryTheory.Quotient.sound _ ⟨h⟩

/-- If two chain maps become equal in the homotopy category, then they are homotopic. -/
/-
**HomotopyCategory.homotopyOfEq** 是 Mathlib 中的一个定义，位于命名空间 `HomotopyCategory`。
形式化陈述：homotopyOfEq {C D : HomologicalComplex V c} (f g : C ⟶ D) (w : (quotient V
 c).map f = (quotient V c).map g) : Homotopy f g
参数：f g : C ⟶ D；w : (quotient V c).map f = (quotient V c).map g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If two chain maps become equal in the homotopy category, then they are homotopic
.
-/
def homotopyOfEq {C D : HomologicalComplex V c} (f g : C ⟶ D)
    (w : (quotient V c).map f = (quotient V c).map g) : Homotopy f g :=
  ((Quotient.functor_map_eq_iff _ _ _).mp w).some
/-
**HomotopyCategory.quotient_map_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `HomotopyC
ategory`。
形式化陈述：quotient_map_eq_zero_iff {C D : HomologicalComplex V c} (f : C ⟶ D) : (quo
tient V c).map f = 0 ↔ Nonempty (Homotopy f 0)
参数：f : C ⟶ D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `HomotopyCategory.instAdditiveHomologicalComplexQuotient`：∀ {ι : Type u_2
} (V : Type u) [inst : CategoryTheory.Category.{v, u} V] [inst_1 : CategoryTheor
y.Preadditive V]   (c : ComplexShape ι), (Hom…
· 使用定理 `HomotopyCategory.eq_of_homotopy`：eq_of_homotopy {C D : HomologicalComple
x V c} (f g : C ⟶ D) (h : Homotopy f g) : (quotient V c).map f = (quotient V c).
map g
-/
lemma quotient_map_eq_zero_iff {C D : HomologicalComplex V c} (f : C ⟶ D) :
    (quotient V c).map f = 0 ↔ Nonempty (Homotopy f 0) :=
  ⟨fun h ↦ ⟨homotopyOfEq _ _ (by simpa using h)⟩,
    fun ⟨h⟩ ↦ by simpa using eq_of_homotopy _ _ h⟩

set_option backward.isDefEq.respectTransparency false in
/-- An arbitrarily chosen representation of the image of a chain map in the homotopy category
is homotopic to the original chain map.
-/
/-
**HomotopyCategory.homotopyOutMap** 是 Mathlib 中的一个定义，位于命名空间 `HomotopyCategory`。
形式化陈述：homotopyOutMap {C D : HomologicalComplex V c} (f : C ⟶ D) : Homotopy ((quo
tient V c).map f).out f
参数：f : C ⟶ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An arbitrarily chosen representation of the image of a chain map in the homotopy
 category
is homotopic to the original chain map.
-/
def homotopyOutMap {C D : HomologicalComplex V c} (f : C ⟶ D) :
    Homotopy ((quotient V c).map f).out f := by
  apply homotopyOfEq
  simp

set_option backward.isDefEq.respectTransparency false in
/-
**HomotopyCategory.quotient_map_out_comp_out** 是 Mathlib 中的一个定理，位于命名空间 `Homotopy
Category`。
形式化陈述：quotient_map_out_comp_out {C D E : HomotopyCategory V c} (f : C ⟶ D) (g : 
D ⟶ E) : (quotient V c).map (Quot.out f ≫ Quot.out g) = f ≫ g
参数：f : C ⟶ D；g : D ⟶ E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `HomotopyCategory.quotient_map_out`：quotient_map_out {C D : HomotopyCateg
ory V c} (f : C ⟶ D) : (quotient V c).map f.out = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem quotient_map_out_comp_out {C D E : HomotopyCategory V c} (f : C ⟶ D) (g : D ⟶ E) :
    (quotient V c).map (Quot.out f ≫ Quot.out g) = f ≫ g := by simp

/-- Homotopy equivalent complexes become isomorphic in the homotopy category. -/
@[simps]
/-
**HomotopyCategory.isoOfHomotopyEquiv** 是 Mathlib 中的一个定义，位于命名空间 `HomotopyCategor
y`。
形式化陈述：isoOfHomotopyEquiv {C D : HomologicalComplex V c} (f : HomotopyEquiv C D) 
: (quotient V c).obj C ≅ (quotient V c).obj D where hom
参数：f : HomotopyEquiv C D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Homotopy equivalent complexes become isomorphic in the homotopy category.
-/
def isoOfHomotopyEquiv {C D : HomologicalComplex V c} (f : HomotopyEquiv C D) :
    (quotient V c).obj C ≅ (quotient V c).obj D where
  hom := (quotient V c).map f.hom
  inv := (quotient V c).map f.inv
  hom_inv_id := by
    rw [← (quotient V c).map_comp, ← (quotient V c).map_id]
    exact eq_of_homotopy _ _ f.homotopyHomInvId
  inv_hom_id := by
    rw [← (quotient V c).map_comp, ← (quotient V c).map_id]
    exact eq_of_homotopy _ _ f.homotopyInvHomId

set_option backward.isDefEq.respectTransparency false in
/-- If two complexes become isomorphic in the homotopy category,
  then they were homotopy equivalent. -/
/-
**HomotopyCategory.homotopyEquivOfIso** 是 Mathlib 中的一个定义，位于命名空间 `HomotopyCategor
y`。
形式化陈述：homotopyEquivOfIso {C D : HomologicalComplex V c} (i : (quotient V c).obj 
C ≅ (quotient V c).obj D) : HomotopyEquiv C D where hom
参数：i : (quotient V c).obj C ≅ (quotient V c).obj D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If two complexes become isomorphic in the homotopy category,
  then they were homotopy equivalent.
-/
def homotopyEquivOfIso {C D : HomologicalComplex V c}
    (i : (quotient V c).obj C ≅ (quotient V c).obj D) : HomotopyEquiv C D where
  hom := Quot.out i.hom
  inv := Quot.out i.inv
  homotopyHomInvId :=
    homotopyOfEq _ _
      (by rw [quotient_map_out_comp_out, i.hom_inv_id, (quotient V c).map_id])
  homotopyInvHomId :=
    homotopyOfEq _ _
      (by rw [quotient_map_out_comp_out, i.inv_hom_id, (quotient V c).map_id])

variable (V c) in
/-
**HomotopyCategory.quotient_inverts_homotopyEquivalences** 是 Mathlib 中的一个引理，位于命名
空间 `HomotopyCategory`。
形式化陈述：quotient_inverts_homotopyEquivalences : (HomologicalComplex.homotopyEquiva
lences V c).IsInvertedBy (quotient V c)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
lemma quotient_inverts_homotopyEquivalences :
    (HomologicalComplex.homotopyEquivalences V c).IsInvertedBy (quotient V c) := by
  rintro K L _ ⟨e, rfl⟩
  change IsIso (isoOfHomotopyEquiv e).hom
  infer_instance

variable (V c) in
/-
**HomotopyCategory.inverseImage_quotient_isomorphisms** 是 Mathlib 中的一个引理，位于命名空间 
`HomotopyCategory`。
形式化陈述：inverseImage_quotient_isomorphisms : (MorphismProperty.isomorphisms _).inv
erseImage (HomotopyCategory.quotient V c) = homotopyEquivalences V c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.map_surjective`：map_surjective (F : C ⥤ D) [Full 
F] : Function.Surjective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `HomotopyCategory.instFullHomologicalComplexQuotient`：∀ {ι : Type u_2} (V
 : Type u) [inst : CategoryTheory.Category.{v, u} V] [inst_1 : CategoryTheory.Pr
eadditive V]   (c : ComplexShape ι), (Hom…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用引理 `HomotopyCategory.quotient_inverts_homotopyEquivalences`：quotient_inverts
_homotopyEquivalences : (HomologicalComplex.homotopyEquivalences V c).IsInverted
By (quotient V c)
-/
lemma inverseImage_quotient_isomorphisms :
    (MorphismProperty.isomorphisms _).inverseImage (HomotopyCategory.quotient V c) =
      homotopyEquivalences V c := by
  ext K L f
  simp only [MorphismProperty.inverseImage_iff, MorphismProperty.isomorphisms.iff]
  refine ⟨fun _ ↦ ?_, fun hf ↦ quotient_inverts_homotopyEquivalences _ _ _ hf⟩
  obtain ⟨g, hg⟩ := (quotient V c).map_surjective (inv ((quotient _ _).map f))
  exact ⟨{
    hom := f
    inv := g
    homotopyHomInvId := homotopyOfEq _ _ (by simp [hg])
    homotopyInvHomId := homotopyOfEq _ _ (by simp [hg]) }, rfl⟩
/-
**HomotopyCategory.isZero_quotient_obj_iff** 是 Mathlib 中的一个引理，位于命名空间 `HomotopyCa
tegory`。
形式化陈述：isZero_quotient_obj_iff (C : HomologicalComplex V c) : IsZero ((quotient _
 _).obj C) ↔ Nonempty (Homotopy (𝟙 C) 0)
参数：C : HomologicalComplex V c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsZero.iff_id_eq_zero`：iff_id_eq_zero (X : C) : Is
Zero X ↔ 𝟙 X = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `HomotopyCategory.instAdditiveHomologicalComplexQuotient`：∀ {ι : Type u_2
} (V : Type u) [inst : CategoryTheory.Category.{v, u} V] [inst_1 : CategoryTheor
y.Preadditive V]   (c : ComplexShape ι), (Hom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HomotopyCategory.eq_of_homotopy`：eq_of_homotopy {C D : HomologicalComple
x V c} (f g : C ⟶ D) (h : Homotopy f g) : (quotient V c).map f = (quotient V c).
map g
-/
lemma isZero_quotient_obj_iff (C : HomologicalComplex V c) :
    IsZero ((quotient _ _).obj C) ↔ Nonempty (Homotopy (𝟙 C) 0) := by
  rw [IsZero.iff_id_eq_zero]
  constructor
  · intro h
    exact ⟨(homotopyOfEq _ _ (by simp [h]))⟩
  · rintro ⟨h⟩
    simpa using (eq_of_homotopy _ _ h)

variable (V c)

section

variable [CategoryWithHomology V]

/-- The `i`-th homology, as a functor from the homotopy category. -/
/-
**HomotopyCategory.homologyFunctor** 是 Mathlib 中的一个定义，位于命名空间 `HomotopyCategory`。
形式化陈述：homologyFunctor (i : ι) : HomotopyCategory V c ⥤ V
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `i`-th homology, as a functor from the homotopy category.
-/
noncomputable def homologyFunctor (i : ι) : HomotopyCategory V c ⥤ V :=
  CategoryTheory.Quotient.lift _ (HomologicalComplex.homologyFunctor V c i) (by
    rintro K L f g ⟨h⟩
    exact h.homologyMap_eq i)

/-- The homology functor on the homotopy category is induced by
the homology functor on homological complexes. -/
/-
**HomotopyCategory.homologyFunctorFactors** 是 Mathlib 中的一个定义，位于命名空间 `HomotopyCat
egory`。
形式化陈述：homologyFunctorFactors (i : ι) : quotient V c ⋙ homologyFunctor V c i ≅ Ho
mologicalComplex.homologyFunctor V c i
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homology functor on the homotopy category is induced by
the homology functor on homological complexes.
-/
noncomputable def homologyFunctorFactors (i : ι) :
    quotient V c ⋙ homologyFunctor V c i ≅
      HomologicalComplex.homologyFunctor V c i :=
  Quotient.lift.isLift _ _ _

-- this is to prevent any abuse of defeq
attribute [irreducible] homologyFunctor homologyFunctorFactors
/-
**HomotopyCategory.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (i : ι) : (homologyFunctor V c i).Additive := by
  have := Functor.additive_of_iso (homologyFunctorFactors V c i).symm
  exact Functor.additive_of_full_essSurj_comp (quotient V c) _

end

end HomotopyCategory

namespace CategoryTheory

variable {V} {W : Type*} [Category* W] [Preadditive W]

/-- An additive functor induces a functor between homotopy categories. -/
@[simps! obj]
/-
**CategoryTheory.Functor.mapHomotopyCategory** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Functor`。
形式化陈述：{ι : Type u_2} →   {V : Type u} →     [inst : CategoryTheory.Category.{v, 
u} V] →       [inst_1 : CategoryTheory.Preadditive V] →         {W : Type u_3} →
           [inst_2 : CategoryTheory.Category.{v_1, u_3} W] →             [inst_3
 : CategoryTheory.Preadditive W] →               (F : CategoryTheory.Functor V W
) →                 [F.Additive] →                   (c : ComplexShape ι) → Cate
goryTheory.Functor (HomotopyCategory V c) (HomotopyCategory W c)
参数：F : CategoryTheory.Functor V W；c : ComplexShape ι；HomotopyCategory V c；Homoto
pyCategory W c。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…

--- 原说明 ---
An additive functor induces a functor between homotopy categories.
-/
def Functor.mapHomotopyCategory (F : V ⥤ W) [F.Additive] (c : ComplexShape ι) :
    HomotopyCategory V c ⥤ HomotopyCategory W c :=
  CategoryTheory.Quotient.lift _ (F.mapHomologicalComplex c ⋙ HomotopyCategory.quotient W c)
    (fun _ _ _ _ ⟨h⟩ => HomotopyCategory.eq_of_homotopy _ _ (F.mapHomotopy h))

@[simp]
/-
**CategoryTheory.Functor.mapHomotopyCategory_map** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Functor`。
形式化陈述：∀ {ι : Type u_2} {V : Type u} [inst : CategoryTheory.Category.{v, u} V] [i
nst_1 : CategoryTheory.Preadditive V]   {W : Type u_3} [inst_2 : CategoryTheory.
Category.{v_1, u_3} W] [inst_3 : CategoryTheory.Preadditive W]   (F : CategoryTh
eory.Functor V W) [inst_4 : F.Additive] {c : ComplexShape ι} {K L : HomologicalC
omplex V c}   (f : K ⟶ L),   (F.mapHomotopyCategory c).map ((HomotopyCategory.qu
otient V c).map f) =     (HomotopyCategory.quotient W c).map ((F.mapHomologicalC
omplex c).map f)
参数：F : CategoryTheory.Functor V W；f : K ⟶ L；F.mapHomotopyCategory c；(HomotopyCat
egory.quotient V c).map f；HomotopyCategory.quotient W c；(F.mapHomologicalComplex
 c).map f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Functor.mapHomotopyCategory_map (F : V ⥤ W) [F.Additive] {c : ComplexShape ι}
    {K L : HomologicalComplex V c} (f : K ⟶ L) :
    (F.mapHomotopyCategory c).map ((HomotopyCategory.quotient V c).map f) =
      (HomotopyCategory.quotient W c).map ((F.mapHomologicalComplex c).map f) :=
  rfl

/-- The obvious isomorphism between
`HomotopyCategory.quotient V c ⋙ F.mapHomotopyCategory c` and
`F.mapHomologicalComplex c ⋙ HomotopyCategory.quotient W c` when `F : V ⥤ W` is
an additive functor. -/
/-
**CategoryTheory.Functor.mapHomotopyCategoryFactors** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Functor`。
形式化陈述：{ι : Type u_2} →   {V : Type u} →     [inst : CategoryTheory.Category.{v, 
u} V] →       [inst_1 : CategoryTheory.Preadditive V] →         {W : Type u_3} →
           [inst_2 : CategoryTheory.Category.{v_1, u_3} W] →             [inst_3
 : CategoryTheory.Preadditive W] →               (F : CategoryTheory.Functor V W
) →                 [inst_4 : F.Additive] →                   (c : ComplexShape 
ι) →                     (HomotopyCategory.quotient V c).comp (F.mapHomotopyCate
gory c) ≅                       (F.mapHomologicalComplex c).comp (HomotopyCatego
ry.quotient W c)
参数：F : CategoryTheory.Functor V W；c : ComplexShape ι；HomotopyCategory.quotient V
 c；F.mapHomotopyCategory c；F.mapHomologicalComplex c；HomotopyCategory.quotient W
 c。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…

--- 原说明 ---
The obvious isomorphism between
`HomotopyCategory.quotient V c ⋙ F.mapHomotopyCategory c` and
`F.mapHomologicalComplex c ⋙ HomotopyCategory.quotient W c` when `F : V ⥤ W` is
an additive functor.
-/
def Functor.mapHomotopyCategoryFactors (F : V ⥤ W) [F.Additive] (c : ComplexShape ι) :
    HomotopyCategory.quotient V c ⋙ F.mapHomotopyCategory c ≅
      F.mapHomologicalComplex c ⋙ HomotopyCategory.quotient W c :=
  CategoryTheory.Quotient.lift.isLift _ _ _

set_option backward.isDefEq.respectTransparency false in
-- TODO develop lifting of natural transformations for general quotient categories so that
-- `NatTrans.mapHomotopyCategory` become a particular case of it
/-- A natural transformation induces a natural transformation between
  the induced functors on the homotopy category. -/
@[simps]
/-
**CategoryTheory.NatTrans.mapHomotopyCategory** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.NatTrans`。
形式化陈述：{ι : Type u_2} →   {V : Type u} →     [inst : CategoryTheory.Category.{v, 
u} V] →       [inst_1 : CategoryTheory.Preadditive V] →         {W : Type u_3} →
           [inst_2 : CategoryTheory.Category.{v_1, u_3} W] →             [inst_3
 : CategoryTheory.Preadditive W] →               {F G : CategoryTheory.Functor V
 W} →                 [inst_4 : F.Additive] →                   [inst_5 : G.Addi
tive] →                     (F ⟶ G) → (c : ComplexShape ι) → F.mapHomotopyCatego
ry c ⟶ G.mapHomotopyCategory c
参数：F ⟶ G；c : ComplexShape ι。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…

--- 原说明 ---
A natural transformation induces a natural transformation between
  the induced functors on the homotopy category.
-/
def NatTrans.mapHomotopyCategory {F G : V ⥤ W} [F.Additive] [G.Additive] (α : F ⟶ G)
    (c : ComplexShape ι) : F.mapHomotopyCategory c ⟶ G.mapHomotopyCategory c where
  app C := (HomotopyCategory.quotient W c).map ((NatTrans.mapHomologicalComplex α c).app C.as)
  naturality := by
    rintro ⟨C⟩ ⟨D⟩ ⟨f : C ⟶ D⟩
    simp only [HomotopyCategory.quot_mk_eq_quotient_map, Functor.mapHomotopyCategory_map,
      ← Functor.map_comp, NatTrans.naturality]

@[simp]
/-
**CategoryTheory.NatTrans.mapHomotopyCategory_id** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.NatTrans`。
形式化陈述：∀ {ι : Type u_2} {V : Type u} [inst : CategoryTheory.Category.{v, u} V] [i
nst_1 : CategoryTheory.Preadditive V]   {W : Type u_3} [inst_2 : CategoryTheory.
Category.{v_1, u_3} W] [inst_3 : CategoryTheory.Preadditive W]   (c : ComplexSha
pe ι) (F : CategoryTheory.Functor V W) [inst_4 : F.Additive],   CategoryTheory.N
atTrans.mapHomotopyCategory (CategoryTheory.CategoryStruct.id F) c =     Categor
yTheory.CategoryStruct.id (F.mapHomotopyCategory c)
参数：c : ComplexShape ι；F : CategoryTheory.Functor V W；CategoryTheory.CategoryStru
ct.id F；F.mapHomotopyCategory c。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem NatTrans.mapHomotopyCategory_id (c : ComplexShape ι) (F : V ⥤ W) [F.Additive] :
    NatTrans.mapHomotopyCategory (𝟙 F) c = 𝟙 (F.mapHomotopyCategory c) := by cat_disch

@[simp]
/-
**CategoryTheory.NatTrans.mapHomotopyCategory_comp** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.NatTrans`。
形式化陈述：∀ {ι : Type u_2} {V : Type u} [inst : CategoryTheory.Category.{v, u} V] [i
nst_1 : CategoryTheory.Preadditive V]   {W : Type u_3} [inst_2 : CategoryTheory.
Category.{v_1, u_3} W] [inst_3 : CategoryTheory.Preadditive W]   (c : ComplexSha
pe ι) {F G H : CategoryTheory.Functor V W} [inst_4 : F.Additive] [inst_5 : G.Add
itive]   [inst_6 : H.Additive] (α : F ⟶ G) (β : G ⟶ H),   CategoryTheory.NatTran
s.mapHomotopyCategory (CategoryTheory.CategoryStruct.comp α β) c =     CategoryT
heory.CategoryStruct.comp (CategoryTheory.NatTrans.mapHomotopyCategory α c)     
  (CategoryTheory.NatTrans.mapHomotopyCategory β c)
参数：c : ComplexShape ι；α : F ⟶ G；β : G ⟶ H；CategoryTheory.CategoryStruct.comp α β
；CategoryTheory.NatTrans.mapHomotopyCategory α c；CategoryTheory.NatTrans.mapHomo
topyCategory β c。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem NatTrans.mapHomotopyCategory_comp (c : ComplexShape ι) {F G H : V ⥤ W} [F.Additive]
    [G.Additive] [H.Additive] (α : F ⟶ G) (β : G ⟶ H) :
    NatTrans.mapHomotopyCategory (α ≫ β) c =
      NatTrans.mapHomotopyCategory α c ≫ NatTrans.mapHomotopyCategory β c := by cat_disch
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : V ⥤ W) [F.Additive] (c : ComplexShape ι) :
    (F.mapHomotopyCategory c).Additive :=
  have := Functor.additive_of_iso (F.mapHomotopyCategoryFactors c).symm
  (HomotopyCategory.quotient V c).additive_of_full_essSurj_comp (F.mapHomotopyCategory c)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : V ⥤ W) [F.Additive] (c : ComplexShape ι) [Linear R V] [Linear R W] [F.Linear R] :
    Functor.Linear R (F.mapHomotopyCategory c) :=
  have := Functor.linear_of_iso R (F.mapHomotopyCategoryFactors c).symm
  (HomotopyCategory.quotient V c).linear_of_full_essSurj_comp (F.mapHomotopyCategory c)

/-- If additive functors are related by an isomorphism `F ⋙ G ≅ H`, this is
the corresponding isomorphism for the induced functors on homotopy categories
of homological complexes. -/
/-
**CategoryTheory.Functor.mapHomotopyCategoryCompIso** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Functor`。
形式化陈述：{ι : Type u_2} →   {V : Type u} →     [inst : CategoryTheory.Category.{v, 
u} V] →       [inst_1 : CategoryTheory.Preadditive V] →         {W : Type u_3} →
           [inst_2 : CategoryTheory.Category.{v_1, u_3} W] →             [inst_3
 : CategoryTheory.Preadditive W] →               {W' : Type u_4} →              
   [inst_4 : CategoryTheory.Category.{u_5, u_4} W'] →                   [inst_5 
: CategoryTheory.Preadditive W'] →                     {F : CategoryTheory.Funct
or V W} →                       {G : CategoryTheory.Functor W W'} →             
            {H : CategoryTheory.Functor V W'} →                           (F.com
p G ≅ H) →                             [inst_6 : F.Additive] →                  
             [inst_7 : G.Additive] →                                 [inst_8 : H
.Additive] →                                   (c : ComplexShape ι) →           
                          (F.mapHomotopyCategory c).comp (G.mapHomotopyCategory 
c) ≅ H.mapHomotopyCategory c
参数：F.comp G ≅ H；c : ComplexShape ι；F.mapHomotopyCategory c；G.mapHomotopyCategory
 c。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…

--- 原说明 ---
If additive functors are related by an isomorphism `F ⋙ G ≅ H`, this is
the corresponding isomorphism for the induced functors on homotopy categories
of homological complexes.
-/
def Functor.mapHomotopyCategoryCompIso {W' : Type*} [Category W'] [Preadditive W']
    {F : V ⥤ W} {G : W ⥤ W'} {H : V ⥤ W'} (e : F ⋙ G ≅ H)
    [F.Additive] [G.Additive] [H.Additive] (c : ComplexShape ι) :
    F.mapHomotopyCategory c ⋙ G.mapHomotopyCategory c ≅ H.mapHomotopyCategory c :=
  Quotient.natIsoLift _ (isoWhiskerRight (Functor.mapHomologicalComplexCompIso e c)
    (HomotopyCategory.quotient W' c))

variable {c} in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The preimage by a fully faithful functor of a homotopy between morphisms
of homological complexes. -/
/-
**CategoryTheory.Functor.preimageHomotopy** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：{ι : Type u_2} →   {V : Type u} →     [inst : CategoryTheory.Category.{v, 
u} V] →       [inst_1 : CategoryTheory.Preadditive V] →         {c : ComplexShap
e ι} →           {W : Type u_3} →             [inst_2 : CategoryTheory.Category.
{v_1, u_3} W] →               [inst_3 : CategoryTheory.Preadditive W] →         
        (F : CategoryTheory.Functor V W) →                   [inst_4 : F.Additiv
e] →                     [F.Full] →                       [F.Faithful] →        
                 {K L : HomologicalComplex V c} →                           {f₁ 
f₂ : K ⟶ L} →                             Homotopy ((F.mapHomologicalComplex c).
map f₁) ((F.mapHomologicalComplex c).map f₂) →                               Hom
otopy f₁ f₂
参数：F : CategoryTheory.Functor V W；(F.mapHomologicalComplex c).map f₁；(F.mapHomol
ogicalComplex c).map f₂。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…

--- 原说明 ---
The preimage by a fully faithful functor of a homotopy between morphisms
of homological complexes.
-/
def Functor.preimageHomotopy
    (F : V ⥤ W) [F.Additive] [F.Full] [F.Faithful]
    {K L : HomologicalComplex V c} {f₁ f₂ : K ⟶ L}
    (H : Homotopy ((F.mapHomologicalComplex c).map f₁) ((F.mapHomologicalComplex c).map f₂)) :
    Homotopy f₁ f₂ where
  hom i j := F.preimage (H.hom i j)
  zero i j hij := F.map_injective (by simp only [map_preimage, Functor.map_zero, H.zero i j hij])
  comm i := F.map_injective (by simp [dsimp% H.comm i, dNext, prevD])
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : V ⥤ W) [F.Full] [F.Faithful] [F.Additive] :
    (F.mapHomotopyCategory c).Faithful where
  map_injective := by
    rintro ⟨K⟩ ⟨L⟩ f₁ f₂ h
    obtain ⟨f₁, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f₁
    obtain ⟨f₂, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f₂
    exact HomotopyCategory.eq_of_homotopy _ _
      (F.preimageHomotopy (HomotopyCategory.homotopyOfEq _ _ h))
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : V ⥤ W) [F.Full] [F.Faithful] [F.Additive] :
    (F.mapHomotopyCategory c).Full where
  map_surjective := by
    rintro ⟨K⟩ ⟨L⟩ ⟨f⟩
    obtain ⟨g : K ⟶ L, rfl⟩ := (F.mapHomologicalComplex c).map_surjective f
    exact ⟨(HomotopyCategory.quotient V c).map g, rfl⟩

end CategoryTheory

namespace HomologicalComplex

variable {ι : Type*} {V : Type u} [Category.{v} V] [Preadditive V] {c : ComplexShape ι}

open HomotopyCategory in
/-
**HomologicalComplex.isIso_quotient_map_iff_homotopyEquivalences** 是 Mathlib 中的一
个引理，位于命名空间 `HomologicalComplex`。
形式化陈述：isIso_quotient_map_iff_homotopyEquivalences {K L : HomologicalComplex V c}
 (f : K ⟶ L) : IsIso ((quotient _ _).map f) ↔ homotopyEquivalences _ _ f
参数：f : K ⟶ L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_surjective`：map_surjective (F : C ⥤ D) [Full 
F] : Function.Surjective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `HomotopyCategory.instFullHomologicalComplexQuotient`：∀ {ι : Type u_2} (V
 : Type u) [inst : CategoryTheory.Category.{v, u} V] [inst_1 : CategoryTheory.Pr
eadditive V]   (c : ComplexShape ι), (Hom…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用引理 `HomotopyCategory.quotient_inverts_homotopyEquivalences`：quotient_inverts
_homotopyEquivalences : (HomologicalComplex.homotopyEquivalences V c).IsInverted
By (quotient V c)
-/
lemma isIso_quotient_map_iff_homotopyEquivalences
    {K L : HomologicalComplex V c} (f : K ⟶ L) :
    IsIso ((quotient _ _).map f) ↔
      homotopyEquivalences _ _ f := by
  refine ⟨fun _ ↦ ?_, fun hf ↦ quotient_inverts_homotopyEquivalences V c f hf⟩
  obtain ⟨g, hg⟩ := (quotient V c).map_surjective (inv ((quotient V c).map f))
  let e : HomotopyEquiv K L :=
    { hom := f
      inv := g
      homotopyHomInvId := HomotopyCategory.homotopyOfEq _ _ (by cat_disch)
      homotopyInvHomId := HomotopyCategory.homotopyOfEq _ _ (by cat_disch) }
  exact ⟨e, rfl⟩

end HomologicalComplex

