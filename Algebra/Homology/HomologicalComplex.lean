/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison
-/
module

public import Mathlib.Algebra.Homology.ComplexShape
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.CategoryTheory.GradedObject
public import Mathlib.Algebra.Homology.ShortComplex.Basic

/-!
# Homological complexes.

A `HomologicalComplex V c` with a "shape" controlled by `c : ComplexShape ι`
has chain groups `X i` (objects in `V`) indexed by `i : ι`,
and a differential `d i j` whenever `c.Rel i j`.

We in fact ask for differentials `d i j` for all `i j : ι`,
but have a field `shape` requiring that these are zero when not allowed by `c`.
This avoids a lot of dependent type theory hell!

The composite of any two differentials `d i j ≫ d j k` must be zero.

We provide `ChainComplex V α` for
`α`-indexed chain complexes in which `d i j ≠ 0` only if `j + 1 = i`,
and similarly `CochainComplex V α`, with `i = j + 1`.

There is a category structure, where morphisms are chain maps.

For `C : HomologicalComplex V c`, we define `C.xNext i`, which is either `C.X j` for some
arbitrarily chosen `j` such that `c.r i j`, or `C.X i` if there is no such `j`.
Similarly we have `C.xPrev j`.
Defined in terms of these we have `C.dFrom i : C.X i ⟶ C.xNext i` and
`C.dTo j : C.xPrev j ⟶ C.X j`, which are either defined as `C.d i j`, or zero, as needed.
-/

@[expose] public section


universe v u

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {ι : Type*}
variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

/-- A `HomologicalComplex V c` with a "shape" controlled by `c : ComplexShape ι`
has chain groups `X i` (objects in `V`) indexed by `i : ι`,
and a differential `d i j` whenever `c.Rel i j`.

We in fact ask for differentials `d i j` for all `i j : ι`,
but have a field `shape` requiring that these are zero when not allowed by `c`.
This avoids a lot of dependent type theory hell!

The composite of any two differentials `d i j ≫ d j k` must be zero.
-/
/-
**HomologicalComplex** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：HomologicalComplex (c : ComplexShape ι) where X : ι -> V d : forall i j, X
 i ⟶ X j shape : forall i j, ¬c.Rel i j -> d i j = 0
参数：c : ComplexShape ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `HomologicalComplex V c` with a "shape" controlled by `c : ComplexShape ι`
has chain groups `X i` (objects in `V`) indexed by `i : ι`,
and a differential `d i j` whenever `c.Rel i j`.

We in fact ask for differentials `d i j` for all `i j : ι`,
but have a field `shape` requiring that these are zero when not allowed by `c`.
This avoids a lot of dependent type theory hell!

The composite of any two differentials `d i j ≫ d j k` must be zero.
-/
structure HomologicalComplex (c : ComplexShape ι) where
  X : ι → V
  d : ∀ i j, X i ⟶ X j
  shape : ∀ i j, ¬c.Rel i j → d i j = 0 := by cat_disch
  d_comp_d' : ∀ i j k, c.Rel i j → c.Rel j k → d i j ≫ d j k = 0 := by cat_disch

namespace HomologicalComplex

attribute [simp] shape

variable {V} {c : ComplexShape ι}

@[reassoc (attr := simp)]
/-
**HomologicalComplex.d_comp_d** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComplex`。
形式化陈述：d_comp_d (C : HomologicalComplex V c) (i j k : ι) : C.d i j ≫ C.d j k = 0
参数：C : HomologicalComplex V c；i j k : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.d_comp_d'`：∀ {ι : Type u_1} {V : Type u} [inst : Cate
goryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms
 V] {c : ComplexSh…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.shape`：∀ {ι : Type u_1} {V : Type u} [inst : Category
Theory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] 
{c : ComplexSh…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
-/
theorem d_comp_d (C : HomologicalComplex V c) (i j k : ι) : C.d i j ≫ C.d j k = 0 := by
  by_cases hij : c.Rel i j
  · by_cases hjk : c.Rel j k
    · exact C.d_comp_d' i j k hij hjk
    · rw [C.shape j k hjk, comp_zero]
  · rw [C.shape i j hij, zero_comp]
/-
**HomologicalComplex.ext** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComplex`。
形式化陈述：ext {C₁ C₂ : HomologicalComplex V c} (h_X : C₁.X = C₂.X) (h_d : forall i j
 : ι, c.Rel i j -> C₁.d i j ≫ eqToHom (congr_fun h_X j) = eqToHom (congr_fun h_X
 i) ≫ C₂.d i j) : C₁ = C₂
参数：h_X : C₁.X = C₂.X；h_d : forall i j : ι, c.Rel i j -> C₁.d i j ≫ eqToHom (cong
r_fun h_X j) = eqToHom (congr_fun h_X i) ≫ C₂.d i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HomologicalComplex.mk.injEq`：∀ {ι : Type u_1} {V : Type u} [inst : Categ
oryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
V] {c : ComplexSh…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
theorem ext {C₁ C₂ : HomologicalComplex V c} (h_X : C₁.X = C₂.X)
    (h_d :
      ∀ i j : ι,
        c.Rel i j → C₁.d i j ≫ eqToHom (congr_fun h_X j) = eqToHom (congr_fun h_X i) ≫ C₂.d i j) :
    C₁ = C₂ := by
  obtain ⟨X₁, d₁, s₁, h₁⟩ := C₁
  obtain ⟨X₂, d₂, s₂, h₂⟩ := C₂
  dsimp at h_X
  subst h_X
  simp only [mk.injEq, heq_eq_eq, true_and]
  ext i j
  by_cases hij : c.Rel i j
  · simpa only [comp_id, id_comp, eqToHom_refl] using h_d i j hij
  · rw [s₁ i j hij, s₂ i j hij]

/-- The obvious isomorphism `K.X p ≅ K.X q` when `p = q`. -/
/-
**HomologicalComplex.XIsoOfEq** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：XIsoOfEq (K : HomologicalComplex V c) {p q : ι} (h : p = q) : K.X p ≅ K.X 
q
参数：K : HomologicalComplex V c；h : p = q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious isomorphism `K.X p ≅ K.X q` when `p = q`.
-/
def XIsoOfEq (K : HomologicalComplex V c) {p q : ι} (h : p = q) : K.X p ≅ K.X q :=
  eqToIso (by rw [h])

@[simp]
/-
**HomologicalComplex.XIsoOfEq_rfl** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`
。
形式化陈述：XIsoOfEq_rfl (K : HomologicalComplex V c) (p : ι) : K.XIsoOfEq (rfl : p = 
p) = Iso.refl _
参数：K : HomologicalComplex V c；p : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma XIsoOfEq_rfl (K : HomologicalComplex V c) (p : ι) :
    K.XIsoOfEq (rfl : p = p) = Iso.refl _ := rfl

@[reassoc (attr := simp)]
/-
**HomologicalComplex.XIsoOfEq_hom_comp_XIsoOfEq_hom** 是 Mathlib 中的一个引理，位于命名空间 `H
omologicalComplex`。
形式化陈述：XIsoOfEq_hom_comp_XIsoOfEq_hom (K : HomologicalComplex V c) {p₁ p₂ p₃ : ι}
 (h₁₂ : p₁ = p₂) (h₂₃ : p₂ = p₃) : (K.XIsoOfEq h₁₂).hom ≫ (K.XIsoOfEq h₂₃).hom =
 (K.XIsoOfEq (h₁₂.trans h₂₃)).hom
参数：K : HomologicalComplex V c；h₁₂ : p₁ = p₂；h₂₃ : p₂ = p₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma XIsoOfEq_hom_comp_XIsoOfEq_hom (K : HomologicalComplex V c) {p₁ p₂ p₃ : ι}
    (h₁₂ : p₁ = p₂) (h₂₃ : p₂ = p₃) :
    (K.XIsoOfEq h₁₂).hom ≫ (K.XIsoOfEq h₂₃).hom = (K.XIsoOfEq (h₁₂.trans h₂₃)).hom := by
  dsimp [XIsoOfEq]
  simp only [eqToHom_trans]

@[reassoc (attr := simp)]
/-
**HomologicalComplex.XIsoOfEq_hom_comp_XIsoOfEq_inv** 是 Mathlib 中的一个引理，位于命名空间 `H
omologicalComplex`。
形式化陈述：XIsoOfEq_hom_comp_XIsoOfEq_inv (K : HomologicalComplex V c) {p₁ p₂ p₃ : ι}
 (h₁₂ : p₁ = p₂) (h₃₂ : p₃ = p₂) : (K.XIsoOfEq h₁₂).hom ≫ (K.XIsoOfEq h₃₂).inv =
 (K.XIsoOfEq (h₁₂.trans h₃₂.symm)).hom
参数：K : HomologicalComplex V c；h₁₂ : p₁ = p₂；h₃₂ : p₃ = p₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma XIsoOfEq_hom_comp_XIsoOfEq_inv (K : HomologicalComplex V c) {p₁ p₂ p₃ : ι}
    (h₁₂ : p₁ = p₂) (h₃₂ : p₃ = p₂) :
    (K.XIsoOfEq h₁₂).hom ≫ (K.XIsoOfEq h₃₂).inv = (K.XIsoOfEq (h₁₂.trans h₃₂.symm)).hom := by
  dsimp [XIsoOfEq]
  simp only [eqToHom_trans]

@[reassoc (attr := simp)]
/-
**HomologicalComplex.XIsoOfEq_inv_comp_XIsoOfEq_hom** 是 Mathlib 中的一个引理，位于命名空间 `H
omologicalComplex`。
形式化陈述：XIsoOfEq_inv_comp_XIsoOfEq_hom (K : HomologicalComplex V c) {p₁ p₂ p₃ : ι}
 (h₂₁ : p₂ = p₁) (h₂₃ : p₂ = p₃) : (K.XIsoOfEq h₂₁).inv ≫ (K.XIsoOfEq h₂₃).hom =
 (K.XIsoOfEq (h₂₁.symm.trans h₂₃)).hom
参数：K : HomologicalComplex V c；h₂₁ : p₂ = p₁；h₂₃ : p₂ = p₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma XIsoOfEq_inv_comp_XIsoOfEq_hom (K : HomologicalComplex V c) {p₁ p₂ p₃ : ι}
    (h₂₁ : p₂ = p₁) (h₂₃ : p₂ = p₃) :
    (K.XIsoOfEq h₂₁).inv ≫ (K.XIsoOfEq h₂₃).hom = (K.XIsoOfEq (h₂₁.symm.trans h₂₃)).hom := by
  dsimp [XIsoOfEq]
  simp only [eqToHom_trans]

@[reassoc (attr := simp)]
/-
**HomologicalComplex.XIsoOfEq_inv_comp_XIsoOfEq_inv** 是 Mathlib 中的一个引理，位于命名空间 `H
omologicalComplex`。
形式化陈述：XIsoOfEq_inv_comp_XIsoOfEq_inv (K : HomologicalComplex V c) {p₁ p₂ p₃ : ι}
 (h₂₁ : p₂ = p₁) (h₃₂ : p₃ = p₂) : (K.XIsoOfEq h₂₁).inv ≫ (K.XIsoOfEq h₃₂).inv =
 (K.XIsoOfEq (h₃₂.trans h₂₁).symm).hom
参数：K : HomologicalComplex V c；h₂₁ : p₂ = p₁；h₃₂ : p₃ = p₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma XIsoOfEq_inv_comp_XIsoOfEq_inv (K : HomologicalComplex V c) {p₁ p₂ p₃ : ι}
    (h₂₁ : p₂ = p₁) (h₃₂ : p₃ = p₂) :
    (K.XIsoOfEq h₂₁).inv ≫ (K.XIsoOfEq h₃₂).inv = (K.XIsoOfEq (h₃₂.trans h₂₁).symm).hom := by
  dsimp [XIsoOfEq]
  simp only [eqToHom_trans]

@[reassoc (attr := simp)]
/-
**HomologicalComplex.XIsoOfEq_hom_comp_d** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalC
omplex`。
形式化陈述：XIsoOfEq_hom_comp_d (K : HomologicalComplex V c) {p₁ p₂ : ι} (h : p₁ = p₂)
 (p₃ : ι) : (K.XIsoOfEq h).hom ≫ K.d p₂ p₃ = K.d p₁ p₃
参数：K : HomologicalComplex V c；h : p₁ = p₂；p₃ : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma XIsoOfEq_hom_comp_d (K : HomologicalComplex V c) {p₁ p₂ : ι} (h : p₁ = p₂) (p₃ : ι) :
    (K.XIsoOfEq h).hom ≫ K.d p₂ p₃ = K.d p₁ p₃ := by subst h; simp

@[reassoc (attr := simp)]
/-
**HomologicalComplex.XIsoOfEq_inv_comp_d** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalC
omplex`。
形式化陈述：XIsoOfEq_inv_comp_d (K : HomologicalComplex V c) {p₂ p₁ : ι} (h : p₂ = p₁)
 (p₃ : ι) : (K.XIsoOfEq h).inv ≫ K.d p₂ p₃ = K.d p₁ p₃
参数：K : HomologicalComplex V c；h : p₂ = p₁；p₃ : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma XIsoOfEq_inv_comp_d (K : HomologicalComplex V c) {p₂ p₁ : ι} (h : p₂ = p₁) (p₃ : ι) :
    (K.XIsoOfEq h).inv ≫ K.d p₂ p₃ = K.d p₁ p₃ := by subst h; simp

@[reassoc (attr := simp)]
/-
**HomologicalComplex.d_comp_XIsoOfEq_hom** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalC
omplex`。
形式化陈述：d_comp_XIsoOfEq_hom (K : HomologicalComplex V c) {p₂ p₃ : ι} (h : p₂ = p₃)
 (p₁ : ι) : K.d p₁ p₂ ≫ (K.XIsoOfEq h).hom = K.d p₁ p₃
参数：K : HomologicalComplex V c；h : p₂ = p₃；p₁ : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma d_comp_XIsoOfEq_hom (K : HomologicalComplex V c) {p₂ p₃ : ι} (h : p₂ = p₃) (p₁ : ι) :
    K.d p₁ p₂ ≫ (K.XIsoOfEq h).hom = K.d p₁ p₃ := by subst h; simp

@[reassoc (attr := simp)]
/-
**HomologicalComplex.d_comp_XIsoOfEq_inv** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalC
omplex`。
形式化陈述：d_comp_XIsoOfEq_inv (K : HomologicalComplex V c) {p₂ p₃ : ι} (h : p₃ = p₂)
 (p₁ : ι) : K.d p₁ p₂ ≫ (K.XIsoOfEq h).inv = K.d p₁ p₃
参数：K : HomologicalComplex V c；h : p₃ = p₂；p₁ : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma d_comp_XIsoOfEq_inv (K : HomologicalComplex V c) {p₂ p₃ : ι} (h : p₃ = p₂) (p₁ : ι) :
    K.d p₁ p₂ ≫ (K.XIsoOfEq h).inv = K.d p₁ p₃ := by subst h; simp

end HomologicalComplex

/-- An `α`-indexed chain complex is a `HomologicalComplex`
in which `d i j ≠ 0` only if `j + 1 = i`.
-/
/-
**ChainComplex** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：ChainComplex (α : Type*) [AddRightCancelSemigroup α] [One α] : Type _
参数：α : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G

--- 原说明 ---
An `α`-indexed chain complex is a `HomologicalComplex`
in which `d i j ≠ 0` only if `j + 1 = i`.
-/
abbrev ChainComplex (α : Type*) [AddRightCancelSemigroup α] [One α] : Type _ :=
  HomologicalComplex V (ComplexShape.down α)

/-- An `α`-indexed cochain complex is a `HomologicalComplex`
in which `d i j ≠ 0` only if `i + 1 = j`.
-/
/-
**CochainComplex** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：CochainComplex (α : Type*) [AddRightCancelSemigroup α] [One α] : Type _
参数：α : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G

--- 原说明 ---
An `α`-indexed cochain complex is a `HomologicalComplex`
in which `d i j ≠ 0` only if `i + 1 = j`.
-/
abbrev CochainComplex (α : Type*) [AddRightCancelSemigroup α] [One α] : Type _ :=
  HomologicalComplex V (ComplexShape.up α)

namespace ChainComplex

@[simp]
/-
**ChainComplex.prev** 是 Mathlib 中的一个定理，位于命名空间 `ChainComplex`。
形式化陈述：prev (α : Type*) [AddRightCancelSemigroup α] [One α] (i : α) : (ComplexSha
pe.down α).prev i = i + 1
参数：α : Type*；i : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.prev_eq'`：∀ {ι : Type u_1} (c : ComplexShape ι) {i j : ι}, 
c.Rel j i → c.prev i = j
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem prev (α : Type*) [AddRightCancelSemigroup α] [One α] (i : α) :
    (ComplexShape.down α).prev i = i + 1 :=
  (ComplexShape.down α).prev_eq' rfl

@[simp]
/-
**ChainComplex.next** 是 Mathlib 中的一个定理，位于命名空间 `ChainComplex`。
形式化陈述：next (α : Type*) [AddGroup α] [One α] (i : α) : (ComplexShape.down α).next
 i = i - 1
参数：α : Type*；i : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.next_eq'`：next_eq' (c : ComplexShape ι) {i j : ι} (h : c.Re
l i j) : c.next i = j
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
-/
theorem next (α : Type*) [AddGroup α] [One α] (i : α) : (ComplexShape.down α).next i = i - 1 :=
  (ComplexShape.down α).next_eq' <| sub_add_cancel _ _

@[simp]
/-
**ChainComplex.next_nat_zero** 是 Mathlib 中的一个定理，位于命名空间 `ChainComplex`。
形式化陈述：next_nat_zero : (ComplexShape.down Nat).next 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem next_nat_zero : (ComplexShape.down ℕ).next 0 = 0 := by
  refine dif_neg ?_
  push Not
  intro
  apply Nat.noConfusion

@[simp]
/-
**ChainComplex.next_nat_succ** 是 Mathlib 中的一个定理，位于命名空间 `ChainComplex`。
形式化陈述：next_nat_succ (i : Nat) : (ComplexShape.down Nat).next (i + 1) = i
参数：i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.next_eq'`：next_eq' (c : ComplexShape ι) {i j : ι} (h : c.Re
l i j) : c.next i = j
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem next_nat_succ (i : ℕ) : (ComplexShape.down ℕ).next (i + 1) = i :=
  (ComplexShape.down ℕ).next_eq' rfl

end ChainComplex

namespace CochainComplex

@[simp]
/-
**CochainComplex.prev** 是 Mathlib 中的一个定理，位于命名空间 `CochainComplex`。
形式化陈述：prev (α : Type*) [AddGroup α] [One α] (i : α) : (ComplexShape.up α).prev i
 = i - 1
参数：α : Type*；i : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.prev_eq'`：∀ {ι : Type u_1} (c : ComplexShape ι) {i j : ι}, 
c.Rel j i → c.prev i = j
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
-/
theorem prev (α : Type*) [AddGroup α] [One α] (i : α) : (ComplexShape.up α).prev i = i - 1 :=
  (ComplexShape.up α).prev_eq' <| sub_add_cancel _ _

@[simp]
/-
**CochainComplex.next** 是 Mathlib 中的一个定理，位于命名空间 `CochainComplex`。
形式化陈述：next (α : Type*) [AddRightCancelSemigroup α] [One α] (i : α) : (ComplexSha
pe.up α).next i = i + 1
参数：α : Type*；i : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.next_eq'`：next_eq' (c : ComplexShape ι) {i j : ι} (h : c.Re
l i j) : c.next i = j
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem next (α : Type*) [AddRightCancelSemigroup α] [One α] (i : α) :
    (ComplexShape.up α).next i = i + 1 :=
  (ComplexShape.up α).next_eq' rfl

@[simp]
/-
**CochainComplex.prev_nat_zero** 是 Mathlib 中的一个定理，位于命名空间 `CochainComplex`。
形式化陈述：prev_nat_zero : (ComplexShape.up Nat).prev 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem prev_nat_zero : (ComplexShape.up ℕ).prev 0 = 0 := by
  refine dif_neg ?_
  push Not
  intro
  apply Nat.noConfusion

@[simp]
/-
**CochainComplex.prev_nat_succ** 是 Mathlib 中的一个定理，位于命名空间 `CochainComplex`。
形式化陈述：prev_nat_succ (i : Nat) : (ComplexShape.up Nat).prev (i + 1) = i
参数：i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.prev_eq'`：∀ {ι : Type u_1} (c : ComplexShape ι) {i j : ι}, 
c.Rel j i → c.prev i = j
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem prev_nat_succ (i : ℕ) : (ComplexShape.up ℕ).prev (i + 1) = i :=
  (ComplexShape.up ℕ).prev_eq' rfl

end CochainComplex

namespace HomologicalComplex

variable {V}
variable {c : ComplexShape ι} (C : HomologicalComplex V c)

/-- A morphism of homological complexes consists of maps between the chain groups,
commuting with the differentials.
-/
@[ext]
/-
**HomologicalComplex.Hom** 是 Mathlib 中的一个结构，位于命名空间 `HomologicalComplex`。
形式化陈述：Hom (A B : HomologicalComplex V c) where f : forall i, A.X i ⟶ B.X i comm'
 : forall i j, c.Rel i j -> f i ≫ B.d i j = A.d i j ≫ f j
参数：A B : HomologicalComplex V c。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of homological complexes consists of maps between the chain groups,
commuting with the differentials.
-/
structure Hom (A B : HomologicalComplex V c) where
  f : ∀ i, A.X i ⟶ B.X i
  comm' : ∀ i j, c.Rel i j → f i ≫ B.d i j = A.d i j ≫ f j := by cat_disch

@[reassoc (attr := simp)]
/-
**HomologicalComplex.Hom.comm** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComplex.Hom`
。
形式化陈述：∀ {ι : Type u_1} {V : Type u} [inst : CategoryTheory.Category.{v, u} V]   
[inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] {c : ComplexShape ι} {A B : 
HomologicalComplex V c} (f : A.Hom B)   (i j : ι), CategoryTheory.CategoryStruct
.comp (f.f i) (B.d i j) = CategoryTheory.CategoryStruct.comp (A.d i j) (f.f j)
参数：f : A.Hom B；i j : ι；f.f i；B.d i j；A.d i j；f.f j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.Hom.comm'`：∀ {ι : Type u_1} {V : Type u} [inst : Cate
goryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms
 V] {c : ComplexSh…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.shape`：∀ {ι : Type u_1} {V : Type u} [inst : Category
Theory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] 
{c : ComplexSh…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
-/
theorem Hom.comm {A B : HomologicalComplex V c} (f : A.Hom B) (i j : ι) :
    f.f i ≫ B.d i j = A.d i j ≫ f.f j := by
  by_cases hij : c.Rel i j
  · exact f.comm' i j hij
  · rw [A.shape i j hij, B.shape i j hij, comp_zero, zero_comp]
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (A B : HomologicalComplex V c) : Inhabited (Hom A B) :=
  ⟨{ f := fun _ => 0 }⟩

/-- Identity chain map. -/
/-
**HomologicalComplex.id** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：id (A : HomologicalComplex V c) : Hom A A where f _
参数：A : HomologicalComplex V c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Identity chain map.
-/
def id (A : HomologicalComplex V c) : Hom A A where f _ := 𝟙 _

/-- Composition of chain maps. -/
/-
**HomologicalComplex.comp** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：comp (A B C : HomologicalComplex V c) (φ : Hom A B) (ψ : Hom B C) : Hom A 
C where f i
参数：A B C : HomologicalComplex V c；φ : Hom A B；ψ : Hom B C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of chain maps.
-/
def comp (A B C : HomologicalComplex V c) (φ : Hom A B) (ψ : Hom B C) : Hom A C where
  f i := φ.f i ≫ ψ.f i

section

attribute [local simp] id comp

/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (HomologicalComplex V c) where
  Hom := Hom
  id := id
  comp := comp _ _ _

end

@[ext]
/-
**HomologicalComplex.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`。
形式化陈述：hom_ext {C D : HomologicalComplex V c} (f g : C ⟶ D) (h : forall i, f.f i 
= g.f i) : f = g
参数：f g : C ⟶ D；h : forall i, f.f i = g.f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.Hom.ext`：∀ {ι : Type u_1} {V : Type u} {inst : Catego
ryTheory.Category.{v, u} V}   {inst_1 : CategoryTheory.Limits.HasZeroMorphisms V
} {c : ComplexSh…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma hom_ext {C D : HomologicalComplex V c} (f g : C ⟶ D)
    (h : ∀ i, f.f i = g.f i) : f = g := by
  apply Hom.ext
  funext
  apply h

@[simp]
/-
**HomologicalComplex.id_f** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComplex`。
形式化陈述：id_f (C : HomologicalComplex V c) (i : ι) : Hom.f (𝟙 C) i = 𝟙 (C.X i)
参数：C : HomologicalComplex V c；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_f (C : HomologicalComplex V c) (i : ι) : Hom.f (𝟙 C) i = 𝟙 (C.X i) :=
  rfl

@[simp, reassoc]
/-
**HomologicalComplex.comp_f** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComplex`。
形式化陈述：comp_f {C₁ C₂ C₃ : HomologicalComplex V c} (f : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i 
: ι) : (f ≫ g).f i = f.f i ≫ g.f i
参数：f : C₁ ⟶ C₂；g : C₂ ⟶ C₃；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_f {C₁ C₂ C₃ : HomologicalComplex V c} (f : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i : ι) :
    (f ≫ g).f i = f.f i ≫ g.f i :=
  rfl

@[simp]
/-
**HomologicalComplex.eqToHom_f** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComplex`。
形式化陈述：eqToHom_f {C₁ C₂ : HomologicalComplex V c} (h : C₁ = C₂) (n : ι) : Homolog
icalComplex.Hom.f (eqToHom h) n = eqToHom (congr_fun (congr_arg HomologicalCompl
ex.X h) n)
参数：h : C₁ = C₂；n : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem eqToHom_f {C₁ C₂ : HomologicalComplex V c} (h : C₁ = C₂) (n : ι) :
    HomologicalComplex.Hom.f (eqToHom h) n =
      eqToHom (congr_fun (congr_arg HomologicalComplex.X h) n) := by
  subst h
  rfl

-- We'll use this later to show that `HomologicalComplex V c` is preadditive when `V` is.
/-
**HomologicalComplex.hom_f_injective** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalCompl
ex`。
形式化陈述：hom_f_injective {C₁ C₂ : HomologicalComplex V c} : Function.Injective fun 
f : Hom C₁ C₂ => f.f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.Hom.ext`：∀ {ι : Type u_1} {V : Type u} {inst : Catego
ryTheory.Category.{v, u} V}   {inst_1 : CategoryTheory.Limits.HasZeroMorphisms V
} {c : ComplexSh…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem hom_f_injective {C₁ C₂ : HomologicalComplex V c} :
    Function.Injective fun f : Hom C₁ C₂ => f.f := by cat_disch
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X Y : HomologicalComplex V c) : Zero (X ⟶ Y) :=
  ⟨{ f := fun _ => 0}⟩

@[simp]
/-
**HomologicalComplex.zero_f** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComplex`。
形式化陈述：zero_f (C D : HomologicalComplex V c) (i : ι) : (0 : C ⟶ D).f i = 0
参数：C D : HomologicalComplex V c；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_f (C D : HomologicalComplex V c) (i : ι) : (0 : C ⟶ D).f i = 0 :=
  rfl
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasZeroMorphisms (HomologicalComplex V c) where

open ZeroObject

/-- The zero complex -/
/-
**HomologicalComplex.zero** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：zero [HasZeroObject V] : HomologicalComplex V c where X _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The zero complex
-/
noncomputable def zero [HasZeroObject V] : HomologicalComplex V c where
  X _ := 0
  d _ _ := 0
/-
**HomologicalComplex.isZero_zero** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComplex`。
形式化陈述：isZero_zero [HasZeroObject V] : IsZero (zero : HomologicalComplex V c)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem isZero_zero [HasZeroObject V] : IsZero (zero : HomologicalComplex V c) := by
  refine ⟨fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩⟩
  all_goals
    ext
    dsimp only [zero]
    subsingleton
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasZeroObject V] : HasZeroObject (HomologicalComplex V c) :=
  ⟨⟨zero, isZero_zero⟩⟩
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [HasZeroObject V] : Inhabited (HomologicalComplex V c) :=
  ⟨zero⟩
/-
**HomologicalComplex.congr_hom** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComplex`。
形式化陈述：congr_hom {C D : HomologicalComplex V c} {f g : C ⟶ D} (w : f = g) (i : ι)
 : f.f i = g.f i
参数：w : f = g；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem congr_hom {C D : HomologicalComplex V c} {f g : C ⟶ D} (w : f = g) (i : ι) :
    f.f i = g.f i :=
  congr_fun (congr_arg Hom.f w) i
/-
**HomologicalComplex.mono_of_mono_f** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComple
x`。
形式化陈述：mono_of_mono_f {K L : HomologicalComplex V c} (φ : K ⟶ L) (hφ : forall i, 
Mono (φ.f i)) : Mono φ where right_cancellation g h eq
参数：φ : K ⟶ L；hφ : forall i, Mono (φ.f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `HomologicalComplex.congr_hom`：congr_hom {C D : HomologicalComplex V c} {
f g : C ⟶ D} (w : f = g) (i : ι) : f.f i = g.f i
-/
lemma mono_of_mono_f {K L : HomologicalComplex V c} (φ : K ⟶ L)
    (hφ : ∀ i, Mono (φ.f i)) : Mono φ where
  right_cancellation g h eq := by
    ext i
    rw [← cancel_mono (φ.f i)]
    exact congr_hom eq i
/-
**HomologicalComplex.epi_of_epi_f** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`
。
形式化陈述：epi_of_epi_f {K L : HomologicalComplex V c} (φ : K ⟶ L) (hφ : forall i, Ep
i (φ.f i)) : Epi φ where left_cancellation g h eq
参数：φ : K ⟶ L；hφ : forall i, Epi (φ.f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `HomologicalComplex.congr_hom`：congr_hom {C D : HomologicalComplex V c} {
f g : C ⟶ D} (w : f = g) (i : ι) : f.f i = g.f i
-/
lemma epi_of_epi_f {K L : HomologicalComplex V c} (φ : K ⟶ L)
    (hφ : ∀ i, Epi (φ.f i)) : Epi φ where
  left_cancellation g h eq := by
    ext i
    rw [← cancel_epi (φ.f i)]
    exact congr_hom eq i

section

variable (V c)

/-- The functor picking out the `i`-th object of a complex. -/
@[simps]
/-
**HomologicalComplex.eval** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：eval (i : ι) : HomologicalComplex V c ⥤ V where obj C
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor picking out the `i`-th object of a complex.
-/
def eval (i : ι) : HomologicalComplex V c ⥤ V where
  obj C := C.X i
  map f := f.f i
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (i : ι) : (eval V c i).PreservesZeroMorphisms where

/-- The functor forgetting the differential in a complex, obtaining a graded object. -/
@[simps]
/-
**HomologicalComplex.forget** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：forget : HomologicalComplex V c ⥤ GradedObject ι V where obj C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor forgetting the differential in a complex, obtaining a graded object.
-/
def forget : HomologicalComplex V c ⥤ GradedObject ι V where
  obj C := C.X
  map f := f.f
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget V c).Faithful where
  map_injective h := by
    ext i
    exact congr_fun h i

set_option backward.defeqAttrib.useBackward true in
/-- Forgetting the differentials than picking out the `i`-th object is the same as
just picking out the `i`-th object. -/
@[simps!]
/-
**HomologicalComplex.forgetEval** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：forgetEval (i : ι) : forget V c ⋙ GradedObject.eval i ≅ eval V c i
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Forgetting the differentials than picking out the `i`-th object is the same as
just picking out the `i`-th object.
-/
def forgetEval (i : ι) : forget V c ⋙ GradedObject.eval i ≅ eval V c i :=
  NatIso.ofComponents fun _ => Iso.refl _

set_option backward.defeqAttrib.useBackward true in
/-- The differential as a natural transformation between `eval`. -/
/-
**HomologicalComplex.dNatTrans** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：{ι : Type u_1} →   (V : Type u) →     [inst : CategoryTheory.Category.{v, 
u} V] →       [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] →         (c :
 ComplexShape ι) → (i j : ι) → HomologicalComplex.eval V c i ⟶ HomologicalComple
x.eval V c j
参数：V : Type u；c : ComplexShape ι；i j : ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The differential as a natural transformation between `eval`.
-/
@[simps] def dNatTrans (i j : ι) :
    HomologicalComplex.eval V c i ⟶ HomologicalComplex.eval V c j where
  app X := X.d i j

end

noncomputable section

@[reassoc]
/-
**HomologicalComplex.XIsoOfEq_hom_naturality** 是 Mathlib 中的一个引理，位于命名空间 `Homologi
calComplex`。
形式化陈述：XIsoOfEq_hom_naturality {K L : HomologicalComplex V c} (φ : K ⟶ L) {n n' :
 ι} (h : n = n') : φ.f n ≫ (L.XIsoOfEq h).hom = (K.XIsoOfEq h).hom ≫ φ.f n'
参数：φ : K ⟶ L；h : n = n'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
lemma XIsoOfEq_hom_naturality {K L : HomologicalComplex V c} (φ : K ⟶ L) {n n' : ι} (h : n = n') :
    φ.f n ≫ (L.XIsoOfEq h).hom = (K.XIsoOfEq h).hom ≫ φ.f n' := by subst h; simp

@[reassoc]
/-
**HomologicalComplex.XIsoOfEq_inv_naturality** 是 Mathlib 中的一个引理，位于命名空间 `Homologi
calComplex`。
形式化陈述：XIsoOfEq_inv_naturality {K L : HomologicalComplex V c} (φ : K ⟶ L) {n n' :
 ι} (h : n = n') : φ.f n' ≫ (L.XIsoOfEq h).inv = (K.XIsoOfEq h).inv ≫ φ.f n
参数：φ : K ⟶ L；h : n = n'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
lemma XIsoOfEq_inv_naturality {K L : HomologicalComplex V c} (φ : K ⟶ L) {n n' : ι} (h : n = n') :
    φ.f n' ≫ (L.XIsoOfEq h).inv = (K.XIsoOfEq h).inv ≫ φ.f n := by subst h; simp

/-- If `C.d i j` and `C.d i j'` are both allowed, then we must have `j = j'`,
and so the differentials only differ by an `eqToHom`.
-/
@[simp]
/-
**HomologicalComplex.d_comp_eqToHom** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComple
x`。
形式化陈述：d_comp_eqToHom {i j j' : ι} (rij : c.Rel i j) (rij' : c.Rel i j') : C.d i 
j' ≫ eqToHom (congr_arg C.X (c.next_eq rij' rij)) = C.d i j
参数：rij : c.Rel i j；rij' : c.Rel i j'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `ComplexShape.next_eq`：∀ {ι : Type u_1} (self : ComplexShape ι) {i j j' :
 ι}, self.Rel i j → self.Rel i j' → j = j'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `C.d i j` and `C.d i j'` are both allowed, then we must have `j = j'`,
and so the differentials only differ by an `eqToHom`.
-/
theorem d_comp_eqToHom {i j j' : ι} (rij : c.Rel i j) (rij' : c.Rel i j') :
    C.d i j' ≫ eqToHom (congr_arg C.X (c.next_eq rij' rij)) = C.d i j := by
  obtain rfl := c.next_eq rij rij'
  simp only [eqToHom_refl, comp_id]

/-- If `C.d i j` and `C.d i' j` are both allowed, then we must have `i = i'`,
and so the differentials only differ by an `eqToHom`.
-/
@[simp]
/-
**HomologicalComplex.eqToHom_comp_d** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComple
x`。
形式化陈述：eqToHom_comp_d {i i' j : ι} (rij : c.Rel i j) (rij' : c.Rel i' j) : eqToHo
m (congr_arg C.X (c.prev_eq rij rij')) ≫ C.d i' j = C.d i j
参数：rij : c.Rel i j；rij' : c.Rel i' j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ComplexShape.prev_eq`：∀ {ι : Type u_1} (self : ComplexShape ι) {i i' j :
 ι}, self.Rel i j → self.Rel i' j → i = i'

--- 原说明 ---
If `C.d i j` and `C.d i' j` are both allowed, then we must have `i = i'`,
and so the differentials only differ by an `eqToHom`.
-/
theorem eqToHom_comp_d {i i' j : ι} (rij : c.Rel i j) (rij' : c.Rel i' j) :
    eqToHom (congr_arg C.X (c.prev_eq rij rij')) ≫ C.d i' j = C.d i j := by
  obtain rfl := c.prev_eq rij rij'
  simp only [eqToHom_refl, id_comp]
/-
**HomologicalComplex.kernel_eq_kernel** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComp
lex`。
形式化陈述：kernel_eq_kernel [HasKernels V] {i j j' : ι} (r : c.Rel i j) (r' : c.Rel i
 j') : kernelSubobject (C.d i j) = kernelSubobject (C.d i j')
参数：r : c.Rel i j；r' : c.Rel i j'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `ComplexShape.next_eq`：∀ {ι : Type u_1} (self : ComplexShape ι) {i j j' :
 ι}, self.Rel i j → self.Rel i j' → j = j'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HomologicalComplex.d_comp_eqToHom`：d_comp_eqToHom {i j j' : ι} (rij : c.
Rel i j) (rij' : c.Rel i j') : C.d i j' ≫ eqToHom (congr_arg C.X (c.next_eq rij'
 rij)) = C.d i j
· 使用定理 `CategoryTheory.Limits.kernelSubobject_comp_mono`：kernelSubobject_comp_mo
no (f : X ⟶ Y) [HasKernel f] {Z : C} (h : Y ⟶ Z) [Mono h] : kernelSubobject (f ≫
 h) = kernelSubobject f
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.instIsIsoEqToHom`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (h : X = Y),   CategoryTheory.IsIso (CategoryTheo
ry.eqToHom h)
-/
theorem kernel_eq_kernel [HasKernels V] {i j j' : ι} (r : c.Rel i j) (r' : c.Rel i j') :
    kernelSubobject (C.d i j) = kernelSubobject (C.d i j') := by
  rw [← d_comp_eqToHom C r r']
  apply kernelSubobject_comp_mono
/-
**HomologicalComplex.image_eq_image** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComple
x`。
形式化陈述：image_eq_image [HasImages V] [HasEqualizers V] {i i' j : ι} (r : c.Rel i j
) (r' : c.Rel i' j) : imageSubobject (C.d i j) = imageSubobject (C.d i' j)
参数：r : c.Rel i j；r' : c.Rel i' j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasImages.has_image`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasImages C] {X Y : C}
   (f : X ⟶ Y), CategoryTheory.…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `ComplexShape.prev_eq`：∀ {ι : Type u_1} (self : ComplexShape ι) {i i' j :
 ι}, self.Rel i j → self.Rel i' j → i = i'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HomologicalComplex.eqToHom_comp_d`：eqToHom_comp_d {i i' j : ι} (rij : c.
Rel i j) (rij' : c.Rel i' j) : eqToHom (congr_arg C.X (c.prev_eq rij rij')) ≫ C.
d i' j = C.d i j
· 使用定理 `CategoryTheory.Limits.imageSubobject_iso_comp`：imageSubobject_iso_comp [
HasEqualizers C] {X' : C} (h : X' ⟶ X) [IsIso h] (f : X ⟶ Y) [HasImage f] : imag
eSubobject (h ≫ f) = imageSubobject…
· 使用定理 `CategoryTheory.instIsIsoEqToHom`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (h : X = Y),   CategoryTheory.IsIso (CategoryTheo
ry.eqToHom h)
-/
theorem image_eq_image [HasImages V] [HasEqualizers V] {i i' j : ι} (r : c.Rel i j)
    (r' : c.Rel i' j) : imageSubobject (C.d i j) = imageSubobject (C.d i' j) := by
  rw [← eqToHom_comp_d C r r']
  apply imageSubobject_iso_comp

section

/-- Either `C.X i`, if there is some `i` with `c.Rel i j`, or `C.X j`. -/
/-
**HomologicalComplex.xPrev** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomologicalComplex`。
形式化陈述：xPrev (j : ι) : V
参数：j : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Either `C.X i`, if there is some `i` with `c.Rel i j`, or `C.X j`.
-/
abbrev xPrev (j : ι) : V :=
  C.X (c.prev j)

/-- If `c.Rel i j`, then `C.xPrev j` is isomorphic to `C.X i`. -/
/-
**HomologicalComplex.xPrevIso** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：xPrevIso {i j : ι} (r : c.Rel i j) : C.xPrev j ≅ C.X i
参数：r : c.Rel i j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `c.Rel i j`, then `C.xPrev j` is isomorphic to `C.X i`.
-/
def xPrevIso {i j : ι} (r : c.Rel i j) : C.xPrev j ≅ C.X i :=
  eqToIso <| by rw [← c.prev_eq' r]

/-- If there is no `i` so `c.Rel i j`, then `C.xPrev j` is isomorphic to `C.X j`. -/
/-
**HomologicalComplex.xPrevIsoSelf** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`
。
形式化陈述：xPrevIsoSelf {j : ι} (h : ¬c.Rel (c.prev j) j) : C.xPrev j ≅ C.X j
参数：h : ¬c.Rel (c.prev j) j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If there is no `i` so `c.Rel i j`, then `C.xPrev j` is isomorphic to `C.X j`.
-/
def xPrevIsoSelf {j : ι} (h : ¬c.Rel (c.prev j) j) : C.xPrev j ≅ C.X j :=
  eqToIso <|
    congr_arg C.X
      (by
        dsimp [ComplexShape.prev]
        rw [dif_neg]
        push Not; intro i hi
        have : c.prev j = i := c.prev_eq' hi
        rw [this] at h; contradiction)

/-- Either `C.X j`, if there is some `j` with `c.rel i j`, or `C.X i`. -/
/-
**HomologicalComplex.xNext** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomologicalComplex`。
形式化陈述：xNext (i : ι) : V
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Either `C.X j`, if there is some `j` with `c.rel i j`, or `C.X i`.
-/
abbrev xNext (i : ι) : V :=
  C.X (c.next i)

/-- If `c.Rel i j`, then `C.xNext i` is isomorphic to `C.X j`. -/
/-
**HomologicalComplex.xNextIso** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：xNextIso {i j : ι} (r : c.Rel i j) : C.xNext i ≅ C.X j
参数：r : c.Rel i j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `c.Rel i j`, then `C.xNext i` is isomorphic to `C.X j`.
-/
def xNextIso {i j : ι} (r : c.Rel i j) : C.xNext i ≅ C.X j :=
  eqToIso <| by rw [← c.next_eq' r]

/-- If there is no `j` so `c.Rel i j`, then `C.xNext i` is isomorphic to `C.X i`. -/
/-
**HomologicalComplex.xNextIsoSelf** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`
。
形式化陈述：xNextIsoSelf {i : ι} (h : ¬c.Rel i (c.next i)) : C.xNext i ≅ C.X i
参数：h : ¬c.Rel i (c.next i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If there is no `j` so `c.Rel i j`, then `C.xNext i` is isomorphic to `C.X i`.
-/
def xNextIsoSelf {i : ι} (h : ¬c.Rel i (c.next i)) : C.xNext i ≅ C.X i :=
  eqToIso <|
    congr_arg C.X
      (by
        dsimp [ComplexShape.next]
        rw [dif_neg]; rintro ⟨j, hj⟩
        have : c.next i = j := c.next_eq' hj
        rw [this] at h; contradiction)

/-- The differential mapping into `C.X j`, or zero if there isn't one.
-/
/-
**HomologicalComplex.dTo** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomologicalComplex`。
形式化陈述：dTo (j : ι) : C.xPrev j ⟶ C.X j
参数：j : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The differential mapping into `C.X j`, or zero if there isn't one.
-/
abbrev dTo (j : ι) : C.xPrev j ⟶ C.X j :=
  C.d (c.prev j) j

/-- The differential mapping out of `C.X i`, or zero if there isn't one.
-/
/-
**HomologicalComplex.dFrom** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomologicalComplex`。
形式化陈述：dFrom (i : ι) : C.X i ⟶ C.xNext i
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The differential mapping out of `C.X i`, or zero if there isn't one.
-/
abbrev dFrom (i : ι) : C.X i ⟶ C.xNext i :=
  C.d i (c.next i)
/-
**HomologicalComplex.dTo_eq** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComplex`。
形式化陈述：dTo_eq {i j : ι} (r : c.Rel i j) : C.dTo j = (C.xPrevIso r).hom ≫ C.d i j
参数：r : c.Rel i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `ComplexShape.prev_eq'`：∀ {ι : Type u_1} (c : ComplexShape ι) {i j : ι}, 
c.Rel j i → c.prev i = j
-/
theorem dTo_eq {i j : ι} (r : c.Rel i j) : C.dTo j = (C.xPrevIso r).hom ≫ C.d i j := by
  obtain rfl := c.prev_eq' r
  exact (Category.id_comp _).symm
/-
**HomologicalComplex.dTo_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComplex`。
形式化陈述：dTo_eq_zero {j : ι} (h : ¬c.Rel (c.prev j) j) : C.dTo j = 0
参数：h : ¬c.Rel (c.prev j) j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.shape`：∀ {ι : Type u_1} {V : Type u} [inst : Category
Theory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] 
{c : ComplexSh…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dTo_eq_zero {j : ι} (h : ¬c.Rel (c.prev j) j) : C.dTo j = 0 := by
  simp [h]
/-
**HomologicalComplex.dFrom_eq** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComplex`。
形式化陈述：dFrom_eq {i j : ι} (r : c.Rel i j) : C.dFrom i = C.d i j ≫ (C.xNextIso r).
inv
参数：r : c.Rel i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `ComplexShape.next_eq'`：next_eq' (c : ComplexShape ι) {i j : ι} (h : c.Re
l i j) : c.next i = j
-/
theorem dFrom_eq {i j : ι} (r : c.Rel i j) : C.dFrom i = C.d i j ≫ (C.xNextIso r).inv := by
  obtain rfl := c.next_eq' r
  exact (Category.comp_id _).symm
/-
**HomologicalComplex.dFrom_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComplex
`。
形式化陈述：dFrom_eq_zero {i : ι} (h : ¬c.Rel i (c.next i)) : C.dFrom i = 0
参数：h : ¬c.Rel i (c.next i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.shape`：∀ {ι : Type u_1} {V : Type u} [inst : Category
Theory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] 
{c : ComplexSh…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dFrom_eq_zero {i : ι} (h : ¬c.Rel i (c.next i)) : C.dFrom i = 0 := by
  simp [h]

@[reassoc (attr := simp)]
/-
**HomologicalComplex.xPrevIso_comp_dTo** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalCom
plex`。
形式化陈述：xPrevIso_comp_dTo {i j : ι} (r : c.Rel i j) : (C.xPrevIso r).inv ≫ C.dTo j
 = C.d i j
参数：r : c.Rel i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.dTo_eq`：dTo_eq {i j : ι} (r : c.Rel i j) : C.dTo j = 
(C.xPrevIso r).hom ≫ C.d i j
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem xPrevIso_comp_dTo {i j : ι} (r : c.Rel i j) : (C.xPrevIso r).inv ≫ C.dTo j = C.d i j := by
  simp [C.dTo_eq r]

@[reassoc]
/-
**HomologicalComplex.xPrevIsoSelf_comp_dTo** 是 Mathlib 中的一个定理，位于命名空间 `Homologica
lComplex`。
形式化陈述：xPrevIsoSelf_comp_dTo {j : ι} (h : ¬c.Rel (c.prev j) j) : (C.xPrevIsoSelf 
h).inv ≫ C.dTo j = 0
参数：h : ¬c.Rel (c.prev j) j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.shape`：∀ {ι : Type u_1} {V : Type u} [inst : Category
Theory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] 
{c : ComplexSh…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem xPrevIsoSelf_comp_dTo {j : ι} (h : ¬c.Rel (c.prev j) j) :
    (C.xPrevIsoSelf h).inv ≫ C.dTo j = 0 := by simp [h]

@[reassoc (attr := simp)]
/-
**HomologicalComplex.dFrom_comp_xNextIso** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalC
omplex`。
形式化陈述：dFrom_comp_xNextIso {i j : ι} (r : c.Rel i j) : C.dFrom i ≫ (C.xNextIso r)
.hom = C.d i j
参数：r : c.Rel i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.dFrom_eq`：dFrom_eq {i j : ι} (r : c.Rel i j) : C.dFro
m i = C.d i j ≫ (C.xNextIso r).inv
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
theorem dFrom_comp_xNextIso {i j : ι} (r : c.Rel i j) :
    C.dFrom i ≫ (C.xNextIso r).hom = C.d i j := by
  simp [C.dFrom_eq r]

@[reassoc]
/-
**HomologicalComplex.dFrom_comp_xNextIsoSelf** 是 Mathlib 中的一个定理，位于命名空间 `Homologi
calComplex`。
形式化陈述：dFrom_comp_xNextIsoSelf {i : ι} (h : ¬c.Rel i (c.next i)) : C.dFrom i ≫ (C
.xNextIsoSelf h).hom = 0
参数：h : ¬c.Rel i (c.next i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.shape`：∀ {ι : Type u_1} {V : Type u} [inst : Category
Theory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] 
{c : ComplexSh…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dFrom_comp_xNextIsoSelf {i : ι} (h : ¬c.Rel i (c.next i)) :
    C.dFrom i ≫ (C.xNextIsoSelf h).hom = 0 := by simp [h]

-- This is not a simp lemma; the LHS already simplifies.
/-
**HomologicalComplex.dTo_comp_dFrom** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComple
x`。
形式化陈述：dTo_comp_dFrom (j : ι) : C.dTo j ≫ C.dFrom j = 0
参数：j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.d_comp_d`：d_comp_d (C : HomologicalComplex V c) (i j 
k : ι) : C.d i j ≫ C.d j k = 0
-/
theorem dTo_comp_dFrom (j : ι) : C.dTo j ≫ C.dFrom j = 0 :=
  C.d_comp_d _ _ _
/-
**HomologicalComplex.kernel_from_eq_kernel** 是 Mathlib 中的一个定理，位于命名空间 `Homologica
lComplex`。
形式化陈述：kernel_from_eq_kernel [HasKernels V] {i j : ι} (r : c.Rel i j) : kernelSub
object (C.dFrom i) = kernelSubobject (C.d i j)
参数：r : c.Rel i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.dFrom_eq`：dFrom_eq {i j : ι} (r : c.Rel i j) : C.dFro
m i = C.d i j ≫ (C.xNextIso r).inv
· 使用定理 `CategoryTheory.Limits.kernelSubobject_comp_mono`：kernelSubobject_comp_mo
no (f : X ⟶ Y) [HasKernel f] {Z : C} (h : Y ⟶ Z) [Mono h] : kernelSubobject (f ≫
 h) = kernelSubobject f
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
-/
theorem kernel_from_eq_kernel [HasKernels V] {i j : ι} (r : c.Rel i j) :
    kernelSubobject (C.dFrom i) = kernelSubobject (C.d i j) := by
  rw [C.dFrom_eq r]
  apply kernelSubobject_comp_mono
/-
**HomologicalComplex.image_to_eq_image** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalCom
plex`。
形式化陈述：image_to_eq_image [HasImages V] [HasEqualizers V] {i j : ι} (r : c.Rel i j
) : imageSubobject (C.dTo j) = imageSubobject (C.d i j)
参数：r : c.Rel i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasImages.has_image`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasImages C] {X Y : C}
   (f : X ⟶ Y), CategoryTheory.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.dTo_eq`：dTo_eq {i j : ι} (r : c.Rel i j) : C.dTo j = 
(C.xPrevIso r).hom ≫ C.d i j
· 使用定理 `CategoryTheory.Limits.imageSubobject_iso_comp`：imageSubobject_iso_comp [
HasEqualizers C] {X' : C} (h : X' ⟶ X) [IsIso h] (f : X ⟶ Y) [HasImage f] : imag
eSubobject (h ≫ f) = imageSubobject…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
theorem image_to_eq_image [HasImages V] [HasEqualizers V] {i j : ι} (r : c.Rel i j) :
    imageSubobject (C.dTo j) = imageSubobject (C.d i j) := by
  rw [C.dTo_eq r]
  apply imageSubobject_iso_comp

end

namespace Hom

variable {C₁ C₂ C₃ : HomologicalComplex V c}

/-- The `i`-th component of an isomorphism of chain complexes. -/
@[simps!]
/-
**HomologicalComplex.Hom.isoApp** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex.Ho
m`。
形式化陈述：isoApp (f : C₁ ≅ C₂) (i : ι) : C₁.X i ≅ C₂.X i
参数：f : C₁ ≅ C₂；i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `i`-th component of an isomorphism of chain complexes.
-/
def isoApp (f : C₁ ≅ C₂) (i : ι) : C₁.X i ≅ C₂.X i :=
  (eval V c i).mapIso f

/-- Construct an isomorphism of chain complexes from isomorphism of the objects
which commute with the differentials. -/
@[simps]
/-
**HomologicalComplex.Hom.isoOfComponents** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalC
omplex.Hom`。
形式化陈述：isoOfComponents (f : forall i, C₁.X i ≅ C₂.X i) (hf : forall i j, c.Rel i 
j -> (f i).hom ≫ C₂.d i j = C₁.d i j ≫ (f j).hom
参数：f : forall i, C₁.X i ≅ C₂.X i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an isomorphism of chain complexes from isomorphism of the objects
which commute with the differentials.
-/
def isoOfComponents (f : ∀ i, C₁.X i ≅ C₂.X i)
    (hf : ∀ i j, c.Rel i j → (f i).hom ≫ C₂.d i j = C₁.d i j ≫ (f j).hom := by cat_disch) :
    C₁ ≅ C₂ where
  hom :=
    { f := fun i => (f i).hom
      comm' := hf }
  inv :=
    { f := fun i => (f i).inv
      comm' := fun i j hij =>
        calc
          (f i).inv ≫ C₁.d i j = (f i).inv ≫ (C₁.d i j ≫ (f j).hom) ≫ (f j).inv := by simp
          _ = (f i).inv ≫ ((f i).hom ≫ C₂.d i j) ≫ (f j).inv := by rw [hf i j hij]
          _ = C₂.d i j ≫ (f j).inv := by simp }
  hom_inv_id := by
    ext i
    exact (f i).hom_inv_id
  inv_hom_id := by
    ext i
    exact (f i).inv_hom_id

@[simp]
/-
**HomologicalComplex.Hom.isoOfComponents_app** 是 Mathlib 中的一个定理，位于命名空间 `Homologi
calComplex.Hom`。
形式化陈述：isoOfComponents_app (f : forall i, C₁.X i ≅ C₂.X i) (hf : forall i j, c.Re
l i j -> (f i).hom ≫ C₂.d i j = C₁.d i j ≫ (f j).hom) (i : ι) : isoApp (isoOfCom
ponents f hf) i = f i
参数：f : forall i, C₁.X i ≅ C₂.X i；hf : forall i j, c.Rel i j -> (f i).hom ≫ C₂.d 
i j = C₁.d i j ≫ (f j).hom；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.Hom.isoApp_hom`：∀ {ι : Type u_1} {V : Type u} [inst :
 CategoryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms V] {c : ComplexSh…
· 使用定理 `HomologicalComplex.Hom.isoOfComponents_hom_f`：∀ {ι : Type u_1} {V : Type
 u} [inst : CategoryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.
HasZeroMorphisms V] {c : ComplexSh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isoOfComponents_app (f : ∀ i, C₁.X i ≅ C₂.X i)
    (hf : ∀ i j, c.Rel i j → (f i).hom ≫ C₂.d i j = C₁.d i j ≫ (f j).hom) (i : ι) :
    isoApp (isoOfComponents f hf) i = f i := by
  ext
  simp
/-
**HomologicalComplex.Hom.isIso_of_components** 是 Mathlib 中的一个定理，位于命名空间 `Homologi
calComplex.Hom`。
形式化陈述：isIso_of_components (f : C₁ ⟶ C₂) [forall n : ι, IsIso (f.f n)] : IsIso f
参数：f : C₁ ⟶ C₂；f.f n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
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
theorem isIso_of_components (f : C₁ ⟶ C₂) [∀ n : ι, IsIso (f.f n)] : IsIso f :=
  (HomologicalComplex.Hom.isoOfComponents fun n => asIso (f.f n)).isIso_hom

/-! Lemmas relating chain maps and `dTo`/`dFrom`. -/


/-- `f.prev j` is `f.f i` if there is some `r i j`, and `f.f j` otherwise. -/
/-
**HomologicalComplex.Hom.prev** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomologicalComplex.Ho
m`。
形式化陈述：prev (f : Hom C₁ C₂) (j : ι) : C₁.xPrev j ⟶ C₂.xPrev j
参数：f : Hom C₁ C₂；j : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f.prev j` is `f.f i` if there is some `r i j`, and `f.f j` otherwise.
-/
abbrev prev (f : Hom C₁ C₂) (j : ι) : C₁.xPrev j ⟶ C₂.xPrev j :=
  f.f _
/-
**HomologicalComplex.Hom.prev_eq** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComplex.H
om`。
形式化陈述：prev_eq (f : Hom C₁ C₂) {i j : ι} (w : c.Rel i j) : f.prev j = (C₁.xPrevIs
o w).hom ≫ f.f i ≫ (C₂.xPrevIso w).inv
参数：f : Hom C₁ C₂；w : c.Rel i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `ComplexShape.prev_eq'`：∀ {ι : Type u_1} (c : ComplexShape ι) {i j : ι}, 
c.Rel j i → c.prev i = j
-/
theorem prev_eq (f : Hom C₁ C₂) {i j : ι} (w : c.Rel i j) :
    f.prev j = (C₁.xPrevIso w).hom ≫ f.f i ≫ (C₂.xPrevIso w).inv := by
  obtain rfl := c.prev_eq' w
  simp only [xPrevIso, eqToIso_refl, Iso.refl_hom, Iso.refl_inv, comp_id, id_comp]

/-- `f.next i` is `f.f j` if there is some `r i j`, and `f.f j` otherwise. -/
/-
**HomologicalComplex.Hom.next** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomologicalComplex.Ho
m`。
形式化陈述：next (f : Hom C₁ C₂) (i : ι) : C₁.xNext i ⟶ C₂.xNext i
参数：f : Hom C₁ C₂；i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f.next i` is `f.f j` if there is some `r i j`, and `f.f j` otherwise.
-/
abbrev next (f : Hom C₁ C₂) (i : ι) : C₁.xNext i ⟶ C₂.xNext i :=
  f.f _
/-
**HomologicalComplex.Hom.next_eq** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComplex.H
om`。
形式化陈述：next_eq (f : Hom C₁ C₂) {i j : ι} (w : c.Rel i j) : f.next i = (C₁.xNextIs
o w).hom ≫ f.f j ≫ (C₂.xNextIso w).inv
参数：f : Hom C₁ C₂；w : c.Rel i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `ComplexShape.next_eq'`：next_eq' (c : ComplexShape ι) {i j : ι} (h : c.Re
l i j) : c.next i = j
-/
theorem next_eq (f : Hom C₁ C₂) {i j : ι} (w : c.Rel i j) :
    f.next i = (C₁.xNextIso w).hom ≫ f.f j ≫ (C₂.xNextIso w).inv := by
  obtain rfl := c.next_eq' w
  simp only [xNextIso, eqToIso_refl, Iso.refl_hom, Iso.refl_inv, comp_id, id_comp]

@[reassoc, elementwise]
/-
**HomologicalComplex.Hom.comm_from** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComplex
.Hom`。
形式化陈述：comm_from (f : Hom C₁ C₂) (i : ι) : f.f i ≫ C₂.dFrom i = C₁.dFrom i ≫ f.ne
xt i
参数：f : Hom C₁ C₂；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.Hom.comm`：∀ {ι : Type u_1} {V : Type u} [inst : Categ
oryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
V] {c : ComplexSh…
-/
theorem comm_from (f : Hom C₁ C₂) (i : ι) : f.f i ≫ C₂.dFrom i = C₁.dFrom i ≫ f.next i :=
  f.comm _ _

attribute [simp] comm_from_apply

@[reassoc, elementwise]
/-
**HomologicalComplex.Hom.comm_to** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComplex.H
om`。
形式化陈述：comm_to (f : Hom C₁ C₂) (j : ι) : f.prev j ≫ C₂.dTo j = C₁.dTo j ≫ f.f j
参数：f : Hom C₁ C₂；j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.Hom.comm`：∀ {ι : Type u_1} {V : Type u} [inst : Categ
oryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
V] {c : ComplexSh…
-/
theorem comm_to (f : Hom C₁ C₂) (j : ι) : f.prev j ≫ C₂.dTo j = C₁.dTo j ≫ f.f j :=
  f.comm _ _

attribute [simp] comm_to_apply

/-- A morphism of chain complexes
induces a morphism of arrows of the differentials out of each object.
-/
/-
**HomologicalComplex.Hom.sqFrom** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex.Ho
m`。
形式化陈述：sqFrom (f : Hom C₁ C₂) (i : ι) : Arrow.mk (C₁.dFrom i) ⟶ Arrow.mk (C₂.dFro
m i)
参数：f : Hom C₁ C₂；i : ι。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.Hom.comm_from`：comm_from (f : Hom C₁ C₂) (i : ι) : f.
f i ≫ C₂.dFrom i = C₁.dFrom i ≫ f.next i

--- 原说明 ---
A morphism of chain complexes
induces a morphism of arrows of the differentials out of each object.
-/
def sqFrom (f : Hom C₁ C₂) (i : ι) : Arrow.mk (C₁.dFrom i) ⟶ Arrow.mk (C₂.dFrom i) :=
  Arrow.homMk _ _ (f.comm_from i)

@[simp]
/-
**HomologicalComplex.Hom.sqFrom_left** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalCompl
ex.Hom`。
形式化陈述：sqFrom_left (f : Hom C₁ C₂) (i : ι) : (f.sqFrom i).left = f.f i
参数：f : Hom C₁ C₂；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sqFrom_left (f : Hom C₁ C₂) (i : ι) : (f.sqFrom i).left = f.f i :=
  rfl

@[simp]
/-
**HomologicalComplex.Hom.sqFrom_right** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComp
lex.Hom`。
形式化陈述：sqFrom_right (f : Hom C₁ C₂) (i : ι) : (f.sqFrom i).right = f.next i
参数：f : Hom C₁ C₂；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sqFrom_right (f : Hom C₁ C₂) (i : ι) : (f.sqFrom i).right = f.next i :=
  rfl

@[simp]
/-
**HomologicalComplex.Hom.sqFrom_id** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComplex
.Hom`。
形式化陈述：sqFrom_id (C₁ : HomologicalComplex V c) (i : ι) : sqFrom (𝟙 C₁) i = 𝟙 _
参数：C₁ : HomologicalComplex V c；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sqFrom_id (C₁ : HomologicalComplex V c) (i : ι) : sqFrom (𝟙 C₁) i = 𝟙 _ :=
  rfl

@[simp]
/-
**HomologicalComplex.Hom.sqFrom_comp** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalCompl
ex.Hom`。
形式化陈述：sqFrom_comp (f : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i : ι) : sqFrom (f ≫ g) i = sqFro
m f i ≫ sqFrom g i
参数：f : C₁ ⟶ C₂；g : C₂ ⟶ C₃；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sqFrom_comp (f : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i : ι) :
    sqFrom (f ≫ g) i = sqFrom f i ≫ sqFrom g i :=
  rfl

/-- A morphism of chain complexes
induces a morphism of arrows of the differentials into each object.
-/
/-
**HomologicalComplex.Hom.sqTo** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex.Hom`
。
形式化陈述：sqTo (f : Hom C₁ C₂) (j : ι) : Arrow.mk (C₁.dTo j) ⟶ Arrow.mk (C₂.dTo j)
参数：f : Hom C₁ C₂；j : ι。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.Hom.comm_to`：comm_to (f : Hom C₁ C₂) (j : ι) : f.prev
 j ≫ C₂.dTo j = C₁.dTo j ≫ f.f j

--- 原说明 ---
A morphism of chain complexes
induces a morphism of arrows of the differentials into each object.
-/
def sqTo (f : Hom C₁ C₂) (j : ι) : Arrow.mk (C₁.dTo j) ⟶ Arrow.mk (C₂.dTo j) :=
  Arrow.homMk _ _ (f.comm_to j)

@[simp]
/-
**HomologicalComplex.Hom.sqTo_left** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComplex
.Hom`。
形式化陈述：sqTo_left (f : Hom C₁ C₂) (j : ι) : (f.sqTo j).left = f.prev j
参数：f : Hom C₁ C₂；j : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sqTo_left (f : Hom C₁ C₂) (j : ι) : (f.sqTo j).left = f.prev j :=
  rfl

@[simp]
/-
**HomologicalComplex.Hom.sqTo_right** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComple
x.Hom`。
形式化陈述：sqTo_right (f : Hom C₁ C₂) (j : ι) : (f.sqTo j).right = f.f j
参数：f : Hom C₁ C₂；j : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sqTo_right (f : Hom C₁ C₂) (j : ι) : (f.sqTo j).right = f.f j :=
  rfl
/-
**HomologicalComplex.Hom.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : C₁ ⟶ C₂) [IsIso f] (j : ι) : IsIso (f.f j) :=
  inferInstanceAs (IsIso ((eval _ _ j).map f))
/-
**HomologicalComplex.Hom.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : C₁ ⟶ C₂) [IsSplitEpi f] (j : ι) : IsSplitEpi (f.f j) :=
  inferInstanceAs (IsSplitEpi ((eval _ _ j).map f))
/-
**HomologicalComplex.Hom.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : C₁ ⟶ C₂) [IsSplitMono f] (j : ι) : IsSplitMono (f.f j) :=
  inferInstanceAs (IsSplitMono ((eval _ _ j).map f))

@[push ←, simp]
/-
**HomologicalComplex.Hom.inv_f_apply** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalCompl
ex.Hom`。
形式化陈述：inv_f_apply (f : C₁ ⟶ C₂) [IsIso f] (j : ι) : (inv f).f j = inv (f.f j)
参数：f : C₁ ⟶ C₂；j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsIso.eq_inv_of_inv_hom_id`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {X Y : C} {f : Y ⟶ X} [inst_1 : CategoryTheory.IsIso
 f]   {g : X ⟶ Y}, CategoryTheo…
· 使用定理 `HomologicalComplex.Hom.instIsIsoF`：∀ {ι : Type u_1} {V : Type u} [inst :
 CategoryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms V] {c : ComplexSh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_f_apply (f : C₁ ⟶ C₂) [IsIso f] (j : ι) : (inv f).f j = inv (f.f j) := by
  apply IsIso.eq_inv_of_inv_hom_id
  simp [← comp_f]

end Hom

end

end HomologicalComplex

namespace ChainComplex

section Of

variable {V} {α : Type*} [AddRightCancelSemigroup α] [One α] [DecidableEq α]

/-- Auxiliary definition for differentials for `ChainComplex.of`. -/
/-
**ChainComplex.of.d** 是 Mathlib 中的一个定义，位于命名空间 `ChainComplex.of`。
形式化陈述：{V : Type u} →   [inst : CategoryTheory.Category.{v, u} V] →     [Category
Theory.Limits.HasZeroMorphisms V] →       {α : Type u_2} →         [inst_2 : Add
RightCancelSemigroup α] →           [inst_3 : One α] → [DecidableEq α] → (X : α 
→ V) → ((n : α) → X (n + 1) ⟶ X n) → (i j : α) → X i ⟶ X j
参数：X : α → V；(n : α) → X (n + 1) ⟶ X n；i j : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for differentials for `ChainComplex.of`.
-/
def of.d (X : α → V) (d : ∀ n, X (n + 1) ⟶ X n) (i : α) (j : α) : X i ⟶ X j :=
  if h : i = j + 1 then eqToHom (by rw [h]) ≫ d j else 0

set_option backward.defeqAttrib.useBackward true in
/-- Construct an `α`-indexed chain complex from a dependently-typed differential.
-/
/-
**ChainComplex.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `ChainComplex`。
形式化陈述：of (X : α -> V) (d : forall n, X (n + 1) ⟶ X n) (sq : forall n, d (n + 1) 
≫ d n = 0) : ChainComplex V α
参数：X : α -> V；d : forall n, X (n + 1) ⟶ X n；sq : forall n, d (n + 1) ≫ d n = 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G

--- 原说明 ---
Construct an `α`-indexed chain complex from a dependently-typed differential.
-/
abbrev of (X : α → V) (d : ∀ n, X (n + 1) ⟶ X n) (sq : ∀ n, d (n + 1) ≫ d n = 0) :
    ChainComplex V α :=
  { X := X
    d := of.d X d
    shape := fun i j w => by simp [of.d, (Ne.symm w)]
    d_comp_d' := fun i j k hij hjk => by
      dsimp [of.d] at hij hjk ⊢
      subst hij hjk
      simp only [eqToHom_refl, id_comp, dite_eq_ite, ite_true, sq] }

variable (X : α → V) (d : ∀ n, X (n + 1) ⟶ X n) (sq : ∀ n, d (n + 1) ≫ d n = 0)
/-
**ChainComplex.of_X** 是 Mathlib 中的一个定理，位于命名空间 `ChainComplex`。
形式化陈述：of_X : (of X d sq).X = X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem of_X : (of X d sq).X = X :=
  rfl

@[simp]
/-
**ChainComplex.of_d** 是 Mathlib 中的一个定理，位于命名空间 `ChainComplex`。
形式化陈述：of_d (j : α) : of.d X d (j + 1) j = d j
参数：j : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
theorem of_d (j : α) : of.d X d (j + 1) j = d j := by
  dsimp [of.d]
  rw [if_pos rfl, Category.id_comp]
/-
**ChainComplex.of_d_ne** 是 Mathlib 中的一个定理，位于命名空间 `ChainComplex`。
形式化陈述：of_d_ne {i j : α} (h : i != j + 1) : of.d X d i j = 0
参数：h : i != j + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem of_d_ne {i j : α} (h : i ≠ j + 1) : of.d X d i j = 0 := by
  simp [of.d, dif_neg h]

end Of

section OfHom

variable {V} {α : Type*} [AddRightCancelSemigroup α] [One α] [DecidableEq α]
variable (X : α → V) (d_X : ∀ n, X (n + 1) ⟶ X n) (sq_X : ∀ n, d_X (n + 1) ≫ d_X n = 0) (Y : α → V)
  (d_Y : ∀ n, Y (n + 1) ⟶ Y n) (sq_Y : ∀ n, d_Y (n + 1) ≫ d_Y n = 0)

/-- A constructor for chain maps between `α`-indexed chain complexes built using `ChainComplex.of`,
from a dependently typed collection of morphisms.
-/
/-
**ChainComplex.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `ChainComplex`。
形式化陈述：ofHom {X Y : ChainComplex V α} (f : forall i : α, X.X i ⟶ Y.X i) (comm : f
orall i : α, f (i + 1) ≫ Y.d (i + 1) i = X.d (i + 1) i ≫ f i) : X ⟶ Y where f
参数：f : forall i : α, X.X i ⟶ Y.X i；comm : forall i : α, f (i + 1) ≫ Y.d (i + 1) 
i = X.d (i + 1) i ≫ f i。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G

--- 原说明 ---
A constructor for chain maps between `α`-indexed chain complexes built using `Ch
ainComplex.of`,
from a dependently typed collection of morphisms.
-/
abbrev ofHom {X Y : ChainComplex V α} (f : ∀ i : α, X.X i ⟶ Y.X i)
    (comm : ∀ i : α, f (i + 1) ≫ Y.d (i + 1) i = X.d (i + 1) i ≫ f i) :
    X ⟶ Y where
  f := f
  comm' n m := by
    simp only [ComplexShape.down_Rel]
    rintro rfl
    simpa using comm m

end OfHom

section Mk

variable {V}


variable (X₀ X₁ X₂ : V) (d₀ : X₁ ⟶ X₀) (d₁ : X₂ ⟶ X₁) (s : d₁ ≫ d₀ = 0)
  (succ : ∀ (S : ShortComplex V), Σ' (X₃ : V) (d₂ : X₃ ⟶ S.X₁), d₂ ≫ S.f = 0)

/-- Auxiliary definition for `mk`. -/
/-
**ChainComplex.mkAux** 是 Mathlib 中的一个定义，位于命名空间 `ChainComplex`。
形式化陈述：{V : Type u} →   [inst : CategoryTheory.Category.{v, u} V] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms V] →       (X₀ X₁ X₂ : V) →         (d₀ 
: X₁ ⟶ X₀) →           (d₁ : X₂ ⟶ X₁) →             CategoryTheory.CategoryStruc
t.comp d₁ d₀ = 0 →               ((S : CategoryTheory.ShortComplex V) →         
          (X₃ : V) ×' (d₂ : X₃ ⟶ S.X₁) ×' CategoryTheory.CategoryStruct.comp d₂ 
S.f = 0) →                 ℕ → CategoryTheory.ShortComplex V
参数：X₀ X₁ X₂ : V；d₀ : X₁ ⟶ X₀；d₁ : X₂ ⟶ X₁；(S : CategoryTheory.ShortComplex V) → 
                  (X₃ : V) ×' (d₂ : X₃ ⟶ S.X₁) ×' CategoryTheory.CategoryStruct.
comp d₂ S.f = 0。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `mk`.
-/
def mkAux : ℕ → ShortComplex V
  | 0 => ShortComplex.mk _ _ s
  | n + 1 => ShortComplex.mk _ _ (succ (mkAux n)).2.2

/-- An inductive constructor for `ℕ`-indexed chain complexes.

You provide explicitly the first two differentials,
then a function which takes two differentials and the fact they compose to zero,
and returns the next object, its differential, and the fact it composes appropriately to zero.

See also `mk'`, which only sees the previous differential in the inductive step.
-/
/-
**ChainComplex.mk** 是 Mathlib 中的一个定义，位于命名空间 `ChainComplex`。
形式化陈述：mk : ChainComplex V Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An inductive constructor for `ℕ`-indexed chain complexes.

You provide explicitly the first two differentials,
then a function which takes two differentials and the fact they compose to zero,
and returns the next object, its differential, and the fact it composes appropri
ately to zero.

See also `mk'`, which only sees the previous differential in the inductive step.
-/
def mk : ChainComplex V ℕ :=
  of (fun n => (mkAux X₀ X₁ X₂ d₀ d₁ s succ n).X₃) (fun n => (mkAux X₀ X₁ X₂ d₀ d₁ s succ n).g)
    fun n => (mkAux X₀ X₁ X₂ d₀ d₁ s succ n).zero

@[simp]
/-
**ChainComplex.mk_X_0** 是 Mathlib 中的一个定理，位于命名空间 `ChainComplex`。
形式化陈述：mk_X_0 : (mk X₀ X₁ X₂ d₀ d₁ s succ).X 0 = X₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem mk_X_0 : (mk X₀ X₁ X₂ d₀ d₁ s succ).X 0 = X₀ :=
  rfl

@[simp]
/-
**ChainComplex.mk_X_1** 是 Mathlib 中的一个定理，位于命名空间 `ChainComplex`。
形式化陈述：mk_X_1 : (mk X₀ X₁ X₂ d₀ d₁ s succ).X 1 = X₁
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem mk_X_1 : (mk X₀ X₁ X₂ d₀ d₁ s succ).X 1 = X₁ :=
  rfl

@[simp]
/-
**ChainComplex.mk_X_2** 是 Mathlib 中的一个定理，位于命名空间 `ChainComplex`。
形式化陈述：mk_X_2 : (mk X₀ X₁ X₂ d₀ d₁ s succ).X 2 = X₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem mk_X_2 : (mk X₀ X₁ X₂ d₀ d₁ s succ).X 2 = X₂ :=
  rfl

@[simp]
/-
**ChainComplex.mk_d_1_0** 是 Mathlib 中的一个定理，位于命名空间 `ChainComplex`。
形式化陈述：mk_d_1_0 : (mk X₀ X₁ X₂ d₀ d₁ s succ).d 1 0 = d₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
theorem mk_d_1_0 : (mk X₀ X₁ X₂ d₀ d₁ s succ).d 1 0 = d₀ := by
  change ite (1 = 0 + 1) (𝟙 X₁ ≫ d₀) 0 = d₀
  rw [if_pos rfl, Category.id_comp]

@[simp]
/-
**ChainComplex.mk_d_2_1** 是 Mathlib 中的一个定理，位于命名空间 `ChainComplex`。
形式化陈述：mk_d_2_1 : (mk X₀ X₁ X₂ d₀ d₁ s succ).d 2 1 = d₁
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
theorem mk_d_2_1 : (mk X₀ X₁ X₂ d₀ d₁ s succ).d 2 1 = d₁ := by
  change ite (2 = 1 + 1) (𝟙 X₂ ≫ d₁) 0 = d₁
  rw [if_pos rfl, Category.id_comp]
/-
**ChainComplex.mk_congr_succ_X** 是 Mathlib 中的一个引理，位于命名空间 `ChainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_congr_succ_X₃ {S S' : ShortComplex V} (h : S = S') :
    (succ S).1 = (succ S').1 := by rw [h]
/-
**ChainComplex.mk_congr_succ_d** 是 Mathlib 中的一个引理，位于命名空间 `ChainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_congr_succ_d₂ {S S' : ShortComplex V} (h : S = S') :
    (succ S).2.1 = eqToHom (by subst h; rfl) ≫ (succ S').2.1 ≫ eqToHom (by subst h; rfl) := by
  subst h
  simp

set_option backward.isDefEq.respectTransparency.types false in
/-
**ChainComplex.mkAux_eq_shortComplex_mk_d_comp_d** 是 Mathlib 中的一个引理，位于命名空间 `Chai
nComplex`。
形式化陈述：mkAux_eq_shortComplex_mk_d_comp_d (n : Nat) : mkAux X₀ X₁ X₂ d₀ d₁ s succ 
n = ShortComplex.mk _ _ ((mk X₀ X₁ X₂ d₀ d₁ s succ).d_comp_d (n + 2) (n + 1) n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `HomologicalComplex.d_comp_d`：d_comp_d (C : HomologicalComplex V c) (i j 
k : ι) : C.d i j ≫ C.d j k = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ChainComplex.of_d`：of_d (j : α) : of.d X d (j + 1) j = d j
· 使用定理 `CategoryTheory.ShortComplex.mk.congr_simp`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C]   {X₁ X₂ X₃ : C} (f f_1 :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mkAux_eq_shortComplex_mk_d_comp_d (n : ℕ) :
    mkAux X₀ X₁ X₂ d₀ d₁ s succ n =
      ShortComplex.mk _ _ ((mk X₀ X₁ X₂ d₀ d₁ s succ).d_comp_d (n + 2) (n + 1) n) := by
  rw [show n + 2 = n + 1 + 1 from rfl]
  simp [mk, mkAux]

/-- The isomorphism from `(mk X₀ X₁ X₂ d₀ d₁ s succ).X (n + 3)` that is given by
the inductive construction. -/
/-
**ChainComplex.mkXIso** 是 Mathlib 中的一个定义，位于命名空间 `ChainComplex`。
形式化陈述：mkXIso (n : Nat) : (mk X₀ X₁ X₂ d₀ d₁ s succ).X (n + 3) ≅ (succ (ShortComp
lex.mk _ _ ((mk X₀ X₁ X₂ d₀ d₁ s succ).d_comp_d (n + 2) (n + 1) n))).1
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism from `(mk X₀ X₁ X₂ d₀ d₁ s succ).X (n + 3)` that is given by
the inductive construction.
-/
def mkXIso (n : ℕ) :
    (mk X₀ X₁ X₂ d₀ d₁ s succ).X (n + 3) ≅
      (succ (ShortComplex.mk _ _ ((mk X₀ X₁ X₂ d₀ d₁ s succ).d_comp_d (n + 2) (n + 1) n))).1 :=
  eqToIso (by
    rw [← mk_congr_succ_X₃ succ
      (mkAux_eq_shortComplex_mk_d_comp_d X₀ X₁ X₂ d₀ d₁ s succ n)]
    rfl)

set_option backward.isDefEq.respectTransparency.types false in
/-
**ChainComplex.mk_d** 是 Mathlib 中的一个引理，位于命名空间 `ChainComplex`。
形式化陈述：mk_d (n : Nat) : (mk X₀ X₁ X₂ d₀ d₁ s succ).d (n + 3) (n + 2) = (mkXIso X₀
 X₁ X₂ d₀ d₁ s succ n).hom ≫ (succ (ShortComplex.mk _ _ ((mk X₀ X₁ X₂ d₀ d₁ s su
cc).d_comp_d (n + 2) (n + 1) n))).2.1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `HomologicalComplex.d_comp_d`：d_comp_d (C : HomologicalComplex V c) (i j 
k : ι) : C.d i j ≫ C.d j k = 0
· 使用引理 `ChainComplex.mkAux_eq_shortComplex_mk_d_comp_d`：mkAux_eq_shortComplex_mk
_d_comp_d (n : Nat) : mkAux X₀ X₁ X₂ d₀ d₁ s succ n = ShortComplex.mk _ _ ((mk X
₀ X₁ X₂ d₀ d₁ s succ).d_comp_d (n + …
· 使用引理 `ChainComplex.mk_congr_succ_d₂`：mk_congr_succ_d₂ {S S' : ShortComplex V} 
(h : S = S') : (succ S).2.1 = eqToHom (by subst h; rfl) ≫ (succ S').2.1 ≫ eqToHo
m (by subst h; rfl)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `CategoryTheory.eqToHom_refl`：eqToHom_refl {C : Type u₁} [CategoryStruct.
{v₁} C] (X : C) (p : X = X) : eqToHom p = 𝟙 X
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma mk_d (n : ℕ) :
    (mk X₀ X₁ X₂ d₀ d₁ s succ).d (n + 3) (n + 2) =
      (mkXIso X₀ X₁ X₂ d₀ d₁ s succ n).hom ≫ (succ
        (ShortComplex.mk _ _ ((mk X₀ X₁ X₂ d₀ d₁ s succ).d_comp_d (n + 2) (n + 1) n))).2.1 := by
  have eq := mk_congr_succ_d₂ succ
    (mkAux_eq_shortComplex_mk_d_comp_d X₀ X₁ X₂ d₀ d₁ s succ n)
  set_option backward.isDefEq.respectTransparency false in
    rw [eqToHom_refl, comp_id] at eq
  refine Eq.trans ?_ eq
  dsimp only [mk, of, of.d]
  rw [dif_pos (by rfl), eqToHom_refl, id_comp]
  rfl

/-- A simpler inductive constructor for `ℕ`-indexed chain complexes.

You provide explicitly the first differential,
then a function which takes a differential,
and returns the next object, its differential, and the fact it composes appropriately to zero.
-/
/-
**ChainComplex.mk'** 是 Mathlib 中的一个定义，位于命名空间 `ChainComplex`。
形式化陈述：mk' (X₀ X₁ : V) (d : X₁ ⟶ X₀) (succ' : forall {X₀ X₁ : V} (f : X₁ ⟶ X₀), Σ
' (X₂ : V) (d : X₂ ⟶ X₁), d ≫ f = 0) : ChainComplex V Nat
参数：X₀ X₁ : V；d : X₁ ⟶ X₀；succ' : forall {X₀ X₁ : V} (f : X₁ ⟶ X₀), Σ' (X₂ : V) (
d : X₂ ⟶ X₁), d ≫ f = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A simpler inductive constructor for `ℕ`-indexed chain complexes.

You provide explicitly the first differential,
then a function which takes a differential,
and returns the next object, its differential, and the fact it composes appropri
ately to zero.
-/
def mk' (X₀ X₁ : V) (d : X₁ ⟶ X₀)
    (succ' : ∀ {X₀ X₁ : V} (f : X₁ ⟶ X₀), Σ' (X₂ : V) (d : X₂ ⟶ X₁), d ≫ f = 0) :
    ChainComplex V ℕ :=
  mk _ _ _ _ _ (succ' d).2.2 (fun S => succ' S.f)

variable (succ' : ∀ {X₀ X₁ : V} (f : X₁ ⟶ X₀), Σ' (X₂ : V) (d : X₂ ⟶ X₁), d ≫ f = 0)

@[simp]
/-
**ChainComplex.mk'_X_0** 是 Mathlib 中的一个定理，位于命名空间 `ChainComplex`。
形式化陈述：∀ {V : Type u} [inst : CategoryTheory.Category.{v, u} V] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms V] (X₀ X₁ : V)   (d₀ : X₁ ⟶ X₀)   (succ' : {X₀ X
₁ : V} → (f : X₁ ⟶ X₀) → (X₂ : V) ×' (d : X₂ ⟶ X₁) ×' CategoryTheory.CategoryStr
uct.comp d f = 0),   (ChainComplex.mk' X₀ X₁ d₀ fun {X₀ X₁} => succ').X 0 = X₀
参数：X₀ X₁ : V；d₀ : X₁ ⟶ X₀；succ' : {X₀ X₁ : V} → (f : X₁ ⟶ X₀) → (X₂ : V) ×' (d :
 X₂ ⟶ X₁) ×' CategoryTheory.CategoryStruct.comp d f = 0；ChainComplex.mk' X₀ X₁ d
₀ fun {X₀ X₁} => succ'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem mk'_X_0 : (mk' X₀ X₁ d₀ succ').X 0 = X₀ :=
  rfl

@[simp]
/-
**ChainComplex.mk'_X_1** 是 Mathlib 中的一个定理，位于命名空间 `ChainComplex`。
形式化陈述：∀ {V : Type u} [inst : CategoryTheory.Category.{v, u} V] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms V] (X₀ X₁ : V)   (d₀ : X₁ ⟶ X₀)   (succ' : {X₀ X
₁ : V} → (f : X₁ ⟶ X₀) → (X₂ : V) ×' (d : X₂ ⟶ X₁) ×' CategoryTheory.CategoryStr
uct.comp d f = 0),   (ChainComplex.mk' X₀ X₁ d₀ fun {X₀ X₁} => succ').X 1 = X₁
参数：X₀ X₁ : V；d₀ : X₁ ⟶ X₀；succ' : {X₀ X₁ : V} → (f : X₁ ⟶ X₀) → (X₂ : V) ×' (d :
 X₂ ⟶ X₁) ×' CategoryTheory.CategoryStruct.comp d f = 0；ChainComplex.mk' X₀ X₁ d
₀ fun {X₀ X₁} => succ'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem mk'_X_1 : (mk' X₀ X₁ d₀ succ').X 1 = X₁ :=
  rfl


@[simp]
/-
**ChainComplex.mk'_d_1_0** 是 Mathlib 中的一个定理，位于命名空间 `ChainComplex`。
形式化陈述：∀ {V : Type u} [inst : CategoryTheory.Category.{v, u} V] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms V] (X₀ X₁ : V)   (d₀ : X₁ ⟶ X₀)   (succ' : {X₀ X
₁ : V} → (f : X₁ ⟶ X₀) → (X₂ : V) ×' (d : X₂ ⟶ X₁) ×' CategoryTheory.CategoryStr
uct.comp d f = 0),   (ChainComplex.mk' X₀ X₁ d₀ fun {X₀ X₁} => succ').d 1 0 = d₀
参数：X₀ X₁ : V；d₀ : X₁ ⟶ X₀；succ' : {X₀ X₁ : V} → (f : X₁ ⟶ X₀) → (X₂ : V) ×' (d :
 X₂ ⟶ X₁) ×' CategoryTheory.CategoryStruct.comp d f = 0；ChainComplex.mk' X₀ X₁ d
₀ fun {X₀ X₁} => succ'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
theorem mk'_d_1_0 : (mk' X₀ X₁ d₀ succ').d 1 0 = d₀ := by
  change ite (1 = 0 + 1) (𝟙 X₁ ≫ d₀) 0 = d₀
  rw [if_pos rfl, Category.id_comp]

set_option backward.isDefEq.respectTransparency.types false in
/-- The isomorphism from `(mk' X₀ X₁ d₀ succ').X (n + 2)` that is given by
the inductive construction. -/
/-
**ChainComplex.mk'XIso** 是 Mathlib 中的一个定义，位于命名空间 `ChainComplex`。
形式化陈述：{V : Type u} →   [inst : CategoryTheory.Category.{v, u} V] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms V] →       (X₀ X₁ : V) →         (d₀ : X
₁ ⟶ X₀) →           (succ' :               {X₀ X₁ : V} → (f : X₁ ⟶ X₀) → (X₂ : V
) ×' (d : X₂ ⟶ X₁) ×' CategoryTheory.CategoryStruct.comp d f = 0) →             
(n : ℕ) →               (ChainComplex.mk' X₀ X₁ d₀ fun {X₀ X₁} => succ').X (n + 
2) ≅                 (succ' ((ChainComplex.mk' X₀ X₁ d₀ fun {X₀ X₁} => succ').d 
(n + 1) n)).fst
参数：X₀ X₁ : V；d₀ : X₁ ⟶ X₀；succ' :               {X₀ X₁ : V} → (f : X₁ ⟶ X₀) → (X
₂ : V) ×' (d : X₂ ⟶ X₁) ×' CategoryTheory.CategoryStruct.comp d f = 0；n : ℕ；Chai
nComplex.mk' X₀ X₁ d₀ fun {X₀ X₁} => succ'；n + 2；succ' ((ChainComplex.mk' X₀ X₁ 
d₀ fun {X₀ X₁} => succ').d (n + 1) n)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism from `(mk' X₀ X₁ d₀ succ').X (n + 2)` that is given by
the inductive construction.
-/
def mk'XIso (n : ℕ) :
    (mk' X₀ X₁ d₀ succ').X (n + 2) ≅ (succ' ((mk' X₀ X₁ d₀ succ').d (n + 1) n)).1 := by
  obtain _ | n := n
  · apply eqToIso
    dsimp [mk', mk, of, mkAux, of.d]
    rw [id_comp]
  · exact mkXIso _ _ _ _ _ (succ' d₀).2.2 (fun S => succ' S.f) n
/-
**ChainComplex.mk'_congr_succ'_d** 是 Mathlib 中的一个定理，位于命名空间 `ChainComplex`。
形式化陈述：∀ {V : Type u} [inst : CategoryTheory.Category.{v, u} V] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms V]   (succ' : {X₀ X₁ : V} → (f : X₁ ⟶ X₀) → (X₂ 
: V) ×' (d : X₂ ⟶ X₁) ×' CategoryTheory.CategoryStruct.comp d f = 0)   {X Y : V}
 (f g : X ⟶ Y) (h : f = g),   (succ' f).snd.fst = CategoryTheory.CategoryStruct.
comp (CategoryTheory.eqToHom ⋯) (succ' g).snd.fst
参数：succ' : {X₀ X₁ : V} → (f : X₁ ⟶ X₀) → (X₂ : V) ×' (d : X₂ ⟶ X₁) ×' CategoryTh
eory.CategoryStruct.comp d f = 0；f g : X ⟶ Y；h : f = g；succ' f；CategoryTheory.eq
ToHom ⋯；succ' g。
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
lemma mk'_congr_succ'_d {X Y : V} (f g : X ⟶ Y) (h : f = g) :
    (succ' f).2.1 = eqToHom (by rw [h]) ≫ (succ' g).2.1 := by
  subst h
  simp
/-
**ChainComplex.mk'_d** 是 Mathlib 中的一个定理，位于命名空间 `ChainComplex`。
形式化陈述：∀ {V : Type u} [inst : CategoryTheory.Category.{v, u} V] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms V] (X₀ X₁ : V)   (d₀ : X₁ ⟶ X₀)   (succ' : {X₀ X
₁ : V} → (f : X₁ ⟶ X₀) → (X₂ : V) ×' (d : X₂ ⟶ X₁) ×' CategoryTheory.CategoryStr
uct.comp d f = 0)   (n : ℕ),   (ChainComplex.mk' X₀ X₁ d₀ fun {X₀ X₁} => succ').
d (n + 2) (n + 1) =     CategoryTheory.CategoryStruct.comp (ChainComplex.mk'XIso
 X₀ X₁ d₀ (fun {X₀ X₁} => succ') n).hom       (succ' ((ChainComplex.mk' X₀ X₁ d₀
 fun {X₀ X₁} => succ').d (n + 1) n)).snd.fst
参数：X₀ X₁ : V；d₀ : X₁ ⟶ X₀；succ' : {X₀ X₁ : V} → (f : X₁ ⟶ X₀) → (X₂ : V) ×' (d :
 X₂ ⟶ X₁) ×' CategoryTheory.CategoryStruct.comp d f = 0；n : ℕ；ChainComplex.mk' X
₀ X₁ d₀ fun {X₀ X₁} => succ'；n + 2；n + 1；ChainComplex.mk'XIso X₀ X₁ d₀ (fun {X₀ 
X₁} => succ') n；succ' ((ChainComplex.mk' X₀ X₁ d₀ fun {X₀ X₁} => succ').d (n + 1
) n)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ChainComplex.mk_d_2_1`：mk_d_2_1 : (mk X₀ X₁ X₂ d₀ d₁ s succ).d 2 1 = d₁
· 使用定理 `ChainComplex.mk'_congr_succ'_d`：∀ {V : Type u} [inst : CategoryTheory.Ca
tegory.{v, u} V] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V]   (succ' : 
{X₀ X₁ : V} → (f : X…
· 使用定理 `ChainComplex.mk_d_1_0`：mk_d_1_0 : (mk X₀ X₁ X₂ d₀ d₁ s succ).d 1 0 = d₀
· 使用引理 `ChainComplex.mk_d`：mk_d (n : Nat) : (mk X₀ X₁ X₂ d₀ d₁ s succ).d (n + 3)
 (n + 2) = (mkXIso X₀ X₁ X₂ d₀ d₁ s succ n).hom ≫ (succ (ShortComplex.mk _ _ ((m
k X₀ X₁…
-/
lemma mk'_d (n : ℕ) :
    (mk' X₀ X₁ d₀ succ').d (n + 2) (n + 1) = (mk'XIso X₀ X₁ d₀ succ' n).hom ≫
      (succ' ((mk' X₀ X₁ d₀ succ').d (n + 1) n)).2.1 := by
  obtain _ | n := n
  · dsimp [mk'XIso, mk']
    rw [mk_d_2_1]
    apply mk'_congr_succ'_d
    rw [mk_d_1_0]
  · apply mk_d

end Mk

section MkHom

variable {V}
variable (P Q : ChainComplex V ℕ) (zero : P.X 0 ⟶ Q.X 0) (one : P.X 1 ⟶ Q.X 1)
  (one_zero_comm : one ≫ Q.d 1 0 = P.d 1 0 ≫ zero)
  (succ :
    ∀ (n : ℕ)
      (p :
        Σ' (f : P.X n ⟶ Q.X n) (f' : P.X (n + 1) ⟶ Q.X (n + 1)),
          f' ≫ Q.d (n + 1) n = P.d (n + 1) n ≫ f),
      Σ' f'' : P.X (n + 2) ⟶ Q.X (n + 2), f'' ≫ Q.d (n + 2) (n + 1) = P.d (n + 2) (n + 1) ≫ p.2.1)

/-- An auxiliary construction for `mkHom`.

Here we build by induction a family of commutative squares,
but don't require at the type level that these successive commutative squares actually agree.
They do in fact agree, and we then capture that at the type level (i.e. by constructing a chain map)
in `mkHom`.
-/
/-
**ChainComplex.mkHomAux** 是 Mathlib 中的一个定义，位于命名空间 `ChainComplex`。
形式化陈述：{V : Type u} →   [inst : CategoryTheory.Category.{v, u} V] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms V] →       (P Q : ChainComplex V ℕ) →   
      (zero : P.X 0 ⟶ Q.X 0) →           (one : P.X 1 ⟶ Q.X 1) →             Cat
egoryTheory.CategoryStruct.comp one (Q.d 1 0) = CategoryTheory.CategoryStruct.co
mp (P.d 1 0) zero →               ((n : ℕ) →                   (p :             
          (f : P.X n ⟶ Q.X n) ×'                         (f' : P.X (n + 1) ⟶ Q.X
 (n + 1)) ×'                           CategoryTheory.CategoryStruct.comp f' (Q.
d (n + 1) n) =                             CategoryTheory.CategoryStruct.comp (P
.d (n + 1) n) f) →                     (f'' : P.X (n + 2) ⟶ Q.X (n + 2)) ×'     
                  CategoryTheory.CategoryStruct.comp f'' (Q.d (n + 2) (n + 1)) =
                         CategoryTheory.CategoryStruct.comp (P.d (n + 2) (n + 1)
) p.snd.fst) →                 (n : ℕ) →                   (f : P.X n ⟶ Q.X n) ×
'                     (f' : P.X (n + 1) ⟶ Q.X (n + 1)) ×'                       
CategoryTheory.CategoryStruct.comp f' (Q.d (n + 1) n) =                         
CategoryTheory.CategoryStruct.comp (P.d (n + 1) n) f
参数：P Q : ChainComplex V ℕ；zero : P.X 0 ⟶ Q.X 0；one : P.X 1 ⟶ Q.X 1；Q.d 1 0；P.d 1
 0；(n : ℕ) →                   (p :                       (f : P.X n ⟶ Q.X n) ×'
                         (f' : P.X (n + 1) ⟶ Q.X (n + 1)) ×'                    
       CategoryTheory.CategoryStruct.comp f' (Q.d (n + 1) n) =                  
           CategoryTheory.CategoryStruct.comp (P.d (n + 1) n) f) →              
       (f'' : P.X (n + 2) ⟶ Q.X (n + 2)) ×'                       CategoryTheory
.CategoryStruct.comp f'' (Q.d (n + 2) (n + 1)) =                         Categor
yTheory.CategoryStruct.comp (P.d (n + 2) (n + 1)) p.snd.fst；n : ℕ；f : P.X n ⟶ Q.
X n；f' : P.X (n + 1) ⟶ Q.X (n + 1)；Q.d (n + 1) n；P.d (n + 1) n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary construction for `mkHom`.

Here we build by induction a family of commutative squares,
but don't require at the type level that these successive commutative squares ac
tually agree.
They do in fact agree, and we then capture that at the type level (i.e. by const
ructing a chain map)
in `mkHom`.
-/
def mkHomAux :
    ∀ n,
      Σ' (f : P.X n ⟶ Q.X n) (f' : P.X (n + 1) ⟶ Q.X (n + 1)),
        f' ≫ Q.d (n + 1) n = P.d (n + 1) n ≫ f
  | 0 => ⟨zero, one, one_zero_comm⟩
  | n + 1 => ⟨(mkHomAux n).2.1, (succ n (mkHomAux n)).1, (succ n (mkHomAux n)).2⟩

/-- A constructor for chain maps between `ℕ`-indexed chain complexes,
working by induction on commutative squares.

You need to provide the components of the chain map in degrees 0 and 1,
show that these form a commutative square,
and then give a construction of each component,
and the fact that it forms a commutative square with the previous component,
using as an inductive hypothesis the data (and commutativity) of the previous two components.
-/
/-
**ChainComplex.mkHom** 是 Mathlib 中的一个定义，位于命名空间 `ChainComplex`。
形式化陈述：mkHom : P ⟶ Q where f n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A constructor for chain maps between `ℕ`-indexed chain complexes,
working by induction on commutative squares.

You need to provide the components of the chain map in degrees 0 and 1,
show that these form a commutative square,
and then give a construction of each component,
and the fact that it forms a commutative square with the previous component,
using as an inductive hypothesis the data (and commutativity) of the previous tw
o components.
-/
def mkHom : P ⟶ Q where
  f n := (mkHomAux P Q zero one one_zero_comm succ n).1
  comm' n m := by
    rintro (rfl : m + 1 = n)
    exact (mkHomAux P Q zero one one_zero_comm succ m).2.2

@[simp]
/-
**ChainComplex.mkHom_f_0** 是 Mathlib 中的一个定理，位于命名空间 `ChainComplex`。
形式化陈述：mkHom_f_0 : (mkHom P Q zero one one_zero_comm succ).f 0 = zero
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem mkHom_f_0 : (mkHom P Q zero one one_zero_comm succ).f 0 = zero :=
  rfl

@[simp]
/-
**ChainComplex.mkHom_f_1** 是 Mathlib 中的一个定理，位于命名空间 `ChainComplex`。
形式化陈述：mkHom_f_1 : (mkHom P Q zero one one_zero_comm succ).f 1 = one
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem mkHom_f_1 : (mkHom P Q zero one one_zero_comm succ).f 1 = one :=
  rfl

@[simp]
/-
**ChainComplex.mkHom_f_succ_succ** 是 Mathlib 中的一个定理，位于命名空间 `ChainComplex`。
形式化陈述：mkHom_f_succ_succ (n : Nat) : (mkHom P Q zero one one_zero_comm succ).f (n
 + 2) = (succ n ⟨(mkHom P Q zero one one_zero_comm succ).f n, (mkHom P Q zero on
e one_zero_comm succ).f (n + 1), (mkHom P Q zero one one_zero_comm succ).comm (n
 + 1) n⟩).1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem mkHom_f_succ_succ (n : ℕ) :
    (mkHom P Q zero one one_zero_comm succ).f (n + 2) =
      (succ n
          ⟨(mkHom P Q zero one one_zero_comm succ).f n,
            (mkHom P Q zero one one_zero_comm succ).f (n + 1),
            (mkHom P Q zero one one_zero_comm succ).comm (n + 1) n⟩).1 := by
  dsimp [mkHom, mkHomAux]

end MkHom

end ChainComplex

namespace CochainComplex

section Of

variable {V} {α : Type*} [AddRightCancelSemigroup α] [One α] [DecidableEq α]

/-- Auxiliary definition for differentials for `CochainComplex.of`. -/
/-
**CochainComplex.of.d** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex.of`。
形式化陈述：{V : Type u} →   [inst : CategoryTheory.Category.{v, u} V] →     [Category
Theory.Limits.HasZeroMorphisms V] →       {α : Type u_2} →         [inst_2 : Add
RightCancelSemigroup α] →           [inst_3 : One α] → [DecidableEq α] → (X : α 
→ V) → ((n : α) → X n ⟶ X (n + 1)) → (i j : α) → X i ⟶ X j
参数：X : α → V；(n : α) → X n ⟶ X (n + 1)；i j : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for differentials for `CochainComplex.of`.
-/
def of.d (X : α → V) (d : ∀ n, X n ⟶ X (n + 1)) (i : α) (j : α) : X i ⟶ X j :=
  if h : i + 1 = j then d _ ≫ eqToHom (by rw [h]) else 0

set_option backward.defeqAttrib.useBackward true in
/-- Construct an `α`-indexed cochain complex from a dependently-typed differential.
-/
/-
**CochainComplex.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `CochainComplex`。
形式化陈述：of (X : α -> V) (d : forall n, X n ⟶ X (n + 1)) (sq : forall n, d n ≫ d (n
 + 1) = 0) : CochainComplex V α
参数：X : α -> V；d : forall n, X n ⟶ X (n + 1)；sq : forall n, d n ≫ d (n + 1) = 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G

--- 原说明 ---
Construct an `α`-indexed cochain complex from a dependently-typed differential.
-/
abbrev of (X : α → V) (d : ∀ n, X n ⟶ X (n + 1)) (sq : ∀ n, d n ≫ d (n + 1) = 0) :
    CochainComplex V α :=
  { X := X
    d := of.d X d
    shape := fun i j w => dif_neg (c := i + 1 = j) w
    d_comp_d' := fun i j k => by
      dsimp [of.d]
      split_ifs with h h' h'
      · subst h h'
        simp [sq]
      all_goals simp }

variable (X : α → V) (d : ∀ n, X n ⟶ X (n + 1)) (sq : ∀ n, d n ≫ d (n + 1) = 0)
/-
**CochainComplex.of_X** 是 Mathlib 中的一个定理，位于命名空间 `CochainComplex`。
形式化陈述：of_X : (of X d sq).X = X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem of_X : (of X d sq).X = X :=
  rfl

@[simp]
/-
**CochainComplex.of_d** 是 Mathlib 中的一个定理，位于命名空间 `CochainComplex`。
形式化陈述：of_d (j : α) : of.d X d j (j + 1) = d j
参数：j : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
theorem of_d (j : α) : of.d X d j (j + 1) = d j := by
  dsimp [of.d]
  rw [if_pos rfl, Category.comp_id]
/-
**CochainComplex.of_d_ne** 是 Mathlib 中的一个定理，位于命名空间 `CochainComplex`。
形式化陈述：of_d_ne {i j : α} (h : i + 1 != j) : of.d X d i j = 0
参数：h : i + 1 != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem of_d_ne {i j : α} (h : i + 1 ≠ j) : of.d X d i j = 0 := by
  simp [of.d, dif_neg h]

end Of

section OfHom

variable {V} {α : Type*} [AddRightCancelSemigroup α] [One α] [DecidableEq α]
variable (X : α → V) (d_X : ∀ n, X n ⟶ X (n + 1)) (sq_X : ∀ n, d_X n ≫ d_X (n + 1) = 0) (Y : α → V)
  (d_Y : ∀ n, Y n ⟶ Y (n + 1)) (sq_Y : ∀ n, d_Y n ≫ d_Y (n + 1) = 0)

/--
A constructor for chain maps between `α`-indexed cochain complexes built using `CochainComplex.of`,
from a dependently typed collection of morphisms.
-/
/-
**CochainComplex.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `CochainComplex`。
形式化陈述：ofHom {X Y : CochainComplex V α} (f : forall i : α, X.X i ⟶ Y.X i) (comm :
 forall i : α, f i ≫ Y.d i (i + 1) = X.d i (i + 1) ≫ f (i + 1)) : X ⟶ Y where f
参数：f : forall i : α, X.X i ⟶ Y.X i；comm : forall i : α, f i ≫ Y.d i (i + 1) = X.
d i (i + 1) ≫ f (i + 1)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G

--- 原说明 ---
A constructor for chain maps between `α`-indexed cochain complexes built using `
CochainComplex.of`,
from a dependently typed collection of morphisms.
-/
abbrev ofHom {X Y : CochainComplex V α} (f : ∀ i : α, X.X i ⟶ Y.X i)
    (comm : ∀ i : α, f i ≫ Y.d i (i + 1) = X.d i (i + 1) ≫ f (i + 1)) :
    X ⟶ Y where
  f := f
  comm' n m := by
    simp only [ComplexShape.up_Rel]
    rintro rfl
    simpa using comm n

end OfHom

section Mk

variable {V}
variable (X₀ X₁ X₂ : V) (d₀ : X₀ ⟶ X₁) (d₁ : X₁ ⟶ X₂) (s : d₀ ≫ d₁ = 0)
  (succ : ∀ (S : ShortComplex V), Σ' (X₄ : V) (d₂ : S.X₃ ⟶ X₄), S.g ≫ d₂ = 0)

/-- Auxiliary definition for `mk`. -/
/-
**CochainComplex.mkAux** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex`。
形式化陈述：{V : Type u} →   [inst : CategoryTheory.Category.{v, u} V] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms V] →       (X₀ X₁ X₂ : V) →         (d₀ 
: X₀ ⟶ X₁) →           (d₁ : X₁ ⟶ X₂) →             CategoryTheory.CategoryStruc
t.comp d₀ d₁ = 0 →               ((S : CategoryTheory.ShortComplex V) →         
          (X₄ : V) ×' (d₂ : S.X₃ ⟶ X₄) ×' CategoryTheory.CategoryStruct.comp S.g
 d₂ = 0) →                 ℕ → CategoryTheory.ShortComplex V
参数：X₀ X₁ X₂ : V；d₀ : X₀ ⟶ X₁；d₁ : X₁ ⟶ X₂；(S : CategoryTheory.ShortComplex V) → 
                  (X₄ : V) ×' (d₂ : S.X₃ ⟶ X₄) ×' CategoryTheory.CategoryStruct.
comp S.g d₂ = 0。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `mk`.
-/
def mkAux : ℕ → ShortComplex V
  | 0 => ShortComplex.mk _ _ s
  | n + 1 => ShortComplex.mk _ _ (succ (mkAux n)).2.2

/-- An inductive constructor for `ℕ`-indexed cochain complexes.

You provide explicitly the first two differentials,
then a function which takes two differentials and the fact they compose to zero,
and returns the next object, its differential, and the fact it composes appropriately to zero.

See also `mk'`, which only sees the previous differential in the inductive step.
-/
/-
**CochainComplex.mk** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex`。
形式化陈述：mk : CochainComplex V Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An inductive constructor for `ℕ`-indexed cochain complexes.

You provide explicitly the first two differentials,
then a function which takes two differentials and the fact they compose to zero,
and returns the next object, its differential, and the fact it composes appropri
ately to zero.

See also `mk'`, which only sees the previous differential in the inductive step.
-/
def mk : CochainComplex V ℕ :=
  of (fun n => (mkAux X₀ X₁ X₂ d₀ d₁ s succ n).X₁) (fun n => (mkAux X₀ X₁ X₂ d₀ d₁ s succ n).f)
    fun n => (mkAux X₀ X₁ X₂ d₀ d₁ s succ n).zero

@[simp]
/-
**CochainComplex.mk_X_0** 是 Mathlib 中的一个定理，位于命名空间 `CochainComplex`。
形式化陈述：mk_X_0 : (mk X₀ X₁ X₂ d₀ d₁ s succ).X 0 = X₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem mk_X_0 : (mk X₀ X₁ X₂ d₀ d₁ s succ).X 0 = X₀ :=
  rfl

@[simp]
/-
**CochainComplex.mk_X_1** 是 Mathlib 中的一个定理，位于命名空间 `CochainComplex`。
形式化陈述：mk_X_1 : (mk X₀ X₁ X₂ d₀ d₁ s succ).X 1 = X₁
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem mk_X_1 : (mk X₀ X₁ X₂ d₀ d₁ s succ).X 1 = X₁ :=
  rfl

@[simp]
/-
**CochainComplex.mk_X_2** 是 Mathlib 中的一个定理，位于命名空间 `CochainComplex`。
形式化陈述：mk_X_2 : (mk X₀ X₁ X₂ d₀ d₁ s succ).X 2 = X₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem mk_X_2 : (mk X₀ X₁ X₂ d₀ d₁ s succ).X 2 = X₂ :=
  rfl

@[simp]
/-
**CochainComplex.mk_d_1_0** 是 Mathlib 中的一个定理，位于命名空间 `CochainComplex`。
形式化陈述：mk_d_1_0 : (mk X₀ X₁ X₂ d₀ d₁ s succ).d 0 1 = d₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
theorem mk_d_1_0 : (mk X₀ X₁ X₂ d₀ d₁ s succ).d 0 1 = d₀ := by
  change ite (1 = 0 + 1) (d₀ ≫ 𝟙 X₁) 0 = d₀
  rw [if_pos rfl, Category.comp_id]

@[simp]
/-
**CochainComplex.mk_d_2_0** 是 Mathlib 中的一个定理，位于命名空间 `CochainComplex`。
形式化陈述：mk_d_2_0 : (mk X₀ X₁ X₂ d₀ d₁ s succ).d 1 2 = d₁
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
theorem mk_d_2_0 : (mk X₀ X₁ X₂ d₀ d₁ s succ).d 1 2 = d₁ := by
  change ite (2 = 1 + 1) (d₁ ≫ 𝟙 X₂) 0 = d₁
  rw [if_pos rfl, Category.comp_id]

-- TODO simp lemmas for the inductive steps? It's not entirely clear that they are needed.
/-- A simpler inductive constructor for `ℕ`-indexed cochain complexes.

You provide explicitly the first differential,
then a function which takes a differential,
and returns the next object, its differential, and the fact it composes appropriately to zero.
-/
/-
**CochainComplex.mk'** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex`。
形式化陈述：mk' (X₀ X₁ : V) (d : X₀ ⟶ X₁) -- (succ' : ∀ : Σ X₀ X₁ : V, X₀ ⟶ X₁, Σ' (X₂
 : V) (d : t.2.1 ⟶ X₂), t.2.2 ≫ d = 0) : (succ' : forall {X₀ X₁ : V} (f : X₀ ⟶ X
₁), Σ' (X₂ : V) (d : X₁ ⟶ X₂), f ≫ d = 0) : CochainComplex V Nat
参数：X₀ X₁ : V；d : X₀ ⟶ X₁；succ' : ∀ : Σ X₀ X₁ : V, X₀ ⟶ X₁, Σ' (X₂ : V) (d : t.2.
1 ⟶ X₂), t.2.2 ≫ d = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A simpler inductive constructor for `ℕ`-indexed cochain complexes.

You provide explicitly the first differential,
then a function which takes a differential,
and returns the next object, its differential, and the fact it composes appropri
ately to zero.
-/
def mk' (X₀ X₁ : V) (d : X₀ ⟶ X₁)
    -- (succ' : ∀ : Σ X₀ X₁ : V, X₀ ⟶ X₁, Σ' (X₂ : V) (d : t.2.1 ⟶ X₂), t.2.2 ≫ d = 0) :
    (succ' : ∀ {X₀ X₁ : V} (f : X₀ ⟶ X₁), Σ' (X₂ : V) (d : X₁ ⟶ X₂), f ≫ d = 0) :
    CochainComplex V ℕ :=
  mk _ _ _ _ _ (succ' d).2.2 (fun S => succ' S.g)

variable (succ' : ∀ {X₀ X₁ : V} (f : X₀ ⟶ X₁), Σ' (X₂ : V) (d : X₁ ⟶ X₂), f ≫ d = 0)

@[simp]
/-
**CochainComplex.mk'_X_0** 是 Mathlib 中的一个定理，位于命名空间 `CochainComplex`。
形式化陈述：∀ {V : Type u} [inst : CategoryTheory.Category.{v, u} V] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms V] (X₀ X₁ : V)   (d₀ : X₀ ⟶ X₁)   (succ' : {X₀ X
₁ : V} → (f : X₀ ⟶ X₁) → (X₂ : V) ×' (d : X₁ ⟶ X₂) ×' CategoryTheory.CategoryStr
uct.comp f d = 0),   (CochainComplex.mk' X₀ X₁ d₀ fun {X₀ X₁} => succ').X 0 = X₀
参数：X₀ X₁ : V；d₀ : X₀ ⟶ X₁；succ' : {X₀ X₁ : V} → (f : X₀ ⟶ X₁) → (X₂ : V) ×' (d :
 X₁ ⟶ X₂) ×' CategoryTheory.CategoryStruct.comp f d = 0；CochainComplex.mk' X₀ X₁
 d₀ fun {X₀ X₁} => succ'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem mk'_X_0 : (mk' X₀ X₁ d₀ succ').X 0 = X₀ :=
  rfl

@[simp]
/-
**CochainComplex.mk'_X_1** 是 Mathlib 中的一个定理，位于命名空间 `CochainComplex`。
形式化陈述：∀ {V : Type u} [inst : CategoryTheory.Category.{v, u} V] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms V] (X₀ X₁ : V)   (d₀ : X₀ ⟶ X₁)   (succ' : {X₀ X
₁ : V} → (f : X₀ ⟶ X₁) → (X₂ : V) ×' (d : X₁ ⟶ X₂) ×' CategoryTheory.CategoryStr
uct.comp f d = 0),   (CochainComplex.mk' X₀ X₁ d₀ fun {X₀ X₁} => succ').X 1 = X₁
参数：X₀ X₁ : V；d₀ : X₀ ⟶ X₁；succ' : {X₀ X₁ : V} → (f : X₀ ⟶ X₁) → (X₂ : V) ×' (d :
 X₁ ⟶ X₂) ×' CategoryTheory.CategoryStruct.comp f d = 0；CochainComplex.mk' X₀ X₁
 d₀ fun {X₀ X₁} => succ'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem mk'_X_1 : (mk' X₀ X₁ d₀ succ').X 1 = X₁ :=
  rfl

@[simp]
/-
**CochainComplex.mk'_d_1_0** 是 Mathlib 中的一个定理，位于命名空间 `CochainComplex`。
形式化陈述：∀ {V : Type u} [inst : CategoryTheory.Category.{v, u} V] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms V] (X₀ X₁ : V)   (d₀ : X₀ ⟶ X₁)   (succ' : {X₀ X
₁ : V} → (f : X₀ ⟶ X₁) → (X₂ : V) ×' (d : X₁ ⟶ X₂) ×' CategoryTheory.CategoryStr
uct.comp f d = 0),   (CochainComplex.mk' X₀ X₁ d₀ fun {X₀ X₁} => succ').d 0 1 = 
d₀
参数：X₀ X₁ : V；d₀ : X₀ ⟶ X₁；succ' : {X₀ X₁ : V} → (f : X₀ ⟶ X₁) → (X₂ : V) ×' (d :
 X₁ ⟶ X₂) ×' CategoryTheory.CategoryStruct.comp f d = 0；CochainComplex.mk' X₀ X₁
 d₀ fun {X₀ X₁} => succ'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
theorem mk'_d_1_0 : (mk' X₀ X₁ d₀ succ').d 0 1 = d₀ := by
  change ite (1 = 0 + 1) (d₀ ≫ 𝟙 X₁) 0 = d₀
  rw [if_pos rfl, Category.comp_id]

-- TODO simp lemmas for the inductive steps? It's not entirely clear that they are needed.
end Mk

section MkHom

variable {V}
variable (P Q : CochainComplex V ℕ) (zero : P.X 0 ⟶ Q.X 0) (one : P.X 1 ⟶ Q.X 1)
  (one_zero_comm : zero ≫ Q.d 0 1 = P.d 0 1 ≫ one)
  (succ : ∀ (n : ℕ) (p : Σ' (f : P.X n ⟶ Q.X n) (f' : P.X (n + 1) ⟶ Q.X (n + 1)),
          f ≫ Q.d n (n + 1) = P.d n (n + 1) ≫ f'),
      Σ' f'' : P.X (n + 2) ⟶ Q.X (n + 2), p.2.1 ≫ Q.d (n + 1) (n + 2) = P.d (n + 1) (n + 2) ≫ f'')

/-- An auxiliary construction for `mkHom`.

Here we build by induction a family of commutative squares,
but don't require at the type level that these successive commutative squares actually agree.
They do in fact agree, and we then capture that at the type level (i.e. by constructing a chain map)
in `mkHom`.
-/
/-
**CochainComplex.mkHomAux** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex`。
形式化陈述：{V : Type u} →   [inst : CategoryTheory.Category.{v, u} V] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms V] →       (P Q : CochainComplex V ℕ) → 
        (zero : P.X 0 ⟶ Q.X 0) →           (one : P.X 1 ⟶ Q.X 1) →             C
ategoryTheory.CategoryStruct.comp zero (Q.d 0 1) = CategoryTheory.CategoryStruct
.comp (P.d 0 1) one →               ((n : ℕ) →                   (p :           
            (f : P.X n ⟶ Q.X n) ×'                         (f' : P.X (n + 1) ⟶ Q
.X (n + 1)) ×'                           CategoryTheory.CategoryStruct.comp f (Q
.d n (n + 1)) =                             CategoryTheory.CategoryStruct.comp (
P.d n (n + 1)) f') →                     (f'' : P.X (n + 2) ⟶ Q.X (n + 2)) ×'   
                    CategoryTheory.CategoryStruct.comp p.snd.fst (Q.d (n + 1) (n
 + 2)) =                         CategoryTheory.CategoryStruct.comp (P.d (n + 1)
 (n + 2)) f'') →                 (n : ℕ) →                   (f : P.X n ⟶ Q.X n)
 ×'                     (f' : P.X (n + 1) ⟶ Q.X (n + 1)) ×'                     
  CategoryTheory.CategoryStruct.comp f (Q.d n (n + 1)) =                        
 CategoryTheory.CategoryStruct.comp (P.d n (n + 1)) f'
参数：P Q : CochainComplex V ℕ；zero : P.X 0 ⟶ Q.X 0；one : P.X 1 ⟶ Q.X 1；Q.d 0 1；P.d
 0 1；(n : ℕ) →                   (p :                       (f : P.X n ⟶ Q.X n) 
×'                         (f' : P.X (n + 1) ⟶ Q.X (n + 1)) ×'                  
         CategoryTheory.CategoryStruct.comp f (Q.d n (n + 1)) =                 
            CategoryTheory.CategoryStruct.comp (P.d n (n + 1)) f') →            
         (f'' : P.X (n + 2) ⟶ Q.X (n + 2)) ×'                       CategoryTheo
ry.CategoryStruct.comp p.snd.fst (Q.d (n + 1) (n + 2)) =                        
 CategoryTheory.CategoryStruct.comp (P.d (n + 1) (n + 2)) f''；n : ℕ；f : P.X n ⟶ 
Q.X n；f' : P.X (n + 1) ⟶ Q.X (n + 1)；Q.d n (n + 1)；P.d n (n + 1)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary construction for `mkHom`.

Here we build by induction a family of commutative squares,
but don't require at the type level that these successive commutative squares ac
tually agree.
They do in fact agree, and we then capture that at the type level (i.e. by const
ructing a chain map)
in `mkHom`.
-/
def mkHomAux :
    ∀ n,
      Σ' (f : P.X n ⟶ Q.X n) (f' : P.X (n + 1) ⟶ Q.X (n + 1)),
        f ≫ Q.d n (n + 1) = P.d n (n + 1) ≫ f'
  | 0 => ⟨zero, one, one_zero_comm⟩
  | n + 1 => ⟨(mkHomAux n).2.1, (succ n (mkHomAux n)).1, (succ n (mkHomAux n)).2⟩

/-- A constructor for chain maps between `ℕ`-indexed cochain complexes,
working by induction on commutative squares.

You need to provide the components of the chain map in degrees 0 and 1,
show that these form a commutative square,
and then give a construction of each component,
and the fact that it forms a commutative square with the previous component,
using as an inductive hypothesis the data (and commutativity) of the previous two components.
-/
/-
**CochainComplex.mkHom** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex`。
形式化陈述：mkHom : P ⟶ Q where f n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A constructor for chain maps between `ℕ`-indexed cochain complexes,
working by induction on commutative squares.

You need to provide the components of the chain map in degrees 0 and 1,
show that these form a commutative square,
and then give a construction of each component,
and the fact that it forms a commutative square with the previous component,
using as an inductive hypothesis the data (and commutativity) of the previous tw
o components.
-/
def mkHom : P ⟶ Q where
  f n := (mkHomAux P Q zero one one_zero_comm succ n).1
  comm' n m := by
    rintro (rfl : n + 1 = m)
    exact (mkHomAux P Q zero one one_zero_comm succ n).2.2

@[simp]
/-
**CochainComplex.mkHom_f_0** 是 Mathlib 中的一个定理，位于命名空间 `CochainComplex`。
形式化陈述：mkHom_f_0 : (mkHom P Q zero one one_zero_comm succ).f 0 = zero
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem mkHom_f_0 : (mkHom P Q zero one one_zero_comm succ).f 0 = zero :=
  rfl

@[simp]
/-
**CochainComplex.mkHom_f_1** 是 Mathlib 中的一个定理，位于命名空间 `CochainComplex`。
形式化陈述：mkHom_f_1 : (mkHom P Q zero one one_zero_comm succ).f 1 = one
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem mkHom_f_1 : (mkHom P Q zero one one_zero_comm succ).f 1 = one :=
  rfl

@[simp]
/-
**CochainComplex.mkHom_f_succ_succ** 是 Mathlib 中的一个定理，位于命名空间 `CochainComplex`。
形式化陈述：mkHom_f_succ_succ (n : Nat) : (mkHom P Q zero one one_zero_comm succ).f (n
 + 2) = (succ n ⟨(mkHom P Q zero one one_zero_comm succ).f n, (mkHom P Q zero on
e one_zero_comm succ).f (n + 1), (mkHom P Q zero one one_zero_comm succ).comm n 
(n + 1)⟩).1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem mkHom_f_succ_succ (n : ℕ) :
    (mkHom P Q zero one one_zero_comm succ).f (n + 2) =
      (succ n
          ⟨(mkHom P Q zero one one_zero_comm succ).f n,
            (mkHom P Q zero one one_zero_comm succ).f (n + 1),
            (mkHom P Q zero one one_zero_comm succ).comm n (n + 1)⟩).1 := by
  dsimp [mkHom, mkHomAux]

end MkHom

end CochainComplex

