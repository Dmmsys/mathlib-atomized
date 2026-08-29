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

/--
Definition of `HomologicalComplex` / `HomologicalComplex` 的定义

English:
structure HomologicalComplex
  parameters: (c : ComplexShape ι)
  axioms and operations (4):
    - X : ι -> V
    - d : forall i j, X i ⟶ X j
    - shape : forall i j, ¬c.Rel i j -> d i j = 0  [default: by cat_disch]
    - d_comp_d' : forall i j k, c.Rel i j -> c.Rel j k -> d i j ≫ d j k = 0  [default: by cat_disch]

中文:
结构 同调复形
  参数: (c : 余mplexShape ι)
  公理与运算 (4 个):
    - X : ι -> V
    - d : 对任意 i j, X i ⟶ X j
    - shape : 对任意 i j, ¬c.关系 i j -> d i j = 0  [默认: by cat_disch]
    - d_comp_d' : 对任意 i j k, c.关系 i j -> c.关系 j k -> d i j ≫ d j k = 0  [默认: by cat_disch]

Depends on / 依赖: c.Rel, cat_disch, d_comp_d
-/
structure HomologicalComplex (c : ComplexShape ι) where
  X : ι -> V
  d : forall i j, X i ⟶ X j
  shape : forall i j, ¬c.Rel i j -> d i j = 0 := by cat_disch
  d_comp_d' : forall i j k, c.Rel i j -> c.Rel j k -> d i j ≫ d j k = 0 := by cat_disch

namespace HomologicalComplex

attribute [simp] shape

variable {V} {c : ComplexShape ι}

@[reassoc (attr := simp)]
/--
theorem `d_comp_d` / 定理 `d_comp_d`

English:
theorem d_comp_d
  given: (C : HomologicalComplex V c) (i j k : ι)
  statement: C.d i j ≫ C.d j k = 0
  proof: by
  by_cases hij : c.Rel i j
  · by_cases hjk : c.Rel j k
    · exact C.d_comp_d' i j k hij hjk
    · rw [C.shape j k hjk, comp_zero]
  · rw [C.shape i j hij, zero_comp]

中文:
定理 d_comp_d
  条件: (C : 同调复形 V c) (i j k : ι)
  结论: C.d i j ≫ C.d j k = 0
  证明: by
  by_cases hij : c.Rel i j
  · by_cases hjk : c.Rel j k
    · exact C.d_comp_d' i j k hij hjk
    · rw [C.shape j k hjk, comp_zero]
  · rw [C.shape i j hij, zero_comp]

Depends on / 依赖: C.d_comp_d, C.shape, c.Rel, comp_zero, d_comp_d, zero_comp
-/
theorem d_comp_d (C : HomologicalComplex V c) (i j k : ι) : C.d i j ≫ C.d j k = 0 := by
  by_cases hij : c.Rel i j
  · by_cases hjk : c.Rel j k
    · exact C.d_comp_d' i j k hij hjk
    · rw [C.shape j k hjk, comp_zero]
  · rw [C.shape i j hij, zero_comp]

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: {C₁ C₂ : HomologicalComplex V c} (h_X : C₁.X = C₂.X)
  proof: by
  obtain ⟨X₁, d₁, s₁, h₁⟩ := C₁
  obtain ⟨X₂, d₂, s₂, h₂⟩ := C₂
  dsimp at h_X
  subst h_X
  simp only [mk.injEq, heq_eq_eq, true_and]
  ext i j
  by_cases hij : c.Rel i j
  · simpa only [comp_id, id_comp, eqToHom_refl] using h_d i j hij
  · rw [s₁ i j hij, s₂ i j hij]

中文:
定理 ext
  结论: {C₁ C₂ : 同调复形 V c} (h_X : C₁.X = C₂.X)
  证明: by
  obtain ⟨X₁, d₁, s₁, h₁⟩ := C₁
  obtain ⟨X₂, d₂, s₂, h₂⟩ := C₂
  dsimp at h_X
  subst h_X
  simp only [mk.injEq, heq_eq_eq, true_and]
  ext i j
  by_cases hij : c.Rel i j
  · simpa only [comp_id, id_comp, eqToHom_refl] using h_d i j hij
  · rw [s₁ i j hij, s₂ i j hij]

Depends on / 依赖: c.Rel, comp_id, eqToHom_refl, heq_eq_eq, id_comp, mk.injEq, true_and
-/
theorem ext {C₁ C₂ : HomologicalComplex V c} (h_X : C₁.X = C₂.X)
    (h_d :
      forall i j : ι,
        c.Rel i j -> C₁.d i j ≫ eqToHom (congr_fun h_X j) = eqToHom (congr_fun h_X i) ≫ C₂.d i j) :
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

/--
Definition of `XIsoOfEq` / `XIsoOfEq` 的定义

English:
definition XIsoOfEq
  signature: (K : HomologicalComplex V c) {p q : ι} (h : p = q)
  body: eqToIso (by rw [h])

@[simp]

中文:
定义 XIsoOfEq
  签名: (K : 同调复形 V c) {p q : ι} (h : p = q)
  定义体: eqToIso (by rw [h])

@[simp]

Depends on / 依赖: eqToIso
-/
def XIsoOfEq (K : HomologicalComplex V c) {p q : ι} (h : p = q) : K.X p ≅ K.X q :=
  eqToIso (by rw [h])

@[simp]
/--
lemma `XIsoOfEq_rfl` / 引理 `XIsoOfEq_rfl`

English:
lemma XIsoOfEq_rfl
  given: (K : HomologicalComplex V c) (p : ι)
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 XIsoOfEq_rfl
  条件: (K : 同调复形 V c) (p : ι)
  证明: rfl

@[reassoc (attr := simp)]
-/
lemma XIsoOfEq_rfl (K : HomologicalComplex V c) (p : ι) :
    K.XIsoOfEq (rfl : p = p) = Iso.refl _ := rfl

@[reassoc (attr := simp)]
/--
lemma `XIsoOfEq_hom_comp_XIsoOfEq_hom` / 引理 `XIsoOfEq_hom_comp_XIsoOfEq_hom`

English:
lemma XIsoOfEq_hom_comp_XIsoOfEq_hom
  statement: (K : HomologicalComplex V c) {p₁ p₂ p₃ : ι}
  proof: by
  dsimp [XIsoOfEq]
  simp only [eqToHom_trans]

@[reassoc (attr := simp)]

中文:
引理 XIsoOfEq_hom_comp_XIsoOfEq_hom
  结论: (K : 同调复形 V c) {p₁ p₂ p₃ : ι}
  证明: by
  dsimp [XIsoOfEq]
  simp only [eqToHom_trans]

@[reassoc (attr := simp)]

Depends on / 依赖: XIsoOfEq, eqToHom_trans
-/
lemma XIsoOfEq_hom_comp_XIsoOfEq_hom (K : HomologicalComplex V c) {p₁ p₂ p₃ : ι}
    (h₁₂ : p₁ = p₂) (h₂₃ : p₂ = p₃) :
    (K.XIsoOfEq h₁₂).hom ≫ (K.XIsoOfEq h₂₃).hom = (K.XIsoOfEq (h₁₂.trans h₂₃)).hom := by
  dsimp [XIsoOfEq]
  simp only [eqToHom_trans]

@[reassoc (attr := simp)]
/--
lemma `XIsoOfEq_hom_comp_XIsoOfEq_inv` / 引理 `XIsoOfEq_hom_comp_XIsoOfEq_inv`

English:
lemma XIsoOfEq_hom_comp_XIsoOfEq_inv
  statement: (K : HomologicalComplex V c) {p₁ p₂ p₃ : ι}
  proof: by
  dsimp [XIsoOfEq]
  simp only [eqToHom_trans]

@[reassoc (attr := simp)]

中文:
引理 XIsoOfEq_hom_comp_XIsoOfEq_inv
  结论: (K : 同调复形 V c) {p₁ p₂ p₃ : ι}
  证明: by
  dsimp [XIsoOfEq]
  simp only [eqToHom_trans]

@[reassoc (attr := simp)]

Depends on / 依赖: XIsoOfEq, eqToHom_trans
-/
lemma XIsoOfEq_hom_comp_XIsoOfEq_inv (K : HomologicalComplex V c) {p₁ p₂ p₃ : ι}
    (h₁₂ : p₁ = p₂) (h₃₂ : p₃ = p₂) :
    (K.XIsoOfEq h₁₂).hom ≫ (K.XIsoOfEq h₃₂).inv = (K.XIsoOfEq (h₁₂.trans h₃₂.symm)).hom := by
  dsimp [XIsoOfEq]
  simp only [eqToHom_trans]

@[reassoc (attr := simp)]
/--
lemma `XIsoOfEq_inv_comp_XIsoOfEq_hom` / 引理 `XIsoOfEq_inv_comp_XIsoOfEq_hom`

English:
lemma XIsoOfEq_inv_comp_XIsoOfEq_hom
  statement: (K : HomologicalComplex V c) {p₁ p₂ p₃ : ι}
  proof: by
  dsimp [XIsoOfEq]
  simp only [eqToHom_trans]

@[reassoc (attr := simp)]

中文:
引理 XIsoOfEq_inv_comp_XIsoOfEq_hom
  结论: (K : 同调复形 V c) {p₁ p₂ p₃ : ι}
  证明: by
  dsimp [XIsoOfEq]
  simp only [eqToHom_trans]

@[reassoc (attr := simp)]

Depends on / 依赖: XIsoOfEq, eqToHom_trans
-/
lemma XIsoOfEq_inv_comp_XIsoOfEq_hom (K : HomologicalComplex V c) {p₁ p₂ p₃ : ι}
    (h₂₁ : p₂ = p₁) (h₂₃ : p₂ = p₃) :
    (K.XIsoOfEq h₂₁).inv ≫ (K.XIsoOfEq h₂₃).hom = (K.XIsoOfEq (h₂₁.symm.trans h₂₃)).hom := by
  dsimp [XIsoOfEq]
  simp only [eqToHom_trans]

@[reassoc (attr := simp)]
/--
lemma `XIsoOfEq_inv_comp_XIsoOfEq_inv` / 引理 `XIsoOfEq_inv_comp_XIsoOfEq_inv`

English:
lemma XIsoOfEq_inv_comp_XIsoOfEq_inv
  statement: (K : HomologicalComplex V c) {p₁ p₂ p₃ : ι}
  proof: by
  dsimp [XIsoOfEq]
  simp only [eqToHom_trans]

@[reassoc (attr := simp)]

中文:
引理 XIsoOfEq_inv_comp_XIsoOfEq_inv
  结论: (K : 同调复形 V c) {p₁ p₂ p₃ : ι}
  证明: by
  dsimp [XIsoOfEq]
  simp only [eqToHom_trans]

@[reassoc (attr := simp)]

Depends on / 依赖: XIsoOfEq, eqToHom_trans
-/
lemma XIsoOfEq_inv_comp_XIsoOfEq_inv (K : HomologicalComplex V c) {p₁ p₂ p₃ : ι}
    (h₂₁ : p₂ = p₁) (h₃₂ : p₃ = p₂) :
    (K.XIsoOfEq h₂₁).inv ≫ (K.XIsoOfEq h₃₂).inv = (K.XIsoOfEq (h₃₂.trans h₂₁).symm).hom := by
  dsimp [XIsoOfEq]
  simp only [eqToHom_trans]

@[reassoc (attr := simp)]
/--
lemma `XIsoOfEq_hom_comp_d` / 引理 `XIsoOfEq_hom_comp_d`

English:
lemma XIsoOfEq_hom_comp_d
  given: (K : HomologicalComplex V c) {p₁ p₂ : ι} (h : p₁ = p₂) (p₃ : ι)
  proof: by subst h; simp

@[reassoc (attr := simp)]

中文:
引理 XIsoOfEq_hom_comp_d
  条件: (K : 同调复形 V c) {p₁ p₂ : ι} (h : p₁ = p₂) (p₃ : ι)
  证明: by subst h; simp

@[reassoc (attr := simp)]
-/
lemma XIsoOfEq_hom_comp_d (K : HomologicalComplex V c) {p₁ p₂ : ι} (h : p₁ = p₂) (p₃ : ι) :
    (K.XIsoOfEq h).hom ≫ K.d p₂ p₃ = K.d p₁ p₃ := by subst h; simp

@[reassoc (attr := simp)]
/--
lemma `XIsoOfEq_inv_comp_d` / 引理 `XIsoOfEq_inv_comp_d`

English:
lemma XIsoOfEq_inv_comp_d
  given: (K : HomologicalComplex V c) {p₂ p₁ : ι} (h : p₂ = p₁) (p₃ : ι)
  proof: by subst h; simp

@[reassoc (attr := simp)]

中文:
引理 XIsoOfEq_inv_comp_d
  条件: (K : 同调复形 V c) {p₂ p₁ : ι} (h : p₂ = p₁) (p₃ : ι)
  证明: by subst h; simp

@[reassoc (attr := simp)]
-/
lemma XIsoOfEq_inv_comp_d (K : HomologicalComplex V c) {p₂ p₁ : ι} (h : p₂ = p₁) (p₃ : ι) :
    (K.XIsoOfEq h).inv ≫ K.d p₂ p₃ = K.d p₁ p₃ := by subst h; simp

@[reassoc (attr := simp)]
/--
lemma `d_comp_XIsoOfEq_hom` / 引理 `d_comp_XIsoOfEq_hom`

English:
lemma d_comp_XIsoOfEq_hom
  given: (K : HomologicalComplex V c) {p₂ p₃ : ι} (h : p₂ = p₃) (p₁ : ι)
  proof: by subst h; simp

@[reassoc (attr := simp)]

中文:
引理 d_comp_XIsoOfEq_hom
  条件: (K : 同调复形 V c) {p₂ p₃ : ι} (h : p₂ = p₃) (p₁ : ι)
  证明: by subst h; simp

@[reassoc (attr := simp)]
-/
lemma d_comp_XIsoOfEq_hom (K : HomologicalComplex V c) {p₂ p₃ : ι} (h : p₂ = p₃) (p₁ : ι) :
    K.d p₁ p₂ ≫ (K.XIsoOfEq h).hom = K.d p₁ p₃ := by subst h; simp

@[reassoc (attr := simp)]
/--
lemma `d_comp_XIsoOfEq_inv` / 引理 `d_comp_XIsoOfEq_inv`

English:
lemma d_comp_XIsoOfEq_inv
  given: (K : HomologicalComplex V c) {p₂ p₃ : ι} (h : p₃ = p₂) (p₁ : ι)
  proof: by subst h; simp

中文:
引理 d_comp_XIsoOfEq_inv
  条件: (K : 同调复形 V c) {p₂ p₃ : ι} (h : p₃ = p₂) (p₁ : ι)
  证明: by subst h; simp
-/
lemma d_comp_XIsoOfEq_inv (K : HomologicalComplex V c) {p₂ p₃ : ι} (h : p₃ = p₂) (p₁ : ι) :
    K.d p₁ p₂ ≫ (K.XIsoOfEq h).inv = K.d p₁ p₃ := by subst h; simp

end HomologicalComplex

/--
Definition of `ChainComplex` / `ChainComplex` 的定义

English:
abbreviation ChainComplex
  signature: (α : Type*) [AddRightCancelSemigroup α] [One α]
  body: HomologicalComplex V (ComplexShape.down α)

中文:
缩写 链复形
  签名: (α : 类型) [加法右消去半群 α] [幺 α]
  定义体: HomologicalComplex V (ComplexShape.down α)

Depends on / 依赖: ComplexShape, ComplexShape.down, HomologicalComplex
-/
abbrev ChainComplex (α : Type*) [AddRightCancelSemigroup α] [One α] : Type _ :=
  HomologicalComplex V (ComplexShape.down α)

/--
Definition of `CochainComplex` / `CochainComplex` 的定义

English:
abbreviation CochainComplex
  signature: (α : Type*) [AddRightCancelSemigroup α] [One α]
  body: HomologicalComplex V (ComplexShape.up α)

中文:
缩写 上链复形
  签名: (α : 类型) [加法右消去半群 α] [幺 α]
  定义体: HomologicalComplex V (ComplexShape.up α)

Depends on / 依赖: ComplexShape, ComplexShape.up, HomologicalComplex
-/
abbrev CochainComplex (α : Type*) [AddRightCancelSemigroup α] [One α] : Type _ :=
  HomologicalComplex V (ComplexShape.up α)

namespace ChainComplex

@[simp]
/--
theorem `prev` / 定理 `prev`

English:
theorem prev
  given: (α : Type*) [AddRightCancelSemigroup α] [One α] (i : α)
  proof: (ComplexShape.down α).prev_eq' rfl

@[simp]

中文:
定理 prev
  条件: (α : 类型) [加法右消去半群 α] [幺 α] (i : α)
  证明: (ComplexShape.down α).prev_eq' rfl

@[simp]

Depends on / 依赖: ComplexShape, ComplexShape.down, prev_eq
-/
theorem prev (α : Type*) [AddRightCancelSemigroup α] [One α] (i : α) :
    (ComplexShape.down α).prev i = i + 1 :=
  (ComplexShape.down α).prev_eq' rfl

@[simp]
/--
theorem `next` / 定理 `next`

English:
theorem next
  given: (α : Type*) [AddGroup α] [One α] (i : α)
  statement: (ComplexShape.down α).next i = i - 1
  proof: (ComplexShape.down α).next_eq' sub_add_cancel _ _

@[simp]

中文:
定理 next
  条件: (α : 类型) [加法群 α] [幺 α] (i : α)
  结论: (余mplexShape.down α).next i = i - 1
  证明: (ComplexShape.down α).next_eq' sub_add_cancel _ _

@[simp]

Depends on / 依赖: ComplexShape, ComplexShape.down, next_eq, sub_add_cancel
-/
theorem next (α : Type*) [AddGroup α] [One α] (i : α) : (ComplexShape.down α).next i = i - 1 :=
(ComplexShape.down α).next_eq' sub_add_cancel _ _

@[simp]
/--
theorem `next_nat_zero` / 定理 `next_nat_zero`

English:
theorem next_nat_zero
  statement: (ComplexShape.down Nat).next 0 = 0
  proof: by
  refine dif_neg ?_
  push Not
  intro
  apply Nat.noConfusion

@[simp]

中文:
定理 next_nat_zero
  结论: (余mplexShape.down 自然数).next 0 = 0
  证明: by
  refine dif_neg ?_
  push Not
  intro
  apply Nat.noConfusion

@[simp]

Depends on / 依赖: Nat.noConfusion, dif_neg, noConfusion
-/
theorem next_nat_zero : (ComplexShape.down Nat).next 0 = 0 := by
  refine dif_neg ?_
  push Not
  intro
  apply Nat.noConfusion

@[simp]
/--
theorem `next_nat_succ` / 定理 `next_nat_succ`

English:
theorem next_nat_succ
  given: (i : Nat)
  statement: (ComplexShape.down Nat).next (i + 1) = i
  proof: (ComplexShape.down Nat).next_eq' rfl

中文:
定理 next_nat_succ
  条件: (i : 自然数)
  结论: (余mplexShape.down 自然数).next (i + 1) = i
  证明: (ComplexShape.down Nat).next_eq' rfl

Depends on / 依赖: ComplexShape, ComplexShape.down, next_eq
-/
theorem next_nat_succ (i : Nat) : (ComplexShape.down Nat).next (i + 1) = i :=
  (ComplexShape.down Nat).next_eq' rfl

end ChainComplex

namespace CochainComplex

@[simp]
/--
theorem `prev` / 定理 `prev`

English:
theorem prev
  given: (α : Type*) [AddGroup α] [One α] (i : α)
  statement: (ComplexShape.up α).prev i = i - 1
  proof: (ComplexShape.up α).prev_eq' sub_add_cancel _ _

@[simp]

中文:
定理 prev
  条件: (α : 类型) [加法群 α] [幺 α] (i : α)
  结论: (余mplexShape.up α).prev i = i - 1
  证明: (ComplexShape.up α).prev_eq' sub_add_cancel _ _

@[simp]

Depends on / 依赖: ComplexShape, ComplexShape.up, prev_eq, sub_add_cancel
-/
theorem prev (α : Type*) [AddGroup α] [One α] (i : α) : (ComplexShape.up α).prev i = i - 1 :=
(ComplexShape.up α).prev_eq' sub_add_cancel _ _

@[simp]
/--
theorem `next` / 定理 `next`

English:
theorem next
  given: (α : Type*) [AddRightCancelSemigroup α] [One α] (i : α)
  proof: (ComplexShape.up α).next_eq' rfl

@[simp]

中文:
定理 next
  条件: (α : 类型) [加法右消去半群 α] [幺 α] (i : α)
  证明: (ComplexShape.up α).next_eq' rfl

@[simp]

Depends on / 依赖: ComplexShape, ComplexShape.up, next_eq
-/
theorem next (α : Type*) [AddRightCancelSemigroup α] [One α] (i : α) :
    (ComplexShape.up α).next i = i + 1 :=
  (ComplexShape.up α).next_eq' rfl

@[simp]
/--
theorem `prev_nat_zero` / 定理 `prev_nat_zero`

English:
theorem prev_nat_zero
  statement: (ComplexShape.up Nat).prev 0 = 0
  proof: by
  refine dif_neg ?_
  push Not
  intro
  apply Nat.noConfusion

@[simp]

中文:
定理 prev_nat_zero
  结论: (余mplexShape.up 自然数).prev 0 = 0
  证明: by
  refine dif_neg ?_
  push Not
  intro
  apply Nat.noConfusion

@[simp]

Depends on / 依赖: Nat.noConfusion, dif_neg, noConfusion
-/
theorem prev_nat_zero : (ComplexShape.up Nat).prev 0 = 0 := by
  refine dif_neg ?_
  push Not
  intro
  apply Nat.noConfusion

@[simp]
/--
theorem `prev_nat_succ` / 定理 `prev_nat_succ`

English:
theorem prev_nat_succ
  given: (i : Nat)
  statement: (ComplexShape.up Nat).prev (i + 1) = i
  proof: (ComplexShape.up Nat).prev_eq' rfl

中文:
定理 prev_nat_succ
  条件: (i : 自然数)
  结论: (余mplexShape.up 自然数).prev (i + 1) = i
  证明: (ComplexShape.up Nat).prev_eq' rfl

Depends on / 依赖: ComplexShape, ComplexShape.up, prev_eq
-/
theorem prev_nat_succ (i : Nat) : (ComplexShape.up Nat).prev (i + 1) = i :=
  (ComplexShape.up Nat).prev_eq' rfl

end CochainComplex

namespace HomologicalComplex

variable {V}
variable {c : ComplexShape ι} (C : HomologicalComplex V c)

/-- A morphism of homological complexes consists of maps between the chain groups,
commuting with the differentials.
-/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (A B : HomologicalComplex V c)
  axioms and operations (2):
    - f : forall i, A.X i ⟶ B.X i
    - comm' : forall i j, c.Rel i j -> f i ≫ B.d i j = A.d i j ≫ f j  [default: by cat_disch]

中文:
结构 态射
  参数: (A B : 同调复形 V c)
  公理与运算 (2 个):
    - f : 对任意 i, A.X i ⟶ B.X i
    - comm' : 对任意 i j, c.关系 i j -> f i ≫ B.d i j = A.d i j ≫ f j  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure Hom (A B : HomologicalComplex V c) where
  f : forall i, A.X i ⟶ B.X i
  comm' : forall i j, c.Rel i j -> f i ≫ B.d i j = A.d i j ≫ f j := by cat_disch

@[reassoc (attr := simp)]
/--
theorem `Hom.comm` / 定理 `Hom.comm`

English:
theorem Hom.comm
  given: {A B : HomologicalComplex V c} (f : A.Hom B) (i j : ι)
  proof: by
  by_cases hij : c.Rel i j
  · exact f.comm' i j hij
  · rw [A.shape i j hij, B.shape i j hij, comp_zero, zero_comp]

中文:
定理 态射.comm
  条件: {A B : 同调复形 V c} (f : A.态射 B) (i j : ι)
  证明: by
  by_cases hij : c.Rel i j
  · exact f.comm' i j hij
  · rw [A.shape i j hij, B.shape i j hij, comp_zero, zero_comp]

Depends on / 依赖: A.shape, B.shape, c.Rel, comp_zero, f.comm, zero_comp
-/
theorem Hom.comm {A B : HomologicalComplex V c} (f : A.Hom B) (i j : ι) :
    f.f i ≫ B.d i j = A.d i j ≫ f.f j := by
  by_cases hij : c.Rel i j
  · exact f.comm' i j hij
  · rw [A.shape i j hij, B.shape i j hij, comp_zero, zero_comp]

instance (A B : HomologicalComplex V c) : Inhabited (Hom A B) :=
  ⟨{ f := fun _ => 0 }⟩

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (A : HomologicalComplex V c)
  body: 𝟙 _

中文:
定义 id
  签名: (A : 同调复形 V c)
  定义体: 𝟙 _
-/
def id (A : HomologicalComplex V c) : Hom A A where f _ := 𝟙 _

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (A B C : HomologicalComplex V c) (φ : Hom A B) (ψ : Hom B C)
  body: φ.f i ≫ ψ.f i

中文:
定义 comp
  签名: (A B C : 同调复形 V c) (φ : 态射 A B) (ψ : 态射 B C)
  定义体: φ.f i ≫ ψ.f i
-/
def comp (A B C : HomologicalComplex V c) (φ : Hom A B) (ψ : Hom B C) : Hom A C where
  f i := φ.f i ≫ ψ.f i

section

attribute [local simp] id comp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (HomologicalComplex V c)
  body: Hom
  id := id
  comp := comp _ _ _

中文:
实例 :
  签名: 范畴 (同调复形 V c)
  定义体: Hom
  id := id
  comp := comp _ _ _
-/
instance : Category (HomologicalComplex V c) where
  Hom := Hom
  id := id
  comp := comp _ _ _

end

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  statement: {C D : HomologicalComplex V c} (f g : C ⟶ D)
  proof: by
  apply Hom.ext
  funext
  apply h

@[simp]

中文:
引理 hom_ext
  结论: {C D : 同调复形 V c} (f g : C ⟶ D)
  证明: by
  apply Hom.ext
  funext
  apply h

@[simp]

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {C D : HomologicalComplex V c} (f g : C ⟶ D)
    (h : forall i, f.f i = g.f i) : f = g := by
  apply Hom.ext
  funext
  apply h

@[simp]
/--
theorem `id_f` / 定理 `id_f`

English:
theorem id_f
  given: (C : HomologicalComplex V c) (i : ι)
  statement: Hom.f (𝟙 C) i = 𝟙 (C.X i)
  proof: rfl

@[simp, reassoc]

中文:
定理 id_f
  条件: (C : 同调复形 V c) (i : ι)
  结论: 态射.f (𝟙 C) i = 𝟙 (C.X i)
  证明: rfl

@[simp, reassoc]
-/
theorem id_f (C : HomologicalComplex V c) (i : ι) : Hom.f (𝟙 C) i = 𝟙 (C.X i) :=
  rfl

@[simp, reassoc]
/--
theorem `comp_f` / 定理 `comp_f`

English:
theorem comp_f
  given: {C₁ C₂ C₃ : HomologicalComplex V c} (f : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i : ι)
  proof: rfl

@[simp]

中文:
定理 comp_f
  条件: {C₁ C₂ C₃ : 同调复形 V c} (f : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i : ι)
  证明: rfl

@[simp]
-/
theorem comp_f {C₁ C₂ C₃ : HomologicalComplex V c} (f : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i : ι) :
    (f ≫ g).f i = f.f i ≫ g.f i :=
  rfl

@[simp]
/--
theorem `eqToHom_f` / 定理 `eqToHom_f`

English:
theorem eqToHom_f
  given: {C₁ C₂ : HomologicalComplex V c} (h : C₁ = C₂) (n : ι)
  proof: by
  subst h
  rfl

中文:
定理 eqToHom_f
  条件: {C₁ C₂ : 同调复形 V c} (h : C₁ = C₂) (n : ι)
  证明: by
  subst h
  rfl
-/
theorem eqToHom_f {C₁ C₂ : HomologicalComplex V c} (h : C₁ = C₂) (n : ι) :
    HomologicalComplex.Hom.f (eqToHom h) n =
      eqToHom (congr_fun (congr_arg HomologicalComplex.X h) n) := by
  subst h
  rfl

-- We'll use this later to show that `HomologicalComplex V c` is preadditive when `V` is.
/--
theorem `hom_f_injective` / 定理 `hom_f_injective`

English:
theorem hom_f_injective
  given: {C₁ C₂ : HomologicalComplex V c}
  proof: by cat_disch

中文:
定理 hom_f_injective
  条件: {C₁ C₂ : 同调复形 V c}
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
theorem hom_f_injective {C₁ C₂ : HomologicalComplex V c} :
    Function.Injective fun f : Hom C₁ C₂ => f.f := by cat_disch

instance (X Y : HomologicalComplex V c) : Zero (X ⟶ Y) :=
  ⟨{ f := fun _ => 0}⟩

@[simp]
/--
theorem `zero_f` / 定理 `zero_f`

English:
theorem zero_f
  given: (C D : HomologicalComplex V c) (i : ι)
  statement: (0 : C ⟶ D).f i = 0
  proof: rfl

中文:
定理 zero_f
  条件: (C D : 同调复形 V c) (i : ι)
  结论: (0 : C ⟶ D).f i = 0
  证明: rfl
-/
theorem zero_f (C D : HomologicalComplex V c) (i : ι) : (0 : C ⟶ D).f i = 0 :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasZeroMorphisms (HomologicalComplex V c)

中文:
实例 :
  签名: 有ZeroMorphisms (同调复形 V c)
-/
instance : HasZeroMorphisms (HomologicalComplex V c) where

open ZeroObject

/--
Definition of `zero` / `zero` 的定义

English:
definition zero
  signature: [HasZeroObject V]
  body: 0
  d _ _ := 0

中文:
定义 zero
  签名: [有ZeroObject V]
  定义体: 0
  d _ _ := 0
-/
noncomputable def zero [HasZeroObject V] : HomologicalComplex V c where
  X _ := 0
  d _ _ := 0

/--
theorem `isZero_zero` / 定理 `isZero_zero`

English:
theorem isZero_zero
  given: [HasZeroObject V]
  statement: IsZero (zero : HomologicalComplex V c)
  proof: by
  refine ⟨fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩⟩
  all_goals
    ext
    dsimp only [zero]
    subsingleton

中文:
定理 isZero_zero
  条件: [有ZeroObject V]
  结论: 是零 (zero : 同调复形 V c)
  证明: by
  refine ⟨fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩⟩
  all_goals
    ext
    dsimp only [zero]
    subsingleton

Depends on / 依赖: all_goals, subsingleton
-/
theorem isZero_zero [HasZeroObject V] : IsZero (zero : HomologicalComplex V c) := by
  refine ⟨fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩⟩
  all_goals
    ext
    dsimp only [zero]
    subsingleton

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasZeroObject
  signature: V] : HasZeroObject (HomologicalComplex V c)
  body: ⟨⟨zero, isZero_zero⟩⟩

中文:
实例 [有ZeroObject
  签名: V] : 有ZeroObject (同调复形 V c)
  定义体: ⟨⟨zero, isZero_zero⟩⟩

Depends on / 依赖: isZero_zero
-/
instance [HasZeroObject V] : HasZeroObject (HomologicalComplex V c) :=
  ⟨⟨zero, isZero_zero⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasZeroObject
  signature: V] : Inhabited (HomologicalComplex V c)
  body: ⟨zero⟩

中文:
实例 [有ZeroObject
  签名: V] : 可居 (同调复形 V c)
  定义体: ⟨zero⟩
-/
noncomputable instance [HasZeroObject V] : Inhabited (HomologicalComplex V c) :=
  ⟨zero⟩

/--
theorem `congr_hom` / 定理 `congr_hom`

English:
theorem congr_hom
  given: {C D : HomologicalComplex V c} {f g : C ⟶ D} (w : f = g) (i : ι)
  proof: congr_fun (congr_arg Hom.f w) i

中文:
定理 congr_hom
  条件: {C D : 同调复形 V c} {f g : C ⟶ D} (w : f = g) (i : ι)
  证明: congr_fun (congr_arg Hom.f w) i

Depends on / 依赖: Hom.f, congr_arg, congr_fun
-/
theorem congr_hom {C D : HomologicalComplex V c} {f g : C ⟶ D} (w : f = g) (i : ι) :
    f.f i = g.f i :=
  congr_fun (congr_arg Hom.f w) i

/--
lemma `mono_of_mono_f` / 引理 `mono_of_mono_f`

English:
lemma mono_of_mono_f
  statement: {K L : HomologicalComplex V c} (φ : K ⟶ L)
  proof: by
    ext i
    rw [← cancel_mono (φ.f i)]
    exact congr_hom eq i

中文:
引理 mono_of_mono_f
  结论: {K L : 同调复形 V c} (φ : K ⟶ L)
  证明: by
    ext i
    rw [← cancel_mono (φ.f i)]
    exact congr_hom eq i

Depends on / 依赖: cancel_mono, congr_hom
-/
lemma mono_of_mono_f {K L : HomologicalComplex V c} (φ : K ⟶ L)
    (hφ : forall i, Mono (φ.f i)) : Mono φ where
  right_cancellation g h eq := by
    ext i
    rw [← cancel_mono (φ.f i)]
    exact congr_hom eq i

/--
lemma `epi_of_epi_f` / 引理 `epi_of_epi_f`

English:
lemma epi_of_epi_f
  statement: {K L : HomologicalComplex V c} (φ : K ⟶ L)
  proof: by
    ext i
    rw [← cancel_epi (φ.f i)]
    exact congr_hom eq i

中文:
引理 epi_of_epi_f
  结论: {K L : 同调复形 V c} (φ : K ⟶ L)
  证明: by
    ext i
    rw [← cancel_epi (φ.f i)]
    exact congr_hom eq i

Depends on / 依赖: cancel_epi, congr_hom
-/
lemma epi_of_epi_f {K L : HomologicalComplex V c} (φ : K ⟶ L)
    (hφ : forall i, Epi (φ.f i)) : Epi φ where
  left_cancellation g h eq := by
    ext i
    rw [← cancel_epi (φ.f i)]
    exact congr_hom eq i

section

variable (V c)

/-- The functor picking out the `i`-th object of a complex. -/
@[simps]
/--
Definition of `eval` / `eval` 的定义

English:
definition eval
  signature: (i : ι)
  body: C.X i
  map f := f.f i

中文:
定义 eval
  签名: (i : ι)
  定义体: C.X i
  map f := f.f i
-/
def eval (i : ι) : HomologicalComplex V c ⥤ V where
  obj C := C.X i
  map f := f.f i

instance (i : ι) : (eval V c i).PreservesZeroMorphisms where

/-- The functor forgetting the differential in a complex, obtaining a graded object. -/
@[simps]
/--
Definition of `forget` / `forget` 的定义

English:
definition forget
  signature: : HomologicalComplex V c ⥤ GradedObject ι V where
  body: C.X
  map f := f.f

中文:
定义 forget
  签名: : 同调复形 V c ⥤ GradedObject ι V where
  定义体: C.X
  map f := f.f
-/
def forget : HomologicalComplex V c ⥤ GradedObject ι V where
  obj C := C.X
  map f := f.f

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget V c).Faithful
  body: by
    ext i
    exact congr_fun h i

中文:
实例 :
  签名: (forget V c).忠实
  定义体: by
    ext i
    exact congr_fun h i

Depends on / 依赖: congr_fun
-/
instance : (forget V c).Faithful where
  map_injective h := by
    ext i
    exact congr_fun h i

set_option backward.defeqAttrib.useBackward true in
/-- Forgetting the differentials than picking out the `i`-th object is the same as
just picking out the `i`-th object. -/
@[simps!]
/--
Definition of `forgetEval` / `forgetEval` 的定义

English:
definition forgetEval
  signature: (i : ι)
  body: NatIso.ofComponents fun _ => Iso.refl _

中文:
定义 forgetEval
  签名: (i : ι)
  定义体: NatIso.ofComponents fun _ => Iso.refl _

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def forgetEval (i : ι) : forget V c ⋙ GradedObject.eval i ≅ eval V c i :=
  NatIso.ofComponents fun _ => Iso.refl _

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `dNatTrans` / `dNatTrans` 的定义

English:
definition dNatTrans
  signature: (i j : ι)
  body: X.d i j

中文:
定义 d自然数Trans
  签名: (i j : ι)
  定义体: X.d i j
-/
@[simps] def dNatTrans (i j : ι) :
    HomologicalComplex.eval V c i ⟶ HomologicalComplex.eval V c j where
  app X := X.d i j

end

noncomputable section

@[reassoc]
/--
lemma `XIsoOfEq_hom_naturality` / 引理 `XIsoOfEq_hom_naturality`

English:
lemma XIsoOfEq_hom_naturality
  given: {K L : HomologicalComplex V c} (φ : K ⟶ L) {n n' : ι} (h : n = n')
  proof: by subst h; simp

@[reassoc]

中文:
引理 XIsoOfEq_hom_naturality
  条件: {K L : 同调复形 V c} (φ : K ⟶ L) {n n' : ι} (h : n = n')
  证明: by subst h; simp

@[reassoc]
-/
lemma XIsoOfEq_hom_naturality {K L : HomologicalComplex V c} (φ : K ⟶ L) {n n' : ι} (h : n = n') :
    φ.f n ≫ (L.XIsoOfEq h).hom = (K.XIsoOfEq h).hom ≫ φ.f n' := by subst h; simp

@[reassoc]
/--
lemma `XIsoOfEq_inv_naturality` / 引理 `XIsoOfEq_inv_naturality`

English:
lemma XIsoOfEq_inv_naturality
  given: {K L : HomologicalComplex V c} (φ : K ⟶ L) {n n' : ι} (h : n = n')
  proof: by subst h; simp

中文:
引理 XIsoOfEq_inv_naturality
  条件: {K L : 同调复形 V c} (φ : K ⟶ L) {n n' : ι} (h : n = n')
  证明: by subst h; simp
-/
lemma XIsoOfEq_inv_naturality {K L : HomologicalComplex V c} (φ : K ⟶ L) {n n' : ι} (h : n = n') :
    φ.f n' ≫ (L.XIsoOfEq h).inv = (K.XIsoOfEq h).inv ≫ φ.f n := by subst h; simp

/-- If `C.d i j` and `C.d i j'` are both allowed, then we must have `j = j'`,
and so the differentials only differ by an `eqToHom`.
-/
@[simp]
/--
theorem `d_comp_eqToHom` / 定理 `d_comp_eqToHom`

English:
theorem d_comp_eqToHom
  given: {i j j' : ι} (rij : c.Rel i j) (rij' : c.Rel i j')
  proof: by
  obtain rfl := c.next_eq rij rij'
  simp only [eqToHom_refl, comp_id]

中文:
定理 d_comp_eqToHom
  条件: {i j j' : ι} (rij : c.关系 i j) (rij' : c.关系 i j')
  证明: by
  obtain rfl := c.next_eq rij rij'
  simp only [eqToHom_refl, comp_id]

Depends on / 依赖: c.next_eq, comp_id, eqToHom_refl, next_eq
-/
theorem d_comp_eqToHom {i j j' : ι} (rij : c.Rel i j) (rij' : c.Rel i j') :
    C.d i j' ≫ eqToHom (congr_arg C.X (c.next_eq rij' rij)) = C.d i j := by
  obtain rfl := c.next_eq rij rij'
  simp only [eqToHom_refl, comp_id]

/-- If `C.d i j` and `C.d i' j` are both allowed, then we must have `i = i'`,
and so the differentials only differ by an `eqToHom`.
-/
@[simp]
/--
theorem `eqToHom_comp_d` / 定理 `eqToHom_comp_d`

English:
theorem eqToHom_comp_d
  given: {i i' j : ι} (rij : c.Rel i j) (rij' : c.Rel i' j)
  proof: by
  obtain rfl := c.prev_eq rij rij'
  simp only [eqToHom_refl, id_comp]

中文:
定理 eqToHom_comp_d
  条件: {i i' j : ι} (rij : c.关系 i j) (rij' : c.关系 i' j)
  证明: by
  obtain rfl := c.prev_eq rij rij'
  simp only [eqToHom_refl, id_comp]

Depends on / 依赖: c.prev_eq, eqToHom_refl, id_comp, prev_eq
-/
theorem eqToHom_comp_d {i i' j : ι} (rij : c.Rel i j) (rij' : c.Rel i' j) :
    eqToHom (congr_arg C.X (c.prev_eq rij rij')) ≫ C.d i' j = C.d i j := by
  obtain rfl := c.prev_eq rij rij'
  simp only [eqToHom_refl, id_comp]

/--
theorem `kernel_eq_kernel` / 定理 `kernel_eq_kernel`

English:
theorem kernel_eq_kernel
  given: [HasKernels V] {i j j' : ι} (r : c.Rel i j) (r' : c.Rel i j')
  proof: by
  rw [← d_comp_eqToHom C r r']
  apply kernelSubobject_comp_mono

中文:
定理 kernel_eq_kernel
  条件: [有Kernels V] {i j j' : ι} (r : c.关系 i j) (r' : c.关系 i j')
  证明: by
  rw [← d_comp_eqToHom C r r']
  apply kernelSubobject_comp_mono

Depends on / 依赖: d_comp_eqToHom, kernelSubobject_comp_mono
-/
theorem kernel_eq_kernel [HasKernels V] {i j j' : ι} (r : c.Rel i j) (r' : c.Rel i j') :
    kernelSubobject (C.d i j) = kernelSubobject (C.d i j') := by
  rw [← d_comp_eqToHom C r r']
  apply kernelSubobject_comp_mono

/--
theorem `image_eq_image` / 定理 `image_eq_image`

English:
theorem image_eq_image
  statement: [HasImages V] [HasEqualizers V] {i i' j : ι} (r : c.Rel i j)
  proof: by
  rw [← eqToHom_comp_d C r r']
  apply imageSubobject_iso_comp

中文:
定理 image_eq_image
  结论: [有Images V] [HasEqualizers V] {i i' j : ι} (r : c.关系 i j)
  证明: by
  rw [← eqToHom_comp_d C r r']
  apply imageSubobject_iso_comp

Depends on / 依赖: eqToHom_comp_d, imageSubobject_iso_comp
-/
theorem image_eq_image [HasImages V] [HasEqualizers V] {i i' j : ι} (r : c.Rel i j)
    (r' : c.Rel i' j) : imageSubobject (C.d i j) = imageSubobject (C.d i' j) := by
  rw [← eqToHom_comp_d C r r']
  apply imageSubobject_iso_comp

section

/--
Definition of `xPrev` / `xPrev` 的定义

English:
abbreviation xPrev
  signature: (j : ι)
  body: C.X (c.prev j)

中文:
缩写 xPrev
  签名: (j : ι)
  定义体: C.X (c.prev j)

Depends on / 依赖: c.prev
-/
abbrev xPrev (j : ι) : V :=
  C.X (c.prev j)

/--
Definition of `xPrevIso` / `xPrevIso` 的定义

English:
definition xPrevIso
  signature: {i j : ι} (r : c.Rel i j)
  body: eqToIso by rw [← c.prev_eq' r]

中文:
定义 xPrevIso
  签名: {i j : ι} (r : c.关系 i j)
  定义体: eqToIso by rw [← c.prev_eq' r]

Depends on / 依赖: c.prev_eq, eqToIso, prev_eq
-/
def xPrevIso {i j : ι} (r : c.Rel i j) : C.xPrev j ≅ C.X i :=
eqToIso by rw [← c.prev_eq' r]

/--
Definition of `xPrevIsoSelf` / `xPrevIsoSelf` 的定义

English:
definition xPrevIsoSelf
  signature: {j : ι} (h : ¬c.Rel (c.prev j) j)
  body: eqToIso
    congr_arg C.X
      (by
        dsimp [ComplexShape.prev]
        rw [dif_neg]
        push Not; intro i hi
        have : c.prev j = i := c.prev_eq' hi
        rw [this] at h; contradiction)

中文:
定义 xPrevIsoSelf
  签名: {j : ι} (h : ¬c.关系 (c.prev j) j)
  定义体: eqToIso
    congr_arg C.X
      (by
        dsimp [ComplexShape.prev]
        rw [dif_neg]
        push Not; intro i hi
        have : c.prev j = i := c.prev_eq' hi
        rw [this] at h; contradiction)

Depends on / 依赖: ComplexShape, ComplexShape.prev, c.prev, c.prev_eq, congr_arg, dif_neg, eqToIso, prev_eq
-/
def xPrevIsoSelf {j : ι} (h : ¬c.Rel (c.prev j) j) : C.xPrev j ≅ C.X j :=
eqToIso
    congr_arg C.X
      (by
        dsimp [ComplexShape.prev]
        rw [dif_neg]
        push Not; intro i hi
        have : c.prev j = i := c.prev_eq' hi
        rw [this] at h; contradiction)

/--
Definition of `xNext` / `xNext` 的定义

English:
abbreviation xNext
  signature: (i : ι)
  body: C.X (c.next i)

中文:
缩写 xNext
  签名: (i : ι)
  定义体: C.X (c.next i)

Depends on / 依赖: c.next, infer_instance, singleFunctor, singleFunctors
-/
abbrev xNext (i : ι) : V :=
  C.X (c.next i)

/--
Definition of `xNextIso` / `xNextIso` 的定义

English:
definition xNextIso
  signature: {i j : ι} (r : c.Rel i j)
  body: eqToIso by rw [← c.next_eq' r]

中文:
定义 xNextIso
  签名: {i j : ι} (r : c.关系 i j)
  定义体: eqToIso by rw [← c.next_eq' r]

Depends on / 依赖: c.next_eq, eqToIso, next_eq
-/
def xNextIso {i j : ι} (r : c.Rel i j) : C.xNext i ≅ C.X j :=
eqToIso by rw [← c.next_eq' r]

/--
Definition of `xNextIsoSelf` / `xNextIsoSelf` 的定义

English:
definition xNextIsoSelf
  signature: {i : ι} (h : ¬c.Rel i (c.next i))
  body: eqToIso
    congr_arg C.X
      (by
        dsimp [ComplexShape.next]
        rw [dif_neg]; rintro ⟨j, hj⟩
        have : c.next i = j := c.next_eq' hj
        rw [this] at h; contradiction)

中文:
定义 xNextIsoSelf
  签名: {i : ι} (h : ¬c.关系 i (c.next i))
  定义体: eqToIso
    congr_arg C.X
      (by
        dsimp [ComplexShape.next]
        rw [dif_neg]; rintro ⟨j, hj⟩
        have : c.next i = j := c.next_eq' hj
        rw [this] at h; contradiction)

Depends on / 依赖: ComplexShape, ComplexShape.next, c.next, c.next_eq, congr_arg, dif_neg, eqToIso, next_eq
-/
def xNextIsoSelf {i : ι} (h : ¬c.Rel i (c.next i)) : C.xNext i ≅ C.X i :=
eqToIso
    congr_arg C.X
      (by
        dsimp [ComplexShape.next]
        rw [dif_neg]; rintro ⟨j, hj⟩
        have : c.next i = j := c.next_eq' hj
        rw [this] at h; contradiction)

/--
Definition of `dTo` / `dTo` 的定义

English:
abbreviation dTo
  signature: (j : ι)
  body: C.d (c.prev j) j

中文:
缩写 dTo
  签名: (j : ι)
  定义体: C.d (c.prev j) j

Depends on / 依赖: c.prev
-/
abbrev dTo (j : ι) : C.xPrev j ⟶ C.X j :=
  C.d (c.prev j) j

/--
Definition of `dFrom` / `dFrom` 的定义

English:
abbreviation dFrom
  signature: (i : ι)
  body: C.d i (c.next i)

中文:
缩写 dFrom
  签名: (i : ι)
  定义体: C.d i (c.next i)

Depends on / 依赖: c.next
-/
abbrev dFrom (i : ι) : C.X i ⟶ C.xNext i :=
  C.d i (c.next i)

/--
theorem `dTo_eq` / 定理 `dTo_eq`

English:
theorem dTo_eq
  given: {i j : ι} (r : c.Rel i j)
  statement: C.dTo j = (C.xPrevIso r).hom ≫ C.d i j
  proof: by
  obtain rfl := c.prev_eq' r
  exact (Category.id_comp _).symm

中文:
定理 dTo_eq
  条件: {i j : ι} (r : c.关系 i j)
  结论: C.dTo j = (C.xPrevIso r).hom ≫ C.d i j
  证明: by
  obtain rfl := c.prev_eq' r
  exact (Category.id_comp _).symm

Depends on / 依赖: Category, Category.id_comp, c.prev_eq, id_comp, prev_eq
-/
theorem dTo_eq {i j : ι} (r : c.Rel i j) : C.dTo j = (C.xPrevIso r).hom ≫ C.d i j := by
  obtain rfl := c.prev_eq' r
  exact (Category.id_comp _).symm

/--
theorem `dTo_eq_zero` / 定理 `dTo_eq_zero`

English:
theorem dTo_eq_zero
  given: {j : ι} (h : ¬c.Rel (c.prev j) j)
  statement: C.dTo j = 0
  proof: by
  simp [h]

中文:
定理 dTo_eq_zero
  条件: {j : ι} (h : ¬c.关系 (c.prev j) j)
  结论: C.dTo j = 0
  证明: by
  simp [h]
-/
theorem dTo_eq_zero {j : ι} (h : ¬c.Rel (c.prev j) j) : C.dTo j = 0 := by
  simp [h]

/--
theorem `dFrom_eq` / 定理 `dFrom_eq`

English:
theorem dFrom_eq
  given: {i j : ι} (r : c.Rel i j)
  statement: C.dFrom i = C.d i j ≫ (C.xNextIso r).inv
  proof: by
  obtain rfl := c.next_eq' r
  exact (Category.comp_id _).symm

中文:
定理 dFrom_eq
  条件: {i j : ι} (r : c.关系 i j)
  结论: C.dFrom i = C.d i j ≫ (C.xNextIso r).inv
  证明: by
  obtain rfl := c.next_eq' r
  exact (Category.comp_id _).symm

Depends on / 依赖: Category, Category.comp_id, c.next_eq, comp_id, next_eq
-/
theorem dFrom_eq {i j : ι} (r : c.Rel i j) : C.dFrom i = C.d i j ≫ (C.xNextIso r).inv := by
  obtain rfl := c.next_eq' r
  exact (Category.comp_id _).symm

/--
theorem `dFrom_eq_zero` / 定理 `dFrom_eq_zero`

English:
theorem dFrom_eq_zero
  given: {i : ι} (h : ¬c.Rel i (c.next i))
  statement: C.dFrom i = 0
  proof: by
  simp [h]

@[reassoc (attr := simp)]

中文:
定理 dFrom_eq_zero
  条件: {i : ι} (h : ¬c.关系 i (c.next i))
  结论: C.dFrom i = 0
  证明: by
  simp [h]

@[reassoc (attr := simp)]
-/
theorem dFrom_eq_zero {i : ι} (h : ¬c.Rel i (c.next i)) : C.dFrom i = 0 := by
  simp [h]

@[reassoc (attr := simp)]
/--
theorem `xPrevIso_comp_dTo` / 定理 `xPrevIso_comp_dTo`

English:
theorem xPrevIso_comp_dTo
  given: {i j : ι} (r : c.Rel i j)
  statement: (C.xPrevIso r).inv ≫ C.dTo j = C.d i j
  proof: by
  simp [C.dTo_eq r]

@[reassoc]

中文:
定理 xPrevIso_comp_dTo
  条件: {i j : ι} (r : c.关系 i j)
  结论: (C.xPrevIso r).inv ≫ C.dTo j = C.d i j
  证明: by
  simp [C.dTo_eq r]

@[reassoc]

Depends on / 依赖: C.dTo_eq, dTo_eq
-/
theorem xPrevIso_comp_dTo {i j : ι} (r : c.Rel i j) : (C.xPrevIso r).inv ≫ C.dTo j = C.d i j := by
  simp [C.dTo_eq r]

@[reassoc]
/--
theorem `xPrevIsoSelf_comp_dTo` / 定理 `xPrevIsoSelf_comp_dTo`

English:
theorem xPrevIsoSelf_comp_dTo
  given: {j : ι} (h : ¬c.Rel (c.prev j) j)
  proof: by simp [h]

@[reassoc (attr := simp)]

中文:
定理 xPrevIsoSelf_comp_dTo
  条件: {j : ι} (h : ¬c.关系 (c.prev j) j)
  证明: by simp [h]

@[reassoc (attr := simp)]
-/
theorem xPrevIsoSelf_comp_dTo {j : ι} (h : ¬c.Rel (c.prev j) j) :
    (C.xPrevIsoSelf h).inv ≫ C.dTo j = 0 := by simp [h]

@[reassoc (attr := simp)]
/--
theorem `dFrom_comp_xNextIso` / 定理 `dFrom_comp_xNextIso`

English:
theorem dFrom_comp_xNextIso
  given: {i j : ι} (r : c.Rel i j)
  proof: by
  simp [C.dFrom_eq r]

@[reassoc]

中文:
定理 dFrom_comp_xNextIso
  条件: {i j : ι} (r : c.关系 i j)
  证明: by
  simp [C.dFrom_eq r]

@[reassoc]

Depends on / 依赖: C.dFrom_eq, dFrom_eq
-/
theorem dFrom_comp_xNextIso {i j : ι} (r : c.Rel i j) :
    C.dFrom i ≫ (C.xNextIso r).hom = C.d i j := by
  simp [C.dFrom_eq r]

@[reassoc]
/--
theorem `dFrom_comp_xNextIsoSelf` / 定理 `dFrom_comp_xNextIsoSelf`

English:
theorem dFrom_comp_xNextIsoSelf
  given: {i : ι} (h : ¬c.Rel i (c.next i))
  proof: by simp [h]

中文:
定理 dFrom_comp_xNextIsoSelf
  条件: {i : ι} (h : ¬c.关系 i (c.next i))
  证明: by simp [h]
-/
theorem dFrom_comp_xNextIsoSelf {i : ι} (h : ¬c.Rel i (c.next i)) :
    C.dFrom i ≫ (C.xNextIsoSelf h).hom = 0 := by simp [h]

-- This is not a simp lemma; the LHS already simplifies.
/--
theorem `dTo_comp_dFrom` / 定理 `dTo_comp_dFrom`

English:
theorem dTo_comp_dFrom
  given: (j : ι)
  statement: C.dTo j ≫ C.dFrom j = 0
  proof: C.d_comp_d _ _ _

中文:
定理 dTo_comp_dFrom
  条件: (j : ι)
  结论: C.dTo j ≫ C.dFrom j = 0
  证明: C.d_comp_d _ _ _

Depends on / 依赖: C.d_comp_d, d_comp_d
-/
theorem dTo_comp_dFrom (j : ι) : C.dTo j ≫ C.dFrom j = 0 :=
  C.d_comp_d _ _ _

/--
theorem `kernel_from_eq_kernel` / 定理 `kernel_from_eq_kernel`

English:
theorem kernel_from_eq_kernel
  given: [HasKernels V] {i j : ι} (r : c.Rel i j)
  proof: by
  rw [C.dFrom_eq r]
  apply kernelSubobject_comp_mono

中文:
定理 kernel_from_eq_kernel
  条件: [有Kernels V] {i j : ι} (r : c.关系 i j)
  证明: by
  rw [C.dFrom_eq r]
  apply kernelSubobject_comp_mono

Depends on / 依赖: C.dFrom_eq, dFrom_eq, kernelSubobject_comp_mono
-/
theorem kernel_from_eq_kernel [HasKernels V] {i j : ι} (r : c.Rel i j) :
    kernelSubobject (C.dFrom i) = kernelSubobject (C.d i j) := by
  rw [C.dFrom_eq r]
  apply kernelSubobject_comp_mono

/--
theorem `image_to_eq_image` / 定理 `image_to_eq_image`

English:
theorem image_to_eq_image
  given: [HasImages V] [HasEqualizers V] {i j : ι} (r : c.Rel i j)
  proof: by
  rw [C.dTo_eq r]
  apply imageSubobject_iso_comp

中文:
定理 image_to_eq_image
  条件: [有Images V] [HasEqualizers V] {i j : ι} (r : c.关系 i j)
  证明: by
  rw [C.dTo_eq r]
  apply imageSubobject_iso_comp

Depends on / 依赖: C.dTo_eq, dTo_eq, imageSubobject_iso_comp
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
/--
Definition of `isoApp` / `isoApp` 的定义

English:
definition isoApp
  signature: (f : C₁ ≅ C₂) (i : ι)
  body: (eval V c i).mapIso f

中文:
定义 isoApp
  签名: (f : C₁ ≅ C₂) (i : ι)
  定义体: (eval V c i).mapIso f

Depends on / 依赖: mapIso
-/
def isoApp (f : C₁ ≅ C₂) (i : ι) : C₁.X i ≅ C₂.X i :=
  (eval V c i).mapIso f

/-- Construct an isomorphism of chain complexes from isomorphism of the objects
which commute with the differentials. -/
@[simps]
/--
Definition of `isoOfComponents` / `isoOfComponents` 的定义

English:
definition isoOfComponents
  signature: (f : forall i, C₁.X i ≅ C₂.X i)
  body: { f := fun i => (f i).hom
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

中文:
定义 isoOfComponents
  签名: (f : 对任意 i, C₁.X i ≅ C₂.X i)
  定义体: { f := fun i => (f i).hom
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

Depends on / 依赖: cat_disch, hom_inv_id, inv_hom_id
-/
def isoOfComponents (f : forall i, C₁.X i ≅ C₂.X i)
    (hf : forall i j, c.Rel i j -> (f i).hom ≫ C₂.d i j = C₁.d i j ≫ (f j).hom := by cat_disch) :
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
/--
theorem `isoOfComponents_app` / 定理 `isoOfComponents_app`

English:
theorem isoOfComponents_app
  statement: (f : forall i, C₁.X i ≅ C₂.X i)
  proof: by
  ext
  simp

中文:
定理 isoOfComponents_app
  结论: (f : 对任意 i, C₁.X i ≅ C₂.X i)
  证明: by
  ext
  simp
-/
theorem isoOfComponents_app (f : forall i, C₁.X i ≅ C₂.X i)
    (hf : forall i j, c.Rel i j -> (f i).hom ≫ C₂.d i j = C₁.d i j ≫ (f j).hom) (i : ι) :
    isoApp (isoOfComponents f hf) i = f i := by
  ext
  simp

/--
theorem `isIso_of_components` / 定理 `isIso_of_components`

English:
theorem isIso_of_components
  given: (f : C₁ ⟶ C₂) [forall n : ι, IsIso (f.f n)]
  statement: IsIso f
  proof: (HomologicalComplex.Hom.isoOfComponents fun n => asIso (f.f n)).isIso_hom

中文:
定理 isIso_of_components
  条件: (f : C₁ ⟶ C₂) [对任意 n : ι, 是同构 (f.f n)]
  结论: 是同构 f
  证明: (HomologicalComplex.Hom.isoOfComponents fun n => asIso (f.f n)).isIso_hom

Depends on / 依赖: HomologicalComplex, HomologicalComplex.Hom.isoOfComponents, isIso_hom, isoOfComponents
-/
theorem isIso_of_components (f : C₁ ⟶ C₂) [forall n : ι, IsIso (f.f n)] : IsIso f :=
  (HomologicalComplex.Hom.isoOfComponents fun n => asIso (f.f n)).isIso_hom

/-! Lemmas relating chain maps and `dTo`/`dFrom`. -/


/--
Definition of `prev` / `prev` 的定义

English:
abbreviation prev
  signature: (f : Hom C₁ C₂) (j : ι)
  body: f.f _

中文:
缩写 prev
  签名: (f : 态射 C₁ C₂) (j : ι)
  定义体: f.f _
-/
abbrev prev (f : Hom C₁ C₂) (j : ι) : C₁.xPrev j ⟶ C₂.xPrev j :=
  f.f _

/--
theorem `prev_eq` / 定理 `prev_eq`

English:
theorem prev_eq
  given: (f : Hom C₁ C₂) {i j : ι} (w : c.Rel i j)
  proof: by
  obtain rfl := c.prev_eq' w
  simp only [xPrevIso, eqToIso_refl, Iso.refl_hom, Iso.refl_inv, comp_id, id_comp]

中文:
定理 prev_eq
  条件: (f : 态射 C₁ C₂) {i j : ι} (w : c.关系 i j)
  证明: by
  obtain rfl := c.prev_eq' w
  simp only [xPrevIso, eqToIso_refl, Iso.refl_hom, Iso.refl_inv, comp_id, id_comp]

Depends on / 依赖: Iso.refl_hom, Iso.refl_inv, c.prev_eq, comp_id, eqToIso_refl, id_comp, prev_eq, refl_hom, refl_inv, xPrevIso
-/
theorem prev_eq (f : Hom C₁ C₂) {i j : ι} (w : c.Rel i j) :
    f.prev j = (C₁.xPrevIso w).hom ≫ f.f i ≫ (C₂.xPrevIso w).inv := by
  obtain rfl := c.prev_eq' w
  simp only [xPrevIso, eqToIso_refl, Iso.refl_hom, Iso.refl_inv, comp_id, id_comp]

/--
Definition of `next` / `next` 的定义

English:
abbreviation next
  signature: (f : Hom C₁ C₂) (i : ι)
  body: f.f _

中文:
缩写 next
  签名: (f : 态射 C₁ C₂) (i : ι)
  定义体: f.f _
-/
abbrev next (f : Hom C₁ C₂) (i : ι) : C₁.xNext i ⟶ C₂.xNext i :=
  f.f _

/--
theorem `next_eq` / 定理 `next_eq`

English:
theorem next_eq
  given: (f : Hom C₁ C₂) {i j : ι} (w : c.Rel i j)
  proof: by
  obtain rfl := c.next_eq' w
  simp only [xNextIso, eqToIso_refl, Iso.refl_hom, Iso.refl_inv, comp_id, id_comp]

@[reassoc, elementwise]

中文:
定理 next_eq
  条件: (f : 态射 C₁ C₂) {i j : ι} (w : c.关系 i j)
  证明: by
  obtain rfl := c.next_eq' w
  simp only [xNextIso, eqToIso_refl, Iso.refl_hom, Iso.refl_inv, comp_id, id_comp]

@[reassoc, elementwise]

Depends on / 依赖: Iso.refl_hom, Iso.refl_inv, c.next_eq, comp_id, eqToIso_refl, id_comp, next_eq, refl_hom, refl_inv, xNextIso
-/
theorem next_eq (f : Hom C₁ C₂) {i j : ι} (w : c.Rel i j) :
    f.next i = (C₁.xNextIso w).hom ≫ f.f j ≫ (C₂.xNextIso w).inv := by
  obtain rfl := c.next_eq' w
  simp only [xNextIso, eqToIso_refl, Iso.refl_hom, Iso.refl_inv, comp_id, id_comp]

@[reassoc, elementwise]
/--
theorem `comm_from` / 定理 `comm_from`

English:
theorem comm_from
  given: (f : Hom C₁ C₂) (i : ι)
  statement: f.f i ≫ C₂.dFrom i = C₁.dFrom i ≫ f.next i
  proof: f.comm _ _

中文:
定理 comm_from
  条件: (f : 态射 C₁ C₂) (i : ι)
  结论: f.f i ≫ C₂.dFrom i = C₁.dFrom i ≫ f.next i
  证明: f.comm _ _

Depends on / 依赖: f.comm
-/
theorem comm_from (f : Hom C₁ C₂) (i : ι) : f.f i ≫ C₂.dFrom i = C₁.dFrom i ≫ f.next i :=
  f.comm _ _

attribute [simp] comm_from_apply

@[reassoc, elementwise]
/--
theorem `comm_to` / 定理 `comm_to`

English:
theorem comm_to
  given: (f : Hom C₁ C₂) (j : ι)
  statement: f.prev j ≫ C₂.dTo j = C₁.dTo j ≫ f.f j
  proof: f.comm _ _

中文:
定理 comm_to
  条件: (f : 态射 C₁ C₂) (j : ι)
  结论: f.prev j ≫ C₂.dTo j = C₁.dTo j ≫ f.f j
  证明: f.comm _ _

Depends on / 依赖: f.comm
-/
theorem comm_to (f : Hom C₁ C₂) (j : ι) : f.prev j ≫ C₂.dTo j = C₁.dTo j ≫ f.f j :=
  f.comm _ _

attribute [simp] comm_to_apply

/--
Definition of `sqFrom` / `sqFrom` 的定义

English:
definition sqFrom
  signature: (f : Hom C₁ C₂) (i : ι)
  body: Arrow.homMk _ _ (f.comm_from i)

@[simp]

中文:
定义 sqFrom
  签名: (f : 态射 C₁ C₂) (i : ι)
  定义体: Arrow.homMk _ _ (f.comm_from i)

@[simp]

Depends on / 依赖: Arrow.homMk, comm_from, f.comm_from
-/
def sqFrom (f : Hom C₁ C₂) (i : ι) : Arrow.mk (C₁.dFrom i) ⟶ Arrow.mk (C₂.dFrom i) :=
  Arrow.homMk _ _ (f.comm_from i)

@[simp]
/--
theorem `sqFrom_left` / 定理 `sqFrom_left`

English:
theorem sqFrom_left
  given: (f : Hom C₁ C₂) (i : ι)
  statement: (f.sqFrom i).left = f.f i
  proof: rfl

@[simp]

中文:
定理 sqFrom_left
  条件: (f : 态射 C₁ C₂) (i : ι)
  结论: (f.sqFrom i).left = f.f i
  证明: rfl

@[simp]
-/
theorem sqFrom_left (f : Hom C₁ C₂) (i : ι) : (f.sqFrom i).left = f.f i :=
  rfl

@[simp]
/--
theorem `sqFrom_right` / 定理 `sqFrom_right`

English:
theorem sqFrom_right
  given: (f : Hom C₁ C₂) (i : ι)
  statement: (f.sqFrom i).right = f.next i
  proof: rfl

@[simp]

中文:
定理 sqFrom_right
  条件: (f : 态射 C₁ C₂) (i : ι)
  结论: (f.sqFrom i).right = f.next i
  证明: rfl

@[simp]
-/
theorem sqFrom_right (f : Hom C₁ C₂) (i : ι) : (f.sqFrom i).right = f.next i :=
  rfl

@[simp]
/--
theorem `sqFrom_id` / 定理 `sqFrom_id`

English:
theorem sqFrom_id
  given: (C₁ : HomologicalComplex V c) (i : ι)
  statement: sqFrom (𝟙 C₁) i = 𝟙 _
  proof: rfl

@[simp]

中文:
定理 sqFrom_id
  条件: (C₁ : 同调复形 V c) (i : ι)
  结论: sqFrom (𝟙 C₁) i = 𝟙 _
  证明: rfl

@[simp]
-/
theorem sqFrom_id (C₁ : HomologicalComplex V c) (i : ι) : sqFrom (𝟙 C₁) i = 𝟙 _ :=
  rfl

@[simp]
/--
theorem `sqFrom_comp` / 定理 `sqFrom_comp`

English:
theorem sqFrom_comp
  given: (f : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i : ι)
  proof: rfl

中文:
定理 sqFrom_comp
  条件: (f : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i : ι)
  证明: rfl
-/
theorem sqFrom_comp (f : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i : ι) :
    sqFrom (f ≫ g) i = sqFrom f i ≫ sqFrom g i :=
  rfl

/--
Definition of `sqTo` / `sqTo` 的定义

English:
definition sqTo
  signature: (f : Hom C₁ C₂) (j : ι)
  body: Arrow.homMk _ _ (f.comm_to j)

@[simp]

中文:
定义 sqTo
  签名: (f : 态射 C₁ C₂) (j : ι)
  定义体: Arrow.homMk _ _ (f.comm_to j)

@[simp]

Depends on / 依赖: Arrow.homMk, comm_to, f.comm_to
-/
def sqTo (f : Hom C₁ C₂) (j : ι) : Arrow.mk (C₁.dTo j) ⟶ Arrow.mk (C₂.dTo j) :=
  Arrow.homMk _ _ (f.comm_to j)

@[simp]
/--
theorem `sqTo_left` / 定理 `sqTo_left`

English:
theorem sqTo_left
  given: (f : Hom C₁ C₂) (j : ι)
  statement: (f.sqTo j).left = f.prev j
  proof: rfl

@[simp]

中文:
定理 sqTo_left
  条件: (f : 态射 C₁ C₂) (j : ι)
  结论: (f.sqTo j).left = f.prev j
  证明: rfl

@[simp]
-/
theorem sqTo_left (f : Hom C₁ C₂) (j : ι) : (f.sqTo j).left = f.prev j :=
  rfl

@[simp]
/--
theorem `sqTo_right` / 定理 `sqTo_right`

English:
theorem sqTo_right
  given: (f : Hom C₁ C₂) (j : ι)
  statement: (f.sqTo j).right = f.f j
  proof: rfl

中文:
定理 sqTo_right
  条件: (f : 态射 C₁ C₂) (j : ι)
  结论: (f.sqTo j).right = f.f j
  证明: rfl
-/
theorem sqTo_right (f : Hom C₁ C₂) (j : ι) : (f.sqTo j).right = f.f j :=
  rfl

instance (f : C₁ ⟶ C₂) [IsIso f] (j : ι) : IsIso (f.f j) :=
  inferInstanceAs (IsIso ((eval _ _ j).map f))

instance (f : C₁ ⟶ C₂) [IsSplitEpi f] (j : ι) : IsSplitEpi (f.f j) :=
  inferInstanceAs (IsSplitEpi ((eval _ _ j).map f))

instance (f : C₁ ⟶ C₂) [IsSplitMono f] (j : ι) : IsSplitMono (f.f j) :=
  inferInstanceAs (IsSplitMono ((eval _ _ j).map f))

@[push ←, simp]
/--
lemma `inv_f_apply` / 引理 `inv_f_apply`

English:
lemma inv_f_apply
  given: (f : C₁ ⟶ C₂) [IsIso f] (j : ι)
  statement: (inv f).f j = inv (f.f j)
  proof: by
  apply IsIso.eq_inv_of_inv_hom_id
  simp [← comp_f]

中文:
引理 inv_f_apply
  条件: (f : C₁ ⟶ C₂) [是同构 f] (j : ι)
  结论: (inv f).f j = inv (f.f j)
  证明: by
  apply IsIso.eq_inv_of_inv_hom_id
  simp [← comp_f]

Depends on / 依赖: IsIso.eq_inv_of_inv_hom_id, comp_f, eq_inv_of_inv_hom_id
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

/--
Definition of `of.d` / `of.d` 的定义

English:
definition of.d
  signature: (X : α -> V) (d : forall n, X (n + 1) ⟶ X n) (i : α) (j : α)
  body: if h : i = j + 1 then eqToHom (by rw [h]) ≫ d j else 0

中文:
定义 of.d
  签名: (X : α -> V) (d : 对任意 n, X (n + 1) ⟶ X n) (i : α) (j : α)
  定义体: if h : i = j + 1 then eqToHom (by rw [h]) ≫ d j else 0

Depends on / 依赖: eqToHom
-/
def of.d (X : α -> V) (d : forall n, X (n + 1) ⟶ X n) (i : α) (j : α) : X i ⟶ X j :=
  if h : i = j + 1 then eqToHom (by rw [h]) ≫ d j else 0

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: (X : α -> V) (d : forall n, X (n + 1) ⟶ X n) (sq : forall n, d (n + 1) ≫ d n = 0)
  body: { X := X
    d := of.d X d
    shape := fun i j w => by simp [of.d, (Ne.symm w)]
    d_comp_d' := fun i j k hij hjk => by
      dsimp [of.d] at hij hjk ⊢
      subst hij hjk
      simp only [eqToHom_refl, id_comp, dite_eq_ite, ite_true, sq] }

中文:
缩写 of
  签名: (X : α -> V) (d : 对任意 n, X (n + 1) ⟶ X n) (sq : 对任意 n, d (n + 1) ≫ d n = 0)
  定义体: { X := X
    d := of.d X d
    shape := fun i j w => by simp [of.d, (Ne.symm w)]
    d_comp_d' := fun i j k hij hjk => by
      dsimp [of.d] at hij hjk ⊢
      subst hij hjk
      simp only [eqToHom_refl, id_comp, dite_eq_ite, ite_true, sq] }

Depends on / 依赖: Ne.symm, d_comp_d, dite_eq_ite, eqToHom_refl, id_comp, ite_true, of.d
-/
abbrev of (X : α -> V) (d : forall n, X (n + 1) ⟶ X n) (sq : forall n, d (n + 1) ≫ d n = 0) :
    ChainComplex V α :=
  { X := X
    d := of.d X d
    shape := fun i j w => by simp [of.d, (Ne.symm w)]
    d_comp_d' := fun i j k hij hjk => by
      dsimp [of.d] at hij hjk ⊢
      subst hij hjk
      simp only [eqToHom_refl, id_comp, dite_eq_ite, ite_true, sq] }

variable (X : α -> V) (d : forall n, X (n + 1) ⟶ X n) (sq : forall n, d (n + 1) ≫ d n = 0)

/--
theorem `of_X` / 定理 `of_X`

English:
theorem of_X
  statement: (of X d sq).X = X
  proof: rfl

@[simp]

中文:
定理 of_X
  结论: (of X d sq).X = X
  证明: rfl

@[simp]
-/
theorem of_X : (of X d sq).X = X :=
  rfl

@[simp]
/--
theorem `of_d` / 定理 `of_d`

English:
theorem of_d
  given: (j : α)
  statement: of.d X d (j + 1) j = d j
  proof: by
  dsimp [of.d]
  rw [if_pos rfl]; rw [Category.id_comp]

中文:
定理 of_d
  条件: (j : α)
  结论: of.d X d (j + 1) j = d j
  证明: by
  dsimp [of.d]
  rw [if_pos rfl]; rw [Category.id_comp]

Depends on / 依赖: Category, Category.id_comp, id_comp, if_pos, of.d
-/
theorem of_d (j : α) : of.d X d (j + 1) j = d j := by
  dsimp [of.d]
  rw [if_pos rfl]; rw [Category.id_comp]

/--
theorem `of_d_ne` / 定理 `of_d_ne`

English:
theorem of_d_ne
  given: {i j : α} (h : i != j + 1)
  statement: of.d X d i j = 0
  proof: by
  simp [of.d, dif_neg h]

中文:
定理 of_d_ne
  条件: {i j : α} (h : i != j + 1)
  结论: of.d X d i j = 0
  证明: by
  simp [of.d, dif_neg h]

Depends on / 依赖: dif_neg, of.d
-/
theorem of_d_ne {i j : α} (h : i != j + 1) : of.d X d i j = 0 := by
  simp [of.d, dif_neg h]

end Of

section OfHom

variable {V} {α : Type*} [AddRightCancelSemigroup α] [One α] [DecidableEq α]
variable (X : α -> V) (d_X : forall n, X (n + 1) ⟶ X n) (sq_X : forall n, d_X (n + 1) ≫ d_X n = 0) (Y : α -> V)
  (d_Y : forall n, Y (n + 1) ⟶ Y n) (sq_Y : forall n, d_Y (n + 1) ≫ d_Y n = 0)

/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: {X Y : ChainComplex V α} (f : forall i : α, X.X i ⟶ Y.X i)
  body: f
  comm' n m := by
    simp only [ComplexShape.down_Rel]
    rintro rfl
    simpa using comm m

中文:
缩写 ofHom
  签名: {X Y : 链复形 V α} (f : 对任意 i : α, X.X i ⟶ Y.X i)
  定义体: f
  comm' n m := by
    simp only [ComplexShape.down_Rel]
    rintro rfl
    simpa using comm m
-/
abbrev ofHom {X Y : ChainComplex V α} (f : forall i : α, X.X i ⟶ Y.X i)
    (comm : forall i : α, f (i + 1) ≫ Y.d (i + 1) i = X.d (i + 1) i ≫ f i) :
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
  (succ : forall (S : ShortComplex V), Σ' (X₃ : V) (d₂ : X₃ ⟶ S.X₁), d₂ ≫ S.f = 0)

/--
Definition of `mkAux` / `mkAux` 的定义

English:
definition mkAux
  signature: : Nat -> ShortComplex V

中文:
定义 mkAux
  签名: : 自然数 -> 短复形 V
-/
def mkAux : Nat -> ShortComplex V
  | 0 => ShortComplex.mk _ _ s
  | n + 1 => ShortComplex.mk _ _ (succ (mkAux n)).2.2

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: : ChainComplex V Nat
  body: of (fun n => (mkAux X₀ X₁ X₂ d₀ d₁ s succ n).X₃) (fun n => (mkAux X₀ X₁ X₂ d₀ d₁ s succ n).g)
    fun n => (mkAux X₀ X₁ X₂ d₀ d₁ s succ n).zero

@[simp]

中文:
定义 mk
  签名: : 链复形 V 自然数
  定义体: of (fun n => (mkAux X₀ X₁ X₂ d₀ d₁ s succ n).X₃) (fun n => (mkAux X₀ X₁ X₂ d₀ d₁ s succ n).g)
    fun n => (mkAux X₀ X₁ X₂ d₀ d₁ s succ n).zero

@[simp]
-/
def mk : ChainComplex V Nat :=
  of (fun n => (mkAux X₀ X₁ X₂ d₀ d₁ s succ n).X₃) (fun n => (mkAux X₀ X₁ X₂ d₀ d₁ s succ n).g)
    fun n => (mkAux X₀ X₁ X₂ d₀ d₁ s succ n).zero

@[simp]
/--
theorem `mk_X_0` / 定理 `mk_X_0`

English:
theorem mk_X_0
  statement: (mk X₀ X₁ X₂ d₀ d₁ s succ).X 0 = X₀
  proof: rfl

@[simp]

中文:
定理 mk_X_0
  结论: (mk X₀ X₁ X₂ d₀ d₁ s succ).X 0 = X₀
  证明: rfl

@[simp]
-/
theorem mk_X_0 : (mk X₀ X₁ X₂ d₀ d₁ s succ).X 0 = X₀ :=
  rfl

@[simp]
/--
theorem `mk_X_1` / 定理 `mk_X_1`

English:
theorem mk_X_1
  statement: (mk X₀ X₁ X₂ d₀ d₁ s succ).X 1 = X₁
  proof: rfl

@[simp]

中文:
定理 mk_X_1
  结论: (mk X₀ X₁ X₂ d₀ d₁ s succ).X 1 = X₁
  证明: rfl

@[simp]

Depends on / 依赖: CochainComplex, CochainComplex.mappingCone.mapTrianglehIso, ComplexShape, ComplexShape.up, G.mapHomotopyCategory, mapHomotopyCategory, mapIso, mapTriangle, mapTriangle.mapIso, mapTrianglehIso, mappingCone
-/
theorem mk_X_1 : (mk X₀ X₁ X₂ d₀ d₁ s succ).X 1 = X₁ :=
  rfl

@[simp]
/--
theorem `mk_X_2` / 定理 `mk_X_2`

English:
theorem mk_X_2
  statement: (mk X₀ X₁ X₂ d₀ d₁ s succ).X 2 = X₂
  proof: rfl

@[simp]

中文:
定理 mk_X_2
  结论: (mk X₀ X₁ X₂ d₀ d₁ s succ).X 2 = X₂
  证明: rfl

@[simp]
-/
theorem mk_X_2 : (mk X₀ X₁ X₂ d₀ d₁ s succ).X 2 = X₂ :=
  rfl

@[simp]
/--
theorem `mk_d_1_0` / 定理 `mk_d_1_0`

English:
theorem mk_d_1_0
  statement: (mk X₀ X₁ X₂ d₀ d₁ s succ).d 1 0 = d₀
  proof: by
  change ite (1 = 0 + 1) (𝟙 X₁ ≫ d₀) 0 = d₀
  rw [if_pos rfl]; rw [Category.id_comp]

@[simp]

中文:
定理 mk_d_1_0
  结论: (mk X₀ X₁ X₂ d₀ d₁ s succ).d 1 0 = d₀
  证明: by
  change ite (1 = 0 + 1) (𝟙 X₁ ≫ d₀) 0 = d₀
  rw [if_pos rfl]; rw [Category.id_comp]

@[simp]

Depends on / 依赖: Category, Category.id_comp, id_comp, if_pos
-/
theorem mk_d_1_0 : (mk X₀ X₁ X₂ d₀ d₁ s succ).d 1 0 = d₀ := by
  change ite (1 = 0 + 1) (𝟙 X₁ ≫ d₀) 0 = d₀
  rw [if_pos rfl]; rw [Category.id_comp]

@[simp]
/--
theorem `mk_d_2_1` / 定理 `mk_d_2_1`

English:
theorem mk_d_2_1
  statement: (mk X₀ X₁ X₂ d₀ d₁ s succ).d 2 1 = d₁
  proof: by
  change ite (2 = 1 + 1) (𝟙 X₂ ≫ d₁) 0 = d₁
  rw [if_pos rfl]; rw [Category.id_comp]

中文:
定理 mk_d_2_1
  结论: (mk X₀ X₁ X₂ d₀ d₁ s succ).d 2 1 = d₁
  证明: by
  change ite (2 = 1 + 1) (𝟙 X₂ ≫ d₁) 0 = d₁
  rw [if_pos rfl]; rw [Category.id_comp]

Depends on / 依赖: Category, Category.id_comp, id_comp, if_pos
-/
theorem mk_d_2_1 : (mk X₀ X₁ X₂ d₀ d₁ s succ).d 2 1 = d₁ := by
  change ite (2 = 1 + 1) (𝟙 X₂ ≫ d₁) 0 = d₁
  rw [if_pos rfl]; rw [Category.id_comp]

/--
lemma `mk_congr_succ_X₃` / 引理 `mk_congr_succ_X₃`

English:
lemma mk_congr_succ_X₃
  given: {S S' : ShortComplex V} (h : S = S')
  proof: by rw [h]

中文:
引理 mk_congr_succ_X₃
  条件: {S S' : 短复形 V} (h : S = S')
  证明: by rw [h]
-/
lemma mk_congr_succ_X₃ {S S' : ShortComplex V} (h : S = S') :
    (succ S).1 = (succ S').1 := by rw [h]

/--
lemma `mk_congr_succ_d₂` / 引理 `mk_congr_succ_d₂`

English:
lemma mk_congr_succ_d₂
  given: {S S' : ShortComplex V} (h : S = S')
  proof: by
  subst h
  simp

中文:
引理 mk_congr_succ_d₂
  条件: {S S' : 短复形 V} (h : S = S')
  证明: by
  subst h
  simp
-/
lemma mk_congr_succ_d₂ {S S' : ShortComplex V} (h : S = S') :
    (succ S).2.1 = eqToHom (by subst h; rfl) ≫ (succ S').2.1 ≫ eqToHom (by subst h; rfl) := by
  subst h
  simp

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `mkAux_eq_shortComplex_mk_d_comp_d` / 引理 `mkAux_eq_shortComplex_mk_d_comp_d`

English:
lemma mkAux_eq_shortComplex_mk_d_comp_d
  given: (n : Nat)
  proof: by
  rw [show n + 2 = n + 1 + 1 from rfl]
  simp [mk, mkAux]

中文:
引理 mkAux_eq_shortComplex_mk_d_comp_d
  条件: (n : 自然数)
  证明: by
  rw [show n + 2 = n + 1 + 1 from rfl]
  simp [mk, mkAux]

Depends on / 依赖: Additive, CochainComplex, CochainComplex.shiftFunctor, shiftFunctor
-/
lemma mkAux_eq_shortComplex_mk_d_comp_d (n : Nat) :
    mkAux X₀ X₁ X₂ d₀ d₁ s succ n =
      ShortComplex.mk _ _ ((mk X₀ X₁ X₂ d₀ d₁ s succ).d_comp_d (n + 2) (n + 1) n) := by
  rw [show n + 2 = n + 1 + 1 from rfl]
  simp [mk, mkAux]

/--
Definition of `mkXIso` / `mkXIso` 的定义

English:
definition mkXIso
  signature: (n : Nat)
  body: eqToIso (by
    rw [← mk_congr_succ_X₃ succ
      (mkAux_eq_shortComplex_mk_d_comp_d X₀ X₁ X₂ d₀ d₁ s succ n)]
    rfl)

中文:
定义 mkXIso
  签名: (n : 自然数)
  定义体: eqToIso (by
    rw [← mk_congr_succ_X₃ succ
      (mkAux_eq_shortComplex_mk_d_comp_d X₀ X₁ X₂ d₀ d₁ s succ n)]
    rfl)

Depends on / 依赖: eqToIso, mkAux_eq_shortComplex_mk_d_comp_d
-/
def mkXIso (n : Nat) :
    (mk X₀ X₁ X₂ d₀ d₁ s succ).X (n + 3) ≅
      (succ (ShortComplex.mk _ _ ((mk X₀ X₁ X₂ d₀ d₁ s succ).d_comp_d (n + 2) (n + 1) n))).1 :=
  eqToIso (by
    rw [← mk_congr_succ_X₃ succ
      (mkAux_eq_shortComplex_mk_d_comp_d X₀ X₁ X₂ d₀ d₁ s succ n)]
    rfl)

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `mk_d` / 引理 `mk_d`

English:
lemma mk_d
  given: (n : Nat)
  proof: by
  have eq := mk_congr_succ_d₂ succ
    (mkAux_eq_shortComplex_mk_d_comp_d X₀ X₁ X₂ d₀ d₁ s succ n)
  set_option backward.isDefEq.respectTransparency false in
    rw [eqToHom_refl]; rw [comp_id] at eq
  refine Eq.trans ?_ eq
  dsimp only [mk, of, of.d]
  rw [dif_pos (by rfl)]; rw [eqToHom_refl]; rw [id_comp]
  rfl

中文:
引理 mk_d
  条件: (n : 自然数)
  证明: by
  have eq := mk_congr_succ_d₂ succ
    (mkAux_eq_shortComplex_mk_d_comp_d X₀ X₁ X₂ d₀ d₁ s succ n)
  set_option backward.isDefEq.respectTransparency false in
    rw [eqToHom_refl]; rw [comp_id] at eq
  refine Eq.trans ?_ eq
  dsimp only [mk, of, of.d]
  rw [dif_pos (by rfl)]; rw [eqToHom_refl]; rw [id_comp]
  rfl

Depends on / 依赖: Eq.trans, backward, backward.isDefEq.respectTransparency, comp_id, dif_pos, eqToHom_refl, id_comp, isDefEq, mkAux_eq_shortComplex_mk_d_comp_d, of.d, respectTransparency, set_option
-/
lemma mk_d (n : Nat) :
    (mk X₀ X₁ X₂ d₀ d₁ s succ).d (n + 3) (n + 2) =
      (mkXIso X₀ X₁ X₂ d₀ d₁ s succ n).hom ≫ (succ
        (ShortComplex.mk _ _ ((mk X₀ X₁ X₂ d₀ d₁ s succ).d_comp_d (n + 2) (n + 1) n))).2.1 := by
  have eq := mk_congr_succ_d₂ succ
    (mkAux_eq_shortComplex_mk_d_comp_d X₀ X₁ X₂ d₀ d₁ s succ n)
  set_option backward.isDefEq.respectTransparency false in
    rw [eqToHom_refl]; rw [comp_id] at eq
  refine Eq.trans ?_ eq
  dsimp only [mk, of, of.d]
  rw [dif_pos (by rfl)]; rw [eqToHom_refl]; rw [id_comp]
  rfl

/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: (X₀ X₁ : V) (d : X₁ ⟶ X₀)
  body: mk _ _ _ _ _ (succ' d).2.2 (fun S => succ' S.f)

中文:
定义 mk'
  签名: (X₀ X₁ : V) (d : X₁ ⟶ X₀)
  定义体: mk _ _ _ _ _ (succ' d).2.2 (fun S => succ' S.f)
-/
def mk' (X₀ X₁ : V) (d : X₁ ⟶ X₀)
    (succ' : forall {X₀ X₁ : V} (f : X₁ ⟶ X₀), Σ' (X₂ : V) (d : X₂ ⟶ X₁), d ≫ f = 0) :
    ChainComplex V Nat :=
  mk _ _ _ _ _ (succ' d).2.2 (fun S => succ' S.f)

variable (succ' : forall {X₀ X₁ : V} (f : X₁ ⟶ X₀), Σ' (X₂ : V) (d : X₂ ⟶ X₁), d ≫ f = 0)

@[simp]
/--
theorem `mk'_X_0` / 定理 `mk'_X_0`

English:
theorem mk'_X_0
  statement: (mk' X₀ X₁ d₀ succ').X 0 = X₀
  proof: rfl

@[simp]

中文:
定理 mk'_X_0
  结论: (mk' X₀ X₁ d₀ succ').X 0 = X₀
  证明: rfl

@[simp]
-/
theorem mk'_X_0 : (mk' X₀ X₁ d₀ succ').X 0 = X₀ :=
  rfl

@[simp]
/--
theorem `mk'_X_1` / 定理 `mk'_X_1`

English:
theorem mk'_X_1
  statement: (mk' X₀ X₁ d₀ succ').X 1 = X₁
  proof: rfl


@[simp]

中文:
定理 mk'_X_1
  结论: (mk' X₀ X₁ d₀ succ').X 1 = X₁
  证明: rfl


@[simp]
-/
theorem mk'_X_1 : (mk' X₀ X₁ d₀ succ').X 1 = X₁ :=
  rfl


@[simp]
/--
theorem `mk'_d_1_0` / 定理 `mk'_d_1_0`

English:
theorem mk'_d_1_0
  statement: (mk' X₀ X₁ d₀ succ').d 1 0 = d₀
  proof: by
  change ite (1 = 0 + 1) (𝟙 X₁ ≫ d₀) 0 = d₀
  rw [if_pos rfl]; rw [Category.id_comp]

中文:
定理 mk'_d_1_0
  结论: (mk' X₀ X₁ d₀ succ').d 1 0 = d₀
  证明: by
  change ite (1 = 0 + 1) (𝟙 X₁ ≫ d₀) 0 = d₀
  rw [if_pos rfl]; rw [Category.id_comp]

Depends on / 依赖: _eq_shiftFunctorAdd, shiftFunctorAdd, shiftFunctorAdd_inv_app_f
-/
theorem mk'_d_1_0 : (mk' X₀ X₁ d₀ succ').d 1 0 = d₀ := by
  change ite (1 = 0 + 1) (𝟙 X₁ ≫ d₀) 0 = d₀
  rw [if_pos rfl]; rw [Category.id_comp]

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `mk'XIso` / `mk'XIso` 的定义

English:
definition mk'XIso
  signature: (n : Nat)
  body: by
  obtain _ | n := n
  · apply eqToIso
    dsimp [mk', mk, of, mkAux, of.d]
    rw [id_comp]
  · exact mkXIso _ _ _ _ _ (succ' d₀).2.2 (fun S => succ' S.f) n

中文:
定义 mk'XIso
  签名: (n : 自然数)
  定义体: by
  obtain _ | n := n
  · apply eqToIso
    dsimp [mk', mk, of, mkAux, of.d]
    rw [id_comp]
  · exact mkXIso _ _ _ _ _ (succ' d₀).2.2 (fun S => succ' S.f) n

Depends on / 依赖: _eq_shiftFunctorAdd, shiftFunctorAdd, shiftFunctorAdd_hom_app_f
-/
def mk'XIso (n : Nat) :
    (mk' X₀ X₁ d₀ succ').X (n + 2) ≅ (succ' ((mk' X₀ X₁ d₀ succ').d (n + 1) n)).1 := by
  obtain _ | n := n
  · apply eqToIso
    dsimp [mk', mk, of, mkAux, of.d]
    rw [id_comp]
  · exact mkXIso _ _ _ _ _ (succ' d₀).2.2 (fun S => succ' S.f) n

/--
lemma `mk'_congr_succ'_d` / 引理 `mk'_congr_succ'_d`

English:
lemma mk'_congr_succ'_d
  given: {X Y : V} (f g : X ⟶ Y) (h : f = g)
  proof: by
  subst h
  simp

中文:
引理 mk'_congr_succ'_d
  条件: {X Y : V} (f g : X ⟶ Y) (h : f = g)
  证明: by
  subst h
  simp
-/
lemma mk'_congr_succ'_d {X Y : V} (f g : X ⟶ Y) (h : f = g) :
    (succ' f).2.1 = eqToHom (by rw [h]) ≫ (succ' g).2.1 := by
  subst h
  simp

/--
lemma `mk'_d` / 引理 `mk'_d`

English:
lemma mk'_d
  given: (n : Nat)
  proof: by
  obtain _ | n := n
  · dsimp [mk'XIso, mk']
    rw [mk_d_2_1]
    apply mk'_congr_succ'_d
    rw [mk_d_1_0]
  · apply mk_d

中文:
引理 mk'_d
  条件: (n : 自然数)
  证明: by
  obtain _ | n := n
  · dsimp [mk'XIso, mk']
    rw [mk_d_2_1]
    apply mk'_congr_succ'_d
    rw [mk_d_1_0]
  · apply mk_d
-/
lemma mk'_d (n : Nat) :
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
variable (P Q : ChainComplex V Nat) (zero : P.X 0 ⟶ Q.X 0) (one : P.X 1 ⟶ Q.X 1)
  (one_zero_comm : one ≫ Q.d 1 0 = P.d 1 0 ≫ zero)
  (succ :
    forall (n : Nat)
      (p :
        Σ' (f : P.X n ⟶ Q.X n) (f' : P.X (n + 1) ⟶ Q.X (n + 1)),
          f' ≫ Q.d (n + 1) n = P.d (n + 1) n ≫ f),
      Σ' f'' : P.X (n + 2) ⟶ Q.X (n + 2), f'' ≫ Q.d (n + 2) (n + 1) = P.d (n + 2) (n + 1) ≫ p.2.1)

/--
Definition of `mkHomAux` / `mkHomAux` 的定义

English:
definition mkHomAux
  signature: :

中文:
定义 mkHomAux
  签名: :
-/
def mkHomAux :
    forall n,
      Σ' (f : P.X n ⟶ Q.X n) (f' : P.X (n + 1) ⟶ Q.X (n + 1)),
        f' ≫ Q.d (n + 1) n = P.d (n + 1) n ≫ f
  | 0 => ⟨zero, one, one_zero_comm⟩
  | n + 1 => ⟨(mkHomAux n).2.1, (succ n (mkHomAux n)).1, (succ n (mkHomAux n)).2⟩

/--
Definition of `mkHom` / `mkHom` 的定义

English:
definition mkHom
  signature: : P ⟶ Q where
  body: (mkHomAux P Q zero one one_zero_comm succ n).1
  comm' n m := by
    rintro (rfl : m + 1 = n)
    exact (mkHomAux P Q zero one one_zero_comm succ m).2.2

@[simp]

中文:
定义 mkHom
  签名: : P ⟶ Q where
  定义体: (mkHomAux P Q zero one one_zero_comm succ n).1
  comm' n m := by
    rintro (rfl : m + 1 = n)
    exact (mkHomAux P Q zero one one_zero_comm succ m).2.2

@[simp]

Depends on / 依赖: XIsoOfEq, _hom_app_f, eqToIso, eqToIso.hom, mkHomAux, one_zero_comm, shiftFunctorAdd
-/
def mkHom : P ⟶ Q where
  f n := (mkHomAux P Q zero one one_zero_comm succ n).1
  comm' n m := by
    rintro (rfl : m + 1 = n)
    exact (mkHomAux P Q zero one one_zero_comm succ m).2.2

@[simp]
/--
theorem `mkHom_f_0` / 定理 `mkHom_f_0`

English:
theorem mkHom_f_0
  statement: (mkHom P Q zero one one_zero_comm succ).f 0 = zero
  proof: rfl

@[simp]

中文:
定理 mkHom_f_0
  结论: (mkHom P Q zero one one_zero_comm succ).f 0 = zero
  证明: rfl

@[simp]
-/
theorem mkHom_f_0 : (mkHom P Q zero one one_zero_comm succ).f 0 = zero :=
  rfl

@[simp]
/--
theorem `mkHom_f_1` / 定理 `mkHom_f_1`

English:
theorem mkHom_f_1
  statement: (mkHom P Q zero one one_zero_comm succ).f 1 = one
  proof: rfl

@[simp]

中文:
定理 mkHom_f_1
  结论: (mkHom P Q zero one one_zero_comm succ).f 1 = one
  证明: rfl

@[simp]
-/
theorem mkHom_f_1 : (mkHom P Q zero one one_zero_comm succ).f 1 = one :=
  rfl

@[simp]
/--
theorem `mkHom_f_succ_succ` / 定理 `mkHom_f_succ_succ`

English:
theorem mkHom_f_succ_succ
  given: (n : Nat)
  proof: by
  dsimp [mkHom, mkHomAux]

中文:
定理 mkHom_f_succ_succ
  条件: (n : 自然数)
  证明: by
  dsimp [mkHom, mkHomAux]

Depends on / 依赖: mkHomAux
-/
theorem mkHom_f_succ_succ (n : Nat) :
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

/--
Definition of `of.d` / `of.d` 的定义

English:
definition of.d
  signature: (X : α -> V) (d : forall n, X n ⟶ X (n + 1)) (i : α) (j : α)
  body: if h : i + 1 = j then d _ ≫ eqToHom (by rw [h]) else 0

中文:
定义 of.d
  签名: (X : α -> V) (d : 对任意 n, X n ⟶ X (n + 1)) (i : α) (j : α)
  定义体: if h : i + 1 = j then d _ ≫ eqToHom (by rw [h]) else 0
-/
def of.d (X : α -> V) (d : forall n, X n ⟶ X (n + 1)) (i : α) (j : α) : X i ⟶ X j :=
  if h : i + 1 = j then d _ ≫ eqToHom (by rw [h]) else 0

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: (X : α -> V) (d : forall n, X n ⟶ X (n + 1)) (sq : forall n, d n ≫ d (n + 1) = 0)
  body: { X := X
    d := of.d X d
    shape := fun i j w => dif_neg (c := i + 1 = j) w
    d_comp_d' := fun i j k => by
      dsimp [of.d]
      split_ifs with h h' h'
      · subst h h'
        simp [sq]
      all_goals simp }

中文:
缩写 of
  签名: (X : α -> V) (d : 对任意 n, X n ⟶ X (n + 1)) (sq : 对任意 n, d n ≫ d (n + 1) = 0)
  定义体: { X := X
    d := of.d X d
    shape := fun i j w => dif_neg (c := i + 1 = j) w
    d_comp_d' := fun i j k => by
      dsimp [of.d]
      split_ifs with h h' h'
      · subst h h'
        simp [sq]
      all_goals simp }

Depends on / 依赖: all_goals, d_comp_d, dif_neg, of.d, split_ifs
-/
abbrev of (X : α -> V) (d : forall n, X n ⟶ X (n + 1)) (sq : forall n, d n ≫ d (n + 1) = 0) :
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

variable (X : α -> V) (d : forall n, X n ⟶ X (n + 1)) (sq : forall n, d n ≫ d (n + 1) = 0)

/--
theorem `of_X` / 定理 `of_X`

English:
theorem of_X
  statement: (of X d sq).X = X
  proof: rfl

@[simp]

中文:
定理 of_X
  结论: (of X d sq).X = X
  证明: rfl

@[simp]
-/
theorem of_X : (of X d sq).X = X :=
  rfl

@[simp]
/--
theorem `of_d` / 定理 `of_d`

English:
theorem of_d
  given: (j : α)
  statement: of.d X d j (j + 1) = d j
  proof: by
  dsimp [of.d]
  rw [if_pos rfl]; rw [Category.comp_id]

中文:
定理 of_d
  条件: (j : α)
  结论: of.d X d j (j + 1) = d j
  证明: by
  dsimp [of.d]
  rw [if_pos rfl]; rw [Category.comp_id]

Depends on / 依赖: Category, Category.comp_id, comp_id, if_pos, of.d
-/
theorem of_d (j : α) : of.d X d j (j + 1) = d j := by
  dsimp [of.d]
  rw [if_pos rfl]; rw [Category.comp_id]

/--
theorem `of_d_ne` / 定理 `of_d_ne`

English:
theorem of_d_ne
  given: {i j : α} (h : i + 1 != j)
  statement: of.d X d i j = 0
  proof: by
  simp [of.d, dif_neg h]

中文:
定理 of_d_ne
  条件: {i j : α} (h : i + 1 != j)
  结论: of.d X d i j = 0
  证明: by
  simp [of.d, dif_neg h]

Depends on / 依赖: dif_neg, of.d
-/
theorem of_d_ne {i j : α} (h : i + 1 != j) : of.d X d i j = 0 := by
  simp [of.d, dif_neg h]

end Of

section OfHom

variable {V} {α : Type*} [AddRightCancelSemigroup α] [One α] [DecidableEq α]
variable (X : α -> V) (d_X : forall n, X n ⟶ X (n + 1)) (sq_X : forall n, d_X n ≫ d_X (n + 1) = 0) (Y : α -> V)
  (d_Y : forall n, Y n ⟶ Y (n + 1)) (sq_Y : forall n, d_Y n ≫ d_Y (n + 1) = 0)

/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: {X Y : CochainComplex V α} (f : forall i : α, X.X i ⟶ Y.X i)
  body: f
  comm' n m := by
    simp only [ComplexShape.up_Rel]
    rintro rfl
    simpa using comm n

中文:
缩写 ofHom
  签名: {X Y : 上链复形 V α} (f : 对任意 i : α, X.X i ⟶ Y.X i)
  定义体: f
  comm' n m := by
    simp only [ComplexShape.up_Rel]
    rintro rfl
    simpa using comm n
-/
abbrev ofHom {X Y : CochainComplex V α} (f : forall i : α, X.X i ⟶ Y.X i)
    (comm : forall i : α, f i ≫ Y.d i (i + 1) = X.d i (i + 1) ≫ f (i + 1)) :
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
  (succ : forall (S : ShortComplex V), Σ' (X₄ : V) (d₂ : S.X₃ ⟶ X₄), S.g ≫ d₂ = 0)

/--
Definition of `mkAux` / `mkAux` 的定义

English:
definition mkAux
  signature: : Nat -> ShortComplex V

中文:
定义 mkAux
  签名: : 自然数 -> 短复形 V
-/
def mkAux : Nat -> ShortComplex V
  | 0 => ShortComplex.mk _ _ s
  | n + 1 => ShortComplex.mk _ _ (succ (mkAux n)).2.2

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: : CochainComplex V Nat
  body: of (fun n => (mkAux X₀ X₁ X₂ d₀ d₁ s succ n).X₁) (fun n => (mkAux X₀ X₁ X₂ d₀ d₁ s succ n).f)
    fun n => (mkAux X₀ X₁ X₂ d₀ d₁ s succ n).zero

@[simp]

中文:
定义 mk
  签名: : 上链复形 V 自然数
  定义体: of (fun n => (mkAux X₀ X₁ X₂ d₀ d₁ s succ n).X₁) (fun n => (mkAux X₀ X₁ X₂ d₀ d₁ s succ n).f)
    fun n => (mkAux X₀ X₁ X₂ d₀ d₁ s succ n).zero

@[simp]
-/
def mk : CochainComplex V Nat :=
  of (fun n => (mkAux X₀ X₁ X₂ d₀ d₁ s succ n).X₁) (fun n => (mkAux X₀ X₁ X₂ d₀ d₁ s succ n).f)
    fun n => (mkAux X₀ X₁ X₂ d₀ d₁ s succ n).zero

@[simp]
/--
theorem `mk_X_0` / 定理 `mk_X_0`

English:
theorem mk_X_0
  statement: (mk X₀ X₁ X₂ d₀ d₁ s succ).X 0 = X₀
  proof: rfl

@[simp]

中文:
定理 mk_X_0
  结论: (mk X₀ X₁ X₂ d₀ d₁ s succ).X 0 = X₀
  证明: rfl

@[simp]
-/
theorem mk_X_0 : (mk X₀ X₁ X₂ d₀ d₁ s succ).X 0 = X₀ :=
  rfl

@[simp]
/--
theorem `mk_X_1` / 定理 `mk_X_1`

English:
theorem mk_X_1
  statement: (mk X₀ X₁ X₂ d₀ d₁ s succ).X 1 = X₁
  proof: rfl

@[simp]

中文:
定理 mk_X_1
  结论: (mk X₀ X₁ X₂ d₀ d₁ s succ).X 1 = X₁
  证明: rfl

@[simp]
-/
theorem mk_X_1 : (mk X₀ X₁ X₂ d₀ d₁ s succ).X 1 = X₁ :=
  rfl

@[simp]
/--
theorem `mk_X_2` / 定理 `mk_X_2`

English:
theorem mk_X_2
  statement: (mk X₀ X₁ X₂ d₀ d₁ s succ).X 2 = X₂
  proof: rfl

@[simp]

中文:
定理 mk_X_2
  结论: (mk X₀ X₁ X₂ d₀ d₁ s succ).X 2 = X₂
  证明: rfl

@[simp]
-/
theorem mk_X_2 : (mk X₀ X₁ X₂ d₀ d₁ s succ).X 2 = X₂ :=
  rfl

@[simp]
/--
theorem `mk_d_1_0` / 定理 `mk_d_1_0`

English:
theorem mk_d_1_0
  statement: (mk X₀ X₁ X₂ d₀ d₁ s succ).d 0 1 = d₀
  proof: by
  change ite (1 = 0 + 1) (d₀ ≫ 𝟙 X₁) 0 = d₀
  rw [if_pos rfl]; rw [Category.comp_id]

@[simp]

中文:
定理 mk_d_1_0
  结论: (mk X₀ X₁ X₂ d₀ d₁ s succ).d 0 1 = d₀
  证明: by
  change ite (1 = 0 + 1) (d₀ ≫ 𝟙 X₁) 0 = d₀
  rw [if_pos rfl]; rw [Category.comp_id]

@[simp]

Depends on / 依赖: Additive, Category, Category.comp_id, ComplexShape, ComplexShape.up, Functor, Functor.additive_of_full_essSurj_comp, Functor.additive_of_iso, additive_of_full_essSurj_comp, additive_of_iso, commShiftIso, comp_id, if_pos, quotient, shiftFunctor
-/
theorem mk_d_1_0 : (mk X₀ X₁ X₂ d₀ d₁ s succ).d 0 1 = d₀ := by
  change ite (1 = 0 + 1) (d₀ ≫ 𝟙 X₁) 0 = d₀
  rw [if_pos rfl]; rw [Category.comp_id]

@[simp]
/--
theorem `mk_d_2_0` / 定理 `mk_d_2_0`

English:
theorem mk_d_2_0
  statement: (mk X₀ X₁ X₂ d₀ d₁ s succ).d 1 2 = d₁
  proof: by
  change ite (2 = 1 + 1) (d₁ ≫ 𝟙 X₂) 0 = d₁
  rw [if_pos rfl]; rw [Category.comp_id]

中文:
定理 mk_d_2_0
  结论: (mk X₀ X₁ X₂ d₀ d₁ s succ).d 1 2 = d₁
  证明: by
  change ite (2 = 1 + 1) (d₁ ≫ 𝟙 X₂) 0 = d₁
  rw [if_pos rfl]; rw [Category.comp_id]

Depends on / 依赖: Category, Category.comp_id, ComplexShape, ComplexShape.up, Functor, Functor.map_smul, HomotopyCategory, HomotopyCategory.quotient, NatIso, NatIso.naturality_1, commShiftIso, comp_id, if_pos, map_smul, map_surjective, naturality_1, quotient
-/
theorem mk_d_2_0 : (mk X₀ X₁ X₂ d₀ d₁ s succ).d 1 2 = d₁ := by
  change ite (2 = 1 + 1) (d₁ ≫ 𝟙 X₂) 0 = d₁
  rw [if_pos rfl]; rw [Category.comp_id]

-- TODO simp lemmas for the inductive steps? It's not entirely clear that they are needed.
/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: (X₀ X₁ : V) (d : X₀ ⟶ X₁)
  body: mk _ _ _ _ _ (succ' d).2.2 (fun S => succ' S.g)

中文:
定义 mk'
  签名: (X₀ X₁ : V) (d : X₀ ⟶ X₁)
  定义体: mk _ _ _ _ _ (succ' d).2.2 (fun S => succ' S.g)
-/
def mk' (X₀ X₁ : V) (d : X₀ ⟶ X₁)
    -- (succ' : ∀ : Σ X₀ X₁ : V, X₀ ⟶ X₁, Σ' (X₂ : V) (d : t.2.1 ⟶ X₂), t.2.2 ≫ d = 0) :
    (succ' : forall {X₀ X₁ : V} (f : X₀ ⟶ X₁), Σ' (X₂ : V) (d : X₁ ⟶ X₂), f ≫ d = 0) :
    CochainComplex V Nat :=
  mk _ _ _ _ _ (succ' d).2.2 (fun S => succ' S.g)

variable (succ' : forall {X₀ X₁ : V} (f : X₀ ⟶ X₁), Σ' (X₂ : V) (d : X₁ ⟶ X₂), f ≫ d = 0)

@[simp]
/--
theorem `mk'_X_0` / 定理 `mk'_X_0`

English:
theorem mk'_X_0
  statement: (mk' X₀ X₁ d₀ succ').X 0 = X₀
  proof: rfl

@[simp]

中文:
定理 mk'_X_0
  结论: (mk' X₀ X₁ d₀ succ').X 0 = X₀
  证明: rfl

@[simp]
-/
theorem mk'_X_0 : (mk' X₀ X₁ d₀ succ').X 0 = X₀ :=
  rfl

@[simp]
/--
theorem `mk'_X_1` / 定理 `mk'_X_1`

English:
theorem mk'_X_1
  statement: (mk' X₀ X₁ d₀ succ').X 1 = X₁
  proof: rfl

@[simp]

中文:
定理 mk'_X_1
  结论: (mk' X₀ X₁ d₀ succ').X 1 = X₁
  证明: rfl

@[simp]
-/
theorem mk'_X_1 : (mk' X₀ X₁ d₀ succ').X 1 = X₁ :=
  rfl

@[simp]
/--
theorem `mk'_d_1_0` / 定理 `mk'_d_1_0`

English:
theorem mk'_d_1_0
  statement: (mk' X₀ X₁ d₀ succ').d 0 1 = d₀
  proof: by
  change ite (1 = 0 + 1) (d₀ ≫ 𝟙 X₁) 0 = d₀
  rw [if_pos rfl]; rw [Category.comp_id]

中文:
定理 mk'_d_1_0
  结论: (mk' X₀ X₁ d₀ succ').d 0 1 = d₀
  证明: by
  change ite (1 = 0 + 1) (d₀ ≫ 𝟙 X₁) 0 = d₀
  rw [if_pos rfl]; rw [Category.comp_id]
-/
theorem mk'_d_1_0 : (mk' X₀ X₁ d₀ succ').d 0 1 = d₀ := by
  change ite (1 = 0 + 1) (d₀ ≫ 𝟙 X₁) 0 = d₀
  rw [if_pos rfl]; rw [Category.comp_id]

-- TODO simp lemmas for the inductive steps? It's not entirely clear that they are needed.
end Mk

section MkHom

variable {V}
variable (P Q : CochainComplex V Nat) (zero : P.X 0 ⟶ Q.X 0) (one : P.X 1 ⟶ Q.X 1)
  (one_zero_comm : zero ≫ Q.d 0 1 = P.d 0 1 ≫ one)
  (succ : forall (n : Nat) (p : Σ' (f : P.X n ⟶ Q.X n) (f' : P.X (n + 1) ⟶ Q.X (n + 1)),
          f ≫ Q.d n (n + 1) = P.d n (n + 1) ≫ f'),
      Σ' f'' : P.X (n + 2) ⟶ Q.X (n + 2), p.2.1 ≫ Q.d (n + 1) (n + 2) = P.d (n + 1) (n + 2) ≫ f'')

/--
Definition of `mkHomAux` / `mkHomAux` 的定义

English:
definition mkHomAux
  signature: :

中文:
定义 mkHomAux
  签名: :
-/
def mkHomAux :
    forall n,
      Σ' (f : P.X n ⟶ Q.X n) (f' : P.X (n + 1) ⟶ Q.X (n + 1)),
        f ≫ Q.d n (n + 1) = P.d n (n + 1) ≫ f'
  | 0 => ⟨zero, one, one_zero_comm⟩
  | n + 1 => ⟨(mkHomAux n).2.1, (succ n (mkHomAux n)).1, (succ n (mkHomAux n)).2⟩

/--
Definition of `mkHom` / `mkHom` 的定义

English:
definition mkHom
  signature: : P ⟶ Q where
  body: (mkHomAux P Q zero one one_zero_comm succ n).1
  comm' n m := by
    rintro (rfl : n + 1 = m)
    exact (mkHomAux P Q zero one one_zero_comm succ n).2.2

@[simp]

中文:
定义 mkHom
  签名: : P ⟶ Q where
  定义体: (mkHomAux P Q zero one one_zero_comm succ n).1
  comm' n m := by
    rintro (rfl : n + 1 = m)
    exact (mkHomAux P Q zero one one_zero_comm succ n).2.2

@[simp]

Depends on / 依赖: mkHomAux, one_zero_comm
-/
def mkHom : P ⟶ Q where
  f n := (mkHomAux P Q zero one one_zero_comm succ n).1
  comm' n m := by
    rintro (rfl : n + 1 = m)
    exact (mkHomAux P Q zero one one_zero_comm succ n).2.2

@[simp]
/--
theorem `mkHom_f_0` / 定理 `mkHom_f_0`

English:
theorem mkHom_f_0
  statement: (mkHom P Q zero one one_zero_comm succ).f 0 = zero
  proof: rfl

@[simp]

中文:
定理 mkHom_f_0
  结论: (mkHom P Q zero one one_zero_comm succ).f 0 = zero
  证明: rfl

@[simp]
-/
theorem mkHom_f_0 : (mkHom P Q zero one one_zero_comm succ).f 0 = zero :=
  rfl

@[simp]
/--
theorem `mkHom_f_1` / 定理 `mkHom_f_1`

English:
theorem mkHom_f_1
  statement: (mkHom P Q zero one one_zero_comm succ).f 1 = one
  proof: rfl

@[simp]

中文:
定理 mkHom_f_1
  结论: (mkHom P Q zero one one_zero_comm succ).f 1 = one
  证明: rfl

@[simp]
-/
theorem mkHom_f_1 : (mkHom P Q zero one one_zero_comm succ).f 1 = one :=
  rfl

@[simp]
/--
theorem `mkHom_f_succ_succ` / 定理 `mkHom_f_succ_succ`

English:
theorem mkHom_f_succ_succ
  given: (n : Nat)
  proof: by
  dsimp [mkHom, mkHomAux]

中文:
定理 mkHom_f_succ_succ
  条件: (n : 自然数)
  证明: by
  dsimp [mkHom, mkHomAux]

Depends on / 依赖: mkHomAux
-/
theorem mkHom_f_succ_succ (n : Nat) :
    (mkHom P Q zero one one_zero_comm succ).f (n + 2) =
      (succ n
          ⟨(mkHom P Q zero one one_zero_comm succ).f n,
            (mkHom P Q zero one one_zero_comm succ).f (n + 1),
            (mkHom P Q zero one one_zero_comm succ).comm n (n + 1)⟩).1 := by
  dsimp [mkHom, mkHomAux]

end MkHom

end CochainComplex
