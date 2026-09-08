/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Algebra.Homology.Embedding.Restriction

/-!
# Opposite categories of cochain complexes

We construct an equivalence of categories `CochainComplex.opEquivalence C`
between `(CochainComplex C ℤ)ᵒᵖ` and `CochainComplex Cᵒᵖ ℤ`, and we show
that two morphisms in `CochainComplex C ℤ` are homotopic iff they are
homotopic as morphisms in `CochainComplex Cᵒᵖ ℤ`.

-/

@[expose] public section

noncomputable section

open Opposite CategoryTheory Limits

variable (C : Type*) [Category* C]

namespace ComplexShape

/-- The embedding of the complex shape `up ℤ` in `down ℤ` given by `n ↦ -n`. -/
@[simps]
/-
**ComplexShape.embeddingUpIntDownInt** 是 Mathlib 中的一个定义，位于命名空间 `ComplexShape`。
形式化陈述：embeddingUpIntDownInt : (up Int).Embedding (down Int) where f n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The embedding of the complex shape `up ℤ` in `down ℤ` given by `n ↦ -n`.
-/
def embeddingUpIntDownInt : (up ℤ).Embedding (down ℤ) where
  f n := -n
  injective_f _ _ := by simp
  rel := by simp

set_option backward.defeqAttrib.useBackward true in
/-
**ComplexShape.** 是 Mathlib 中的一个实例，位于命名空间 `ComplexShape`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : embeddingUpIntDownInt.IsRelIff where
  rel' := by dsimp; lia

set_option backward.defeqAttrib.useBackward true in
/-- The embedding of the complex shape `down ℤ` in `up ℤ` given by `n ↦ -n`. -/
@[simps]
/-
**ComplexShape.embeddingDownIntUpInt** 是 Mathlib 中的一个定义，位于命名空间 `ComplexShape`。
形式化陈述：embeddingDownIntUpInt : (down Int).Embedding (up Int) where f n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The embedding of the complex shape `down ℤ` in `up ℤ` given by `n ↦ -n`.
-/
def embeddingDownIntUpInt : (down ℤ).Embedding (up ℤ) where
  f n := -n
  injective_f _ _ := by simp
  rel := by dsimp; lia

set_option backward.defeqAttrib.useBackward true in
/-
**ComplexShape.** 是 Mathlib 中的一个实例，位于命名空间 `ComplexShape`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : embeddingDownIntUpInt.IsRelIff where
  rel' := by dsimp; lia

end ComplexShape

namespace ChainComplex

variable [HasZeroMorphisms C]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
attribute [local simp] HomologicalComplex.XIsoOfEq in
/-- The equivalence of categories `ChainComplex C ℤ ≌ CochainComplex C ℤ`. -/
/-
**ChainComplex.cochainComplexEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `ChainComplex
`。
形式化陈述：cochainComplexEquivalence : ChainComplex C Int ≌ CochainComplex C Int wher
e functor
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.instIsRelIffIntEmbeddingUpIntDownInt`：ComplexShape.embeddin
gUpIntDownInt.IsRelIff
· 使用定理 `ComplexShape.instIsRelIffIntEmbeddingDownIntUpInt`：ComplexShape.embeddin
gDownIntUpInt.IsRelIff

--- 原说明 ---
The equivalence of categories `ChainComplex C ℤ ≌ CochainComplex C ℤ`.
-/
def cochainComplexEquivalence :
    ChainComplex C ℤ ≌ CochainComplex C ℤ where
  functor := ComplexShape.embeddingUpIntDownInt.restrictionFunctor C
  inverse := ComplexShape.embeddingDownIntUpInt.restrictionFunctor C
  unitIso :=
    NatIso.ofComponents (fun K ↦ HomologicalComplex.Hom.isoOfComponents
      (fun n ↦ K.XIsoOfEq (by simp)))
  counitIso :=
    NatIso.ofComponents (fun K ↦ HomologicalComplex.Hom.isoOfComponents
      (fun n ↦ K.XIsoOfEq (by simp)))

end ChainComplex

namespace CochainComplex

/-- The equivalence of categories `(CochainComplex C ℤ)ᵒᵖ ≌ CochainComplex Cᵒᵖ ℤ`. -/
/-
**CochainComplex.opEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex`。
形式化陈述：opEquivalence [HasZeroMorphisms C] : (CochainComplex C Int)ᵒᵖ ≌ CochainCom
plex Cᵒᵖ Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence of categories `(CochainComplex C ℤ)ᵒᵖ ≌ CochainComplex Cᵒᵖ ℤ`.
-/
def opEquivalence [HasZeroMorphisms C] :
    (CochainComplex C ℤ)ᵒᵖ ≌ CochainComplex Cᵒᵖ ℤ :=
  (HomologicalComplex.opEquivalence C (.up ℤ)).trans
    (ChainComplex.cochainComplexEquivalence _)

variable {C} [Preadditive C]

attribute [local simp] opEquivalence ChainComplex.cochainComplexEquivalence

section

variable {K L : CochainComplex C ℤ} {f g : K ⟶ L}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given an homotopy between morphisms of cochain complexes indexed by `ℤ`,
this is the corresponding homotopy between morphisms of cochain complexes
in the opposite category. -/
/-
**CochainComplex.homotopyOp** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex`。
形式化陈述：homotopyOp (h : Homotopy f g) : Homotopy ((opEquivalence C).functor.map f.
op) ((opEquivalence C).functor.map g.op) where hom p q
参数：h : Homotopy f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an homotopy between morphisms of cochain complexes indexed by `ℤ`,
this is the corresponding homotopy between morphisms of cochain complexes
in the opposite category.
-/
def homotopyOp (h : Homotopy f g) :
    Homotopy ((opEquivalence C).functor.map f.op)
      ((opEquivalence C).functor.map g.op) where
  hom p q := (h.hom (-q) (-p)).op
  zero p q hpq := by
    rw [h.zero, op_zero]
    dsimp at hpq ⊢
    lia
  comm n := by
    dsimp
    simp only [h.comm, op_add, add_left_inj]
    rw [add_comm]
    congr 1
    · rw [prevD_eq _ (j' := - (n + 1)) (by simp)]
      symm
      exact dNext_eq _ (i' := n + 1) (by simp)
    · rw [dNext_eq _ (i' := - (n - 1)) (by dsimp; lia)]
      symm
      exact prevD_eq _ (j' := n - 1) (by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CochainComplex.homotopyOp_hom_eq** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
形式化陈述：homotopyOp_hom_eq (h : Homotopy f g) (p q p' q' : Int) (hp : p + p' = 0
参数：h : Homotopy f g；p q p' q' : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma homotopyOp_hom_eq (h : Homotopy f g)
    (p q p' q' : ℤ) (hp : p + p' = 0 := by lia) (hq : q + q' = 0 := by lia) :
    (homotopyOp h).hom p q =
      (L.XIsoOfEq (by dsimp; lia)).hom.op ≫ (h.hom q' p').op ≫
        (K.XIsoOfEq (by dsimp; lia)).hom.op := by
  obtain rfl : p' = -p := by lia
  obtain rfl : q' = -q := by lia
  simp [homotopyOp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The homotopy between two morphisms of cochain complexes indexed by `ℤ`
which correspond to an homotopy between morphisms of cochain complexes
in the opposite category. -/
/-
**CochainComplex.homotopyUnop** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex`。
形式化陈述：homotopyUnop (h : Homotopy ((opEquivalence C).functor.map f.op) ((opEquiva
lence C).functor.map g.op)) : Homotopy f g where hom p q
参数：h : Homotopy ((opEquivalence C).functor.map f.op) ((opEquivalence C).functor.
map g.op)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homotopy between two morphisms of cochain complexes indexed by `ℤ`
which correspond to an homotopy between morphisms of cochain complexes
in the opposite category.
-/
def homotopyUnop (h : Homotopy ((opEquivalence C).functor.map f.op)
    ((opEquivalence C).functor.map g.op)) :
    Homotopy f g where
  hom p q := (K.XIsoOfEq (by simp)).hom ≫ (h.hom (-q) (-p)).unop ≫ (L.XIsoOfEq (by simp)).hom
  zero p q hpq := by
    rw [h.zero, unop_zero, zero_comp, comp_zero]
    dsimp at hpq ⊢
    lia
  comm n := Quiver.Hom.op_inj (by
    have H (p q p' q' : ℤ) (hp : p = p') (hq : q = q') :
      h.hom p q = (L.XIsoOfEq (by simpa using hp.symm)).hom.op ≫ h.hom p' q' ≫
        (K.XIsoOfEq (by simpa)).hom.op := by
      subst hp hq
      simp
    obtain ⟨n, rfl⟩ : ∃ (m : ℤ), n = -m := ⟨-n , by simp⟩
    have := h.comm n
    dsimp at this
    rw [op_add, op_add, this, add_left_inj, add_comm]
    congr 1
    · refine (prevD_eq _ (j' := n - 1) (by dsimp; lia)).trans ?_
      rw [dNext_eq _ (i' := - (n - 1)) (by dsimp; lia)]
      dsimp
      simp [H (- -n) (- -(n - 1)) n (n - 1) (by lia) (by lia), ← op_comp_assoc]
    · refine (dNext_eq _ (i' := n + 1) (by dsimp)).trans ?_
      rw [prevD_eq _ (j' := - (n + 1)) (by simp)]
      dsimp
      simp [H (- -(n + 1)) (- -n) (n + 1) n (by simp) (by simp), ← op_comp_assoc, ← op_comp])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CochainComplex.homotopyUnop_hom_eq** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
形式化陈述：homotopyUnop_hom_eq (h : Homotopy ((opEquivalence C).functor.map f.op) ((o
pEquivalence C).functor.map g.op)) (p q p' q' : Int) (hp : p + p' = 0
参数：h : Homotopy ((opEquivalence C).functor.map f.op) ((opEquivalence C).functor.
map g.op)；p q p' q' : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ComplexShape.instIsRelIffIntEmbeddingUpIntDownInt`：ComplexShape.embeddin
gUpIntDownInt.IsRelIff
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma homotopyUnop_hom_eq
    (h : Homotopy ((opEquivalence C).functor.map f.op)
      ((opEquivalence C).functor.map g.op))
    (p q p' q' : ℤ) (hp : p + p' = 0 := by lia) (hq : q + q' = 0 := by lia) :
    (homotopyUnop h).hom p q =
      (K.XIsoOfEq (by dsimp; lia)).hom ≫ (h.hom q' p').unop ≫
        (L.XIsoOfEq (by dsimp; lia)).hom := by
  obtain rfl : p' = -p := by lia
  obtain rfl : q' = -q := by lia
  simp [homotopyUnop]

end

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Two morphisms of cochain complexes indexed by `ℤ` are homotopic iff
they are homotopic after the application of the functor
`(opEquivalence C).functor : (CochainComplex C ℤ)ᵒᵖ ⥤ CochainComplex Cᵒᵖ ℤ`. -/
/-
**CochainComplex.homotopyOpEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex`。
形式化陈述：homotopyOpEquiv {K L : CochainComplex C Int} {f g : K ⟶ L} : Homotopy f g 
≃ Homotopy ((opEquivalence C).functor.map f.op) ((opEquivalence C).functor.map g
.op) where toFun h
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two morphisms of cochain complexes indexed by `ℤ` are homotopic iff
they are homotopic after the application of the functor
`(opEquivalence C).functor : (CochainComplex C ℤ)ᵒᵖ ⥤ CochainComplex Cᵒᵖ ℤ`.
-/
def homotopyOpEquiv {K L : CochainComplex C ℤ} {f g : K ⟶ L} :
    Homotopy f g ≃ Homotopy ((opEquivalence C).functor.map f.op)
      ((opEquivalence C).functor.map g.op) where
  toFun h := homotopyOp h
  invFun h := homotopyUnop h
  left_inv h := by
    ext p q
    simp [homotopyUnop_hom_eq _ p q (-p) (-q),
      homotopyOp_hom_eq _ (-q) (-p) q p]
  right_inv h := by
    ext p q
    simp [homotopyOp_hom_eq _ p q (-p) (-q),
      homotopyUnop_hom_eq _ (-q) (-p) q p]

set_option backward.isDefEq.respectTransparency.types false in
/-
**CochainComplex.exactAt_op** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
形式化陈述：exactAt_op {K : CochainComplex C Int} {n : Int} (hK : K.ExactAt n) (m : In
t) (hm : n + m = 0
参数：hK : K.ExactAt n；m : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomologicalComplex.exactAt_iff'`：exactAt_iff' (hi : c.prev j = i) (hk : 
c.next j = k) : K.ExactAt j ↔ (K.sc' i j k).Exact
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CochainComplex.prev`：prev (α : Type*) [AddGroup α] [One α] (i : α) : (Co
mplexShape.up α).prev i = i - 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CochainComplex.next`：next (α : Type*) [AddRightCancelSemigroup α] [One α
] (i : α) : (ComplexShape.up α).next i = i + 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ShortComplex.exact_unop_iff`：exact_unop_iff (S : ShortCom
plex Cᵒᵖ) : S.unop.Exact ↔ S.Exact
-/
lemma exactAt_op {K : CochainComplex C ℤ} {n : ℤ} (hK : K.ExactAt n)
    (m : ℤ) (hm : n + m = 0 := by lia) :
    ((opEquivalence C).functor.obj (op K)).ExactAt m := by
  obtain rfl : n = -m := by lia
  rw [HomologicalComplex.exactAt_iff' _ (m - 1) m (m + 1) (by simp) (by simp),
    ← ShortComplex.exact_unop_iff]
  rwa [HomologicalComplex.exactAt_iff' _ (-(m + 1)) (-m) (-(m - 1)) (by grind [prev])
    (by grind [next])] at hK
/-
**CochainComplex.acyclic_op** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
形式化陈述：acyclic_op {K : CochainComplex C Int} (hK : K.Acyclic) : ((opEquivalence C
).functor.obj (op K)).Acyclic
参数：hK : K.Acyclic。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.exactAt_op`：exactAt_op {K : CochainComplex C Int} {n : In
t} (hK : K.ExactAt n) (m : Int) (hm : n + m = 0
-/
lemma acyclic_op {K : CochainComplex C ℤ} (hK : K.Acyclic) :
    ((opEquivalence C).functor.obj (op K)).Acyclic :=
  fun n ↦ exactAt_op (hK (-n)) n

end CochainComplex

