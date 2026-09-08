/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.AreComplementary
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-!
# Truncations on cochain complexes indexed by the integers.

In this file, we introduce abbreviations for the canonical truncations
`CochainComplex.truncLE`, `CochainComplex.truncGE` of cochain
complexes indexed by `ℤ`, as well as the conditions
`CochainComplex.IsStrictlyLE`, `CochainComplex.IsStrictlyGE`,
`CochainComplex.IsLE`, and `CochainComplex.IsGE`.

-/

@[expose] public section

open CategoryTheory Category Limits ComplexShape ZeroObject

namespace CochainComplex

variable {C : Type*} [Category* C]

open HomologicalComplex

section HasZeroMorphisms

variable [HasZeroMorphisms C] (K L : CochainComplex C ℤ) (φ : K ⟶ L) (e : K ≅ L)

section

variable [HasZeroObject C] [∀ i, K.HasHomology i] [∀ i, L.HasHomology i]

/-- If `K : CochainComplex C ℤ`, this is the canonical truncation `≤ n` of `K`. -/
/-
**CochainComplex.truncLE** 是 Mathlib 中的一个缩写定义，位于命名空间 `CochainComplex`。
形式化陈述：truncLE (n : Int) : CochainComplex C Int
参数：n : Int。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.instIsTruncLENatIntEmbeddingUpIntLE`：∀ (p : ℤ), (ComplexSha
pe.embeddingUpIntLE p).IsTruncLE

--- 原说明 ---
If `K : CochainComplex C ℤ`, this is the canonical truncation `≤ n` of `K`.
-/
noncomputable abbrev truncLE (n : ℤ) : CochainComplex C ℤ :=
  HomologicalComplex.truncLE K (embeddingUpIntLE n)

/-- If `K : CochainComplex C ℤ`, this is the canonical truncation `≥ n` of `K`. -/
/-
**CochainComplex.truncGE** 是 Mathlib 中的一个缩写定义，位于命名空间 `CochainComplex`。
形式化陈述：truncGE (n : Int) : CochainComplex C Int
参数：n : Int。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.instIsTruncGENatIntEmbeddingUpIntGE`：∀ (p : ℤ), (ComplexSha
pe.embeddingUpIntGE p).IsTruncGE

--- 原说明 ---
If `K : CochainComplex C ℤ`, this is the canonical truncation `≥ n` of `K`.
-/
noncomputable abbrev truncGE (n : ℤ) : CochainComplex C ℤ :=
  HomologicalComplex.truncGE K (embeddingUpIntGE n)

/-- The canonical map `K.truncLE n ⟶ K` for `K : CochainComplex C ℤ`. -/
/-
**CochainComplex.** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map `K.truncLE n ⟶ K` for `K : CochainComplex C ℤ`.
-/
noncomputable def ιTruncLE (n : ℤ) : K.truncLE n ⟶ K :=
  HomologicalComplex.ιTruncLE K (embeddingUpIntLE n)

/-- The canonical map `K ⟶ K.truncGE n` for `K : CochainComplex C ℤ`. -/
/-
**CochainComplex.** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map `K ⟶ K.truncGE n` for `K : CochainComplex C ℤ`.
-/
noncomputable def πTruncGE (n : ℤ) : K ⟶ K.truncGE n :=
  HomologicalComplex.πTruncGE K (embeddingUpIntGE n)
/-
**CochainComplex.quasiIsoAt_** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma quasiIsoAt_ιTruncLE (n q : ℤ) (hq : q ≤ n) :
    QuasiIsoAt (K.ιTruncLE n) q := by
  obtain ⟨k, rfl⟩ := Int.le.dest hq
  exact HomologicalComplex.quasiIsoAt_ιTruncLE (j := k) _ _ (by simp)
/-
**CochainComplex.quasiIsoAt_** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma quasiIsoAt_πTruncGE (n q : ℤ) (hq : n ≤ q) :
    QuasiIsoAt (K.πTruncGE n) q := by
  obtain ⟨k, rfl⟩ := Int.le.dest hq
  exact HomologicalComplex.quasiIsoAt_πTruncGE (j := k) _ _ (by simp)
/-
**CochainComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℤ) : QuasiIsoAt (K.πTruncGE n) n :=
  quasiIsoAt_πTruncGE _ _ _ (by lia)
/-
**CochainComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℤ) : QuasiIsoAt (K.ιTruncLE n) n :=
  quasiIsoAt_ιTruncLE _ _ _ (by lia)

section

variable {K L}

/-- The morphism `K.truncLE n ⟶ L.truncLE n` induced by a morphism `K ⟶ L`. -/
/-
**CochainComplex.truncLEMap** 是 Mathlib 中的一个缩写定义，位于命名空间 `CochainComplex`。
形式化陈述：truncLEMap (n : Int) : K.truncLE n ⟶ L.truncLE n
参数：n : Int。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.instIsTruncLENatIntEmbeddingUpIntLE`：∀ (p : ℤ), (ComplexSha
pe.embeddingUpIntLE p).IsTruncLE

--- 原说明 ---
The morphism `K.truncLE n ⟶ L.truncLE n` induced by a morphism `K ⟶ L`.
-/
noncomputable abbrev truncLEMap (n : ℤ) : K.truncLE n ⟶ L.truncLE n :=
  HomologicalComplex.truncLEMap φ (embeddingUpIntLE n)

/-- The morphism `K.truncGE n ⟶ L.truncGE n` induced by a morphism `K ⟶ L`. -/
/-
**CochainComplex.truncGEMap** 是 Mathlib 中的一个缩写定义，位于命名空间 `CochainComplex`。
形式化陈述：truncGEMap (n : Int) : K.truncGE n ⟶ L.truncGE n
参数：n : Int。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.instIsTruncGENatIntEmbeddingUpIntGE`：∀ (p : ℤ), (ComplexSha
pe.embeddingUpIntGE p).IsTruncGE

--- 原说明 ---
The morphism `K.truncGE n ⟶ L.truncGE n` induced by a morphism `K ⟶ L`.
-/
noncomputable abbrev truncGEMap (n : ℤ) : K.truncGE n ⟶ L.truncGE n :=
  HomologicalComplex.truncGEMap φ (embeddingUpIntGE n)

@[reassoc (attr := simp)]
/-
**CochainComplex.** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιTruncLE_naturality (n : ℤ) :
    truncLEMap φ n ≫ L.ιTruncLE n = K.ιTruncLE n ≫ φ := by
  apply HomologicalComplex.ιTruncLE_naturality

@[reassoc (attr := simp)]
/-
**CochainComplex.** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma πTruncGE_naturality (n : ℤ) :
    K.πTruncGE n ≫ truncGEMap φ n = φ ≫ L.πTruncGE n := by
  apply HomologicalComplex.πTruncGE_naturality

end

end

/-- The condition that a cochain complex `K` is strictly `≥ n`. -/
/-
**CochainComplex.IsStrictlyGE** 是 Mathlib 中的一个缩写定义，位于命名空间 `CochainComplex`。
形式化陈述：IsStrictlyGE (n : Int)
参数：n : Int。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condition that a cochain complex `K` is strictly `≥ n`.
-/
abbrev IsStrictlyGE (n : ℤ) := K.IsStrictlySupported (embeddingUpIntGE n)

/-- The condition that a cochain complex `K` is strictly `≤ n`. -/
/-
**CochainComplex.IsStrictlyLE** 是 Mathlib 中的一个缩写定义，位于命名空间 `CochainComplex`。
形式化陈述：IsStrictlyLE (n : Int)
参数：n : Int。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condition that a cochain complex `K` is strictly `≤ n`.
-/
abbrev IsStrictlyLE (n : ℤ) := K.IsStrictlySupported (embeddingUpIntLE n)

/-- The condition that a cochain complex `K` is (cohomologically) `≥ n`. -/
/-
**CochainComplex.IsGE** 是 Mathlib 中的一个缩写定义，位于命名空间 `CochainComplex`。
形式化陈述：IsGE (n : Int)
参数：n : Int。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condition that a cochain complex `K` is (cohomologically) `≥ n`.
-/
abbrev IsGE (n : ℤ) := K.IsSupported (embeddingUpIntGE n)

/-- The condition that a cochain complex `K` is (cohomologically) `≤ n`. -/
/-
**CochainComplex.IsLE** 是 Mathlib 中的一个缩写定义，位于命名空间 `CochainComplex`。
形式化陈述：IsLE (n : Int)
参数：n : Int。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condition that a cochain complex `K` is (cohomologically) `≤ n`.
-/
abbrev IsLE (n : ℤ) := K.IsSupported (embeddingUpIntLE n)
/-
**CochainComplex.isZero_of_isStrictlyGE** 是 Mathlib 中的一个引理，位于命名空间 `CochainComple
x`。
形式化陈述：isZero_of_isStrictlyGE (n i : Int) (hi : i < n
参数：n i : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.isZero_X_of_isStrictlySupported`：isZero_X_of_isStrict
lySupported [K.IsStrictlySupported e] (i' : ι') (hi' : forall i, e.f i != i') : 
IsZero (K.X i')
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma isZero_of_isStrictlyGE (n i : ℤ) (hi : i < n := by lia) [K.IsStrictlyGE n] :
    IsZero (K.X i) :=
  isZero_X_of_isStrictlySupported K (embeddingUpIntGE n) i
    (by simpa only [notMem_range_embeddingUpIntGE_iff] using hi)
/-
**CochainComplex.isZero_of_isStrictlyLE** 是 Mathlib 中的一个引理，位于命名空间 `CochainComple
x`。
形式化陈述：isZero_of_isStrictlyLE (n i : Int) (hi : n < i
参数：n i : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.isZero_X_of_isStrictlySupported`：isZero_X_of_isStrict
lySupported [K.IsStrictlySupported e] (i' : ι') (hi' : forall i, e.f i != i') : 
IsZero (K.X i')
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma isZero_of_isStrictlyLE (n i : ℤ) (hi : n < i := by lia) [K.IsStrictlyLE n] :
    IsZero (K.X i) :=
  isZero_X_of_isStrictlySupported K (embeddingUpIntLE n) i
    (by simpa only [notMem_range_embeddingUpIntLE_iff] using hi)
/-
**CochainComplex.exactAt_of_isGE** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
形式化陈述：exactAt_of_isGE (n i : Int) (hi : i < n
参数：n i : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.exactAt_of_isSupported`：exactAt_of_isSupported [K.IsS
upported e] (i' : ι') (hi' : forall i, e.f i != i') : K.ExactAt i'
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma exactAt_of_isGE (n i : ℤ) (hi : i < n := by lia) [K.IsGE n] :
    K.ExactAt i :=
  exactAt_of_isSupported K (embeddingUpIntGE n) i
    (by simpa only [notMem_range_embeddingUpIntGE_iff] using hi)
/-
**CochainComplex.exactAt_of_isLE** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
形式化陈述：exactAt_of_isLE (n i : Int) (hi : n < i
参数：n i : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.exactAt_of_isSupported`：exactAt_of_isSupported [K.IsS
upported e] (i' : ι') (hi' : forall i, e.f i != i') : K.ExactAt i'
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma exactAt_of_isLE (n i : ℤ) (hi : n < i := by lia) [K.IsLE n] :
    K.ExactAt i :=
  exactAt_of_isSupported K (embeddingUpIntLE n) i
    (by simpa only [notMem_range_embeddingUpIntLE_iff] using hi)
/-
**CochainComplex.isZero_of_isGE** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
形式化陈述：isZero_of_isGE (n i : Int) (hi : i < n
参数：n i : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `HomologicalComplex.ExactAt.isZero_homology`：∀ {C : Type u_1} [inst : Cat
egoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphi
sms C]   {ι : Type u_2} {c : Com…
· 使用引理 `CochainComplex.exactAt_of_isGE`：exactAt_of_isGE (n i : Int) (hi : i < n
-/
lemma isZero_of_isGE (n i : ℤ) (hi : i < n := by lia) [K.IsGE n] [K.HasHomology i] :
    IsZero (K.homology i) :=
  (K.exactAt_of_isGE n i hi).isZero_homology
/-
**CochainComplex.isZero_of_isLE** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
形式化陈述：isZero_of_isLE (n i : Int) (hi : n < i
参数：n i : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `HomologicalComplex.ExactAt.isZero_homology`：∀ {C : Type u_1} [inst : Cat
egoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphi
sms C]   {ι : Type u_2} {c : Com…
· 使用引理 `CochainComplex.exactAt_of_isLE`：exactAt_of_isLE (n i : Int) (hi : n < i
-/
lemma isZero_of_isLE (n i : ℤ) (hi : n < i := by lia) [K.IsLE n] [K.HasHomology i] :
    IsZero (K.homology i) :=
  (K.exactAt_of_isLE n i hi).isZero_homology
/-
**CochainComplex.isStrictlyGE_iff** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
形式化陈述：isStrictlyGE_iff (n : Int) : K.IsStrictlyGE n ↔ forall (i : Int) (_ : i < 
n
参数：n : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.isZero_of_isStrictlyGE`：isZero_of_isStrictlyGE (n i : Int
) (hi : i < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ComplexShape.notMem_range_embeddingUpIntGE_iff`：notMem_range_embeddingUp
IntGE_iff (n : Int) : (forall (i : Nat), (embeddingUpIntGE p).f i != n) ↔ n < p
-/
lemma isStrictlyGE_iff (n : ℤ) :
    K.IsStrictlyGE n ↔ ∀ (i : ℤ) (_ : i < n := by lia), IsZero (K.X i) := by
  constructor
  · intro _ i hi
    exact K.isZero_of_isStrictlyGE n i hi
  · intro h
    refine IsStrictlySupported.mk (fun i hi ↦ ?_)
    rw [notMem_range_embeddingUpIntGE_iff] at hi
    exact h i hi
/-
**CochainComplex.isStrictlyLE_iff** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
形式化陈述：isStrictlyLE_iff (n : Int) : K.IsStrictlyLE n ↔ forall (i : Int) (_ : n < 
i), IsZero (K.X i)
参数：n : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.isZero_of_isStrictlyLE`：isZero_of_isStrictlyLE (n i : Int
) (hi : n < i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ComplexShape.notMem_range_embeddingUpIntLE_iff`：notMem_range_embeddingUp
IntLE_iff (n : Int) : (forall (i : Nat), (embeddingUpIntLE p).f i != n) ↔ p < n
-/
lemma isStrictlyLE_iff (n : ℤ) :
    K.IsStrictlyLE n ↔ ∀ (i : ℤ) (_ : n < i), IsZero (K.X i) := by
  constructor
  · intro _ i hi
    exact K.isZero_of_isStrictlyLE n i hi
  · intro h
    refine IsStrictlySupported.mk (fun i hi ↦ ?_)
    rw [notMem_range_embeddingUpIntLE_iff] at hi
    exact h i hi
/-
**CochainComplex.isGE_iff** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
形式化陈述：isGE_iff (n : Int) : K.IsGE n ↔ forall (i : Int) (_ : i < n), K.ExactAt i
参数：n : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.exactAt_of_isGE`：exactAt_of_isGE (n i : Int) (hi : i < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ComplexShape.notMem_range_embeddingUpIntGE_iff`：notMem_range_embeddingUp
IntGE_iff (n : Int) : (forall (i : Nat), (embeddingUpIntGE p).f i != n) ↔ n < p
-/
lemma isGE_iff (n : ℤ) :
    K.IsGE n ↔ ∀ (i : ℤ) (_ : i < n), K.ExactAt i := by
  constructor
  · intro _ i hi
    exact K.exactAt_of_isGE n i hi
  · intro h
    refine IsSupported.mk (fun i hi ↦ ?_)
    rw [notMem_range_embeddingUpIntGE_iff] at hi
    exact h i hi
/-
**CochainComplex.isLE_iff** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
形式化陈述：isLE_iff (n : Int) : K.IsLE n ↔ forall (i : Int) (_ : n < i), K.ExactAt i
参数：n : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.exactAt_of_isLE`：exactAt_of_isLE (n i : Int) (hi : n < i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ComplexShape.notMem_range_embeddingUpIntLE_iff`：notMem_range_embeddingUp
IntLE_iff (n : Int) : (forall (i : Nat), (embeddingUpIntLE p).f i != n) ↔ p < n
-/
lemma isLE_iff (n : ℤ) :
    K.IsLE n ↔ ∀ (i : ℤ) (_ : n < i), K.ExactAt i := by
  constructor
  · intro _ i hi
    exact K.exactAt_of_isLE n i hi
  · intro h
    refine IsSupported.mk (fun i hi ↦ ?_)
    rw [notMem_range_embeddingUpIntLE_iff] at hi
    exact h i hi
/-
**CochainComplex.isStrictlyLE_of_le** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
形式化陈述：isStrictlyLE_of_le (p q : Int) (hpq : p <= q) [K.IsStrictlyLE p] : K.IsStr
ictlyLE q
参数：p q : Int；hpq : p <= q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.isStrictlyLE_iff`：isStrictlyLE_iff (n : Int) : K.IsStrict
lyLE n ↔ forall (i : Int) (_ : n < i), IsZero (K.X i)
· 使用引理 `CochainComplex.isZero_of_isStrictlyLE`：isZero_of_isStrictlyLE (n i : Int
) (hi : n < i
-/
lemma isStrictlyLE_of_le (p q : ℤ) (hpq : p ≤ q) [K.IsStrictlyLE p] :
    K.IsStrictlyLE q := by
  rw [isStrictlyLE_iff]
  intro i hi
  exact K.isZero_of_isStrictlyLE p _
/-
**CochainComplex.isStrictlyGE_of_ge** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
形式化陈述：isStrictlyGE_of_ge (p q : Int) (hpq : p <= q) [K.IsStrictlyGE q] : K.IsStr
ictlyGE p
参数：p q : Int；hpq : p <= q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.isStrictlyGE_iff`：isStrictlyGE_iff (n : Int) : K.IsStrict
lyGE n ↔ forall (i : Int) (_ : i < n
· 使用引理 `CochainComplex.isZero_of_isStrictlyGE`：isZero_of_isStrictlyGE (n i : Int
) (hi : i < n
-/
lemma isStrictlyGE_of_ge (p q : ℤ) (hpq : p ≤ q) [K.IsStrictlyGE q] :
    K.IsStrictlyGE p := by
  rw [isStrictlyGE_iff]
  intro i hi
  exact K.isZero_of_isStrictlyGE q _
/-
**CochainComplex.isLE_of_le** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
形式化陈述：isLE_of_le (p q : Int) (hpq : p <= q) [K.IsLE p] : K.IsLE q
参数：p q : Int；hpq : p <= q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.isLE_iff`：isLE_iff (n : Int) : K.IsLE n ↔ forall (i : Int
) (_ : n < i), K.ExactAt i
· 使用引理 `CochainComplex.exactAt_of_isLE`：exactAt_of_isLE (n i : Int) (hi : n < i
-/
lemma isLE_of_le (p q : ℤ) (hpq : p ≤ q) [K.IsLE p] :
    K.IsLE q := by
  rw [isLE_iff]
  intro i hi
  exact K.exactAt_of_isLE p _
/-
**CochainComplex.isGE_of_ge** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
形式化陈述：isGE_of_ge (p q : Int) (hpq : p <= q) [K.IsGE q] : K.IsGE p
参数：p q : Int；hpq : p <= q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.isGE_iff`：isGE_iff (n : Int) : K.IsGE n ↔ forall (i : Int
) (_ : i < n), K.ExactAt i
· 使用引理 `CochainComplex.exactAt_of_isGE`：exactAt_of_isGE (n i : Int) (hi : i < n
-/
lemma isGE_of_ge (p q : ℤ) (hpq : p ≤ q) [K.IsGE q] :
    K.IsGE p := by
  rw [isGE_iff]
  intro i hi
  exact K.exactAt_of_isGE q _

section

variable {K L}

include e

/-
**CochainComplex.isStrictlyLE_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
形式化陈述：isStrictlyLE_of_iso (n : Int) [K.IsStrictlyLE n] : L.IsStrictlyLE n
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `HomologicalComplex.isStrictlySupported_of_iso`：isStrictlySupported_of_is
o [K.IsStrictlySupported e] : L.IsStrictlySupported e where isZero i' hi'
-/
lemma isStrictlyLE_of_iso (n : ℤ) [K.IsStrictlyLE n] : L.IsStrictlyLE n := by
  apply isStrictlySupported_of_iso e
/-
**CochainComplex.isStrictlyGE_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
形式化陈述：isStrictlyGE_of_iso (n : Int) [K.IsStrictlyGE n] : L.IsStrictlyGE n
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `HomologicalComplex.isStrictlySupported_of_iso`：isStrictlySupported_of_is
o [K.IsStrictlySupported e] : L.IsStrictlySupported e where isZero i' hi'
-/
lemma isStrictlyGE_of_iso (n : ℤ) [K.IsStrictlyGE n] : L.IsStrictlyGE n := by
  apply isStrictlySupported_of_iso e
/-
**CochainComplex.isLE_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
形式化陈述：isLE_of_iso (n : Int) [K.IsLE n] : L.IsLE n
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `HomologicalComplex.isSupported_of_iso`：isSupported_of_iso [K.IsSupported
 e] : L.IsSupported e where exactAt i' hi'
-/
lemma isLE_of_iso (n : ℤ) [K.IsLE n] : L.IsLE n := by
  apply isSupported_of_iso e
/-
**CochainComplex.isGE_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
形式化陈述：isGE_of_iso (n : Int) [K.IsGE n] : L.IsGE n
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `HomologicalComplex.isSupported_of_iso`：isSupported_of_iso [K.IsSupported
 e] : L.IsSupported e where exactAt i' hi'
-/
lemma isGE_of_iso (n : ℤ) [K.IsGE n] : L.IsGE n := by
  apply isSupported_of_iso e

end

section

variable [HasZeroObject C]

/-
**CochainComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : CochainComplex C ℕ) :
    CochainComplex.IsStrictlyGE (X.extend embeddingUpNat) 0 where
  isZero _ _ := isZero_extend_X _ _ _ (by aesop)
/-
**CochainComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : ChainComplex C ℕ) :
    CochainComplex.IsStrictlyLE (X.extend embeddingDownNat) 0 where
  isZero _ _ := isZero_extend_X _ _ _ (by aesop)

set_option backward.isDefEq.respectTransparency.types false in
/-- A cochain complex that is both strictly `≤ n` and `≥ n` is isomorphic to
a complex `(single _ _ n).obj M` for some object `M`. -/
/-
**CochainComplex.exists_iso_single** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
形式化陈述：exists_iso_single (n : Int) [K.IsStrictlyGE n] [K.IsStrictlyLE n] : exists
 (M : C), Nonempty (K ≅ (single _ _ n).obj M)
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_src`：eq_of_src (hX : IsZero X) (f g :
 X ⟶ Y) : f = g
· 使用引理 `CochainComplex.isZero_of_isStrictlyGE`：isZero_of_isStrictlyGE (n i : Int
) (hi : i < n
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_tgt`：eq_of_tgt (hX : IsZero X) (f g :
 Y ⟶ X) : f = g
· 使用引理 `CochainComplex.isZero_of_isStrictlyLE`：isZero_of_isStrictlyLE (n i : Int
) (hi : n < i
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `HomologicalComplex.mkHomToSingle_f`：mkHomToSingle_f {K : HomologicalComp
lex V c} {j : ι} {A : V} (φ : K.X j ⟶ A) (hφ : forall (i : ι), c.Rel i j -> K.d 
i j ≫ φ = 0) : (mkHomToS…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用引理 `HomologicalComplex.mkHomFromSingle_f`：mkHomFromSingle_f {K : Homological
Complex V c} {j : ι} {A : V} (φ : A ⟶ K.X j) (hφ : forall (k : ι), c.Rel j k -> 
φ ≫ K.d j k = 0) : (mkHomF…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `HomologicalComplex.from_single_hom_ext`：from_single_hom_ext {K : Homolog
icalComplex V c} {j : ι} {A : V} {f g : (single V c j).obj A ⟶ K} (hfg : f.f j =
 g.f j) : f = g
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …

--- 原说明 ---
A cochain complex that is both strictly `≤ n` and `≥ n` is isomorphic to
a complex `(single _ _ n).obj M` for some object `M`.
-/
lemma exists_iso_single (n : ℤ) [K.IsStrictlyGE n] [K.IsStrictlyLE n] :
    ∃ (M : C), Nonempty (K ≅ (single _ _ n).obj M) :=
  ⟨K.X n, ⟨{
      hom := mkHomToSingle (𝟙 _) (fun i (hi : i + 1 = n) ↦
        (K.isZero_of_isStrictlyGE n i (by lia)).eq_of_src _ _)
      inv := mkHomFromSingle (𝟙 _) (fun i (hi : n + 1 = i) ↦
        (K.isZero_of_isStrictlyLE n i (by lia)).eq_of_tgt _ _)
      hom_inv_id := by
        ext i
        obtain hi | rfl | hi := lt_trichotomy i n
        · apply (K.isZero_of_isStrictlyGE n i (by lia)).eq_of_src
        · simp
        · apply (K.isZero_of_isStrictlyLE n i (by lia)).eq_of_tgt
      inv_hom_id := by aesop }⟩⟩
/-
**CochainComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (A : C) (n : ℤ) :
    IsStrictlyGE ((single C (ComplexShape.up ℤ) n).obj A) n := by
  rw [isStrictlyGE_iff]
  intro i hi
  exact isZero_single_obj_X _ _ _ _ (by lia)
/-
**CochainComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (A : C) (n : ℤ) :
    IsStrictlyLE ((single C (ComplexShape.up ℤ) n).obj A) n := by
  rw [isStrictlyLE_iff]
  intro i hi
  exact isZero_single_obj_X _ _ _ _ (by lia)

variable [∀ i, K.HasHomology i] [∀ i, L.HasHomology i] (n : ℤ)
/-
**CochainComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [K.IsStrictlyGE n] : IsIso (K.πTruncGE n) := by dsimp [πTruncGE]; infer_instance
/-
**CochainComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [K.IsStrictlyLE n] : IsIso (K.ιTruncLE n) := by dsimp [ιTruncLE]; infer_instance
/-
**CochainComplex.isIso_** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isIso_πTruncGE_iff : IsIso (K.πTruncGE n) ↔ K.IsStrictlyGE n := by
  apply HomologicalComplex.isIso_πTruncGE_iff
/-
**CochainComplex.isIso_** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isIso_ιTruncLE_iff : IsIso (K.ιTruncLE n) ↔ K.IsStrictlyLE n := by
  apply HomologicalComplex.isIso_ιTruncLE_iff
/-
**CochainComplex.quasiIso_** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma quasiIso_πTruncGE_iff : QuasiIso (K.πTruncGE n) ↔ K.IsGE n :=
  quasiIso_πTruncGE_iff_isSupported K (embeddingUpIntGE n)
/-
**CochainComplex.quasiIso_** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma quasiIso_ιTruncLE_iff : QuasiIso (K.ιTruncLE n) ↔ K.IsLE n :=
  quasiIso_ιTruncLE_iff_isSupported K (embeddingUpIntLE n)
/-
**CochainComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [K.IsGE n] : QuasiIso (K.πTruncGE n) := by
  rw [quasiIso_πTruncGE_iff]
  infer_instance
/-
**CochainComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [K.IsLE n] : QuasiIso (K.ιTruncLE n) := by
  rw [quasiIso_ιTruncLE_iff]
  infer_instance

variable {K L}

set_option backward.defeqAttrib.useBackward true in
/-
**CochainComplex.quasiIso_truncGEMap_iff** 是 Mathlib 中的一个引理，位于命名空间 `CochainCompl
ex`。
形式化陈述：quasiIso_truncGEMap_iff : QuasiIso (truncGEMap φ n) ↔ forall (i : Int) (_ 
: n <= i), QuasiIsoAt φ i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `HomologicalComplex.truncGE.instHasHomology`：∀ {ι : Type u_1} {ι' : Type 
u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst : Catego
ryTheory.Category.{v_1, u_3} C] …
· 使用定理 `ComplexShape.instIsTruncGENatIntEmbeddingUpIntGE`：∀ (p : ℤ), (ComplexSha
pe.embeddingUpIntGE p).IsTruncGE
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomologicalComplex.quasiIso_truncGEMap_iff`：quasiIso_truncGEMap_iff : Qu
asiIso (truncGEMap φ e) ↔ forall (i : ι) (i' : ι') (_ : e.f i = i'), QuasiIsoAt 
φ i'
· 使用定理 `Int.le.dest`：∀ {a b : ℤ}, a ≤ b → ∃ n, a + ↑n = b
-/
lemma quasiIso_truncGEMap_iff :
    QuasiIso (truncGEMap φ n) ↔ ∀ (i : ℤ) (_ : n ≤ i), QuasiIsoAt φ i := by
  rw [HomologicalComplex.quasiIso_truncGEMap_iff]
  constructor
  · intro h i hi
    obtain ⟨k, rfl⟩ := Int.le.dest hi
    exact h k _ rfl
  · rintro h i i' rfl
    exact h _ (by dsimp; lia)

set_option backward.defeqAttrib.useBackward true in
/-
**CochainComplex.quasiIso_truncLEMap_iff** 是 Mathlib 中的一个引理，位于命名空间 `CochainCompl
ex`。
形式化陈述：quasiIso_truncLEMap_iff : QuasiIso (truncLEMap φ n) ↔ forall (i : Int) (_ 
: i <= n), QuasiIsoAt φ i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `HomologicalComplex.instHasHomologyTruncLE`：∀ {ι : Type u_1} {ι' : Type u
_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [inst : Categor
yTheory.Category.{v_1, u_3} C] …
· 使用定理 `ComplexShape.instIsTruncLENatIntEmbeddingUpIntLE`：∀ (p : ℤ), (ComplexSha
pe.embeddingUpIntLE p).IsTruncLE
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomologicalComplex.quasiIso_truncLEMap_iff`：quasiIso_truncLEMap_iff : Qu
asiIso (truncLEMap φ e) ↔ forall (i : ι) (i' : ι') (_ : e.f i = i'), QuasiIsoAt 
φ i'
· 使用定理 `Int.le.dest`：∀ {a b : ℤ}, a ≤ b → ∃ n, a + ↑n = b
-/
lemma quasiIso_truncLEMap_iff :
    QuasiIso (truncLEMap φ n) ↔ ∀ (i : ℤ) (_ : i ≤ n), QuasiIsoAt φ i := by
  rw [HomologicalComplex.quasiIso_truncLEMap_iff]
  constructor
  · intro h i hi
    obtain ⟨k, rfl⟩ := Int.le.dest hi
    exact h k _ (by dsimp; lia)
  · rintro h i i' rfl
    exact h _ (by dsimp; lia)

end

section

variable {D : Type*} [Category* D] [HasZeroMorphisms D]

/-
**CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff** 是 Mathlib 中的一个引理，位
于命名空间 `CochainComplex`。
形式化陈述：isStrictlyGE_mapHomologicalComplex_obj_iff (F : C ⥤ D) [F.Faithful] [F.Pre
servesZeroMorphisms] (n : Int) : CochainComplex.IsStrictlyGE ((F.mapHomologicalC
omplex (.up Int)).obj K) n ↔ K.IsStrictlyGE n
参数：F : C ⥤ D；n : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.isStrictlySupported_mapHomologicalComplex_obj_iff`：is
StrictlySupported_mapHomologicalComplex_obj_iff [F.Faithful] : ((F.mapHomologica
lComplex c').obj K).IsStrictlySupported e ↔ K.IsStrictlySu…
-/
lemma isStrictlyGE_mapHomologicalComplex_obj_iff
    (F : C ⥤ D) [F.Faithful] [F.PreservesZeroMorphisms] (n : ℤ) :
    CochainComplex.IsStrictlyGE ((F.mapHomologicalComplex (.up ℤ)).obj K) n ↔
      K.IsStrictlyGE n :=
  isStrictlySupported_mapHomologicalComplex_obj_iff ..
/-
**CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff** 是 Mathlib 中的一个引理，位
于命名空间 `CochainComplex`。
形式化陈述：isStrictlyLE_mapHomologicalComplex_obj_iff (F : C ⥤ D) [F.Faithful] [F.Pre
servesZeroMorphisms] (n : Int) : CochainComplex.IsStrictlyLE ((F.mapHomologicalC
omplex (.up Int)).obj K) n ↔ K.IsStrictlyLE n
参数：F : C ⥤ D；n : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.isStrictlySupported_mapHomologicalComplex_obj_iff`：is
StrictlySupported_mapHomologicalComplex_obj_iff [F.Faithful] : ((F.mapHomologica
lComplex c').obj K).IsStrictlySupported e ↔ K.IsStrictlySu…
-/
lemma isStrictlyLE_mapHomologicalComplex_obj_iff
    (F : C ⥤ D) [F.Faithful] [F.PreservesZeroMorphisms] (n : ℤ) :
    CochainComplex.IsStrictlyLE ((F.mapHomologicalComplex (.up ℤ)).obj K) n ↔
      K.IsStrictlyLE n :=
  isStrictlySupported_mapHomologicalComplex_obj_iff ..

end

end HasZeroMorphisms

section Preadditive

variable [Preadditive C]

/-
**CochainComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasZeroObject C] (A : C) (n : ℤ) : ((singleFunctor C n).obj A).IsStrictlyGE n :=
  inferInstanceAs (IsStrictlyGE ((single C (ComplexShape.up ℤ) n).obj A) n)
/-
**CochainComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasZeroObject C] (A : C) (n : ℤ) : ((singleFunctor C n).obj A).IsStrictlyLE n :=
  inferInstanceAs (IsStrictlyLE ((single C (ComplexShape.up ℤ) n).obj A) n)

variable (K : CochainComplex C ℤ)
/-
**CochainComplex.isStrictlyLE_shift** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
形式化陈述：isStrictlyLE_shift (n : Int) [K.IsStrictlyLE n] (a n' : Int) (h : a + n' =
 n) : (K⟦a⟧).IsStrictlyLE n'
参数：n : Int；a n' : Int；h : a + n' = n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.isStrictlyLE_iff`：isStrictlyLE_iff (n : Int) : K.IsStrict
lyLE n ↔ forall (i : Int) (_ : n < i), IsZero (K.X i)
· 使用定理 `CategoryTheory.Limits.IsZero.of_iso`：of_iso (hY : IsZero Y) (e : X ≅ Y) 
: IsZero X
· 使用引理 `CochainComplex.isZero_of_isStrictlyLE`：isZero_of_isStrictlyLE (n i : Int
) (hi : n < i
-/
lemma isStrictlyLE_shift (n : ℤ) [K.IsStrictlyLE n] (a n' : ℤ) (h : a + n' = n) :
    (K⟦a⟧).IsStrictlyLE n' := by
  rw [isStrictlyLE_iff]
  intro i hi
  exact IsZero.of_iso (K.isZero_of_isStrictlyLE n _ (by lia)) (K.shiftFunctorObjXIso a i _ rfl)
/-
**CochainComplex.isStrictlyGE_shift** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
形式化陈述：isStrictlyGE_shift (n : Int) [K.IsStrictlyGE n] (a n' : Int) (h : a + n' =
 n) : (K⟦a⟧).IsStrictlyGE n'
参数：n : Int；a n' : Int；h : a + n' = n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.isStrictlyGE_iff`：isStrictlyGE_iff (n : Int) : K.IsStrict
lyGE n ↔ forall (i : Int) (_ : i < n
· 使用定理 `CategoryTheory.Limits.IsZero.of_iso`：of_iso (hY : IsZero Y) (e : X ≅ Y) 
: IsZero X
· 使用引理 `CochainComplex.isZero_of_isStrictlyGE`：isZero_of_isStrictlyGE (n i : Int
) (hi : i < n
-/
lemma isStrictlyGE_shift (n : ℤ) [K.IsStrictlyGE n] (a n' : ℤ) (h : a + n' = n) :
    (K⟦a⟧).IsStrictlyGE n' := by
  rw [isStrictlyGE_iff]
  intro i hi
  exact IsZero.of_iso (K.isZero_of_isStrictlyGE n _ (by lia)) (K.shiftFunctorObjXIso a i _ rfl)

section

variable [CategoryWithHomology C]

/-
**CochainComplex.isLE_shift** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
形式化陈述：isLE_shift (n : Int) [K.IsLE n] (a n' : Int) (h : a + n' = n) : (K⟦a⟧).IsL
E n'
参数：n : Int；a n' : Int；h : a + n' = n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.isLE_iff`：isLE_iff (n : Int) : K.IsLE n ↔ forall (i : Int
) (_ : n < i), K.ExactAt i
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用引理 `HomologicalComplex.exactAt_iff_isZero_homology`：exactAt_iff_isZero_homol
ogy [K.HasHomology i] : K.ExactAt i ↔ IsZero (K.homology i)
· 使用定理 `CategoryTheory.Limits.IsZero.of_iso`：of_iso (hY : IsZero Y) (e : X ≅ Y) 
: IsZero X
· 使用引理 `CochainComplex.isZero_of_isLE`：isZero_of_isLE (n i : Int) (hi : n < i
-/
lemma isLE_shift (n : ℤ) [K.IsLE n] (a n' : ℤ) (h : a + n' = n) : (K⟦a⟧).IsLE n' := by
  rw [isLE_iff]
  intro i hi
  rw [exactAt_iff_isZero_homology]
  exact IsZero.of_iso (K.isZero_of_isLE n (a + i) (by lia))
    (((homologyFunctor C _ (0 : ℤ)).shiftIso a i _ rfl).app K)
/-
**CochainComplex.isGE_shift** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
形式化陈述：isGE_shift (n : Int) [K.IsGE n] (a n' : Int) (h : a + n' = n) : (K⟦a⟧).IsG
E n'
参数：n : Int；a n' : Int；h : a + n' = n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.isGE_iff`：isGE_iff (n : Int) : K.IsGE n ↔ forall (i : Int
) (_ : i < n), K.ExactAt i
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用引理 `HomologicalComplex.exactAt_iff_isZero_homology`：exactAt_iff_isZero_homol
ogy [K.HasHomology i] : K.ExactAt i ↔ IsZero (K.homology i)
· 使用定理 `CategoryTheory.Limits.IsZero.of_iso`：of_iso (hY : IsZero Y) (e : X ≅ Y) 
: IsZero X
· 使用引理 `CochainComplex.isZero_of_isGE`：isZero_of_isGE (n i : Int) (hi : i < n
-/
lemma isGE_shift (n : ℤ) [K.IsGE n] (a n' : ℤ) (h : a + n' = n) : (K⟦a⟧).IsGE n' := by
  rw [isGE_iff]
  intro i hi
  rw [exactAt_iff_isZero_homology]
  exact IsZero.of_iso (K.isZero_of_isGE n (a + i) (by lia))
    (((homologyFunctor C _ (0 : ℤ)).shiftIso a i _ rfl).app K)

end

end Preadditive

section HasZeroMorphisms

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
  (K L : CochainComplex C ℤ) (φ : K ⟶ L) (e : K ≅ L)
  [∀ (i : ℤ), K.HasHomology i] [∀ (i : ℤ), L.HasHomology i] (n : ℤ)

set_option backward.defeqAttrib.useBackward true in
/-- When `K` is a cochain complex indexed by `ℤ` and `n < i`, this is
the isomorphism `(K.truncGE n).X i ≅ K.X i`. -/
/-
**CochainComplex.truncGEXIso** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex`。
形式化陈述：truncGEXIso (n i : Int) (hi : n < i
参数：n i : Int。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.instIsTruncGENatIntEmbeddingUpIntGE`：∀ (p : ℤ), (ComplexSha
pe.embeddingUpIntGE p).IsTruncGE

--- 原说明 ---
When `K` is a cochain complex indexed by `ℤ` and `n < i`, this is
the isomorphism `(K.truncGE n).X i ≅ K.X i`.
-/
noncomputable def truncGEXIso (n i : ℤ) (hi : n < i := by lia) :
    (K.truncGE n).X i ≅ K.X i :=
  HomologicalComplex.truncGEXIso K (embeddingUpIntGE n) (i := (i - n).natAbs) (by
      dsimp
      rw [Int.natAbs_of_nonneg (by lia), add_sub_cancel])
    (fun h ↦ by
      rw [boundaryGE_embeddingUpIntGE_iff, Int.natAbs_eq_zero] at h
      lia)

set_option backward.defeqAttrib.useBackward true in
/-- When `K` is a cochain complex indexed by `ℤ` and `i < n`, this is
the isomorphism `(K.truncLE n).X i ≅ K.X i`. -/
/-
**CochainComplex.truncLEXIso** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex`。
形式化陈述：truncLEXIso (n i : Int) (hi : i < n
参数：n i : Int。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.instIsTruncLENatIntEmbeddingUpIntLE`：∀ (p : ℤ), (ComplexSha
pe.embeddingUpIntLE p).IsTruncLE

--- 原说明 ---
When `K` is a cochain complex indexed by `ℤ` and `i < n`, this is
the isomorphism `(K.truncLE n).X i ≅ K.X i`.
-/
noncomputable def truncLEXIso (n i : ℤ) (hi : i < n := by lia) :
    (K.truncLE n).X i ≅ K.X i :=
  HomologicalComplex.truncLEXIso K (embeddingUpIntLE n) (i := (n - i).natAbs) (by
      dsimp
      rw [Int.natAbs_of_nonneg (by lia), sub_sub_cancel])
    (fun h ↦ by
      rw [boundaryLE_embeddingUpIntLE_iff, Int.natAbs_eq_zero] at h
      lia)

/-- When `K` is a cochain complex indexed by `ℤ`, this is the isomorphism
`(K.truncGE n).X n ≅ K.opcycles n`. -/
/-
**CochainComplex.truncGEXIsoOpcycles** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex`。
形式化陈述：truncGEXIsoOpcycles (n : Int) : (K.truncGE n).X n ≅ K.opcycles n
参数：n : Int。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.instIsTruncGENatIntEmbeddingUpIntGE`：∀ (p : ℤ), (ComplexSha
pe.embeddingUpIntGE p).IsTruncGE

--- 原说明 ---
When `K` is a cochain complex indexed by `ℤ`, this is the isomorphism
`(K.truncGE n).X n ≅ K.opcycles n`.
-/
noncomputable def truncGEXIsoOpcycles (n : ℤ) :
    (K.truncGE n).X n ≅ K.opcycles n :=
  HomologicalComplex.truncGEXIsoOpcycles K (embeddingUpIntGE n) (i := 0) (by simp)
    (by rw [boundaryGE_embeddingUpIntGE_iff])

/-- When `K` is a cochain complex indexed by `ℤ`, this is the isomorphism
`(K.truncLE n).X n ≅ K.cycles n`. -/
/-
**CochainComplex.truncLEXIsoCycles** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex`。
形式化陈述：truncLEXIsoCycles (n : Int) : (K.truncLE n).X n ≅ K.cycles n
参数：n : Int。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.instIsTruncLENatIntEmbeddingUpIntLE`：∀ (p : ℤ), (ComplexSha
pe.embeddingUpIntLE p).IsTruncLE

--- 原说明 ---
When `K` is a cochain complex indexed by `ℤ`, this is the isomorphism
`(K.truncLE n).X n ≅ K.cycles n`.
-/
noncomputable def truncLEXIsoCycles (n : ℤ) :
    (K.truncLE n).X n ≅ K.cycles n :=
  HomologicalComplex.truncLEXIsoCycles K (embeddingUpIntLE n) (i := 0) (by simp)
    (by rw [boundaryLE_embeddingUpIntLE_iff])
/-
**CochainComplex.acyclic_truncGE_iff** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
形式化陈述：acyclic_truncGE_iff (n₀ n₁ : Int) (h : n₀ + 1 = n₁
参数：n₀ n₁ : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `ComplexShape.instIsTruncGENatIntEmbeddingUpIntGE`：∀ (p : ℤ), (ComplexSha
pe.embeddingUpIntGE p).IsTruncGE
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomologicalComplex.acyclic_truncGE_iff_isSupportedOutside`：acyclic_trunc
GE_iff_isSupportedOutside : (K.truncGE e).Acyclic ↔ K.IsSupportedOutside e
· 使用引理 `ComplexShape.Embedding.AreComplementary.isSupportedOutside₂_iff`：isSuppo
rtedOutside₂_iff : K.IsSupportedOutside e₂ ↔ K.IsSupported e₁
· 使用引理 `ComplexShape.Embedding.embeddingUpInt_areComplementary`：embeddingUpInt_a
reComplementary (n₀ n₁ : Int) (h : n₀ + 1 = n₁) : AreComplementary (embeddingUpI
ntLE n₀) (embeddingUpIntGE n₁) where disjoin…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma acyclic_truncGE_iff (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁ := by lia) :
    (K.truncGE n₁).Acyclic ↔ K.IsLE n₀ := by
  dsimp [truncGE]
  rw [acyclic_truncGE_iff_isSupportedOutside,
    (Embedding.embeddingUpInt_areComplementary n₀ n₁ h).isSupportedOutside₂_iff]
/-
**CochainComplex.acyclic_truncLE_iff** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
形式化陈述：acyclic_truncLE_iff (n₀ n₁ : Int) (h : n₀ + 1 = n₁
参数：n₀ n₁ : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `ComplexShape.instIsTruncLENatIntEmbeddingUpIntLE`：∀ (p : ℤ), (ComplexSha
pe.embeddingUpIntLE p).IsTruncLE
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomologicalComplex.acyclic_truncLE_iff_isSupportedOutside`：acyclic_trunc
LE_iff_isSupportedOutside : (K.truncLE e).Acyclic ↔ K.IsSupportedOutside e
· 使用引理 `ComplexShape.Embedding.AreComplementary.isSupportedOutside₁_iff`：isSuppo
rtedOutside₁_iff : K.IsSupportedOutside e₁ ↔ K.IsSupported e₂
· 使用引理 `ComplexShape.Embedding.embeddingUpInt_areComplementary`：embeddingUpInt_a
reComplementary (n₀ n₁ : Int) (h : n₀ + 1 = n₁) : AreComplementary (embeddingUpI
ntLE n₀) (embeddingUpIntGE n₁) where disjoin…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma acyclic_truncLE_iff (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁ := by lia) :
    (K.truncLE n₀).Acyclic ↔ K.IsGE n₁ := by
  dsimp [truncLE]
  rw [acyclic_truncLE_iff_isSupportedOutside,
    (Embedding.embeddingUpInt_areComplementary n₀ n₁ h).isSupportedOutside₁_iff]

end HasZeroMorphisms

section Abelian

variable [Abelian C] (K L : CochainComplex C ℤ)

/-- The cokernel sequence of the monomorphism `K.ιTruncLE n`. -/
/-
**CochainComplex.shortComplexTruncLE** 是 Mathlib 中的一个缩写定义，位于命名空间 `CochainComplex
`。
形式化陈述：shortComplexTruncLE (n : Int) : ShortComplex (CochainComplex C Int)
参数：n : Int。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.instIsTruncLENatIntEmbeddingUpIntLE`：∀ (p : ℤ), (ComplexSha
pe.embeddingUpIntLE p).IsTruncLE

--- 原说明 ---
The cokernel sequence of the monomorphism `K.ιTruncLE n`.
-/
noncomputable abbrev shortComplexTruncLE (n : ℤ) : ShortComplex (CochainComplex C ℤ) :=
  HomologicalComplex.shortComplexTruncLE K (embeddingUpIntLE n)
/-
**CochainComplex.shortComplexTruncLE_shortExact** 是 Mathlib 中的一个引理，位于命名空间 `Cocha
inComplex`。
形式化陈述：shortComplexTruncLE_shortExact (n : Int) : (K.shortComplexTruncLE n).Short
Exact
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.shortComplexTruncLE_shortExact`：shortComplexTruncLE_s
hortExact : (K.shortComplexTruncLE e).ShortExact where exact
· 使用定理 `ComplexShape.instIsTruncLENatIntEmbeddingUpIntLE`：∀ (p : ℤ), (ComplexSha
pe.embeddingUpIntLE p).IsTruncLE
-/
lemma shortComplexTruncLE_shortExact (n : ℤ) :
    (K.shortComplexTruncLE n).ShortExact := by
  apply HomologicalComplex.shortComplexTruncLE_shortExact

variable (n₀ n₁ : ℤ)

/-- The canonical morphism `(K.shortComplexTruncLE n₀).X₃ ⟶ K.truncGE n₁`. -/
/-
**CochainComplex.shortComplexTruncLEX** 是 Mathlib 中的一个缩写定义，位于命名空间 `CochainComple
x`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical morphism `(K.shortComplexTruncLE n₀).X₃ ⟶ K.truncGE n₁`.
-/
noncomputable abbrev shortComplexTruncLEX₃ToTruncGE (h : n₀ + 1 = n₁ := by lia) :
    (K.shortComplexTruncLE n₀).X₃ ⟶ K.truncGE n₁ :=
  HomologicalComplex.shortComplexTruncLEX₃ToTruncGE K
    (Embedding.embeddingUpInt_areComplementary n₀ n₁ h)

@[reassoc]
/-
**CochainComplex.g_shortComplexTruncLEX** 是 Mathlib 中的一个引理，位于命名空间 `CochainComple
x`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma g_shortComplexTruncLEX₃ToTruncGE (h : n₀ + 1 = n₁ := by lia) :
    (K.shortComplexTruncLE n₀).g ≫ K.shortComplexTruncLEX₃ToTruncGE n₀ n₁ h = K.πTruncGE n₁ := by
  apply HomologicalComplex.g_shortComplexTruncLEX₃ToTruncGE
/-
**CochainComplex.injective_opcycles** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
形式化陈述：injective_opcycles [Injective (K.X n₀)] [Injective (K.X n₁)] [K.IsStrictly
GE n₀] (hK : K.ExactAt n₀) (h : n₀ + 1 = n₁
参数：K.X n₀；K.X n₁；hK : K.ExactAt n₀。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomologicalComplex.d_pOpcycles`：d_pOpcycles [K.HasHomology j] : K.d i j 
≫ K.pOpcycles j = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `HomologicalComplex.exactAt_iff'`：exactAt_iff' (hi : c.prev j = i) (hk : 
c.next j = k) : K.ExactAt j ↔ (K.sc' i j k).Exact
· 使用定理 `CochainComplex.prev`：prev (α : Type*) [AddGroup α] [One α] (i : α) : (Co
mplexShape.up α).prev i = i - 1
· 使用定理 `CochainComplex.next`：next (α : Type*) [AddRightCancelSemigroup α] [One α
] (i : α) : (ComplexShape.up α).next i = i + 1
· 使用定理 `CategoryTheory.ShortComplex.Exact.mono_g`：∀ {C : Type u_1} [inst : Categ
oryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S : 
CategoryTheory.ShortComplex C}…
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_src`：eq_of_src (hX : IsZero X) (f g :
 X ⟶ Y) : f = g
· 使用引理 `CochainComplex.isZero_of_isStrictlyGE`：isZero_of_isStrictlyGE (n i : Int
) (hi : i < n
· 使用引理 `CategoryTheory.ShortComplex.exact_of_g_is_cokernel`：exact_of_g_is_cokern
el (hS : IsColimit (CokernelCofork.ofπ S.g S.zero)) [S.HasHomology] : S.Exact
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `HomologicalComplex.instEpiPOpcycles`：∀ {C : Type u_1} [inst : CategoryTh
eory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {ι : Type u_2} {c : Com…
· 使用定理 `CategoryTheory.Retract.injective`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {X Y : C} (h : CategoryTheory.Retract X Y)   [i : Category
Theory.Injective Y], C…
· 使用定理 `CategoryTheory.balanced_of_strongMonoCategory`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [CategoryTheory.StrongMonoCategory C],   Categor
yTheory.Balanced C
· 使用定理 `CategoryTheory.strongMonoCategory_of_regularMonoCategory`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.IsRegularMonoCateg
ory C],   CategoryTheory.StrongMonoCategory C
· 使用定理 `CategoryTheory.regularMonoCategoryOfNormalMonoCategory`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasZ
eroMorphisms C]   [CategoryTheory.IsNormalMo…
· 使用定理 `CategoryTheory.Abelian.toIsNormalMonoCategory`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryThe
ory.IsNormalMonoCategory C
· 使用定理 `CategoryTheory.ShortComplex.Splitting.s_g`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S :
 CategoryTheory.ShortComplex C}…
-/
lemma injective_opcycles [Injective (K.X n₀)] [Injective (K.X n₁)]
    [K.IsStrictlyGE n₀] (hK : K.ExactAt n₀) (h : n₀ + 1 = n₁ := by lia) :
    Injective (K.opcycles n₁) := by
  let S : ShortComplex C := ShortComplex.mk (K.d n₀ n₁) (K.pOpcycles n₁) (by simp)
  have : Mono S.f := by
    let T := K.sc' (n₀ - 1) n₀ n₁
    have hT : T.Exact := by
      rwa [← K.exactAt_iff' (n₀ - 1) n₀ n₁ (by simp) (by simpa)]
    exact hT.mono_g ((K.isZero_of_isStrictlyGE n₀ _).eq_of_src ..)
  have hS : S.ShortExact :=
    { exact := S.exact_of_g_is_cokernel (K.opcyclesIsCokernel n₀ n₁ (by simp [← h])) }
  exact Retract.injective
    { i := _, r := _, retract := (hS.splittingOfInjective).s_g }

end Abelian

end CochainComplex

