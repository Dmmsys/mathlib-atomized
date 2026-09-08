/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Xavier Roblot
-/
module

public import Mathlib.FieldTheory.PrimeField
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

/-!
# Totally real and totally complex number fields

This file defines the type of totally real and totally complex number fields.

## Main Definitions and Results

* `NumberField.IsTotallyReal`: a field `K` is totally real if all of its infinite places
  are real. In other words, the image of every ring homomorphism `K → ℂ` is a subset of `ℝ`.
* `NumberField.IsTotallyComplex`: a field `K` is totally complex if all of its infinite
  places are complex.
* `NumberField.maximalRealSubfield`: the maximal real subfield of `K`. It is totally real,
  see `NumberField.isTotallyReal_maximalRealSubfield`, and contains all the other totally real
  subfields of `K`, see `NumberField.IsTotallyReal.le_maximalRealSubfield`

## Tags

number field, infinite places, totally real, totally complex
-/

@[expose] public section

namespace NumberField

open InfinitePlace Module

section TotallyRealField

/-

## Totally real number fields

-/

/-- A field `K` is totally real if all of its infinite places are real. In other words,
the image of every ring homomorphism `K → ℂ` is a subset of `ℝ`. -/
/-
**NumberField.IsTotallyReal** 是 Mathlib 中的一个归纳类型，位于命名空间 `NumberField`。
形式化陈述：(K : Type u_1) → [Field K] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A field `K` is totally real if all of its infinite places are real. In other wor
ds,
the image of every ring homomorphism `K → ℂ` is a subset of `ℝ`.
-/
@[mk_iff] class IsTotallyReal (K : Type*) [Field K] where
  isReal : ∀ v : InfinitePlace K, v.IsReal

variable {F : Type*} [Field F] {K : Type*} [Field K]
/-
**NumberField.nrComplexPlaces_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `NumberField
`。
形式化陈述：nrComplexPlaces_eq_zero_iff [NumberField K] : nrComplexPlaces K = 0 ↔ IsTo
tallyReal K
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nrComplexPlaces_eq_zero_iff [NumberField K] :
    nrComplexPlaces K = 0 ↔ IsTotallyReal K := by
  simp [Fintype.card_eq_zero_iff, isEmpty_subtype, isTotallyReal_iff]
/-
**NumberField.IsTotallyReal.complexEmbedding_isReal** 是 Mathlib 中的一个定理，位于命名空间 `N
umberField.IsTotallyReal`。
形式化陈述：∀ {K : Type u_2} [inst : Field K] [NumberField.IsTotallyReal K] (φ : K →+*
 ℂ), NumberField.ComplexEmbedding.IsReal φ
参数：φ : K →+* ℂ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `NumberField.InfinitePlace.isReal_mk_iff`：isReal_mk_iff {φ : K ->+* Compl
ex} : IsReal (mk φ) ↔ ComplexEmbedding.IsReal φ
· 使用定理 `NumberField.IsTotallyReal.isReal`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField.IsTotallyReal K] (v : NumberField.InfinitePlace K), v.IsReal
-/
theorem IsTotallyReal.complexEmbedding_isReal [IsTotallyReal K] (φ : K →+* ℂ) :
    ComplexEmbedding.IsReal φ :=
  isReal_mk_iff.mp <| isReal (InfinitePlace.mk φ)

@[simp]
/-
**NumberField.IsTotallyReal.mult_eq** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.IsTot
allyReal`。
形式化陈述：∀ {K : Type u_2} [inst : Field K] [NumberField.IsTotallyReal K] (w : Numbe
rField.InfinitePlace K), w.mult = 1
参数：w : NumberField.InfinitePlace K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.InfinitePlace.mult_isReal`：mult_isReal (w : {w : InfinitePla
ce K // IsReal w}) : mult w.1 = 1
· 使用定理 `NumberField.IsTotallyReal.isReal`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField.IsTotallyReal K] (v : NumberField.InfinitePlace K), v.IsReal
-/
theorem IsTotallyReal.mult_eq [IsTotallyReal K] (w : InfinitePlace K) : mult w = 1 :=
  mult_isReal ⟨w, isReal w⟩
/-
**NumberField.IsTotallyReal.ofRingEquiv** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.I
sTotallyReal`。
形式化陈述：∀ {F : Type u_1} [inst : Field F] {K : Type u_2} [inst_1 : Field K] [Numbe
rField.IsTotallyReal F] (f : F ≃+* K),   NumberField.IsTotallyReal K
参数：f : F ≃+* K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用引理 `NumberField.InfinitePlace.isReal_comap_iff`：isReal_comap_iff (f : k ≃+* 
K) {w : InfinitePlace K} : IsReal (w.comap (f : k ->+* K)) ↔ IsReal w
· 使用定理 `NumberField.IsTotallyReal.isReal`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField.IsTotallyReal K] (v : NumberField.InfinitePlace K), v.IsReal
-/
theorem IsTotallyReal.ofRingEquiv [IsTotallyReal F] (f : F ≃+* K) : IsTotallyReal K where
  isReal _ := (isReal_comap_iff f).mp <| IsTotallyReal.isReal _

variable (F K) in
/-
**NumberField.IsTotallyReal.of_algebra** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.Is
TotallyReal`。
形式化陈述：∀ (F : Type u_1) [inst : Field F] (K : Type u_2) [inst_1 : Field K] [Numbe
rField.IsTotallyReal K] [inst_3 : Algebra F K]   [Algebra.IsAlgebraic F K], Numb
erField.IsTotallyReal F
参数：F : Type u_1；K : Type u_2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NumberField.InfinitePlace.comap_surjective`：comap_surjective [Algebra k 
K] [Algebra.IsAlgebraic k K] : Function.Surjective (comap · (algebraMap k K))
· 使用定理 `NumberField.InfinitePlace.IsReal.comap`：∀ {k : Type u_1} [inst : Field k
] {K : Type u_2} [inst_1 : Field K] (f : k →+* K) {w : NumberField.InfinitePlace
 K},   w.IsReal → (w.comap f…
· 使用定理 `NumberField.IsTotallyReal.isReal`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField.IsTotallyReal K] (v : NumberField.InfinitePlace K), v.IsReal
-/
theorem IsTotallyReal.of_algebra [IsTotallyReal K] [Algebra F K] [Algebra.IsAlgebraic F K] :
    IsTotallyReal F where
  isReal w := by
    obtain ⟨W, rfl⟩ : ∃ W : InfinitePlace K, W.comap (algebraMap F K) = w := comap_surjective w
    exact IsReal.comap _ (IsTotallyReal.isReal W)
/-
**NumberField.isTotallyReal_iff_ofRingEquiv** 是 Mathlib 中的一个定理，位于命名空间 `NumberFie
ld`。
形式化陈述：isTotallyReal_iff_ofRingEquiv (f : F ≃+* K) : IsTotallyReal F ↔ IsTotallyR
eal K
参数：f : F ≃+* K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.IsTotallyReal.ofRingEquiv`：∀ {F : Type u_1} [inst : Field F]
 {K : Type u_2} [inst_1 : Field K] [NumberField.IsTotallyReal F] (f : F ≃+* K), 
  NumberField.IsTotallyReal…
-/
theorem isTotallyReal_iff_ofRingEquiv (f : F ≃+* K) : IsTotallyReal F ↔ IsTotallyReal K :=
  ⟨fun _ ↦ .ofRingEquiv f, fun _ ↦ .ofRingEquiv f.symm⟩

@[simp]
/-
**NumberField.isTotallyReal_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `NumberField`。
形式化陈述：isTotallyReal_top_iff : IsTotallyReal (⊤ : Subfield K) ↔ IsTotallyReal K
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.isTotallyReal_iff_ofRingEquiv`：isTotallyReal_iff_ofRingEquiv
 (f : F ≃+* K) : IsTotallyReal F ↔ IsTotallyReal K
-/
theorem isTotallyReal_top_iff : IsTotallyReal (⊤ : Subfield K) ↔ IsTotallyReal K :=
  isTotallyReal_iff_ofRingEquiv Subfield.topEquiv
/-
**NumberField.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsTotallyReal K] [CharZero K] (F : IntermediateField ℚ K) [Algebra.IsAlgebraic F K] :
    IsTotallyReal F :=
  IsTotallyReal.of_algebra F K
/-
**NumberField.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsTotallyReal K] (F : Subfield K) [Algebra.IsAlgebraic F K] : IsTotallyReal F :=
  IsTotallyReal.of_algebra F K

variable (K)

@[simp]
/-
**NumberField.IsTotallyReal.nrComplexPlaces_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `N
umberField.IsTotallyReal`。
形式化陈述：∀ (K : Type u_2) [inst : Field K] [inst_1 : NumberField K] [h : NumberFiel
d.IsTotallyReal K],   NumberField.InfinitePlace.nrComplexPlaces K = 0
参数：K : Type u_2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NumberField.nrComplexPlaces_eq_zero_iff`：nrComplexPlaces_eq_zero_iff [Nu
mberField K] : nrComplexPlaces K = 0 ↔ IsTotallyReal K
-/
theorem IsTotallyReal.nrComplexPlaces_eq_zero [NumberField K] [h : IsTotallyReal K] :
    nrComplexPlaces K = 0 :=
  nrComplexPlaces_eq_zero_iff.mpr h
/-
**NumberField.IsTotallyReal.finrank** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.IsTot
allyReal`。
形式化陈述：∀ (K : Type u_2) [inst : Field K] [inst_1 : NumberField K] [h : NumberFiel
d.IsTotallyReal K],   Module.finrank ℚ K = NumberField.InfinitePlace.nrRealPlace
s K
参数：K : Type u_2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.InfinitePlace.card_add_two_mul_card_eq_rank`：card_add_two_mu
l_card_eq_rank : nrRealPlaces K + 2 * nrComplexPlaces K = finrank Rat K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NumberField.nrComplexPlaces_eq_zero_iff`：nrComplexPlaces_eq_zero_iff [Nu
mberField K] : nrComplexPlaces K = 0 ↔ IsTotallyReal K
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
protected theorem IsTotallyReal.finrank [NumberField K] [h : IsTotallyReal K] :
    finrank ℚ K = nrRealPlaces K := by
  rw [← card_add_two_mul_card_eq_rank, nrComplexPlaces_eq_zero_iff.mpr h, mul_zero, add_zero]
/-
**NumberField.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsTotallyReal ℚ where
  isReal v := by
    rw [Subsingleton.elim v Rat.infinitePlace]
    exact Rat.isReal_infinitePlace
/-
**NumberField.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsTotallyReal K] :
    IsTotallyReal (⊤ : Subfield K) := isTotallyReal_top_iff.mpr ‹_›
/-
**NumberField._root_.IntermediateField.isTotallyReal_bot** 是 Mathlib 中的一个实例，位于命名
空间 `NumberField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.IntermediateField.isTotallyReal_bot [CharZero K] :
    IsTotallyReal (⊥ : IntermediateField ℚ K) :=
  IsTotallyReal.ofRingEquiv (IntermediateField.botEquiv ℚ K).symm.toRingEquiv
/-
**NumberField._root_.Subfield.isTotallyReal_bot** 是 Mathlib 中的一个实例，位于命名空间 `Numbe
rField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.Subfield.isTotallyReal_bot [CharZero K] :
    IsTotallyReal (⊥ : Subfield K) := by
  rw [Subfield.bot_eq_of_charZero]
  exact IsTotallyReal.ofRingEquiv (algebraMap ℚ K).rangeRestrictFieldEquiv

section maximalRealSubfield

open ComplexEmbedding

/--
The maximal real subfield of `K`. It is totally real,
see `NumberField.isTotallyReal_maximalRealSubfield`, and contains all the other totally real
subfields of `K`, see `NumberField.IsTotallyReal.le_maximalRealSubfield`.
-/
/-
**NumberField.maximalRealSubfield** 是 Mathlib 中的一个定义，位于命名空间 `NumberField`。
形式化陈述：maximalRealSubfield : Subfield K where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The maximal real subfield of `K`. It is totally real,
see `NumberField.isTotallyReal_maximalRealSubfield`, and contains all the other 
totally real
subfields of `K`, see `NumberField.IsTotallyReal.le_maximalRealSubfield`.
-/
def maximalRealSubfield : Subfield K where
  carrier := {x | ∀ φ : K →+* ℂ, star (φ x) = φ x}
  mul_mem' hx hy _ := by rw [map_mul, star_mul, hx, hy, mul_comm]
  one_mem' := by simp
  add_mem' hx hy _ := by rw [map_add, star_add, hx, hy]
  zero_mem' := by simp
  neg_mem' := by simp
  inv_mem' := by simp

variable {K}
/-
**NumberField.mem_maximalRealSubfield_iff** 是 Mathlib 中的一个定理，位于命名空间 `NumberField
`。
形式化陈述：mem_maximalRealSubfield_iff (x : K) : x in maximalRealSubfield K ↔ forall 
φ : K ->+* Complex, star (φ x) = φ x
参数：x : K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_maximalRealSubfield_iff (x : K) :
    x ∈ maximalRealSubfield K ↔ ∀ φ : K →+* ℂ, star (φ x) = φ x := .rfl
/-
**NumberField.IsTotallyReal.le_maximalRealSubfield** 是 Mathlib 中的一个定理，位于命名空间 `Nu
mberField.IsTotallyReal`。
形式化陈述：∀ {K : Type u_2} [inst : Field K] (E : Subfield K) [NumberField.IsTotallyR
eal ↥E], E ≤ NumberField.maximalRealSubfield K
参数：E : Subfield K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `RCLike.star_def`：star_def : (Star.star : K -> K) = conj
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.ComplexEmbedding.conjugate_coe_eq`：conjugate_coe_eq (φ : K -
>+* Complex) (x : K) : (conjugate φ) x = conj (φ x)
· 使用定理 `RingHom.congr_fun`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring
 α} {x_1 : NonAssocSemiring β} {f g : α →+* β},   f = g → ∀ (x_2 : α), f x_2 = g
 x_2
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NumberField.ComplexEmbedding.isReal_iff`：isReal_iff {φ : K ->+* Complex}
 : IsReal φ ↔ conjugate φ = φ
· 使用引理 `NumberField.InfinitePlace.isReal_mk_iff`：isReal_mk_iff {φ : K ->+* Compl
ex} : IsReal (mk φ) ↔ ComplexEmbedding.IsReal φ
· 使用定理 `NumberField.IsTotallyReal.isReal`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField.IsTotallyReal K] (v : NumberField.InfinitePlace K), v.IsReal
-/
theorem IsTotallyReal.le_maximalRealSubfield (E : Subfield K) [IsTotallyReal E] :
    E ≤ maximalRealSubfield K := by
  intro x hx φ
  rw [show φ x = (φ.comp E.subtype) ⟨x, hx⟩ by simp, RCLike.star_def, ← conjugate_coe_eq]
  refine RingHom.congr_fun ?_ _
  exact ComplexEmbedding.isReal_iff.mp <| isReal_mk_iff.mp <| isReal _

@[simp]
/-
**NumberField.IsTotallyReal.maximalRealSubfield_eq_top** 是 Mathlib 中的一个定理，位于命名空间
 `NumberField.IsTotallyReal`。
形式化陈述：∀ {K : Type u_2} [inst : Field K] [NumberField.IsTotallyReal K], NumberFie
ld.maximalRealSubfield K = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `NumberField.IsTotallyReal.le_maximalRealSubfield`：∀ {K : Type u_2} [inst
 : Field K] (E : Subfield K) [NumberField.IsTotallyReal ↥E], E ≤ NumberField.max
imalRealSubfield K
· 使用定理 `NumberField.instIsTotallyRealSubtypeMemSubfieldTop`：∀ (K : Type u_2) [in
st : Field K] [NumberField.IsTotallyReal K], NumberField.IsTotallyReal ↥⊤
-/
theorem IsTotallyReal.maximalRealSubfield_eq_top [IsTotallyReal K] :
    maximalRealSubfield K = ⊤ :=
  top_unique <| NumberField.IsTotallyReal.le_maximalRealSubfield _

variable [CharZero K] [Algebra.IsAlgebraic ℚ K]

local instance (k : Subfield K) : Algebra.IsAlgebraic k K :=
  Algebra.IsAlgebraic.tower_top k (K := ℚ) (A := K)
/-
**NumberField.isTotallyReal_maximalRealSubfield** 是 Mathlib 中的一个实例，位于命名空间 `Numbe
rField`。
形式化陈述：isTotallyReal_maximalRealSubfield : IsTotallyReal (maximalRealSubfield K) 
where isReal w
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.InfinitePlace.isReal_iff`：isReal_iff {w : InfinitePlace K} :
 IsReal w ↔ ComplexEmbedding.IsReal (embedding w)
· 使用定理 `NumberField.ComplexEmbedding.isReal_iff`：isReal_iff {φ : K ->+* Complex}
 : IsReal φ ↔ conjugate φ = φ
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `RingHom.star_apply`：RingHom.star_apply {S : Type*} [NonAssocSemiring S] 
(f : S ->+* R) (s : S) : star f s = star (f s)
· 使用定理 `NumberField.instIsAlgebraicSubtypeMemSubfield`：∀ {K : Type u_2} [inst : 
Field K] [inst_1 : CharZero K] [Algebra.IsAlgebraic ℚ K] (k : Subfield K),   Alg
ebra.IsAlgebraic (↥k) K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.ComplexEmbedding.lift_algebraMap_apply`：lift_algebraMap_appl
y [Algebra k K] [Algebra.IsAlgebraic k K] (φ : k ->+* Complex) (x : k) : lift K 
φ (algebraMap k K x) = φ x
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
instance isTotallyReal_maximalRealSubfield :
    IsTotallyReal (maximalRealSubfield K) where
  isReal w := by
    rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    ext x
    rw [RingHom.star_apply, ← lift_algebraMap_apply K w.embedding]
    exact x.prop _
/-
**NumberField.isTotallyReal_iff_le_maximalRealSubfield** 是 Mathlib 中的一个定理，位于命名空间
 `NumberField`。
形式化陈述：isTotallyReal_iff_le_maximalRealSubfield {E : Subfield K} : IsTotallyReal 
E ↔ E <= maximalRealSubfield K
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.IsTotallyReal.le_maximalRealSubfield`：∀ {K : Type u_2} [inst
 : Field K] (E : Subfield K) [NumberField.IsTotallyReal ↥E], E ≤ NumberField.max
imalRealSubfield K
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Algebra.IsAlgebraic.tower_bot`：Algebra.IsAlgebraic.tower_bot (K L A : Ty
pe*) [CommRing K] [Field L] [Ring A] [Algebra K L] [Algebra L A] [Algebra K A] [
IsScalarTower K L A…
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `NumberField.instIsAlgebraicSubtypeMemSubfield`：∀ {K : Type u_2} [inst : 
Field K] [inst_1 : CharZero K] [Algebra.IsAlgebraic ℚ K] (k : Subfield K),   Alg
ebra.IsAlgebraic (↥k) K
· 使用定理 `NumberField.IsTotallyReal.of_algebra`：∀ (F : Type u_1) [inst : Field F] 
(K : Type u_2) [inst_1 : Field K] [NumberField.IsTotallyReal K] [inst_3 : Algebr
a F K]   [Algebra.IsAlgebr…
-/
theorem isTotallyReal_iff_le_maximalRealSubfield {E : Subfield K} :
    IsTotallyReal E ↔ E ≤ maximalRealSubfield K := by
  refine ⟨fun h ↦ h.le_maximalRealSubfield, fun h ↦ ?_⟩
  let _ : Algebra E (maximalRealSubfield K) := RingHom.toAlgebra <| Subfield.inclusion h
  have : IsScalarTower E (maximalRealSubfield K) K := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.IsAlgebraic E (maximalRealSubfield K) :=
      Algebra.IsAlgebraic.tower_bot E (maximalRealSubfield K) K
  exact IsTotallyReal.of_algebra _ (maximalRealSubfield K)
/-
**NumberField.isTotallyReal_sup** 是 Mathlib 中的一个实例，位于命名空间 `NumberField`。
形式化陈述：isTotallyReal_sup {E F : Subfield K} [hE : IsTotallyReal E] [hF : IsTotall
yReal F] : IsTotallyReal (E ⊔ F : Subfield K)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.isTotallyReal_iff_le_maximalRealSubfield`：isTotallyReal_iff_
le_maximalRealSubfield {E : Subfield K} : IsTotallyReal E ↔ E <= maximalRealSubf
ield K
· 使用定理 `sup_le_iff`：sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
instance isTotallyReal_sup {E F : Subfield K} [hE : IsTotallyReal E] [hF : IsTotallyReal F] :
    IsTotallyReal (E ⊔ F : Subfield K) := by
  rw [isTotallyReal_iff_le_maximalRealSubfield, sup_le_iff,
    ← isTotallyReal_iff_le_maximalRealSubfield, ← isTotallyReal_iff_le_maximalRealSubfield]
  exact ⟨hE, hF⟩
/-
**NumberField.isTotallyReal_iSup** 是 Mathlib 中的一个实例，位于命名空间 `NumberField`。
形式化陈述：isTotallyReal_iSup {ι : Type*} {k : ι -> Subfield K} [forall i, IsTotallyR
eal (k i)] : IsTotallyReal (⨆ i, k i : Subfield K)
参数：k i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_of_empty`：iSup_of_empty [IsEmpty ι] (f : ι -> α) : iSup f = ⊥
· 使用定理 `Subfield.isTotallyReal_bot`：∀ (K : Type u_2) [inst : Field K] [CharZero 
K], NumberField.IsTotallyReal ↥⊥
· 使用定理 `NumberField.isTotallyReal_iff_le_maximalRealSubfield`：isTotallyReal_iff_
le_maximalRealSubfield {E : Subfield K} : IsTotallyReal E ↔ E <= maximalRealSubf
ield K
· 使用定理 `iSup_le_iff`：iSup_le_iff : iSup f <= a ↔ forall i, f i <= a
· 使用定理 `NumberField.IsTotallyReal.le_maximalRealSubfield`：∀ {K : Type u_2} [inst
 : Field K] (E : Subfield K) [NumberField.IsTotallyReal ↥E], E ≤ NumberField.max
imalRealSubfield K
-/
instance isTotallyReal_iSup {ι : Type*} {k : ι → Subfield K} [∀ i, IsTotallyReal (k i)] :
    IsTotallyReal (⨆ i, k i : Subfield K) := by
  obtain hι | ⟨⟨i⟩⟩ := isEmpty_or_nonempty ι
  · rw [iSup_of_empty]
    infer_instance
  · rw [isTotallyReal_iff_le_maximalRealSubfield, iSup_le_iff]
    exact fun i ↦ IsTotallyReal.le_maximalRealSubfield (k i)
/-
**NumberField.maximalRealSubfield_eq_top_iff_isTotallyReal** 是 Mathlib 中的一个定理，位于
命名空间 `NumberField`。
形式化陈述：maximalRealSubfield_eq_top_iff_isTotallyReal : maximalRealSubfield K = ⊤ ↔
 IsTotallyReal K where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsIntegral.tower_top`：Algebra.IsIntegral.tower_top [Algebra R S]
 [Algebra R T] [Algebra S T] [IsScalarTower R S T] [h : Algebra.IsIntegral R T] 
: Algebra.IsIntegr…
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.isTotallyReal_top_iff`：isTotallyReal_top_iff : IsTotallyReal
 (⊤ : Subfield K) ↔ IsTotallyReal K
· 使用定理 `NumberField.isTotallyReal_iff_le_maximalRealSubfield`：isTotallyReal_iff_
le_maximalRealSubfield {E : Subfield K} : IsTotallyReal E ↔ E <= maximalRealSubf
ield K
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `NumberField.IsTotallyReal.maximalRealSubfield_eq_top`：∀ {K : Type u_2} [
inst : Field K] [NumberField.IsTotallyReal K], NumberField.maximalRealSubfield K
 = ⊤
-/
theorem maximalRealSubfield_eq_top_iff_isTotallyReal :
    maximalRealSubfield K = ⊤ ↔ IsTotallyReal K where
  mp h := by
    have : Algebra.IsIntegral (⊤ : Subfield K) K := Algebra.IsIntegral.tower_top ℚ
    rw [← isTotallyReal_top_iff, isTotallyReal_iff_le_maximalRealSubfield, h]
  mpr _ := IsTotallyReal.maximalRealSubfield_eq_top

end maximalRealSubfield

end TotallyRealField

section TotallyComplexField

/-
## Totally complex number fields
-/

open InfinitePlace

/--
A field `K` is totally complex if all of its infinite places are complex.
-/
/-
**NumberField.IsTotallyComplex** 是 Mathlib 中的一个归纳类型，位于命名空间 `NumberField`。
形式化陈述：(K : Type u_1) → [Field K] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A field `K` is totally complex if all of its infinite places are complex.
-/
@[mk_iff] class IsTotallyComplex (K : Type*) [Field K] where
  isComplex : ∀ v : InfinitePlace K, v.IsComplex

variable (F : Type*) [Field F] {K : Type*} [Field K] [Algebra F K]
/-
**NumberField.nrRealPlaces_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `NumberField`。
形式化陈述：nrRealPlaces_eq_zero_iff [NumberField K] : nrRealPlaces K = 0 ↔ IsTotallyC
omplex K
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nrRealPlaces_eq_zero_iff [NumberField K] :
    nrRealPlaces K = 0 ↔ IsTotallyComplex K := by
  simp [Fintype.card_eq_zero_iff, isEmpty_subtype, isTotallyComplex_iff]
/-
**NumberField.IsTotallyComplex.complexEmbedding_not_isReal** 是 Mathlib 中的一个定理，位于
命名空间 `NumberField.IsTotallyComplex`。
形式化陈述：∀ {K : Type u_2} [inst : Field K] [NumberField.IsTotallyComplex K] (φ : K 
→+* ℂ), ¬NumberField.ComplexEmbedding.IsReal φ
参数：φ : K →+* ℂ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `NumberField.InfinitePlace.isReal_mk_iff`：isReal_mk_iff {φ : K ->+* Compl
ex} : IsReal (mk φ) ↔ ComplexEmbedding.IsReal φ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NumberField.InfinitePlace.not_isReal_iff_isComplex`：not_isReal_iff_isCom
plex {w : InfinitePlace K} : ¬IsReal w ↔ IsComplex w
· 使用定理 `NumberField.IsTotallyComplex.isComplex`：∀ {K : Type u_1} {inst : Field K
} [self : NumberField.IsTotallyComplex K] (v : NumberField.InfinitePlace K), v.I
sComplex
-/
theorem IsTotallyComplex.complexEmbedding_not_isReal [IsTotallyComplex K] (φ : K →+* ℂ) :
    ¬ ComplexEmbedding.IsReal φ :=
  isReal_mk_iff.not.mp <| not_isReal_iff_isComplex.mpr <| isComplex (InfinitePlace.mk φ)

@[simp]
/-
**NumberField.IsTotallyComplex.mult_eq** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.Is
TotallyComplex`。
形式化陈述：∀ {K : Type u_2} [inst : Field K] [NumberField.IsTotallyComplex K] (w : Nu
mberField.InfinitePlace K), w.mult = 2
参数：w : NumberField.InfinitePlace K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.InfinitePlace.mult_isComplex`：mult_isComplex (w : {w : Infin
itePlace K // IsComplex w}) : mult w.1 = 2
· 使用定理 `NumberField.IsTotallyComplex.isComplex`：∀ {K : Type u_1} {inst : Field K
} [self : NumberField.IsTotallyComplex K] (v : NumberField.InfinitePlace K), v.I
sComplex
-/
theorem IsTotallyComplex.mult_eq [IsTotallyComplex K] (w : InfinitePlace K) : mult w = 2 :=
  mult_isComplex ⟨w, isComplex w⟩

variable (K)
/-
**NumberField.isTotallyComplex_of_algebra** 是 Mathlib 中的一个定理，位于命名空间 `NumberField
`。
形式化陈述：isTotallyComplex_of_algebra [IsTotallyComplex F] : IsTotallyComplex K wher
e isComplex _
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.InfinitePlace.IsComplex.of_comap`：∀ {k : Type u_1} [inst : F
ield k] {K : Type u_2} [inst_1 : Field K] (f : k →+* K) {w : NumberField.Infinit
ePlace K},   (w.comap f).IsComplex…
· 使用定理 `NumberField.IsTotallyComplex.isComplex`：∀ {K : Type u_1} {inst : Field K
} [self : NumberField.IsTotallyComplex K] (v : NumberField.InfinitePlace K), v.I
sComplex
-/
theorem isTotallyComplex_of_algebra [IsTotallyComplex F] :
    IsTotallyComplex K where
  isComplex _ := IsComplex.of_comap (algebraMap F K) <| IsTotallyComplex.isComplex _

@[simp]
/-
**NumberField.IsTotallyComplex.nrRealPlaces_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `N
umberField.IsTotallyComplex`。
形式化陈述：∀ (K : Type u_2) [inst : Field K] [inst_1 : NumberField K] [h : NumberFiel
d.IsTotallyComplex K],   NumberField.InfinitePlace.nrRealPlaces K = 0
参数：K : Type u_2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NumberField.nrRealPlaces_eq_zero_iff`：nrRealPlaces_eq_zero_iff [NumberFi
eld K] : nrRealPlaces K = 0 ↔ IsTotallyComplex K
-/
theorem IsTotallyComplex.nrRealPlaces_eq_zero [NumberField K] [h : IsTotallyComplex K] :
    nrRealPlaces K = 0 :=
  nrRealPlaces_eq_zero_iff.mpr h
/-
**NumberField.IsTotallyComplex.finrank** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.Is
TotallyComplex`。
形式化陈述：∀ (K : Type u_2) [inst : Field K] [inst_1 : NumberField K] [h : NumberFiel
d.IsTotallyComplex K],   Module.finrank ℚ K = 2 * NumberField.InfinitePlace.nrCo
mplexPlaces K
参数：K : Type u_2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.InfinitePlace.card_add_two_mul_card_eq_rank`：card_add_two_mu
l_card_eq_rank : nrRealPlaces K + 2 * nrComplexPlaces K = finrank Rat K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NumberField.nrRealPlaces_eq_zero_iff`：nrRealPlaces_eq_zero_iff [NumberFi
eld K] : nrRealPlaces K = 0 ↔ IsTotallyComplex K
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
protected theorem IsTotallyComplex.finrank [NumberField K] [h : IsTotallyComplex K] :
    finrank ℚ K = 2 * nrComplexPlaces K := by
  rw [← card_add_two_mul_card_eq_rank, nrRealPlaces_eq_zero_iff.mpr h, zero_add]

end TotallyComplexField

end NumberField

