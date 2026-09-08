/-
Copyright (c) 2025 Peter Nelson and Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Junyan Xu
-/
module

public import Mathlib.Combinatorics.Matroid.Map
public import Mathlib.Combinatorics.Matroid.Rank.ENat
public import Mathlib.Combinatorics.Matroid.Rank.Finite
public import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Cardinal-valued rank

In a finitary matroid, all bases have the same cardinality.
In fact, something stronger holds: if each of `I` and `J` is a basis for a set `X`,
then `#(I \ J) = #(J \ I)` and (consequently) `#I = #J`.
This file introduces a typeclass `InvariantCardinalRank` that applies to any matroid
such that this property holds for all `I`, `J` and `X`.

A matroid satisfying this condition has a well-defined cardinality-valued rank function,
both for itself and all its minors.

## Main Declarations

* `Matroid.InvariantCardinalRank` : a typeclass capturing the idea that a matroid and all its minors
  have a well-behaved cardinal-valued rank function.
* `Matroid.cRank M` is the supremum of the cardinalities of the bases of matroid `M`.
* `Matroid.cRk M X` is the supremum of the cardinalities of the bases of a set `X` in a matroid `M`.
* `invariantCardinalRank_of_finitary` is the instance
  showing that `Finitary` matroids are `InvariantCardinalRank`.
* `cRk_inter_add_cRk_union_le` states that cardinal rank is submodular.

## Notes

It is not (provably) the case that all matroids are `InvariantCardinalRank`,
since the equicardinality of bases in general matroids is independent of ZFC
(see the module docstring of `Mathlib/Combinatorics/Matroid/Basic.lean`).
Lemmas like `Matroid.Base.cardinalMk_sdiff_comm` become true for all matroids
only if they are weakened by replacing `Cardinal.mk` with the cruder `ℕ∞`-valued `Set.encard`.
The `ℕ∞`-valued rank and rank functions `Matroid.eRank` and `Matroid.eRk`,
which have a more unconditionally strong API,
are developed in `Mathlib/Combinatorics/Matroid/Rank/ENat.lean`.

## Implementation Details

Since the functions `cRank` and `cRk` are defined as suprema,
independently of the `Matroid.InvariantCardinalRank` typeclass,
they are well-defined for all matroids.
However, for matroids that do not satisfy `InvariantCardinalRank`, they are badly behaved.
For instance, in general `cRk` is not submodular,
and its value may differ on a set `X` and the closure of `X`.
We state and prove theorems without `InvariantCardinalRank` whenever possible,
which sometime makes their proofs longer than they would be with the instance.

## TODO

* Higgs' theorem : if the generalized continuum hypothesis holds,
  then every matroid is `InvariantCardinalRank`.

-/

@[expose] public section

universe u v

variable {α : Type u} {β : Type v} {f : α → β} {M : Matroid α} {I J B B' X Y : Set α}

open Cardinal Set

namespace Matroid

section Rank

variable {κ : Cardinal}

/-- The rank (supremum of the cardinalities of bases) of a matroid `M` as a `Cardinal`.
See `Matroid.eRank` for a better-behaved `ℕ∞`-valued version. -/
/-
**Matroid.cRank** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：cRank (M : Matroid α)
参数：M : Matroid α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The rank (supremum of the cardinalities of bases) of a matroid `M` as a `Cardina
l`.
See `Matroid.eRank` for a better-behaved `ℕ∞`-valued version.
-/
noncomputable def cRank (M : Matroid α) := ⨆ B : {B // M.IsBase B}, #B

/-- The rank (supremum of the cardinalities of bases) of a set `X` in a matroid `M`,
as a `Cardinal`. See `Matroid.eRk` for a better-behaved `ℕ∞`-valued version. -/
/-
**Matroid.cRk** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：cRk (M : Matroid α) (X : Set α)
参数：M : Matroid α；X : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The rank (supremum of the cardinalities of bases) of a set `X` in a matroid `M`,
as a `Cardinal`. See `Matroid.eRk` for a better-behaved `ℕ∞`-valued version.
-/
noncomputable def cRk (M : Matroid α) (X : Set α) := (M ↾ X).cRank
/-
**Matroid.IsBase.cardinalMk_le_cRank** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase`。
形式化陈述：∀ {α : Type u} {M : Matroid α} {B : Set α}, M.IsBase B → Cardinal.mk ↑B ≤ 
M.cRank
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f
· 使用定理 `Cardinal.bddAbove_of_small`：bddAbove_of_small {s : Set Cardinal.{u}} [h 
: Small.{u} s] : BddAbove s
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
theorem IsBase.cardinalMk_le_cRank (hB : M.IsBase B) : #B ≤ M.cRank :=
  le_ciSup (f := fun B : {B // M.IsBase B} ↦ #B.1) bddAbove_of_small ⟨B, hB⟩
/-
**Matroid.Indep.cardinalMk_le_cRank** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u} {M : Matroid α} {I : Set α}, M.Indep I → Cardinal.mk ↑I ≤ M
.cRank
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.exists_isBase_superset`：∀ {α : Type u_1} {M : Matroid α} {
I : Set α}, M.Indep I → ∃ B, M.IsBase B ∧ I ⊆ B
· 使用定理 `le_ciSup_of_le`：le_ciSup_of_le {f : ι -> α} (H : BddAbove (range f)) (c 
: ι) (h : a <= f c) : a <= iSup f
· 使用定理 `Cardinal.bddAbove_of_small`：bddAbove_of_small {s : Set Cardinal.{u}} [h 
: Small.{u} s] : BddAbove s
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Cardinal.mk_le_mk_of_subset`：mk_le_mk_of_subset {α} {s t : Set α} (h : s
 subseteq t) : #s <= #t
-/
theorem Indep.cardinalMk_le_cRank (ind : M.Indep I) : #I ≤ M.cRank :=
  have ⟨B, isBase, hIB⟩ := ind.exists_isBase_superset
  le_ciSup_of_le bddAbove_of_small ⟨B, isBase⟩ (mk_le_mk_of_subset hIB)
/-
**Matroid.cRank_eq_iSup_cardinalMk_indep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：cRank_eq_iSup_cardinalMk_indep : M.cRank = ⨆ I : {I // M.Indep I}, #I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `ciSup_le'`：ciSup_le' {f : ι -> α} {a : α} (h : forall i, f i <= a) : ⨆ i
, f i <= a
· 使用定理 `le_ciSup_of_le`：le_ciSup_of_le {f : ι -> α} (H : BddAbove (range f)) (c 
: ι) (h : a <= f c) : a <= iSup f
· 使用定理 `Cardinal.bddAbove_of_small`：bddAbove_of_small {s : Set Cardinal.{u}} [h 
: Small.{u} s] : BddAbove s
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Matroid.IsBase.indep`：∀ {α : Type u_1} {M : Matroid α} {B : Set α}, M.Is
Base B → M.Indep B
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Matroid.Indep.exists_isBase_superset`：∀ {α : Type u_1} {M : Matroid α} {
I : Set α}, M.Indep I → ∃ B, M.IsBase B ∧ I ⊆ B
· 使用定理 `Cardinal.mk_le_mk_of_subset`：mk_le_mk_of_subset {α} {s t : Set α} (h : s
 subseteq t) : #s <= #t
-/
theorem cRank_eq_iSup_cardinalMk_indep : M.cRank = ⨆ I : {I // M.Indep I}, #I :=
  (ciSup_le' fun B ↦ le_ciSup_of_le bddAbove_of_small ⟨B, B.2.indep⟩ <| by rfl).antisymm <|
    ciSup_le' fun I ↦
      have ⟨B, isBase, hIB⟩ := I.2.exists_isBase_superset
      le_ciSup_of_le bddAbove_of_small ⟨B, isBase⟩ (mk_le_mk_of_subset hIB)
/-
**Matroid.IsBasis'.cardinalMk_le_cRk** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis'
`。
形式化陈述：∀ {α : Type u} {M : Matroid α} {I X : Set α}, M.IsBasis' I X → Cardinal.mk
 ↑I ≤ M.cRk X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBase.cardinalMk_le_cRank`：∀ {α : Type u} {M : Matroid α} {B : 
Set α}, M.IsBase B → Cardinal.mk ↑B ≤ M.cRank
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matroid.isBase_restrict_iff'`：isBase_restrict_iff' : (M ↾ X).IsBase I ↔ 
M.IsBasis' I X
-/
theorem IsBasis'.cardinalMk_le_cRk (hIX : M.IsBasis' I X) : #I ≤ M.cRk X :=
  (isBase_restrict_iff'.2 hIX).cardinalMk_le_cRank
/-
**Matroid.IsBasis.cardinalMk_le_cRk** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis`。
形式化陈述：∀ {α : Type u} {M : Matroid α} {I X : Set α}, M.IsBasis I X → Cardinal.mk 
↑I ≤ M.cRk X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis'.cardinalMk_le_cRk`：∀ {α : Type u} {M : Matroid α} {I X 
: Set α}, M.IsBasis' I X → Cardinal.mk ↑I ≤ M.cRk X
· 使用定理 `Matroid.IsBasis.isBasis'`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}
, M.IsBasis I X → M.IsBasis' I X
-/
theorem IsBasis.cardinalMk_le_cRk (hIX : M.IsBasis I X) : #I ≤ M.cRk X :=
  hIX.isBasis'.cardinalMk_le_cRk
/-
**Matroid.cRank_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：cRank_le_iff : M.cRank <= κ ↔ forall ⦃B⦄, M.IsBase B -> #B <= κ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Matroid.IsBase.cardinalMk_le_cRank`：∀ {α : Type u} {M : Matroid α} {B : 
Set α}, M.IsBase B → Cardinal.mk ↑B ≤ M.cRank
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用定理 `Matroid.instNonemptySubtypeSetIsBase`：∀ {α : Type u_1} (M : Matroid α), 
Nonempty { B // M.IsBase B }
-/
theorem cRank_le_iff : M.cRank ≤ κ ↔ ∀ ⦃B⦄, M.IsBase B → #B ≤ κ :=
  ⟨fun h _ hB ↦ (hB.cardinalMk_le_cRank.trans h), fun h ↦ ciSup_le fun ⟨_, hB⟩ ↦ h hB⟩
/-
**Matroid.cRk_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：cRk_le_iff : M.cRk X <= κ ↔ forall ⦃I⦄, M.IsBasis' I X -> #I <= κ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cRk_le_iff : M.cRk X ≤ κ ↔ ∀ ⦃I⦄, M.IsBasis' I X → #I ≤ κ := by
  simp_rw [cRk, cRank_le_iff, isBase_restrict_iff']
/-
**Matroid.Indep.cardinalMk_le_cRk_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.I
ndep`。
形式化陈述：∀ {α : Type u} {M : Matroid α} {I X : Set α}, M.Indep I → I ⊆ X → Cardinal
.mk ↑I ≤ M.cRk X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.subset_isBasis'_of_subset`：∀ {α : Type u_1} {M : Matroid α
} {I X : Set α}, M.Indep I → I ⊆ X → ∃ J, M.IsBasis' J X ∧ I ⊆ J
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.mk_le_mk_of_subset`：mk_le_mk_of_subset {α} {s t : Set α} (h : s
 subseteq t) : #s <= #t
· 使用定理 `Matroid.IsBasis'.cardinalMk_le_cRk`：∀ {α : Type u} {M : Matroid α} {I X 
: Set α}, M.IsBasis' I X → Cardinal.mk ↑I ≤ M.cRk X
-/
theorem Indep.cardinalMk_le_cRk_of_subset (hI : M.Indep I) (hIX : I ⊆ X) : #I ≤ M.cRk X :=
  let ⟨_, hJ, hIJ⟩ := hI.subset_isBasis'_of_subset hIX
  (mk_le_mk_of_subset hIJ).trans hJ.cardinalMk_le_cRk
/-
**Matroid.cRk_le_cardinalMk** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：cRk_le_cardinalMk (M : Matroid α) (X : Set α) : M.cRk X <= #X
参数：M : Matroid α；X : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用定理 `Matroid.instNonemptySubtypeSetIsBase`：∀ {α : Type u_1} (M : Matroid α), 
Nonempty { B // M.IsBase B }
· 使用定理 `Cardinal.mk_le_mk_of_subset`：mk_le_mk_of_subset {α} {s t : Set α} (h : s
 subseteq t) : #s <= #t
· 使用定理 `Matroid.IsBase.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {B : Set 
α}, M.IsBase B → B ⊆ M.E
-/
theorem cRk_le_cardinalMk (M : Matroid α) (X : Set α) : M.cRk X ≤ #X :=
  ciSup_le fun ⟨_, hI⟩ ↦ mk_le_mk_of_subset hI.subset_ground
/-
**Matroid.cRk_ground** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u} (M : Matroid α), M.cRk M.E = M.cRank
参数：M : Matroid α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.cRk.eq_1`：∀ {α : Type u} (M : Matroid α) (X : Set α), M.cRk X = 
(M.restrict X).cRank
· 使用定理 `Matroid.restrict_ground_eq_self`：∀ {α : Type u_1} (M : Matroid α), M.res
trict M.E = M
-/
@[simp] theorem cRk_ground (M : Matroid α) : M.cRk M.E = M.cRank := by
  rw [cRk, restrict_ground_eq_self]
/-
**Matroid.cRank_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u} (M : Matroid α) (X : Set α), (M.restrict X).cRank = M.cRk X
参数：M : Matroid α；X : Set α；M.restrict X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem cRank_restrict (M : Matroid α) (X : Set α) : (M ↾ X).cRank = M.cRk X := rfl
/-
**Matroid.cRk_mono** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：cRk_mono (M : Matroid α) : Monotone M.cRk
参数：M : Matroid α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Matroid.Indep.subset_isBasis'_of_subset`：∀ {α : Type u_1} {M : Matroid α
} {I X : Set α}, M.Indep I → I ⊆ X → ∃ J, M.IsBasis' J X ∧ I ⊆ J
· 使用定理 `Matroid.IsBasis'.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis' I X → M.Indep I
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Matroid.IsBasis'.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α},
 M.IsBasis' I X → I ⊆ X
· 使用定理 `Cardinal.mk_le_mk_of_subset`：mk_le_mk_of_subset {α} {s t : Set α} (h : s
 subseteq t) : #s <= #t
· 使用定理 `Matroid.IsBasis'.cardinalMk_le_cRk`：∀ {α : Type u} {M : Matroid α} {I X 
: Set α}, M.IsBasis' I X → Cardinal.mk ↑I ≤ M.cRk X
-/
theorem cRk_mono (M : Matroid α) : Monotone M.cRk := by
  simp only [Monotone, cRk_le_iff]
  intro X Y hXY I hIX
  obtain ⟨J, hJ, hIJ⟩ := hIX.indep.subset_isBasis'_of_subset (hIX.subset.trans hXY)
  exact (mk_le_mk_of_subset hIJ).trans hJ.cardinalMk_le_cRk
/-
**Matroid.cRk_le_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：cRk_le_of_subset (M : Matroid α) (hXY : X subseteq Y) : M.cRk X <= M.cRk Y
参数：M : Matroid α；hXY : X subseteq Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.cRk_mono`：cRk_mono (M : Matroid α) : Monotone M.cRk
-/
theorem cRk_le_of_subset (M : Matroid α) (hXY : X ⊆ Y) : M.cRk X ≤ M.cRk Y :=
  M.cRk_mono hXY
/-
**Matroid.cRk_inter_ground** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u} (M : Matroid α) (X : Set α), M.cRk (X ∩ M.E) = M.cRk X
参数：M : Matroid α；X : Set α；X ∩ M.E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Matroid.cRk_le_of_subset`：cRk_le_of_subset (M : Matroid α) (hXY : X subs
eteq Y) : M.cRk X <= M.cRk Y
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matroid.cRk_le_iff`：cRk_le_iff : M.cRk X <= κ ↔ forall ⦃I⦄, M.IsBasis' I
 X -> #I <= κ
· 使用定理 `Matroid.IsBasis.cardinalMk_le_cRk`：∀ {α : Type u} {M : Matroid α} {I X :
 Set α}, M.IsBasis I X → Cardinal.mk ↑I ≤ M.cRk X
· 使用定理 `Matroid.IsBasis'.isBasis_inter_ground`：∀ {α : Type u_1} {M : Matroid α} 
{I X : Set α}, M.IsBasis' I X → M.IsBasis I (X ∩ M.E)
-/
@[simp] theorem cRk_inter_ground (M : Matroid α) (X : Set α) : M.cRk (X ∩ M.E) = M.cRk X :=
  (M.cRk_le_of_subset inter_subset_left).antisymm <| cRk_le_iff.2
    fun _ h ↦ h.isBasis_inter_ground.cardinalMk_le_cRk
/-
**Matroid.cRk_restrict_subset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：cRk_restrict_subset (M : Matroid α) (hYX : Y subseteq X) : (M ↾ X).cRk Y =
 M.cRk Y
参数：M : Matroid α；hYX : Y subseteq X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.inter_eq_self_of_subset_left`：inter_eq_self_of_subset_left {s t : Se
t α} : s subseteq t -> s inter t = s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Matroid.IsBasis'.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α},
 M.IsBasis' I X → I ⊆ X
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matroid.IsBasis'.cardinalMk_le_cRk`：∀ {α : Type u} {M : Matroid α} {I X 
: Set α}, M.IsBasis' I X → Cardinal.mk ↑I ≤ M.cRk X
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem cRk_restrict_subset (M : Matroid α) (hYX : Y ⊆ X) : (M ↾ X).cRk Y = M.cRk Y := by
  have aux : ∀ ⦃I⦄, M.IsBasis' I Y ↔ (M ↾ X).IsBasis' I Y := by
    simp_rw [isBasis'_restrict_iff, inter_eq_self_of_subset_left hYX, iff_self_and]
    exact fun I h ↦ h.subset.trans hYX
  simp_rw [le_antisymm_iff, cRk_le_iff]
  exact ⟨fun I hI ↦ (aux.2 hI).cardinalMk_le_cRk, fun I hI ↦ (aux.1 hI).cardinalMk_le_cRk⟩
/-
**Matroid.cRk_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：cRk_restrict (M : Matroid α) (X Y : Set α) : (M ↾ X).cRk Y = M.cRk (X inte
r Y)
参数：M : Matroid α；X Y : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.cRk_inter_ground`：∀ {α : Type u} (M : Matroid α) (X : Set α), M.
cRk (X ∩ M.E) = M.cRk X
· 使用定理 `Matroid.restrict_ground_eq`：∀ {α : Type u_1} {M : Matroid α} {R : Set α}
, (M.restrict R).E = R
· 使用定理 `Matroid.cRk_restrict_subset`：cRk_restrict_subset (M : Matroid α) (hYX : 
Y subseteq X) : (M ↾ X).cRk Y = M.cRk Y
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
-/
theorem cRk_restrict (M : Matroid α) (X Y : Set α) : (M ↾ X).cRk Y = M.cRk (X ∩ Y) := by
  rw [← cRk_inter_ground, restrict_ground_eq, cRk_restrict_subset _ inter_subset_right,
    inter_comm]
/-
**Matroid.Indep.cRk_eq_cardinalMk** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u} {M : Matroid α} {I : Set α}, M.Indep I → Cardinal.mk ↑I = M
.cRk I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `Matroid.cRk_le_cardinalMk`：cRk_le_cardinalMk (M : Matroid α) (X : Set α)
 : M.cRk X <= #X
· 使用定理 `Matroid.IsBasis.cardinalMk_le_cRk`：∀ {α : Type u} {M : Matroid α} {I X :
 Set α}, M.IsBasis I X → Cardinal.mk ↑I ≤ M.cRk X
· 使用定理 `Matroid.Indep.isBasis_self`：∀ {α : Type u_1} {M : Matroid α} {I : Set α}
, M.Indep I → M.IsBasis I I
-/
theorem Indep.cRk_eq_cardinalMk (hI : M.Indep I) : #I = M.cRk I :=
  (M.cRk_le_cardinalMk I).antisymm' (hI.isBasis_self.cardinalMk_le_cRk)
/-
**Matroid.cRk_map_image_lift** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u} {β : Type v} {f : α → β} (M : Matroid α) (hf : Set.InjOn f 
M.E) (X : Set α),   autoParam (X ⊆ M.E) Matroid.cRk_map_image_lift._auto_1 →    
 Cardinal.lift.{u, v} ((M.map f hf).cRk (f '' X)) = Cardinal.lift.{v, u} (M.cRk 
X)
参数：M : Matroid α；hf : Set.InjOn f M.E；X : Set α；X ⊆ M.E；(M.map f hf).cRk (f '' X
)；M.cRk X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.cRk.eq_1`：∀ {α : Type u} (M : Matroid α) (X : Set α), M.cRk X = 
(M.restrict X).cRank
· 使用定理 `Matroid.cRank.eq_1`：∀ {α : Type u} (M : Matroid α), M.cRank = ⨆ B, Cardi
nal.mk ↑↑B
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用定理 `Cardinal.lift_iSup`：lift_iSup {ι : Type v} {f : ι -> Cardinal.{w}} (hf :
 BddAbove (range f)) : lift.{u} (iSup f) = ⨆ i, lift.{u} (f i)
· 使用定理 `Cardinal.bddAbove_of_small`：bddAbove_of_small {s : Set Cardinal.{u}} [h 
: Small.{u} s] : BddAbove s
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ciSup_le_iff`：ciSup_le_iff [Nonempty ι] {f : ι -> α} {a : α} (hf : BddAb
ove (range f)) : iSup f <= a ↔ forall i, f i <= a
· 使用定理 `Matroid.instNonemptySubtypeSetIsBase`：∀ {α : Type u_1} (M : Matroid α), 
Nonempty { B // M.IsBase B }
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `Matroid.isBasis'_iff_isBasis`：∀ {α : Type u_1} {M : Matroid α} {I X : Se
t α},   autoParam (X ⊆ M.E) Matroid.isBasis'_iff_isBasis._auto_1 → (M.IsBasis' I
 X ↔ M.IsBasis I X…
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Matroid.map_isBasis_iff'`：map_isBasis_iff' {I X : Set β} {hf} : (M.map f
 hf).IsBasis I X ↔ exists I₀ X₀, M.IsBasis I₀ X₀ ∧ I = f '' I₀ ∧ X = f '' X₀
· 使用定理 `Cardinal.mk_image_eq_of_injOn_lift`：mk_image_eq_of_injOn_lift {α : Type 
u} {β : Type v} (f : α -> β) (s : Set α) (h : InjOn f s) : lift.{u} #(f '' s) = 
lift.{v} #s
· 使用定理 `Set.InjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α →
 β}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `Matroid.IsBasis.cardinalMk_le_cRk`：∀ {α : Type u} {M : Matroid α} {I X :
 Set α}, M.IsBasis I X → Cardinal.mk ↑I ≤ M.cRk X
· 使用定理 `Set.InjOn.image_eq_image_iff`：∀ {α : Type u_1} {β : Type u_2} {s s₁ s₂ :
 Set α} {f : α → β},   Set.InjOn f s → s₁ ⊆ s → s₂ ⊆ s → (f '' s₁ = f '' s₂ ↔ s₁
 = s₂)
· 使用定理 `Matroid.IsBasis.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → X ⊆ M.E
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsBasis.map`：∀ {α : Type u_1} {β : Type u_2} {I : Set α} {M : Ma
troid α} {X : Set α},   M.IsBasis I X → ∀ {f : α → β} (hf : Set.InjOn f M.E), (M
.map f hf…
-/
@[simp] theorem cRk_map_image_lift (M : Matroid α) (hf : InjOn f M.E) (X : Set α)
    (hX : X ⊆ M.E := by aesop_mat) : lift.{u, v} ((M.map f hf).cRk (f '' X)) = lift (M.cRk X) := by
  nth_rw 1 [cRk, cRank, le_antisymm_iff, lift_iSup bddAbove_of_small, cRk, cRank, cRk, cRank]
  nth_rw 2 [lift_iSup bddAbove_of_small]
  simp only [ciSup_le_iff bddAbove_of_small, Subtype.forall, isBase_restrict_iff',
    isBasis'_iff_isBasis hX, isBasis'_iff_isBasis (show f '' X ⊆ (M.map f hf).E from image_mono hX)]
  refine ⟨fun I hI ↦ ?_, fun I hI ↦ ?_⟩
  · obtain ⟨I, X', hIX, rfl, hXX'⟩ := map_isBasis_iff'.1 hI
    rw [mk_image_eq_of_injOn_lift _ _ (hf.mono hIX.indep.subset_ground), lift_le]
    obtain rfl : X = X' := by rwa [hf.image_eq_image_iff hX hIX.subset_ground] at hXX'
    exact hIX.cardinalMk_le_cRk
  rw [← mk_image_eq_of_injOn_lift _ _ (hf.mono hI.indep.subset_ground), lift_le]
  exact (hI.map hf).cardinalMk_le_cRk
/-
**Matroid.cRk_map_image** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α β : Type u} {f : α → β} (M : Matroid α) (hf : Set.InjOn f M.E) (X : S
et α),   autoParam (X ⊆ M.E) Matroid.cRk_map_image._auto_1 → (M.map f hf).cRk (f
 '' X) = M.cRk X
参数：M : Matroid α；hf : Set.InjOn f M.E；X : Set α；X ⊆ M.E；M.map f hf；f '' X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lift_inj`：lift_inj {a b : Cardinal.{u}} : lift.{v, u} a = lift.
{v, u} b ↔ a = b
· 使用定理 `Matroid.cRk_map_image_lift`：∀ {α : Type u} {β : Type v} {f : α → β} (M :
 Matroid α) (hf : Set.InjOn f M.E) (X : Set α),   autoParam (X ⊆ M.E) Matroid.cR
k_map_image_lift…
-/
@[simp] theorem cRk_map_image {β : Type u} {f : α → β} (M : Matroid α) (hf : InjOn f M.E)
    (X : Set α) (hX : X ⊆ M.E := by aesop_mat) : (M.map f hf).cRk (f '' X) = M.cRk X :=
  lift_inj.1 <| M.cRk_map_image_lift ..
/-
**Matroid.cRk_map_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：cRk_map_eq {β : Type u} {f : α -> β} {X : Set β} (M : Matroid α) (hf : Inj
On f M.E) : (M.map f hf).cRk X = M.cRk (f ⁻¹' X)
参数：M : Matroid α；hf : InjOn f M.E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.cRk_inter_ground`：∀ {α : Type u} (M : Matroid α) (X : Set α), M.
cRk (X ∩ M.E) = M.cRk X
· 使用定理 `Matroid.cRk_map_image`：∀ {α β : Type u} {f : α → β} (M : Matroid α) (hf 
: Set.InjOn f M.E) (X : Set α),   autoParam (X ⊆ M.E) Matroid.cRk_map_image._aut
o_1 → (M.ma…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.image_preimage_inter`：image_preimage_inter (f : α -> β) (s : Set α) 
(t : Set β) : f '' (f ⁻¹' t inter s) = t inter f '' s
· 使用定理 `Matroid.map_ground`：∀ {α : Type u_1} {β : Type u_2} (M : Matroid α) (f :
 α → β) (hf : Set.InjOn f M.E), (M.map f hf).E = f '' M.E
-/
theorem cRk_map_eq {β : Type u} {f : α → β} {X : Set β} (M : Matroid α) (hf : InjOn f M.E) :
    (M.map f hf).cRk X = M.cRk (f ⁻¹' X) := by
  rw [← M.cRk_inter_ground, ← M.cRk_map_image hf _, image_preimage_inter, ← map_ground _ _ hf,
    cRk_inter_ground]
/-
**Matroid.cRk_comap_lift** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u} {β : Type v} (M : Matroid β) (f : α → β) (X : Set α),   Car
dinal.lift.{v, u} ((M.comap f).cRk X) = Cardinal.lift.{u, v} (M.cRk (f '' X))
参数：M : Matroid β；f : α → β；X : Set α；(M.comap f).cRk X；M.cRk (f '' X)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.cRk.eq_1`：∀ {α : Type u} (M : Matroid α) (X : Set α), M.cRk X = 
(M.restrict X).cRank
· 使用定理 `Matroid.cRank.eq_1`：∀ {α : Type u} (M : Matroid α), M.cRank = ⨆ B, Cardi
nal.mk ↑↑B
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用定理 `Cardinal.lift_iSup`：lift_iSup {ι : Type v} {f : ι -> Cardinal.{w}} (hf :
 BddAbove (range f)) : lift.{u} (iSup f) = ⨆ i, lift.{u} (f i)
· 使用定理 `Cardinal.bddAbove_of_small`：bddAbove_of_small {s : Set Cardinal.{u}} [h 
: Small.{u} s] : BddAbove s
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ciSup_le_iff`：ciSup_le_iff [Nonempty ι] {f : ι -> α} {a : α} (hf : BddAb
ove (range f)) : iSup f <= a ↔ forall i, f i <= a
· 使用定理 `Matroid.instNonemptySubtypeSetIsBase`：∀ {α : Type u_1} (M : Matroid α), 
Nonempty { B // M.IsBase B }
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_image_eq_of_injOn_lift`：mk_image_eq_of_injOn_lift {α : Type 
u} {β : Type v} (f : α -> β) (s : Set α) (h : InjOn f s) : lift.{u} #(f '' s) = 
lift.{v} #s
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `Matroid.IsBasis'.cardinalMk_le_cRk`：∀ {α : Type u} {M : Matroid α} {I X 
: Set α}, M.IsBasis' I X → Cardinal.mk ↑I ≤ M.cRk X
· 使用引理 `Set.exists_subset_bijOn`：exists_subset_bijOn : exists s' subseteq s, Bij
On f s' (f '' s)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Set.BijOn.image_eq`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set
 β} {f : α → β}, Set.BijOn f s t → f '' s = t
· 使用定理 `Set.image_preimage_inter`：image_preimage_inter (f : α -> β) (s : Set α) 
(t : Set β) : f '' (f ⁻¹' t inter s) = t inter f '' s
· 使用定理 `Set.inter_eq_self_of_subset_left`：inter_eq_self_of_subset_left {s t : Se
t α} : s subseteq t -> s inter t = s
· 使用定理 `Matroid.IsBasis'.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α},
 M.IsBasis' I X → I ⊆ X
· 使用定理 `Set.BijOn.injOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
 {f : α → β}, Set.BijOn f s t → Set.InjOn f s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matroid.comap_isBasis'_iff`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} 
{N : Matroid β} {I X : Set α},   (N.comap f).IsBasis' I X ↔ N.IsBasis' (f '' I) 
(f '' X) ∧ Set.I…
-/
@[simp] theorem cRk_comap_lift (M : Matroid β) (f : α → β) (X : Set α) :
    lift.{v, u} ((M.comap f).cRk X) = lift (M.cRk (f '' X)) := by
  nth_rw 1 [cRk, cRank, le_antisymm_iff, lift_iSup bddAbove_of_small, cRk, cRank, cRk, cRank]
  nth_rw 2 [lift_iSup bddAbove_of_small]
  simp only [ciSup_le_iff bddAbove_of_small, Subtype.forall, isBase_restrict_iff',
    comap_isBasis'_iff, and_imp]
  refine ⟨fun I hI hfI hIX ↦ ?_, fun I hIX ↦ ?_⟩
  · rw [← mk_image_eq_of_injOn_lift _ _ hfI, lift_le]
    exact hI.cardinalMk_le_cRk
  obtain ⟨I₀, hI₀X, rfl, hfI₀⟩ := show ∃ I₀ ⊆ X, f '' I₀ = I ∧ InjOn f I₀ by
    obtain ⟨I₀, hI₀ss, hbij⟩ := exists_subset_bijOn (f ⁻¹' I ∩ X) f
    refine ⟨I₀, hI₀ss.trans inter_subset_right, ?_, hbij.injOn⟩
    rw [hbij.image_eq, image_preimage_inter, inter_eq_self_of_subset_left hIX.subset]
  rw [mk_image_eq_of_injOn_lift _ _ hfI₀, lift_le]
  exact IsBasis'.cardinalMk_le_cRk <| comap_isBasis'_iff.2 ⟨hIX, hfI₀, hI₀X⟩
/-
**Matroid.cRk_comap** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α β : Type u} (M : Matroid β) (f : α → β) (X : Set α), (M.comap f).cRk 
X = M.cRk (f '' X)
参数：M : Matroid β；f : α → β；X : Set α；M.comap f；f '' X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lift_inj`：lift_inj {a b : Cardinal.{u}} : lift.{v, u} a = lift.
{v, u} b ↔ a = b
· 使用定理 `Matroid.cRk_comap_lift`：∀ {α : Type u} {β : Type v} (M : Matroid β) (f :
 α → β) (X : Set α),   Cardinal.lift.{v, u} ((M.comap f).cRk X) = Cardinal.lift.
{u, v} (M.cR…
-/
@[simp] theorem cRk_comap {β : Type u} (M : Matroid β) (f : α → β) (X : Set α) :
    (M.comap f).cRk X = M.cRk (f '' X) :=
  lift_inj.1 <| M.cRk_comap_lift ..

end Rank

section Invariant

/-- A class stating that cardinality-valued rank is well-defined
(i.e. all bases are equicardinal) for a matroid `M` and its minors.
Notably, this holds for `Finitary` matroids; see `Matroid.invariantCardinalRank_of_finitary`. -/
@[mk_iff]
/-
**Matroid.InvariantCardinalRank** 是 Mathlib 中的一个归纳类型，位于命名空间 `Matroid`。
形式化陈述：{α : Type u} → Matroid α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A class stating that cardinality-valued rank is well-defined
(i.e. all bases are equicardinal) for a matroid `M` and its minors.
Notably, this holds for `Finitary` matroids; see `Matroid.invariantCardinalRank_
of_finitary`.
-/
class InvariantCardinalRank (M : Matroid α) : Prop where
  forall_card_isBasis_diff :
    ∀ ⦃I J X⦄, M.IsBasis I X → M.IsBasis J X → #(I \ J : Set α) = #(J \ I : Set α)

variable [InvariantCardinalRank M]
/-
**Matroid.IsBasis.cardinalMk_sdiff_comm** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBas
is`。
形式化陈述：∀ {α : Type u} {M : Matroid α} {I J X : Set α} [M.InvariantCardinalRank], 
  M.IsBasis I X → M.IsBasis J X → Cardinal.mk ↑(I \ J) = Cardinal.mk ↑(J \ I)
参数：I \ J；J \ I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.InvariantCardinalRank.forall_card_isBasis_diff`：∀ {α : Type u} {
M : Matroid α} [self : M.InvariantCardinalRank] ⦃I J X : Set α⦄,   M.IsBasis I X
 → M.IsBasis J X → Cardinal.mk ↑(I \ J) = Ca…
-/
theorem IsBasis.cardinalMk_sdiff_comm (hIX : M.IsBasis I X) (hJX : M.IsBasis J X) :
    #(I \ J : Set α) = #(J \ I : Set α) :=
  InvariantCardinalRank.forall_card_isBasis_diff hIX hJX

@[deprecated (since := "2026-06-03")]
alias IsBasis.cardinalMk_diff_comm := IsBasis.cardinalMk_sdiff_comm
/-
**Matroid.IsBasis'.cardinalMk_sdiff_comm** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBa
sis'`。
形式化陈述：∀ {α : Type u} {M : Matroid α} {I J X : Set α} [M.InvariantCardinalRank], 
  M.IsBasis' I X → M.IsBasis' J X → Cardinal.mk ↑(I \ J) = Cardinal.mk ↑(J \ I)
参数：I \ J；J \ I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis.cardinalMk_sdiff_comm`：∀ {α : Type u} {M : Matroid α} {I
 J X : Set α} [M.InvariantCardinalRank],   M.IsBasis I X → M.IsBasis J X → Cardi
nal.mk ↑(I \ J) = Cardinal.…
· 使用定理 `Matroid.IsBasis'.isBasis_inter_ground`：∀ {α : Type u_1} {M : Matroid α} 
{I X : Set α}, M.IsBasis' I X → M.IsBasis I (X ∩ M.E)
-/
theorem IsBasis'.cardinalMk_sdiff_comm (hIX : M.IsBasis' I X) (hJX : M.IsBasis' J X) :
    #(I \ J : Set α) = #(J \ I : Set α) :=
  hIX.isBasis_inter_ground.cardinalMk_sdiff_comm hJX.isBasis_inter_ground

@[deprecated (since := "2026-06-03")]
alias IsBasis'.cardinalMk_diff_comm := IsBasis'.cardinalMk_sdiff_comm
/-
**Matroid.IsBase.cardinalMk_sdiff_comm** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase
`。
形式化陈述：∀ {α : Type u} {M : Matroid α} {B B' : Set α} [M.InvariantCardinalRank],  
 M.IsBase B → M.IsBase B' → Cardinal.mk ↑(B \ B') = Cardinal.mk ↑(B' \ B)
参数：B \ B'；B' \ B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis.cardinalMk_sdiff_comm`：∀ {α : Type u} {M : Matroid α} {I
 J X : Set α} [M.InvariantCardinalRank],   M.IsBasis I X → M.IsBasis J X → Cardi
nal.mk ↑(I \ J) = Cardinal.…
· 使用定理 `Matroid.IsBase.isBasis_ground`：∀ {α : Type u_1} {M : Matroid α} {B : Set
 α}, M.IsBase B → M.IsBasis B M.E
-/
theorem IsBase.cardinalMk_sdiff_comm (hB : M.IsBase B) (hB' : M.IsBase B') :
    #(B \ B' : Set α) = #(B' \ B : Set α) :=
  hB.isBasis_ground.cardinalMk_sdiff_comm hB'.isBasis_ground

@[deprecated (since := "2026-06-03")]
alias IsBase.cardinalMk_diff_comm := IsBase.cardinalMk_sdiff_comm
/-
**Matroid.IsBasis.cardinalMk_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis`。
形式化陈述：∀ {α : Type u} {M : Matroid α} {I J X : Set α} [M.InvariantCardinalRank], 
  M.IsBasis I X → M.IsBasis J X → Cardinal.mk ↑I = Cardinal.mk ↑J
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sdiff_union_inter`：sdiff_union_inter (s t : Set α) : s \ t union s i
nter t = s
· 使用定理 `Cardinal.mk_union_of_disjoint`：mk_union_of_disjoint {α : Type u} {S T : 
Set α} (H : Disjoint S T) : #(S union T : Set α) = #S + #T
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用引理 `Set.disjoint_sdiff_left`：disjoint_sdiff_left : Disjoint (t \ s) s
· 使用定理 `Matroid.IsBasis.cardinalMk_sdiff_comm`：∀ {α : Type u} {M : Matroid α} {I
 J X : Set α} [M.InvariantCardinalRank],   M.IsBasis I X → M.IsBasis J X → Cardi
nal.mk ↑(I \ J) = Cardinal.…
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
-/
theorem IsBasis.cardinalMk_eq (hIX : M.IsBasis I X) (hJX : M.IsBasis J X) : #I = #J := by
  rw [← sdiff_union_inter I J,
    mk_union_of_disjoint (disjoint_sdiff_left.mono_right inter_subset_right),
    hIX.cardinalMk_sdiff_comm hJX,
    ← mk_union_of_disjoint (disjoint_sdiff_left.mono_right inter_subset_left),
    inter_comm, sdiff_union_inter]
/-
**Matroid.IsBasis'.cardinalMk_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis'`。
形式化陈述：∀ {α : Type u} {M : Matroid α} {I J X : Set α} [M.InvariantCardinalRank], 
  M.IsBasis' I X → M.IsBasis' J X → Cardinal.mk ↑I = Cardinal.mk ↑J
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis.cardinalMk_eq`：∀ {α : Type u} {M : Matroid α} {I J X : S
et α} [M.InvariantCardinalRank],   M.IsBasis I X → M.IsBasis J X → Cardinal.mk ↑
I = Cardinal.mk ↑J
· 使用定理 `Matroid.IsBasis'.isBasis_inter_ground`：∀ {α : Type u_1} {M : Matroid α} 
{I X : Set α}, M.IsBasis' I X → M.IsBasis I (X ∩ M.E)
-/
theorem IsBasis'.cardinalMk_eq (hIX : M.IsBasis' I X) (hJX : M.IsBasis' J X) : #I = #J :=
  hIX.isBasis_inter_ground.cardinalMk_eq hJX.isBasis_inter_ground
/-
**Matroid.IsBase.cardinalMk_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase`。
形式化陈述：∀ {α : Type u} {M : Matroid α} {B B' : Set α} [M.InvariantCardinalRank],  
 M.IsBase B → M.IsBase B' → Cardinal.mk ↑B = Cardinal.mk ↑B'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis.cardinalMk_eq`：∀ {α : Type u} {M : Matroid α} {I J X : S
et α} [M.InvariantCardinalRank],   M.IsBasis I X → M.IsBasis J X → Cardinal.mk ↑
I = Cardinal.mk ↑J
· 使用定理 `Matroid.IsBase.isBasis_ground`：∀ {α : Type u_1} {M : Matroid α} {B : Set
 α}, M.IsBase B → M.IsBasis B M.E
-/
theorem IsBase.cardinalMk_eq (hB : M.IsBase B) (hB' : M.IsBase B') : #B = #B' :=
  hB.isBasis_ground.cardinalMk_eq hB'.isBasis_ground
/-
**Matroid.Indep.cardinalMk_le_isBase** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u} {M : Matroid α} {I B : Set α} [M.InvariantCardinalRank],   
M.Indep I → M.IsBase B → Cardinal.mk ↑I ≤ Cardinal.mk ↑B
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.exists_isBase_superset`：∀ {α : Type u_1} {M : Matroid α} {
I : Set α}, M.Indep I → ∃ B, M.IsBase B ∧ I ⊆ B
· 使用定理 `Cardinal.mk_le_mk_of_subset`：mk_le_mk_of_subset {α} {s t : Set α} (h : s
 subseteq t) : #s <= #t
· 使用定理 `Matroid.IsBase.cardinalMk_eq`：∀ {α : Type u} {M : Matroid α} {B B' : Set
 α} [M.InvariantCardinalRank],   M.IsBase B → M.IsBase B' → Cardinal.mk ↑B = Car
dinal.mk ↑B'
-/
theorem Indep.cardinalMk_le_isBase (hI : M.Indep I) (hB : M.IsBase B) : #I ≤ #B :=
  have ⟨_B', hB', hIB'⟩ := hI.exists_isBase_superset
  hB'.cardinalMk_eq hB ▸ mk_le_mk_of_subset hIB'
/-
**Matroid.Indep.cardinalMk_le_isBasis'** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`
。
形式化陈述：∀ {α : Type u} {M : Matroid α} {I J X : Set α} [M.InvariantCardinalRank], 
  M.Indep I → M.IsBasis' J X → I ⊆ X → Cardinal.mk ↑I ≤ Cardinal.mk ↑J
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.subset_isBasis'_of_subset`：∀ {α : Type u_1} {M : Matroid α
} {I X : Set α}, M.Indep I → I ⊆ X → ∃ J, M.IsBasis' J X ∧ I ⊆ J
· 使用定理 `Cardinal.mk_le_mk_of_subset`：mk_le_mk_of_subset {α} {s t : Set α} (h : s
 subseteq t) : #s <= #t
· 使用定理 `Matroid.IsBasis'.cardinalMk_eq`：∀ {α : Type u} {M : Matroid α} {I J X : 
Set α} [M.InvariantCardinalRank],   M.IsBasis' I X → M.IsBasis' J X → Cardinal.m
k ↑I = Cardinal.mk ↑…
-/
theorem Indep.cardinalMk_le_isBasis' (hI : M.Indep I) (hJ : M.IsBasis' J X) (hIX : I ⊆ X) :
    #I ≤ #J :=
  have ⟨_J', hJ', hIJ'⟩ := hI.subset_isBasis'_of_subset hIX
  hJ'.cardinalMk_eq hJ ▸ mk_le_mk_of_subset hIJ'
/-
**Matroid.Indep.cardinalMk_le_isBasis** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u} {M : Matroid α} {I J X : Set α} [M.InvariantCardinalRank], 
  M.Indep I → M.IsBasis J X → I ⊆ X → Cardinal.mk ↑I ≤ Cardinal.mk ↑J
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.cardinalMk_le_isBasis'`：∀ {α : Type u} {M : Matroid α} {I 
J X : Set α} [M.InvariantCardinalRank],   M.Indep I → M.IsBasis' J X → I ⊆ X → C
ardinal.mk ↑I ≤ Cardinal.m…
· 使用定理 `Matroid.IsBasis.isBasis'`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}
, M.IsBasis I X → M.IsBasis' I X
-/
theorem Indep.cardinalMk_le_isBasis (hI : M.Indep I) (hJ : M.IsBasis J X) (hIX : I ⊆ X) :
    #I ≤ #J :=
  hI.cardinalMk_le_isBasis' hJ.isBasis' hIX
/-
**Matroid.IsBase.cardinalMk_eq_cRank** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase`。
形式化陈述：∀ {α : Type u} {M : Matroid α} {B : Set α} [M.InvariantCardinalRank], M.Is
Base B → Cardinal.mk ↑B = M.cRank
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBase.cardinalMk_eq`：∀ {α : Type u} {M : Matroid α} {B B' : Set
 α} [M.InvariantCardinalRank],   M.IsBase B → M.IsBase B' → Cardinal.mk ↑B = Car
dinal.mk ↑B'
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ciSup_const`：ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a
· 使用定理 `Matroid.instNonemptySubtypeSetIsBase`：∀ {α : Type u_1} (M : Matroid α), 
Nonempty { B // M.IsBase B }
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsBase.cardinalMk_eq_cRank (hB : M.IsBase B) : #B = M.cRank := by
  have hrw : ∀ B' : {B : Set α // M.IsBase B}, #B' = #B := fun B' ↦ B'.2.cardinalMk_eq hB
  simp [cRank, hrw]

/-- Restrictions of matroids with cardinal rank functions have cardinal rank functions. -/
/-
**Matroid.invariantCardinalRank_restrict** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
形式化陈述：invariantCardinalRank_restrict : InvariantCardinalRank (M ↾ X)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis.cardinalMk_sdiff_comm`：∀ {α : Type u} {M : Matroid α} {I
 J X : Set α} [M.InvariantCardinalRank],   M.IsBasis I X → M.IsBasis J X → Cardi
nal.mk ↑(I \ J) = Cardinal.…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.isBasis_restrict_iff'`：isBasis_restrict_iff' : (M ↾ R).IsBasis I
 X ↔ M.IsBasis I (X inter M.E) ∧ X subseteq R

--- 原说明 ---
Restrictions of matroids with cardinal rank functions have cardinal rank functio
ns.
-/
instance invariantCardinalRank_restrict : InvariantCardinalRank (M ↾ X) := by
  refine ⟨fun I J Y hI hJ ↦ ?_⟩
  rw [isBasis_restrict_iff'] at hI hJ
  exact hI.1.cardinalMk_sdiff_comm hJ.1
/-
**Matroid.IsBasis'.cardinalMk_eq_cRk** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis'
`。
形式化陈述：∀ {α : Type u} {M : Matroid α} {I X : Set α} [M.InvariantCardinalRank], M.
IsBasis' I X → Cardinal.mk ↑I = M.cRk X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.cRk.eq_1`：∀ {α : Type u} (M : Matroid α) (X : Set α), M.cRk X = 
(M.restrict X).cRank
· 使用定理 `Matroid.IsBase.cardinalMk_eq_cRank`：∀ {α : Type u} {M : Matroid α} {B : 
Set α} [M.InvariantCardinalRank], M.IsBase B → Cardinal.mk ↑B = M.cRank
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matroid.isBase_restrict_iff'`：isBase_restrict_iff' : (M ↾ X).IsBase I ↔ 
M.IsBasis' I X
-/
theorem IsBasis'.cardinalMk_eq_cRk (hIX : M.IsBasis' I X) : #I = M.cRk X := by
  rw [cRk, (isBase_restrict_iff'.2 hIX).cardinalMk_eq_cRank]
/-
**Matroid.IsBasis.cardinalMk_eq_cRk** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis`。
形式化陈述：∀ {α : Type u} {M : Matroid α} {I X : Set α} [M.InvariantCardinalRank], M.
IsBasis I X → Cardinal.mk ↑I = M.cRk X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis'.cardinalMk_eq_cRk`：∀ {α : Type u} {M : Matroid α} {I X 
: Set α} [M.InvariantCardinalRank], M.IsBasis' I X → Cardinal.mk ↑I = M.cRk X
· 使用定理 `Matroid.IsBasis.isBasis'`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}
, M.IsBasis I X → M.IsBasis' I X
-/
theorem IsBasis.cardinalMk_eq_cRk (hIX : M.IsBasis I X) : #I = M.cRk X :=
  hIX.isBasis'.cardinalMk_eq_cRk
/-
**Matroid.cRk_closure** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u} (M : Matroid α) [M.InvariantCardinalRank] (X : Set α), M.cR
k (M.closure X) = M.cRk X
参数：M : Matroid α；X : Set α；M.closure X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBasis'`：exists_isBasis' (M : Matroid α) (X : Set α) : e
xists I, M.IsBasis' I X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsBasis.cardinalMk_eq_cRk`：∀ {α : Type u} {M : Matroid α} {I X :
 Set α} [M.InvariantCardinalRank], M.IsBasis I X → Cardinal.mk ↑I = M.cRk X
· 使用定理 `Matroid.IsBasis'.isBasis_closure_right`：∀ {α : Type u_2} {M : Matroid α}
 {X I : Set α}, M.IsBasis' I X → M.IsBasis I (M.closure X)
· 使用定理 `Matroid.IsBasis'.cardinalMk_eq_cRk`：∀ {α : Type u} {M : Matroid α} {I X 
: Set α} [M.InvariantCardinalRank], M.IsBasis' I X → Cardinal.mk ↑I = M.cRk X
-/
@[simp] theorem cRk_closure (M : Matroid α) [InvariantCardinalRank M] (X : Set α) :
    M.cRk (M.closure X) = M.cRk X := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [← hI.isBasis_closure_right.cardinalMk_eq_cRk, ← hI.cardinalMk_eq_cRk]
/-
**Matroid.cRk_closure_congr** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：cRk_closure_congr (hXY : M.closure X = M.closure Y) : M.cRk X = M.cRk Y
参数：hXY : M.closure X = M.closure Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.cRk_closure`：∀ {α : Type u} (M : Matroid α) [M.InvariantCardinal
Rank] (X : Set α), M.cRk (M.closure X) = M.cRk X
-/
theorem cRk_closure_congr (hXY : M.closure X = M.closure Y) : M.cRk X = M.cRk Y := by
  rw [← cRk_closure, hXY, cRk_closure]
/-
**Matroid.Spanning.cRank_le_cardinalMk** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Spanni
ng`。
形式化陈述：∀ {α : Type u} {M : Matroid α} {X : Set α} [M.InvariantCardinalRank], M.Sp
anning X → M.cRank ≤ Cardinal.mk ↑X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Spanning.exists_isBase_subset`：∀ {α : Type u_2} {M : Matroid α} 
{S : Set α}, M.Spanning S → ∃ B, M.IsBase B ∧ B ⊆ S
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsBase.cardinalMk_eq_cRank`：∀ {α : Type u} {M : Matroid α} {B : 
Set α} [M.InvariantCardinalRank], M.IsBase B → Cardinal.mk ↑B = M.cRank
· 使用定理 `Cardinal.mk_le_mk_of_subset`：mk_le_mk_of_subset {α} {s t : Set α} (h : s
 subseteq t) : #s <= #t
-/
theorem Spanning.cRank_le_cardinalMk (h : M.Spanning X) : M.cRank ≤ #X :=
  have ⟨_B, hB, hBX⟩ := h.exists_isBase_subset
  (hB.cardinalMk_eq_cRank).symm.trans_le (mk_le_mk_of_subset hBX)

variable (M : Matroid α) [InvariantCardinalRank M] (e : α) (X Y : Set α)
/-
**Matroid.cRk_union_closure_right_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u} (M : Matroid α) [M.InvariantCardinalRank] (X Y : Set α), M.
cRk (X ∪ M.closure Y) = M.cRk (X ∪ Y)
参数：M : Matroid α；X Y : Set α；X ∪ M.closure Y；X ∪ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.cRk_closure_congr`：cRk_closure_congr (hXY : M.closure X = M.clos
ure Y) : M.cRk X = M.cRk Y
· 使用定理 `Matroid.closure_union_closure_right_eq`：∀ {α : Type u_2} (M : Matroid α)
 (X Y : Set α), M.closure (X ∪ M.closure Y) = M.closure (X ∪ Y)
-/
@[simp] theorem cRk_union_closure_right_eq : M.cRk (X ∪ M.closure Y) = M.cRk (X ∪ Y) :=
  M.cRk_closure_congr (M.closure_union_closure_right_eq _ _)
/-
**Matroid.cRk_union_closure_left_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u} (M : Matroid α) [M.InvariantCardinalRank] (X Y : Set α), M.
cRk (M.closure X ∪ Y) = M.cRk (X ∪ Y)
参数：M : Matroid α；X Y : Set α；M.closure X ∪ Y；X ∪ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.cRk_closure_congr`：cRk_closure_congr (hXY : M.closure X = M.clos
ure Y) : M.cRk X = M.cRk Y
· 使用定理 `Matroid.closure_union_closure_left_eq`：∀ {α : Type u_2} (M : Matroid α) 
(X Y : Set α), M.closure (M.closure X ∪ Y) = M.closure (X ∪ Y)
-/
@[simp] theorem cRk_union_closure_left_eq : M.cRk (M.closure X ∪ Y) = M.cRk (X ∪ Y) :=
  M.cRk_closure_congr (M.closure_union_closure_left_eq _ _)
/-
**Matroid.cRk_insert_closure_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u} (M : Matroid α) [M.InvariantCardinalRank] (e : α) (X : Set 
α),   M.cRk (insert e (M.closure X)) = M.cRk (insert e X)
参数：M : Matroid α；e : α；X : Set α；insert e (M.closure X)；insert e X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `Matroid.cRk_union_closure_left_eq`：∀ {α : Type u} (M : Matroid α) [M.Inv
ariantCardinalRank] (X Y : Set α), M.cRk (M.closure X ∪ Y) = M.cRk (X ∪ Y)
-/
@[simp] theorem cRk_insert_closure_eq : M.cRk (insert e (M.closure X)) = M.cRk (insert e X) := by
  rw [← union_singleton, cRk_union_closure_left_eq, union_singleton]
/-
**Matroid.cRk_union_closure_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：cRk_union_closure_eq : M.cRk (M.closure X union M.closure Y) = M.cRk (X un
ion Y)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.cRk_union_closure_right_eq`：∀ {α : Type u} (M : Matroid α) [M.In
variantCardinalRank] (X Y : Set α), M.cRk (X ∪ M.closure Y) = M.cRk (X ∪ Y)
· 使用定理 `Matroid.cRk_union_closure_left_eq`：∀ {α : Type u} (M : Matroid α) [M.Inv
ariantCardinalRank] (X Y : Set α), M.cRk (M.closure X ∪ Y) = M.cRk (X ∪ Y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cRk_union_closure_eq : M.cRk (M.closure X ∪ M.closure Y) = M.cRk (X ∪ Y) := by
  simp

/-- The `Cardinal` rank function is submodular. -/
/-
**Matroid.cRk_inter_add_cRk_union_le** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：cRk_inter_add_cRk_union_le : M.cRk (X inter Y) + M.cRk (X union Y) <= M.cR
k X + M.cRk Y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBasis'`：exists_isBasis' (M : Matroid α) (X : Set α) : e
xists I, M.IsBasis' I X
· 使用定理 `Matroid.Indep.subset_isBasis'_of_subset`：∀ {α : Type u_1} {M : Matroid α
} {I X : Set α}, M.Indep I → I ⊆ X → ∃ J, M.IsBasis' J X ∧ I ⊆ J
· 使用定理 `Matroid.IsBasis'.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis' I X → M.Indep I
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Matroid.IsBasis'.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α},
 M.IsBasis' I X → I ⊆ X
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.cRk_union_closure_eq`：cRk_union_closure_eq : M.cRk (M.closure X 
union M.closure Y) = M.cRk (X union Y)
· 使用定理 `Matroid.IsBasis'.closure_eq_closure`：∀ {α : Type u_2} {M : Matroid α} {X
 I : Set α}, M.IsBasis' I X → M.closure I = M.closure X
· 使用定理 `Matroid.IsBasis'.cardinalMk_eq_cRk`：∀ {α : Type u} {M : Matroid α} {I X 
: Set α} [M.InvariantCardinalRank], M.IsBasis' I X → Cardinal.mk ↑I = M.cRk X
· 使用定理 `Cardinal.mk_union_add_mk_inter`：mk_union_add_mk_inter {α : Type u} {S T 
: Set α} : #(S union T : Set α) + #(S inter T : Set α) = #S + #T
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `Matroid.cRk_le_cardinalMk`：cRk_le_cardinalMk (M : Matroid α) (X : Set α)
 : M.cRk X <= #X
· 使用定理 `Cardinal.mk_le_mk_of_subset`：mk_le_mk_of_subset {α} {s t : Set α} (h : s
 subseteq t) : #s <= #t
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t

--- 原说明 ---
The `Cardinal` rank function is submodular.
-/
theorem cRk_inter_add_cRk_union_le : M.cRk (X ∩ Y) + M.cRk (X ∪ Y) ≤ M.cRk X + M.cRk Y := by
  obtain ⟨Ii, hIi⟩ := M.exists_isBasis' (X ∩ Y)
  obtain ⟨IX, hIX, hIX'⟩ :=
    hIi.indep.subset_isBasis'_of_subset (hIi.subset.trans inter_subset_left)
  obtain ⟨IY, hIY, hIY'⟩ :=
    hIi.indep.subset_isBasis'_of_subset (hIi.subset.trans inter_subset_right)
  rw [← cRk_union_closure_eq, ← hIX.closure_eq_closure, ← hIY.closure_eq_closure,
    cRk_union_closure_eq, ← hIi.cardinalMk_eq_cRk, ← hIX.cardinalMk_eq_cRk,
    ← hIY.cardinalMk_eq_cRk, ← mk_union_add_mk_inter, add_comm]
  exact add_le_add (M.cRk_le_cardinalMk _) (mk_le_mk_of_subset (subset_inter hIX' hIY'))

end Invariant

section Instances

/-- `Finitary` matroids have a cardinality-valued rank function. -/
/-
**Matroid.invariantCardinalRank_of_finitary** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
形式化陈述：invariantCardinalRank_of_finitary [Finitary M] : InvariantCardinalRank M
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.cast_ncard`：cast_ncard {s : Set α} (hs : s.Finite) : (s.ncard : Card
inal) = Cardinal.mk s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matroid.IsBase.sdiff_finite_comm`：∀ {α : Type u_1} {M : Matroid α} {B₁ B
₂ : Set α}, M.IsBase B₁ → M.IsBase B₂ → ((B₁ \ B₂).Finite ↔ (B₂ \ B₁).Finite)
· 使用定理 `Matroid.IsBase.ncard_sdiff_comm`：∀ {α : Type u_1} {M : Matroid α} {B₁ B₂
 : Set α}, M.IsBase B₁ → M.IsBase B₂ → (B₁ \ B₂).ncard = (B₂ \ B₁).ncard
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Matroid.IsBase.insert_dep`：∀ {α : Type u_1} {M : Matroid α} {B : Set α} 
{e : α}, M.IsBase B → e ∈ M.E \ B → M.Dep (insert e B)
· 使用定理 `Matroid.IsBase.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {B : Set 
α}, M.IsBase B → B ⊆ M.E
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Matroid.Finitary.indep_of_forall_finite`：∀ {α : Type u_1} {M : Matroid α
} [self : M.Finitary] (I : Set α), (∀ J ⊆ I, J.Finite → M.Indep J) → M.Indep I
· 使用定理 `Matroid.Indep.subset`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.
Indep J → I ⊆ J → M.Indep I
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
· 使用定理 `Set.Finite.sdiff`：∀ {α : Type u} {s t : Set α}, s.Finite → (s \ t).Finit
e
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.sdiff_singleton_subset_iff`：sdiff_singleton_subset_iff : s \ {a} sub
seteq t ↔ s subseteq insert a t
· 使用引理 `Set.subset_insert_sdiff_singleton`：subset_insert_sdiff_singleton (x : α)
 (s : Set α) : s subseteq insert x (s \ {x})
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Set.sdiff_inter_self_eq_sdiff`：sdiff_inter_self_eq_sdiff {s t : Set α} :
 s \ (t inter s) = s \ t
· 使用定理 `Set.sdiff_subset_iff`：sdiff_subset_iff {s t u : Set α} : s \ t subseteq 
u ↔ s subseteq t union u
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.iUnion_subset`：iUnion_subset {s : ι -> Set α} {t : Set α} (h : foral
l i, s i subseteq t) : ⋃ i, s i subseteq t
（共 51 条，此处仅展示前 30 条）

--- 原说明 ---
`Finitary` matroids have a cardinality-valued rank function.
-/
instance invariantCardinalRank_of_finitary [Finitary M] : InvariantCardinalRank M := by
  suffices aux : ∀ ⦃B B'⦄ ⦃N : Matroid α⦄, Finitary N → N.IsBase B → N.IsBase B' →
      #(B \ B' : Set α) ≤ #(B' \ B : Set α) from
    ⟨fun I J X hI hJ ↦ (aux (restrict_finitary X) hI.isBase_restrict hJ.isBase_restrict).antisymm
      (aux (restrict_finitary X) hJ.isBase_restrict hI.isBase_restrict)⟩
  intro B B' N hfin hB hB'
  by_cases h : (B' \ B).Finite
  · rw [← cast_ncard h, ← cast_ncard, hB.ncard_sdiff_comm hB']
    exact (hB'.sdiff_finite_comm hB).mp h
  rw [← Set.Infinite, ← infinite_coe_iff] at h
  have (a : α) (ha : a ∈ B' \ B) : ∃ S : Set α, Finite S ∧ S ⊆ B ∧ ¬ N.Indep (insert a S) := by
    have := (hB.insert_dep ⟨hB'.subset_ground ha.1, ha.2⟩).1
    contrapose! this
    exact Finitary.indep_of_forall_finite _ fun J hJ fin ↦ (this (J \ {a}) fin.sdiff.to_subtype <|
      sdiff_singleton_subset_iff.mpr hJ).subset (subset_insert_sdiff_singleton ..)
  choose S S_fin hSB dep using this
  let U := ⋃ a : ↥(B' \ B), S a a.2
  suffices B \ B' ⊆ U by
    refine (mk_le_mk_of_subset this).trans <| (mk_iUnion_le ..).trans
      <| (mul_le_max_of_aleph0_le_left (by simp)).trans ?_
    simp only [sup_le_iff, le_refl, true_and]
    exact ciSup_le' fun e ↦ (lt_aleph0_of_finite _).le.trans <| by simp
  rw [← sdiff_inter_self_eq_sdiff, sdiff_subset_iff, inter_comm]
  have hUB : (B ∩ B') ∪ U ⊆ B :=
    union_subset inter_subset_left (iUnion_subset fun e ↦ (hSB e.1 e.2))
  by_contra hBU
  have ⟨a, ha, ind⟩ := hB.exists_insert_of_ssubset ⟨hUB, hBU⟩ hB'
  have : a ∈ B' \ B := ⟨ha.1, fun haB ↦ ha.2 (.inl ⟨haB, ha.1⟩)⟩
  refine dep a this (ind.subset <| insert_subset_insert <| .trans ?_ subset_union_right)
  exact subset_iUnion_of_subset ⟨a, this⟩ subset_rfl
/-
**Matroid.invariantCardinalRank_map** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
形式化陈述：invariantCardinalRank_map (M : Matroid α) [InvariantCardinalRank M] (hf : 
InjOn f M.E) : InvariantCardinalRank (M.map f hf)
参数：M : Matroid α；hf : InjOn f M.E。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Matroid.map_isBasis_iff'`：map_isBasis_iff' {I X : Set β} {hf} : (M.map f
 hf).IsBasis I X ↔ exists I₀ X₀, M.IsBasis I₀ X₀ ∧ I = f '' I₀ ∧ X = f '' X₀
· 使用定理 `Matroid.IsBasis.cardinalMk_sdiff_comm`：∀ {α : Type u} {M : Matroid α} {I
 J X : Set α} [M.InvariantCardinalRank],   M.IsBasis I X → M.IsBasis J X → Cardi
nal.mk ↑(I \ J) = Cardinal.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sdiff_self_inter`：sdiff_self_inter {s t : Set α} : s \ (s inter t) =
 s \ t
· 使用定理 `Set.sdiff_inter_self_eq_sdiff`：sdiff_inter_self_eq_sdiff {s t : Set α} :
 s \ (t inter s) = s \ t
· 使用定理 `Set.InjOn.image_inter`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {s t 
u : Set α},   Set.InjOn f u → s ⊆ u → t ⊆ u → f '' (s ∩ t) = f '' s ∩ f '' t
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.InjOn.image_sdiff`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : 
α → β} {t : Set α},   Set.InjOn f s → f '' (s \ t) = f '' s \ f '' (s ∩ t)
· 使用定理 `Set.InjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α →
 β}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁
· 使用定理 `Cardinal.lift_inj`：lift_inj {a b : Cardinal.{u}} : lift.{v, u} a = lift.
{v, u} b ↔ a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_image_eq_of_injOn_lift`：mk_image_eq_of_injOn_lift {α : Type 
u} {β : Type v} (f : α -> β) (s : Set α) (h : InjOn f s) : lift.{u} #(f '' s) = 
lift.{v} #s
· 使用定理 `Matroid.Indep.sdiff`：∀ {α : Type u_1} {M : Matroid α} {I : Set α}, M.Ind
ep I → ∀ (X : Set α), M.Indep (I \ X)
· 使用定理 `Set.InjOn.image_eq_image_iff`：∀ {α : Type u_1} {β : Type u_2} {s s₁ s₂ :
 Set α} {f : α → β},   Set.InjOn f s → s₁ ⊆ s → s₂ ⊆ s → (f '' s₁ = f '' s₂ ↔ s₁
 = s₂)
· 使用定理 `Matroid.IsBasis.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → X ⊆ M.E
-/
instance invariantCardinalRank_map (M : Matroid α) [InvariantCardinalRank M] (hf : InjOn f M.E) :
    InvariantCardinalRank (M.map f hf) := by
  refine ⟨fun I J X hI hJ ↦ ?_⟩
  obtain ⟨I, X, hIX, rfl, rfl⟩ := map_isBasis_iff'.1 hI
  obtain ⟨J, X', hJX, rfl, h'⟩ := map_isBasis_iff'.1 hJ
  obtain rfl : X = X' := by
    rwa [InjOn.image_eq_image_iff hf hIX.subset_ground hJX.subset_ground] at h'
  have hcard := hIX.cardinalMk_sdiff_comm hJX
  rwa [← lift_inj.{u, v},
    ← mk_image_eq_of_injOn_lift _ _ (hf.mono ((hIX.indep.sdiff _).subset_ground)),
    ← mk_image_eq_of_injOn_lift _ _ (hf.mono ((hJX.indep.sdiff _).subset_ground)),
    lift_inj, (hf.mono hIX.indep.subset_ground).image_sdiff,
    (hf.mono hJX.indep.subset_ground).image_sdiff, inter_comm,
    hf.image_inter hJX.indep.subset_ground hIX.indep.subset_ground,
    sdiff_inter_self_eq_sdiff, sdiff_self_inter] at hcard
/-
**Matroid.invariantCardinalRank_comap** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
形式化陈述：invariantCardinalRank_comap (M : Matroid β) [InvariantCardinalRank M] (f :
 α -> β) : InvariantCardinalRank (M.comap f)
参数：M : Matroid β；f : α -> β。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matroid.comap_isBasis_iff`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
N : Matroid β} {I X : Set α},   (N.comap f).IsBasis I X ↔ N.IsBasis (f '' I) (f 
'' X) ∧ Set.Inj…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_inj`：lift_inj {a b : Cardinal.{u}} : lift.{v, u} a = lift.
{v, u} b ↔ a = b
· 使用定理 `Cardinal.mk_image_eq_of_injOn_lift`：mk_image_eq_of_injOn_lift {α : Type 
u} {β : Type v} (f : α -> β) (s : Set α) (h : InjOn f s) : lift.{u} #(f '' s) = 
lift.{v} #s
· 使用定理 `Set.InjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α →
 β}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Set.InjOn.image_sdiff`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : 
α → β} {t : Set α},   Set.InjOn f s → f '' (s \ t) = f '' s \ f '' (s ∩ t)
· 使用定理 `Set.sdiff_union_sdiff_cancel`：sdiff_union_sdiff_cancel (hts : t subseteq
 s) (hut : u subseteq t) : s \ t union t \ u = s \ u
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.image_inter_subset`：image_inter_subset (f : α -> β) (s t : Set α) : 
f '' (s inter t) subseteq f '' s inter f '' t
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.sdiff_inter_self_eq_sdiff`：sdiff_inter_self_eq_sdiff {s t : Set α} :
 s \ (t inter s) = s \ t
· 使用定理 `Cardinal.mk_union_of_disjoint`：mk_union_of_disjoint {α : Type u} {S T : 
Set α} (H : Disjoint S T) : #(S union T : Set α) = #S + #T
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Set.disjoint_sdiff_left`：disjoint_sdiff_left : Disjoint (t \ s) s
· 使用定理 `Matroid.IsBasis.cardinalMk_sdiff_comm`：∀ {α : Type u} {M : Matroid α} {I
 J X : Set α} [M.InvariantCardinalRank],   M.IsBasis I X → M.IsBasis J X → Cardi
nal.mk ↑(I \ J) = Cardinal.…
-/
instance invariantCardinalRank_comap (M : Matroid β) [InvariantCardinalRank M] (f : α → β) :
    InvariantCardinalRank (M.comap f) := by
  refine ⟨fun I J X hI hJ ↦ ?_⟩
  obtain ⟨hI, hfI, hIX⟩ := comap_isBasis_iff.1 hI
  obtain ⟨hJ, hfJ, hJX⟩ := comap_isBasis_iff.1 hJ
  rw [← lift_inj.{u, v}, ← mk_image_eq_of_injOn_lift _ _ (hfI.mono sdiff_subset),
    ← mk_image_eq_of_injOn_lift _ _ (hfJ.mono sdiff_subset), lift_inj, hfI.image_sdiff,
    hfJ.image_sdiff, ← sdiff_union_sdiff_cancel inter_subset_left (image_inter_subset f I J),
    inter_comm, sdiff_inter_self_eq_sdiff, mk_union_of_disjoint, hI.cardinalMk_sdiff_comm hJ,
    ← sdiff_union_sdiff_cancel inter_subset_left (image_inter_subset f J I), inter_comm,
    sdiff_inter_self_eq_sdiff, mk_union_of_disjoint, inter_comm J I] <;>
  exact disjoint_sdiff_left.mono_right (sdiff_subset.trans inter_subset_left)

end Instances

/-
**Matroid.rankFinite_iff_cRank_lt_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：rankFinite_iff_cRank_lt_aleph0 : M.RankFinite ↔ M.cRank < ℵ₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lt_aleph0_iff_finite`：lt_aleph0_iff_finite {α : Type u} : #α < 
ℵ₀ ↔ Finite α
· 使用定理 `Matroid.IsBase.cardinalMk_eq_cRank`：∀ {α : Type u} {M : Matroid α} {B : 
Set α} [M.InvariantCardinalRank], M.IsBase B → Cardinal.mk ↑B = M.cRank
· 使用定理 `Matroid.exists_isBase`：∀ {α : Type u_1} (self : Matroid α), ∃ B, self.Is
Base B
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Matroid.IsBase.cardinalMk_le_cRank`：∀ {α : Type u} {M : Matroid α} {B : 
Set α}, M.IsBase B → Cardinal.mk ↑B ≤ M.cRank
-/
theorem rankFinite_iff_cRank_lt_aleph0 : M.RankFinite ↔ M.cRank < ℵ₀ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨?_⟩⟩
  · have ⟨B, hB, fin⟩ := h
    exact hB.cardinalMk_eq_cRank ▸ lt_aleph0_iff_finite.mpr fin
  have ⟨B, hB⟩ := M.exists_isBase
  simp_rw [← finite_coe_iff, ← lt_aleph0_iff_finite]
  exact ⟨B, hB, hB.cardinalMk_le_cRank.trans_lt h⟩
/-
**Matroid.rankInfinite_iff_aleph0_le_cRank** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：rankInfinite_iff_aleph0_le_cRank : M.RankInfinite ↔ ℵ₀ <= M.cRank
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Matroid.rankFinite_iff_cRank_lt_aleph0`：rankFinite_iff_cRank_lt_aleph0 :
 M.RankFinite ↔ M.cRank < ℵ₀
· 使用定理 `Matroid.not_rankFinite_iff`：not_rankFinite_iff (M : Matroid α) : ¬ RankF
inite M ↔ RankInfinite M
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem rankInfinite_iff_aleph0_le_cRank : M.RankInfinite ↔ ℵ₀ ≤ M.cRank := by
  rw [← not_lt, ← rankFinite_iff_cRank_lt_aleph0, not_rankFinite_iff]
/-
**Matroid.isRkFinite_iff_cRk_lt_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：isRkFinite_iff_cRk_lt_aleph0 : M.IsRkFinite X ↔ M.cRk X < ℵ₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsRkFinite.eq_1`：∀ {α : Type u_1} (M : Matroid α) (X : Set α), M
.IsRkFinite X = (M.restrict X).RankFinite
· 使用定理 `Matroid.rankFinite_iff_cRank_lt_aleph0`：rankFinite_iff_cRank_lt_aleph0 :
 M.RankFinite ↔ M.cRank < ℵ₀
· 使用定理 `Matroid.cRank_restrict`：∀ {α : Type u} (M : Matroid α) (X : Set α), (M.r
estrict X).cRank = M.cRk X
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isRkFinite_iff_cRk_lt_aleph0 : M.IsRkFinite X ↔ M.cRk X < ℵ₀ := by
  rw [IsRkFinite, rankFinite_iff_cRank_lt_aleph0, cRank_restrict]
/-
**Matroid.Indep.isBase_of_cRank_le** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u} {M : Matroid α} {I : Set α} [M.RankFinite], M.Indep I → M.c
Rank ≤ Cardinal.mk ↑I → M.IsBase I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.isBase_of_maximal`：∀ {α : Type u_1} {M : Matroid α} {I : S
et α}, M.Indep I → (∀ ⦃J : Set α⦄, M.Indep J → I ⊆ J → I = J) → M.IsBase I
· 使用定理 `Set.Finite.eq_of_subset_of_encard_le`：∀ {α : Type u_1} {s t : Set α}, s.
Finite → s ⊆ t → t.encard ≤ s.encard → s = t
· 使用定理 `Matroid.Indep.finite`：∀ {α : Type u_1} {M : Matroid α} {I : Set α} [M.Ra
nkFinite], M.Indep I → I.Finite
· 使用定理 `OrderRingHom.monotone'`：∀ {α : Type u_6} {β : Type u_7} [inst : NonAssoc
Semiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3 : Preo
rder β] (sel…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Matroid.Indep.cardinalMk_le_cRank`：∀ {α : Type u} {M : Matroid α} {I : S
et α}, M.Indep I → Cardinal.mk ↑I ≤ M.cRank
-/
theorem Indep.isBase_of_cRank_le [M.RankFinite] (ind : M.Indep I) (le : M.cRank ≤ #I) :
    M.IsBase I :=
  ind.isBase_of_maximal fun _J ind_J hIJ ↦ ind.finite.eq_of_subset_of_encard_le hIJ <|
    toENat.monotone' <| ind_J.cardinalMk_le_cRank.trans le
/-
**Matroid.Spanning.isBase_of_le_cRank** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Spannin
g`。
形式化陈述：∀ {α : Type u} {M : Matroid α} {X : Set α} [M.RankFinite], M.Spanning X → 
Cardinal.mk ↑X ≤ M.cRank → M.IsBase X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Spanning.exists_isBase_subset`：∀ {α : Type u_2} {M : Matroid α} 
{S : Set α}, M.Spanning S → ∃ B, M.IsBase B ∧ B ⊆ S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Finite.eq_of_subset_of_encard_le`：∀ {α : Type u_1} {s t : Set α}, s.
Finite → s ⊆ t → t.encard ≤ s.encard → s = t
· 使用定理 `Matroid.IsBase.finite`：∀ {α : Type u_1} {M : Matroid α} {B : Set α} [M.R
ankFinite], M.IsBase B → B.Finite
· 使用定理 `OrderRingHom.monotone'`：∀ {α : Type u_6} {β : Type u_7} [inst : NonAssoc
Semiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3 : Preo
rder β] (sel…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Matroid.IsBase.cardinalMk_eq_cRank`：∀ {α : Type u} {M : Matroid α} {B : 
Set α} [M.InvariantCardinalRank], M.IsBase B → Cardinal.mk ↑B = M.cRank
-/
theorem Spanning.isBase_of_le_cRank [M.RankFinite] (h : M.Spanning X) (le : #X ≤ M.cRank) :
    M.IsBase X := by
  have ⟨B, hB, hBX⟩ := h.exists_isBase_subset
  rwa [← hB.finite.eq_of_subset_of_encard_le hBX
    (toENat.monotone' <| le.trans hB.cardinalMk_eq_cRank.ge)]
/-
**Matroid.Indep.isBase_of_cRank_le_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.
Indep`。
形式化陈述：∀ {α : Type u} {M : Matroid α} {I : Set α}, M.Indep I → M.cRank ≤ Cardinal
.mk ↑I → I.Finite → M.IsBase I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matroid.rankFinite_iff_cRank_lt_aleph0`：rankFinite_iff_cRank_lt_aleph0 :
 M.RankFinite ↔ M.cRank < ℵ₀
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Cardinal.lt_aleph0_iff_finite`：lt_aleph0_iff_finite {α : Type u} : #α < 
ℵ₀ ↔ Finite α
· 使用定理 `Matroid.Indep.isBase_of_cRank_le`：∀ {α : Type u} {M : Matroid α} {I : Se
t α} [M.RankFinite], M.Indep I → M.cRank ≤ Cardinal.mk ↑I → M.IsBase I
-/
theorem Indep.isBase_of_cRank_le_of_finite (ind : M.Indep I)
    (le : M.cRank ≤ #I) (fin : I.Finite) : M.IsBase I :=
  have := rankFinite_iff_cRank_lt_aleph0.mpr (le.trans_lt <| lt_aleph0_iff_finite.mpr fin)
  ind.isBase_of_cRank_le le
/-
**Matroid.Spanning.isBase_of_le_cRank_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Matro
id.Spanning`。
形式化陈述：∀ {α : Type u} {M : Matroid α} {X : Set α}, M.Spanning X → Cardinal.mk ↑X 
≤ M.cRank → X.Finite → M.IsBase X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Spanning.exists_isBase_subset`：∀ {α : Type u_2} {M : Matroid α} 
{S : Set α}, M.Spanning S → ∃ B, M.IsBase B ∧ B ⊆ S
· 使用定理 `Matroid.IsBase.rankFinite_of_finite`：∀ {α : Type u_1} {M : Matroid α} {B
 : Set α}, M.IsBase B → B.Finite → M.RankFinite
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Matroid.Spanning.isBase_of_le_cRank`：∀ {α : Type u} {M : Matroid α} {X :
 Set α} [M.RankFinite], M.Spanning X → Cardinal.mk ↑X ≤ M.cRank → M.IsBase X
-/
theorem Spanning.isBase_of_le_cRank_of_finite (h : M.Spanning X)
    (le : #X ≤ M.cRank) (fin : X.Finite) : M.IsBase X :=
  have ⟨_B, hB, hBX⟩ := h.exists_isBase_subset
  have := hB.rankFinite_of_finite (fin.subset hBX)
  h.isBase_of_le_cRank le

@[simp]
/-
**Matroid.toENat_cRank_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：toENat_cRank_eq (M : Matroid α) : M.cRank.toENat = M.eRank
参数：M : Matroid α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.rankFinite_or_rankInfinite`：rankFinite_or_rankInfinite (M : Matr
oid α) : RankFinite M ∨ RankInfinite M
· 使用定理 `Matroid.exists_isBase`：∀ {α : Type u_1} (self : Matroid α), ∃ B, self.Is
Base B
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsBase.cardinalMk_eq_cRank`：∀ {α : Type u} {M : Matroid α} {B : 
Set α} [M.InvariantCardinalRank], M.IsBase B → Cardinal.mk ↑B = M.cRank
· 使用定理 `Matroid.IsBase.encard_eq_eRank`：∀ {α : Type u_1} {M : Matroid α} {B : Se
t α}, M.IsBase B → B.encard = M.eRank
· 使用定理 `Set.toENat_cardinalMk`：∀ {α : Type u_1} (s : Set α), Cardinal.toENat (Ca
rdinal.mk ↑s) = s.encard
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Matroid.eRank_eq_top`：eRank_eq_top [RankInfinite M] : M.eRank = ⊤
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matroid.rankInfinite_iff_aleph0_le_cRank`：rankInfinite_iff_aleph0_le_cRa
nk : M.RankInfinite ↔ ℵ₀ <= M.cRank
-/
theorem toENat_cRank_eq (M : Matroid α) : M.cRank.toENat = M.eRank := by
  obtain h | h := M.rankFinite_or_rankInfinite
  · obtain ⟨B, hB⟩ := M.exists_isBase
    rw [← hB.cardinalMk_eq_cRank, ← hB.encard_eq_eRank, toENat_cardinalMk]
  simp [rankInfinite_iff_aleph0_le_cRank.1 h]

@[simp]
/-
**Matroid.toENat_cRk_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：toENat_cRk_eq (M : Matroid α) (X : Set α) : (M.cRk X).toENat = M.eRk X
参数：M : Matroid α；X : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.cRk.eq_1`：∀ {α : Type u} (M : Matroid α) (X : Set α), M.cRk X = 
(M.restrict X).cRank
· 使用定理 `Matroid.toENat_cRank_eq`：toENat_cRank_eq (M : Matroid α) : M.cRank.toENa
t = M.eRank
· 使用定理 `Matroid.eRk.eq_1`：∀ {α : Type u_1} (M : Matroid α) (X : Set α), M.eRk X 
= (M.restrict X).eRank
-/
theorem toENat_cRk_eq (M : Matroid α) (X : Set α) : (M.cRk X).toENat = M.eRk X := by
  rw [cRk, toENat_cRank_eq, eRk]

end Matroid

