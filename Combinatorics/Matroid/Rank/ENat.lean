/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
module

public import Mathlib.Combinatorics.Matroid.Rank.Finite
public import Mathlib.Combinatorics.Matroid.Loop
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Tactic.TautoSet

/-!
# `ℕ∞`-valued rank

If the 'cardinality' of `s : Set α` is taken to mean the `ℕ∞`-valued term `Set.encard s`,
then all bases of any `M : Matroid α` have the same cardinality,
and for each `X : Set α` with `X ⊆ M.E`, all `M`-bases for `X` have the same cardinality.
The 'rank' of a matroid is the cardinality of all its bases,
and the 'rank' of a set `X` in a matroid `M` is the cardinality of each `M`-basis of `X`.
This file defines these two concepts as a term `Matroid.eRank M : ℕ∞`
and a function `Matroid.eRk M : Set α → ℕ∞` respectively.

The rank function `Matroid.eRk` satisfies three properties, often known as (R1), (R2), (R3):
* `M.eRk X ≤ Set.encard X`,
* `M.eRk X ≤ M.eRk Y` for all `X ⊆ Y`,
* `M.eRk X + M.eRk Y ≥ M.eRk (X ∪ Y) + M.eRk (X ∩ Y)` for all `X, Y`.

In fact, if `α` is finite, then any function `Set α → ℕ∞` satisfying these properties
is the rank function of a `Matroid α`; in other words, properties (R1) - (R3) give an alternative
definition of finite matroids, and a finite matroid is determined by its rank function.
Because of this, and the convenient quantitative language of these axioms,
the rank function is often the preferred perspective on matroids in the literature.
(The above doesn't work as well for infinite matroids,
which is why mathlib defines matroids using bases/independence. )

## Main Declarations

* `Matroid.eRank M` is the `ℕ∞`-valued cardinality of each base of `M`.
* `Matroid.eRk M X` is the `ℕ∞`-valued cardinality of each `M`-basis of `X`.
* `Matroid.eRk_inter_add_eRk_union_le` : the function `M.eRk` is submodular.
* `Matroid.dual_eRk_add_eRank` : a subtraction-free formula for the dual rank of a set.

## Notes

It is natural to ask if equicardinality of bases holds if 'cardinality' refers to
a term in `Cardinal` instead of `ℕ∞`, but the answer is that it doesn't.
The cardinal-valued rank functions `Matroid.cRank` and `Matroid.cRk` are defined in
`Mathlib/Combinatorics/Matroid/Rank/Cardinal.lean`, but have less desirable properties in general.
See the module docstring of that file for a discussion.

## Implementation Details

It would be equivalent to define `Matroid.eRank (M : Matroid α) := (Matroid.cRank M).toENat`
and similar for `Matroid.eRk`, and some of the API for `cRank`/`cRk` would carry over
in a way that shortens certain proofs in this file (though not substantially).
Although this file transitively imports `Cardinal` via `Set.encard`,
there are plans to refactor the latter to be independent of the former,
which would carry over to the current version of this file.
-/

@[expose] public section

open Set ENat

namespace Matroid

variable {α : Type*} {M : Matroid α} {I B X Y : Set α} {n : ℕ∞} {e f : α}

section Basic

/-- The rank `Matroid.eRank M` of `M` is the `ℕ∞`-valued cardinality of each base of `M`.
(See `Matroid.cRank` for a worse-behaved cardinal-valued version) -/
/-
**Matroid.eRank** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：eRank (M : Matroid α) : Nat∞
参数：M : Matroid α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The rank `Matroid.eRank M` of `M` is the `ℕ∞`-valued cardinality of each base of
 `M`.
(See `Matroid.cRank` for a worse-behaved cardinal-valued version)
-/
noncomputable def eRank (M : Matroid α) : ℕ∞ := ⨆ B : {B // M.IsBase B}, B.1.encard

/-- The rank `Matroid.eRk M X` of a set `X` is the `ℕ∞`-valued cardinality of each basis of `X`.
(See `Matroid.cRk` for a worse-behaved cardinal-valued version) -/
/-
**Matroid.eRk** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：eRk (M : Matroid α) (X : Set α) : Nat∞
参数：M : Matroid α；X : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The rank `Matroid.eRk M X` of a set `X` is the `ℕ∞`-valued cardinality of each b
asis of `X`.
(See `Matroid.cRk` for a worse-behaved cardinal-valued version)
-/
noncomputable def eRk (M : Matroid α) (X : Set α) : ℕ∞ := (M ↾ X).eRank
/-
**Matroid.eRank_def** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRank_def (M : Matroid α) : M.eRank = M.eRk M.E
参数：M : Matroid α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.eRk.eq_1`：∀ {α : Type u_1} (M : Matroid α) (X : Set α), M.eRk X 
= (M.restrict X).eRank
· 使用定理 `Matroid.restrict_ground_eq_self`：∀ {α : Type u_1} (M : Matroid α), M.res
trict M.E = M
-/
lemma eRank_def (M : Matroid α) : M.eRank = M.eRk M.E := by
  rw [eRk, restrict_ground_eq_self]

@[simp]
/-
**Matroid.eRk_ground** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_ground (M : Matroid α) : M.eRk M.E = M.eRank
参数：M : Matroid α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.eRank_def`：eRank_def (M : Matroid α) : M.eRank = M.eRk M.E
-/
lemma eRk_ground (M : Matroid α) : M.eRk M.E = M.eRank :=
  M.eRank_def.symm

@[simp]
/-
**Matroid.eRank_restrict** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRank_restrict (M : Matroid α) (X : Set α) : (M ↾ X).eRank = M.eRk X
参数：M : Matroid α；X : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eRank_restrict (M : Matroid α) (X : Set α) : (M ↾ X).eRank = M.eRk X := rfl
/-
**Matroid.IsBase.encard_eq_eRank** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B : Set α}, M.IsBase B → B.encard = M.eR
ank
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matroid.IsBase.encard_eq_encard_of_isBase`：∀ {α : Type u_1} {M : Matroid
 α} {B₁ B₂ : Set α}, M.IsBase B₁ → M.IsBase B₂ → B₁.encard = B₂.encard
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `ciSup_const`：ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a
· 使用定理 `Matroid.instNonemptySubtypeSetIsBase`：∀ {α : Type u_1} (M : Matroid α), 
Nonempty { B // M.IsBase B }
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsBase.encard_eq_eRank (hB : M.IsBase B) : B.encard = M.eRank := by
  simp [eRank, show ∀ B' : {B // M.IsBase B}, B'.1.encard = B.encard from
    fun B' ↦ B'.2.encard_eq_encard_of_isBase hB]
/-
**Matroid.IsBasis'.encard_eq_eRk** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis'`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M.IsBasis' I X → I.encard 
= M.eRk X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBase.encard_eq_eRank`：∀ {α : Type u_1} {M : Matroid α} {B : Se
t α}, M.IsBase B → B.encard = M.eRank
· 使用定理 `Matroid.IsBasis'.isBase_restrict`：∀ {α : Type u_1} {M : Matroid α} {I X 
: Set α}, M.IsBasis' I X → (M.restrict X).IsBase I
-/
lemma IsBasis'.encard_eq_eRk (hI : M.IsBasis' I X) : I.encard = M.eRk X :=
  hI.isBase_restrict.encard_eq_eRank
/-
**Matroid.IsBasis.encard_eq_eRk** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M.IsBasis I X → I.encard =
 M.eRk X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis'.encard_eq_eRk`：∀ {α : Type u_1} {M : Matroid α} {I X : 
Set α}, M.IsBasis' I X → I.encard = M.eRk X
· 使用定理 `Matroid.IsBasis.isBasis'`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}
, M.IsBasis I X → M.IsBasis' I X
-/
lemma IsBasis.encard_eq_eRk (hI : M.IsBasis I X) : I.encard = M.eRk X :=
  hI.isBasis'.encard_eq_eRk
/-
**Matroid.eq_eRk_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eq_eRk_iff (hX : X subseteq M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Matroid.exists_isBasis`：exists_isBasis (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsBasis.encard_eq_eRk`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → I.encard = M.eRk X
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma eq_eRk_iff (hX : X ⊆ M.E := by aesop_mat) :
    M.eRk X = n ↔ ∃ I, M.IsBasis I X ∧ I.encard = n :=
  ⟨fun h ↦ (M.exists_isBasis X).elim (fun I hI ↦ ⟨I, hI, by rw [hI.encard_eq_eRk, ← h]⟩),
    fun ⟨I, hI, hIc⟩ ↦ by rw [← hI.encard_eq_eRk, hIc]⟩
/-
**Matroid.Indep.eRk_eq_encard** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I : Set α}, M.Indep I → M.eRk I = I.enca
rd
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Matroid.eq_eRk_iff`：eq_eRk_iff (hX : X subseteq M.E
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `Matroid.Indep.isBasis_self`：∀ {α : Type u_1} {M : Matroid α} {I : Set α}
, M.Indep I → M.IsBasis I I
-/
lemma Indep.eRk_eq_encard (hI : M.Indep I) : M.eRk I = I.encard :=
  (eq_eRk_iff hI.subset_ground).mpr ⟨I, hI.isBasis_self, rfl⟩
/-
**Matroid.IsBasis'.eRk_eq_eRk** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis'`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M.IsBasis' I X → M.eRk I =
 M.eRk X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsBasis'.encard_eq_eRk`：∀ {α : Type u_1} {M : Matroid α} {I X : 
Set α}, M.IsBasis' I X → I.encard = M.eRk X
· 使用定理 `Matroid.Indep.eRk_eq_encard`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → M.eRk I = I.encard
· 使用定理 `Matroid.IsBasis'.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis' I X → M.Indep I
-/
lemma IsBasis'.eRk_eq_eRk (hIX : M.IsBasis' I X) : M.eRk I = M.eRk X := by
  rw [← hIX.encard_eq_eRk, hIX.indep.eRk_eq_encard]
/-
**Matroid.IsBasis.eRk_eq_eRk** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M.IsBasis I X → M.eRk I = 
M.eRk X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsBasis.encard_eq_eRk`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → I.encard = M.eRk X
· 使用定理 `Matroid.Indep.eRk_eq_encard`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → M.eRk I = I.encard
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
-/
lemma IsBasis.eRk_eq_eRk (hIX : M.IsBasis I X) : M.eRk I = M.eRk X := by
  rw [← hIX.encard_eq_eRk, hIX.indep.eRk_eq_encard]
/-
**Matroid.IsBasis'.eRk_eq_encard** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis'`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M.IsBasis' I X → M.eRk X =
 I.encard
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsBasis'.eRk_eq_eRk`：∀ {α : Type u_1} {M : Matroid α} {I X : Set
 α}, M.IsBasis' I X → M.eRk I = M.eRk X
· 使用定理 `Matroid.Indep.eRk_eq_encard`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → M.eRk I = I.encard
· 使用定理 `Matroid.IsBasis'.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis' I X → M.Indep I
-/
lemma IsBasis'.eRk_eq_encard (hIX : M.IsBasis' I X) : M.eRk X = I.encard := by
  rw [← hIX.eRk_eq_eRk, hIX.indep.eRk_eq_encard]
/-
**Matroid.IsBasis.eRk_eq_encard** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M.IsBasis I X → M.eRk X = 
I.encard
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsBasis.eRk_eq_eRk`：∀ {α : Type u_1} {M : Matroid α} {I X : Set 
α}, M.IsBasis I X → M.eRk I = M.eRk X
· 使用定理 `Matroid.Indep.eRk_eq_encard`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → M.eRk I = I.encard
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
-/
lemma IsBasis.eRk_eq_encard (hIX : M.IsBasis I X) : M.eRk X = I.encard := by
  rw [← hIX.eRk_eq_eRk, hIX.indep.eRk_eq_encard]
/-
**Matroid.IsBase.eRk_eq_eRank** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B : Set α}, M.IsBase B → M.eRk B = M.eRa
nk
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.Indep.eRk_eq_encard`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → M.eRk I = I.encard
· 使用定理 `Matroid.IsBase.indep`：∀ {α : Type u_1} {M : Matroid α} {B : Set α}, M.Is
Base B → M.Indep B
· 使用引理 `Matroid.eRank_def`：eRank_def (M : Matroid α) : M.eRank = M.eRk M.E
· 使用定理 `Matroid.IsBasis.encard_eq_eRk`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → I.encard = M.eRk X
· 使用定理 `Matroid.IsBase.isBasis_ground`：∀ {α : Type u_1} {M : Matroid α} {B : Set
 α}, M.IsBase B → M.IsBasis B M.E
-/
lemma IsBase.eRk_eq_eRank (hB : M.IsBase B) : M.eRk B = M.eRank := by
  rw [hB.indep.eRk_eq_encard, eRank_def, hB.isBasis_ground.encard_eq_eRk]

@[simp]
/-
**Matroid.eRk_inter_ground** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_inter_ground (M : Matroid α) (X : Set α) : M.eRk (X inter M.E) = M.eRk
 X
参数：M : Matroid α；X : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBasis'`：exists_isBasis' (M : Matroid α) (X : Set α) : e
xists I, M.IsBasis' I X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsBasis'.eRk_eq_eRk`：∀ {α : Type u_1} {M : Matroid α} {I X : Set
 α}, M.IsBasis' I X → M.eRk I = M.eRk X
· 使用定理 `Matroid.IsBasis.eRk_eq_eRk`：∀ {α : Type u_1} {M : Matroid α} {I X : Set 
α}, M.IsBasis I X → M.eRk I = M.eRk X
· 使用定理 `Matroid.IsBasis'.isBasis_inter_ground`：∀ {α : Type u_1} {M : Matroid α} 
{I X : Set α}, M.IsBasis' I X → M.IsBasis I (X ∩ M.E)
-/
lemma eRk_inter_ground (M : Matroid α) (X : Set α) : M.eRk (X ∩ M.E) = M.eRk X := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [← hI.eRk_eq_eRk, hI.isBasis_inter_ground.eRk_eq_eRk]

@[simp]
/-
**Matroid.eRk_ground_inter** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_ground_inter (M : Matroid α) (X : Set α) : M.eRk (M.E inter X) = M.eRk
 X
参数：M : Matroid α；X : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用引理 `Matroid.eRk_inter_ground`：eRk_inter_ground (M : Matroid α) (X : Set α) :
 M.eRk (X inter M.E) = M.eRk X
-/
lemma eRk_ground_inter (M : Matroid α) (X : Set α) : M.eRk (M.E ∩ X) = M.eRk X := by
  rw [inter_comm, eRk_inter_ground]

@[simp]
/-
**Matroid.eRk_union_ground** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_union_ground (M : Matroid α) (X : Set α) : M.eRk (X union M.E) = M.eRa
nk
参数：M : Matroid α；X : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.eRk_inter_ground`：eRk_inter_ground (M : Matroid α) (X : Set α) :
 M.eRk (X inter M.E) = M.eRk X
· 使用定理 `Set.inter_eq_self_of_subset_right`：inter_eq_self_of_subset_right {s t : 
Set α} : t subseteq s -> s inter t = t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用引理 `Matroid.eRank_def`：eRank_def (M : Matroid α) : M.eRank = M.eRk M.E
-/
lemma eRk_union_ground (M : Matroid α) (X : Set α) : M.eRk (X ∪ M.E) = M.eRank := by
  rw [← eRk_inter_ground, inter_eq_self_of_subset_right subset_union_right, eRank_def]

@[simp]
/-
**Matroid.eRk_ground_union** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_ground_union (M : Matroid α) (X : Set α) : M.eRk (M.E union X) = M.eRa
nk
参数：M : Matroid α；X : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用引理 `Matroid.eRk_union_ground`：eRk_union_ground (M : Matroid α) (X : Set α) :
 M.eRk (X union M.E) = M.eRank
-/
lemma eRk_ground_union (M : Matroid α) (X : Set α) : M.eRk (M.E ∪ X) = M.eRank := by
  rw [union_comm, eRk_union_ground]
/-
**Matroid.eRk_insert_of_notMem_ground** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_insert_of_notMem_ground (X : Set α) (he : e ∉ M.E) : M.eRk (insert e X
) = M.eRk X
参数：X : Set α；he : e ∉ M.E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.eRk_inter_ground`：eRk_inter_ground (M : Matroid α) (X : Set α) :
 M.eRk (X inter M.E) = M.eRk X
· 使用定理 `Set.insert_inter_of_notMem`：insert_inter_of_notMem (h : a ∉ t) : insert 
a s inter t = s inter t
-/
lemma eRk_insert_of_notMem_ground (X : Set α) (he : e ∉ M.E) : M.eRk (insert e X) = M.eRk X := by
  rw [← eRk_inter_ground, insert_inter_of_notMem he, eRk_inter_ground]
/-
**Matroid.eRk_eq_eRank** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_eq_eRank (hX : M.E subseteq X) : M.eRk X = M.eRank
参数：hX : M.E subseteq X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.eRk_inter_ground`：eRk_inter_ground (M : Matroid α) (X : Set α) :
 M.eRk (X inter M.E) = M.eRk X
· 使用定理 `Set.inter_eq_self_of_subset_right`：inter_eq_self_of_subset_right {s t : 
Set α} : t subseteq s -> s inter t = t
· 使用引理 `Matroid.eRank_def`：eRank_def (M : Matroid α) : M.eRank = M.eRk M.E
-/
lemma eRk_eq_eRank (hX : M.E ⊆ X) : M.eRk X = M.eRank := by
  rw [← eRk_inter_ground, inter_eq_self_of_subset_right hX, eRank_def]
/-
**Matroid.eRk_compl_union_of_disjoint** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_compl_union_of_disjoint (M : Matroid α) (hXY : Disjoint X Y) : M.eRk (
M.E \ X union Y) = M.eRk (M.E \ X)
参数：M : Matroid α；hXY : Disjoint X Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.eRk_inter_ground`：eRk_inter_ground (M : Matroid α) (X : Set α) :
 M.eRk (X inter M.E) = M.eRk X
· 使用定理 `Set.union_inter_distrib_right`：union_inter_distrib_right (s t u : Set α)
 : (s union t) inter u = s inter u union t inter u
· 使用定理 `Set.inter_eq_self_of_subset_left`：inter_eq_self_of_subset_left {s t : Se
t α} : s subseteq t -> s inter t = s
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Set.union_eq_self_of_subset_right`：union_eq_self_of_subset_right {s t : 
Set α} (h : t subseteq s) : s union t = s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.subset_sdiff`：subset_sdiff : s subseteq t \ u ↔ s subseteq t ∧ Disjo
int s u
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
-/
lemma eRk_compl_union_of_disjoint (M : Matroid α) (hXY : Disjoint X Y) :
    M.eRk (M.E \ X ∪ Y) = M.eRk (M.E \ X) := by
  rw [← eRk_inter_ground, union_inter_distrib_right, inter_eq_self_of_subset_left sdiff_subset,
    union_eq_self_of_subset_right
      (subset_sdiff.2 ⟨inter_subset_right, hXY.symm.mono_left inter_subset_left⟩)]
/-
**Matroid.one_le_eRank** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：one_le_eRank (M : Matroid α) [RankPos M] : 1 <= M.eRank
参数：M : Matroid α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBase`：∀ {α : Type u_1} (self : Matroid α), ∃ B, self.Is
Base B
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsBase.encard_eq_eRank`：∀ {α : Type u_1} {M : Matroid α} {B : Se
t α}, M.IsBase B → B.encard = M.eRank
· 使用定理 `Set.one_le_encard_iff_nonempty`：∀ {α : Type u_1} {s : Set α}, 1 ≤ s.enca
rd ↔ s.Nonempty
· 使用定理 `Matroid.IsBase.nonempty`：∀ {α : Type u_1} {M : Matroid α} {B : Set α} [M
.RankPos], M.IsBase B → B.Nonempty
-/
lemma one_le_eRank (M : Matroid α) [RankPos M] : 1 ≤ M.eRank := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [← hB.encard_eq_eRank, one_le_encard_iff_nonempty]
  exact hB.nonempty

@[simp]
/-
**Matroid.eRk_univ_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_univ_eq (M : Matroid α) : M.eRk univ = M.eRank
参数：M : Matroid α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.eRk_inter_ground`：eRk_inter_ground (M : Matroid α) (X : Set α) :
 M.eRk (X inter M.E) = M.eRk X
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用引理 `Matroid.eRank_def`：eRank_def (M : Matroid α) : M.eRank = M.eRk M.E
-/
lemma eRk_univ_eq (M : Matroid α) : M.eRk univ = M.eRank := by
  rw [← eRk_inter_ground, univ_inter, eRank_def]

@[simp]
/-
**Matroid.eRk_empty** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_empty (M : Matroid α) : M.eRk ∅ = 0
参数：M : Matroid α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsBasis.encard_eq_eRk`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → I.encard = M.eRk X
· 使用定理 `Matroid.Indep.isBasis_self`：∀ {α : Type u_1} {M : Matroid α} {I : Set α}
, M.Indep I → M.IsBasis I I
· 使用定理 `Matroid.empty_indep`：∀ {α : Type u_1} (M : Matroid α), M.Indep ∅
· 使用定理 `Set.encard_empty`：∀ {α : Type u_1}, ∅.encard = 0
-/
lemma eRk_empty (M : Matroid α) : M.eRk ∅ = 0 := by
  rw [← M.empty_indep.isBasis_self.encard_eq_eRk, encard_empty]

@[simp]
/-
**Matroid.eRk_closure_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_closure_eq (M : Matroid α) (X : Set α) : M.eRk (M.closure X) = M.eRk X
参数：M : Matroid α；X : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBasis'`：exists_isBasis' (M : Matroid α) (X : Set α) : e
xists I, M.IsBasis' I X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsBasis'.closure_eq_closure`：∀ {α : Type u_2} {M : Matroid α} {X
 I : Set α}, M.IsBasis' I X → M.closure I = M.closure X
· 使用定理 `Matroid.IsBasis.encard_eq_eRk`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → I.encard = M.eRk X
· 使用定理 `Matroid.Indep.isBasis_closure`：∀ {α : Type u_2} {M : Matroid α} {I : Set
 α}, M.Indep I → M.IsBasis I (M.closure I)
· 使用定理 `Matroid.IsBasis'.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis' I X → M.Indep I
· 使用定理 `Matroid.IsBasis'.encard_eq_eRk`：∀ {α : Type u_1} {M : Matroid α} {I X : 
Set α}, M.IsBasis' I X → I.encard = M.eRk X
-/
lemma eRk_closure_eq (M : Matroid α) (X : Set α) : M.eRk (M.closure X) = M.eRk X := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [← hI.closure_eq_closure, ← hI.indep.isBasis_closure.encard_eq_eRk, hI.encard_eq_eRk]

@[simp]
/-
**Matroid.eRk_union_closure_right_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_union_closure_right_eq (M : Matroid α) (X Y : Set α) : M.eRk (X union 
M.closure Y) = M.eRk (X union Y)
参数：M : Matroid α；X Y : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.eRk_closure_eq`：eRk_closure_eq (M : Matroid α) (X : Set α) : M.e
Rk (M.closure X) = M.eRk X
· 使用定理 `Matroid.closure_union_closure_right_eq`：∀ {α : Type u_2} (M : Matroid α)
 (X Y : Set α), M.closure (X ∪ M.closure Y) = M.closure (X ∪ Y)
-/
lemma eRk_union_closure_right_eq (M : Matroid α) (X Y : Set α) :
    M.eRk (X ∪ M.closure Y) = M.eRk (X ∪ Y) := by
  rw [← eRk_closure_eq, closure_union_closure_right_eq, eRk_closure_eq]

@[simp]
/-
**Matroid.eRk_union_closure_left_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_union_closure_left_eq (M : Matroid α) (X Y : Set α) : M.eRk (M.closure
 X union Y) = M.eRk (X union Y)
参数：M : Matroid α；X Y : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.eRk_closure_eq`：eRk_closure_eq (M : Matroid α) (X : Set α) : M.e
Rk (M.closure X) = M.eRk X
· 使用定理 `Matroid.closure_union_closure_left_eq`：∀ {α : Type u_2} (M : Matroid α) 
(X Y : Set α), M.closure (M.closure X ∪ Y) = M.closure (X ∪ Y)
-/
lemma eRk_union_closure_left_eq (M : Matroid α) (X Y : Set α) :
    M.eRk (M.closure X ∪ Y) = M.eRk (X ∪ Y) := by
  rw [← eRk_closure_eq, closure_union_closure_left_eq, eRk_closure_eq]

@[simp]
/-
**Matroid.eRk_insert_closure_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_insert_closure_eq (M : Matroid α) (e : α) (X : Set α) : M.eRk (insert 
e (M.closure X)) = M.eRk (insert e X)
参数：M : Matroid α；e : α；X : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用引理 `Matroid.eRk_union_closure_left_eq`：eRk_union_closure_left_eq (M : Matroi
d α) (X Y : Set α) : M.eRk (M.closure X union Y) = M.eRk (X union Y)
-/
lemma eRk_insert_closure_eq (M : Matroid α) (e : α) (X : Set α) :
    M.eRk (insert e (M.closure X)) = M.eRk (insert e X) := by
  rw [← union_singleton, eRk_union_closure_left_eq, union_singleton]

/-- A version of `Matroid.restrict_eRk_eq` with no `X ⊆ R` hypothesis and thus a less simple RHS. -/
@[simp]
/-
**Matroid.restrict_eRk_eq'** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：restrict_eRk_eq' (M : Matroid α) (R X : Set α) : (M ↾ R).eRk X = M.eRk (X 
inter R)
参数：M : Matroid α；R X : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBasis'`：exists_isBasis' (M : Matroid α) (X : Set α) : e
xists I, M.IsBasis' I X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsBasis'.eRk_eq_encard`：∀ {α : Type u_1} {M : Matroid α} {I X : 
Set α}, M.IsBasis' I X → M.eRk X = I.encard
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.eRk_inter_ground`：eRk_inter_ground (M : Matroid α) (X : Set α) :
 M.eRk (X inter M.E) = M.eRk X
· 使用定理 `Matroid.IsBasis.eRk_eq_encard`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → M.eRk X = I.encard
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Matroid.restrict_ground_eq`：∀ {α : Type u_1} {M : Matroid α} {R : Set α}
, (M.restrict R).E = R
· 使用定理 `Matroid.isBasis_restrict_iff'`：isBasis_restrict_iff' : (M ↾ R).IsBasis I
 X ↔ M.IsBasis I (X inter M.E) ∧ X subseteq R
· 使用定理 `Matroid.isBasis'_iff_isBasis_inter_ground`：∀ {α : Type u_1} {M : Matroid
 α} {I X : Set α}, M.IsBasis' I X ↔ M.IsBasis I (X ∩ M.E)

--- 原说明 ---
A version of `Matroid.restrict_eRk_eq` with no `X ⊆ R` hypothesis and thus a les
s simple RHS.
-/
lemma restrict_eRk_eq' (M : Matroid α) (R X : Set α) : (M ↾ R).eRk X = M.eRk (X ∩ R) := by
  obtain ⟨I, hI⟩ := (M ↾ R).exists_isBasis' X
  rw [hI.eRk_eq_encard]
  rw [isBasis'_iff_isBasis_inter_ground, isBasis_restrict_iff', restrict_ground_eq] at hI
  rw [← eRk_inter_ground, ← hI.1.eRk_eq_encard]
/-
**Matroid.restrict_eRk_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：restrict_eRk_eq (M : Matroid α) {R : Set α} (h : X subseteq R) : (M ↾ R).e
Rk X = M.eRk X
参数：M : Matroid α；h : X subseteq R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.restrict_eRk_eq'`：restrict_eRk_eq' (M : Matroid α) (R X : Set α)
 : (M ↾ R).eRk X = M.eRk (X inter R)
· 使用定理 `Set.inter_eq_self_of_subset_left`：inter_eq_self_of_subset_left {s t : Se
t α} : s subseteq t -> s inter t = s
-/
lemma restrict_eRk_eq (M : Matroid α) {R : Set α} (h : X ⊆ R) : (M ↾ R).eRk X = M.eRk X := by
  rw [restrict_eRk_eq', inter_eq_self_of_subset_left h]
/-
**Matroid.IsBasis'.eRk_eq_eRk_union** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis'`
。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M.IsBasis' I X → ∀ (Y : Se
t α), M.eRk (I ∪ Y) = M.eRk (X ∪ Y)
参数：Y : Set α；I ∪ Y；X ∪ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.eRk_union_closure_left_eq`：eRk_union_closure_left_eq (M : Matroi
d α) (X Y : Set α) : M.eRk (M.closure X union Y) = M.eRk (X union Y)
· 使用定理 `Matroid.IsBasis'.closure_eq_closure`：∀ {α : Type u_2} {M : Matroid α} {X
 I : Set α}, M.IsBasis' I X → M.closure I = M.closure X
-/
lemma IsBasis'.eRk_eq_eRk_union (hIX : M.IsBasis' I X) (Y : Set α) :
    M.eRk (I ∪ Y) = M.eRk (X ∪ Y) := by
  rw [← eRk_union_closure_left_eq, hIX.closure_eq_closure, eRk_union_closure_left_eq]
/-
**Matroid.IsBasis'.eRk_eq_eRk_insert** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis'
`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M.IsBasis' I X → ∀ (e : α)
, M.eRk (insert e I) = M.eRk (insert e X)
参数：e : α；insert e I；insert e X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `Matroid.IsBasis'.eRk_eq_eRk_union`：∀ {α : Type u_1} {M : Matroid α} {I X
 : Set α}, M.IsBasis' I X → ∀ (Y : Set α), M.eRk (I ∪ Y) = M.eRk (X ∪ Y)
-/
lemma IsBasis'.eRk_eq_eRk_insert (hIX : M.IsBasis' I X) (e : α) :
    M.eRk (insert e I) = M.eRk (insert e X) := by
  rw [← union_singleton, hIX.eRk_eq_eRk_union, union_singleton]
/-
**Matroid.IsBasis.eRk_eq_eRk_union** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M.IsBasis I X → ∀ (Y : Set
 α), M.eRk (I ∪ Y) = M.eRk (X ∪ Y)
参数：Y : Set α；I ∪ Y；X ∪ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis'.eRk_eq_eRk_union`：∀ {α : Type u_1} {M : Matroid α} {I X
 : Set α}, M.IsBasis' I X → ∀ (Y : Set α), M.eRk (I ∪ Y) = M.eRk (X ∪ Y)
· 使用定理 `Matroid.IsBasis.isBasis'`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}
, M.IsBasis I X → M.IsBasis' I X
-/
lemma IsBasis.eRk_eq_eRk_union (hIX : M.IsBasis I X) (Y : Set α) : M.eRk (I ∪ Y) = M.eRk (X ∪ Y) :=
  hIX.isBasis'.eRk_eq_eRk_union Y
/-
**Matroid.IsBasis.eRk_eq_eRk_insert** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M.IsBasis I X → ∀ (e : α),
 M.eRk (insert e I) = M.eRk (insert e X)
参数：e : α；insert e I；insert e X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `Matroid.IsBasis.eRk_eq_eRk_union`：∀ {α : Type u_1} {M : Matroid α} {I X 
: Set α}, M.IsBasis I X → ∀ (Y : Set α), M.eRk (I ∪ Y) = M.eRk (X ∪ Y)
-/
lemma IsBasis.eRk_eq_eRk_insert (hIX : M.IsBasis I X) (e : α) :
    M.eRk (insert e I) = M.eRk (insert e X) := by
  rw [← union_singleton, hIX.eRk_eq_eRk_union, union_singleton]
/-
**Matroid.eRk_le_encard** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_le_encard (M : Matroid α) (X : Set α) : M.eRk X <= X.encard
参数：M : Matroid α；X : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBasis'`：exists_isBasis' (M : Matroid α) (X : Set α) : e
xists I, M.IsBasis' I X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsBasis'.eRk_eq_encard`：∀ {α : Type u_1} {M : Matroid α} {I X : 
Set α}, M.IsBasis' I X → M.eRk X = I.encard
· 使用定理 `Set.encard_mono`：encard_mono {α : Type*} : Monotone (encard : Set α -> N
at∞)
· 使用定理 `Matroid.IsBasis'.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α},
 M.IsBasis' I X → I ⊆ X
-/
lemma eRk_le_encard (M : Matroid α) (X : Set α) : M.eRk X ≤ X.encard := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [hI.eRk_eq_encard]
  exact encard_mono hI.subset
/-
**Matroid.eRank_le_encard_ground** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRank_le_encard_ground (M : Matroid α) : M.eRank <= M.E.encard
参数：M : Matroid α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用引理 `Matroid.eRank_def`：eRank_def (M : Matroid α) : M.eRank = M.eRk M.E
· 使用引理 `Matroid.eRk_le_encard`：eRk_le_encard (M : Matroid α) (X : Set α) : M.eRk
 X <= X.encard
-/
lemma eRank_le_encard_ground (M : Matroid α) : M.eRank ≤ M.E.encard :=
  M.eRank_def.trans_le <| M.eRk_le_encard M.E
/-
**Matroid.eRk_mono** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_mono (M : Matroid α) : Monotone M.eRk
参数：M : Matroid α。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsBasis'.eRk_eq_encard`：∀ {α : Type u_1} {M : Matroid α} {I X : 
Set α}, M.IsBasis' I X → M.eRk X = I.encard
· 使用定理 `Set.encard_mono`：encard_mono {α : Type*} : Monotone (encard : Set α -> N
at∞)
-/
lemma eRk_mono (M : Matroid α) : Monotone M.eRk := by
  rintro X Y (hXY : X ⊆ Y)
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_isBasis'_of_subset (hI.subset.trans hXY)
  rw [hI.eRk_eq_encard, hJ.eRk_eq_encard]
  exact encard_mono hIJ
/-
**Matroid.eRk_le_eRank** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_le_eRank (M : Matroid α) (X : Set α) : M.eRk X <= M.eRank
参数：M : Matroid α；X : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.eRank_def`：eRank_def (M : Matroid α) : M.eRank = M.eRk M.E
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.eRk_inter_ground`：eRk_inter_ground (M : Matroid α) (X : Set α) :
 M.eRk (X inter M.E) = M.eRk X
· 使用引理 `Matroid.eRk_mono`：eRk_mono (M : Matroid α) : Monotone M.eRk
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
lemma eRk_le_eRank (M : Matroid α) (X : Set α) : M.eRk X ≤ M.eRank := by
  rw [eRank_def, ← eRk_inter_ground]; exact M.eRk_mono inter_subset_right
/-
**Matroid.eRk_eq_eRk_of_subset_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_eq_eRk_of_subset_of_le (hXY : X subseteq Y) (hYX : M.eRk Y <= M.eRk X)
 : M.eRk X = M.eRk Y
参数：hXY : X subseteq Y；hYX : M.eRk Y <= M.eRk X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用引理 `Matroid.eRk_mono`：eRk_mono (M : Matroid α) : Monotone M.eRk
-/
lemma eRk_eq_eRk_of_subset_of_le (hXY : X ⊆ Y) (hYX : M.eRk Y ≤ M.eRk X) : M.eRk X = M.eRk Y :=
  (M.eRk_mono hXY).antisymm hYX
/-
**Matroid.le_eRk_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：le_eRk_iff : n <= M.eRk X ↔ exists I, I subseteq X ∧ M.Indep I ∧ I.encard 
= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBasis'`：exists_isBasis' (M : Matroid α) (X : Set α) : e
xists I, M.IsBasis' I X
· 使用定理 `Set.exists_subset_encard_eq`：exists_subset_encard_eq {k : Nat∞} (hk : k 
<= s.encard) : exists t, t subseteq s ∧ t.encard = k
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsBasis'.encard_eq_eRk`：∀ {α : Type u_1} {M : Matroid α} {I X : 
Set α}, M.IsBasis' I X → I.encard = M.eRk X
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Matroid.IsBasis'.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α},
 M.IsBasis' I X → I ⊆ X
· 使用定理 `Matroid.Indep.subset`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.
Indep J → I ⊆ J → M.Indep I
· 使用定理 `Matroid.IsBasis'.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis' I X → M.Indep I
· 使用定理 `Matroid.Indep.eRk_eq_encard`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → M.eRk I = I.encard
· 使用引理 `Matroid.eRk_mono`：eRk_mono (M : Matroid α) : Monotone M.eRk
-/
lemma le_eRk_iff : n ≤ M.eRk X ↔ ∃ I, I ⊆ X ∧ M.Indep I ∧ I.encard = n := by
  refine ⟨fun h ↦ ?_, fun ⟨I, hIX, hI, hIc⟩ ↦ ?_⟩
  · obtain ⟨J, hJ⟩ := M.exists_isBasis' X
    rw [← hJ.encard_eq_eRk] at h
    obtain ⟨I, hIJ, rfl⟩ := exists_subset_encard_eq h
    exact ⟨_, hIJ.trans hJ.subset, hJ.indep.subset hIJ, rfl⟩
  rw [← hIc, ← hI.eRk_eq_encard]
  exact M.eRk_mono hIX
/-
**Matroid.eRk_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_le_iff : M.eRk X <= n ↔ forall ⦃I⦄, I subseteq X -> M.Indep I -> I.enc
ard <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.Indep.eRk_eq_encard`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → M.eRk I = I.encard
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Matroid.eRk_mono`：eRk_mono (M : Matroid α) : Monotone M.eRk
· 使用定理 `Matroid.exists_isBasis'`：exists_isBasis' (M : Matroid α) (X : Set α) : e
xists I, M.IsBasis' I X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsBasis'.encard_eq_eRk`：∀ {α : Type u_1} {M : Matroid α} {I X : 
Set α}, M.IsBasis' I X → I.encard = M.eRk X
· 使用定理 `Matroid.IsBasis'.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α},
 M.IsBasis' I X → I ⊆ X
· 使用定理 `Matroid.IsBasis'.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis' I X → M.Indep I
-/
lemma eRk_le_iff : M.eRk X ≤ n ↔ ∀ ⦃I⦄, I ⊆ X → M.Indep I → I.encard ≤ n := by
  refine ⟨fun h I hIX hI ↦ (hI.eRk_eq_encard.symm.trans_le ((M.eRk_mono hIX).trans h)), fun h ↦ ?_⟩
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [← hI.encard_eq_eRk]
  exact h hI.subset hI.indep
/-
**Matroid.Indep.encard_le_eRk_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep
`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M.Indep I → I ⊆ X → I.enca
rd ≤ M.eRk X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matroid.eRk_mono`：eRk_mono (M : Matroid α) : Monotone M.eRk
· 使用定理 `Matroid.Indep.eRk_eq_encard`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → M.eRk I = I.encard
-/
lemma Indep.encard_le_eRk_of_subset (hI : M.Indep I) (hIX : I ⊆ X) : I.encard ≤ M.eRk X :=
  hI.eRk_eq_encard ▸ M.eRk_mono hIX
/-
**Matroid.Indep.encard_le_eRank** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I : Set α}, M.Indep I → I.encard ≤ M.eRa
nk
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.Indep.eRk_eq_encard`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → M.eRk I = I.encard
· 使用引理 `Matroid.eRank_def`：eRank_def (M : Matroid α) : M.eRank = M.eRk M.E
· 使用引理 `Matroid.eRk_mono`：eRk_mono (M : Matroid α) : Monotone M.eRk
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
-/
lemma Indep.encard_le_eRank (hI : M.Indep I) : I.encard ≤ M.eRank := by
  rw [← hI.eRk_eq_encard, eRank_def]
  exact M.eRk_mono hI.subset_ground

/-- A version of `eRk_eq_zero_iff'` with no ground-set hypothesis. -/
/-
**Matroid.eRk_eq_zero_iff'** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_eq_zero_iff' : M.eRk X = 0 ↔ X inter M.E subseteq M.loops
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBasis`：exists_isBasis (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.eRk_inter_ground`：eRk_inter_ground (M : Matroid α) (X : Set α) :
 M.eRk (X inter M.E) = M.eRk X
· 使用定理 `Matroid.IsBasis.encard_eq_eRk`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → I.encard = M.eRk X
· 使用定理 `Set.encard_eq_zero`：∀ {α : Type u_1} {s : Set α}, s.encard = 0 ↔ s = ∅
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_empty_iff_forall_notMem`：eq_empty_iff_forall_notMem {s : Set α} :
 s = ∅ ↔ forall x, x ∉ s
· 使用定理 `Matroid.IsNonloop.not_isLoop`：∀ {α : Type u_1} {M : Matroid α} {e : α}, 
M.IsNonloop e → ¬M.IsLoop e
· 使用定理 `Matroid.Indep.isNonloop_of_mem`：∀ {α : Type u_1} {M : Matroid α} {e : α}
 {I : Set α}, M.Indep I → e ∈ I → M.IsNonloop e
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X

--- 原说明 ---
A version of `eRk_eq_zero_iff'` with no ground-set hypothesis.
-/
lemma eRk_eq_zero_iff' : M.eRk X = 0 ↔ X ∩ M.E ⊆ M.loops := by
  obtain ⟨I, hI⟩ := M.exists_isBasis (X ∩ M.E)
  rw [← eRk_inter_ground, ← hI.encard_eq_eRk, encard_eq_zero]
  refine ⟨fun h ↦ by simpa [h] using! hI, fun h ↦ eq_empty_iff_forall_notMem.2 fun e heI ↦ ?_⟩
  exact (hI.indep.isNonloop_of_mem heI).not_isLoop (h (hI.subset heI))

@[simp]
/-
**Matroid.eRk_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_eq_zero_iff (hX : X subseteq M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.eRk_eq_zero_iff'`：eRk_eq_zero_iff' : M.eRk X = 0 ↔ X inter M.E s
ubseteq M.loops
· 使用定理 `Set.inter_eq_self_of_subset_left`：inter_eq_self_of_subset_left {s t : Se
t α} : s subseteq t -> s inter t = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma eRk_eq_zero_iff (hX : X ⊆ M.E := by aesop_mat) : M.eRk X = 0 ↔ X ⊆ M.loops := by
  rw [eRk_eq_zero_iff', inter_eq_self_of_subset_left hX]

@[simp]
/-
**Matroid.eRk_loops** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_loops : M.eRk M.loops = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma eRk_loops : M.eRk M.loops = 0 := by
  simp [eRk_eq_zero_iff']

/-! ### Submodularity -/

/-- The `ℕ∞`-valued rank function is submodular. -/
/-
**Matroid.eRk_inter_add_eRk_union_le** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_inter_add_eRk_union_le (M : Matroid α) (X Y : Set α) : M.eRk (X inter 
Y) + M.eRk (X union Y) <= M.eRk X + M.eRk Y
参数：M : Matroid α；X Y : Set α。
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
· 使用定理 `Matroid.IsBasis'.eRk_eq_eRk_union`：∀ {α : Type u_1} {M : Matroid α} {I X
 : Set α}, M.IsBasis' I X → ∀ (Y : Set α), M.eRk (I ∪ Y) = M.eRk (X ∪ Y)
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `Matroid.IsBasis'.encard_eq_eRk`：∀ {α : Type u_1} {M : Matroid α} {I X : 
Set α}, M.IsBasis' I X → I.encard = M.eRk X
· 使用定理 `Set.encard_union_add_encard_inter`：encard_union_add_encard_inter (s t : 
Set α) : (s union t).encard + (s inter t).encard = s.encard + t.encard
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `Matroid.eRk_le_encard`：eRk_le_encard (M : Matroid α) (X : Set α) : M.eRk
 X <= X.encard
· 使用定理 `Set.encard_mono`：encard_mono {α : Type*} : Monotone (encard : Set α -> N
at∞)
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t

--- 原说明 ---
The `ℕ∞`-valued rank function is submodular.
-/
lemma eRk_inter_add_eRk_union_le (M : Matroid α) (X Y : Set α) :
    M.eRk (X ∩ Y) + M.eRk (X ∪ Y) ≤ M.eRk X + M.eRk Y := by
  obtain ⟨Ii, hIi⟩ := M.exists_isBasis' (X ∩ Y)
  obtain ⟨IX, hIX, hIX'⟩ :=
    hIi.indep.subset_isBasis'_of_subset (hIi.subset.trans inter_subset_left)
  obtain ⟨IY, hIY, hIY'⟩ :=
    hIi.indep.subset_isBasis'_of_subset (hIi.subset.trans inter_subset_right)
  rw [← hIX.eRk_eq_eRk_union, union_comm, ← hIY.eRk_eq_eRk_union, ← hIi.encard_eq_eRk,
    ← hIX.encard_eq_eRk, ← hIY.encard_eq_eRk, union_comm, ← encard_union_add_encard_inter, add_comm]
  exact add_le_add (eRk_le_encard _ _) (encard_mono (subset_inter hIX' hIY'))

alias eRk_submod := eRk_inter_add_eRk_union_le

/-- A version of submodularity applied to the insertion of some `e` into two sets. -/
/-
**Matroid.eRk_insert_inter_add_eRk_insert_union_le** 是 Mathlib 中的一个引理，位于命名空间 `Ma
troid`。
形式化陈述：eRk_insert_inter_add_eRk_insert_union_le (M : Matroid α) (X Y : Set α) : M
.eRk (insert e (X inter Y)) + M.eRk (insert e (X union Y)) <= M.eRk (insert e X)
 + M.eRk (insert e Y)
参数：M : Matroid α；X Y : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_inter_distrib`：insert_inter_distrib (a : α) (s t : Set α) : i
nsert a (s inter t) = insert a s inter insert a t
· 使用定理 `Set.insert_union_distrib`：insert_union_distrib (a : α) (s t : Set α) : i
nsert a (s union t) = insert a s union insert a t
· 使用定理 `Matroid.eRk_submod`：∀ {α : Type u_1} (M : Matroid α) (X Y : Set α), M.eR
k (X ∩ Y) + M.eRk (X ∪ Y) ≤ M.eRk X + M.eRk Y

--- 原说明 ---
A version of submodularity applied to the insertion of some `e` into two sets.
-/
lemma eRk_insert_inter_add_eRk_insert_union_le (M : Matroid α) (X Y : Set α) :
    M.eRk (insert e (X ∩ Y)) + M.eRk (insert e (X ∪ Y))
      ≤ M.eRk (insert e X) + M.eRk (insert e Y) := by
  rw [insert_inter_distrib, insert_union_distrib]
  apply M.eRk_submod

/-- A version of submodularity applied to the complements of two sets. -/
/-
**Matroid.eRk_compl_union_add_eRk_compl_inter_le** 是 Mathlib 中的一个引理，位于命名空间 `Matr
oid`。
形式化陈述：eRk_compl_union_add_eRk_compl_inter_le (M : Matroid α) (X Y : Set α) : M.e
Rk (M.E \ (X union Y)) + M.eRk (M.E \ (X inter Y)) <= M.eRk (M.E \ X) + M.eRk (M
.E \ Y)
参数：M : Matroid α；X Y : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sdiff_inter_sdiff`：sdiff_inter_sdiff : s \ t inter (s \ u) = s \ (t 
union u)
· 使用定理 `Set.sdiff_inter`：sdiff_inter {s t u : Set α} : s \ (t inter u) = s \ t u
nion s \ u
· 使用定理 `Matroid.eRk_submod`：∀ {α : Type u_1} (M : Matroid α) (X Y : Set α), M.eR
k (X ∩ Y) + M.eRk (X ∪ Y) ≤ M.eRk X + M.eRk Y

--- 原说明 ---
A version of submodularity applied to the complements of two sets.
-/
lemma eRk_compl_union_add_eRk_compl_inter_le (M : Matroid α) (X Y : Set α) :
    M.eRk (M.E \ (X ∪ Y)) + M.eRk (M.E \ (X ∩ Y)) ≤ M.eRk (M.E \ X) + M.eRk (M.E \ Y) := by
  rw [← sdiff_inter_sdiff, sdiff_inter]
  apply M.eRk_submod

/-- A version of submodularity applied to the complements of two insertions. -/
/-
**Matroid.eRk_compl_insert_union_add_eRk_compl_insert_inter_le** 是 Mathlib 中的一个引
理，位于命名空间 `Matroid`。
形式化陈述：eRk_compl_insert_union_add_eRk_compl_insert_inter_le (M : Matroid α) (X Y 
: Set α) : M.eRk (M.E \ insert e (X union Y)) + M.eRk (M.E \ insert e (X inter Y
)) <= M.eRk (M.E \ insert e X) + M.eRk (M.E \ insert e Y)
参数：M : Matroid α；X Y : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_union_distrib`：insert_union_distrib (a : α) (s t : Set α) : i
nsert a (s union t) = insert a s union insert a t
· 使用定理 `Set.insert_inter_distrib`：insert_inter_distrib (a : α) (s t : Set α) : i
nsert a (s inter t) = insert a s inter insert a t
· 使用引理 `Matroid.eRk_compl_union_add_eRk_compl_inter_le`：eRk_compl_union_add_eRk_
compl_inter_le (M : Matroid α) (X Y : Set α) : M.eRk (M.E \ (X union Y)) + M.eRk
 (M.E \ (X inter Y)) <= M.eRk (M.E \…

--- 原说明 ---
A version of submodularity applied to the complements of two insertions.
-/
lemma eRk_compl_insert_union_add_eRk_compl_insert_inter_le (M : Matroid α) (X Y : Set α) :
    M.eRk (M.E \ insert e (X ∪ Y)) + M.eRk (M.E \ insert e (X ∩ Y)) ≤
      M.eRk (M.E \ insert e X) + M.eRk (M.E \ insert e Y) := by
  rw [insert_union_distrib, insert_inter_distrib]
  exact M.eRk_compl_union_add_eRk_compl_inter_le (insert e X) (insert e Y)
/-
**Matroid.eRk_union_le_eRk_add_eRk** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_union_le_eRk_add_eRk (M : Matroid α) (X Y : Set α) : M.eRk (X union Y)
 <= M.eRk X + M.eRk Y
参数：M : Matroid α；X Y : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_add_self`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ b + a
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `Matroid.eRk_submod`：∀ {α : Type u_1} (M : Matroid α) (X Y : Set α), M.eR
k (X ∩ Y) + M.eRk (X ∪ Y) ≤ M.eRk X + M.eRk Y
-/
lemma eRk_union_le_eRk_add_eRk (M : Matroid α) (X Y : Set α) : M.eRk (X ∪ Y) ≤ M.eRk X + M.eRk Y :=
  le_add_self.trans (M.eRk_submod X Y)
/-
**Matroid.eRk_eq_eRk_union_eRk_le_zero** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_eq_eRk_union_eRk_le_zero (X : Set α) (hY : M.eRk Y <= 0) : M.eRk (X un
ion Y) = M.eRk X
参数：X : Set α；hY : M.eRk Y <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Matroid.eRk_union_le_eRk_add_eRk`：eRk_union_le_eRk_add_eRk (M : Matroid 
α) (X Y : Set α) : M.eRk (X union Y) <= M.eRk X + M.eRk Y
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `Matroid.eRk_mono`：eRk_mono (M : Matroid α) : Monotone M.eRk
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
-/
lemma eRk_eq_eRk_union_eRk_le_zero (X : Set α) (hY : M.eRk Y ≤ 0) : M.eRk (X ∪ Y) = M.eRk X :=
  (((M.eRk_union_le_eRk_add_eRk X Y).trans (by gcongr)).trans_eq (add_zero _)).antisymm
    (M.eRk_mono subset_union_left)
/-
**Matroid.eRk_eq_eRk_sdiff_eRk_le_zero** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_eq_eRk_sdiff_eRk_le_zero (X : Set α) (hY : M.eRk Y <= 0) : M.eRk (X \ 
Y) = M.eRk X
参数：X : Set α；hY : M.eRk Y <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.eRk_eq_eRk_union_eRk_le_zero`：eRk_eq_eRk_union_eRk_le_zero (X : 
Set α) (hY : M.eRk Y <= 0) : M.eRk (X union Y) = M.eRk X
· 使用定理 `Set.sdiff_union_self`：sdiff_union_self {s t : Set α} : s \ t union t = s
 union t
-/
lemma eRk_eq_eRk_sdiff_eRk_le_zero (X : Set α) (hY : M.eRk Y ≤ 0) : M.eRk (X \ Y) = M.eRk X := by
  rw [← eRk_eq_eRk_union_eRk_le_zero (X \ Y) hY, sdiff_union_self,
    eRk_eq_eRk_union_eRk_le_zero _ hY]

@[deprecated (since := "2026-06-03")]
alias eRk_eq_eRk_diff_eRk_le_zero := eRk_eq_eRk_sdiff_eRk_le_zero
/-
**Matroid.eRk_le_eRk_inter_add_eRk_sdiff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_le_eRk_inter_add_eRk_sdiff (M : Matroid α) (X Y : Set α) : M.eRk X <= 
M.eRk (X inter Y) + M.eRk (X \ Y)
参数：M : Matroid α；X Y : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_union_sdiff`：inter_union_sdiff (s t : Set α) : s inter t union
 s \ t = s
· 使用引理 `Matroid.eRk_union_le_eRk_add_eRk`：eRk_union_le_eRk_add_eRk (M : Matroid 
α) (X Y : Set α) : M.eRk (X union Y) <= M.eRk X + M.eRk Y
-/
lemma eRk_le_eRk_inter_add_eRk_sdiff (M : Matroid α) (X Y : Set α) :
    M.eRk X ≤ M.eRk (X ∩ Y) + M.eRk (X \ Y) := by
  nth_rw 1 [← inter_union_sdiff X Y]; apply eRk_union_le_eRk_add_eRk

@[deprecated (since := "2026-06-03")]
alias eRk_le_eRk_inter_add_eRk_diff := eRk_le_eRk_inter_add_eRk_sdiff
/-
**Matroid.eRk_le_eRk_add_eRk_sdiff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_le_eRk_add_eRk_sdiff (M : Matroid α) (h : Y subseteq X) : M.eRk X <= M
.eRk Y + M.eRk (X \ Y)
参数：M : Matroid α；h : Y subseteq X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.union_sdiff_cancel`：union_sdiff_cancel {s t : Set α} (h : s subseteq
 t) : s union t \ s = t
· 使用引理 `Matroid.eRk_union_le_eRk_add_eRk`：eRk_union_le_eRk_add_eRk (M : Matroid 
α) (X Y : Set α) : M.eRk (X union Y) <= M.eRk X + M.eRk Y
-/
lemma eRk_le_eRk_add_eRk_sdiff (M : Matroid α) (h : Y ⊆ X) :
    M.eRk X ≤ M.eRk Y + M.eRk (X \ Y) := by
  nth_rw 1 [← union_sdiff_cancel h]; apply eRk_union_le_eRk_add_eRk

@[deprecated (since := "2026-06-03")] alias eRk_le_eRk_add_eRk_diff := eRk_le_eRk_add_eRk_sdiff
/-
**Matroid.eRk_union_le_encard_add_eRk** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_union_le_encard_add_eRk (M : Matroid α) (X Y : Set α) : M.eRk (X union
 Y) <= X.encard + M.eRk Y
参数：M : Matroid α；X Y : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Matroid.eRk_union_le_eRk_add_eRk`：eRk_union_le_eRk_add_eRk (M : Matroid 
α) (X Y : Set α) : M.eRk (X union Y) <= M.eRk X + M.eRk Y
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `Matroid.eRk_le_encard`：eRk_le_encard (M : Matroid α) (X : Set α) : M.eRk
 X <= X.encard
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma eRk_union_le_encard_add_eRk (M : Matroid α) (X Y : Set α) :
    M.eRk (X ∪ Y) ≤ X.encard + M.eRk Y :=
  (M.eRk_union_le_eRk_add_eRk X Y).trans <| by grw [M.eRk_le_encard]
/-
**Matroid.eRk_union_le_eRk_add_encard** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_union_le_eRk_add_encard (M : Matroid α) (X Y : Set α) : M.eRk (X union
 Y) <= M.eRk X + Y.encard
参数：M : Matroid α；X Y : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Matroid.eRk_union_le_eRk_add_eRk`：eRk_union_le_eRk_add_eRk (M : Matroid 
α) (X Y : Set α) : M.eRk (X union Y) <= M.eRk X + M.eRk Y
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `Matroid.eRk_le_encard`：eRk_le_encard (M : Matroid α) (X : Set α) : M.eRk
 X <= X.encard
-/
lemma eRk_union_le_eRk_add_encard (M : Matroid α) (X Y : Set α) :
    M.eRk (X ∪ Y) ≤ M.eRk X + Y.encard :=
  (M.eRk_union_le_eRk_add_eRk X Y).trans <| by grw [← M.eRk_le_encard]
/-
**Matroid.eRank_le_encard_add_eRk_compl** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRank_le_encard_add_eRk_compl (M : Matroid α) (X : Set α) : M.eRank <= X.e
ncard + M.eRk (M.E \ X)
参数：M : Matroid α；X : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.eRk_inter_ground`：eRk_inter_ground (M : Matroid α) (X : Set α) :
 M.eRk (X inter M.E) = M.eRk X
· 使用引理 `Matroid.eRank_def`：eRank_def (M : Matroid α) : M.eRank = M.eRk M.E
· 使用定理 `Set.union_sdiff_self`：union_sdiff_self {s t : Set α} : s union t \ s = s
 union t
· 使用定理 `Set.union_inter_cancel_right`：union_inter_cancel_right {s t : Set α} : (
s union t) inter t = t
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `Matroid.eRk_union_le_encard_add_eRk`：eRk_union_le_encard_add_eRk (M : Ma
troid α) (X Y : Set α) : M.eRk (X union Y) <= X.encard + M.eRk Y
-/
lemma eRank_le_encard_add_eRk_compl (M : Matroid α) (X : Set α) :
    M.eRank ≤ X.encard + M.eRk (M.E \ X) :=
  le_trans (by rw [← eRk_inter_ground, eRank_def, union_sdiff_self,
    union_inter_cancel_right]) (M.eRk_union_le_encard_add_eRk X (M.E \ X))

end Basic

/-! ### Finiteness -/

/-
**Matroid.eRank_ne_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRank_ne_top_iff (M : Matroid α) : M.eRank != ⊤ ↔ M.RankFinite
参数：M : Matroid α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBase`：∀ {α : Type u_1} (self : Matroid α), ∃ B, self.Is
Base B
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsBase.encard_eq_eRank`：∀ {α : Type u_1} {M : Matroid α} {B : Se
t α}, M.IsBase B → B.encard = M.eRank
· 使用定理 `Set.encard_ne_top_iff`：encard_ne_top_iff : s.encard != ⊤ ↔ s.Finite
· 使用定理 `Matroid.IsBase.rankFinite_of_finite`：∀ {α : Type u_1} {M : Matroid α} {B
 : Set α}, M.IsBase B → B.Finite → M.RankFinite
· 使用定理 `Matroid.IsBase.finite`：∀ {α : Type u_1} {M : Matroid α} {B : Set α} [M.R
ankFinite], M.IsBase B → B.Finite

--- 原说明 ---
### Finiteness
-/
lemma eRank_ne_top_iff (M : Matroid α) : M.eRank ≠ ⊤ ↔ M.RankFinite := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [← hB.encard_eq_eRank, encard_ne_top_iff]
  exact ⟨fun h ↦ hB.rankFinite_of_finite h, fun h ↦ hB.finite⟩

@[simp]
/-
**Matroid.eRank_eq_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRank_eq_top_iff (M : Matroid α) : M.eRank = ⊤ ↔ M.RankInfinite
参数：M : Matroid α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.not_rankFinite_iff`：not_rankFinite_iff (M : Matroid α) : ¬ RankF
inite M ↔ RankInfinite M
· 使用引理 `Matroid.eRank_ne_top_iff`：eRank_ne_top_iff (M : Matroid α) : M.eRank != 
⊤ ↔ M.RankFinite
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma eRank_eq_top_iff (M : Matroid α) : M.eRank = ⊤ ↔ M.RankInfinite := by
  rw [← not_rankFinite_iff, ← eRank_ne_top_iff, not_not]

@[simp]
/-
**Matroid.eRank_lt_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRank_lt_top_iff : M.eRank < ⊤ ↔ M.RankFinite
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma eRank_lt_top_iff : M.eRank < ⊤ ↔ M.RankFinite := by
  simp [lt_top_iff_ne_top]

@[simp]
/-
**Matroid.eRank_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRank_eq_top [RankInfinite M] : M.eRank = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Matroid.eRank_eq_top_iff`：eRank_eq_top_iff (M : Matroid α) : M.eRank = ⊤
 ↔ M.RankInfinite
-/
lemma eRank_eq_top [RankInfinite M] : M.eRank = ⊤ :=
  (eRank_eq_top_iff _).2 <| by assumption

@[simp]
/-
**Matroid.eRk_eq_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_eq_top_iff : M.eRk X = ⊤ ↔ ¬ M.IsRkFinite X
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBasis'`：exists_isBasis' (M : Matroid α) (X : Set α) : e
xists I, M.IsBasis' I X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsBasis'.eRk_eq_encard`：∀ {α : Type u_1} {M : Matroid α} {I X : 
Set α}, M.IsBasis' I X → M.eRk X = I.encard
· 使用定理 `Set.encard_eq_top_iff`：∀ {α : Type u_1} {s : Set α}, s.encard = ⊤ ↔ s.In
finite
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsBasis'.finite_iff_isRkFinite`：∀ {α : Type u_1} {M : Matroid α}
 {X I : Set α}, M.IsBasis' I X → (I.Finite ↔ M.IsRkFinite X)
· 使用定理 `Set.Infinite.eq_1`：∀ {α : Type u} (s : Set α), s.Infinite = ¬s.Finite
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma eRk_eq_top_iff : M.eRk X = ⊤ ↔ ¬ M.IsRkFinite X := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [hI.eRk_eq_encard, encard_eq_top_iff, ← hI.finite_iff_isRkFinite, Set.Infinite]
/-
**Matroid.eRk_ne_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_ne_top_iff : M.eRk X != ⊤ ↔ M.IsRkFinite X
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma eRk_ne_top_iff : M.eRk X ≠ ⊤ ↔ M.IsRkFinite X := by
  simp

@[simp]
/-
**Matroid.eRk_lt_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_lt_top_iff : M.eRk X < ⊤ ↔ M.IsRkFinite X
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用引理 `Matroid.eRk_ne_top_iff`：eRk_ne_top_iff : M.eRk X != ⊤ ↔ M.IsRkFinite X
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma eRk_lt_top_iff : M.eRk X < ⊤ ↔ M.IsRkFinite X := by
  rw [lt_top_iff_ne_top, eRk_ne_top_iff]
/-
**Matroid.IsRkFinite.eRk_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsRkFinite`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X : Set α}, M.IsRkFinite X → M.eRk X < ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Matroid.eRk_lt_top_iff`：eRk_lt_top_iff : M.eRk X < ⊤ ↔ M.IsRkFinite X
-/
lemma IsRkFinite.eRk_lt_top (h : M.IsRkFinite X) : M.eRk X < ⊤ :=
  eRk_lt_top_iff.2 h

/-- If `X` is a finite-rank set, and `I` is a subset of `X` of cardinality
no larger than the rank of `X` that spans `X`, then `I` is a basis for `X`. -/
/-
**Matroid.IsRkFinite.isBasis_of_subset_closure_of_subset_of_encard_le** 是 Mathli
b 中的一个定理，位于命名空间 `Matroid.IsRkFinite`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α},   M.IsRkFinite X → X ⊆ M.c
losure I → I ⊆ X → I.encard ≤ M.eRk X → M.IsBasis I X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBasis`：exists_isBasis (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.closure_inter_ground`：∀ {α : Type u_2} (M : Matroid α) (X : Set 
α), M.closure (X ∩ M.E) = M.closure X
· 使用引理 `Matroid.closure_subset_closure_of_subset_closure`：closure_subset_closure
_of_subset_closure (hXY : X subseteq M.closure Y) : M.closure X subseteq M.closu
re Y
· 使用定理 `Matroid.IsBasis.subset_closure`：∀ {α : Type u_2} {M : Matroid α} {X I : 
Set α}, M.IsBasis I X → X ⊆ M.closure I
· 使用定理 `Matroid.Indep.isBasis_of_subset_of_subset_closure`：∀ {α : Type u_2} {M :
 Matroid α} {X I : Set α}, M.Indep I → I ⊆ X → X ⊆ M.closure I → M.IsBasis I X
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
· 使用定理 `Set.Finite.eq_of_subset_of_encard_le`：∀ {α : Type u_1} {s t : Set α}, s.
Finite → s ⊆ t → t.encard ≤ s.encard → s = t
· 使用定理 `Matroid.IsRkFinite.finite_of_isBasis`：∀ {α : Type u_1} {M : Matroid α} {
X I : Set α}, M.IsRkFinite X → M.IsBasis I X → I.Finite
· 使用定理 `Matroid.IsBasis.encard_eq_eRk`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → I.encard = M.eRk X

--- 原说明 ---
If `X` is a finite-rank set, and `I` is a subset of `X` of cardinality
no larger than the rank of `X` that spans `X`, then `I` is a basis for `X`.
-/
lemma IsRkFinite.isBasis_of_subset_closure_of_subset_of_encard_le (hX : M.IsRkFinite X)
    (hXI : X ⊆ M.closure I) (hIX : I ⊆ X) (hI : I.encard ≤ M.eRk X) : M.IsBasis I X := by
  obtain ⟨J, hJ⟩ := M.exists_isBasis (I ∩ M.E)
  have hIJ := hJ.subset.trans inter_subset_left
  rw [← closure_inter_ground] at hXI
  replace hXI := hXI.trans <| M.closure_subset_closure_of_subset_closure hJ.subset_closure
  have hJX := hJ.indep.isBasis_of_subset_of_subset_closure (hIJ.trans hIX) hXI
  rw [← hJX.encard_eq_eRk] at hI
  rwa [← Finite.eq_of_subset_of_encard_le (hX.finite_of_isBasis hJX) hIJ hI]

/-- If `X` is a finite-rank set, and `Y` is a superset of `X` of rank no larger than that of `X`,
then `X` and `Y` have the same closure. -/
/-
**Matroid.IsRkFinite.closure_eq_closure_of_subset_of_eRk_ge_eRk** 是 Mathlib 中的一个
定理，位于命名空间 `Matroid.IsRkFinite`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X Y : Set α}, M.IsRkFinite X → X ⊆ Y → M
.eRk Y ≤ M.eRk X → M.closure X = M.closure Y
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.closure_inter_ground`：∀ {α : Type u_2} (M : Matroid α) (X : Set 
α), M.closure (X ∩ M.E) = M.closure X
· 使用定理 `Matroid.IsBasis.closure_eq_closure`：∀ {α : Type u_2} {M : Matroid α} {X 
I : Set α}, M.IsBasis I X → M.closure I = M.closure X
· 使用定理 `Matroid.IsBasis'.isBasis_inter_ground`：∀ {α : Type u_1} {M : Matroid α} 
{I X : Set α}, M.IsBasis' I X → M.IsBasis I (X ∩ M.E)
· 使用定理 `Set.Finite.eq_of_subset_of_encard_le`：∀ {α : Type u_1} {s t : Set α}, s.
Finite → s ⊆ t → t.encard ≤ s.encard → s = t
· 使用定理 `Matroid.Indep.finite_of_subset_isRkFinite`：∀ {α : Type u_1} {M : Matroid
 α} {X I : Set α}, M.Indep I → I ⊆ X → M.IsRkFinite X → I.Finite
· 使用定理 `Matroid.IsBasis'.eRk_eq_encard`：∀ {α : Type u_1} {M : Matroid α} {I X : 
Set α}, M.IsBasis' I X → M.eRk X = I.encard

--- 原说明 ---
If `X` is a finite-rank set, and `Y` is a superset of `X` of rank no larger than
 that of `X`,
then `X` and `Y` have the same closure.
-/
lemma IsRkFinite.closure_eq_closure_of_subset_of_eRk_ge_eRk (hX : M.IsRkFinite X) (hXY : X ⊆ Y)
    (hr : M.eRk Y ≤ M.eRk X) : M.closure X = M.closure Y := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_isBasis'_of_subset (hI.subset.trans hXY)
  rw [hI.eRk_eq_encard, hJ.eRk_eq_encard] at hr
  rw [← closure_inter_ground, ← M.closure_inter_ground Y,
    ← hI.isBasis_inter_ground.closure_eq_closure,
    ← hJ.isBasis_inter_ground.closure_eq_closure, Finite.eq_of_subset_of_encard_le
      (hI.indep.finite_of_subset_isRkFinite hI.subset hX) hIJ hr]

/-! ### Insertion -/

/-
**Matroid.eRk_insert_le_add_one** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_insert_le_add_one (M : Matroid α) (e : α) (X : Set α) : M.eRk (insert 
e X) <= M.eRk X + 1
参数：M : Matroid α；e : α；X : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Matroid.eRk_union_le_eRk_add_eRk`：eRk_union_le_eRk_add_eRk (M : Matroid 
α) (X Y : Set α) : M.eRk (X union Y) <= M.eRk X + M.eRk Y
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.encard_singleton`：∀ {α : Type u_1} (e : α), {e}.encard = 1
· 使用引理 `Matroid.eRk_le_encard`：eRk_le_encard (M : Matroid α) (X : Set α) : M.eRk
 X <= X.encard

--- 原说明 ---
### Insertion
-/
lemma eRk_insert_le_add_one (M : Matroid α) (e : α) (X : Set α) :
    M.eRk (insert e X) ≤ M.eRk X + 1 :=
  union_singleton ▸ (M.eRk_union_le_eRk_add_eRk _ _).trans <| by
    gcongr; simpa using M.eRk_le_encard {e}
/-
**Matroid.eRk_insert_eq_add_one** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_insert_eq_add_one (he : e in M.E \ M.closure X) : M.eRk (insert e X) =
 M.eRk X + 1
参数：he : e in M.E \ M.closure X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBasis'`：exists_isBasis' (M : Matroid α) (X : Set α) : e
xists I, M.IsBasis' I X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.eRk_closure_eq`：eRk_closure_eq (M : Matroid α) (X : Set α) : M.e
Rk (M.closure X) = M.eRk X
· 使用引理 `Matroid.closure_insert_congr_right`：closure_insert_congr_right (h : M.cl
osure X = M.closure Y) : M.closure (insert e X) = M.closure (insert e Y)
· 使用定理 `Matroid.IsBasis'.closure_eq_closure`：∀ {α : Type u_2} {M : Matroid α} {X
 I : Set α}, M.IsBasis' I X → M.closure I = M.closure X
· 使用定理 `Matroid.IsBasis'.eRk_eq_encard`：∀ {α : Type u_1} {M : Matroid α} {I X : 
Set α}, M.IsBasis' I X → M.eRk X = I.encard
· 使用定理 `Matroid.Indep.eRk_eq_encard`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → M.eRk I = I.encard
· 使用定理 `not_and`：∀ {a b : Prop}, ¬(a ∧ b) ↔ a → ¬b
· 使用定理 `Matroid.Indep.mem_closure_iff'`：∀ {α : Type u_2} {M : Matroid α} {I : Se
t α} {x : α},   M.Indep I → (x ∈ M.closure I ↔ x ∈ M.E ∧ (M.Indep (insert x I) →
 x ∈ I))
· 使用定理 `Matroid.IsBasis'.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis' I X → M.Indep I
· 使用定理 `Set.mem_sdiff`：mem_sdiff {s t : Set α} (x : α) : x in s \ t ↔ x in s ∧ x
 ∉ t
· 使用定理 `Decidable.not_or_of_imp`：∀ {a b : Prop} [Decidable a], (a → b) → ¬a ∨ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.not_imp_iff_and_not`：∀ {a b : Prop} [Decidable a], ¬(a → b) ↔ 
a ∧ ¬b
· 使用定理 `Set.encard_insert_of_notMem`：encard_insert_of_notMem {a : α} (has : a ∉ 
s) : (insert a s).encard = s.encard + 1
-/
lemma eRk_insert_eq_add_one (he : e ∈ M.E \ M.closure X) : M.eRk (insert e X) = M.eRk X + 1 := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [← hI.closure_eq_closure, mem_sdiff, hI.indep.mem_closure_iff', not_and] at he
  rw [← eRk_closure_eq, ← closure_insert_congr_right hI.closure_eq_closure, hI.eRk_eq_encard,
    eRk_closure_eq, Indep.eRk_eq_encard (by tauto), encard_insert_of_notMem (by tauto)]
/-
**Matroid.exists_eRk_insert_eq_add_one_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`
。
形式化陈述：exists_eRk_insert_eq_add_one_of_lt (h : M.eRk X < M.eRk Y) : exists y in Y
 \ X, M.eRk (insert y X) = M.eRk X + 1
参数：h : M.eRk X < M.eRk Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.eRk_inter_ground`：eRk_inter_ground (M : Matroid α) (X : Set α) :
 M.eRk (X inter M.E) = M.eRk X
· 使用引理 `Matroid.eRk_closure_eq`：eRk_closure_eq (M : Matroid α) (X : Set α) : M.e
Rk (M.closure X) = M.eRk X
· 使用引理 `Matroid.eRk_mono`：eRk_mono (M : Matroid α) : Monotone M.eRk
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.not_subset`：not_subset : ¬s subseteq t ↔ exists a in s, a ∉ t
· 使用引理 `Matroid.mem_closure_of_mem'`：mem_closure_of_mem' (M : Matroid α) (heX : 
e in X) (h : e in M.E
· 使用引理 `Matroid.eRk_insert_eq_add_one`：eRk_insert_eq_add_one (he : e in M.E \ M.
closure X) : M.eRk (insert e X) = M.eRk X + 1
-/
lemma exists_eRk_insert_eq_add_one_of_lt (h : M.eRk X < M.eRk Y) :
    ∃ y ∈ Y \ X, M.eRk (insert y X) = M.eRk X + 1 := by
  have hz : ¬ Y ∩ M.E ⊆ M.closure X := by
    contrapose! h
    simpa using M.eRk_mono h
  obtain ⟨e, ⟨heZ, heE⟩, heX⟩ := not_subset.1 hz
  refine ⟨e, ⟨heZ, fun heX' ↦ heX (mem_closure_of_mem' _ heX')⟩, eRk_insert_eq_add_one ⟨heE, heX⟩⟩
/-
**Matroid.IsRkFinite.closure_eq_closure_of_subset_of_forall_insert** 是 Mathlib 中
的一个定理，位于命名空间 `Matroid.IsRkFinite`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X Y : Set α},   M.IsRkFinite X → X ⊆ Y →
 (∀ e ∈ Y \ X, M.eRk (insert e X) ≤ M.eRk X) → M.closure X = M.closure Y
参数：∀ e ∈ Y \ X, M.eRk (insert e X) ≤ M.eRk X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsRkFinite.closure_eq_closure_of_subset_of_eRk_ge_eRk`：∀ {α : Ty
pe u_1} {M : Matroid α} {X Y : Set α}, M.IsRkFinite X → X ⊆ Y → M.eRk Y ≤ M.eRk 
X → M.closure X = M.closure Y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用引理 `Matroid.exists_eRk_insert_eq_add_one_of_lt`：exists_eRk_insert_eq_add_one
_of_lt (h : M.eRk X < M.eRk Y) : exists y in Y \ X, M.eRk (insert y X) = M.eRk X
 + 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENat.add_one_le_iff`：add_one_le_iff (hm : m != ⊤) : m + 1 <= n ↔ m < n
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Matroid.IsRkFinite.eRk_lt_top`：∀ {α : Type u_1} {M : Matroid α} {X : Set
 α}, M.IsRkFinite X → M.eRk X < ⊤
-/
lemma IsRkFinite.closure_eq_closure_of_subset_of_forall_insert (hX : M.IsRkFinite X) (hXY : X ⊆ Y)
    (hY : ∀ e ∈ Y \ X, M.eRk (Insert.insert e X) ≤ M.eRk X) : M.closure X = M.closure Y := by
  refine hX.closure_eq_closure_of_subset_of_eRk_ge_eRk hXY <| not_lt.1 fun hlt ↦ ?_
  obtain ⟨z, hz, hr⟩ := exists_eRk_insert_eq_add_one_of_lt hlt
  simpa [hr, ENat.add_one_le_iff hX.eRk_lt_top.ne] using hY z hz
/-
**Matroid.eRk_eq_of_eRk_insert_le_forall** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_eq_of_eRk_insert_le_forall (hXY : X subseteq Y) (hY : forall e in Y \ 
X, M.eRk (insert e X) <= M.eRk X) : M.eRk X = M.eRk Y
参数：hXY : X subseteq Y；hY : forall e in Y \ X, M.eRk (insert e X) <= M.eRk X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.eRk_closure_eq`：eRk_closure_eq (M : Matroid α) (X : Set α) : M.e
Rk (M.closure X) = M.eRk X
· 使用定理 `Matroid.IsRkFinite.closure_eq_closure_of_subset_of_forall_insert`：∀ {α :
 Type u_1} {M : Matroid α} {X Y : Set α},   M.IsRkFinite X → X ⊆ Y → (∀ e ∈ Y \ 
X, M.eRk (insert e X) ≤ M.eRk X) → M.closure X = M.clo…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Matroid.eRk_eq_top_iff`：eRk_eq_top_iff : M.eRk X = ⊤ ↔ ¬ M.IsRkFinite X
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Matroid.IsRkFinite.subset`：∀ {α : Type u_1} {M : Matroid α} {X Y : Set α
}, M.IsRkFinite X → Y ⊆ X → M.IsRkFinite Y
-/
lemma eRk_eq_of_eRk_insert_le_forall (hXY : X ⊆ Y)
    (hY : ∀ e ∈ Y \ X, M.eRk (insert e X) ≤ M.eRk X) : M.eRk X = M.eRk Y := by
  by_cases hX : M.IsRkFinite X
  · rw [← eRk_closure_eq, hX.closure_eq_closure_of_subset_of_forall_insert hXY hY, eRk_closure_eq]
  rw [eRk_eq_top_iff.2 hX, eRk_eq_top_iff.2 (mt (fun h ↦ h.subset hXY) hX)]

/-! ### Independence -/

/-
**Matroid.indep_iff_eRk_eq_encard_of_finite** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：indep_iff_eRk_eq_encard_of_finite (hI : I.Finite) : M.Indep I ↔ M.eRk I = 
I.encard
参数：hI : I.Finite。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.Indep.eRk_eq_encard`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → M.eRk I = I.encard
· 使用定理 `Matroid.exists_isBasis'`：exists_isBasis' (M : Matroid α) (X : Set α) : e
xists I, M.IsBasis' I X
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Finite.eq_of_subset_of_encard_le'`：∀ {α : Type u_1} {s t : Set α}, t
.Finite → s ⊆ t → t.encard ≤ s.encard → s = t
· 使用定理 `Matroid.IsBasis'.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α},
 M.IsBasis' I X → I ⊆ X
· 使用定理 `Matroid.IsBasis'.eRk_eq_encard`：∀ {α : Type u_1} {M : Matroid α} {I X : 
Set α}, M.IsBasis' I X → M.eRk X = I.encard
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Matroid.IsBasis'.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis' I X → M.Indep I

--- 原说明 ---
### Independence
-/
lemma indep_iff_eRk_eq_encard_of_finite (hI : I.Finite) : M.Indep I ↔ M.eRk I = I.encard := by
  refine ⟨fun h ↦ by rw [h.eRk_eq_encard], fun h ↦ ?_⟩
  obtain ⟨J, hJ⟩ := M.exists_isBasis' I
  rw [← hI.eq_of_subset_of_encard_le' hJ.subset]
  · exact hJ.indep
  rw [← h, ← hJ.eRk_eq_encard]

/-- In a matroid known to have finite rank, `Matroid.indep_iff_eRk_eq_encard_of_finite`
is true without the finiteness assumption. -/
/-
**Matroid.indep_iff_eRk_eq_encard** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：indep_iff_eRk_eq_encard [M.RankFinite] : M.Indep I ↔ M.eRk I = I.encard
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.eRk_eq_encard`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → M.eRk I = I.encard
· 使用定理 `Set.finite_or_infinite`：∀ {α : Type u} (s : Set α), s.Finite ∨ s.Infinit
e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.indep_iff_eRk_eq_encard_of_finite`：indep_iff_eRk_eq_encard_of_fi
nite (hI : I.Finite) : M.Indep I ↔ M.eRk I = I.encard
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Matroid.IsRkFinite.eRk_lt_top`：∀ {α : Type u_1} {M : Matroid α} {X : Set
 α}, M.IsRkFinite X → M.eRk X < ⊤
· 使用引理 `Matroid.isRkFinite_set`：isRkFinite_set (M : Matroid α) [RankFinite M] (X
 : Set α) : M.IsRkFinite X
· 使用定理 `Set.Infinite.encard_eq`：∀ {α : Type u_1} {s : Set α}, s.Infinite → s.enc
ard = ⊤

--- 原说明 ---
In a matroid known to have finite rank, `Matroid.indep_iff_eRk_eq_encard_of_fini
te`
is true without the finiteness assumption.
-/
lemma indep_iff_eRk_eq_encard [M.RankFinite] : M.Indep I ↔ M.eRk I = I.encard := by
  refine ⟨Indep.eRk_eq_encard, fun h ↦ ?_⟩
  obtain hfin | hinf := I.finite_or_infinite
  · rwa [indep_iff_eRk_eq_encard_of_finite hfin]
  rw [hinf.encard_eq] at h
  exact False.elim <| (M.isRkFinite_set I).eRk_lt_top.ne h
/-
**Matroid.IsRkFinite.indep_of_encard_le_eRk** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.I
sRkFinite`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I : Set α}, M.IsRkFinite I → I.encard ≤ 
M.eRk I → M.Indep I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.indep_iff_eRk_eq_encard_of_finite`：indep_iff_eRk_eq_encard_of_fi
nite (hI : I.Finite) : M.Indep I ↔ M.eRk I = I.encard
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Matroid.IsRkFinite.eRk_lt_top`：∀ {α : Type u_1} {M : Matroid α} {X : Set
 α}, M.IsRkFinite X → M.eRk X < ⊤
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用引理 `Matroid.eRk_le_encard`：eRk_le_encard (M : Matroid α) (X : Set α) : M.eRk
 X <= X.encard
-/
lemma IsRkFinite.indep_of_encard_le_eRk (hX : M.IsRkFinite I) (h : encard I ≤ M.eRk I) :
    M.Indep I := by
  rw [indep_iff_eRk_eq_encard_of_finite _]
  · exact (M.eRk_le_encard I).antisymm h
  simpa using h.trans_lt hX.eRk_lt_top
/-
**Matroid.eRk_lt_encard_of_dep_of_finite** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_lt_encard_of_dep_of_finite (h : X.Finite) (hX : M.Dep X) : M.eRk X < X
.encard
参数：h : X.Finite；hX : M.Dep X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用引理 `Matroid.eRk_le_encard`：eRk_le_encard (M : Matroid α) (X : Set α) : M.eRk
 X <= X.encard
· 使用定理 `Matroid.Indep.not_dep`：∀ {α : Type u_1} {M : Matroid α} {I : Set α}, M.I
ndep I → ¬M.Dep I
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Matroid.indep_iff_eRk_eq_encard_of_finite`：indep_iff_eRk_eq_encard_of_fi
nite (hI : I.Finite) : M.Indep I ↔ M.eRk I = I.encard
-/
lemma eRk_lt_encard_of_dep_of_finite (h : X.Finite) (hX : M.Dep X) : M.eRk X < X.encard :=
  lt_of_le_of_ne (M.eRk_le_encard X) fun h' ↦
    ((indep_iff_eRk_eq_encard_of_finite h).mpr h').not_dep hX
/-
**Matroid.eRk_lt_encard_iff_dep_of_finite** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_lt_encard_iff_dep_of_finite (hX : X.Finite) (hXE : X subseteq M.E
参数：hX : X.Finite。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.not_indep_iff`：∀ {α : Type u_1} {M : Matroid α} {X : Set α}, aut
oParam (X ⊆ M.E) Matroid.not_indep_iff._auto_1 → (¬M.Indep X ↔ M.Dep X)
· 使用引理 `Matroid.indep_iff_eRk_eq_encard_of_finite`：indep_iff_eRk_eq_encard_of_fi
nite (hI : I.Finite) : M.Indep I ↔ M.eRk I = I.encard
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用引理 `Matroid.eRk_lt_encard_of_dep_of_finite`：eRk_lt_encard_of_dep_of_finite (
h : X.Finite) (hX : M.Dep X) : M.eRk X < X.encard
-/
lemma eRk_lt_encard_iff_dep_of_finite (hX : X.Finite) (hXE : X ⊆ M.E := by aesop_mat) :
    M.eRk X < X.encard ↔ M.Dep X := by
  refine ⟨fun h ↦ ?_, fun h ↦ eRk_lt_encard_of_dep_of_finite hX h⟩
  rw [← not_indep_iff, indep_iff_eRk_eq_encard_of_finite hX]
  exact h.ne
/-
**Matroid.Dep.eRk_lt_encard** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Dep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X : Set α} [M.RankFinite], M.Dep X → M.e
Rk X < X.encard
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用引理 `Matroid.eRk_le_encard`：eRk_le_encard (M : Matroid α) (X : Set α) : M.eRk
 X <= X.encard
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.indep_iff_eRk_eq_encard`：indep_iff_eRk_eq_encard [M.RankFinite] 
: M.Indep I ↔ M.eRk I = I.encard
· 使用定理 `Matroid.Dep.not_indep`：∀ {α : Type u_1} {M : Matroid α} {D : Set α}, M.D
ep D → ¬M.Indep D
-/
lemma Dep.eRk_lt_encard [M.RankFinite] (hX : M.Dep X) : M.eRk X < X.encard := by
  refine (M.eRk_le_encard X).lt_of_ne ?_
  rw [ne_eq, ← indep_iff_eRk_eq_encard]
  exact hX.not_indep
/-
**Matroid.eRk_lt_encard_iff_dep** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_lt_encard_iff_dep [M.RankFinite] (hXE : X subseteq M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matroid.not_indep_iff`：∀ {α : Type u_1} {M : Matroid α} {X : Set α}, aut
oParam (X ⊆ M.E) Matroid.not_indep_iff._auto_1 → (¬M.Indep X ↔ M.Dep X)
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Matroid.Indep.eRk_eq_encard`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → M.eRk I = I.encard
· 使用定理 `Matroid.Dep.eRk_lt_encard`：∀ {α : Type u_1} {M : Matroid α} {X : Set α} 
[M.RankFinite], M.Dep X → M.eRk X < X.encard
-/
lemma eRk_lt_encard_iff_dep [M.RankFinite] (hXE : X ⊆ M.E := by aesop_mat) :
    M.eRk X < X.encard ↔ M.Dep X :=
  ⟨fun h ↦ (not_indep_iff).1 fun hi ↦ h.ne hi.eRk_eq_encard, Dep.eRk_lt_encard⟩
/-
**Matroid.Indep.exists_insert_of_encard_lt** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.In
dep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I J : Set α},   M.Indep I → M.Indep J → 
I.encard < J.encard → ∃ e ∈ J \ I, M.Indep (insert e I)
参数：insert e I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.augment`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α},  
 M.Indep I → M.Indep J → I.encard < J.encard → ∃ e ∈ J \ I, M.Indep (insert e I)
-/
lemma Indep.exists_insert_of_encard_lt {I J : Set α} (hI : M.Indep I) (hJ : M.Indep J)
    (hcard : I.encard < J.encard) : ∃ e ∈ J \ I, M.Indep (insert e I) :=
  augment hI hJ hcard
/-
**Matroid.isBasis'_iff_indep_encard_eq_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Matr
oid`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, I.Finite → (M.IsBasis' I X
 ↔ I ⊆ X ∧ M.Indep I ∧ I.encard = M.eRk X)
参数：M.IsBasis' I X ↔ I ⊆ X ∧ M.Indep I ∧ I.encard = M.eRk X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis'.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α},
 M.IsBasis' I X → I ⊆ X
· 使用定理 `Matroid.IsBasis'.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis' I X → M.Indep I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsBasis'.eRk_eq_encard`：∀ {α : Type u_1} {M : Matroid α} {I X : 
Set α}, M.IsBasis' I X → M.eRk X = I.encard
· 使用定理 `Matroid.Indep.subset_isBasis'_of_subset`：∀ {α : Type u_1} {M : Matroid α
} {I X : Set α}, M.Indep I → I ⊆ X → ∃ J, M.IsBasis' J X ∧ I ⊆ J
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.eq_of_subset_of_encard_le`：∀ {α : Type u_1} {s t : Set α}, s.
Finite → s ⊆ t → t.encard ≤ s.encard → s = t
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matroid.IsBasis'.encard_eq_eRk`：∀ {α : Type u_1} {M : Matroid α} {I X : 
Set α}, M.IsBasis' I X → I.encard = M.eRk X
-/
lemma isBasis'_iff_indep_encard_eq_of_finite (hIfin : I.Finite) :
    M.IsBasis' I X ↔ I ⊆ X ∧ M.Indep I ∧ I.encard = M.eRk X := by
  refine ⟨fun h ↦ ⟨h.subset,h.indep, h.eRk_eq_encard.symm⟩, fun ⟨hIX, hI, hcard⟩ ↦ ?_⟩
  obtain ⟨J, hJ, hIJ⟩ := hI.subset_isBasis'_of_subset hIX
  rwa [hIfin.eq_of_subset_of_encard_le hIJ (hJ.encard_eq_eRk.trans hcard.symm).le]
/-
**Matroid.isBasis_iff_indep_encard_eq_of_finite** 是 Mathlib 中的一个引理，位于命名空间 `Matro
id`。
形式化陈述：isBasis_iff_indep_encard_eq_of_finite (hIfin : I.Finite) (hX : X subseteq 
M.E
参数：hIfin : I.Finite。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.isBasis'_iff_isBasis`：∀ {α : Type u_1} {M : Matroid α} {I X : Se
t α},   autoParam (X ⊆ M.E) Matroid.isBasis'_iff_isBasis._auto_1 → (M.IsBasis' I
 X ↔ M.IsBasis I X…
· 使用定理 `Matroid.isBasis'_iff_indep_encard_eq_of_finite`：∀ {α : Type u_1} {M : Ma
troid α} {I X : Set α}, I.Finite → (M.IsBasis' I X ↔ I ⊆ X ∧ M.Indep I ∧ I.encar
d = M.eRk X)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isBasis_iff_indep_encard_eq_of_finite (hIfin : I.Finite) (hX : X ⊆ M.E := by aesop_mat) :
    M.IsBasis I X ↔ I ⊆ X ∧ M.Indep I ∧ I.encard = M.eRk X := by
  rw [← isBasis'_iff_isBasis, isBasis'_iff_indep_encard_eq_of_finite hIfin]

/-- If `I` is a finite independent subset of `X` for which `M.eRk X ≤ M.eRk I`,
then `I` is a `Basis'` for `X`. -/
/-
**Matroid.Indep.isBasis'_of_eRk_ge** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M.Indep I → I.Finite → I ⊆
 X → M.eRk X ≤ M.eRk I → M.IsBasis' I X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matroid.isBasis'_iff_indep_encard_eq_of_finite`：∀ {α : Type u_1} {M : Ma
troid α} {I X : Set α}, I.Finite → (M.IsBasis' I X ↔ I ⊆ X ∧ M.Indep I ∧ I.encar
d = M.eRk X)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用引理 `Matroid.eRk_mono`：eRk_mono (M : Matroid α) : Monotone M.eRk
· 使用定理 `Matroid.Indep.eRk_eq_encard`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → M.eRk I = I.encard

--- 原说明 ---
If `I` is a finite independent subset of `X` for which `M.eRk X ≤ M.eRk I`,
then `I` is a `Basis'` for `X`.
-/
lemma Indep.isBasis'_of_eRk_ge (hI : M.Indep I) (hIfin : I.Finite) (hIX : I ⊆ X)
    (h : M.eRk X ≤ M.eRk I) : M.IsBasis' I X :=
  (isBasis'_iff_indep_encard_eq_of_finite hIfin).2
    ⟨hIX, hI, by rw [h.antisymm (M.eRk_mono hIX), hI.eRk_eq_encard]⟩
/-
**Matroid.Indep.isBasis_of_eRk_ge** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α},   M.Indep I →     I.Finite
 → I ⊆ X → M.eRk X ≤ M.eRk I → autoParam (X ⊆ M.E) Matroid.Indep.isBasis_of_eRk_
ge._auto_1 → M.IsBasis I X
参数：X ⊆ M.E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis'.isBasis`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}
,   M.IsBasis' I X → autoParam (X ⊆ M.E) Matroid.IsBasis'.isBasis._auto_1 → M.Is
Basis I X
· 使用定理 `Matroid.Indep.isBasis'_of_eRk_ge`：∀ {α : Type u_1} {M : Matroid α} {I X 
: Set α}, M.Indep I → I.Finite → I ⊆ X → M.eRk X ≤ M.eRk I → M.IsBasis' I X
-/
lemma Indep.isBasis_of_eRk_ge (hI : M.Indep I) (hIfin : I.Finite) (hIX : I ⊆ X)
    (h : M.eRk X ≤ M.eRk I) (hX : X ⊆ M.E := by aesop_mat) : M.IsBasis I X :=
  (hI.isBasis'_of_eRk_ge hIfin hIX h).isBasis
/-
**Matroid.Indep.isBase_of_eRk_ge** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I : Set α}, M.Indep I → I.Finite → M.eRa
nk ≤ M.eRk I → M.IsBase I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.isBasis_of_eRk_ge`：∀ {α : Type u_1} {M : Matroid α} {I X :
 Set α},   M.Indep I →     I.Finite → I ⊆ X → M.eRk X ≤ M.eRk I → autoParam (X ⊆
 M.E) Matroid.Indep.i…
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用引理 `Matroid.eRk_ground`：eRk_ground (M : Matroid α) : M.eRk M.E = M.eRank
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma Indep.isBase_of_eRk_ge (hI : M.Indep I) (hIfin : I.Finite) (h : M.eRank ≤ M.eRk I) :
    M.IsBase I := by
  simpa using hI.isBasis_of_eRk_ge hIfin hI.subset_ground (M.eRk_ground.trans_le h)
/-
**Matroid.IsCircuit.eRk_add_one_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsCircuit`
。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {C : Set α}, M.IsCircuit C → M.eRk C + 1 
= C.encard
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBasis`：exists_isBasis (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
· 使用定理 `Matroid.IsCircuit.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {C : S
et α}, M.IsCircuit C → C ⊆ M.E
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matroid.IsCircuit.isBasis_iff_insert_eq`：∀ {α : Type u_1} {M : Matroid α
} {C I : Set α}, M.IsCircuit C → (M.IsBasis I C ↔ ∃ e ∈ C \ I, C = insert e I)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsBasis.eRk_eq_encard`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → M.eRk X = I.encard
· 使用定理 `Set.encard_insert_of_notMem`：encard_insert_of_notMem {a : α} (has : a ∉ 
s) : (insert a s).encard = s.encard + 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma IsCircuit.eRk_add_one_eq {C : Set α} (hC : M.IsCircuit C) : M.eRk C + 1 = C.encard := by
  obtain ⟨I, hI⟩ := M.exists_isBasis C
  obtain ⟨e, ⟨heC, heI⟩, rfl⟩ := hC.isBasis_iff_insert_eq.1 hI
  rw [hI.eRk_eq_encard, encard_insert_of_notMem heI]

/-! ### Singletons -/

/-
**Matroid.IsLoop.eRk_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsLoop`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e : α}, M.IsLoop e → M.eRk {e} = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.eRk_closure_eq`：eRk_closure_eq (M : Matroid α) (X : Set α) : M.e
Rk (M.closure X) = M.eRk X
· 使用定理 `Matroid.IsLoop.closure`：∀ {α : Type u_1} {M : Matroid α} {e : α}, M.IsLo
op e → M.closure {e} = M.loops
· 使用定理 `Matroid.loops.eq_1`：∀ {α : Type u_1} (M : Matroid α), M.loops = M.closur
e ∅
· 使用引理 `Matroid.eRk_empty`：eRk_empty (M : Matroid α) : M.eRk ∅ = 0

--- 原说明 ---
### Singletons
-/
lemma IsLoop.eRk_eq (he : M.IsLoop e) : M.eRk {e} = 0 := by
  rw [← eRk_closure_eq, he.closure, loops, eRk_closure_eq, eRk_empty]
/-
**Matroid.IsNonloop.eRk_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsNonloop`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e : α}, M.IsNonloop e → M.eRk {e} = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsBasis.encard_eq_eRk`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → I.encard = M.eRk X
· 使用定理 `Matroid.Indep.isBasis_self`：∀ {α : Type u_1} {M : Matroid α} {I : Set α}
, M.Indep I → M.IsBasis I I
· 使用定理 `Matroid.IsNonloop.indep`：∀ {α : Type u_1} {M : Matroid α} {e : α}, M.IsN
onloop e → M.Indep {e}
· 使用定理 `Set.encard_singleton`：∀ {α : Type u_1} (e : α), {e}.encard = 1
-/
lemma IsNonloop.eRk_eq (he : M.IsNonloop e) : M.eRk {e} = 1 := by
  rw [← he.indep.isBasis_self.encard_eq_eRk, encard_singleton]
/-
**Matroid.eRk_singleton_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_singleton_eq [Loopless M] (he : e in M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsNonloop.eRk_eq`：∀ {α : Type u_1} {M : Matroid α} {e : α}, M.Is
Nonloop e → M.eRk {e} = 1
· 使用引理 `Matroid.isNonloop_of_loopless`：isNonloop_of_loopless [Loopless M] (he : 
e in M.E
-/
lemma eRk_singleton_eq [Loopless M] (he : e ∈ M.E := by aesop_mat) :
    M.eRk {e} = 1 :=
  (M.isNonloop_of_loopless he).eRk_eq

@[simp]
/-
**Matroid.eRk_singleton_le** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_singleton_le (M : Matroid α) (e : α) : M.eRk {e} <= 1
参数：M : Matroid α；e : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用引理 `Matroid.eRk_le_encard`：eRk_le_encard (M : Matroid α) (X : Set α) : M.eRk
 X <= X.encard
· 使用定理 `Set.encard_singleton`：∀ {α : Type u_1} (e : α), {e}.encard = 1
-/
lemma eRk_singleton_le (M : Matroid α) (e : α) : M.eRk {e} ≤ 1 :=
  (M.eRk_le_encard {e}).trans_eq <| encard_singleton e

@[simp]
/-
**Matroid.eRk_singleton_eq_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_singleton_eq_one_iff {e : α} : M.eRk {e} = 1 ↔ M.IsNonloop e
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.indep_singleton`：indep_singleton : M.Indep {e} ↔ M.IsNonloop e
· 使用引理 `Matroid.indep_iff_eRk_eq_encard_of_finite`：indep_iff_eRk_eq_encard_of_fi
nite (hI : I.Finite) : M.Indep I ↔ M.eRk I = I.encard
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.encard_singleton`：∀ {α : Type u_1} (e : α), {e}.encard = 1
· 使用定理 `Matroid.IsNonloop.eRk_eq`：∀ {α : Type u_1} {M : Matroid α} {e : α}, M.Is
Nonloop e → M.eRk {e} = 1
-/
lemma eRk_singleton_eq_one_iff {e : α} : M.eRk {e} = 1 ↔ M.IsNonloop e := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.eRk_eq⟩
  rwa [← indep_singleton, indep_iff_eRk_eq_encard_of_finite (by simp), encard_singleton]
/-
**Matroid.eRk_eq_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_eq_one_iff (hX : X subseteq M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBasis`：exists_isBasis (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsBasis.eRk_eq_encard`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → M.eRk X = I.encard
· 使用定理 `Set.encard_eq_one`：encard_eq_one : s.encard = 1 ↔ exists x, s = {x}
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X
· 使用引理 `Matroid.indep_singleton`：indep_singleton : M.Indep {e} ↔ M.IsNonloop e
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
· 使用定理 `Matroid.IsBasis.subset_closure`：∀ {α : Type u_2} {M : Matroid α} {X I : 
Set α}, M.IsBasis I X → X ⊆ M.closure I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsNonloop.eRk_eq`：∀ {α : Type u_1} {M : Matroid α} {e : α}, M.Is
Nonloop e → M.eRk {e} = 1
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Matroid.eRk_mono`：eRk_mono (M : Matroid α) : Monotone M.eRk
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `Matroid.eRk_closure_eq`：eRk_closure_eq (M : Matroid α) (X : Set α) : M.e
Rk (M.closure X) = M.eRk X
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
lemma eRk_eq_one_iff (hX : X ⊆ M.E := by aesop_mat) :
    M.eRk X = 1 ↔ ∃ e ∈ X, M.IsNonloop e ∧ X ⊆ M.closure {e} := by
  refine ⟨?_, fun ⟨e, heX, he, hXe⟩ ↦ ?_⟩
  · obtain ⟨I, hI⟩ := M.exists_isBasis X
    rw [hI.eRk_eq_encard, encard_eq_one]
    rintro ⟨e, rfl⟩
    exact ⟨e, singleton_subset_iff.1 hI.subset, indep_singleton.1 hI.indep, hI.subset_closure⟩
  rw [← he.eRk_eq]
  exact ((M.eRk_mono hXe).trans (M.eRk_closure_eq _).le).antisymm
    (M.eRk_mono (singleton_subset_iff.2 heX))
/-
**Matroid.eRk_le_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_le_one_iff [M.Nonempty] (hX : X subseteq M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBasis`：exists_isBasis (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.encard_le_one_iff_eq`：encard_le_one_iff_eq : s.encard <= 1 ↔ s = ∅ ∨
 exists x, s = {x}
· 使用定理 `Matroid.IsBasis.eRk_eq_encard`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → M.eRk X = I.encard
· 使用定理 `Matroid.ground_nonempty`：ground_nonempty (M : Matroid α) [M.Nonempty] : 
M.E.Nonempty
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Matroid.IsBasis.subset_closure`：∀ {α : Type u_2} {M : Matroid α} {X I : 
Set α}, M.IsBasis I X → X ⊆ M.closure I
· 使用引理 `Matroid.closure_subset_closure`：closure_subset_closure (M : Matroid α) (
h : X subseteq Y) : M.closure X subseteq M.closure Y
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
· 使用引理 `Matroid.eRk_mono`：eRk_mono (M : Matroid α) : Monotone M.eRk
· 使用引理 `Matroid.eRk_closure_eq`：eRk_closure_eq (M : Matroid α) (X : Set α) : M.e
Rk (M.closure X) = M.eRk X
· 使用定理 `Set.encard_singleton`：∀ {α : Type u_1} (e : α), {e}.encard = 1
· 使用引理 `Matroid.eRk_le_encard`：eRk_le_encard (M : Matroid α) (X : Set α) : M.eRk
 X <= X.encard
-/
lemma eRk_le_one_iff [M.Nonempty] (hX : X ⊆ M.E := by aesop_mat) :
    M.eRk X ≤ 1 ↔ ∃ e ∈ M.E, X ⊆ M.closure {e} := by
  refine ⟨fun h ↦ ?_, fun ⟨e, _, he⟩ ↦ ?_⟩
  · obtain ⟨I, hI⟩ := M.exists_isBasis X
    rw [hI.eRk_eq_encard, encard_le_one_iff_eq] at h
    obtain (rfl | ⟨e, rfl⟩) := h
    · obtain ⟨e, he⟩ := M.ground_nonempty
      exact ⟨e, he, hI.subset_closure.trans ((M.closure_subset_closure (empty_subset _)))⟩
    exact ⟨e, hI.indep.subset_ground rfl,  hI.subset_closure⟩
  refine (M.eRk_mono he).trans ?_
  rw [eRk_closure_eq, ← encard_singleton e]
  exact M.eRk_le_encard {e}

/-! ### Spanning Sets -/

/-
**Matroid.Spanning.eRk_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Spanning`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X : Set α}, M.Spanning X → M.eRk X = M.e
Rank
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBasis`：exists_isBasis (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
· 使用定理 `Matroid.Spanning.subset_ground`：∀ {α : Type u_2} {M : Matroid α} {S : Se
t α}, M.Spanning S → S ⊆ M.E
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用引理 `Matroid.eRk_le_eRank`：eRk_le_eRank (M : Matroid α) (X : Set α) : M.eRk X
 <= M.eRank
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsBasis.encard_eq_eRk`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → I.encard = M.eRk X
· 使用定理 `Matroid.IsBase.encard_eq_eRank`：∀ {α : Type u_1} {M : Matroid α} {B : Se
t α}, M.IsBase B → B.encard = M.eRank
· 使用定理 `Matroid.IsBasis.isBase_of_spanning`：∀ {α : Type u_2} {M : Matroid α} {X 
I : Set α}, M.IsBasis I X → M.Spanning X → M.IsBase I
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
### Spanning Sets
-/
lemma Spanning.eRk_eq (hX : M.Spanning X) : M.eRk X = M.eRank := by
  obtain ⟨B, hB⟩ := M.exists_isBasis X
  exact (M.eRk_le_eRank X).antisymm <| by
    rw [← hB.encard_eq_eRk, ← (hB.isBase_of_spanning hX).encard_eq_eRank]
/-
**Matroid.spanning_iff_eRk_le'** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：spanning_iff_eRk_le' [RankFinite M] : M.Spanning X ↔ M.eRank <= M.eRk X ∧ 
X subseteq M.E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.Spanning.eRk_eq`：∀ {α : Type u_1} {M : Matroid α} {X : Set α}, M
.Spanning X → M.eRk X = M.eRank
· 使用定理 `Matroid.Spanning.subset_ground`：∀ {α : Type u_2} {M : Matroid α} {S : Se
t α}, M.Spanning S → S ⊆ M.E
· 使用定理 `Matroid.exists_isBasis`：exists_isBasis (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
· 使用定理 `Matroid.IsBase.spanning_of_superset`：∀ {α : Type u_2} {M : Matroid α} {X
 B : Set α},   M.IsBase B → B ⊆ X → autoParam (X ⊆ M.E) Matroid.IsBase.spanning_
of_superset._auto_1 → M.S…
· 使用定理 `Matroid.Indep.isBase_of_eRk_ge`：∀ {α : Type u_1} {M : Matroid α} {I : Se
t α}, M.Indep I → I.Finite → M.eRank ≤ M.eRk I → M.IsBase I
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
· 使用定理 `Matroid.Indep.finite`：∀ {α : Type u_1} {M : Matroid α} {I : Set α} [M.Ra
nkFinite], M.Indep I → I.Finite
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Matroid.IsBasis.eRk_eq_eRk`：∀ {α : Type u_1} {M : Matroid α} {I X : Set 
α}, M.IsBasis I X → M.eRk I = M.eRk X
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X
-/
lemma spanning_iff_eRk_le' [RankFinite M] : M.Spanning X ↔ M.eRank ≤ M.eRk X ∧ X ⊆ M.E := by
  refine ⟨fun h ↦ ⟨h.eRk_eq.symm.le, h.subset_ground⟩, fun ⟨h, hX⟩ ↦ ?_⟩
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  exact (hI.indep.isBase_of_eRk_ge
    hI.indep.finite (h.trans hI.eRk_eq_eRk.symm.le)).spanning_of_superset hI.subset
/-
**Matroid.spanning_iff_eRk_le** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：spanning_iff_eRk_le [RankFinite M] (hX : X subseteq M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.spanning_iff_eRk_le'`：spanning_iff_eRk_le' [RankFinite M] : M.Sp
anning X ↔ M.eRank <= M.eRk X ∧ X subseteq M.E
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma spanning_iff_eRk_le [RankFinite M] (hX : X ⊆ M.E := by aesop_mat) :
    M.Spanning X ↔ M.eRank ≤ M.eRk X := by
  rw [spanning_iff_eRk_le', and_iff_left hX]
/-
**Matroid.Spanning.eRank_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Spanning`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X : Set α}, M.Spanning X → (M.restrict X
).eRank = M.eRank
参数：M.restrict X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.eRank_def`：eRank_def (M : Matroid α) : M.eRank = M.eRk M.E
· 使用定理 `Matroid.restrict_ground_eq`：∀ {α : Type u_1} {M : Matroid α} {R : Set α}
, (M.restrict R).E = R
· 使用引理 `Matroid.restrict_eRk_eq`：restrict_eRk_eq (M : Matroid α) {R : Set α} (h 
: X subseteq R) : (M ↾ R).eRk X = M.eRk X
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Matroid.Spanning.eRk_eq`：∀ {α : Type u_1} {M : Matroid α} {X : Set α}, M
.Spanning X → M.eRk X = M.eRank
-/
lemma Spanning.eRank_restrict (hX : M.Spanning X) : (M ↾ X).eRank = M.eRank := by
  rw [eRank_def, restrict_ground_eq, restrict_eRk_eq _ rfl.subset, hX.eRk_eq]

/-! ### Constructions -/

@[simp]
/-
**Matroid.eRank_map** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRank_map {β : Type*} {f : α -> β} (M : Matroid α) (hf : InjOn f M.E) : (M
.map f hf).eRank = M.eRank
参数：M : Matroid α；hf : InjOn f M.E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBase`：∀ {α : Type u_1} (self : Matroid α), ∃ B, self.Is
Base B
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsBase.encard_eq_eRank`：∀ {α : Type u_1} {M : Matroid α} {B : Se
t α}, M.IsBase B → B.encard = M.eRank
· 使用定理 `Matroid.IsBase.map`：∀ {α : Type u_1} {β : Type u_2} {M : Matroid α} {B :
 Set α},   M.IsBase B → ∀ {f : α → β} (hf : Set.InjOn f M.E), (M.map f hf).IsBas
e (f '' …
· 使用定理 `Set.InjOn.encard_image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f :
 α → β}, Set.InjOn f s → (f '' s).encard = s.encard
· 使用定理 `Set.InjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α →
 β}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁
· 使用定理 `Matroid.IsBase.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {B : Set 
α}, M.IsBase B → B ⊆ M.E

--- 原说明 ---
### Constructions
-/
lemma eRank_map {β : Type*} {f : α → β} (M : Matroid α) (hf : InjOn f M.E) :
    (M.map f hf).eRank = M.eRank := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [← (hB.map hf).encard_eq_eRank, ← hB.encard_eq_eRank, (hf.mono hB.subset_ground).encard_image]

@[simp]
/-
**Matroid.eRk_map** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_map {β : Type*} {f : α -> β} (M : Matroid α) (hf : InjOn f M.E) (hX : 
X subseteq M.E
参数：M : Matroid α；hf : InjOn f M.E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBasis`：exists_isBasis (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsBasis.eRk_eq_encard`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → M.eRk X = I.encard
· 使用定理 `Matroid.IsBasis.map`：∀ {α : Type u_1} {β : Type u_2} {I : Set α} {M : Ma
troid α} {X : Set α},   M.IsBasis I X → ∀ {f : α → β} (hf : Set.InjOn f M.E), (M
.map f hf…
· 使用定理 `Set.InjOn.encard_image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f :
 α → β}, Set.InjOn f s → (f '' s).encard = s.encard
· 使用定理 `Set.InjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α →
 β}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
-/
lemma eRk_map {β : Type*} {f : α → β} (M : Matroid α) (hf : InjOn f M.E)
    (hX : X ⊆ M.E := by aesop_mat) : (M.map f hf).eRk (f '' X) = M.eRk X := by
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  rw [hI.eRk_eq_encard, (hI.map hf).eRk_eq_encard, (hf.mono hI.indep.subset_ground).encard_image]

@[simp]
/-
**Matroid.eRk_comap** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_comap {β : Type*} {f : α -> β} (M : Matroid β) (X : Set α) : (M.comap 
f).eRk X = M.eRk (f '' X)
参数：M : Matroid β；X : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBasis'`：exists_isBasis' (M : Matroid α) (X : Set α) : e
xists I, M.IsBasis' I X
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matroid.comap_isBasis'_iff`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} 
{N : Matroid β} {I X : Set α},   (N.comap f).IsBasis' I X ↔ N.IsBasis' (f '' I) 
(f '' X) ∧ Set.I…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsBasis'.encard_eq_eRk`：∀ {α : Type u_1} {M : Matroid α} {I X : 
Set α}, M.IsBasis' I X → I.encard = M.eRk X
· 使用定理 `Set.InjOn.encard_image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f :
 α → β}, Set.InjOn f s → (f '' s).encard = s.encard
-/
lemma eRk_comap {β : Type*} {f : α → β} (M : Matroid β) (X : Set α) :
    (M.comap f).eRk X = M.eRk (f '' X) := by
  obtain ⟨I, hI⟩ := (M.comap f).exists_isBasis' X
  obtain ⟨hI', hinj, -⟩ := comap_isBasis'_iff.1 hI
  rw [← hI.encard_eq_eRk, ← hI'.encard_eq_eRk, hinj.encard_image]

@[simp]
/-
**Matroid.eRk_loopyOn** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_loopyOn (X Y : Set α) : (loopyOn Y).eRk X = 0
参数：X Y : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBasis'`：exists_isBasis' (M : Matroid α) (X : Set α) : e
xists I, M.IsBasis' I X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsBasis'.eRk_eq_encard`：∀ {α : Type u_1} {M : Matroid α} {I X : 
Set α}, M.IsBasis' I X → M.eRk X = I.encard
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matroid.loopyOn_indep_iff`：∀ {α : Type u_1} {E I : Set α}, (Matroid.loop
yOn E).Indep I ↔ I = ∅
· 使用定理 `Matroid.IsBasis'.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis' I X → M.Indep I
· 使用定理 `Set.encard_empty`：∀ {α : Type u_1}, ∅.encard = 0
-/
lemma eRk_loopyOn (X Y : Set α) : (loopyOn Y).eRk X = 0 := by
  obtain ⟨I, hI⟩ := (loopyOn Y).exists_isBasis' X
  rw [hI.eRk_eq_encard, loopyOn_indep_iff.1 hI.indep, encard_empty]

@[simp]
/-
**Matroid.eRank_loopyOn** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRank_loopyOn (X : Set α) : (loopyOn X).eRank = 0
参数：X : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.eRank_def`：eRank_def (M : Matroid α) : M.eRank = M.eRk M.E
· 使用引理 `Matroid.eRk_loopyOn`：eRk_loopyOn (X Y : Set α) : (loopyOn Y).eRk X = 0
-/
lemma eRank_loopyOn (X : Set α) : (loopyOn X).eRank = 0 := by
  rw [eRank_def, eRk_loopyOn]
/-
**Matroid.eRank_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRank_eq_zero_iff : M.eRank = 0 ↔ M = loopyOn M.E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Matroid.closure_empty_eq_ground_iff`：closure_empty_eq_ground_iff : M.clo
sure ∅ = M.E ↔ M = loopyOn M.E
· 使用定理 `Matroid.exists_isBase`：∀ {α : Type u_1} (self : Matroid α), ∃ B, self.Is
Base B
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.encard_eq_zero`：∀ {α : Type u_1} {s : Set α}, s.encard = 0 ↔ s = ∅
· 使用定理 `Matroid.IsBase.encard_eq_eRank`：∀ {α : Type u_1} {M : Matroid α} {B : Se
t α}, M.IsBase B → B.encard = M.eRank
· 使用定理 `Matroid.IsBase.closure_eq`：∀ {α : Type u_2} {M : Matroid α} {B : Set α},
 M.IsBase B → M.closure B = M.E
· 使用引理 `Matroid.eRank_loopyOn`：eRank_loopyOn (X : Set α) : (loopyOn X).eRank = 0
-/
lemma eRank_eq_zero_iff : M.eRank = 0 ↔ M = loopyOn M.E := by
  refine ⟨fun h ↦ closure_empty_eq_ground_iff.1 ?_, fun h ↦ by rw [h, eRank_loopyOn]⟩
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [← hB.encard_eq_eRank, encard_eq_zero] at h
  rw [← h, hB.closure_eq]
/-
**Matroid.exists_of_eRank_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：exists_of_eRank_eq_zero (h : M.eRank = 0) : exists X, M = loopyOn X
参数：h : M.eRank = 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exists_of_eRank_eq_zero (h : M.eRank = 0) : ∃ X, M = loopyOn X :=
  ⟨M.E, by simpa [eRank_eq_zero_iff] using h⟩

@[simp]
/-
**Matroid.eRank_emptyOn** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRank_emptyOn (α : Type*) : (emptyOn α).eRank = 0
参数：α : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.eRank_eq_zero_iff`：eRank_eq_zero_iff : M.eRank = 0 ↔ M = loopyOn
 M.E
· 使用定理 `Matroid.emptyOn_ground`：∀ {α : Type u_1}, (Matroid.emptyOn α).E = ∅
· 使用定理 `Matroid.loopyOn_empty`：∀ (α : Type u_2), Matroid.loopyOn ∅ = Matroid.emp
tyOn α
-/
lemma eRank_emptyOn (α : Type*) : (emptyOn α).eRank = 0 := by
  rw [eRank_eq_zero_iff, emptyOn_ground, loopyOn_empty]
/-
**Matroid.eq_loopyOn_iff_eRank** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eq_loopyOn_iff_eRank : M = loopyOn X ↔ M.eRank = 0 ∧ M.E = X
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Matroid.eRank_loopyOn`：eRank_loopyOn (X : Set α) : (loopyOn X).eRank = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.eRank_eq_zero_iff`：eRank_eq_zero_iff : M.eRank = 0 ↔ M = loopyOn
 M.E
-/
lemma eq_loopyOn_iff_eRank : M = loopyOn X ↔ M.eRank = 0 ∧ M.E = X :=
  ⟨fun h ↦ by rw [h]; simp, fun ⟨h,h'⟩ ↦ by rw [← h', ← eRank_eq_zero_iff, h]⟩

@[simp]
/-
**Matroid.eRank_freeOn** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRank_freeOn (X : Set α) : (freeOn X).eRank = X.encard
参数：X : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.eRank_def`：eRank_def (M : Matroid α) : M.eRank = M.eRk M.E
· 使用定理 `Matroid.freeOn_ground`：∀ {α : Type u_1} {E : Set α}, (Matroid.freeOn E).
E = E
· 使用定理 `Matroid.Indep.eRk_eq_encard`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → M.eRk I = I.encard
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matroid.freeOn_indep_iff`：∀ {α : Type u_1} {E I : Set α}, (Matroid.freeO
n E).Indep I ↔ I ⊆ E
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
-/
lemma eRank_freeOn (X : Set α) : (freeOn X).eRank = X.encard := by
  rw [eRank_def, freeOn_ground, (freeOn_indep_iff.2 rfl.subset).eRk_eq_encard]
/-
**Matroid.eRk_freeOn** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_freeOn (hXY : X subseteq Y) : (freeOn Y).eRk X = X.encard
参数：hXY : X subseteq Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBasis`：exists_isBasis (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsBasis.eRk_eq_encard`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → M.eRk X = I.encard
· 使用定理 `Matroid.Indep.eq_of_isBasis`：∀ {α : Type u_1} {M : Matroid α} {I J : Set
 α}, M.Indep I → M.IsBasis J I → J = I
· 使用定理 `Matroid.freeOn_indep`：freeOn_indep (hIE : I subseteq E) : (freeOn E).Ind
ep I
-/
lemma eRk_freeOn (hXY : X ⊆ Y) : (freeOn Y).eRk X = X.encard := by
  obtain ⟨I, hI⟩ := (freeOn Y).exists_isBasis X
  rw [hI.eRk_eq_encard, (freeOn_indep hXY).eq_of_isBasis hI]

/-! ### Duality -/

/-
**Matroid.IsBase.encard_compl_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B : Set α}, M.IsBase B → (M.E \ B).encar
d = M✶.eRank
参数：M.E \ B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBase.encard_eq_eRank`：∀ {α : Type u_1} {M : Matroid α} {B : Se
t α}, M.IsBase B → B.encard = M.eRank
· 使用定理 `Matroid.IsBase.compl_isBase_dual`：∀ {α : Type u_1} {M : Matroid α} {B : 
Set α}, M.IsBase B → M✶.IsBase (M.E \ B)

--- 原说明 ---
### Duality
-/
lemma IsBase.encard_compl_eq (hB : M.IsBase B) : (M.E \ B).encard = M✶.eRank :=
  (hB.compl_isBase_dual).encard_eq_eRank

/-- A subtraction-free formula for the rank of a set in the dual matroid. -/
/-
**Matroid.eRk_dual_add_eRank** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_dual_add_eRank (M : Matroid α) (X : Set α) (hX : X subseteq M.E
参数：M : Matroid α；X : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBasis`：exists_isBasis (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
· 使用定理 `Matroid.IsBasis.exists_isBasis_inter_eq_of_superset`：∀ {α : Type u_1} {M
 : Matroid α} {I X Y : Set α},   M.IsBasis I X →     X ⊆ Y →       autoParam (Y 
⊆ M.E) Matroid.IsBasis.exists_isBasis_int…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matroid.isBasis_ground_iff`：∀ {α : Type u_1} {M : Matroid α} {B : Set α}
, M.IsBasis B M.E ↔ M.IsBase B
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.dual_dual`：∀ {α : Type u_1} (M : Matroid α), M✶✶ = M
· 使用定理 `Matroid.IsBase.inter_isBasis_iff_compl_inter_isBasis_dual`：∀ {α : Type u
_1} {M : Matroid α} {B X : Set α},   M.IsBase B →     autoParam (X ⊆ M.E) Matroi
d.IsBase.inter_isBasis_iff_compl_inter_isBasis_…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsBase.encard_eq_eRank`：∀ {α : Type u_1} {M : Matroid α} {B : Se
t α}, M.IsBase B → B.encard = M.eRank
· 使用定理 `Matroid.IsBase.compl_isBase_of_dual`：∀ {α : Type u_1} {M : Matroid α} {B
 : Set α}, M✶.IsBase B → M.IsBase (M.E \ B)
· 使用定理 `Matroid.IsBasis.eRk_eq_encard`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → M.eRk X = I.encard
· 使用定理 `Set.encard_union_eq`：encard_union_eq (h : Disjoint s t) : (s union t).en
card = s.encard + t.encard
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Decidable.not_or_of_imp`：∀ {a b : Prop} [Decidable a], (a → b) → ¬a ∨ b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Decidable.not_and_iff_not_or_not'`：∀ {b a : Prop} [Decidable b], ¬(a ∧ b
) ↔ ¬a ∨ ¬b
· 使用定理 `Decidable.of_not_not`：∀ {p : Prop} [Decidable p], ¬¬p → p

--- 原说明 ---
A subtraction-free formula for the rank of a set in the dual matroid.
-/
lemma eRk_dual_add_eRank (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    M✶.eRk X + M.eRank = M.eRk (M.E \ X) + X.encard := by
  obtain ⟨I, hI⟩ := M✶.exists_isBasis X
  obtain ⟨B, hB, rfl⟩ := hI.exists_isBasis_inter_eq_of_superset hX
  have hB' : M✶.IsBase B := isBasis_ground_iff.1 hB
  have hd : M.IsBasis (M.E \ B ∩ (M.E \ X)) (M.E \ X) := by
    simpa using hB'.inter_isBasis_iff_compl_inter_isBasis_dual.1 hI
  rw [← hB'.compl_isBase_of_dual.encard_eq_eRank, hI.eRk_eq_encard, hd.eRk_eq_encard,
    ← encard_union_eq (by tauto_set), ← encard_union_eq (by tauto_set)]
  exact congr_arg _ (by tauto_set)

/-- A version of `Matroid.dual_eRk_add_eRank` for non-subsets of the ground set. -/
/-
**Matroid.eRk_dual_add_eRank'** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRk_dual_add_eRank' (M : Matroid α) (X : Set α) : M✶.eRk X + M.eRank = M.e
Rk (M.E \ X) + (X inter M.E).encard
参数：M : Matroid α；X : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sdiff_inter_self_eq_sdiff`：sdiff_inter_self_eq_sdiff {s t : Set α} :
 s \ (t inter s) = s \ t
· 使用引理 `Matroid.eRk_dual_add_eRank`：eRk_dual_add_eRank (M : Matroid α) (X : Set 
α) (hX : X subseteq M.E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Matroid.dual_ground`：∀ {α : Type u_1} {M : Matroid α}, M✶.E = M.E
· 使用引理 `Matroid.eRk_inter_ground`：eRk_inter_ground (M : Matroid α) (X : Set α) :
 M.eRk (X inter M.E) = M.eRk X

--- 原说明 ---
A version of `Matroid.dual_eRk_add_eRank` for non-subsets of the ground set.
-/
lemma eRk_dual_add_eRank' (M : Matroid α) (X : Set α) :
    M✶.eRk X + M.eRank = M.eRk (M.E \ X) + (X ∩ M.E).encard := by
  rw [← sdiff_inter_self_eq_sdiff, ← eRk_dual_add_eRank .., ← dual_ground, eRk_inter_ground]

@[simp]
/-
**Matroid.eRank_add_eRank_dual** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：eRank_add_eRank_dual (M : Matroid α) : M.eRank + M✶.eRank = M.E.encard
参数：M : Matroid α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBase`：∀ {α : Type u_1} (self : Matroid α), ∃ B, self.Is
Base B
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsBase.encard_eq_eRank`：∀ {α : Type u_1} {M : Matroid α} {B : Se
t α}, M.IsBase B → B.encard = M.eRank
· 使用定理 `Matroid.IsBase.compl_isBase_dual`：∀ {α : Type u_1} {M : Matroid α} {B : 
Set α}, M.IsBase B → M✶.IsBase (M.E \ B)
· 使用定理 `Set.encard_union_eq`：encard_union_eq (h : Disjoint s t) : (s union t).en
card = s.encard + t.encard
· 使用引理 `Set.disjoint_sdiff_right`：disjoint_sdiff_right : Disjoint s (t \ s)
· 使用定理 `Set.union_sdiff_cancel`：union_sdiff_cancel {s t : Set α} (h : s subseteq
 t) : s union t \ s = t
· 使用定理 `Matroid.IsBase.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {B : Set 
α}, M.IsBase B → B ⊆ M.E
-/
lemma eRank_add_eRank_dual (M : Matroid α) : M.eRank + M✶.eRank = M.E.encard := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [← hB.encard_eq_eRank, ← hB.compl_isBase_dual.encard_eq_eRank,
    ← encard_union_eq disjoint_sdiff_right, union_sdiff_cancel hB.subset_ground]

end Matroid

