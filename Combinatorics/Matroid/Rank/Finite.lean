/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
module

public import Mathlib.Combinatorics.Matroid.Closure

/-!
# Finite-rank sets

`Matroid.IsRkFinite M X`  means that every basis of the set `X` in the matroid `M` is finite,
or equivalently that the restriction of `M` to `X` is `Matroid.RankFinite`.
Sets in a matroid with `IsRkFinite` are the largest class of sets for which one can do nontrivial
integer arithmetic involving the rank function.

## Implementation Details

Unlike most set predicates on matroids, a set `X` with `M.IsRkFinite X` need not satisfy `X ⊆ M.E`,
so may contain junk elements. This seems to be what makes the definition easiest to use.
-/

@[expose] public section

variable {α : Type*} {M : Matroid α} {X Y I : Set α} {e : α}

open Set

namespace Matroid

/-- `Matroid.IsRkFinite M X` means that every basis of `X` in `M` is finite. -/
/-
**Matroid.IsRkFinite** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：IsRkFinite (M : Matroid α) (X : Set α) : Prop
参数：M : Matroid α；X : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matroid.IsRkFinite M X` means that every basis of `X` in `M` is finite.
-/
def IsRkFinite (M : Matroid α) (X : Set α) : Prop := (M ↾ X).RankFinite
/-
**Matroid.IsRkFinite.rankFinite** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsRkFinite`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X : Set α}, M.IsRkFinite X → (M.restrict
 X).RankFinite
参数：M.restrict X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsRkFinite.rankFinite (hX : M.IsRkFinite X) : (M ↾ X).RankFinite :=
  hX
/-
**Matroid.RankFinite.isRkFinite** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.RankFinite`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} [M.RankFinite] (X : Set α), M.IsRkFinite 
X
参数：X : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma RankFinite.isRkFinite [RankFinite M] (X : Set α) : M.IsRkFinite X :=
  inferInstanceAs (M ↾ X).RankFinite
/-
**Matroid.IsBasis'.finite_iff_isRkFinite** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBa
sis'`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X I : Set α}, M.IsBasis' I X → (I.Finite
 ↔ M.IsRkFinite X)
参数：I.Finite ↔ M.IsRkFinite X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBase.finite`：∀ {α : Type u_1} {M : Matroid α} {B : Set α} [M.R
ankFinite], M.IsBase B → B.Finite
· 使用定理 `Matroid.IsBasis'.isBase_restrict`：∀ {α : Type u_1} {M : Matroid α} {I X 
: Set α}, M.IsBasis' I X → (M.restrict X).IsBase I
-/
lemma IsBasis'.finite_iff_isRkFinite (hI : M.IsBasis' I X) : I.Finite ↔ M.IsRkFinite X :=
  ⟨fun h ↦ ⟨I, hI, h⟩, fun (_ : (M ↾ X).RankFinite) ↦ hI.isBase_restrict.finite⟩

alias ⟨_, IsBasis'.finite_of_isRkFinite⟩ := IsBasis'.finite_iff_isRkFinite
/-
**Matroid.IsBasis.finite_iff_isRkFinite** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBas
is`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X I : Set α}, M.IsBasis I X → (I.Finite 
↔ M.IsRkFinite X)
参数：I.Finite ↔ M.IsRkFinite X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis'.finite_iff_isRkFinite`：∀ {α : Type u_1} {M : Matroid α}
 {X I : Set α}, M.IsBasis' I X → (I.Finite ↔ M.IsRkFinite X)
· 使用定理 `Matroid.IsBasis.isBasis'`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}
, M.IsBasis I X → M.IsBasis' I X
-/
lemma IsBasis.finite_iff_isRkFinite (hI : M.IsBasis I X) : I.Finite ↔ M.IsRkFinite X :=
  hI.isBasis'.finite_iff_isRkFinite

alias ⟨_, IsBasis.finite_of_isRkFinite⟩ := IsBasis.finite_iff_isRkFinite
/-
**Matroid.IsBasis'.isRkFinite_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBas
is'`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X I : Set α}, M.IsBasis' I X → I.Finite 
→ M.IsRkFinite X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsBasis'.isRkFinite_of_finite (hI : M.IsBasis' I X) (hIfin : I.Finite) : M.IsRkFinite X :=
  ⟨I, hI, hIfin⟩
/-
**Matroid.IsBasis.isRkFinite_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasi
s`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X I : Set α}, M.IsBasis I X → I.Finite →
 M.IsRkFinite X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis.isBasis'`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}
, M.IsBasis I X → M.IsBasis' I X
-/
lemma IsBasis.isRkFinite_of_finite (hI : M.IsBasis I X) (hIfin : I.Finite) : M.IsRkFinite X :=
  ⟨I, hI.isBasis', hIfin⟩

/-- A basis' of an `IsRkFinite` set is finite. -/
/-
**Matroid.IsRkFinite.finite_of_isBasis'** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsRkF
inite`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X I : Set α}, M.IsRkFinite X → M.IsBasis
' I X → I.Finite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsRkFinite.rankFinite`：∀ {α : Type u_1} {M : Matroid α} {X : Set
 α}, M.IsRkFinite X → (M.restrict X).RankFinite
· 使用定理 `Matroid.IsBase.finite`：∀ {α : Type u_1} {M : Matroid α} {B : Set α} [M.R
ankFinite], M.IsBase B → B.Finite
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matroid.isBase_restrict_iff'`：isBase_restrict_iff' : (M ↾ X).IsBase I ↔ 
M.IsBasis' I X

--- 原说明 ---
A basis' of an `IsRkFinite` set is finite.
-/
lemma IsRkFinite.finite_of_isBasis' (h : M.IsRkFinite X) (hI : M.IsBasis' I X) : I.Finite :=
  have := h.rankFinite
  (isBase_restrict_iff'.2 hI).finite
/-
**Matroid.IsRkFinite.finite_of_isBasis** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsRkFi
nite`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X I : Set α}, M.IsRkFinite X → M.IsBasis
 I X → I.Finite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsRkFinite.finite_of_isBasis'`：∀ {α : Type u_1} {M : Matroid α} 
{X I : Set α}, M.IsRkFinite X → M.IsBasis' I X → I.Finite
· 使用定理 `Matroid.IsBasis.isBasis'`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}
, M.IsBasis I X → M.IsBasis' I X
-/
lemma IsRkFinite.finite_of_isBasis (h : M.IsRkFinite X) (hI : M.IsBasis I X) : I.Finite :=
  h.finite_of_isBasis' hI.isBasis'

/-- An `IsRkFinite` set has a finite basis' -/
/-
**Matroid.IsRkFinite.exists_finite_isBasis'** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.I
sRkFinite`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X : Set α}, M.IsRkFinite X → ∃ I, M.IsBa
sis' I X ∧ I.Finite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.RankFinite.exists_finite_isBase`：∀ {α : Type u_1} {M : Matroid α
} [self : M.RankFinite], ∃ B, M.IsBase B ∧ B.Finite

--- 原说明 ---
An `IsRkFinite` set has a finite basis'
-/
lemma IsRkFinite.exists_finite_isBasis' (h : M.IsRkFinite X) : ∃ I, M.IsBasis' I X ∧ I.Finite :=
  h.exists_finite_isBase

/-- An `IsRkFinite` set has a finset basis' -/
/-
**Matroid.IsRkFinite.exists_finset_isBasis'** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.I
sRkFinite`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X : Set α}, M.IsRkFinite X → ∃ I, M.IsBa
sis' (↑I) X
参数：↑I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsRkFinite.exists_finite_isBasis'`：∀ {α : Type u_1} {M : Matroid
 α} {X : Set α}, M.IsRkFinite X → ∃ I, M.IsBasis' I X ∧ I.Finite
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s

--- 原说明 ---
An `IsRkFinite` set has a finset basis'
-/
lemma IsRkFinite.exists_finset_isBasis' (h : M.IsRkFinite X) : ∃ (I : Finset α), M.IsBasis' I X :=
  let ⟨I, hI, hIfin⟩ := h.exists_finite_isBasis'
  ⟨hIfin.toFinset, by simpa⟩

/-- A set satisfies `IsRkFinite` iff it has a finite basis' -/
/-
**Matroid.isRkFinite_iff_exists_isBasis'** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isRkFinite_iff_exists_isBasis' : M.IsRkFinite X ↔ exists I, M.IsBasis' I X
 ∧ I.Finite
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsRkFinite.exists_finite_isBasis'`：∀ {α : Type u_1} {M : Matroid
 α} {X : Set α}, M.IsRkFinite X → ∃ I, M.IsBasis' I X ∧ I.Finite
· 使用定理 `Matroid.IsBasis'.isRkFinite_of_finite`：∀ {α : Type u_1} {M : Matroid α} 
{X I : Set α}, M.IsBasis' I X → I.Finite → M.IsRkFinite X

--- 原说明 ---
A set satisfies `IsRkFinite` iff it has a finite basis'
-/
lemma isRkFinite_iff_exists_isBasis' : M.IsRkFinite X ↔ ∃ I, M.IsBasis' I X ∧ I.Finite :=
  ⟨IsRkFinite.exists_finite_isBasis', fun ⟨_, hIX, hI⟩ ↦ hIX.isRkFinite_of_finite hI⟩
/-
**Matroid.IsRkFinite.subset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsRkFinite`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X Y : Set α}, M.IsRkFinite X → Y ⊆ X → M
.IsRkFinite Y
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
· 使用定理 `Matroid.IsBasis'.isRkFinite_of_finite`：∀ {α : Type u_1} {M : Matroid α} 
{X I : Set α}, M.IsBasis' I X → I.Finite → M.IsRkFinite X
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Matroid.IsBasis'.finite_of_isRkFinite`：∀ {α : Type u_1} {M : Matroid α} 
{X I : Set α}, M.IsBasis' I X → M.IsRkFinite X → I.Finite
-/
lemma IsRkFinite.subset (h : M.IsRkFinite X) (hXY : Y ⊆ X) : M.IsRkFinite Y := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' Y
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_isBasis'_of_subset (hI.subset.trans hXY)
  exact hI.isRkFinite_of_finite <| (hJ.finite_of_isRkFinite h).subset hIJ

@[simp]
/-
**Matroid.isRkFinite_inter_ground_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isRkFinite_inter_ground_iff : M.IsRkFinite (X inter M.E) ↔ M.IsRkFinite X
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBasis'`：exists_isBasis' (M : Matroid α) (X : Set α) : e
xists I, M.IsBasis' I X
· 使用定理 `Matroid.IsBasis'.isRkFinite_of_finite`：∀ {α : Type u_1} {M : Matroid α} 
{X I : Set α}, M.IsBasis' I X → I.Finite → M.IsRkFinite X
· 使用定理 `Matroid.IsBasis.finite_of_isRkFinite`：∀ {α : Type u_1} {M : Matroid α} {
X I : Set α}, M.IsBasis I X → M.IsRkFinite X → I.Finite
· 使用定理 `Matroid.IsBasis'.isBasis_inter_ground`：∀ {α : Type u_1} {M : Matroid α} 
{I X : Set α}, M.IsBasis' I X → M.IsBasis I (X ∩ M.E)
· 使用定理 `Matroid.IsRkFinite.subset`：∀ {α : Type u_1} {M : Matroid α} {X Y : Set α
}, M.IsRkFinite X → Y ⊆ X → M.IsRkFinite Y
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
lemma isRkFinite_inter_ground_iff : M.IsRkFinite (X ∩ M.E) ↔ M.IsRkFinite X :=
  let ⟨_I, hI⟩ := M.exists_isBasis' X
  ⟨fun h ↦ hI.isRkFinite_of_finite (hI.isBasis_inter_ground.finite_of_isRkFinite h),
    fun h ↦ h.subset inter_subset_left⟩
/-
**Matroid.IsRkFinite.inter_ground** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsRkFinite`
。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X : Set α}, M.IsRkFinite X → M.IsRkFinit
e (X ∩ M.E)
参数：X ∩ M.E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Matroid.isRkFinite_inter_ground_iff`：isRkFinite_inter_ground_iff : M.IsR
kFinite (X inter M.E) ↔ M.IsRkFinite X
-/
lemma IsRkFinite.inter_ground (h : M.IsRkFinite X) : M.IsRkFinite (X ∩ M.E) :=
  isRkFinite_inter_ground_iff.2 h
/-
**Matroid.isRkFinite_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isRkFinite_iff (hX : X subseteq M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matroid.isBasis'_iff_isBasis`：∀ {α : Type u_1} {M : Matroid α} {I X : Se
t α},   autoParam (X ⊆ M.E) Matroid.isBasis'_iff_isBasis._auto_1 → (M.IsBasis' I
 X ↔ M.IsBasis I X…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isRkFinite_iff (hX : X ⊆ M.E := by aesop_mat) :
    M.IsRkFinite X ↔ ∃ I, M.IsBasis I X ∧ I.Finite := by
  simp_rw [isRkFinite_iff_exists_isBasis', M.isBasis'_iff_isBasis hX]
/-
**Matroid.Indep.isRkFinite_iff_finite** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I : Set α}, M.Indep I → (M.IsRkFinite I 
↔ I.Finite)
参数：M.IsRkFinite I ↔ I.Finite。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Matroid.IsBasis.finite_iff_isRkFinite`：∀ {α : Type u_1} {M : Matroid α} 
{X I : Set α}, M.IsBasis I X → (I.Finite ↔ M.IsRkFinite X)
· 使用定理 `Matroid.Indep.isBasis_self`：∀ {α : Type u_1} {M : Matroid α} {I : Set α}
, M.Indep I → M.IsBasis I I
-/
lemma Indep.isRkFinite_iff_finite (hI : M.Indep I) : M.IsRkFinite I ↔ I.Finite :=
  hI.isBasis_self.finite_iff_isRkFinite.symm

alias ⟨Indep.finite_of_isRkFinite, _⟩ := Indep.isRkFinite_iff_finite

@[simp]
/-
**Matroid.isRkFinite_of_finite** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isRkFinite_of_finite (M : Matroid α) (hX : X.Finite) : M.IsRkFinite X
参数：M : Matroid α；hX : X.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBasis'`：exists_isBasis' (M : Matroid α) (X : Set α) : e
xists I, M.IsBasis' I X
· 使用定理 `Matroid.IsBasis'.isRkFinite_of_finite`：∀ {α : Type u_1} {M : Matroid α} 
{X I : Set α}, M.IsBasis' I X → I.Finite → M.IsRkFinite X
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Matroid.IsBasis'.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α},
 M.IsBasis' I X → I ⊆ X
-/
lemma isRkFinite_of_finite (M : Matroid α) (hX : X.Finite) : M.IsRkFinite X :=
  let ⟨_, hI⟩ := M.exists_isBasis' X
  hI.isRkFinite_of_finite (hX.subset hI.subset)
/-
**Matroid.Indep.subset_finite_isBasis'_of_subset_of_isRkFinite** 是 Mathlib 中的一个定
理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X I : Set α},   M.Indep I → I ⊆ X → M.Is
RkFinite X → ∃ J, M.IsBasis' J X ∧ I ⊆ J ∧ J.Finite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Matroid.IsBasis'.finite_of_isRkFinite`：∀ {α : Type u_1} {M : Matroid α} 
{X I : Set α}, M.IsBasis' I X → M.IsRkFinite X → I.Finite
· 使用定理 `Matroid.Indep.subset_isBasis'_of_subset`：∀ {α : Type u_1} {M : Matroid α
} {I X : Set α}, M.Indep I → I ⊆ X → ∃ J, M.IsBasis' J X ∧ I ⊆ J
-/
lemma Indep.subset_finite_isBasis'_of_subset_of_isRkFinite (hI : M.Indep I) (hIX : I ⊆ X)
    (hX : M.IsRkFinite X) : ∃ J, M.IsBasis' J X ∧ I ⊆ J ∧ J.Finite :=
  (hI.subset_isBasis'_of_subset hIX).imp fun _ hJ => ⟨hJ.1, hJ.2, hJ.1.finite_of_isRkFinite hX⟩
/-
**Matroid.Indep.subset_finite_isBasis_of_subset_of_isRkFinite** 是 Mathlib 中的一个定理
，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X I : Set α},   M.Indep I →     I ⊆ X → 
      M.IsRkFinite X →         autoParam (X ⊆ M.E) Matroid.Indep.subset_finite_i
sBasis_of_subset_of_isRkFinite._auto_1 →           ∃ J, M.IsBasis J X ∧ I ⊆ J ∧ 
J.Finite
参数：X ⊆ M.E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Matroid.IsBasis.finite_of_isRkFinite`：∀ {α : Type u_1} {M : Matroid α} {
X I : Set α}, M.IsBasis I X → M.IsRkFinite X → I.Finite
· 使用定理 `Matroid.Indep.subset_isBasis_of_subset`：∀ {α : Type u_1} {M : Matroid α}
 {I X : Set α},   M.Indep I → I ⊆ X → autoParam (X ⊆ M.E) Matroid.Indep.subset_i
sBasis_of_subset._auto_1 → ∃…
-/
lemma Indep.subset_finite_isBasis_of_subset_of_isRkFinite (hI : M.Indep I) (hIX : I ⊆ X)
    (hX : M.IsRkFinite X) (hXE : X ⊆ M.E := by aesop_mat) : ∃ J, M.IsBasis J X ∧ I ⊆ J ∧ J.Finite :=
  (hI.subset_isBasis_of_subset hIX).imp fun _ hJ => ⟨hJ.1, hJ.2, hJ.1.finite_of_isRkFinite hX⟩
/-
**Matroid.isRkFinite_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isRkFinite_singleton : M.IsRkFinite {e}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma isRkFinite_singleton : M.IsRkFinite {e} := by
  simp
/-
**Matroid.IsRkFinite.empty** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsRkFinite`。
形式化陈述：∀ {α : Type u_1} (M : Matroid α), M.IsRkFinite ∅
参数：M : Matroid α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matroid.isRkFinite_of_finite`：isRkFinite_of_finite (M : Matroid α) (hX :
 X.Finite) : M.IsRkFinite X
· 使用定理 `Set.finite_empty`：finite_empty : (∅ : Set α).Finite
-/
lemma IsRkFinite.empty (M : Matroid α) : M.IsRkFinite ∅ :=
  isRkFinite_of_finite M finite_empty
/-
**Matroid.IsRkFinite.finite_of_indep_subset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.I
sRkFinite`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X I : Set α}, M.IsRkFinite X → M.Indep I
 → I ⊆ X → I.Finite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.finite_of_isRkFinite`：∀ {α : Type u_1} {M : Matroid α} {I 
: Set α}, M.Indep I → M.IsRkFinite I → I.Finite
· 使用定理 `Matroid.IsRkFinite.subset`：∀ {α : Type u_1} {M : Matroid α} {X Y : Set α
}, M.IsRkFinite X → Y ⊆ X → M.IsRkFinite Y
-/
lemma IsRkFinite.finite_of_indep_subset (hX : M.IsRkFinite X) (hI : M.Indep I) (hIX : I ⊆ X) :
    I.Finite :=
  hI.finite_of_isRkFinite <| hX.subset hIX

@[simp]
/-
**Matroid.isRkFinite_ground_iff_rankFinite** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isRkFinite_ground_iff_rankFinite : M.IsRkFinite M.E ↔ M.RankFinite
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsRkFinite.eq_1`：∀ {α : Type u_1} (M : Matroid α) (X : Set α), M
.IsRkFinite X = (M.restrict X).RankFinite
· 使用定理 `Matroid.restrict_ground_eq_self`：∀ {α : Type u_1} (M : Matroid α), M.res
trict M.E = M
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isRkFinite_ground_iff_rankFinite : M.IsRkFinite M.E ↔ M.RankFinite := by
  rw [IsRkFinite, restrict_ground_eq_self]
/-
**Matroid.isRkFinite_ground** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isRkFinite_ground (M : Matroid α) [RankFinite M] : M.IsRkFinite M.E
参数：M : Matroid α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.isRkFinite_ground_iff_rankFinite`：isRkFinite_ground_iff_rankFini
te : M.IsRkFinite M.E ↔ M.RankFinite
-/
lemma isRkFinite_ground (M : Matroid α) [RankFinite M] : M.IsRkFinite M.E := by
  rwa [isRkFinite_ground_iff_rankFinite]
/-
**Matroid.Indep.finite_of_subset_isRkFinite** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.I
ndep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X I : Set α}, M.Indep I → I ⊆ X → M.IsRk
Finite X → I.Finite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsRkFinite.finite_of_indep_subset`：∀ {α : Type u_1} {M : Matroid
 α} {X I : Set α}, M.IsRkFinite X → M.Indep I → I ⊆ X → I.Finite
-/
lemma Indep.finite_of_subset_isRkFinite (hI : M.Indep I) (hIX : I ⊆ X) (hX : M.IsRkFinite X) :
    I.Finite :=
  hX.finite_of_indep_subset hI hIX
/-
**Matroid.IsRkFinite.closure** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsRkFinite`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X : Set α}, M.IsRkFinite X → M.IsRkFinit
e (M.closure X)
参数：M.closure X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBasis'`：exists_isBasis' (M : Matroid α) (X : Set α) : e
xists I, M.IsBasis' I X
· 使用定理 `Matroid.IsBasis.isRkFinite_of_finite`：∀ {α : Type u_1} {M : Matroid α} {
X I : Set α}, M.IsBasis I X → I.Finite → M.IsRkFinite X
· 使用定理 `Matroid.IsBasis'.isBasis_closure_right`：∀ {α : Type u_2} {M : Matroid α}
 {X I : Set α}, M.IsBasis' I X → M.IsBasis I (M.closure X)
· 使用定理 `Matroid.IsBasis'.finite_of_isRkFinite`：∀ {α : Type u_1} {M : Matroid α} 
{X I : Set α}, M.IsBasis' I X → M.IsRkFinite X → I.Finite
-/
lemma IsRkFinite.closure (h : M.IsRkFinite X) : M.IsRkFinite (M.closure X) :=
  let ⟨_, hI⟩ := M.exists_isBasis' X
  hI.isBasis_closure_right.isRkFinite_of_finite <| hI.finite_of_isRkFinite h

@[simp]
/-
**Matroid.isRkFinite_closure_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isRkFinite_closure_iff : M.IsRkFinite (M.closure X) ↔ M.IsRkFinite X
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.isRkFinite_inter_ground_iff`：isRkFinite_inter_ground_iff : M.IsR
kFinite (X inter M.E) ↔ M.IsRkFinite X
· 使用定理 `Matroid.IsRkFinite.subset`：∀ {α : Type u_1} {M : Matroid α} {X Y : Set α
}, M.IsRkFinite X → Y ⊆ X → M.IsRkFinite Y
· 使用引理 `Matroid.inter_ground_subset_closure`：inter_ground_subset_closure (M : Ma
troid α) (X : Set α) : X inter M.E subseteq M.closure X
· 使用定理 `Matroid.closure_inter_ground`：∀ {α : Type u_2} (M : Matroid α) (X : Set 
α), M.closure (X ∩ M.E) = M.closure X
· 使用定理 `Matroid.IsRkFinite.closure`：∀ {α : Type u_1} {M : Matroid α} {X : Set α}
, M.IsRkFinite X → M.IsRkFinite (M.closure X)
-/
lemma isRkFinite_closure_iff : M.IsRkFinite (M.closure X) ↔ M.IsRkFinite X := by
  rw [← isRkFinite_inter_ground_iff (X := X)]
  exact ⟨fun h ↦ h.subset <| M.inter_ground_subset_closure X, fun h ↦ by simpa using h.closure⟩
/-
**Matroid.IsRkFinite.union** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsRkFinite`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X Y : Set α}, M.IsRkFinite X → M.IsRkFin
ite Y → M.IsRkFinite (X ∪ Y)
参数：X ∪ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsRkFinite.exists_finite_isBasis'`：∀ {α : Type u_1} {M : Matroid
 α} {X : Set α}, M.IsRkFinite X → ∃ I, M.IsBasis' I X ∧ I.Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.isRkFinite_inter_ground_iff`：isRkFinite_inter_ground_iff : M.IsR
kFinite (X inter M.E) ↔ M.IsRkFinite X
· 使用定理 `Matroid.IsRkFinite.subset`：∀ {α : Type u_1} {M : Matroid α} {X Y : Set α
}, M.IsRkFinite X → Y ⊆ X → M.IsRkFinite Y
· 使用定理 `Matroid.IsRkFinite.closure`：∀ {α : Type u_1} {M : Matroid α} {X : Set α}
, M.IsRkFinite X → M.IsRkFinite (M.closure X)
· 使用引理 `Matroid.isRkFinite_of_finite`：isRkFinite_of_finite (M : Matroid α) (hX :
 X.Finite) : M.IsRkFinite X
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用引理 `Matroid.closure_union_congr_left`：closure_union_congr_left {X' : Set α} 
(h : M.closure X = M.closure X') : M.closure (X union Y) = M.closure (X' union Y
)
· 使用定理 `Matroid.IsBasis'.closure_eq_closure`：∀ {α : Type u_2} {M : Matroid α} {X
 I : Set α}, M.IsBasis' I X → M.closure I = M.closure X
· 使用引理 `Matroid.closure_union_congr_right`：closure_union_congr_right {Y' : Set α
} (h : M.closure Y = M.closure Y') : M.closure (X union Y) = M.closure (X union 
Y')
· 使用引理 `Matroid.inter_ground_subset_closure`：inter_ground_subset_closure (M : Ma
troid α) (X : Set α) : X inter M.E subseteq M.closure X
-/
lemma IsRkFinite.union (hX : M.IsRkFinite X) (hY : M.IsRkFinite Y) : M.IsRkFinite (X ∪ Y) := by
  obtain ⟨I, hI, hIfin⟩ := hX.exists_finite_isBasis'
  obtain ⟨J, hJ, hJfin⟩ := hY.exists_finite_isBasis'
  rw [← isRkFinite_inter_ground_iff]
  refine (M.isRkFinite_of_finite (hIfin.union hJfin)).closure.subset ?_
  rw [closure_union_congr_left hI.closure_eq_closure,
    closure_union_congr_right hJ.closure_eq_closure]
  exact inter_ground_subset_closure M (X ∪ Y)
/-
**Matroid.IsRkFinite.isRkFinite_union_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsR
kFinite`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X Y : Set α}, M.IsRkFinite X → (M.IsRkFi
nite (X ∪ Y) ↔ M.IsRkFinite Y)
参数：M.IsRkFinite (X ∪ Y) ↔ M.IsRkFinite Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsRkFinite.subset`：∀ {α : Type u_1} {M : Matroid α} {X Y : Set α
}, M.IsRkFinite X → Y ⊆ X → M.IsRkFinite Y
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `Matroid.IsRkFinite.union`：∀ {α : Type u_1} {M : Matroid α} {X Y : Set α}
, M.IsRkFinite X → M.IsRkFinite Y → M.IsRkFinite (X ∪ Y)
-/
lemma IsRkFinite.isRkFinite_union_iff (hX : M.IsRkFinite X) :
    M.IsRkFinite (X ∪ Y) ↔ M.IsRkFinite Y :=
  ⟨fun h ↦ h.subset subset_union_right, fun h ↦ hX.union h⟩
/-
**Matroid.IsRkFinite.isRkFinite_sdiff_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsR
kFinite`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X Y : Set α}, M.IsRkFinite X → (M.IsRkFi
nite (Y \ X) ↔ M.IsRkFinite Y)
参数：M.IsRkFinite (Y \ X) ↔ M.IsRkFinite Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsRkFinite.isRkFinite_union_iff`：∀ {α : Type u_1} {M : Matroid α
} {X Y : Set α}, M.IsRkFinite X → (M.IsRkFinite (X ∪ Y) ↔ M.IsRkFinite Y)
· 使用定理 `Set.union_sdiff_self`：union_sdiff_self {s t : Set α} : s union t \ s = s
 union t
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma IsRkFinite.isRkFinite_sdiff_iff (hX : M.IsRkFinite X) :
    M.IsRkFinite (Y \ X) ↔ M.IsRkFinite Y := by
  rw [← hX.isRkFinite_union_iff, union_sdiff_self, hX.isRkFinite_union_iff]

@[deprecated (since := "2026-06-03")]
alias IsRkFinite.isRkFinite_diff_iff := IsRkFinite.isRkFinite_sdiff_iff
/-
**Matroid.IsRkFinite.inter_right** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsRkFinite`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X Y : Set α}, M.IsRkFinite X → M.IsRkFin
ite (X ∩ Y)
参数：X ∩ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsRkFinite.subset`：∀ {α : Type u_1} {M : Matroid α} {X Y : Set α
}, M.IsRkFinite X → Y ⊆ X → M.IsRkFinite Y
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
lemma IsRkFinite.inter_right (hX : M.IsRkFinite X) : M.IsRkFinite (X ∩ Y) :=
  hX.subset inter_subset_left
/-
**Matroid.IsRkFinite.inter_left** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsRkFinite`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X Y : Set α}, M.IsRkFinite X → M.IsRkFin
ite (Y ∩ X)
参数：Y ∩ X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsRkFinite.subset`：∀ {α : Type u_1} {M : Matroid α} {X Y : Set α
}, M.IsRkFinite X → Y ⊆ X → M.IsRkFinite Y
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
lemma IsRkFinite.inter_left (hX : M.IsRkFinite X) : M.IsRkFinite (Y ∩ X) :=
  hX.subset inter_subset_right
/-
**Matroid.IsRkFinite.diff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsRkFinite`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X Y : Set α}, M.IsRkFinite X → M.IsRkFin
ite (X \ Y)
参数：X \ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsRkFinite.subset`：∀ {α : Type u_1} {M : Matroid α} {X Y : Set α
}, M.IsRkFinite X → Y ⊆ X → M.IsRkFinite Y
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
-/
lemma IsRkFinite.diff (hX : M.IsRkFinite X) : M.IsRkFinite (X \ Y) :=
  hX.subset sdiff_subset
/-
**Matroid.IsRkFinite.insert** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsRkFinite`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X : Set α}, M.IsRkFinite X → ∀ (e : α), 
M.IsRkFinite (insert e X)
参数：e : α；insert e X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `Matroid.IsRkFinite.union`：∀ {α : Type u_1} {M : Matroid α} {X Y : Set α}
, M.IsRkFinite X → M.IsRkFinite Y → M.IsRkFinite (X ∪ Y)
· 使用引理 `Matroid.isRkFinite_singleton`：isRkFinite_singleton : M.IsRkFinite {e}
-/
lemma IsRkFinite.insert (hX : M.IsRkFinite X) (e : α) : M.IsRkFinite (insert e X) := by
  rw [← union_singleton]
  exact hX.union M.isRkFinite_singleton

@[simp]
/-
**Matroid.isRkFinite_insert_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isRkFinite_insert_iff {e : α} : M.IsRkFinite (insert e X) ↔ M.IsRkFinite X
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.singleton_union`：singleton_union : {a} union s = insert a s
· 使用定理 `Matroid.IsRkFinite.isRkFinite_union_iff`：∀ {α : Type u_1} {M : Matroid α
} {X Y : Set α}, M.IsRkFinite X → (M.IsRkFinite (X ∪ Y) ↔ M.IsRkFinite Y)
· 使用引理 `Matroid.isRkFinite_singleton`：isRkFinite_singleton : M.IsRkFinite {e}
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isRkFinite_insert_iff {e : α} : M.IsRkFinite (insert e X) ↔ M.IsRkFinite X := by
  rw [← singleton_union, isRkFinite_singleton.isRkFinite_union_iff]

@[simp]
/-
**Matroid.IsRkFinite.sdiff_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsRk
Finite`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X : Set α} {e : α}, M.IsRkFinite (X \ {e
}) ↔ M.IsRkFinite X
参数：X \ {e}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsRkFinite.isRkFinite_sdiff_iff`：∀ {α : Type u_1} {M : Matroid α
} {X Y : Set α}, M.IsRkFinite X → (M.IsRkFinite (Y \ X) ↔ M.IsRkFinite Y)
· 使用引理 `Matroid.isRkFinite_singleton`：isRkFinite_singleton : M.IsRkFinite {e}
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma IsRkFinite.sdiff_singleton_iff : M.IsRkFinite (X \ {e}) ↔ M.IsRkFinite X := by
  rw [isRkFinite_singleton.isRkFinite_sdiff_iff]

@[deprecated (since := "2026-06-03")]
alias IsRkFinite.diff_singleton_iff := IsRkFinite.sdiff_singleton_iff
/-
**Matroid.isRkFinite_set** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isRkFinite_set (M : Matroid α) [RankFinite M] (X : Set α) : M.IsRkFinite X
参数：M : Matroid α；X : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBasis'`：exists_isBasis' (M : Matroid α) (X : Set α) : e
xists I, M.IsBasis' I X
· 使用定理 `Matroid.IsBasis'.isRkFinite_of_finite`：∀ {α : Type u_1} {M : Matroid α} 
{X I : Set α}, M.IsBasis' I X → I.Finite → M.IsRkFinite X
· 使用定理 `Matroid.Indep.finite`：∀ {α : Type u_1} {M : Matroid α} {I : Set α} [M.Ra
nkFinite], M.Indep I → I.Finite
· 使用定理 `Matroid.IsBasis'.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis' I X → M.Indep I
-/
lemma isRkFinite_set (M : Matroid α) [RankFinite M] (X : Set α) : M.IsRkFinite X :=
  let ⟨_, hI⟩ := M.exists_isBasis' X
  hI.isRkFinite_of_finite hI.indep.finite

/-- A union of finitely many `IsRkFinite` sets is `IsRkFinite`. -/
/-
**Matroid.IsRkFinite.iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsRkFinite`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {ι : Type u_2} [Finite ι] {Xs : ι → Set α
},   (∀ (i : ι), M.IsRkFinite (Xs i)) → M.IsRkFinite (⋃ i, Xs i)
参数：∀ (i : ι), M.IsRkFinite (Xs i)；⋃ i, Xs i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.finite_iUnion`：finite_iUnion [Finite ι] {f : ι -> Set α} (H : forall
 i, (f i).Finite) : (⋃ i, f i).Finite
· 使用定理 `Matroid.IsRkFinite.finite_of_isBasis'`：∀ {α : Type u_1} {M : Matroid α} 
{X I : Set α}, M.IsRkFinite X → M.IsBasis' I X → I.Finite
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Matroid.isRkFinite_inter_ground_iff`：isRkFinite_inter_ground_iff : M.IsR
kFinite (X inter M.E) ↔ M.IsRkFinite X
· 使用定理 `Matroid.IsRkFinite.subset`：∀ {α : Type u_1} {M : Matroid α} {X Y : Set α
}, M.IsRkFinite X → Y ⊆ X → M.IsRkFinite Y
· 使用定理 `Matroid.IsRkFinite.closure`：∀ {α : Type u_1} {M : Matroid α} {X : Set α}
, M.IsRkFinite X → M.IsRkFinite (M.closure X)
· 使用引理 `Matroid.isRkFinite_of_finite`：isRkFinite_of_finite (M : Matroid α) (hX :
 X.Finite) : M.IsRkFinite X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnion_inter`：iUnion_inter (s : Set β) (t : ι -> Set β) : (⋃ i, t i)
 inter s = ⋃ i, t i inter s
· 使用定理 `Set.iUnion_subset_iff`：iUnion_subset_iff {s : ι -> Set α} {t : Set α} : 
⋃ i, s i subseteq t ↔ forall i, s i subseteq t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Matroid.IsBasis.subset_closure`：∀ {α : Type u_2} {M : Matroid α} {X I : 
Set α}, M.IsBasis I X → X ⊆ M.closure I
· 使用定理 `Matroid.IsBasis'.isBasis_inter_ground`：∀ {α : Type u_1} {M : Matroid α} 
{I X : Set α}, M.IsBasis' I X → M.IsBasis I (X ∩ M.E)
· 使用引理 `Matroid.closure_subset_closure`：closure_subset_closure (M : Matroid α) (
h : X subseteq Y) : M.closure X subseteq M.closure Y
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
· 使用定理 `Matroid.exists_isBasis'`：exists_isBasis' (M : Matroid α) (X : Set α) : e
xists I, M.IsBasis' I X
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
A union of finitely many `IsRkFinite` sets is `IsRkFinite`.
-/
lemma IsRkFinite.iUnion {ι : Type*} [Finite ι] {Xs : ι → Set α} (h : ∀ i, M.IsRkFinite (Xs i)) :
    M.IsRkFinite (⋃ i, Xs i) := by
  choose Is hIs using fun i ↦ M.exists_isBasis' (Xs i)
  have hfin : (⋃ i, Is i).Finite := finite_iUnion <| fun i ↦ (h i).finite_of_isBasis' (hIs i)
  refine isRkFinite_inter_ground_iff.1 <| (M.isRkFinite_of_finite hfin).closure.subset ?_
  rw [iUnion_inter, iUnion_subset_iff]
  exact fun i ↦ (hIs i).isBasis_inter_ground.subset_closure.trans <| M.closure_subset_closure <|
    subset_iUnion ..

end Matroid

