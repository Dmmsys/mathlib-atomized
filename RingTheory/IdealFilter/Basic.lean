/-
Copyright (c) 2025 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/
module

public import Mathlib.Order.PFilter
public import Mathlib.RingTheory.Ideal.Colon

/-!
# Ideal Filters

An **ideal filter** is a filter in the lattice of ideals of a ring `A`.

## Main definitions

* `IdealFilter A`: the type of an ideal filter on a ring `A`.
* `IsUniform F` : a filter `F` is uniform if whenever `I` is an ideal in the filter, then for all
  `a : A`, the colon ideal `I.colon {a}` is in `F`.
* `IsTorsionElem` : Given a filter `F`, an element, `m`, of an `A`-module, `M`, is `F`-torsion if
  there exists an ideal `L` in `F` that annihilates `m`.
* `IsTorsion` : Given a filter `F`, an `A`-module, `M`, is `F`-torsion if every element is torsion.
* `gabrielComposition` : Given two filters `F` and `G`, the Gabriel composition of `F` and `G` is
  the set of ideals `L` of `A` such that there exists an ideal `K` in `G` with `K/L` `F`-torsion.
  This is again a filter.
* `IsGabriel F` : a filter `F` is a Gabriel filter if it is uniform and satisfies axiom T4:
  for all `I : Ideal A`, if there exists `J ∈ F` such that for all `a ∈ J` the colon ideal
  `I.colon {a}` is in `F`, then `I ∈ F`.

## Main statements

* `isGabriel_iff`: a filter is Gabriel iff it is uniform and `F • F = F`.

## Notation

* `F • G`: the Gabriel composition of ideal filters `F` and `G`, defined by
  `gabrielComposition F G`.

## Implementation notes

In the classical literature (e.g. Stenström), *right linear topologies* on a ring are often
described via filters of open **right** ideals, and the terminology is frequently abused by
identifying the topology with its filter of ideals.

In this development we work systematically with **left ideals**. Accordingly, Stenström’s
right-ideal construction `(L : a) = {x ∈ A | a * x ∈ L}` is replaced by the left ideal
`L.colon {a} = {a | x * a ∈ L}`.

With this convention, uniform filters correspond to linear (additive) topologies, while the
additional Gabriel condition (axiom T4) imposes an algebraic saturation property that does not
change the induced topology.

## References

* [Bo Stenström, *Rings and Modules of Quotients*][stenstrom1971]
* [Bo Stenström, *Rings of Quotients*][stenstrom1975]
* [nLab: Uniform filter](https://ncatlab.org/nlab/show/uniform+filter)
* [nLab: Gabriel filter](https://ncatlab.org/nlab/show/Gabriel+filter)
* [nLab: Gabriel composition](https://ncatlab.org/nlab/show/Gabriel+composition+of+filters)

## Tags

ring theory, ideal, filter, uniform filter, Gabriel filter, torsion theory
-/

@[expose] public section

open scoped Pointwise

/-- `IdealFilter A` is the type of `Order.PFilter`s on the lattice of ideals of `A`. -/
/-
**IdealFilter** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：IdealFilter (A : Type*) [Ring A]
参数：A : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IdealFilter A` is the type of `Order.PFilter`s on the lattice of ideals of `A`.
-/
abbrev IdealFilter (A : Type*) [Ring A] := Order.PFilter (Ideal A)

namespace IdealFilter

variable {A : Type*} [Ring A]

/-- A filter of ideals is *uniform* if it is closed under colon by singletons. -/
/-
**IdealFilter.IsUniform** 是 Mathlib 中的一个归纳类型，位于命名空间 `IdealFilter`。
形式化陈述：{A : Type u_1} → [inst : Ring A] → IdealFilter A → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A filter of ideals is *uniform* if it is closed under colon by singletons.
-/
class IsUniform (F : IdealFilter A) : Prop where
  /-- **Axiom T3.**  See [stenstrom1975]. -/
  colon_mem {I : Ideal A} (hI : I ∈ F) (a : A) : I.colon {a} ∈ F

/-- We say that an element `m : M` is `F`-torsion if it is annihilated by some ideal belonging to
the filter `F`. -/
/-
**IdealFilter.IsTorsionElem** 是 Mathlib 中的一个定义，位于命名空间 `IdealFilter`。
形式化陈述：IsTorsionElem (F : IdealFilter A) {M : Type*} [AddCommMonoid M] [Module A 
M] (m : M) : Prop
参数：F : IdealFilter A；m : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that an element `m : M` is `F`-torsion if it is annihilated by some ideal
 belonging to
the filter `F`.
-/
def IsTorsionElem (F : IdealFilter A)
    {M : Type*} [AddCommMonoid M] [Module A M] (m : M) : Prop :=
  ∃ L ∈ F, ∀ a ∈ L, a • m = 0

/-- Module-level `F`-torsion: every element is `F`-torsion. -/
/-
**IdealFilter.IsTorsion** 是 Mathlib 中的一个定义，位于命名空间 `IdealFilter`。
形式化陈述：IsTorsion (F : IdealFilter A) (M : Type*) [AddCommMonoid M] [Module A M] :
 Prop
参数：F : IdealFilter A；M : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Module-level `F`-torsion: every element is `F`-torsion.
-/
def IsTorsion (F : IdealFilter A)
    (M : Type*) [AddCommMonoid M] [Module A M] : Prop :=
  ∀ m : M, IsTorsionElem F m

/-- We say that the quotient `K/L` is `F`-torsion if every element `k ∈ K` is annihilated
(modulo `L`) by some ideal in `F`. Equivalently, for each `k ∈ K` there exists `I ∈ F`
such that `I ≤ L.colon {k}`. This formulation avoids forming the quotient module explicitly. -/
/-
**IdealFilter.IsTorsionQuot** 是 Mathlib 中的一个定义，位于命名空间 `IdealFilter`。
形式化陈述：IsTorsionQuot (F : IdealFilter A) (L K : Ideal A) : Prop
参数：F : IdealFilter A；L K : Ideal A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that the quotient `K/L` is `F`-torsion if every element `k ∈ K` is annihi
lated
(modulo `L`) by some ideal in `F`. Equivalently, for each `k ∈ K` there exists `
I ∈ F`
such that `I ≤ L.colon {k}`. This formulation avoids forming the quotient module
 explicitly.
-/
def IsTorsionQuot (F : IdealFilter A) (L K : Ideal A) : Prop :=
  ∀ k ∈ K, ∃ I ∈ F, I ≤ L.colon {k}

/-- Intersecting the left ideal with `K` does not change `IsTorsionQuot` on the right.
In particular, `IsTorsionQuot F L K` need not require `L ≤ K` for it is equivalent to asserting
the quotient `K / (L ⊓ K)` is `F`-torsion. -/
/-
**IdealFilter.isTorsionQuot_inter_left_iff** 是 Mathlib 中的一个引理，位于命名空间 `IdealFilte
r`。
形式化陈述：isTorsionQuot_inter_left_iff {F : IdealFilter A} {L K : Ideal A} : IsTorsi
onQuot F (L ⊓ K) K ↔ IsTorsionQuot F L K
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Submodule.colon_inf_eq_left_of_subset`：colon_inf_eq_left_of_subset (h : 
S subseteq (N₂ : Set M)) : (N₁ ⊓ N₂).colon S = N₁.colon S
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
Intersecting the left ideal with `K` does not change `IsTorsionQuot` on the righ
t.
In particular, `IsTorsionQuot F L K` need not require `L ≤ K` for it is equivale
nt to asserting
the quotient `K / (L ⊓ K)` is `F`-torsion.
-/
lemma isTorsionQuot_inter_left_iff {F : IdealFilter A} {L K : Ideal A} :
    IsTorsionQuot F (L ⊓ K) K ↔ IsTorsionQuot F L K := by
  constructor <;>
  · intro h k hk
    rcases h k hk with ⟨I, hI, hI_le⟩
    have hcol : (L ⊓ K).colon {k} = Submodule.colon L {k} :=
      Submodule.colon_inf_eq_left_of_subset (Set.singleton_subset_iff.mpr hk)
    exact ⟨I, hI, (by simpa [hcol] using hI_le)⟩
/-
**IdealFilter.isTorsion_def** 是 Mathlib 中的一个定理，位于命名空间 `IdealFilter`。
形式化陈述：∀ {A : Type u_1} [inst : Ring A] (F : IdealFilter A) (M : Type u_2) [inst_
1 : AddCommMonoid M]   [inst_2 : _root_.Module A M], F.IsTorsion M ↔ ∀ (m : M), 
F.IsTorsionElem m
参数：F : IdealFilter A；M : Type u_2；m : M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma isTorsion_def (F : IdealFilter A) (M : Type*) [AddCommMonoid M] [Module A M] :
    IsTorsion F M ↔ ∀ m : M, IsTorsionElem F m :=
  Iff.rfl
/-
**IdealFilter.isTorsionQuot_def** 是 Mathlib 中的一个定理，位于命名空间 `IdealFilter`。
形式化陈述：∀ {A : Type u_1} [inst : Ring A] {F : IdealFilter A} {L K : Ideal A},   F.
IsTorsionQuot L K ↔ ∀ k ∈ ↑K, ∃ I ∈ F, I ≤ Submodule.colon L {k}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma isTorsionQuot_def {F : IdealFilter A} {L K : Ideal A} :
    IsTorsionQuot F L K ↔ ∀ k ∈ (K : Set A), ∃ I ∈ F, I ≤ L.colon {k} :=
  Iff.rfl
/-
**IdealFilter.isTorsionQuot_self** 是 Mathlib 中的一个引理，位于命名空间 `IdealFilter`。
形式化陈述：isTorsionQuot_self (F : IdealFilter A) (I : Ideal A) : IsTorsionQuot F I I
参数：F : IdealFilter A；I : Ideal A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.PFilter.nonempty`：∀ {P : Type u_1} [inst : Preorder P] (F : Order.
PFilter P), (↑F).Nonempty
· 使用定理 `le_of_le_of_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma isTorsionQuot_self (F : IdealFilter A) (I : Ideal A) :
    IsTorsionQuot F I I := by
  intro x hx
  obtain ⟨J, hJ⟩ := F.nonempty
  exact ⟨J, hJ, le_of_le_of_eq le_top (by simpa [eq_comm])⟩
/-
**IdealFilter.IsTorsionQuot.mono_left** 是 Mathlib 中的一个定理，位于命名空间 `IdealFilter.IsT
orsionQuot`。
形式化陈述：∀ {A : Type u_1} [inst : Ring A] {F : IdealFilter A} {I J K : Ideal A},   
I ≤ J → F.IsTorsionQuot I K → F.IsTorsionQuot J K
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.imp_right`：∀ {a b c : Prop}, (a → b) → c ∧ a → c ∧ b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Submodule.colon_mono`：colon_mono (hn : N₁ <= N₂) (hs : S₁ subseteq S₂) :
 N₁.colon S₂ <= N₂.colon S₁
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
lemma IsTorsionQuot.mono_left {F : IdealFilter A}
    {I J K : Ideal A} (hIJ : I ≤ J) (hIK : IsTorsionQuot F I K) : IsTorsionQuot F J K :=
  fun _ h ↦ (hIK _ h).imp fun _ ↦ And.imp_right (le_trans · (Submodule.colon_mono hIJ .rfl))
/-
**IdealFilter.IsTorsionQuot.anti_right** 是 Mathlib 中的一个定理，位于命名空间 `IdealFilter.Is
TorsionQuot`。
形式化陈述：∀ {A : Type u_1} [inst : Ring A] {F : IdealFilter A} {I J K : Ideal A},   
J ≤ K → F.IsTorsionQuot I K → F.IsTorsionQuot I J
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsTorsionQuot.anti_right {F : IdealFilter A}
    {I J K : Ideal A} (hJK : J ≤ K) (hIK : IsTorsionQuot F I K) : IsTorsionQuot F I J :=
  fun x hx ↦ hIK x (hJK hx)
/-
**IdealFilter.IsTorsionQuot.mono** 是 Mathlib 中的一个定理，位于命名空间 `IdealFilter.IsTorsio
nQuot`。
形式化陈述：∀ {A : Type u_1} [inst : Ring A] {F : IdealFilter A} {I J K L : Ideal A}, 
  F.IsTorsionQuot I K → I ≤ J → L ≤ K → F.IsTorsionQuot J L
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IdealFilter.IsTorsionQuot.anti_right`：∀ {A : Type u_1} [inst : Ring A] {
F : IdealFilter A} {I J K : Ideal A},   J ≤ K → F.IsTorsionQuot I K → F.IsTorsio
nQuot I J
· 使用定理 `IdealFilter.IsTorsionQuot.mono_left`：∀ {A : Type u_1} [inst : Ring A] {F
 : IdealFilter A} {I J K : Ideal A},   I ≤ J → F.IsTorsionQuot I K → F.IsTorsion
Quot J K
-/
lemma IsTorsionQuot.mono {F : IdealFilter A} {I J K L : Ideal A} (hIK : IsTorsionQuot F I K)
    (hIJ : I ≤ J) (hLK : L ≤ K) : IsTorsionQuot F J L :=
  (hIK.mono_left hIJ).anti_right hLK
/-
**IdealFilter.IsTorsionQuot.inf** 是 Mathlib 中的一个定理，位于命名空间 `IdealFilter.IsTorsion
Quot`。
形式化陈述：∀ {A : Type u_1} [inst : Ring A] {F : IdealFilter A} {I J K : Ideal A},   
F.IsTorsionQuot I K → F.IsTorsionQuot J K → F.IsTorsionQuot (I ⊓ J) K
参数：I ⊓ J。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.PFilter.inf_mem`：inf_mem (hx : x in F) (hy : y in F) : x ⊓ y in F
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `inf_le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c d : α}, b ≤ 
a → d ≤ c → b ⊓ d ≤ a ⊓ c
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用引理 `Submodule.inf_colon`：inf_colon : (N₁ ⊓ N₂).colon S = N₁.colon S ⊓ N₂.col
on S
-/
lemma IsTorsionQuot.inf {F : IdealFilter A}
    {I J K : Ideal A} (hI : IsTorsionQuot F I K) (hJ : IsTorsionQuot F J K) :
    IsTorsionQuot F (I ⊓ J) K := by
  intro x hx
  obtain ⟨I', hI'F, hI'x⟩ := hI x hx
  obtain ⟨J', hJ'F, hJ'x⟩ := hJ x hx
  exact ⟨_, F.inf_mem hI'F hJ'F, (inf_le_inf hI'x hJ'x).trans Submodule.inf_colon.ge⟩
/-
**IdealFilter.isPFilter_gabrielComposition** 是 Mathlib 中的一个引理，位于命名空间 `IdealFilte
r`。
形式化陈述：isPFilter_gabrielComposition (F G : IdealFilter A) : Order.IsPFilter {L : 
Ideal A | exists K in G, F.IsTorsionQuot L K}
参数：F G : IdealFilter A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsPFilter.of_def`：∀ {P : Type u_1} [inst : Preorder P] {F : Set P}
,   F.Nonempty → DirectedOn (fun x1 x2 => x1 ≥ x2) F → (∀ {x y : P}, x ≤ y → x ∈
 F → y ∈ F) …
· 使用定理 `Order.PFilter.nonempty`：∀ {P : Type u_1} [inst : Preorder P] (F : Order.
PFilter P), (↑F).Nonempty
· 使用引理 `IdealFilter.isTorsionQuot_self`：isTorsionQuot_self (F : IdealFilter A) (
I : Ideal A) : IsTorsionQuot F I I
· 使用定理 `Order.PFilter.inf_mem`：inf_mem (hx : x in F) (hy : y in F) : x ⊓ y in F
· 使用定理 `IdealFilter.IsTorsionQuot.inf`：∀ {A : Type u_1} [inst : Ring A] {F : Ide
alFilter A} {I J K : Ideal A},   F.IsTorsionQuot I K → F.IsTorsionQuot J K → F.I
sTorsionQuot (I ⊓ J…
· 使用定理 `IdealFilter.IsTorsionQuot.anti_right`：∀ {A : Type u_1} [inst : Ring A] {
F : IdealFilter A} {I J K : Ideal A},   J ≤ K → F.IsTorsionQuot I K → F.IsTorsio
nQuot I J
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `IdealFilter.IsTorsionQuot.mono_left`：∀ {A : Type u_1} [inst : Ring A] {F
 : IdealFilter A} {I J K : Ideal A},   I ≤ J → F.IsTorsionQuot I K → F.IsTorsion
Quot J K
-/
lemma isPFilter_gabrielComposition (F G : IdealFilter A) :
    Order.IsPFilter {L : Ideal A | ∃ K ∈ G, F.IsTorsionQuot L K} := by
  refine Order.IsPFilter.of_def ?nonempty ?directed ?mem_of_le
  · obtain ⟨J, hJ⟩ := G.nonempty
    exact ⟨J, J, hJ, isTorsionQuot_self F J⟩
  · rintro I ⟨K, hK, hIK⟩ J ⟨L, hL, hJL⟩
    refine ⟨I ⊓ J, ?_, inf_le_left, inf_le_right⟩
    exact ⟨K ⊓ L, G.inf_mem hK hL,
      (hIK.anti_right inf_le_left).inf (hJL.anti_right inf_le_right)⟩
  · intro I J hIJ ⟨K, hK, hIK⟩
    exact ⟨K, hK, hIK.mono_left hIJ⟩

/-- The Gabriel composition of ideal filters `F` and `G`.
See [nLab: Gabriel composition](https://ncatlab.org/nlab/show/Gabriel+composition+of+filters). -/
/-
**IdealFilter.gabrielComposition** 是 Mathlib 中的一个定义，位于命名空间 `IdealFilter`。
形式化陈述：gabrielComposition (F G : IdealFilter A) : IdealFilter A
参数：F G : IdealFilter A。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `IdealFilter.isPFilter_gabrielComposition`：isPFilter_gabrielComposition (
F G : IdealFilter A) : Order.IsPFilter {L : Ideal A | exists K in G, F.IsTorsion
Quot L K}

--- 原说明 ---
The Gabriel composition of ideal filters `F` and `G`.
See [nLab: Gabriel composition](https://ncatlab.org/nlab/show/Gabriel+compositio
n+of+filters).
-/
def gabrielComposition (F G : IdealFilter A) : IdealFilter A :=
  (isPFilter_gabrielComposition F G).toPFilter

/-- `F • G` is the Gabriel composition of ideal filters `F` and `G`. -/
scoped infixl:70 " • " => gabrielComposition

/-- An ideal filter is Gabriel if it satisfies `IsUniform` and axiom T4.
See [nLab: Gabriel filter](https://ncatlab.org/nlab/show/Gabriel+filter). -/
/-
**IdealFilter.IsGabriel** 是 Mathlib 中的一个归纳类型，位于命名空间 `IdealFilter`。
形式化陈述：{A : Type u_1} → [inst : Ring A] → IdealFilter A → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An ideal filter is Gabriel if it satisfies `IsUniform` and axiom T4.
See [nLab: Gabriel filter](https://ncatlab.org/nlab/show/Gabriel+filter).
-/
class IsGabriel (F : IdealFilter A) extends F.IsUniform where
  /-- **Axiom T4.** See [stenstrom1975]. -/
  gabriel_closed (I : Ideal A) (h : ∃ J ∈ F, ∀ x ∈ J, I.colon {x} ∈ F) : I ∈ F

/-- Characterization of Gabriel filters via `IsUniform` and idempotence of
`gabrielComposition`. -/
/-
**IdealFilter.isGabriel_iff** 是 Mathlib 中的一个定理，位于命名空间 `IdealFilter`。
形式化陈述：isGabriel_iff (F : IdealFilter A) : F.IsGabriel ↔ F.IsUniform ∧ F • F = F
参数：F : IdealFilter A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IdealFilter.IsGabriel.toIsUniform`：∀ {A : Type u_1} {inst : Ring A} {F :
 IdealFilter A} [self : F.IsGabriel], F.IsUniform
· 使用定理 `Order.PFilter.ext`：ext (h : (s : Set P) = t) : s = t
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `IdealFilter.IsGabriel.gabriel_closed`：∀ {A : Type u_1} {inst : Ring A} {
F : IdealFilter A} [self : F.IsGabriel] (I : Ideal A),   (∃ J ∈ F, ∀ x ∈ J, Subm
odule.colon I {x} ∈ F) → I…
· 使用定理 `Order.PFilter.mem_of_le`：mem_of_le {F : PFilter P} : x <= y -> x in F ->
 y in F
· 使用引理 `IdealFilter.isTorsionQuot_self`：isTorsionQuot_self (F : IdealFilter A) (
I : Ideal A) : IsTorsionQuot F I I
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
Characterization of Gabriel filters via `IsUniform` and idempotence of
`gabrielComposition`.
-/
theorem isGabriel_iff (F : IdealFilter A) : F.IsGabriel ↔ F.IsUniform ∧ F • F = F := by
  constructor
  · intro hF
    refine ⟨hF.toIsUniform, ?_⟩
    ext I
    constructor <;> intro hI
    · rcases hI with ⟨J, hJ, htors⟩
      refine hF.gabriel_closed I ⟨J, hJ, fun x hx ↦ ?_⟩
      rcases htors x hx with ⟨K, hK, hincl⟩
      exact Order.PFilter.mem_of_le hincl hK
    · exact ⟨I, hI, isTorsionQuot_self F I⟩
  · rintro ⟨h₁, h₂⟩
    refine { toIsUniform := h₁, gabriel_closed := ?_ }
    rintro I ⟨J, hJ, hcolon⟩
    exact h₂.le ⟨J, hJ, fun x hx ↦ ⟨I.colon {x}, hcolon x hx, by simp⟩⟩

end IdealFilter

