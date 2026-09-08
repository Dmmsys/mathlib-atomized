/-
Copyright (c) 2022 Michael Blyth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Blyth
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Subspaces of Projective Space

In this file we define subspaces of a projective space, and show that the subspaces of a projective
space form a complete lattice under inclusion.

## Implementation Details

A subspace of a projective space ℙ K V is defined to be a structure consisting of a subset of
ℙ K V such that if two nonzero vectors in V determine points in ℙ K V which are in the subset, and
the sum of the two vectors is nonzero, then the point determined by the sum of the two vectors is
also in the subset.

## Results

- There is a Galois insertion between the subsets of points of a projective space
  and the subspaces of the projective space, which is given by taking the span of the set of points.
- The subspaces of a projective space form a complete lattice under inclusion.
- There is a one-to-one order-preserving correspondence between subspaces of a
  projective space and the submodules of the underlying vector space.
-/

@[expose] public section


variable (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V]

namespace Projectivization

open scoped LinearAlgebra.Projectivization

/-- A subspace of a projective space is a structure consisting of a set of points such that:
If two nonzero vectors determine points which are in the set, and the sum of the two vectors is
nonzero, then the point determined by the sum is also in the set. -/
@[ext]
/-
**Projectivization.Subspace** 是 Mathlib 中的一个归纳类型，位于命名空间 `Projectivization`。
形式化陈述：(K : Type u_1) → (V : Type u_2) → [inst : DivisionRing K] → [inst_1 : AddC
ommGroup V] → [_root_.Module K V] → Type u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subspace of a projective space is a structure consisting of a set of points su
ch that:
If two nonzero vectors determine points which are in the set, and the sum of the
 two vectors is
nonzero, then the point determined by the sum is also in the set.
-/
structure Subspace where
  /-- The set of points. -/
  carrier : Set (ℙ K V)
  /-- The addition rule. -/
  mem_add' (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v + w ≠ 0) :
    mk K v hv ∈ carrier → mk K w hw ∈ carrier → mk K (v + w) hvw ∈ carrier

namespace Subspace

variable {K V}

/-
**Projectivization.Subspace.** 是 Mathlib 中的一个实例，位于命名空间 `Projectivization.Subspac
e`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (Subspace K V) (ℙ K V) where
  coe := carrier
  coe_injective A B := by
    cases A
    cases B
    simp
/-
**Projectivization.Subspace.** 是 Mathlib 中的一个实例，位于命名空间 `Projectivization.Subspac
e`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (Subspace K V) := .ofSetLike (Subspace K V) (ℙ K V)

@[simp]
/-
**Projectivization.Subspace.mem_carrier_iff** 是 Mathlib 中的一个定理，位于命名空间 `Projectiv
ization.Subspace`。
形式化陈述：mem_carrier_iff (A : Subspace K V) (x : ℙ K V) : x in A.carrier ↔ x in A
参数：A : Subspace K V；x : ℙ K V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.refl`：∀ (a : Prop), a ↔ a
-/
theorem mem_carrier_iff (A : Subspace K V) (x : ℙ K V) : x ∈ A.carrier ↔ x ∈ A :=
  Iff.refl _
/-
**Projectivization.Subspace.mem_add** 是 Mathlib 中的一个定理，位于命名空间 `Projectivization.
Subspace`。
形式化陈述：mem_add (T : Subspace K V) (v w : V) (hv : v != 0) (hw : w != 0) (hvw : v 
+ w != 0) : Projectivization.mk K v hv in T -> Projectivization.mk K w hw in T -
> Projectivization.mk K (v + w) hvw in T
参数：T : Subspace K V；v w : V；hv : v != 0；hw : w != 0；hvw : v + w != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Projectivization.Subspace.mem_add'`：∀ {K : Type u_1} {V : Type u_2} [ins
t : DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   (se
lf : Projectivization.Su…
-/
theorem mem_add (T : Subspace K V) (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v + w ≠ 0) :
    Projectivization.mk K v hv ∈ T →
      Projectivization.mk K w hw ∈ T → Projectivization.mk K (v + w) hvw ∈ T :=
  T.mem_add' v w hv hw hvw

/-- The span of a set of points in a projective space is defined inductively to be the set of points
which contains the original set, and contains all points determined by the (nonzero) sum of two
nonzero vectors, each of which determine points in the span. -/
/-
**Projectivization.Subspace.spanCarrier** 是 Mathlib 中的一个归纳类型，位于命名空间 `Projectiviz
ation.Subspace`。
形式化陈述：{K : Type u_1} →   {V : Type u_2} →     [inst : DivisionRing K] →       [i
nst_1 : AddCommGroup V] → [inst_2 : _root_.Module K V] → Set (Projectivization K
 V) → Set (Projectivization K V)
参数：Projectivization K V；Projectivization K V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The span of a set of points in a projective space is defined inductively to be t
he set of points
which contains the original set, and contains all points determined by the (nonz
ero) sum of two
nonzero vectors, each of which determine points in the span.
-/
inductive spanCarrier (S : Set (ℙ K V)) : Set (ℙ K V)
  | of (x : ℙ K V) (hx : x ∈ S) : spanCarrier S x
  | mem_add (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v + w ≠ 0) :
      spanCarrier S (Projectivization.mk K v hv) →
      spanCarrier S (Projectivization.mk K w hw) → spanCarrier S (Projectivization.mk K (v + w) hvw)

/-- The span of a set of points in projective space is a subspace. -/
/-
**Projectivization.Subspace.span** 是 Mathlib 中的一个定义，位于命名空间 `Projectivization.Sub
space`。
形式化陈述：span (S : Set (ℙ K V)) : Subspace K V where carrier
参数：S : Set (ℙ K V)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The span of a set of points in projective space is a subspace.
-/
def span (S : Set (ℙ K V)) : Subspace K V where
  carrier := spanCarrier S
  mem_add' v w hv hw hvw := spanCarrier.mem_add v w hv hw hvw

/-- The span of a set of points contains the set of points. -/
/-
**Projectivization.Subspace.subset_span** 是 Mathlib 中的一个定理，位于命名空间 `Projectivizat
ion.Subspace`。
形式化陈述：subset_span (S : Set (ℙ K V)) : S subseteq span S
参数：S : Set (ℙ K V)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The span of a set of points contains the set of points.
-/
theorem subset_span (S : Set (ℙ K V)) : S ⊆ span S := fun _x hx => spanCarrier.of _ hx

/-- The span of a set of points is a Galois insertion between sets of points of a projective space
and subspaces of the projective space. -/
/-
**Projectivization.Subspace.gi** 是 Mathlib 中的一个定义，位于命名空间 `Projectivization.Subsp
ace`。
形式化陈述：gi : GaloisInsertion (span : Set (ℙ K V) -> Subspace K V) SetLike.coe wher
e choice S _hS
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The span of a set of points is a Galois insertion between sets of points of a pr
ojective space
and subspaces of the projective space.
-/
def gi : GaloisInsertion (span : Set (ℙ K V) → Subspace K V) SetLike.coe where
  choice S _hS := span S
  gc A B :=
    ⟨fun h => le_trans (subset_span _) h, by
      intro h x hx
      induction hx with
      | of => apply h; assumption
      | mem_add => apply B.mem_add; assumption'⟩
  le_l_u _ := subset_span _
  choice_eq _ _ := rfl

/-- The span of a subspace is the subspace. -/
@[simp]
/-
**Projectivization.Subspace.span_coe** 是 Mathlib 中的一个定理，位于命名空间 `Projectivization
.Subspace`。
形式化陈述：span_coe (W : Subspace K V) : span ↑W = W
参数：W : Subspace K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_u_eq`：l_u_eq [Preorder α] [PartialOrder β] (gi : Galoi
sInsertion l u) (b : β) : l (u b) = b

--- 原说明 ---
The span of a subspace is the subspace.
-/
theorem span_coe (W : Subspace K V) : span ↑W = W :=
  GaloisInsertion.l_u_eq gi W

/-- The infimum of two subspaces exists. -/
/-
**Projectivization.Subspace.instInf** 是 Mathlib 中的一个实例，位于命名空间 `Projectivization.
Subspace`。
形式化陈述：instInf : Min (Subspace K V)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The infimum of two subspaces exists.
-/
instance instInf : Min (Subspace K V) :=
  ⟨fun A B =>
    ⟨A ⊓ B, fun _v _w hv hw _hvw h1 h2 =>
      ⟨A.mem_add _ _ hv hw _ h1.1 h2.1, B.mem_add _ _ hv hw _ h1.2 h2.2⟩⟩⟩

/-- Infimums of arbitrary collections of subspaces exist. -/
/-
**Projectivization.Subspace.instInfSet** 是 Mathlib 中的一个实例，位于命名空间 `Projectivizati
on.Subspace`。
形式化陈述：instInfSet : InfSet (Subspace K V)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Infimums of arbitrary collections of subspaces exist.
-/
instance instInfSet : InfSet (Subspace K V) :=
  ⟨fun A =>
    ⟨sInf (SetLike.coe '' A), fun v w hv hw hvw h1 h2 t => by
      rintro ⟨s, hs, rfl⟩
      exact s.mem_add v w hv hw _ (h1 s ⟨s, hs, rfl⟩) (h2 s ⟨s, hs, rfl⟩)⟩⟩

/-- The subspaces of a projective space form a complete lattice. -/
/-
**Projectivization.Subspace.** 是 Mathlib 中的一个实例，位于命名空间 `Projectivization.Subspac
e`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subspaces of a projective space form a complete lattice.
-/
instance : CompleteLattice (Subspace K V) :=
  { __ := completeLatticeOfInf (Subspace K V)
      (by
        refine fun s => ⟨fun a ha x hx => hx _ ⟨a, ha, rfl⟩, fun a ha x hx E => ?_⟩
        rintro ⟨E, hE, rfl⟩
        exact ha hE hx)
    inf_le_left := fun A B _ hx => (@inf_le_left _ _ A B) hx
    inf_le_right := fun A B _ hx => (@inf_le_right _ _ A B) hx
    le_inf := fun _ _ _ h1 h2 _ hx => (le_inf h1 h2) hx }
/-
**Projectivization.Subspace.subspaceInhabited** 是 Mathlib 中的一个实例，位于命名空间 `Project
ivization.Subspace`。
形式化陈述：subspaceInhabited : Inhabited (Subspace K V) where default
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance subspaceInhabited : Inhabited (Subspace K V) where default := ⊤

/-- The span of the empty set is the bottom of the lattice of subspaces. -/
@[simp]
/-
**Projectivization.Subspace.span_empty** 是 Mathlib 中的一个定理，位于命名空间 `Projectivizati
on.Subspace`。
形式化陈述：span_empty : span (∅ : Set (ℙ K V)) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…

--- 原说明 ---
The span of the empty set is the bottom of the lattice of subspaces.
-/
theorem span_empty : span (∅ : Set (ℙ K V)) = ⊥ := gi.gc.l_bot

/-- The span of the entire projective space is the top of the lattice of subspaces. -/
@[simp]
/-
**Projectivization.Subspace.span_univ** 是 Mathlib 中的一个定理，位于命名空间 `Projectivizatio
n.Subspace`。
形式化陈述：span_univ : span (Set.univ : Set (ℙ K V)) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Projectivization.Subspace.subset_span`：subset_span (S : Set (ℙ K V)) : S
 subseteq span S
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
The span of the entire projective space is the top of the lattice of subspaces.
-/
theorem span_univ : span (Set.univ : Set (ℙ K V)) = ⊤ := by
  rw [eq_top_iff, SetLike.le_def]
  intro x _hx
  exact subset_span _ (Set.mem_univ x)

/-- The span of a set of points is contained in a subspace if and only if the set of points is
contained in the subspace. -/
/-
**Projectivization.Subspace.span_le_subspace_iff** 是 Mathlib 中的一个定理，位于命名空间 `Proj
ectivization.Subspace`。
形式化陈述：span_le_subspace_iff {S : Set (ℙ K V)} {W : Subspace K V} : span S <= W ↔ 
S subseteq W
参数：ℙ K V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…

--- 原说明 ---
The span of a set of points is contained in a subspace if and only if the set of
 points is
contained in the subspace.
-/
theorem span_le_subspace_iff {S : Set (ℙ K V)} {W : Subspace K V} : span S ≤ W ↔ S ⊆ W :=
  gi.gc S W

/-- If a set of points is a subset of another set of points, then its span will be contained in the
span of that set. -/
@[gcongr, mono]
/-
**Projectivization.Subspace.monotone_span** 是 Mathlib 中的一个定理，位于命名空间 `Projectiviz
ation.Subspace`。
形式化陈述：monotone_span : Monotone (span : Set (ℙ K V) -> Subspace K V)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…

--- 原说明 ---
If a set of points is a subset of another set of points, then its span will be c
ontained in the
span of that set.
-/
theorem monotone_span : Monotone (span : Set (ℙ K V) → Subspace K V) :=
  gi.gc.monotone_l

@[gcongr]
/-
**Projectivization.Subspace.span_le_span** 是 Mathlib 中的一个引理，位于命名空间 `Projectiviza
tion.Subspace`。
形式化陈述：span_le_span {s t : Set (ℙ K V)} (hst : s subseteq t) : span s <= span t
参数：ℙ K V；hst : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Projectivization.Subspace.monotone_span`：monotone_span : Monotone (span 
: Set (ℙ K V) -> Subspace K V)
-/
lemma span_le_span {s t : Set (ℙ K V)} (hst : s ⊆ t) : span s ≤ span t := monotone_span hst
/-
**Projectivization.Subspace.subset_span_trans** 是 Mathlib 中的一个定理，位于命名空间 `Project
ivization.Subspace`。
形式化陈述：subset_span_trans {S T U : Set (ℙ K V)} (hST : S subseteq span T) (hTU : T
 subseteq span U) : S subseteq span U
参数：ℙ K V；hST : S subseteq span T；hTU : T subseteq span U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.le_u_l_trans`：le_u_l_trans {x y z : α} (hxy : x <= u (l
 y)) (hyz : y <= u (l z)) : x <= u (l z)
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem subset_span_trans {S T U : Set (ℙ K V)} (hST : S ⊆ span T) (hTU : T ⊆ span U) :
    S ⊆ span U :=
  gi.gc.le_u_l_trans hST hTU

/-- The supremum of two subspaces is equal to the span of their union. -/
/-
**Projectivization.Subspace.span_union** 是 Mathlib 中的一个定理，位于命名空间 `Projectivizati
on.Subspace`。
形式化陈述：span_union (S T : Set (ℙ K V)) : span (S union T) = span S ⊔ span T
参数：S T : Set (ℙ K V)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…

--- 原说明 ---
The supremum of two subspaces is equal to the span of their union.
-/
theorem span_union (S T : Set (ℙ K V)) : span (S ∪ T) = span S ⊔ span T :=
  (@gi K V _ _ _).gc.l_sup

/-- The supremum of a collection of subspaces is equal to the span of the union of the
collection. -/
/-
**Projectivization.Subspace.span_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Projectivizat
ion.Subspace`。
形式化陈述：span_iUnion {ι} (s : ι -> Set (ℙ K V)) : span (⋃ i, s i) = ⨆ i, span (s i)
参数：s : ι -> Set (ℙ K V)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…

--- 原说明 ---
The supremum of a collection of subspaces is equal to the span of the union of t
he
collection.
-/
theorem span_iUnion {ι} (s : ι → Set (ℙ K V)) : span (⋃ i, s i) = ⨆ i, span (s i) :=
  (@gi K V _ _ _).gc.l_iSup

/-- The supremum of a subspace and the span of a set of points is equal to the span of the union of
the subspace and the set of points. -/
/-
**Projectivization.Subspace.sup_span** 是 Mathlib 中的一个定理，位于命名空间 `Projectivization
.Subspace`。
形式化陈述：sup_span {S : Set (ℙ K V)} {W : Subspace K V} : W ⊔ span S = span (W union
 S)
参数：ℙ K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Projectivization.Subspace.span_union`：span_union (S T : Set (ℙ K V)) : s
pan (S union T) = span S ⊔ span T
· 使用定理 `Projectivization.Subspace.span_coe`：span_coe (W : Subspace K V) : span ↑
W = W

--- 原说明 ---
The supremum of a subspace and the span of a set of points is equal to the span 
of the union of
the subspace and the set of points.
-/
theorem sup_span {S : Set (ℙ K V)} {W : Subspace K V} : W ⊔ span S = span (W ∪ S) := by
  rw [span_union, span_coe]
/-
**Projectivization.Subspace.span_sup** 是 Mathlib 中的一个定理，位于命名空间 `Projectivization
.Subspace`。
形式化陈述：span_sup {S : Set (ℙ K V)} {W : Subspace K V} : span S ⊔ W = span (S union
 W)
参数：ℙ K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Projectivization.Subspace.span_union`：span_union (S T : Set (ℙ K V)) : s
pan (S union T) = span S ⊔ span T
· 使用定理 `Projectivization.Subspace.span_coe`：span_coe (W : Subspace K V) : span ↑
W = W
-/
theorem span_sup {S : Set (ℙ K V)} {W : Subspace K V} : span S ⊔ W = span (S ∪ W) := by
  rw [span_union, span_coe]

/-- A point in a projective space is contained in the span of a set of points if and only if the
point is contained in all subspaces of the projective space which contain the set of points. -/
/-
**Projectivization.Subspace.mem_span** 是 Mathlib 中的一个定理，位于命名空间 `Projectivization
.Subspace`。
形式化陈述：mem_span {S : Set (ℙ K V)} (u : ℙ K V) : u in span S ↔ forall W : Subspace
 K V, S subseteq W -> u in W
参数：ℙ K V；u : ℙ K V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
A point in a projective space is contained in the span of a set of points if and
 only if the
point is contained in all subspaces of the projective space which contain the se
t of points.
-/
theorem mem_span {S : Set (ℙ K V)} (u : ℙ K V) :
    u ∈ span S ↔ ∀ W : Subspace K V, S ⊆ W → u ∈ W := by
  simp_rw [← span_le_subspace_iff]
  exact ⟨fun hu W hW => hW hu, fun W => W (span S) (le_refl _)⟩

/-- The span of a set of points in a projective space is equal to the infimum of the collection of
subspaces which contain the set. -/
/-
**Projectivization.Subspace.span_eq_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Projectiviza
tion.Subspace`。
形式化陈述：span_eq_sInf {S : Set (ℙ K V)} : span S = sInf { W : Subspace K V| S subse
teq W }
参数：ℙ K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Projectivization.Subspace.ext`：∀ {K : Type u_1} {V : Type u_2} {inst : D
ivisionRing K} {inst_1 : AddCommGroup V} {inst_2 : _root_.Module K V}   {x y : P
rojectivization.Sub…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Projectivization.Subspace.mem_span`：mem_span {S : Set (ℙ K V)} (u : ℙ K 
V) : u in span S ↔ forall W : Subspace K V, S subseteq W -> u in W
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a

--- 原说明 ---
The span of a set of points in a projective space is equal to the infimum of the
 collection of
subspaces which contain the set.
-/
theorem span_eq_sInf {S : Set (ℙ K V)} : span S = sInf { W : Subspace K V| S ⊆ W } := by
  ext x
  simp_rw [mem_carrier_iff, mem_span x]
  refine ⟨fun hx => ?_, fun hx W hW => ?_⟩
  · rintro W ⟨T, hT, rfl⟩
    exact hx T hT
  · exact (@sInf_le _ _ { W : Subspace K V | S ⊆ ↑W } W hW) hx

/-- If a set of points in projective space is contained in a subspace, and that subspace is
contained in the span of the set of points, then the span of the set of points is equal to
the subspace. -/
/-
**Projectivization.Subspace.span_eq_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Projectiviz
ation.Subspace`。
形式化陈述：span_eq_of_le {S : Set (ℙ K V)} {W : Subspace K V} (hS : S subseteq W) (hW
 : W <= span S) : span S = W
参数：ℙ K V；hS : S subseteq W；hW : W <= span S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Projectivization.Subspace.span_le_subspace_iff`：span_le_subspace_iff {S 
: Set (ℙ K V)} {W : Subspace K V} : span S <= W ↔ S subseteq W

--- 原说明 ---
If a set of points in projective space is contained in a subspace, and that subs
pace is
contained in the span of the set of points, then the span of the set of points i
s equal to
the subspace.
-/
theorem span_eq_of_le {S : Set (ℙ K V)} {W : Subspace K V} (hS : S ⊆ W) (hW : W ≤ span S) :
    span S = W :=
  le_antisymm (span_le_subspace_iff.mpr hS) hW

/-- The spans of two sets of points in a projective space are equal if and only if each set of
points is contained in the span of the other set. -/
/-
**Projectivization.Subspace.span_eq_span_iff** 是 Mathlib 中的一个定理，位于命名空间 `Projecti
vization.Subspace`。
形式化陈述：span_eq_span_iff {S T : Set (ℙ K V)} : span S = span T ↔ S subseteq span T
 ∧ T subseteq span S
参数：ℙ K V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Projectivization.Subspace.subset_span`：subset_span (S : Set (ℙ K V)) : S
 subseteq span S
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Projectivization.Subspace.span_le_subspace_iff`：span_le_subspace_iff {S 
: Set (ℙ K V)} {W : Subspace K V} : span S <= W ↔ S subseteq W
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
The spans of two sets of points in a projective space are equal if and only if e
ach set of
points is contained in the span of the other set.
-/
theorem span_eq_span_iff {S T : Set (ℙ K V)} : span S = span T ↔ S ⊆ span T ∧ T ⊆ span S :=
  ⟨fun h => ⟨h ▸ subset_span S, h.symm ▸ subset_span T⟩, fun h =>
    le_antisymm (span_le_subspace_iff.2 h.1) (span_le_subspace_iff.2 h.2)⟩

/-- The submodule corresponding to a projective subspace `s`, consisting of the representatives of
points in `s` together with zero. This is the inverse of `Submodule.projectivization`. -/
/-
**Projectivization.Subspace.submodule** 是 Mathlib 中的一个定义，位于命名空间 `Projectivizatio
n.Subspace`。
形式化陈述：submodule : Projectivization.Subspace K V ≃o Submodule K V where toFun s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The submodule corresponding to a projective subspace `s`, consisting of the repr
esentatives of
points in `s` together with zero. This is the inverse of `Submodule.projectiviza
tion`.
-/
def submodule : Projectivization.Subspace K V ≃o Submodule K V where
  toFun s :=
  { carrier := {x | (h : x ≠ 0) → Projectivization.mk K x h ∈ s.carrier}
    add_mem' {x y} hx₁ hy₁ := by
      rcases eq_or_ne x 0 with rfl | hx₂
      · rwa [zero_add]
      rcases eq_or_ne y 0 with rfl | hy₂
      · rwa [add_zero]
      intro hxy
      exact s.mem_add _ _ hx₂ hy₂ hxy (hx₁ hx₂) (hy₁ hy₂)
    zero_mem' h := h.irrefl.elim
    smul_mem' c x h₁ h₂ := by
      convert! h₁ (right_ne_zero_of_smul h₂) using 1
      rw [Projectivization.mk_eq_mk_iff']
      exact ⟨c, rfl⟩ }
  invFun s :=
  { carrier := Set.ofPred <| Projectivization.lift (↑· ∈ s) <| by
      rintro ⟨-, h⟩ ⟨y, -⟩ c rfl
      exact Iff.eq <| s.smul_mem_iff <| left_ne_zero_of_smul h
    mem_add' _ _ _ _ _ h₁ h₂ := s.add_mem h₁ h₂ }
  left_inv s := by
    ext ⟨x, hx⟩
    exact ⟨fun h => h hx, fun h _ => h⟩
  right_inv s := by
    ext x
    suffices x = 0 → x ∈ s by
      simpa [imp_iff_not_or]
    rintro rfl
    exact s.zero_mem
  map_rel_iff'.mp h₁ := Projectivization.ind fun _ hx h₂ => h₁ (fun _ => h₂) hx
  map_rel_iff'.mpr h₁ _ h₂ hx := h₁ <| h₂ hx

@[simp]
/-
**Projectivization.Subspace.mem_submodule_iff** 是 Mathlib 中的一个定理，位于命名空间 `Project
ivization.Subspace`。
形式化陈述：mem_submodule_iff (s : Projectivization.Subspace K V) {v : V} (hv : v != 0
) : v in submodule s ↔ Projectivization.mk K v hv in s
参数：s : Projectivization.Subspace K V；hv : v != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_submodule_iff (s : Projectivization.Subspace K V) {v : V} (hv : v ≠ 0) :
    v ∈ submodule s ↔ Projectivization.mk K v hv ∈ s :=
  ⟨fun h => h hv, fun h _ => h⟩

@[simp]
/-
**Projectivization.Subspace.bot_coe** 是 Mathlib 中的一个引理，位于命名空间 `Projectivization.
Subspace`。
形式化陈述：bot_coe : ((⊥ : Subspace K V) : Set (Projectivization K V)) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `Projectivization.ind`：ind {P : ℙ K V -> Prop} (h : forall (v : V) (h : v
 != 0), P (mk K v h)) : forall p, P p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Projectivization.Subspace.mem_submodule_iff`：mem_submodule_iff (s : Proj
ectivization.Subspace K V) {v : V} (hv : v != 0) : v in submodule s ↔ Projectivi
zation.mk K v hv in s
· 使用定理 `OrderIso.map_bot`：OrderIso.map_bot [LE α] [PartialOrder β] [OrderBot α] 
[OrderBot β] (f : α ≃o β) : f ⊥ = ⊥
· 使用定理 `Submodule.mem_bot`：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
-/
lemma bot_coe : ((⊥ : Subspace K V) : Set (Projectivization K V)) = ∅ := by
  ext x
  simp only [SetLike.mem_coe, Set.mem_empty_iff_false, iff_false]
  induction x using ind with | h v hv =>
  rwa [← Subspace.mem_submodule_iff _ hv, Subspace.submodule.map_bot, Submodule.mem_bot]

end Subspace

end Projectivization

namespace Submodule

open scoped LinearAlgebra.Projectivization

variable {K V}

/-- The projective subspace corresponding to a submodule `s`, consisting of the one-dimensional
subspaces of `s`. This is the inverse of `Projectivization.Subspace.submodule`. -/
/-
**Submodule.projectivization** 是 Mathlib 中的一个缩写定义，位于命名空间 `Submodule`。
形式化陈述：projectivization : Submodule K V ≃o Projectivization.Subspace K V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projective subspace corresponding to a submodule `s`, consisting of the one-
dimensional
subspaces of `s`. This is the inverse of `Projectivization.Subspace.submodule`.
-/
abbrev projectivization : Submodule K V ≃o Projectivization.Subspace K V :=
  Projectivization.Subspace.submodule.symm

@[simp]
/-
**Submodule.mk_mem_projectivization_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mk_mem_projectivization_iff (s : Submodule K V) {v : V} (hv : v != 0) : Pr
ojectivization.mk K v hv in s.projectivization ↔ v in s
参数：s : Submodule K V；hv : v != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_mem_projectivization_iff (s : Submodule K V) {v : V} (hv : v ≠ 0) :
    Projectivization.mk K v hv ∈ s.projectivization ↔ v ∈ s := Iff.rfl
/-
**Submodule.mem_projectivization_iff_submodule_le** 是 Mathlib 中的一个定理，位于命名空间 `Sub
module`。
形式化陈述：mem_projectivization_iff_submodule_le (s : Submodule K V) (x : ℙ K V) : x 
in s.projectivization ↔ x.submodule <= s
参数：s : Submodule K V；x : ℙ K V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Projectivization.ind`：ind {P : ℙ K V -> Prop} (h : forall (v : V) (h : v
 != 0), P (mk K v h)) : forall p, P p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mk_mem_projectivization_iff`：mk_mem_projectivization_iff (s : 
Submodule K V) {v : V} (hv : v != 0) : Projectivization.mk K v hv in s.projectiv
ization ↔ v in s
· 使用定理 `Projectivization.submodule_mk`：submodule_mk (v : V) (hv : v != 0) : (mk 
K v hv).submodule = K ∙ v
· 使用定理 `Submodule.span_singleton_le_iff_mem`：span_singleton_le_iff_mem (m : M) (
p : Submodule R M) : R ∙ m <= p ↔ m in p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mem_projectivization_iff_submodule_le (s : Submodule K V) (x : ℙ K V) :
    x ∈ s.projectivization ↔ x.submodule ≤ s := by
  cases x
  rw [mk_mem_projectivization_iff, Projectivization.submodule_mk,
    Submodule.span_singleton_le_iff_mem]

end Submodule

