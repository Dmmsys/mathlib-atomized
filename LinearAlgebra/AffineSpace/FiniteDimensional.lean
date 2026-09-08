/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.AffineSpace.Basis
public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Centroid
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty

import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.Finiteness.Prod

/-!
# Finite-dimensional subspaces of affine spaces.

This file provides a few results relating to finite-dimensional
subspaces of affine spaces.

## Main definitions

* `Collinear` defines collinear sets of points as those that span a
  subspace of dimension at most 1.

-/

@[expose] public section


noncomputable section

open Affine
open scoped Finset

section AffineSpace'

variable (k : Type*) {V : Type*} {P : Type*}
variable {ι : Type*}

open AffineSubspace Module

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AffineSpace V P]

/-- The `vectorSpan` of a finite set is finite-dimensional. -/
/-
**finiteDimensional_vectorSpan_of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finiteDimensional_vectorSpan_of_finite {s : Set P} (h : Set.Finite s) : Fi
niteDimensional k (vectorSpan k s)
参数：h : Set.Finite s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteDimensional.span_of_finite`：span_of_finite {A : Set V} (hA : Set.F
inite A) : FiniteDimensional K (Submodule.span K A)
· 使用定理 `Set.Finite.vsub`：∀ {α : Type u_2} {β : Type u_3} [inst : VSub α β] {s t 
: Set β}, s.Finite → t.Finite → (s -ᵥ t).Finite

--- 原说明 ---
The `vectorSpan` of a finite set is finite-dimensional.
-/
theorem finiteDimensional_vectorSpan_of_finite {s : Set P} (h : Set.Finite s) :
    FiniteDimensional k (vectorSpan k s) :=
  .span_of_finite k <| h.vsub h

/-- The vector span of a singleton is finite-dimensional. -/
/-
**finiteDimensional_vectorSpan_singleton** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：finiteDimensional_vectorSpan_singleton (p : P) : FiniteDimensional k (vect
orSpan k {p})
参数：p : P。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `finiteDimensional_vectorSpan_of_finite`：finiteDimensional_vectorSpan_of_
finite {s : Set P} (h : Set.Finite s) : FiniteDimensional k (vectorSpan k s)
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite

--- 原说明 ---
The vector span of a singleton is finite-dimensional.
-/
instance finiteDimensional_vectorSpan_singleton (p : P) :
    FiniteDimensional k (vectorSpan k {p}) :=
  finiteDimensional_vectorSpan_of_finite _ (Set.finite_singleton p)

/-- The `vectorSpan` of a family indexed by a `Fintype` is
finite-dimensional. -/
/-
**finiteDimensional_vectorSpan_range** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：finiteDimensional_vectorSpan_range [Finite ι] (p : ι -> P) : FiniteDimensi
onal k (vectorSpan k (Set.range p))
参数：p : ι -> P。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `finiteDimensional_vectorSpan_of_finite`：finiteDimensional_vectorSpan_of_
finite {s : Set P} (h : Set.Finite s) : FiniteDimensional k (vectorSpan k s)
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e

--- 原说明 ---
The `vectorSpan` of a family indexed by a `Fintype` is
finite-dimensional.
-/
instance finiteDimensional_vectorSpan_range [Finite ι] (p : ι → P) :
    FiniteDimensional k (vectorSpan k (Set.range p)) :=
  finiteDimensional_vectorSpan_of_finite k (Set.finite_range _)

/-- The `vectorSpan` of a subset of a family indexed by a `Fintype`
is finite-dimensional. -/
/-
**finiteDimensional_vectorSpan_image_of_finite** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：finiteDimensional_vectorSpan_image_of_finite [Finite ι] (p : ι -> P) (s : 
Set ι) : FiniteDimensional k (vectorSpan k (p '' s))
参数：p : ι -> P；s : Set ι。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `finiteDimensional_vectorSpan_of_finite`：finiteDimensional_vectorSpan_of_
finite {s : Set P} (h : Set.Finite s) : FiniteDimensional k (vectorSpan k s)
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite

--- 原说明 ---
The `vectorSpan` of a subset of a family indexed by a `Fintype`
is finite-dimensional.
-/
instance finiteDimensional_vectorSpan_image_of_finite [Finite ι] (p : ι → P) (s : Set ι) :
    FiniteDimensional k (vectorSpan k (p '' s)) :=
  finiteDimensional_vectorSpan_of_finite k (Set.toFinite _)

/-- The direction of the affine span of a finite set is
finite-dimensional. -/
/-
**finiteDimensional_direction_affineSpan_of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finiteDimensional_direction_affineSpan_of_finite {s : Set P} (h : Set.Fini
te s) : FiniteDimensional k (affineSpan k s).direction
参数：h : Set.Finite s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finiteDimensional_vectorSpan_of_finite`：finiteDimensional_vectorSpan_of_
finite {s : Set P} (h : Set.Finite s) : FiniteDimensional k (vectorSpan k s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s

--- 原说明 ---
The direction of the affine span of a finite set is
finite-dimensional.
-/
theorem finiteDimensional_direction_affineSpan_of_finite {s : Set P} (h : Set.Finite s) :
    FiniteDimensional k (affineSpan k s).direction :=
  (direction_affineSpan k s).symm ▸ finiteDimensional_vectorSpan_of_finite k h

/-- The direction of the affine span of a singleton is finite-dimensional. -/
/-
**finiteDimensional_direction_affineSpan_singleton** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：finiteDimensional_direction_affineSpan_singleton (p : P) : FiniteDimension
al k (affineSpan k {p}).direction
参数：p : P。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s

--- 原说明 ---
The direction of the affine span of a singleton is finite-dimensional.
-/
instance finiteDimensional_direction_affineSpan_singleton (p : P) :
    FiniteDimensional k (affineSpan k {p}).direction := by
  rw [direction_affineSpan]
  infer_instance

/-- The direction of the affine span of a family indexed by a
`Fintype` is finite-dimensional. -/
/-
**finiteDimensional_direction_affineSpan_range** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：finiteDimensional_direction_affineSpan_range [Finite ι] (p : ι -> P) : Fin
iteDimensional k (affineSpan k (Set.range p)).direction
参数：p : ι -> P。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `finiteDimensional_direction_affineSpan_of_finite`：finiteDimensional_dire
ction_affineSpan_of_finite {s : Set P} (h : Set.Finite s) : FiniteDimensional k 
(affineSpan k s).direction
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e

--- 原说明 ---
The direction of the affine span of a family indexed by a
`Fintype` is finite-dimensional.
-/
instance finiteDimensional_direction_affineSpan_range [Finite ι] (p : ι → P) :
    FiniteDimensional k (affineSpan k (Set.range p)).direction :=
  finiteDimensional_direction_affineSpan_of_finite k (Set.finite_range _)

/-- The direction of the affine span of a subset of a family indexed
by a `Fintype` is finite-dimensional. -/
/-
**finiteDimensional_direction_affineSpan_image_of_finite** 是 Mathlib 中的一个实例，位于命名
空间 ``。
形式化陈述：finiteDimensional_direction_affineSpan_image_of_finite [Finite ι] (p : ι -
> P) (s : Set ι) : FiniteDimensional k (affineSpan k (p '' s)).direction
参数：p : ι -> P；s : Set ι。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `finiteDimensional_direction_affineSpan_of_finite`：finiteDimensional_dire
ction_affineSpan_of_finite {s : Set P} (h : Set.Finite s) : FiniteDimensional k 
(affineSpan k s).direction
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite

--- 原说明 ---
The direction of the affine span of a subset of a family indexed
by a `Fintype` is finite-dimensional.
-/
instance finiteDimensional_direction_affineSpan_image_of_finite [Finite ι] (p : ι → P) (s : Set ι) :
    FiniteDimensional k (affineSpan k (p '' s)).direction :=
  finiteDimensional_direction_affineSpan_of_finite k (Set.toFinite _)

/-- An affine-independent family of points in a finite-dimensional affine space is finite. -/
/-
**finite_of_fin_dim_affineIndependent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finite_of_fin_dim_affineIndependent [FiniteDimensional k V] {p : ι -> P} (
hi : AffineIndependent k p) : Finite ι
参数：hi : AffineIndependent k p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsNoetherian.iff_fg`：iff_fg : IsNoetherian K V ↔ Module.Finite K V
· 使用定理 `Set.Finite.finite_of_compl`：∀ {α : Type u} {s : Set α}, s.Finite → sᶜ.Fi
nite → Finite α
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.finite_coe_iff`：finite_coe_iff {s : Set α} : Finite s ↔ s.Finite
· 使用定理 `LinearIndependent.finite_of_isNoetherian`：LinearIndependent.finite_of_is
Noetherian [Nontrivial R] {ι} {v : ι -> M} (hv : LinearIndependent R v) : Finite
 ι
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `affineIndependent_iff_linearIndependent_vsub`：affineIndependent_iff_line
arIndependent_vsub (p : ι -> P) (i1 : ι) : AffineIndependent k p ↔ LinearIndepen
dent k fun i : { x // x != i1 } =>…

--- 原说明 ---
An affine-independent family of points in a finite-dimensional affine space is f
inite.
-/
theorem finite_of_fin_dim_affineIndependent [FiniteDimensional k V] {p : ι → P}
    (hi : AffineIndependent k p) : Finite ι := by
  nontriviality ι; inhabit ι
  rw [affineIndependent_iff_linearIndependent_vsub k p default] at hi
  let : IsNoetherian k V := IsNoetherian.iff_fg.2 inferInstance
  exact
    (Set.finite_singleton default).finite_of_compl (Set.finite_coe_iff.1 hi.finite_of_isNoetherian)

/-- An affine-independent subset of a finite-dimensional affine space is finite. -/
/-
**finite_set_of_fin_dim_affineIndependent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finite_set_of_fin_dim_affineIndependent [FiniteDimensional k V] {s : Set ι
} {f : s -> P} (hi : AffineIndependent k f) : s.Finite
参数：hi : AffineIndependent k f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `finite_of_fin_dim_affineIndependent`：finite_of_fin_dim_affineIndependent
 [FiniteDimensional k V] {p : ι -> P} (hi : AffineIndependent k p) : Finite ι

--- 原说明 ---
An affine-independent subset of a finite-dimensional affine space is finite.
-/
theorem finite_set_of_fin_dim_affineIndependent [FiniteDimensional k V] {s : Set ι} {f : s → P}
    (hi : AffineIndependent k f) : s.Finite :=
  @Set.toFinite _ s (finite_of_fin_dim_affineIndependent k hi)

variable {k}

/-- The supremum of two finite-dimensional affine subspaces is finite-dimensional. -/
/-
**AffineSubspace.finiteDimensional_sup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AffineSubspace.finiteDimensional_sup (s₁ s₂ : AffineSubspace k P) [FiniteD
imensional k s₁.direction] [FiniteDimensional k s₂.direction] : FiniteDimensiona
l k (s₁ ⊔ s₂).direction
参数：s₁ s₂ : AffineSubspace k P。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.eq_bot_or_nonempty`：eq_bot_or_nonempty (Q : AffineSubspac
e k P) : Q = ⊥ ∨ (Q : Set P).Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `bot_sup_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), ⊥ ⊔ a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sup_bot_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), a ⊔ ⊥ = a
· 使用定理 `AffineSubspace.direction_sup`：direction_sup {s₁ s₂ : AffineSubspace k P}
 {p₁ p₂ : P} (hp₁ : p₁ in s₁) (hp₂ : p₂ in s₂) : (s₁ ⊔ s₂).direction = s₁.direct
ion ⊔ s₂.direction…

--- 原说明 ---
The supremum of two finite-dimensional affine subspaces is finite-dimensional.
-/
instance AffineSubspace.finiteDimensional_sup (s₁ s₂ : AffineSubspace k P)
    [FiniteDimensional k s₁.direction] [FiniteDimensional k s₂.direction] :
    FiniteDimensional k (s₁ ⊔ s₂).direction := by
  rcases eq_bot_or_nonempty s₁ with rfl | ⟨p₁, hp₁⟩
  · rwa [bot_sup_eq]
  rcases eq_bot_or_nonempty s₂ with rfl | ⟨p₂, hp₂⟩
  · rwa [sup_bot_eq]
  rw [AffineSubspace.direction_sup hp₁ hp₂]
  infer_instance

/-- The image of a finite-dimensional affine subspace under an affine map is finite-dimensional. -/
/-
**finiteDimensional_direction_map** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：finiteDimensional_direction_map {V₂ P₂ : Type*} [AddCommGroup V₂] [Module 
k V₂] [AffineSpace V₂ P₂] (s : AffineSubspace k P) [FiniteDimensional k s.direct
ion] (f : P ->ᵃ[k] P₂) : FiniteDimensional k (s.map f).direction
参数：s : AffineSubspace k P；f : P ->ᵃ[k] P₂。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.map_direction`：map_direction (s : AffineSubspace k P₁) : 
(s.map f).direction = s.direction.map f.linear
· 使用定理 `FiniteDimensional.instSubtypeMemSubmoduleMap`：∀ (K : Type u) {V : Type v
} [inst : DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]
   {V₂ : Type v'} [inst_3 : AddCom…

--- 原说明 ---
The image of a finite-dimensional affine subspace under an affine map is finite-
dimensional.
-/
instance finiteDimensional_direction_map {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂]
    [AffineSpace V₂ P₂] (s : AffineSubspace k P) [FiniteDimensional k s.direction]
    (f : P →ᵃ[k] P₂) : FiniteDimensional k (s.map f).direction := by
  rw [map_direction]
  infer_instance

/-- The `vectorSpan` of a finite subset of an affinely independent
family has dimension one less than its cardinality. -/
/-
**AffineIndependent.finrank_vectorSpan_image_finset** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：AffineIndependent.finrank_vectorSpan_image_finset [DecidableEq P] {p : ι -
> P} (hi : AffineIndependent k p) {s : Finset ι} {n : Nat} (hc : #s = n + 1) : f
inrank k (vectorSpan k (s.image p : Set P)) = n
参数：hi : AffineIndependent k p；hc : #s = n + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIndependent.mono`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_3} [
inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [inst_3 
: AddTorsor …
· 使用定理 `AffineIndependent.range`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_3} 
[inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [inst_3
 : AddTorsor …
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_image_of_injective`：card_image_of_injective [DecidableEq β] 
(s : Finset α) (H : Injective f) : #(s.image f) = #s
· 使用定理 `AffineIndependent.injective`：∀ {k : Type u_1} {V : Type u_2} {P : Type u
_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [in
st_3 : AddTorsor …
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `vsub_left_injective`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] (p : P), Function.Injective fun x => x -ᵥ p
· 使用定理 `Finset.card_erase_of_mem`：card_erase_of_mem : a in s -> #(s.erase a) = #
s - 1
· 使用定理 `Nat.pred_eq_of_eq_succ`：∀ {m n : ℕ}, m = n.succ → m.pred = n
· 使用定理 `vectorSpan_eq_span_vsub_finset_right_ne`：vectorSpan_eq_span_vsub_finset_
right_ne [DecidableEq P] [DecidableEq V] {s : Finset P} {p : P} (hp : p in s) : 
vectorSpan k (s : Set P) = Su…
· 使用定理 `finrank_span_finset_eq_card`：finrank_span_finset_eq_card {s : Finset M} 
(hs : LinearIndepOn R id (s : Set M)) : finrank R (span R (s : Set M)) = s.card
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
The `vectorSpan` of a finite subset of an affinely independent
family has dimension one less than its cardinality.
-/
theorem AffineIndependent.finrank_vectorSpan_image_finset [DecidableEq P]
    {p : ι → P} (hi : AffineIndependent k p) {s : Finset ι} {n : ℕ} (hc : #s = n + 1) :
    finrank k (vectorSpan k (s.image p : Set P)) = n := by
  classical
  have hi' := hi.range.mono (Set.image_subset_range p ↑s)
  have hc' : #(s.image p) = n + 1 := by rwa [s.card_image_of_injective hi.injective]
  have hn : (s.image p).Nonempty := by simp [hc', ← Finset.card_pos]
  rcases hn with ⟨p₁, hp₁⟩
  have hp₁' : p₁ ∈ p '' s := by simpa using hp₁
  rw [affineIndependent_set_iff_linearIndependent_vsub k hp₁', ← Finset.coe_singleton,
    ← Finset.coe_image, ← Finset.coe_sdiff, Finset.sdiff_singleton_eq_erase, ← Finset.coe_image]
    at hi'
  have hc : #(((s.image p).erase p₁).image (· -ᵥ p₁)) = n := by
    rw [Finset.card_image_of_injective _ (vsub_left_injective _), Finset.card_erase_of_mem hp₁]
    exact Nat.pred_eq_of_eq_succ hc'
  rwa [vectorSpan_eq_span_vsub_finset_right_ne k hp₁, finrank_span_finset_eq_card, hc]

/-- The `vectorSpan` of a finite affinely independent family has
dimension one less than its cardinality. -/
/-
**AffineIndependent.finrank_vectorSpan** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineIndependent.finrank_vectorSpan [Fintype ι] {p : ι -> P} (hi : Affine
Independent k p) {n : Nat} (hc : Fintype.card ι = n + 1) : finrank k (vectorSpan
 k (Set.range p)) = n
参数：hi : AffineIndependent k p；hc : Fintype.card ι = n + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `AffineIndependent.finrank_vectorSpan_image_finset`：AffineIndependent.fin
rank_vectorSpan_image_finset [DecidableEq P] {p : ι -> P} (hi : AffineIndependen
t k p) {s : Finset ι} {n : Nat} (hc : #…
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α

--- 原说明 ---
The `vectorSpan` of a finite affinely independent family has
dimension one less than its cardinality.
-/
theorem AffineIndependent.finrank_vectorSpan [Fintype ι] {p : ι → P} (hi : AffineIndependent k p)
    {n : ℕ} (hc : Fintype.card ι = n + 1) : finrank k (vectorSpan k (Set.range p)) = n := by
  classical
  rw [← Finset.card_univ] at hc
  rw [← Set.image_univ, ← Finset.coe_univ, ← Finset.coe_image]
  exact hi.finrank_vectorSpan_image_finset hc

/-- The `vectorSpan` of a finite affinely independent family has dimension one less than its
cardinality. -/
/-
**AffineIndependent.finrank_vectorSpan_add_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AffineIndependent.finrank_vectorSpan_add_one [Fintype ι] [Nonempty ι] {p :
 ι -> P} (hi : AffineIndependent k p) : finrank k (vectorSpan k (Set.range p)) +
 1 = Fintype.card ι
参数：hi : AffineIndependent k p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineIndependent.finrank_vectorSpan`：AffineIndependent.finrank_vectorSp
an [Fintype ι] {p : ι -> P} (hi : AffineIndependent k p) {n : Nat} (hc : Fintype
.card ι = n + 1) : finrank…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Fintype.card_pos`：card_pos [h : Nonempty α] : 0 < card α

--- 原说明 ---
The `vectorSpan` of a finite affinely independent family has dimension one less 
than its
cardinality.
-/
lemma AffineIndependent.finrank_vectorSpan_add_one [Fintype ι] [Nonempty ι] {p : ι → P}
    (hi : AffineIndependent k p) : finrank k (vectorSpan k (Set.range p)) + 1 = Fintype.card ι := by
  rw [hi.finrank_vectorSpan (tsub_add_cancel_of_le _).symm, tsub_add_cancel_of_le] <;>
    exact Fintype.card_pos

/-- The `vectorSpan` of a finite affinely independent family whose
cardinality is one more than that of the finite-dimensional space is
`⊤`. -/
/-
**AffineIndependent.vectorSpan_eq_top_of_card_eq_finrank_add_one** 是 Mathlib 中的一
个定理，位于命名空间 ``。
形式化陈述：AffineIndependent.vectorSpan_eq_top_of_card_eq_finrank_add_one [FiniteDime
nsional k V] [Fintype ι] {p : ι -> P} (hi : AffineIndependent k p) (hc : Fintype
.card ι = finrank k V + 1) : vectorSpan k (Set.range p) = ⊤
参数：hi : AffineIndependent k p；hc : Fintype.card ι = finrank k V + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.eq_top_of_finrank_eq`：∀ {K : Type u} {V : Type v} [inst : Divi
sionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   [FiniteDime
nsional K V] {S : Su…
· 使用定理 `AffineIndependent.finrank_vectorSpan`：AffineIndependent.finrank_vectorSp
an [Fintype ι] {p : ι -> P} (hi : AffineIndependent k p) {n : Nat} (hc : Fintype
.card ι = n + 1) : finrank…

--- 原说明 ---
The `vectorSpan` of a finite affinely independent family whose
cardinality is one more than that of the finite-dimensional space is
`⊤`.
-/
theorem AffineIndependent.vectorSpan_eq_top_of_card_eq_finrank_add_one [FiniteDimensional k V]
    [Fintype ι] {p : ι → P} (hi : AffineIndependent k p) (hc : Fintype.card ι = finrank k V + 1) :
    vectorSpan k (Set.range p) = ⊤ :=
  Submodule.eq_top_of_finrank_eq <| hi.finrank_vectorSpan hc

variable (k)

/-- The `vectorSpan` of `n + 1` points in an indexed family has
dimension at most `n`. -/
/-
**finrank_vectorSpan_image_finset_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finrank_vectorSpan_image_finset_le [DecidableEq P] (p : ι -> P) (s : Finse
t ι) {n : Nat} (hc : #s = n + 1) : finrank k (vectorSpan k (s.image p : Set P)) 
<= n
参数：p : ι -> P；s : Finset ι；hc : #s = n + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.image_nonempty`：image_nonempty : (s.image f).Nonempty ↔ s.Nonempt
y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_pos`：∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempt
y
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `vectorSpan_eq_span_vsub_finset_right_ne`：vectorSpan_eq_span_vsub_finset_
right_ne [DecidableEq P] [DecidableEq V] {s : Finset P} {p : P} (hp : p in s) : 
vectorSpan k (s : Set P) = Su…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `finrank_span_finset_le_card`：finrank_span_finset_le_card (s : Finset M) 
: (s : Set M).finrank R <= s.card
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
· 使用定理 `Finset.card_image_of_injective`：card_image_of_injective [DecidableEq β] 
(s : Finset α) (H : Injective f) : #(s.image f) = #s
· 使用定理 `vsub_left_injective`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] (p : P), Function.Injective fun x => x -ᵥ p
· 使用定理 `Finset.card_erase_of_mem`：card_erase_of_mem : a in s -> #(s.erase a) = #
s - 1
· 使用定理 `tsub_le_iff_right`：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub 
α] {a b c : α} : a - b <= c ↔ a <= c + b
· 使用定理 `Finset.card_image_le`：card_image_le [DecidableEq β] : #(s.image f) <= #s

--- 原说明 ---
The `vectorSpan` of `n + 1` points in an indexed family has
dimension at most `n`.
-/
theorem finrank_vectorSpan_image_finset_le [DecidableEq P] (p : ι → P) (s : Finset ι) {n : ℕ}
    (hc : #s = n + 1) : finrank k (vectorSpan k (s.image p : Set P)) ≤ n := by
  classical
  have hn : (s.image p).Nonempty := by
    rw [Finset.image_nonempty, ← Finset.card_pos, hc]
    apply Nat.succ_pos
  rcases hn with ⟨p₁, hp₁⟩
  rw [vectorSpan_eq_span_vsub_finset_right_ne k hp₁]
  refine le_trans (finrank_span_finset_le_card (((s.image p).erase p₁).image fun p => p -ᵥ p₁)) ?_
  rw [Finset.card_image_of_injective _ (vsub_left_injective p₁), Finset.card_erase_of_mem hp₁,
    tsub_le_iff_right, ← hc]
  apply Finset.card_image_le

/-- The `vectorSpan` of an indexed family of `n + 1` points has
dimension at most `n`. -/
/-
**finrank_vectorSpan_range_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finrank_vectorSpan_range_le [Fintype ι] (p : ι -> P) {n : Nat} (hc : Finty
pe.card ι = n + 1) : finrank k (vectorSpan k (Set.range p)) <= n
参数：p : ι -> P；hc : Fintype.card ι = n + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `finrank_vectorSpan_image_finset_le`：finrank_vectorSpan_image_finset_le [
DecidableEq P] (p : ι -> P) (s : Finset ι) {n : Nat} (hc : #s = n + 1) : finrank
 k (vectorSpan k (s.imag…
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α

--- 原说明 ---
The `vectorSpan` of an indexed family of `n + 1` points has
dimension at most `n`.
-/
theorem finrank_vectorSpan_range_le [Fintype ι] (p : ι → P) {n : ℕ} (hc : Fintype.card ι = n + 1) :
    finrank k (vectorSpan k (Set.range p)) ≤ n := by
  classical
  rw [← Set.image_univ, ← Finset.coe_univ, ← Finset.coe_image]
  rw [← Finset.card_univ] at hc
  exact finrank_vectorSpan_image_finset_le _ _ _ hc

/-- The `vectorSpan` of an indexed family of `n + 1` points has dimension at most `n`. -/
/-
**finrank_vectorSpan_range_add_one_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：finrank_vectorSpan_range_add_one_le [Fintype ι] [Nonempty ι] (p : ι -> P) 
: finrank k (vectorSpan k (Set.range p)) + 1 <= Fintype.card ι
参数：p : ι -> P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_tsub_iff_right`：le_tsub_iff_right (h : a <= c) : b <= c - a ↔ b + a <
= c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.succ_le_iff`：∀ {m n : ℕ}, m.succ ≤ n ↔ m < n
· 使用定理 `Fintype.card_pos`：card_pos [h : Nonempty α] : 0 < card α
· 使用定理 `finrank_vectorSpan_range_le`：finrank_vectorSpan_range_le [Fintype ι] (p 
: ι -> P) {n : Nat} (hc : Fintype.card ι = n + 1) : finrank k (vectorSpan k (Set
.range p)) <= n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b

--- 原说明 ---
The `vectorSpan` of an indexed family of `n + 1` points has dimension at most `n
`.
-/
lemma finrank_vectorSpan_range_add_one_le [Fintype ι] [Nonempty ι] (p : ι → P) :
    finrank k (vectorSpan k (Set.range p)) + 1 ≤ Fintype.card ι :=
  (le_tsub_iff_right <| Nat.succ_le_iff.2 Fintype.card_pos).1 <| finrank_vectorSpan_range_le _ _
    (tsub_add_cancel_of_le <| Nat.succ_le_iff.2 Fintype.card_pos).symm

/-- `n + 1` points are affinely independent if and only if their
`vectorSpan` has dimension `n`. -/
/-
**affineIndependent_iff_finrank_vectorSpan_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineIndependent_iff_finrank_vectorSpan_eq [Fintype ι] (p : ι -> P) {n : 
Nat} (hc : Fintype.card ι = n + 1) : AffineIndependent k p ↔ finrank k (vectorSp
an k (Set.range p)) = n
参数：p : ι -> P；hc : Fintype.card ι = n + 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `affineIndependent_iff_linearIndependent_vsub`：affineIndependent_iff_line
arIndependent_vsub (p : ι -> P) (i1 : ι) : AffineIndependent k p ↔ LinearIndepen
dent k fun i : { x // x != i1 } =>…
· 使用定理 `linearIndependent_iff_card_eq_finrank_span`：linearIndependent_iff_card_e
q_finrank_span [Nontrivial R] {ι} [Fintype ι] {b : ι -> M} : LinearIndependent R
 b ↔ Fintype.card ι = (Set.range…
· 使用定理 `IsNoetherianRing.orzechProperty`：∀ (R : Type u_1) [inst : Ring R] [IsNoe
therianRing R], OrzechProperty R
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `vectorSpan_range_eq_span_range_vsub_right_ne`：vectorSpan_range_eq_span_r
ange_vsub_right_ne (p : ι -> P) (i₀ : ι) : vectorSpan k (Set.range p) = Submodul
e.span k (Set.range fun i : { x //…
· 使用定理 `Set.finrank.eq_1`：∀ (R : Type u) {M : Type v} [inst : Semiring R] [inst_
1 : AddCommMonoid M] [inst_2 : _root_.Module R M] (s : Set M),   Set.finrank R s
 = Mod…
· 使用定理 `Fintype.subtype_card`：subtype_card {p : α -> Prop} (s : Finset α) (H : f
orall x : α, x in s ↔ p x) : @card { x // p x } (Fintype.subtype s H) = #s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.filter_ne'`：filter_ne' [DecidableEq β] (s : Finset β) (b : β) : (
s.filter fun a => a != b) = s.erase b
· 使用定理 `Finset.card_erase_of_mem`：card_erase_of_mem : a in s -> #(s.erase a) = #
s - 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
`n + 1` points are affinely independent if and only if their
`vectorSpan` has dimension `n`.
-/
theorem affineIndependent_iff_finrank_vectorSpan_eq [Fintype ι] (p : ι → P) {n : ℕ}
    (hc : Fintype.card ι = n + 1) :
    AffineIndependent k p ↔ finrank k (vectorSpan k (Set.range p)) = n := by
  classical
  have hn : Nonempty ι := by simp [← Fintype.card_pos_iff, hc]
  obtain ⟨i₁⟩ := hn
  rw [affineIndependent_iff_linearIndependent_vsub _ _ i₁,
    linearIndependent_iff_card_eq_finrank_span, eq_comm,
    vectorSpan_range_eq_span_range_vsub_right_ne k p i₁, Set.finrank]
  rw [← Finset.card_univ] at hc
  rw [Fintype.subtype_card]
  simp [Finset.filter_ne', Finset.card_erase_of_mem, hc]

/-- `n + 1` points are affinely independent if and only if their
`vectorSpan` has dimension at least `n`. -/
/-
**affineIndependent_iff_le_finrank_vectorSpan** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineIndependent_iff_le_finrank_vectorSpan [Fintype ι] (p : ι -> P) {n : 
Nat} (hc : Fintype.card ι = n + 1) : AffineIndependent k p ↔ n <= finrank k (vec
torSpan k (Set.range p))
参数：p : ι -> P；hc : Fintype.card ι = n + 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `affineIndependent_iff_finrank_vectorSpan_eq`：affineIndependent_iff_finra
nk_vectorSpan_eq [Fintype ι] (p : ι -> P) {n : Nat} (hc : Fintype.card ι = n + 1
) : AffineIndependent k p ↔ finra…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `finrank_vectorSpan_range_le`：finrank_vectorSpan_range_le [Fintype ι] (p 
: ι -> P) {n : Nat} (hc : Fintype.card ι = n + 1) : finrank k (vectorSpan k (Set
.range p)) <= n

--- 原说明 ---
`n + 1` points are affinely independent if and only if their
`vectorSpan` has dimension at least `n`.
-/
theorem affineIndependent_iff_le_finrank_vectorSpan [Fintype ι] (p : ι → P) {n : ℕ}
    (hc : Fintype.card ι = n + 1) :
    AffineIndependent k p ↔ n ≤ finrank k (vectorSpan k (Set.range p)) := by
  rw [affineIndependent_iff_finrank_vectorSpan_eq k p hc]
  constructor
  · rintro rfl
    rfl
  · exact fun hle => le_antisymm (finrank_vectorSpan_range_le k p hc) hle

/-- `n + 2` points are affinely independent if and only if their
`vectorSpan` does not have dimension at most `n`. -/
/-
**affineIndependent_iff_not_finrank_vectorSpan_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineIndependent_iff_not_finrank_vectorSpan_le [Fintype ι] (p : ι -> P) {
n : Nat} (hc : Fintype.card ι = n + 2) : AffineIndependent k p ↔ ¬finrank k (vec
torSpan k (Set.range p)) <= n
参数：p : ι -> P；hc : Fintype.card ι = n + 2。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `affineIndependent_iff_le_finrank_vectorSpan`：affineIndependent_iff_le_fi
nrank_vectorSpan [Fintype ι] (p : ι -> P) {n : Nat} (hc : Fintype.card ι = n + 1
) : AffineIndependent k p ↔ n <= …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.lt_iff_add_one_le`：∀ {m n : ℕ}, m < n ↔ m + 1 ≤ n
· 使用定理 `lt_iff_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a < b 
↔ ¬b ≤ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`n + 2` points are affinely independent if and only if their
`vectorSpan` does not have dimension at most `n`.
-/
theorem affineIndependent_iff_not_finrank_vectorSpan_le [Fintype ι] (p : ι → P) {n : ℕ}
    (hc : Fintype.card ι = n + 2) :
    AffineIndependent k p ↔ ¬finrank k (vectorSpan k (Set.range p)) ≤ n := by
  rw [affineIndependent_iff_le_finrank_vectorSpan k p hc, ← Nat.lt_iff_add_one_le, lt_iff_not_ge]

/-- `n + 2` points have a `vectorSpan` with dimension at most `n` if
and only if they are not affinely independent. -/
/-
**finrank_vectorSpan_le_iff_not_affineIndependent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finrank_vectorSpan_le_iff_not_affineIndependent [Fintype ι] (p : ι -> P) {
n : Nat} (hc : Fintype.card ι = n + 2) : finrank k (vectorSpan k (Set.range p)) 
<= n ↔ ¬AffineIndependent k p
参数：p : ι -> P；hc : Fintype.card ι = n + 2。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_iff_comm`：not_iff_comm : (¬a ↔ b) ↔ (¬b ↔ a)
· 使用定理 `affineIndependent_iff_not_finrank_vectorSpan_le`：affineIndependent_iff_n
ot_finrank_vectorSpan_le [Fintype ι] (p : ι -> P) {n : Nat} (hc : Fintype.card ι
 = n + 2) : AffineIndependent k p ↔ ¬…

--- 原说明 ---
`n + 2` points have a `vectorSpan` with dimension at most `n` if
and only if they are not affinely independent.
-/
theorem finrank_vectorSpan_le_iff_not_affineIndependent [Fintype ι] (p : ι → P) {n : ℕ}
    (hc : Fintype.card ι = n + 2) :
    finrank k (vectorSpan k (Set.range p)) ≤ n ↔ ¬AffineIndependent k p :=
  (not_iff_comm.1 (affineIndependent_iff_not_finrank_vectorSpan_le k p hc).symm).symm

variable {k}
/-
**AffineIndependent.card_le_finrank_succ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AffineIndependent.card_le_finrank_succ [Fintype ι] {p : ι -> P} (hp : Affi
neIndependent k p) : Fintype.card ι <= Module.finrank k (vectorSpan k (Set.range
 p)) + 1
参数：hp : AffineIndependent k p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_eq_zero`：∀ {α : Type u_1} [inst : Fintype α] [IsEmpty α], F
intype.card α = 0
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsub_le_iff_right`：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub 
α] {a b c : α} : a - b <= c ↔ a <= c + b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `affineIndependent_iff_le_finrank_vectorSpan`：affineIndependent_iff_le_fi
nrank_vectorSpan [Fintype ι] (p : ι -> P) {n : Nat} (hc : Fintype.card ι = n + 1
) : AffineIndependent k p ↔ n <= …
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
· 使用定理 `Fintype.card_ne_zero`：card_ne_zero [Nonempty α] : card α != 0
-/
lemma AffineIndependent.card_le_finrank_succ [Fintype ι] {p : ι → P} (hp : AffineIndependent k p) :
    Fintype.card ι ≤ Module.finrank k (vectorSpan k (Set.range p)) + 1 := by
  cases isEmpty_or_nonempty ι
  · simp [Fintype.card_eq_zero]
  rw [← tsub_le_iff_right]
  exact (affineIndependent_iff_le_finrank_vectorSpan _ _
    (tsub_add_cancel_of_le <| Nat.one_le_iff_ne_zero.2 Fintype.card_ne_zero).symm).1 hp

open Finset in
/-- If an affine independent finset is contained in the affine span of another finset, then its
cardinality is at most the cardinality of that finset. -/
/-
**AffineIndependent.card_le_card_of_subset_affineSpan** 是 Mathlib 中的一个引理，位于命名空间 
``。
形式化陈述：AffineIndependent.card_le_card_of_subset_affineSpan {s t : Finset V} (hs :
 AffineIndependent k ((↑) : s -> V)) (hst : (s : Set V) subseteq affineSpan k (t
 : Set V)) : #s <= #t
参数：hs : AffineIndependent k ((↑) : s -> V)；hst : (s : Set V) subseteq affineSpan
 k (t : Set V)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `AffineSubspace.span_empty`：span_empty : affineSpan k (∅ : Set P) = ⊥
· 使用定理 `Finset.Nonempty.to_subtype`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty 
→ Nonempty ↥s
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `Finset.Nonempty.to_set`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → (↑
s).Nonempty
· 使用定理 `AffineSubspace.direction_le`：direction_le {s₁ s₂ : AffineSubspace k P} (
h : s₁ <= s₂) : s₁.direction <= s₂.direction
· 使用定理 `affineSpan_mono`：affineSpan_mono {s₁ s₂ : Set P} (h : s₁ subseteq s₂) : 
affineSpan k s₁ <= affineSpan k s₂
· 使用定理 `add_le_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [i : Ad
dRightMono α] {b c : α}, b ≤ c → ∀ (a : α), b + a ≤ c + a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Submodule.finrank_mono`：Submodule.finrank_mono {s t : Submodule R M} [Mo
dule.Finite R t] (hst : s <= t) : finrank R s <= finrank R t
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s
· 使用定理 `AffineSubspace.affineSpan_coe`：affineSpan_coe (s : AffineSubspace k P) :
 affineSpan k (s : Set P) = s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
If an affine independent finset is contained in the affine span of another finse
t, then its
cardinality is at most the cardinality of that finset.
-/
lemma AffineIndependent.card_le_card_of_subset_affineSpan {s t : Finset V}
    (hs : AffineIndependent k ((↑) : s → V)) (hst : (s : Set V) ⊆ affineSpan k (t : Set V)) :
    #s ≤ #t := by
  obtain rfl | hs' := s.eq_empty_or_nonempty
  · simp
  obtain rfl | ht' := t.eq_empty_or_nonempty
  · simpa [Set.subset_empty_iff] using hst
  have := hs'.to_subtype
  have := ht'.to_set.to_subtype
  have direction_le := AffineSubspace.direction_le (affineSpan_mono k hst)
  rw [AffineSubspace.affineSpan_coe, direction_affineSpan, direction_affineSpan,
    ← @Subtype.range_coe _ (s : Set V), ← @Subtype.range_coe _ (t : Set V)] at direction_le
  have finrank_le := add_le_add_left (Submodule.finrank_mono direction_le) 1
  -- We use `erw` to elide the difference between `↥s` and `↥(s : Set V)}`
  erw [hs.finrank_vectorSpan_add_one] at finrank_le
  simpa using finrank_le.trans <| finrank_vectorSpan_range_add_one_le _ _

open Finset in
/-- If the affine span of an affine independent finset is strictly contained in the affine span of
another finset, then its cardinality is strictly less than the cardinality of that finset. -/
/-
**AffineIndependent.card_lt_card_of_affineSpan_lt_affineSpan** 是 Mathlib 中的一个引理，
位于命名空间 ``。
形式化陈述：AffineIndependent.card_lt_card_of_affineSpan_lt_affineSpan {s t : Finset V
} (hs : AffineIndependent k ((↑) : s -> V)) (hst : affineSpan k (s : Set V) < af
fineSpan k (t : Set V)) : #s < #t
参数：hs : AffineIndependent k ((↑) : s -> V)；hst : affineSpan k (s : Set V) < affi
neSpan k (t : Set V)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `AffineSubspace.span_empty`：span_empty : affineSpan k (∅ : Set P) = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.Nonempty.to_subtype`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty 
→ Nonempty ↥s
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `Finset.Nonempty.to_set`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → (↑
s).Nonempty
· 使用定理 `AffineSubspace.direction_lt_of_nonempty`：direction_lt_of_nonempty {s₁ s₂
 : AffineSubspace k P} (h : s₁ < s₂) (hn : (s₁ : Set P).Nonempty) : s₁.direction
 < s₂.direction
· 使用定理 `Set.Nonempty.affineSpan`：∀ (k : Type u_1) {V : Type u_2} {P : Type u_3} 
[inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [inst_3
 : AddTorsor …
· 使用定理 `add_lt_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [i : Ad
dRightStrictMono α] {b c : α}, b < c → ∀ (a : α), b + a < c + a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Submodule.finrank_lt_finrank_of_lt`：finrank_lt_finrank_of_lt {s t : Subm
odule K V} [FiniteDimensional K t] (hst : s < t) : finrank K s < finrank K t
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用引理 `AffineIndependent.finrank_vectorSpan_add_one`：AffineIndependent.finrank_
vectorSpan_add_one [Fintype ι] [Nonempty ι] {p : ι -> P} (hi : AffineIndependent
 k p) : finrank k (vectorSpan k (S…
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
If the affine span of an affine independent finset is strictly contained in the 
affine span of
another finset, then its cardinality is strictly less than the cardinality of th
at finset.
-/
lemma AffineIndependent.card_lt_card_of_affineSpan_lt_affineSpan {s t : Finset V}
    (hs : AffineIndependent k ((↑) : s → V))
    (hst : affineSpan k (s : Set V) < affineSpan k (t : Set V)) : #s < #t := by
  obtain rfl | hs' := s.eq_empty_or_nonempty
  · simpa [card_pos] using hst
  obtain rfl | ht' := t.eq_empty_or_nonempty
  · simp at hst
  have := hs'.to_subtype
  have := ht'.to_set.to_subtype
  have dir_lt := AffineSubspace.direction_lt_of_nonempty (k := k) hst <| hs'.to_set.affineSpan k
  rw [direction_affineSpan, direction_affineSpan,
    ← @Subtype.range_coe _ (s : Set V), ← @Subtype.range_coe _ (t : Set V)] at dir_lt
  have finrank_lt := add_lt_add_left (Submodule.finrank_lt_finrank_of_lt dir_lt) 1
  -- We use `erw` to elide the difference between `↥s` and `↥(s : Set V)}`
  erw [hs.finrank_vectorSpan_add_one] at finrank_lt
  simpa using finrank_lt.trans_le <| finrank_vectorSpan_range_add_one_le _ _

/-- If the `vectorSpan` of a finite subset of an affinely independent
family lies in a submodule with dimension one less than its
cardinality, it equals that submodule. -/
/-
**AffineIndependent.vectorSpan_image_finset_eq_of_le_of_card_eq_finrank_add_one*
* 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineIndependent.vectorSpan_image_finset_eq_of_le_of_card_eq_finrank_add_
one [DecidableEq P] {p : ι -> P} (hi : AffineIndependent k p) {s : Finset ι} {sm
 : Submodule k V} [FiniteDimensional k sm] (hle : vectorSpan k (s.image p : Set 
P) <= sm) (hc : #s = finrank k sm + 1) : vectorSpan k (s.image p : Set P) = sm
参数：hi : AffineIndependent k p；hle : vectorSpan k (s.image p : Set P) <= sm；hc : 
#s = finrank k sm + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.eq_of_le_of_finrank_eq`：eq_of_le_of_finrank_eq {S₁ S₂ : Submod
ule K V} [FiniteDimensional K S₂] (hle : S₁ <= S₂) (hd : finrank K S₁ = finrank 
K S₂) : S₁ = S₂
· 使用定理 `AffineIndependent.finrank_vectorSpan_image_finset`：AffineIndependent.fin
rank_vectorSpan_image_finset [DecidableEq P] {p : ι -> P} (hi : AffineIndependen
t k p) {s : Finset ι} {n : Nat} (hc : #…

--- 原说明 ---
If the `vectorSpan` of a finite subset of an affinely independent
family lies in a submodule with dimension one less than its
cardinality, it equals that submodule.
-/
theorem AffineIndependent.vectorSpan_image_finset_eq_of_le_of_card_eq_finrank_add_one
    [DecidableEq P] {p : ι → P}
    (hi : AffineIndependent k p) {s : Finset ι} {sm : Submodule k V} [FiniteDimensional k sm]
    (hle : vectorSpan k (s.image p : Set P) ≤ sm) (hc : #s = finrank k sm + 1) :
    vectorSpan k (s.image p : Set P) = sm :=
  Submodule.eq_of_le_of_finrank_eq hle <| hi.finrank_vectorSpan_image_finset hc

/-- If the `vectorSpan` of a finite affinely independent
family lies in a submodule with dimension one less than its
cardinality, it equals that submodule. -/
/-
**AffineIndependent.vectorSpan_eq_of_le_of_card_eq_finrank_add_one** 是 Mathlib 中
的一个定理，位于命名空间 ``。
形式化陈述：AffineIndependent.vectorSpan_eq_of_le_of_card_eq_finrank_add_one [Fintype 
ι] {p : ι -> P} (hi : AffineIndependent k p) {sm : Submodule k V} [FiniteDimensi
onal k sm] (hle : vectorSpan k (Set.range p) <= sm) (hc : Fintype.card ι = finra
nk k sm + 1) : vectorSpan k (Set.range p) = sm
参数：hi : AffineIndependent k p；hle : vectorSpan k (Set.range p) <= sm；hc : Fintyp
e.card ι = finrank k sm + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.eq_of_le_of_finrank_eq`：eq_of_le_of_finrank_eq {S₁ S₂ : Submod
ule K V} [FiniteDimensional K S₂] (hle : S₁ <= S₂) (hd : finrank K S₁ = finrank 
K S₂) : S₁ = S₂
· 使用定理 `AffineIndependent.finrank_vectorSpan`：AffineIndependent.finrank_vectorSp
an [Fintype ι] {p : ι -> P} (hi : AffineIndependent k p) {n : Nat} (hc : Fintype
.card ι = n + 1) : finrank…

--- 原说明 ---
If the `vectorSpan` of a finite affinely independent
family lies in a submodule with dimension one less than its
cardinality, it equals that submodule.
-/
theorem AffineIndependent.vectorSpan_eq_of_le_of_card_eq_finrank_add_one [Fintype ι] {p : ι → P}
    (hi : AffineIndependent k p) {sm : Submodule k V} [FiniteDimensional k sm]
    (hle : vectorSpan k (Set.range p) ≤ sm) (hc : Fintype.card ι = finrank k sm + 1) :
    vectorSpan k (Set.range p) = sm :=
  Submodule.eq_of_le_of_finrank_eq hle <| hi.finrank_vectorSpan hc

/-- If the `affineSpan` of a finite subset of an affinely independent
family lies in an affine subspace whose direction has dimension one
less than its cardinality, it equals that subspace. -/
/-
**AffineIndependent.affineSpan_image_finset_eq_of_le_of_card_eq_finrank_add_one*
* 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineIndependent.affineSpan_image_finset_eq_of_le_of_card_eq_finrank_add_
one [DecidableEq P] {p : ι -> P} (hi : AffineIndependent k p) {s : Finset ι} {sp
 : AffineSubspace k P} [FiniteDimensional k sp.direction] (hle : affineSpan k (s
.image p : Set P) <= sp) (hc : #s = finrank k sp.direction + 1) : affineSpan k (
s.image p : Set P) = sp
参数：hi : AffineIndependent k p；hle : affineSpan k (s.image p : Set P) <= sp；hc : 
#s = finrank k sp.direction + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_pos`：∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempt
y
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `AffineSubspace.eq_of_direction_eq_of_nonempty_of_le`：eq_of_direction_eq_
of_nonempty_of_le {s₁ s₂ : AffineSubspace k P} (hd : s₁.direction = s₂.direction
) (hn : (s₁ : Set P).Nonempty) (hle : s₁ …
· 使用定理 `AffineSubspace.direction_le`：direction_le {s₁ s₂ : AffineSubspace k P} (
h : s₁ <= s₂) : s₁.direction <= s₂.direction
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s
· 使用定理 `AffineIndependent.vectorSpan_image_finset_eq_of_le_of_card_eq_finrank_ad
d_one`：AffineIndependent.vectorSpan_image_finset_eq_of_le_of_card_eq_finrank_add
_one [DecidableEq P] {p : ι -> P} (hi : AffineIndependent k p) {s :…
· 使用定理 `Set.Nonempty.affineSpan`：∀ (k : Type u_1) {V : Type u_2} {P : Type u_3} 
[inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [inst_3
 : AddTorsor …
· 使用定理 `Finset.Nonempty.to_set`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → (↑
s).Nonempty
· 使用定理 `Finset.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} [inst : Decidable
Eq β] {s : Finset α},   s.Nonempty → ∀ (f : α → β), (Finset.image f s).Nonempty

--- 原说明 ---
If the `affineSpan` of a finite subset of an affinely independent
family lies in an affine subspace whose direction has dimension one
less than its cardinality, it equals that subspace.
-/
theorem AffineIndependent.affineSpan_image_finset_eq_of_le_of_card_eq_finrank_add_one
    [DecidableEq P] {p : ι → P}
    (hi : AffineIndependent k p) {s : Finset ι} {sp : AffineSubspace k P}
    [FiniteDimensional k sp.direction] (hle : affineSpan k (s.image p : Set P) ≤ sp)
    (hc : #s = finrank k sp.direction + 1) : affineSpan k (s.image p : Set P) = sp := by
  have hn : s.Nonempty := by
    rw [← Finset.card_pos, hc]
    apply Nat.succ_pos
  refine eq_of_direction_eq_of_nonempty_of_le ?_ ((hn.image p).to_set.affineSpan k) hle
  have hd := direction_le hle
  rw [direction_affineSpan] at hd ⊢
  exact hi.vectorSpan_image_finset_eq_of_le_of_card_eq_finrank_add_one hd hc

/-- If the `affineSpan` of a finite affinely independent family lies
in an affine subspace whose direction has dimension one less than its
cardinality, it equals that subspace. -/
/-
**AffineIndependent.affineSpan_eq_of_le_of_card_eq_finrank_add_one** 是 Mathlib 中
的一个定理，位于命名空间 ``。
形式化陈述：AffineIndependent.affineSpan_eq_of_le_of_card_eq_finrank_add_one [Fintype 
ι] {p : ι -> P} (hi : AffineIndependent k p) {sp : AffineSubspace k P} [FiniteDi
mensional k sp.direction] (hle : affineSpan k (Set.range p) <= sp) (hc : Fintype
.card ι = finrank k sp.direction + 1) : affineSpan k (Set.range p) = sp
参数：hi : AffineIndependent k p；hle : affineSpan k (Set.range p) <= sp；hc : Fintyp
e.card ι = finrank k sp.direction + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `AffineIndependent.affineSpan_image_finset_eq_of_le_of_card_eq_finrank_ad
d_one`：AffineIndependent.affineSpan_image_finset_eq_of_le_of_card_eq_finrank_add
_one [DecidableEq P] {p : ι -> P} (hi : AffineIndependent k p) {s :…
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α

--- 原说明 ---
If the `affineSpan` of a finite affinely independent family lies
in an affine subspace whose direction has dimension one less than its
cardinality, it equals that subspace.
-/
theorem AffineIndependent.affineSpan_eq_of_le_of_card_eq_finrank_add_one [Fintype ι] {p : ι → P}
    (hi : AffineIndependent k p) {sp : AffineSubspace k P} [FiniteDimensional k sp.direction]
    (hle : affineSpan k (Set.range p) ≤ sp) (hc : Fintype.card ι = finrank k sp.direction + 1) :
    affineSpan k (Set.range p) = sp := by
  classical
  rw [← Finset.card_univ] at hc
  rw [← Set.image_univ, ← Finset.coe_univ, ← Finset.coe_image] at hle ⊢
  exact hi.affineSpan_image_finset_eq_of_le_of_card_eq_finrank_add_one hle hc

/-- The `affineSpan` of a finite affinely independent family is `⊤` iff the
family's cardinality is one more than that of the finite-dimensional space. -/
/-
**AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one** 是 Mathlib 中的
一个定理，位于命名空间 ``。
形式化陈述：AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one [FiniteDim
ensional k V] [Fintype ι] {p : ι -> P} (hi : AffineIndependent k p) : affineSpan
 k (Set.range p) = ⊤ ↔ Fintype.card ι = finrank k V + 1
参数：hi : AffineIndependent k p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.succ_pred_eq_of_pos`：∀ {n : ℕ}, 0 < n → n.pred.succ = n
· 使用定理 `AffineSubspace.card_pos_of_affineSpan_eq_top`：card_pos_of_affineSpan_eq_
top {ι : Type*} [Fintype ι] {p : ι -> P} (h : affineSpan k (range p) = ⊤) : 0 < 
Fintype.card ι
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finrank_top`：finrank_top : finrank R (⊤ : Submodule R M) = finrank R M
· 使用定理 `AffineSubspace.vectorSpan_eq_top_of_affineSpan_eq_top`：vectorSpan_eq_top
_of_affineSpan_eq_top {s : Set P} (h : affineSpan k s = ⊤) : vectorSpan k s = ⊤
· 使用定理 `AffineIndependent.finrank_vectorSpan`：AffineIndependent.finrank_vectorSp
an [Fintype ι] {p : ι -> P} (hi : AffineIndependent k p) {n : Nat} (hc : Fintype
.card ι = n + 1) : finrank…
· 使用定理 `AffineIndependent.affineSpan_eq_of_le_of_card_eq_finrank_add_one`：Affine
Independent.affineSpan_eq_of_le_of_card_eq_finrank_add_one [Fintype ι] {p : ι ->
 P} (hi : AffineIndependent k p) {sp : AffineSubspace …
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `AffineSubspace.direction_top`：direction_top : (⊤ : AffineSubspace k P).d
irection = ⊤

--- 原说明 ---
The `affineSpan` of a finite affinely independent family is `⊤` iff the
family's cardinality is one more than that of the finite-dimensional space.
-/
theorem AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one [FiniteDimensional k V]
    [Fintype ι] {p : ι → P} (hi : AffineIndependent k p) :
    affineSpan k (Set.range p) = ⊤ ↔ Fintype.card ι = finrank k V + 1 := by
  constructor
  · intro h_tot
    let n := Fintype.card ι - 1
    have hn : Fintype.card ι = n + 1 :=
      (Nat.succ_pred_eq_of_pos (card_pos_of_affineSpan_eq_top k V P h_tot)).symm
    rw [hn, ← finrank_top, ← (vectorSpan_eq_top_of_affineSpan_eq_top k V P) h_tot,
      ← hi.finrank_vectorSpan hn]
  · intro hc
    rw [← finrank_top, ← direction_top k V P] at hc
    exact hi.affineSpan_eq_of_le_of_card_eq_finrank_add_one le_top hc
/-
**Affine.Simplex.span_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Affine.Simplex.span_eq_top [FiniteDimensional k V] {n : Nat} (T : Affine.S
implex k V n) (hrank : finrank k V = n) : affineSpan k (Set.range T.points) = ⊤
参数：T : Affine.Simplex k V n；hrank : finrank k V = n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one`：AffineI
ndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one [FiniteDimensional k V]
 [Fintype ι] {p : ι -> P} (hi : AffineIndependent k p…
· 使用定理 `Affine.Simplex.independent`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [ins
t_3 : AddTorsor …
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
-/
theorem Affine.Simplex.span_eq_top [FiniteDimensional k V] {n : ℕ} (T : Affine.Simplex k V n)
    (hrank : finrank k V = n) : affineSpan k (Set.range T.points) = ⊤ := by
  rw [AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one T.independent,
    Fintype.card_fin, hrank]

/-- The `vectorSpan` of adding a point to a finite-dimensional subspace is finite-dimensional. -/
/-
**finiteDimensional_vectorSpan_insert** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：finiteDimensional_vectorSpan_insert (s : AffineSubspace k P) [FiniteDimens
ional k s.direction] (p : P) : FiniteDimensional k (vectorSpan k (insert p (s : 
Set P)))
参数：s : AffineSubspace k P；p : P。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s
· 使用定理 `affineSpan_insert_affineSpan`：affineSpan_insert_affineSpan (p : P) (ps :
 Set P) : affineSpan k (insert p (affineSpan k ps : Set P)) = affineSpan k (inse
rt p ps)
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `AffineSubspace.coe_eq_bot_iff`：coe_eq_bot_iff (Q : AffineSubspace k P) :
 (Q : Set P) = ∅ ↔ Q = ⊥
· 使用定理 `AffineSubspace.bot_coe`：bot_coe : ((⊥ : AffineSubspace k P) : Set P) = ∅
· 使用定理 `AffineSubspace.span_empty`：span_empty : affineSpan k (∅ : Set P) = ⊥
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LawfulSingleton.insert_empty_eq`：∀ {α : Type u} {β : Type v} {inst : Emp
tyCollection β} {inst_1 : Insert α β} {inst_2 : Singleton α β}   [self : LawfulS
ingleton α β] (x : α)…
· 使用定理 `Set.instLawfulSingleton`：∀ {α : Type u_1}, LawfulSingleton α (Set α)
· 使用定理 `vectorSpan_singleton`：vectorSpan_singleton (p : P) : vectorSpan k ({p} :
 Set P) = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `AffineSubspace.affineSpan_coe`：affineSpan_coe (s : AffineSubspace k P) :
 affineSpan k (s : Set P) = s
· 使用定理 `AffineSubspace.direction_affineSpan_insert`：direction_affineSpan_insert 
{s : AffineSubspace k P} {p₁ p₂ : P} (hp₁ : p₁ in s) : (affineSpan k (insert p₂ 
(s : Set P))).direction = Submod…

--- 原说明 ---
The `vectorSpan` of adding a point to a finite-dimensional subspace is finite-di
mensional.
-/
instance finiteDimensional_vectorSpan_insert (s : AffineSubspace k P)
    [FiniteDimensional k s.direction] (p : P) :
    FiniteDimensional k (vectorSpan k (insert p (s : Set P))) := by
  rw [← direction_affineSpan, ← affineSpan_insert_affineSpan]
  rcases (s : Set P).eq_empty_or_nonempty with (hs | ⟨p₀, hp₀⟩)
  · rw [coe_eq_bot_iff] at hs
    rw [hs, bot_coe, span_empty, bot_coe, direction_affineSpan]
    convert! finiteDimensional_bot k V <;> simp
  · rw [affineSpan_coe, direction_affineSpan_insert hp₀]
    infer_instance

/-- The direction of the affine span of adding a point to a finite-dimensional subspace is
finite-dimensional. -/
/-
**finiteDimensional_direction_affineSpan_insert** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：finiteDimensional_direction_affineSpan_insert (s : AffineSubspace k P) [Fi
niteDimensional k s.direction] (p : P) : FiniteDimensional k (affineSpan k (inse
rt p (s : Set P))).direction
参数：s : AffineSubspace k P；p : P。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s

--- 原说明 ---
The direction of the affine span of adding a point to a finite-dimensional subsp
ace is
finite-dimensional.
-/
instance finiteDimensional_direction_affineSpan_insert (s : AffineSubspace k P)
    [FiniteDimensional k s.direction] (p : P) :
    FiniteDimensional k (affineSpan k (insert p (s : Set P))).direction :=
  (direction_affineSpan k (insert p (s : Set P))).symm ▸ finiteDimensional_vectorSpan_insert s p

variable (k)

/-- The `vectorSpan` of adding a point to a set with a finite-dimensional `vectorSpan` is
finite-dimensional. -/
/-
**finiteDimensional_vectorSpan_insert_set** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：finiteDimensional_vectorSpan_insert_set (s : Set P) [FiniteDimensional k (
vectorSpan k s)] (p : P) : FiniteDimensional k (vectorSpan k (insert p s))
参数：s : Set P；vectorSpan k s；p : P。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `affineSpan_insert_affineSpan`：affineSpan_insert_affineSpan (p : P) (ps :
 Set P) : affineSpan k (insert p (affineSpan k ps : Set P)) = affineSpan k (inse
rt p ps)

--- 原说明 ---
The `vectorSpan` of adding a point to a set with a finite-dimensional `vectorSpa
n` is
finite-dimensional.
-/
instance finiteDimensional_vectorSpan_insert_set (s : Set P) [FiniteDimensional k (vectorSpan k s)]
    (p : P) : FiniteDimensional k (vectorSpan k (insert p s)) := by
  have : FiniteDimensional k (affineSpan k s).direction :=
    (direction_affineSpan k s).symm ▸ inferInstance
  rw [← direction_affineSpan, ← affineSpan_insert_affineSpan, direction_affineSpan]
  exact finiteDimensional_vectorSpan_insert (affineSpan k s) p

/-- The direction of the affine span of adding a point to a set with a set with finite-dimensional
direction of the `affineSpan` is finite-dimensional. -/
/-
**finiteDimensional_direction_affineSpan_insert_set** 是 Mathlib 中的一个实例，位于命名空间 ``
。
形式化陈述：finiteDimensional_direction_affineSpan_insert_set (s : Set P) [FiniteDimen
sional k (affineSpan k s).direction] (p : P) : FiniteDimensional k (affineSpan k
 (insert p s)).direction
参数：s : Set P；affineSpan k s；p : P。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
The direction of the affine span of adding a point to a set with a set with fini
te-dimensional
direction of the `affineSpan` is finite-dimensional.
-/
instance finiteDimensional_direction_affineSpan_insert_set (s : Set P)
    [FiniteDimensional k (affineSpan k s).direction] (p : P) :
    FiniteDimensional k (affineSpan k (insert p s)).direction := by
  have : FiniteDimensional k (vectorSpan k s) := (direction_affineSpan k s) ▸ inferInstance
  rw [direction_affineSpan]
  infer_instance

/-- A set of points is collinear if their `vectorSpan` has dimension
at most `1`. -/
/-
**Collinear** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Collinear (s : Set P) : Prop
参数：s : Set P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set of points is collinear if their `vectorSpan` has dimension
at most `1`.
-/
def Collinear (s : Set P) : Prop :=
  Module.rank k (vectorSpan k s) ≤ 1

/-- The definition of `Collinear`. -/
/-
**collinear_iff_rank_le_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：collinear_iff_rank_le_one (s : Set P) : Collinear k s ↔ Module.rank k (vec
torSpan k s) <= 1
参数：s : Set P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The definition of `Collinear`.
-/
theorem collinear_iff_rank_le_one (s : Set P) :
    Collinear k s ↔ Module.rank k (vectorSpan k s) ≤ 1 := Iff.rfl

variable {k}

/-- A set of points, whose `vectorSpan` is finite-dimensional, is
collinear if and only if their `vectorSpan` has dimension at most
`1`. -/
/-
**collinear_iff_finrank_le_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：collinear_iff_finrank_le_one {s : Set P} [FiniteDimensional k (vectorSpan 
k s)] : Collinear k s ↔ finrank k (vectorSpan k s) <= 1
参数：vectorSpan k s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `collinear_iff_rank_le_one`：collinear_iff_rank_le_one (s : Set P) : Colli
near k s ↔ Module.rank k (vectorSpan k s) <= 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `Module.finrank_eq_rank`：finrank_eq_rank [Module.Finite R M] : ↑(finrank 
R M) = Module.rank R M
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K

--- 原说明 ---
A set of points, whose `vectorSpan` is finite-dimensional, is
collinear if and only if their `vectorSpan` has dimension at most
`1`.
-/
theorem collinear_iff_finrank_le_one {s : Set P} [FiniteDimensional k (vectorSpan k s)] :
    Collinear k s ↔ finrank k (vectorSpan k s) ≤ 1 := by
  have h := collinear_iff_rank_le_one k s
  rw [← finrank_eq_rank] at h
  exact mod_cast h

alias ⟨Collinear.finrank_le_one, _⟩ := collinear_iff_finrank_le_one

/-- A subset of a collinear set is collinear. -/
/-
**Collinear.subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Collinear.subset {s₁ s₂ : Set P} (hs : s₁ subseteq s₂) (h : Collinear k s₂
) : Collinear k s₁
参数：hs : s₁ subseteq s₂；h : Collinear k s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Submodule.rank_mono`：Submodule.rank_mono {s t : Submodule R M} (h : s <=
 t) : Module.rank R s <= Module.rank R t
· 使用定理 `vectorSpan_mono`：vectorSpan_mono {s₁ s₂ : Set P} (h : s₁ subseteq s₂) : 
vectorSpan k s₁ <= vectorSpan k s₂

--- 原说明 ---
A subset of a collinear set is collinear.
-/
theorem Collinear.subset {s₁ s₂ : Set P} (hs : s₁ ⊆ s₂) (h : Collinear k s₂) : Collinear k s₁ :=
  (Submodule.rank_mono (vectorSpan_mono k hs)).trans h

/-- The `vectorSpan` of collinear points is finite-dimensional. -/
/-
**Collinear.finiteDimensional_vectorSpan** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Collinear.finiteDimensional_vectorSpan {s : Set P} (h : Collinear k s) : F
initeDimensional k (vectorSpan k s)
参数：h : Collinear k s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsNoetherian.iff_fg`：iff_fg : IsNoetherian K V ↔ Module.Finite K V
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsNoetherian.iff_rank_lt_aleph0`：iff_rank_lt_aleph0 : IsNoetherian K V ↔
 Module.rank K V < ℵ₀
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Cardinal.one_lt_aleph0`：one_lt_aleph0 : 1 < ℵ₀

--- 原说明 ---
The `vectorSpan` of collinear points is finite-dimensional.
-/
theorem Collinear.finiteDimensional_vectorSpan {s : Set P} (h : Collinear k s) :
    FiniteDimensional k (vectorSpan k s) :=
  IsNoetherian.iff_fg.1
    (IsNoetherian.iff_rank_lt_aleph0.2 (lt_of_le_of_lt h Cardinal.one_lt_aleph0))

/-- The direction of the affine span of collinear points is finite-dimensional. -/
/-
**Collinear.finiteDimensional_direction_affineSpan** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Collinear.finiteDimensional_direction_affineSpan {s : Set P} (h : Collinea
r k s) : FiniteDimensional k (affineSpan k s).direction
参数：h : Collinear k s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Collinear.finiteDimensional_vectorSpan`：Collinear.finiteDimensional_vect
orSpan {s : Set P} (h : Collinear k s) : FiniteDimensional k (vectorSpan k s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s

--- 原说明 ---
The direction of the affine span of collinear points is finite-dimensional.
-/
theorem Collinear.finiteDimensional_direction_affineSpan {s : Set P} (h : Collinear k s) :
    FiniteDimensional k (affineSpan k s).direction :=
  (direction_affineSpan k s).symm ▸ h.finiteDimensional_vectorSpan

variable (k P)

/-- The empty set is collinear. -/
/-
**collinear_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：collinear_empty : Collinear k (∅ : Set P)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `collinear_iff_rank_le_one`：collinear_iff_rank_le_one (s : Set P) : Colli
near k s ↔ Module.rank k (vectorSpan k s) <= 1
· 使用定理 `vectorSpan_empty`：vectorSpan_empty : vectorSpan k (∅ : Set P) = (⊥ : Sub
module k V)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `rank_subsingleton'`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R] 
[inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Nontrivial R] [Subsin
gleton M…
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α

--- 原说明 ---
The empty set is collinear.
-/
theorem collinear_empty : Collinear k (∅ : Set P) := by
  rw [collinear_iff_rank_le_one, vectorSpan_empty]
  simp

variable {P}

/-- A single point is collinear. -/
/-
**collinear_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：collinear_singleton (p : P) : Collinear k ({p} : Set P)
参数：p : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `collinear_iff_rank_le_one`：collinear_iff_rank_le_one (s : Set P) : Colli
near k s ↔ Module.rank k (vectorSpan k s) <= 1
· 使用定理 `vectorSpan_singleton`：vectorSpan_singleton (p : P) : vectorSpan k ({p} :
 Set P) = ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `rank_subsingleton'`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R] 
[inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Nontrivial R] [Subsin
gleton M…
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α

--- 原说明 ---
A single point is collinear.
-/
theorem collinear_singleton (p : P) : Collinear k ({p} : Set P) := by
  rw [collinear_iff_rank_le_one, vectorSpan_singleton]
  simp

variable {k}

/-- Given a point `p₀` in a set of points, that set is collinear if and
only if the points can all be expressed as multiples of the same
vector, added to `p₀`. -/
/-
**collinear_iff_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：collinear_iff_of_mem {s : Set P} {p₀ : P} (h : p₀ in s) : Collinear k s ↔ 
exists v : V, forall p in s, exists r : k, p = r • v +ᵥ p₀
参数：h : p₀ in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `vsub_mem_vectorSpan`：vsub_mem_vectorSpan {s : Set P} {p₁ p₂ : P} (hp₁ : 
p₁ in s) (hp₂ : p₂ in s) : p₁ -ᵥ p₂ in vectorSpan k s
· 使用定理 `eq_vadd_iff_vsub_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] (p₁ : P) (g : G) (p₂ : P),   p₁ = g +ᵥ p₂ ↔ p₁ -ᵥ p₂ = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vectorSpan_eq_span_vsub_set_right`：vectorSpan_eq_span_vsub_set_right {s 
: Set P} {p : P} (hp : p in s) : vectorSpan k s = Submodule.span k ((· -ᵥ p) '' 
s)
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Set.subset_def`：subset_def : (s subseteq t) = forall x, x in s -> x in t
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B

--- 原说明 ---
Given a point `p₀` in a set of points, that set is collinear if and
only if the points can all be expressed as multiples of the same
vector, added to `p₀`.
-/
theorem collinear_iff_of_mem {s : Set P} {p₀ : P} (h : p₀ ∈ s) :
    Collinear k s ↔ ∃ v : V, ∀ p ∈ s, ∃ r : k, p = r • v +ᵥ p₀ := by
  simp_rw [collinear_iff_rank_le_one, rank_submodule_le_one_iff', Submodule.le_span_singleton_iff]
  constructor
  · rintro ⟨v₀, hv⟩
    use v₀
    intro p hp
    obtain ⟨r, hr⟩ := hv (p -ᵥ p₀) (vsub_mem_vectorSpan k hp h)
    use r
    rw [eq_vadd_iff_vsub_eq]
    exact hr.symm
  · rintro ⟨v, hp₀v⟩
    use v
    intro w hw
    have hs : vectorSpan k s ≤ k ∙ v := by
      rw [vectorSpan_eq_span_vsub_set_right k h, Submodule.span_le, Set.subset_def]
      intro x hx
      rw [SetLike.mem_coe, Submodule.mem_span_singleton]
      rw [Set.mem_image] at hx
      rcases hx with ⟨p, hp, rfl⟩
      rcases hp₀v p hp with ⟨r, rfl⟩
      use r
      simp
    have hw' := SetLike.le_def.1 hs hw
    rwa [Submodule.mem_span_singleton] at hw'

/-- A set of points is collinear if and only if they can all be
expressed as multiples of the same vector, added to the same base
point. -/
/-
**collinear_iff_exists_forall_eq_smul_vadd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：collinear_iff_exists_forall_eq_smul_vadd (s : Set P) : Collinear k s ↔ exi
sts (p₀ : P) (v : V), forall p in s, exists r : k, p = r • v +ᵥ p₀
参数：s : Set P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `collinear_iff_of_mem`：collinear_iff_of_mem {s : Set P} {p₀ : P} (h : p₀ 
in s) : Collinear k s ↔ exists v : V, forall p in s, exists r : k, p = r • v +ᵥ 
p₀
· 使用定理 `vadd_vadd`：∀ {M : Type u_1} {α : Type u_5} [inst : AddMonoid M] [inst_1 
: AddAction M α] (a₁ a₂ : M) (b : α),   a₁ +ᵥ a₂ +ᵥ b = (a₁ + a₂) +ᵥ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A set of points is collinear if and only if they can all be
expressed as multiples of the same vector, added to the same base
point.
-/
theorem collinear_iff_exists_forall_eq_smul_vadd (s : Set P) :
    Collinear k s ↔ ∃ (p₀ : P) (v : V), ∀ p ∈ s, ∃ r : k, p = r • v +ᵥ p₀ := by
  rcases Set.eq_empty_or_nonempty s with (rfl | ⟨⟨p₁, hp₁⟩⟩)
  · simp [collinear_empty]
  · rw [collinear_iff_of_mem hp₁]
    constructor
    · exact fun h => ⟨p₁, h⟩
    · rintro ⟨p, v, hv⟩
      use v
      intro p₂ hp₂
      rcases hv p₂ hp₂ with ⟨r, rfl⟩
      rcases hv p₁ hp₁ with ⟨r₁, rfl⟩
      use r - r₁
      simp [vadd_vadd, ← add_smul]

variable (k) in
/-- Two points are collinear. -/
/-
**collinear_pair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：collinear_pair (p₁ p₂ : P) : Collinear k ({p₁, p₂} : Set P)
参数：p₁ p₂ : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `collinear_iff_exists_forall_eq_smul_vadd`：collinear_iff_exists_forall_eq
_smul_vadd (s : Set P) : Collinear k s ↔ exists (p₀ : P) (v : V), forall p in s,
 exists r : k, p = r • v +ᵥ p₀
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `Set.mem_insert_iff`：mem_insert_iff {x a : α} {s : Set α} : x in insert a
 s ↔ x = a ∨ x in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `zero_vadd`：∀ (M : Type u_1) {α : Type u_5} [inst : AddMonoid M] [inst_1 
: AddAction M α] (b : α), 0 +ᵥ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁

--- 原说明 ---
Two points are collinear.
-/
theorem collinear_pair (p₁ p₂ : P) : Collinear k ({p₁, p₂} : Set P) := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  use p₁, p₂ -ᵥ p₁
  intro p hp
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with hp | hp
  · use 0
    simp [hp]
  · use 1
    simp [hp]

/-- Three points are affinely independent if and only if they are not
collinear. -/
/-
**affineIndependent_iff_not_collinear** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineIndependent_iff_not_collinear {p : Fin 3 -> P} : AffineIndependent k
 p ↔ ¬Collinear k (Set.range p)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `collinear_iff_finrank_le_one`：collinear_iff_finrank_le_one {s : Set P} [
FiniteDimensional k (vectorSpan k s)] : Collinear k s ↔ finrank k (vectorSpan k 
s) <= 1
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `affineIndependent_iff_not_finrank_vectorSpan_le`：affineIndependent_iff_n
ot_finrank_vectorSpan_le [Fintype ι] (p : ι -> P) {n : Nat} (hc : Fintype.card ι
 = n + 2) : AffineIndependent k p ↔ ¬…
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Three points are affinely independent if and only if they are not
collinear.
-/
theorem affineIndependent_iff_not_collinear {p : Fin 3 → P} :
    AffineIndependent k p ↔ ¬Collinear k (Set.range p) := by
  rw [collinear_iff_finrank_le_one,
    affineIndependent_iff_not_finrank_vectorSpan_le k p (Fintype.card_fin 3)]

/-- Three points are collinear if and only if they are not affinely
independent. -/
/-
**collinear_iff_not_affineIndependent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：collinear_iff_not_affineIndependent {p : Fin 3 -> P} : Collinear k (Set.ra
nge p) ↔ ¬AffineIndependent k p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `collinear_iff_finrank_le_one`：collinear_iff_finrank_le_one {s : Set P} [
FiniteDimensional k (vectorSpan k s)] : Collinear k s ↔ finrank k (vectorSpan k 
s) <= 1
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `finrank_vectorSpan_le_iff_not_affineIndependent`：finrank_vectorSpan_le_i
ff_not_affineIndependent [Fintype ι] (p : ι -> P) {n : Nat} (hc : Fintype.card ι
 = n + 2) : finrank k (vectorSpan k (…
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Three points are collinear if and only if they are not affinely
independent.
-/
theorem collinear_iff_not_affineIndependent {p : Fin 3 → P} :
    Collinear k (Set.range p) ↔ ¬AffineIndependent k p := by
  rw [collinear_iff_finrank_le_one,
    finrank_vectorSpan_le_iff_not_affineIndependent k p (Fintype.card_fin 3)]

/-- Three points are affinely independent if and only if they are not collinear. -/
/-
**affineIndependent_iff_not_collinear_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineIndependent_iff_not_collinear_set {p₁ p₂ p₃ : P} : AffineIndependent
 k ![p₁, p₂, p₃] ↔ ¬Collinear k ({p₁, p₂, p₃} : Set P)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `affineIndependent_iff_not_collinear`：affineIndependent_iff_not_collinear
 {p : Fin 3 -> P} : AffineIndependent k p ↔ ¬Collinear k (Set.range p)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.range_cons`：range_cons (x : α) (u : Fin n -> α) : Set.range (vecC
ons x u) = {x} union Set.range u
· 使用定理 `Matrix.range_empty`：range_empty (u : Fin 0 -> α) : Set.range u = ∅
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LawfulSingleton.insert_empty_eq`：∀ {α : Type u} {β : Type v} {inst : Emp
tyCollection β} {inst_1 : Insert α β} {inst_2 : Singleton α β}   [self : LawfulS
ingleton α β] (x : α)…
· 使用定理 `Set.instLawfulSingleton`：∀ {α : Type u_1}, LawfulSingleton α (Set α)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Three points are affinely independent if and only if they are not collinear.
-/
theorem affineIndependent_iff_not_collinear_set {p₁ p₂ p₃ : P} :
    AffineIndependent k ![p₁, p₂, p₃] ↔ ¬Collinear k ({p₁, p₂, p₃} : Set P) := by
  rw [affineIndependent_iff_not_collinear]
  simp_rw [Matrix.range_cons, Matrix.range_empty, Set.singleton_union, insert_empty_eq]

/-- Three points are collinear if and only if they are not affinely independent. -/
/-
**collinear_iff_not_affineIndependent_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：collinear_iff_not_affineIndependent_set {p₁ p₂ p₃ : P} : Collinear k ({p₁,
 p₂, p₃} : Set P) ↔ ¬AffineIndependent k ![p₁, p₂, p₃]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Iff.not_left`：Iff.not_left (h : a ↔ ¬b) : ¬a ↔ b
· 使用定理 `affineIndependent_iff_not_collinear_set`：affineIndependent_iff_not_colli
near_set {p₁ p₂ p₃ : P} : AffineIndependent k ![p₁, p₂, p₃] ↔ ¬Collinear k ({p₁,
 p₂, p₃} : Set P)

--- 原说明 ---
Three points are collinear if and only if they are not affinely independent.
-/
theorem collinear_iff_not_affineIndependent_set {p₁ p₂ p₃ : P} :
    Collinear k ({p₁, p₂, p₃} : Set P) ↔ ¬AffineIndependent k ![p₁, p₂, p₃] :=
  affineIndependent_iff_not_collinear_set.not_left.symm

/-- Three points are affinely independent if and only if they are not collinear. -/
/-
**affineIndependent_iff_not_collinear_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineIndependent_iff_not_collinear_of_ne {p : Fin 3 -> P} {i₁ i₂ i₃ : Fin
 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) : AffineIndependent k p ↔
 ¬Collinear k ({p i₁, p i₂, p i₃} : Set P)
参数：h₁₂ : i₁ != i₂；h₁₃ : i₁ != i₃；h₂₃ : i₂ != i₃。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `affineIndependent_iff_not_collinear`：affineIndependent_iff_not_collinear
 {p : Fin 3 -> P} : AffineIndependent k p ↔ ¬Collinear k (Set.range p)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Set.image_insert_eq`：image_insert_eq {f : α -> β} {a : α} {s : Set α} : 
f '' insert a s = insert (f a) (f '' s)
· 使用定理 `Set.image_pair`：image_pair (f : α -> β) (a b : α) : f '' {a, b} = {f a, 
f b}
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Three points are affinely independent if and only if they are not collinear.
-/
theorem affineIndependent_iff_not_collinear_of_ne {p : Fin 3 → P} {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂)
    (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    AffineIndependent k p ↔ ¬Collinear k ({p i₁, p i₂, p i₃} : Set P) := by
  have hu : (Finset.univ : Finset (Fin 3)) = {i₁, i₂, i₃} := by decide +revert
  rw [affineIndependent_iff_not_collinear, ← Set.image_univ, ← Finset.coe_univ, hu,
    Finset.coe_insert, Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq, Set.image_pair]

/-- Three points are collinear if and only if they are not affinely independent. -/
/-
**collinear_iff_not_affineIndependent_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：collinear_iff_not_affineIndependent_of_ne {p : Fin 3 -> P} {i₁ i₂ i₃ : Fin
 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) : Collinear k ({p i₁, p i
₂, p i₃} : Set P) ↔ ¬AffineIndependent k p
参数：h₁₂ : i₁ != i₂；h₁₃ : i₁ != i₃；h₂₃ : i₂ != i₃。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Iff.not_left`：Iff.not_left (h : a ↔ ¬b) : ¬a ↔ b
· 使用定理 `affineIndependent_iff_not_collinear_of_ne`：affineIndependent_iff_not_col
linear_of_ne {p : Fin 3 -> P} {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i
₃) (h₂₃ : i₂ != i₃) : AffineInd…

--- 原说明 ---
Three points are collinear if and only if they are not affinely independent.
-/
theorem collinear_iff_not_affineIndependent_of_ne {p : Fin 3 → P} {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂)
    (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    Collinear k ({p i₁, p i₂, p i₃} : Set P) ↔ ¬AffineIndependent k p :=
  (affineIndependent_iff_not_collinear_of_ne h₁₂ h₁₃ h₂₃).not_left.symm

/-- If three points are not collinear, the first and second are different. -/
/-
**ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If three points are not collinear, the first and second are different.
-/
theorem ne₁₂_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear k ({p₁, p₂, p₃} : Set P)) :
    p₁ ≠ p₂ := by
  rintro rfl
  simp [collinear_pair] at h

/-- If three points are not collinear, the first and third are different. -/
/-
**ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If three points are not collinear, the first and third are different.
-/
theorem ne₁₃_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear k ({p₁, p₂, p₃} : Set P)) :
    p₁ ≠ p₃ := by
  rintro rfl
  simp [collinear_pair] at h

/-- If three points are not collinear, the second and third are different. -/
/-
**ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If three points are not collinear, the second and third are different.
-/
theorem ne₂₃_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear k ({p₁, p₂, p₃} : Set P)) :
    p₂ ≠ p₃ := by
  rintro rfl
  simp [collinear_pair] at h

/-- A point in a collinear set of points lies in the affine span of any two distinct points of
that set. -/
/-
**Collinear.mem_affineSpan_of_mem_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Collinear.mem_affineSpan_of_mem_of_ne {s : Set P} (h : Collinear k s) {p₁ 
p₂ p₃ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) (hp₃ : p₃ in s) (hp₁p₂ : p₁ != p₂) : 
p₃ in line[k, p₁, p₂]
参数：h : Collinear k s；hp₁ : p₁ in s；hp₂ : p₂ in s；hp₃ : p₃ in s；hp₁p₂ : p₁ != p₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `collinear_iff_of_mem`：collinear_iff_of_mem {s : Set P} {p₀ : P} (h : p₀ 
in s) : Collinear k s ↔ exists v : V, forall p in s, exists r : k, p = r • v +ᵥ 
p₀
· 使用定理 `vadd_left_mem_affineSpan_pair`：vadd_left_mem_affineSpan_pair {p₁ p₂ : P}
 {v : V} : v +ᵥ p₁ in line[k, p₁, p₂] ↔ exists r : k, r • (p₂ -ᵥ p₁) = v
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `zero_vadd`：∀ (M : Type u_1) {α : Type u_5} [inst : AddMonoid M] [inst_1 
: AddAction M α] (b : α), 0 +ᵥ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `IsUnit.div_mul_cancel`：∀ {α : Type u} [inst : DivisionMonoid α] {b : α},
 IsUnit b → ∀ (a : α), a / b * b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
A point in a collinear set of points lies in the affine span of any two distinct
 points of
that set.
-/
theorem Collinear.mem_affineSpan_of_mem_of_ne {s : Set P} (h : Collinear k s) {p₁ p₂ p₃ : P}
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∈ s) (hp₁p₂ : p₁ ≠ p₂) : p₃ ∈ line[k, p₁, p₂] := by
  rw [collinear_iff_of_mem hp₁] at h
  rcases h with ⟨v, h⟩
  rcases h p₂ hp₂ with ⟨r₂, rfl⟩
  rcases h p₃ hp₃ with ⟨r₃, rfl⟩
  rw [vadd_left_mem_affineSpan_pair]
  refine ⟨r₃ / r₂, ?_⟩
  have h₂ : r₂ ≠ 0 := by
    rintro rfl
    simp at hp₁p₂
  simp [smul_smul, h₂]

/-- The affine span of any two distinct points of a collinear set of points equals the affine
span of the whole set. -/
/-
**Collinear.affineSpan_eq_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Collinear.affineSpan_eq_of_ne {s : Set P} (h : Collinear k s) {p₁ p₂ : P} 
(hp₁ : p₁ in s) (hp₂ : p₂ in s) (hp₁p₂ : p₁ != p₂) : line[k, p₁, p₂] = affineSpa
n k s
参数：h : Collinear k s；hp₁ : p₁ in s；hp₂ : p₂ in s；hp₁p₂ : p₁ != p₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `affineSpan_mono`：affineSpan_mono {s₁ s₂ : Set P} (h : s₁ subseteq s₂) : 
affineSpan k s₁ <= affineSpan k s₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.insert_subset_iff`：insert_subset_iff : insert a s subseteq t ↔ a in 
t ∧ s subseteq t
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `affineSpan_le`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_3} [inst : Ri
ng k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [S : AddTorsor V 
P] …
· 使用定理 `Collinear.mem_affineSpan_of_mem_of_ne`：Collinear.mem_affineSpan_of_mem_o
f_ne {s : Set P} (h : Collinear k s) {p₁ p₂ p₃ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in
 s) (hp₃ : p₃ in s) (hp₁p₂ …

--- 原说明 ---
The affine span of any two distinct points of a collinear set of points equals t
he affine
span of the whole set.
-/
theorem Collinear.affineSpan_eq_of_ne {s : Set P} (h : Collinear k s) {p₁ p₂ : P} (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) (hp₁p₂ : p₁ ≠ p₂) : line[k, p₁, p₂] = affineSpan k s :=
  le_antisymm (affineSpan_mono _ (Set.insert_subset_iff.2 ⟨hp₁, Set.singleton_subset_iff.2 hp₂⟩))
    (affineSpan_le.2 fun _ hp => h.mem_affineSpan_of_mem_of_ne hp₁ hp₂ hp hp₁p₂)

/-- Given a collinear set of points, and two distinct points `p₂` and `p₃` in it, a point `p₁` is
collinear with the set if and only if it is collinear with `p₂` and `p₃`. -/
/-
**Collinear.collinear_insert_iff_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Collinear.collinear_insert_iff_of_ne {s : Set P} (h : Collinear k s) {p₁ p
₂ p₃ : P} (hp₂ : p₂ in s) (hp₃ : p₃ in s) (hp₂p₃ : p₂ != p₃) : Collinear k (inse
rt p₁ s) ↔ Collinear k ({p₁, p₂, p₃} : Set P)
参数：h : Collinear k s；hp₂ : p₂ in s；hp₃ : p₃ in s；hp₂p₃ : p₂ != p₃。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s
· 使用定理 `affineSpan_insert_affineSpan`：affineSpan_insert_affineSpan (p : P) (ps :
 Set P) : affineSpan k (insert p (affineSpan k ps : Set P)) = affineSpan k (inse
rt p ps)
· 使用定理 `Collinear.affineSpan_eq_of_ne`：Collinear.affineSpan_eq_of_ne {s : Set P}
 (h : Collinear k s) {p₁ p₂ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) (hp₁p₂ : p₁ != 
p₂) : line[k, p₁, p…
· 使用定理 `Collinear.eq_1`：∀ (k : Type u_1) {V : Type u_2} {P : Type u_3} [inst : D
ivisionRing k] [inst_1 : AddCommGroup V]   [inst_2 : _root_.Module k V] [inst_3 
: Ad…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Given a collinear set of points, and two distinct points `p₂` and `p₃` in it, a 
point `p₁` is
collinear with the set if and only if it is collinear with `p₂` and `p₃`.
-/
theorem Collinear.collinear_insert_iff_of_ne {s : Set P} (h : Collinear k s) {p₁ p₂ p₃ : P}
    (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∈ s) (hp₂p₃ : p₂ ≠ p₃) :
    Collinear k (insert p₁ s) ↔ Collinear k ({p₁, p₂, p₃} : Set P) := by
  have hv : vectorSpan k (insert p₁ s) = vectorSpan k ({p₁, p₂, p₃} : Set P) := by
    conv_rhs => rw [← direction_affineSpan, ← affineSpan_insert_affineSpan]
    rw [← direction_affineSpan, ← affineSpan_insert_affineSpan, h.affineSpan_eq_of_ne hp₂ hp₃ hp₂p₃]
  rw [Collinear, Collinear, hv]

/-- Adding a point in the affine span of a set does not change whether that set is collinear. -/
/-
**collinear_insert_iff_of_mem_affineSpan** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：collinear_insert_iff_of_mem_affineSpan {s : Set P} {p : P} (h : p in affin
eSpan k s) : Collinear k (insert p s) ↔ Collinear k s
参数：h : p in affineSpan k s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Collinear.eq_1`：∀ (k : Type u_1) {V : Type u_2} {P : Type u_3} [inst : D
ivisionRing k] [inst_1 : AddCommGroup V]   [inst_2 : _root_.Module k V] [inst_3 
: Ad…
· 使用定理 `vectorSpan_insert_eq_vectorSpan`：vectorSpan_insert_eq_vectorSpan {p : P}
 {ps : Set P} (h : p in affineSpan k ps) : vectorSpan k (insert p ps) = vectorSp
an k ps
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Adding a point in the affine span of a set does not change whether that set is c
ollinear.
-/
theorem collinear_insert_iff_of_mem_affineSpan {s : Set P} {p : P} (h : p ∈ affineSpan k s) :
    Collinear k (insert p s) ↔ Collinear k s := by
  rw [Collinear, Collinear, vectorSpan_insert_eq_vectorSpan h]

/-- If a point lies in the affine span of two points, those three points are collinear. -/
/-
**collinear_insert_of_mem_affineSpan_pair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：collinear_insert_of_mem_affineSpan_pair {p₁ p₂ p₃ : P} (h : p₁ in line[k, 
p₂, p₃]) : Collinear k ({p₁, p₂, p₃} : Set P)
参数：h : p₁ in line[k, p₂, p₃]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `collinear_insert_iff_of_mem_affineSpan`：collinear_insert_iff_of_mem_affi
neSpan {s : Set P} {p : P} (h : p in affineSpan k s) : Collinear k (insert p s) 
↔ Collinear k s
· 使用定理 `collinear_pair`：collinear_pair (p₁ p₂ : P) : Collinear k ({p₁, p₂} : Set
 P)

--- 原说明 ---
If a point lies in the affine span of two points, those three points are colline
ar.
-/
theorem collinear_insert_of_mem_affineSpan_pair {p₁ p₂ p₃ : P} (h : p₁ ∈ line[k, p₂, p₃]) :
    Collinear k ({p₁, p₂, p₃} : Set P) := by
  rw [collinear_insert_iff_of_mem_affineSpan h]
  exact collinear_pair _ _ _

/-- If two points lie in the affine span of two points, those four points are collinear. -/
/-
**collinear_insert_insert_of_mem_affineSpan_pair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：collinear_insert_insert_of_mem_affineSpan_pair {p₁ p₂ p₃ p₄ : P} (h₁ : p₁ 
in line[k, p₃, p₄]) (h₂ : p₂ in line[k, p₃, p₄]) : Collinear k ({p₁, p₂, p₃, p₄}
 : Set P)
参数：h₁ : p₁ in line[k, p₃, p₄]；h₂ : p₂ in line[k, p₃, p₄]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `collinear_insert_iff_of_mem_affineSpan`：collinear_insert_iff_of_mem_affi
neSpan {s : Set P} {p : P} (h : p in affineSpan k s) : Collinear k (insert p s) 
↔ Collinear k s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AffineSubspace.le_def'`：le_def' (s₁ s₂ : AffineSubspace k P) : s₁ <= s₂ 
↔ forall p in s₁, p in s₂
· 使用定理 `affineSpan_mono`：affineSpan_mono {s₁ s₂ : Set P} (h : s₁ subseteq s₂) : 
affineSpan k s₁ <= affineSpan k s₂
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `collinear_pair`：collinear_pair (p₁ p₂ : P) : Collinear k ({p₁, p₂} : Set
 P)

--- 原说明 ---
If two points lie in the affine span of two points, those four points are collin
ear.
-/
theorem collinear_insert_insert_of_mem_affineSpan_pair {p₁ p₂ p₃ p₄ : P} (h₁ : p₁ ∈ line[k, p₃, p₄])
    (h₂ : p₂ ∈ line[k, p₃, p₄]) : Collinear k ({p₁, p₂, p₃, p₄} : Set P) := by
  rw [collinear_insert_iff_of_mem_affineSpan
      ((AffineSubspace.le_def' _ _).1 (affineSpan_mono k (Set.subset_insert _ _)) _ h₁),
    collinear_insert_iff_of_mem_affineSpan h₂]
  exact collinear_pair _ _ _

/-- If three points lie in the affine span of two points, those five points are collinear. -/
/-
**collinear_insert_insert_insert_of_mem_affineSpan_pair** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：collinear_insert_insert_insert_of_mem_affineSpan_pair {p₁ p₂ p₃ p₄ p₅ : P}
 (h₁ : p₁ in line[k, p₄, p₅]) (h₂ : p₂ in line[k, p₄, p₅]) (h₃ : p₃ in line[k, p
₄, p₅]) : Collinear k ({p₁, p₂, p₃, p₄, p₅} : Set P)
参数：h₁ : p₁ in line[k, p₄, p₅]；h₂ : p₂ in line[k, p₄, p₅]；h₃ : p₃ in line[k, p₄, 
p₅]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `collinear_insert_iff_of_mem_affineSpan`：collinear_insert_iff_of_mem_affi
neSpan {s : Set P} {p : P} (h : p in affineSpan k s) : Collinear k (insert p s) 
↔ Collinear k s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AffineSubspace.le_def'`：le_def' (s₁ s₂ : AffineSubspace k P) : s₁ <= s₂ 
↔ forall p in s₁, p in s₂
· 使用定理 `affineSpan_mono`：affineSpan_mono {s₁ s₂ : Set P} (h : s₁ subseteq s₂) : 
affineSpan k s₁ <= affineSpan k s₂
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `collinear_pair`：collinear_pair (p₁ p₂ : P) : Collinear k ({p₁, p₂} : Set
 P)

--- 原说明 ---
If three points lie in the affine span of two points, those five points are coll
inear.
-/
theorem collinear_insert_insert_insert_of_mem_affineSpan_pair {p₁ p₂ p₃ p₄ p₅ : P}
    (h₁ : p₁ ∈ line[k, p₄, p₅]) (h₂ : p₂ ∈ line[k, p₄, p₅]) (h₃ : p₃ ∈ line[k, p₄, p₅]) :
    Collinear k ({p₁, p₂, p₃, p₄, p₅} : Set P) := by
  rw [collinear_insert_iff_of_mem_affineSpan
      ((AffineSubspace.le_def' _ _).1
        (affineSpan_mono k ((Set.subset_insert _ _).trans (Set.subset_insert _ _))) _ h₁),
    collinear_insert_iff_of_mem_affineSpan
      ((AffineSubspace.le_def' _ _).1 (affineSpan_mono k (Set.subset_insert _ _)) _ h₂),
    collinear_insert_iff_of_mem_affineSpan h₃]
  exact collinear_pair _ _ _

/-- If three points lie in the affine span of two points, the first four points are collinear. -/
/-
**collinear_insert_insert_insert_left_of_mem_affineSpan_pair** 是 Mathlib 中的一个定理，
位于命名空间 ``。
形式化陈述：collinear_insert_insert_insert_left_of_mem_affineSpan_pair {p₁ p₂ p₃ p₄ p₅
 : P} (h₁ : p₁ in line[k, p₄, p₅]) (h₂ : p₂ in line[k, p₄, p₅]) (h₃ : p₃ in line
[k, p₄, p₅]) : Collinear k ({p₁, p₂, p₃, p₄} : Set P)
参数：h₁ : p₁ in line[k, p₄, p₅]；h₂ : p₂ in line[k, p₄, p₅]；h₃ : p₃ in line[k, p₄, 
p₅]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Collinear.subset`：Collinear.subset {s₁ s₂ : Set P} (hs : s₁ subseteq s₂)
 (h : Collinear k s₂) : Collinear k s₁
· 使用定理 `Set.insert_subset_insert`：insert_subset_insert (h : s subseteq t) : inse
rt a s subseteq insert a t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `collinear_insert_insert_insert_of_mem_affineSpan_pair`：collinear_insert_
insert_insert_of_mem_affineSpan_pair {p₁ p₂ p₃ p₄ p₅ : P} (h₁ : p₁ in line[k, p₄
, p₅]) (h₂ : p₂ in line[k, p₄, p₅]) (h₃ : p…

--- 原说明 ---
If three points lie in the affine span of two points, the first four points are 
collinear.
-/
theorem collinear_insert_insert_insert_left_of_mem_affineSpan_pair {p₁ p₂ p₃ p₄ p₅ : P}
    (h₁ : p₁ ∈ line[k, p₄, p₅]) (h₂ : p₂ ∈ line[k, p₄, p₅]) (h₃ : p₃ ∈ line[k, p₄, p₅]) :
    Collinear k ({p₁, p₂, p₃, p₄} : Set P) := by
  refine (collinear_insert_insert_insert_of_mem_affineSpan_pair h₁ h₂ h₃).subset ?_
  gcongr; simp

/-- If three points lie in the affine span of two points, the first three points are collinear. -/
/-
**collinear_triple_of_mem_affineSpan_pair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：collinear_triple_of_mem_affineSpan_pair {p₁ p₂ p₃ p₄ p₅ : P} (h₁ : p₁ in l
ine[k, p₄, p₅]) (h₂ : p₂ in line[k, p₄, p₅]) (h₃ : p₃ in line[k, p₄, p₅]) : Coll
inear k ({p₁, p₂, p₃} : Set P)
参数：h₁ : p₁ in line[k, p₄, p₅]；h₂ : p₂ in line[k, p₄, p₅]；h₃ : p₃ in line[k, p₄, 
p₅]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Collinear.subset`：Collinear.subset {s₁ s₂ : Set P} (hs : s₁ subseteq s₂)
 (h : Collinear k s₂) : Collinear k s₁
· 使用定理 `Set.insert_subset_insert`：insert_subset_insert (h : s subseteq t) : inse
rt a s subseteq insert a t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `collinear_insert_insert_insert_left_of_mem_affineSpan_pair`：collinear_in
sert_insert_insert_left_of_mem_affineSpan_pair {p₁ p₂ p₃ p₄ p₅ : P} (h₁ : p₁ in 
line[k, p₄, p₅]) (h₂ : p₂ in line[k, p₄, p₅]) (h…

--- 原说明 ---
If three points lie in the affine span of two points, the first three points are
 collinear.
-/
theorem collinear_triple_of_mem_affineSpan_pair {p₁ p₂ p₃ p₄ p₅ : P} (h₁ : p₁ ∈ line[k, p₄, p₅])
    (h₂ : p₂ ∈ line[k, p₄, p₅]) (h₃ : p₃ ∈ line[k, p₄, p₅]) :
    Collinear k ({p₁, p₂, p₃} : Set P) := by
  refine (collinear_insert_insert_insert_left_of_mem_affineSpan_pair h₁ h₂ h₃).subset ?_
  gcongr; simp

/-- Replacing a point in an affine independent triple with a collinear point preserves affine
independence. -/
/-
**affineIndependent_of_affineIndependent_collinear_ne** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：affineIndependent_of_affineIndependent_collinear_ne {p₁ p₂ p₃ p : P} (ha :
 AffineIndependent k ![p₁, p₂, p₃]) (hcol : Collinear k {p₂, p₃, p}) (hne : p₂ !
= p) : AffineIndependent k ![p₁, p₂, p]
参数：ha : AffineIndependent k ![p₁, p₂, p₃]；hcol : Collinear k {p₂, p₃, p}；hne : p
₂ != p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `affineIndependent_iff_not_collinear_set`：affineIndependent_iff_not_colli
near_set {p₁ p₂ p₃ : P} : AffineIndependent k ![p₁, p₂, p₃] ↔ ¬Collinear k ({p₁,
 p₂, p₃} : Set P)
· 使用定理 `collinear_insert_insert_of_mem_affineSpan_pair`：collinear_insert_insert_
of_mem_affineSpan_pair {p₁ p₂ p₃ p₄ : P} (h₁ : p₁ in line[k, p₃, p₄]) (h₂ : p₂ i
n line[k, p₃, p₄]) : Collinear k ({p…
· 使用定理 `Collinear.mem_affineSpan_of_mem_of_ne`：Collinear.mem_affineSpan_of_mem_o
f_ne {s : Set P} (h : Collinear k s) {p₁ p₂ p₃ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in
 s) (hp₃ : p₃ in s) (hp₁p₂ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Collinear.subset`：Collinear.subset {s₁ s₂ : Set P} (hs : s₁ subseteq s₂)
 (h : Collinear k s₂) : Collinear k s₁

--- 原说明 ---
Replacing a point in an affine independent triple with a collinear point preserv
es affine
independence.
-/
theorem affineIndependent_of_affineIndependent_collinear_ne {p₁ p₂ p₃ p : P}
    (ha : AffineIndependent k ![p₁, p₂, p₃]) (hcol : Collinear k {p₂, p₃, p}) (hne : p₂ ≠ p) :
    AffineIndependent k ![p₁, p₂, p] := by
  rw [affineIndependent_iff_not_collinear_set]
  by_contra h
  have h1 : Collinear k {p₁, p₃, p₂, p} := by
    apply collinear_insert_insert_of_mem_affineSpan_pair
    · apply Collinear.mem_affineSpan_of_mem_of_ne h (by simp) (by simp) (by simp) hne
    · apply Collinear.mem_affineSpan_of_mem_of_ne hcol (by simp) (by simp) (by simp) hne
  have h2 : Collinear k {p₁, p₂, p₃} := h1.subset (by grind)
  rw [affineIndependent_iff_not_collinear_set] at ha
  exact ha h2

/-- Replacing a point in an affinely independent triple with another point on the same
line preserves affine independence. -/
/-
**affineIndependent_iff_affineIndependent_collinear_ne** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：affineIndependent_iff_affineIndependent_collinear_ne {p₁ p₂ p₃ p : P} (hco
l : Collinear k {p₂, p, p₃}) (hne1 : p₂ != p) (hne2 : p₂ != p₃) : AffineIndepend
ent k ![p₁, p₂, p] ↔ AffineIndependent k ![p₁, p₂, p₃]
参数：hcol : Collinear k {p₂, p, p₃}；hne1 : p₂ != p；hne2 : p₂ != p₃。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `affineIndependent_of_affineIndependent_collinear_ne`：affineIndependent_o
f_affineIndependent_collinear_ne {p₁ p₂ p₃ p : P} (ha : AffineIndependent k ![p₁
, p₂, p₃]) (hcol : Collinear k {p₂, p₃, p…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True

--- 原说明 ---
Replacing a point in an affinely independent triple with another point on the sa
me
line preserves affine independence.
-/
theorem affineIndependent_iff_affineIndependent_collinear_ne {p₁ p₂ p₃ p : P}
    (hcol : Collinear k {p₂, p, p₃}) (hne1 : p₂ ≠ p) (hne2 : p₂ ≠ p₃) :
    AffineIndependent k ![p₁, p₂, p] ↔ AffineIndependent k ![p₁, p₂, p₃] := by
  refine ⟨fun h ↦ affineIndependent_of_affineIndependent_collinear_ne h hcol hne2,
    fun h ↦ affineIndependent_of_affineIndependent_collinear_ne h ?_ hne1⟩
  convert! hcol using 1
  aesop

variable (k) in
/-- A set of points is coplanar if their `vectorSpan` has dimension at most `2`. -/
/-
**Coplanar** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Coplanar (s : Set P) : Prop
参数：s : Set P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set of points is coplanar if their `vectorSpan` has dimension at most `2`.
-/
def Coplanar (s : Set P) : Prop :=
  Module.rank k (vectorSpan k s) ≤ 2

/-- The `vectorSpan` of coplanar points is finite-dimensional. -/
/-
**Coplanar.finiteDimensional_vectorSpan** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Coplanar.finiteDimensional_vectorSpan {s : Set P} (h : Coplanar k s) : Fin
iteDimensional k (vectorSpan k s)
参数：h : Coplanar k s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsNoetherian.iff_fg`：iff_fg : IsNoetherian K V ↔ Module.Finite K V
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsNoetherian.iff_rank_lt_aleph0`：iff_rank_lt_aleph0 : IsNoetherian K V ↔
 Module.rank K V < ℵ₀
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Cardinal.lt_aleph0`：lt_aleph0 {c : Cardinal} : c < ℵ₀ ↔ exists n : Nat, 
c = n

--- 原说明 ---
The `vectorSpan` of coplanar points is finite-dimensional.
-/
theorem Coplanar.finiteDimensional_vectorSpan {s : Set P} (h : Coplanar k s) :
    FiniteDimensional k (vectorSpan k s) := by
  refine IsNoetherian.iff_fg.1 (IsNoetherian.iff_rank_lt_aleph0.2 (lt_of_le_of_lt h ?_))
  exact Cardinal.lt_aleph0.2 ⟨2, rfl⟩

/-- The direction of the affine span of coplanar points is finite-dimensional. -/
/-
**Coplanar.finiteDimensional_direction_affineSpan** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Coplanar.finiteDimensional_direction_affineSpan {s : Set P} (h : Coplanar 
k s) : FiniteDimensional k (affineSpan k s).direction
参数：h : Coplanar k s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Coplanar.finiteDimensional_vectorSpan`：Coplanar.finiteDimensional_vector
Span {s : Set P} (h : Coplanar k s) : FiniteDimensional k (vectorSpan k s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s

--- 原说明 ---
The direction of the affine span of coplanar points is finite-dimensional.
-/
theorem Coplanar.finiteDimensional_direction_affineSpan {s : Set P} (h : Coplanar k s) :
    FiniteDimensional k (affineSpan k s).direction :=
  (direction_affineSpan k s).symm ▸ h.finiteDimensional_vectorSpan

/-- A set of points, whose `vectorSpan` is finite-dimensional, is coplanar if and only if their
`vectorSpan` has dimension at most `2`. -/
/-
**coplanar_iff_finrank_le_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coplanar_iff_finrank_le_two {s : Set P} [FiniteDimensional k (vectorSpan k
 s)] : Coplanar k s ↔ finrank k (vectorSpan k s) <= 2
参数：vectorSpan k s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.finrank_eq_rank`：finrank_eq_rank [Module.Finite R M] : ↑(finrank 
R M) = Module.rank R M
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K

--- 原说明 ---
A set of points, whose `vectorSpan` is finite-dimensional, is coplanar if and on
ly if their
`vectorSpan` has dimension at most `2`.
-/
theorem coplanar_iff_finrank_le_two {s : Set P} [FiniteDimensional k (vectorSpan k s)] :
    Coplanar k s ↔ finrank k (vectorSpan k s) ≤ 2 := by
  have h : Coplanar k s ↔ Module.rank k (vectorSpan k s) ≤ 2 := Iff.rfl
  rw [← finrank_eq_rank] at h
  exact mod_cast h

alias ⟨Coplanar.finrank_le_two, _⟩ := coplanar_iff_finrank_le_two

/-- A subset of a coplanar set is coplanar. -/
/-
**Coplanar.subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Coplanar.subset {s₁ s₂ : Set P} (hs : s₁ subseteq s₂) (h : Coplanar k s₂) 
: Coplanar k s₁
参数：hs : s₁ subseteq s₂；h : Coplanar k s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Submodule.rank_mono`：Submodule.rank_mono {s t : Submodule R M} (h : s <=
 t) : Module.rank R s <= Module.rank R t
· 使用定理 `vectorSpan_mono`：vectorSpan_mono {s₁ s₂ : Set P} (h : s₁ subseteq s₂) : 
vectorSpan k s₁ <= vectorSpan k s₂

--- 原说明 ---
A subset of a coplanar set is coplanar.
-/
theorem Coplanar.subset {s₁ s₂ : Set P} (hs : s₁ ⊆ s₂) (h : Coplanar k s₂) : Coplanar k s₁ :=
  (Submodule.rank_mono (vectorSpan_mono k hs)).trans h

/-- Collinear points are coplanar. -/
/-
**Collinear.coplanar** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Collinear.coplanar {s : Set P} (h : Collinear k s) : Coplanar k s
参数：h : Collinear k s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `one_le_two`：one_le_two [LE α] [ZeroLEOneClass α] [AddLeftMono α] : (1 : 
α) <= 2
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R

--- 原说明 ---
Collinear points are coplanar.
-/
theorem Collinear.coplanar {s : Set P} (h : Collinear k s) : Coplanar k s :=
  le_trans h one_le_two

variable (k) (P)

/-- The empty set is coplanar. -/
/-
**coplanar_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coplanar_empty : Coplanar k (∅ : Set P)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Collinear.coplanar`：Collinear.coplanar {s : Set P} (h : Collinear k s) :
 Coplanar k s
· 使用定理 `collinear_empty`：collinear_empty : Collinear k (∅ : Set P)

--- 原说明 ---
The empty set is coplanar.
-/
theorem coplanar_empty : Coplanar k (∅ : Set P) :=
  (collinear_empty k P).coplanar

variable {P}

/-- A single point is coplanar. -/
/-
**coplanar_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coplanar_singleton (p : P) : Coplanar k ({p} : Set P)
参数：p : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Collinear.coplanar`：Collinear.coplanar {s : Set P} (h : Collinear k s) :
 Coplanar k s
· 使用定理 `collinear_singleton`：collinear_singleton (p : P) : Collinear k ({p} : Se
t P)

--- 原说明 ---
A single point is coplanar.
-/
theorem coplanar_singleton (p : P) : Coplanar k ({p} : Set P) :=
  (collinear_singleton k p).coplanar

/-- Two points are coplanar. -/
/-
**coplanar_pair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coplanar_pair (p₁ p₂ : P) : Coplanar k ({p₁, p₂} : Set P)
参数：p₁ p₂ : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Collinear.coplanar`：Collinear.coplanar {s : Set P} (h : Collinear k s) :
 Coplanar k s
· 使用定理 `collinear_pair`：collinear_pair (p₁ p₂ : P) : Collinear k ({p₁, p₂} : Set
 P)

--- 原说明 ---
Two points are coplanar.
-/
theorem coplanar_pair (p₁ p₂ : P) : Coplanar k ({p₁, p₂} : Set P) :=
  (collinear_pair k p₁ p₂).coplanar

variable {k}

/-- Adding a point in the affine span of a set does not change whether that set is coplanar. -/
/-
**coplanar_insert_iff_of_mem_affineSpan** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coplanar_insert_iff_of_mem_affineSpan {s : Set P} {p : P} (h : p in affine
Span k s) : Coplanar k (insert p s) ↔ Coplanar k s
参数：h : p in affineSpan k s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Coplanar.eq_1`：∀ (k : Type u_1) {V : Type u_2} {P : Type u_3} [inst : Di
visionRing k] [inst_1 : AddCommGroup V]   [inst_2 : _root_.Module k V] [inst_3 :
 Ad…
· 使用定理 `vectorSpan_insert_eq_vectorSpan`：vectorSpan_insert_eq_vectorSpan {p : P}
 {ps : Set P} (h : p in affineSpan k ps) : vectorSpan k (insert p ps) = vectorSp
an k ps
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Adding a point in the affine span of a set does not change whether that set is c
oplanar.
-/
theorem coplanar_insert_iff_of_mem_affineSpan {s : Set P} {p : P} (h : p ∈ affineSpan k s) :
    Coplanar k (insert p s) ↔ Coplanar k s := by
  rw [Coplanar, Coplanar, vectorSpan_insert_eq_vectorSpan h]

end AffineSpace'

section DivisionRing

variable {k : Type*} {V : Type*} {P : Type*}

open AffineSubspace Module Module

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AffineSpace V P]

/-- Adding a point to a finite-dimensional subspace increases the dimension by at most one. -/
/-
**finrank_vectorSpan_insert_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finrank_vectorSpan_insert_le (s : AffineSubspace k P) (p : P) : finrank k 
(vectorSpan k (insert p (s : Set P))) <= finrank k s.direction + 1
参数：s : AffineSubspace k P；p : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s
· 使用定理 `affineSpan_insert_affineSpan`：affineSpan_insert_affineSpan (p : P) (ps :
 Set P) : affineSpan k (insert p (affineSpan k ps : Set P)) = affineSpan k (inse
rt p ps)
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `AffineSubspace.coe_eq_bot_iff`：coe_eq_bot_iff (Q : AffineSubspace k P) :
 (Q : Set P) = ∅ ↔ Q = ⊥
· 使用定理 `AffineSubspace.bot_coe`：bot_coe : ((⊥ : AffineSubspace k P) : Set P) = ∅
· 使用定理 `AffineSubspace.span_empty`：span_empty : affineSpan k (∅ : Set P) = ⊥
· 使用定理 `AffineSubspace.direction_bot`：direction_bot : (⊥ : AffineSubspace k P).d
irection = ⊥
· 使用定理 `finrank_bot`：finrank_bot : finrank R (⊥ : Submodule R M) = 0
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LawfulSingleton.insert_empty_eq`：∀ {α : Type u} {β : Type v} {inst : Emp
tyCollection β} {inst_1 : Insert α β} {inst_2 : Singleton α β}   [self : LawfulS
ingleton α β] (x : α)…
· 使用定理 `Set.instLawfulSingleton`：∀ {α : Type u_1}, LawfulSingleton α (Set α)
· 使用定理 `vectorSpan_singleton`：vectorSpan_singleton (p : P) : vectorSpan k ({p} :
 Set P) = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用引理 `zero_le_one'`：zero_le_one' (α) [Zero α] [One α] [LE α] [ZeroLEOneClass α
] : (0 : α) <= 1
· 使用定理 `AffineSubspace.affineSpan_coe`：affineSpan_coe (s : AffineSubspace k P) :
 affineSpan k (s : Set P) = s
· 使用定理 `AffineSubspace.direction_affineSpan_insert`：direction_affineSpan_insert 
{s : AffineSubspace k P} {p₁ p₂ : P} (hp₁ : p₁ in s) : (affineSpan k (insert p₂ 
(s : Set P))).direction = Submod…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Submodule.finrank_add_le_finrank_add_finrank`：finrank_add_le_finrank_add
_finrank (s t : Submodule K V) [FiniteDimensional K s] [FiniteDimensional K t] :
 finrank K (s ⊔ t : Submodule K V)…
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
Adding a point to a finite-dimensional subspace increases the dimension by at mo
st one.
-/
theorem finrank_vectorSpan_insert_le (s : AffineSubspace k P) (p : P) :
    finrank k (vectorSpan k (insert p (s : Set P))) ≤ finrank k s.direction + 1 := by
  by_cases hf : FiniteDimensional k s.direction; swap
  · have hf' : ¬FiniteDimensional k (vectorSpan k (insert p (s : Set P))) := by
      intro h
      have h' : s.direction ≤ vectorSpan k (insert p (s : Set P)) := by
        conv_lhs => rw [← affineSpan_coe s, direction_affineSpan]
        exact vectorSpan_mono k (Set.subset_insert _ _)
      exact hf (Submodule.finiteDimensional_of_le h')
    rw [finrank_of_infinite_dimensional hf, finrank_of_infinite_dimensional hf', zero_add]
    exact zero_le_one
  rw [← direction_affineSpan, ← affineSpan_insert_affineSpan]
  rcases (s : Set P).eq_empty_or_nonempty with (hs | ⟨p₀, hp₀⟩)
  · rw [coe_eq_bot_iff] at hs
    rw [hs, bot_coe, span_empty, bot_coe, direction_affineSpan, direction_bot, finrank_bot,
      zero_add]
    convert! zero_le_one' ℕ
    rw [← finrank_bot k V]
    convert! rfl <;> simp
  · rw [affineSpan_coe, direction_affineSpan_insert hp₀, add_comm]
    refine (Submodule.finrank_add_le_finrank_add_finrank _ _).trans ?_
    gcongr
    refine finrank_le_one ⟨p -ᵥ p₀, Submodule.mem_span_singleton_self _⟩ fun v => ?_
    have h := v.property
    rw [Submodule.mem_span_singleton] at h
    rcases h with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    ext
    exact hc

variable (k) in
/-- Adding a point to a set with a finite-dimensional span increases the dimension by at most
one. -/
/-
**finrank_vectorSpan_insert_le_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finrank_vectorSpan_insert_le_set (s : Set P) (p : P) : finrank k (vectorSp
an k (insert p s)) <= finrank k (vectorSpan k s) + 1
参数：s : Set P；p : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s
· 使用定理 `affineSpan_insert_affineSpan`：affineSpan_insert_affineSpan (p : P) (ps :
 Set P) : affineSpan k (insert p (affineSpan k ps : Set P)) = affineSpan k (inse
rt p ps)
· 使用定理 `finrank_vectorSpan_insert_le`：finrank_vectorSpan_insert_le (s : AffineSu
bspace k P) (p : P) : finrank k (vectorSpan k (insert p (s : Set P))) <= finrank
 k s.direction + 1

--- 原说明 ---
Adding a point to a set with a finite-dimensional span increases the dimension b
y at most
one.
-/
theorem finrank_vectorSpan_insert_le_set (s : Set P) (p : P) :
    finrank k (vectorSpan k (insert p s)) ≤ finrank k (vectorSpan k s) + 1 := by
  rw [← direction_affineSpan, ← affineSpan_insert_affineSpan, direction_affineSpan,
    ← direction_affineSpan _ s]
  exact finrank_vectorSpan_insert_le ..

/-- Adding a point to a collinear set produces a coplanar set. -/
/-
**Collinear.coplanar_insert** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Collinear.coplanar_insert {s : Set P} (h : Collinear k s) (p : P) : Coplan
ar k (insert p s)
参数：h : Collinear k s；p : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Collinear.finiteDimensional_vectorSpan`：Collinear.finiteDimensional_vect
orSpan {s : Set P} (h : Collinear k s) : FiniteDimensional k (vectorSpan k s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `coplanar_iff_finrank_le_two`：coplanar_iff_finrank_le_two {s : Set P} [Fi
niteDimensional k (vectorSpan k s)] : Coplanar k s ↔ finrank k (vectorSpan k s) 
<= 2
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `finrank_vectorSpan_insert_le_set`：finrank_vectorSpan_insert_le_set (s : 
Set P) (p : P) : finrank k (vectorSpan k (insert p s)) <= finrank k (vectorSpan 
k s) + 1
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Collinear.finrank_le_one`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_3}
 [inst : DivisionRing k] [inst_1 : AddCommGroup V]   [inst_2 : _root_.Module k V
] [inst_3 : Ad…

--- 原说明 ---
Adding a point to a collinear set produces a coplanar set.
-/
theorem Collinear.coplanar_insert {s : Set P} (h : Collinear k s) (p : P) :
    Coplanar k (insert p s) := by
  have : FiniteDimensional k { x // x ∈ vectorSpan k s } := h.finiteDimensional_vectorSpan
  grw [coplanar_iff_finrank_le_two, finrank_vectorSpan_insert_le_set, h.finrank_le_one]

/-- A set of points in a two-dimensional space is coplanar. -/
/-
**coplanar_of_finrank_eq_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coplanar_of_finrank_eq_two (s : Set P) (h : finrank k V = 2) : Coplanar k 
s
参数：s : Set P；h : finrank k V = 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteDimensional.of_finrank_eq_succ`：of_finrank_eq_succ {n : Nat} (hn :
 finrank K V = n.succ) : FiniteDimensional K V
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `coplanar_iff_finrank_le_two`：coplanar_iff_finrank_le_two {s : Set P} [Fi
niteDimensional k (vectorSpan k s)] : Coplanar k s ↔ finrank k (vectorSpan k s) 
<= 2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.finrank_le`：Submodule.finrank_le [Module.Finite R M] (s : Subm
odule R M) : finrank R s <= finrank R M
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K

--- 原说明 ---
A set of points in a two-dimensional space is coplanar.
-/
theorem coplanar_of_finrank_eq_two (s : Set P) (h : finrank k V = 2) : Coplanar k s := by
  have : FiniteDimensional k V := .of_finrank_eq_succ h
  rw [coplanar_iff_finrank_le_two, ← h]
  exact Submodule.finrank_le _

/-- A set of points in a two-dimensional space is coplanar. -/
/-
**coplanar_of_fact_finrank_eq_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coplanar_of_fact_finrank_eq_two (s : Set P) [h : Fact (finrank k V = 2)] :
 Coplanar k s
参数：s : Set P；finrank k V = 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `coplanar_of_finrank_eq_two`：coplanar_of_finrank_eq_two (s : Set P) (h : 
finrank k V = 2) : Coplanar k s
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p

--- 原说明 ---
A set of points in a two-dimensional space is coplanar.
-/
theorem coplanar_of_fact_finrank_eq_two (s : Set P) [h : Fact (finrank k V = 2)] : Coplanar k s :=
  coplanar_of_finrank_eq_two s h.out

variable (k)

/-- Three points are coplanar. -/
/-
**coplanar_triple** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coplanar_triple (p₁ p₂ p₃ : P) : Coplanar k ({p₁, p₂, p₃} : Set P)
参数：p₁ p₂ p₃ : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Collinear.coplanar_insert`：Collinear.coplanar_insert {s : Set P} (h : Co
llinear k s) (p : P) : Coplanar k (insert p s)
· 使用定理 `collinear_pair`：collinear_pair (p₁ p₂ : P) : Collinear k ({p₁, p₂} : Set
 P)

--- 原说明 ---
Three points are coplanar.
-/
theorem coplanar_triple (p₁ p₂ p₃ : P) : Coplanar k ({p₁, p₂, p₃} : Set P) :=
  (collinear_pair k p₂ p₃).coplanar_insert p₁

/-- For a simplex, the centroid, a vertex, and the corresponding `faceOppositeCentroid` are
collinear. -/
/-
**Affine.Simplex.collinear_point_centroid_faceOppositeCentroid** 是 Mathlib 中的一个定
理，位于命名空间 ``。
形式化陈述：Affine.Simplex.collinear_point_centroid_faceOppositeCentroid [CharZero k] 
{n : Nat} [NeZero n] (s : Simplex k P n) (i : Fin (n + 1)) : Collinear k {s.poin
ts i, s.centroid, s.faceOppositeCentroid i}
参数：s : Simplex k P n；i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `collinear_insert_of_mem_affineSpan_pair`：collinear_insert_of_mem_affineS
pan_pair {p₁ p₂ p₃ : P} (h : p₁ in line[k, p₂, p₃]) : Collinear k ({p₁, p₂, p₃} 
: Set P)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `neg_smul_neg`：neg_smul_neg : -r • -x = r • x
· 使用定理 `Affine.Simplex.point_vsub_centroid_eq_smul_vsub`：point_vsub_centroid_eq_
smul_vsub [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) : s.points i -ᵥ s.c
entroid = (n : k) • (s.centroid -ᵥ s.…
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
· 使用定理 `smul_vsub_vadd_mem_affineSpan_pair`：smul_vsub_vadd_mem_affineSpan_pair (
r : k) (p₁ p₂ : P) : r • (p₂ -ᵥ p₁) +ᵥ p₁ in line[k, p₁, p₂]

--- 原说明 ---
For a simplex, the centroid, a vertex, and the corresponding `faceOppositeCentro
id` are
collinear.
-/
theorem Affine.Simplex.collinear_point_centroid_faceOppositeCentroid [CharZero k] {n : ℕ} [NeZero n]
    (s : Simplex k P n) (i : Fin (n + 1)) :
    Collinear k {s.points i, s.centroid, s.faceOppositeCentroid i} := by
  apply collinear_insert_of_mem_affineSpan_pair
  have h : s.points i = (-n : k) • (s.faceOppositeCentroid i -ᵥ s.centroid) +ᵥ s.centroid := by
    rw [← neg_vsub_eq_vsub_rev, neg_smul_neg, ← point_vsub_centroid_eq_smul_vsub, vsub_vadd]
  rw [h]
  exact smul_vsub_vadd_mem_affineSpan_pair _ _ _

end DivisionRing

namespace AffineBasis

universe u₁ u₂ u₃ u₄

variable {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type u₄}
variable [AddCommGroup V] [AffineSpace V P]

section DivisionRing

variable [DivisionRing k] [Module k V]

/-
**AffineBasis.finiteDimensional** 是 Mathlib 中的一个定理，位于命名空间 `AffineBasis`。
形式化陈述：∀ {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type u₄} [inst : AddCommG
roup V] [inst_1 : AddTorsor V P]   [inst_2 : DivisionRing k] [inst_3 : _root_.Mo
dule k V] [Finite ι] (b : AffineBasis ι k P), FiniteDimensional k V
参数：b : AffineBasis ι k P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineBasis.nonempty`：∀ {ι : Type u_1} {k : Type u_5} {V : Type u_6} {P 
: Type u_7} [inst : AddCommGroup V] [inst_1 : AddTorsor V P]   [inst_2 : Ring k]
 [inst_3 :…
· 使用定理 `Module.Basis.finiteDimensional_of_finite`：∀ {K : Type u} {V : Type v} [i
nst : DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V] {ι 
: Type w}   [Finite ι] (h : Mo…
-/
protected theorem finiteDimensional [Finite ι] (b : AffineBasis ι k P) : FiniteDimensional k V :=
  let ⟨i⟩ := b.nonempty
  (b.basisOf i).finiteDimensional_of_finite
/-
**AffineBasis.finite** 是 Mathlib 中的一个定理，位于命名空间 `AffineBasis`。
形式化陈述：∀ {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type u₄} [inst : AddCommG
roup V] [inst_1 : AddTorsor V P]   [inst_2 : DivisionRing k] [inst_3 : _root_.Mo
dule k V] [FiniteDimensional k V] (b : AffineBasis ι k P), Finite ι
参数：b : AffineBasis ι k P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finite_of_fin_dim_affineIndependent`：finite_of_fin_dim_affineIndependent
 [FiniteDimensional k V] {p : ι -> P} (hi : AffineIndependent k p) : Finite ι
· 使用定理 `AffineBasis.ind`：ind : AffineIndependent k b
-/
protected theorem finite [FiniteDimensional k V] (b : AffineBasis ι k P) : Finite ι :=
  finite_of_fin_dim_affineIndependent k b.ind
/-
**AffineBasis.finite_set** 是 Mathlib 中的一个定理，位于命名空间 `AffineBasis`。
形式化陈述：∀ {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type u₄} [inst : AddCommG
roup V] [inst_1 : AddTorsor V P]   [inst_2 : DivisionRing k] [inst_3 : _root_.Mo
dule k V] [FiniteDimensional k V] {s : Set ι} (b : AffineBasis (↑s) k P),   s.Fi
nite
参数：b : AffineBasis (↑s) k P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finite_set_of_fin_dim_affineIndependent`：finite_set_of_fin_dim_affineInd
ependent [FiniteDimensional k V] {s : Set ι} {f : s -> P} (hi : AffineIndependen
t k f) : s.Finite
· 使用定理 `AffineBasis.ind`：ind : AffineIndependent k b
-/
protected theorem finite_set [FiniteDimensional k V] {s : Set ι} (b : AffineBasis s k P) :
    s.Finite :=
  finite_set_of_fin_dim_affineIndependent k b.ind
/-
**AffineBasis.card_eq_finrank_add_one** 是 Mathlib 中的一个定理，位于命名空间 `AffineBasis`。
形式化陈述：card_eq_finrank_add_one [Fintype ι] (b : AffineBasis ι k P) : Fintype.card
 ι = Module.finrank k V + 1
参数：b : AffineBasis ι k P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineBasis.finiteDimensional`：∀ {ι : Type u₁} {k : Type u₂} {V : Type u
₃} {P : Type u₄} [inst : AddCommGroup V] [inst_1 : AddTorsor V P]   [inst_2 : Di
visionRing k] [inst…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one`：AffineI
ndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one [FiniteDimensional k V]
 [Fintype ι] {p : ι -> P} (hi : AffineIndependent k p…
· 使用定理 `AffineBasis.ind`：ind : AffineIndependent k b
· 使用定理 `AffineBasis.tot`：tot : affineSpan k (range b) = ⊤
-/
theorem card_eq_finrank_add_one [Fintype ι] (b : AffineBasis ι k P) :
    Fintype.card ι = Module.finrank k V + 1 :=
  have : FiniteDimensional k V := b.finiteDimensional
  b.ind.affineSpan_eq_top_iff_card_eq_finrank_add_one.mp b.tot
/-
**AffineBasis.exists_affineBasis_of_finiteDimensional** 是 Mathlib 中的一个定理，位于命名空间 
`AffineBasis`。
形式化陈述：exists_affineBasis_of_finiteDimensional [Fintype ι] [FiniteDimensional k V
] (h : Fintype.card ι = Module.finrank k V + 1) : Nonempty (AffineBasis ι k P)
参数：h : Fintype.card ι = Module.finrank k V + 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineBasis.exists_affineBasis`：exists_affineBasis : exists (s : Set P) 
(b : AffineBasis (↥s) k P), ⇑b = ((↑) : s -> P)
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用定理 `AffineBasis.finite_set`：∀ {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P :
 Type u₄} [inst : AddCommGroup V] [inst_1 : AddTorsor V P]   [inst_2 : DivisionR
ing k] [inst…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineBasis.card_eq_finrank_add_one`：card_eq_finrank_add_one [Fintype ι]
 (b : AffineBasis ι k P) : Fintype.card ι = Module.finrank k V + 1
-/
theorem exists_affineBasis_of_finiteDimensional [Fintype ι] [FiniteDimensional k V]
    (h : Fintype.card ι = Module.finrank k V + 1) : Nonempty (AffineBasis ι k P) := by
  obtain ⟨s, b, hb⟩ := AffineBasis.exists_affineBasis k V P
  lift s to Finset P using b.finite_set
  refine ⟨b.reindex <| Fintype.equivOfCardEq ?_⟩
  rw [h, ← b.card_eq_finrank_add_one]

end DivisionRing

end AffineBasis

namespace AffineMap

variable {R S V W P : Type*} [Ring R] [Ring S]
  [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V] [AddTorsor V P]
  [AddCommGroup W] [Module R W] [Module S W] [Module.Finite S W] [SMulCommClass R S W]

/-
**AffineMap.** 是 Mathlib 中的一个实例，位于命名空间 `AffineMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module.Finite S (P →ᵃ[R] W) :=
  have ⟨p⟩ : Nonempty P := inferInstance
  .equiv <| (AffineMap.toConstProdLinearMap S).symm ≪≫ₗ (AffineEquiv.vaddConst R p).congrLeftₗ S W
/-
**AffineMap.finrank_eq** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：finrank_eq [Module.Free S W] [StrongRankCondition R] [StrongRankCondition 
S] : Module.finrank S (P ->ᵃ[R] W) = (Module.finrank R V + 1) * Module.finrank S
 W
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank_prod`：Module.finrank_prod [Module.Finite R M] [Module.Fin
ite R M'] : finrank R (M × M') = finrank R M + finrank R M'
· 使用定理 `Module.finrank_linearMap`：Module.finrank_linearMap : finrank S (M ->ₗ[R]
 N) = finrank R M * finrank S N
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
-/
theorem finrank_eq [Module.Free S W] [StrongRankCondition R] [StrongRankCondition S] :
    Module.finrank S (P →ᵃ[R] W) = (Module.finrank R V + 1) * Module.finrank S W :=
  calc
    _ = Module.finrank S (V →ᵃ[R] W) :=
      have ⟨p⟩ : Nonempty P := inferInstance
      AffineEquiv.vaddConst R p |>.symm.congrLeftₗ S W |>.finrank_eq
    _ = Module.finrank S (W × (V →ₗ[R] W)) := (AffineMap.toConstProdLinearMap S).finrank_eq
    _ = (Module.finrank R V + 1) * Module.finrank S W := by
      rw [Module.finrank_prod, Module.finrank_linearMap]
      ring

end AffineMap

