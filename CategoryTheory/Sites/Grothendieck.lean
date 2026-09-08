/-
Copyright (c) 2020 Bhavik Mehta, Edward Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Edward Ayers
-/
module

public import Mathlib.CategoryTheory.Sites.Sieves
public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Order.Copy
public import Mathlib.Data.Set.Subsingleton

/-!
# Grothendieck topologies

Definition and lemmas about Grothendieck topologies.
A Grothendieck topology for a category `C` is a set of sieves on each object `X` satisfying
certain closure conditions.

Alternate versions of the axioms (in arrow form) are also described.
Two explicit examples of Grothendieck topologies are given:
* The dense topology
* The atomic topology

as well as the complete lattice structure on Grothendieck topologies (which gives two additional
explicit topologies: the discrete and trivial topologies.)

A pretopology, or a basis for a topology is defined in
`Mathlib/CategoryTheory/Sites/Pretopology.lean`. The topology associated
to a topological space is defined in `Mathlib/CategoryTheory/Sites/Spaces.lean`.

## Tags

Grothendieck topology, coverage, pretopology, site

## References

* [nLab, *Grothendieck topology*](https://ncatlab.org/nlab/show/Grothendieck+topology)
* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]

## Implementation notes

We use the definition of [nlab] and [MM92][] (Chapter III, Section 2), where Grothendieck topologies
are saturated collections of morphisms, rather than the notions of the Stacks project (00VG) and
the Elephant, in which topologies are allowed to be unsaturated, and are then completed.
TODO (BM): Add the definition from Stacks, as a pretopology, and complete to a topology.

This is so that we can produce a bijective correspondence between Grothendieck topologies on a
small category and Lawvere-Tierney topologies on its presheaf topos, as well as the equivalence
between Grothendieck topoi and left exact reflective subcategories of presheaf toposes.
-/

@[expose] public section


universe v₁ u₁ v u

namespace CategoryTheory

open Category

variable (C : Type u) [Category.{v} C]

/-- The definition of a Grothendieck topology: a set of sieves `J X` on each object `X` satisfying
three axioms:
1. For every object `X`, the maximal sieve is in `J X`.
2. If `S ∈ J X` then its pullback along any `h : Y ⟶ X` is in `J Y`.
3. If `S ∈ J X` and `R` is a sieve on `X`, then provided that the pullback of `R` along any arrow
   `f : Y ⟶ X` in `S` is in `J Y`, we have that `R` itself is in `J X`.

A sieve `S` on `X` is referred to as `J`-covering, (or just covering), if `S ∈ J X`.

See also [nlab] or [MM92] Chapter III, Section 2, Definition 1. -/
@[stacks 00Z4, wikidata Q1062242]
/-
**CategoryTheory.GrothendieckTopology** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheor
y`。
形式化陈述：(C : Type u) → [CategoryTheory.Category.{v, u} C] → Type (max u v)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The definition of a Grothendieck topology: a set of sieves `J X` on each object 
`X` satisfying
three axioms:
1. For every object `X`, the maximal sieve is in `J X`.
2. If `S ∈ J X` then its pullback along any `h : Y ⟶ X` is in `J Y`.
3. If `S ∈ J X` and `R` is a sieve on `X`, then provided that the pullback of `R
` along any arrow
   `f : Y ⟶ X` in `S` is in `J Y`, we have that `R` itself is in `J X`.

A sieve `S` on `X` is referred to as `J`-covering, (or just covering), if `S ∈ J
 X`.

See also [nlab] or [MM92] Chapter III, Section 2, Definition 1.
-/
structure GrothendieckTopology where
  /-- A Grothendieck topology on `C` consists of a set of sieves for each object `X`,
  which satisfy some axioms. -/
  sieves : ∀ X : C, Set (Sieve X)
  /-- The sieves associated to each object must contain the top sieve.
  Use `GrothendieckTopology.top_mem`. -/
  top_mem' : ∀ X, ⊤ ∈ sieves X
  /-- Stability under pullback. Use `GrothendieckTopology.pullback_stable`. -/
  pullback_stable' : ∀ ⦃X Y : C⦄ ⦃S : Sieve X⦄ (f : Y ⟶ X), S ∈ sieves X → S.pullback f ∈ sieves Y
  /-- Transitivity of sieves in a Grothendieck topology. Use `GrothendieckTopology.transitive`. -/
  transitive' :
    ∀ ⦃X⦄ ⦃S : Sieve X⦄ (_ : S ∈ sieves X) (R : Sieve X),
      (∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f → R.pullback f ∈ sieves Y) → R ∈ sieves X

namespace GrothendieckTopology

/-
**CategoryTheory.GrothendieckTopology.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.GrothendieckTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DFunLike (GrothendieckTopology C) C (fun X ↦ Set (Sieve X)) where
  coe J X := sieves J X
  coe_injective J₁ J₂ h := by cases J₁; cases J₂; congr

variable {C}
variable {X Y : C} {S R : Sieve X}
variable (J : GrothendieckTopology C)

/-- An extensionality lemma in terms of the coercion to a pi-type.
We prove this explicitly rather than deriving it so that it is in terms of the coercion rather than
the projection `.sieves`.
-/
@[ext]
/-
**CategoryTheory.GrothendieckTopology.ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.GrothendieckTopology`。
形式化陈述：ext {J₁ J₂ : GrothendieckTopology C} (h : (J₁ : forall X : C, Set (Sieve X
)) = J₂) : J₁ = J₂
参数：h : (J₁ : forall X : C, Set (Sieve X)) = J₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe

--- 原说明 ---
An extensionality lemma in terms of the coercion to a pi-type.
We prove this explicitly rather than deriving it so that it is in terms of the c
oercion rather than
the projection `.sieves`.
-/
theorem ext {J₁ J₂ : GrothendieckTopology C} (h : (J₁ : ∀ X : C, Set (Sieve X)) = J₂) : J₁ = J₂ :=
  DFunLike.coe_injective h

@[simp]
/-
**CategoryTheory.GrothendieckTopology.mem_sieves_iff_coe** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：mem_sieves_iff_coe : S in J.sieves X ↔ S in J X
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_sieves_iff_coe : S ∈ J.sieves X ↔ S ∈ J X :=
  Iff.rfl

/-- Also known as the maximality axiom. -/
@[simp, grind .]
/-
**CategoryTheory.GrothendieckTopology.top_mem** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.GrothendieckTopology`。
形式化陈述：top_mem (X : C) : ⊤ in J X
参数：X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.top_mem'`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] (self : CategoryTheory.GrothendieckTopology C) (X
 : C),   ⊤ ∈ self.sieves X

--- 原说明 ---
Also known as the maximality axiom.
-/
theorem top_mem (X : C) : ⊤ ∈ J X :=
  J.top_mem' X

/-- Also known as the stability axiom. -/
@[simp, grind .]
/-
**CategoryTheory.GrothendieckTopology.pullback_stable** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.GrothendieckTopology`。
形式化陈述：pullback_stable (f : Y ⟶ X) (hS : S in J X) : S.pullback f in J Y
参数：f : Y ⟶ X；hS : S in J X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.pullback_stable'`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] (self : CategoryTheory.GrothendieckTopolo
gy C) ⦃X Y : C⦄   ⦃S : CategoryTheory.Siev…

--- 原说明 ---
Also known as the stability axiom.
-/
theorem pullback_stable (f : Y ⟶ X) (hS : S ∈ J X) : S.pullback f ∈ J Y :=
  J.pullback_stable' f hS

variable {J} in
@[simp]
/-
**CategoryTheory.GrothendieckTopology.pullback_mem_iff_of_isIso** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：pullback_mem_iff_of_isIso {i : X ⟶ Y} [IsIso i] {S : Sieve Y} : S.pullback
 i in J _ ↔ S in J _
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Sieve.pullback_comp`：pullback_comp {f : Y ⟶ X} {g : Z ⟶ Y
} (S : Sieve X) : S.pullback (g ≫ f) = (S.pullback f).pullback g
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `CategoryTheory.Sieve.pullback_id`：pullback_id : S.pullback (𝟙 _) = S
· 使用定理 `CategoryTheory.GrothendieckTopology.pullback_stable`：pullback_stable (f 
: Y ⟶ X) (hS : S in J X) : S.pullback f in J Y
-/
lemma pullback_mem_iff_of_isIso {i : X ⟶ Y} [IsIso i] {S : Sieve Y} :
    S.pullback i ∈ J _ ↔ S ∈ J _ := by
  refine ⟨fun H ↦ ?_, J.pullback_stable i⟩
  convert! J.pullback_stable (inv i) H
  rw [← Sieve.pullback_comp, IsIso.inv_hom_id, Sieve.pullback_id]

@[grind .]
/-
**CategoryTheory.GrothendieckTopology.transitive** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.GrothendieckTopology`。
形式化陈述：transitive (hS : S in J X) (R : Sieve X) (h : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f 
-> R.pullback f in J Y) : R in J X
参数：hS : S in J X；R : Sieve X；h : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> R.pullback f in 
J Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.transitive'`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] (self : CategoryTheory.GrothendieckTopology C)
 ⦃X : C⦄   ⦃S : CategoryTheory.Sieve …
-/
theorem transitive (hS : S ∈ J X) (R : Sieve X) (h : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f → R.pullback f ∈ J Y) :
    R ∈ J X :=
  J.transitive' hS R h
/-
**CategoryTheory.GrothendieckTopology.covering_of_eq_top** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：covering_of_eq_top : S = ⊤ -> S in J X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.top_mem`：top_mem (X : C) : ⊤ in J X
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem covering_of_eq_top : S = ⊤ → S ∈ J X := fun h => h.symm ▸ J.top_mem X

/-- Given a `GrothendieckTopology` and a set of sieves `s` that is equal, form a new
`GrothendieckTopology` whose set of sieves is definitionally equal to `s`. -/
/-
**CategoryTheory.GrothendieckTopology.copy** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.GrothendieckTopology`。
形式化陈述：copy (J : GrothendieckTopology C) (s : forall X : C, Set (Sieve X)) (h : J
.sieves = s) : GrothendieckTopology C where sieves
参数：J : GrothendieckTopology C；s : forall X : C, Set (Sieve X)；h : J.sieves = s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a `GrothendieckTopology` and a set of sieves `s` that is equal, form a new
`GrothendieckTopology` whose set of sieves is definitionally equal to `s`.
-/
def copy (J : GrothendieckTopology C) (s : ∀ X : C, Set (Sieve X)) (h : J.sieves = s) :
    GrothendieckTopology C where
  sieves := s
  top_mem' := h ▸ J.top_mem'
  pullback_stable' := h ▸ J.pullback_stable'
  transitive' := h ▸ J.transitive'

@[simp]
/-
**CategoryTheory.GrothendieckTopology.sieves_copy** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.GrothendieckTopology`。
形式化陈述：sieves_copy {J : GrothendieckTopology C} {s : forall X : C, Set (Sieve X)}
 {h : J.sieves = s} : (J.copy s h).sieves = s
参数：Sieve X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sieves_copy {J : GrothendieckTopology C} {s : ∀ X : C, Set (Sieve X)} {h : J.sieves = s} :
    (J.copy s h).sieves = s :=
  rfl

@[simp]
/-
**CategoryTheory.GrothendieckTopology.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.GrothendieckTopology`。
形式化陈述：coe_copy {J : GrothendieckTopology C} {s : forall X : C, Set (Sieve X)} {h
 : J.sieves = s} : ⇑(J.copy s h) = s
参数：Sieve X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy {J : GrothendieckTopology C} {s : ∀ X : C, Set (Sieve X)} {h : J.sieves = s} :
    ⇑(J.copy s h) = s :=
  rfl
/-
**CategoryTheory.GrothendieckTopology.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.GrothendieckTopology`。
形式化陈述：copy_eq {J : GrothendieckTopology C} {s : forall X : C, Set (Sieve X)} {h 
: J.sieves = s} : J.copy s h = J
参数：Sieve X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.ext`：ext {J₁ J₂ : GrothendieckTopolo
gy C} (h : (J₁ : forall X : C, Set (Sieve X)) = J₂) : J₁ = J₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem copy_eq {J : GrothendieckTopology C} {s : ∀ X : C, Set (Sieve X)} {h : J.sieves = s} :
    J.copy s h = J :=
  GrothendieckTopology.ext h.symm

/-- If `S` is a subset of `R`, and `S` is covering, then `R` is covering as well.

See also discussion after [MM92] Chapter III, Section 2, Definition 1. -/
@[stacks 00Z5 "(2)"]
/-
**CategoryTheory.GrothendieckTopology.superset_covering** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：superset_covering (Hss : S <= R) (sjx : S in J X) : R in J X
参数：Hss : S <= R；sjx : S in J X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.transitive`：transitive (hS : S in J 
X) (R : Sieve X) (h : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> R.pullback f in J Y) : R in
 J X
· 使用定理 `CategoryTheory.GrothendieckTopology.covering_of_eq_top`：covering_of_eq_t
op : S = ⊤ -> S in J X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `CategoryTheory.Sieve.pullback_eq_top_of_mem`：pullback_eq_top_of_mem (S :
 Sieve X) {f : Y ⟶ X} : S f -> S.pullback f = ⊤
· 使用定理 `CategoryTheory.Sieve.pullback_monotone`：pullback_monotone (f : Y ⟶ X) : 
Monotone (Sieve.pullback f)

--- 原说明 ---
If `S` is a subset of `R`, and `S` is covering, then `R` is covering as well.

See also discussion after [MM92] Chapter III, Section 2, Definition 1.
-/
theorem superset_covering (Hss : S ≤ R) (sjx : S ∈ J X) : R ∈ J X := by
  apply J.transitive sjx R fun Y f hf => _
  intro Y f hf
  apply covering_of_eq_top
  rw [← top_le_iff, ← S.pullback_eq_top_of_mem hf]
  apply Sieve.pullback_monotone _ Hss

/-- The intersection of two covering sieves is covering.

See also [MM92] Chapter III, Section 2, Definition 1 (iv). -/
@[stacks 00Z5 "(1)"]
/-
**CategoryTheory.GrothendieckTopology.intersection_covering** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：intersection_covering (rj : R in J X) (sj : S in J X) : R ⊓ S in J X
参数：rj : R in J X；sj : S in J X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.transitive`：transitive (hS : S in J 
X) (R : Sieve X) (h : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> R.pullback f in J Y) : R in
 J X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Sieve.pullback_inter`：pullback_inter {f : Y ⟶ X} (S R : S
ieve X) : (S ⊓ R).pullback f = S.pullback f ⊓ R.pullback f
· 使用定理 `CategoryTheory.Sieve.pullback_eq_top_of_mem`：pullback_eq_top_of_mem (S :
 Sieve X) {f : Y ⟶ X} : S f -> S.pullback f = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b

--- 原说明 ---
The intersection of two covering sieves is covering.

See also [MM92] Chapter III, Section 2, Definition 1 (iv).
-/
theorem intersection_covering (rj : R ∈ J X) (sj : S ∈ J X) : R ⊓ S ∈ J X := by
  apply J.transitive rj _ fun Y f Hf => _
  intro Y f hf
  rw [Sieve.pullback_inter, R.pullback_eq_top_of_mem hf]
  simp [sj]

@[simp]
/-
**CategoryTheory.GrothendieckTopology.intersection_covering_iff** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：intersection_covering_iff : R ⊓ S in J X ↔ R in J X ∧ S in J X
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.superset_covering`：superset_covering
 (Hss : S <= R) (sjx : S in J X) : R in J X
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `CategoryTheory.GrothendieckTopology.intersection_covering`：intersection_
covering (rj : R in J X) (sj : S in J X) : R ⊓ S in J X
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem intersection_covering_iff : R ⊓ S ∈ J X ↔ R ∈ J X ∧ S ∈ J X :=
  ⟨fun h => ⟨J.superset_covering inf_le_left h, J.superset_covering inf_le_right h⟩, fun t =>
    intersection_covering _ t.1 t.2⟩
/-
**CategoryTheory.GrothendieckTopology.bind_covering** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.GrothendieckTopology`。
形式化陈述：bind_covering {S : Sieve X} {R : forall ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f -> Sieve 
Y} (hS : S in J X) (hR : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄ (H : S f), R H in J Y) : Sieve.b
ind S R in J X
参数：hS : S in J X；hR : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄ (H : S f), R H in J Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.transitive`：transitive (hS : S in J 
X) (R : Sieve X) (h : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> R.pullback f in J Y) : R in
 J X
· 使用定理 `CategoryTheory.GrothendieckTopology.superset_covering`：superset_covering
 (Hss : S <= R) (sjx : S in J X) : R in J X
· 使用定理 `CategoryTheory.Sieve.le_pullback_bind`：le_pullback_bind (S : Presieve X)
 (R : forall ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f -> Sieve Y) (f : Y ⟶ X) (h : S f) : R h <=
 (bind S R).pullback f
-/
theorem bind_covering {S : Sieve X} {R : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → Sieve Y} (hS : S ∈ J X)
    (hR : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (H : S f), R H ∈ J Y) : Sieve.bind S R ∈ J X :=
  J.transitive hS _ fun _ f hf => superset_covering J (Sieve.le_pullback_bind S R f hf) (hR hf)
/-
**CategoryTheory.GrothendieckTopology.bindOfArrows** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.GrothendieckTopology`。
形式化陈述：bindOfArrows {ι : Type*} {X : C} {Z : ι -> C} {f : forall i, Z i ⟶ X} {R :
 forall i, Presieve (Z i)} (h : Sieve.ofArrows Z f in J X) (hR : forall i, Sieve
.generate (R i) in J _) : Sieve.generate (Presieve.bindOfArrows Z f R) in J X
参数：Z i；h : Sieve.ofArrows Z f in J X；hR : forall i, Sieve.generate (R i) in J _。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.superset_covering`：superset_covering
 (Hss : S <= R) (sjx : S in J X) : R in J X
· 使用定理 `CategoryTheory.Presieve.bind_ofArrows_le_bindOfArrows`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {ι : Type u_1} {X : C} (Z : ι → C) (f
 : (i : ι) → Z i ⟶ X)   (R : (i : ι) → Cate…
· 使用定理 `CategoryTheory.GrothendieckTopology.bind_covering`：bind_covering {S : Si
eve X} {R : forall ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f -> Sieve Y} (hS : S in J X) (hR : fo
rall ⦃Y⦄ ⦃f : Y ⟶ X⦄ (H : S f), R H in …
· 使用定理 `CategoryTheory.GrothendieckTopology.pullback_stable`：pullback_stable (f 
: Y ⟶ X) (hS : S in J X) : S.pullback f in J Y
-/
lemma bindOfArrows {ι : Type*} {X : C} {Z : ι → C} {f : ∀ i, Z i ⟶ X} {R : ∀ i, Presieve (Z i)}
    (h : Sieve.ofArrows Z f ∈ J X) (hR : ∀ i, Sieve.generate (R i) ∈ J _) :
    Sieve.generate (Presieve.bindOfArrows Z f R) ∈ J X := by
  refine J.superset_covering (Presieve.bind_ofArrows_le_bindOfArrows _ _ _) ?_
  exact J.bind_covering h fun _ _ _ ↦ J.pullback_stable _ (hR _)

/-- The sieve `S` on `X` `J`-covers an arrow `f` to `X` if `S.pullback f ∈ J Y`.
This definition is an alternate way of presenting a Grothendieck topology.
-/
/-
**CategoryTheory.GrothendieckTopology.Covers** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.GrothendieckTopology`。
形式化陈述：Covers (S : Sieve X) (f : Y ⟶ X) : Prop
参数：S : Sieve X；f : Y ⟶ X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sieve `S` on `X` `J`-covers an arrow `f` to `X` if `S.pullback f ∈ J Y`.
This definition is an alternate way of presenting a Grothendieck topology.
-/
def Covers (S : Sieve X) (f : Y ⟶ X) : Prop :=
  S.pullback f ∈ J Y
/-
**CategoryTheory.GrothendieckTopology.covers_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.GrothendieckTopology`。
形式化陈述：covers_iff (S : Sieve X) (f : Y ⟶ X) : J.Covers S f ↔ S.pullback f in J Y
参数：S : Sieve X；f : Y ⟶ X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem covers_iff (S : Sieve X) (f : Y ⟶ X) : J.Covers S f ↔ S.pullback f ∈ J Y :=
  Iff.rfl
/-
**CategoryTheory.GrothendieckTopology.covering_iff_covers_id** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：covering_iff_covers_id (S : Sieve X) : S in J X ↔ J.Covers S (𝟙 X)
参数：S : Sieve X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Sieve.pullback_id`：pullback_id : S.pullback (𝟙 _) = S
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem covering_iff_covers_id (S : Sieve X) : S ∈ J X ↔ J.Covers S (𝟙 X) := by simp [covers_iff]

/-- The maximality axiom in 'arrow' form: Any arrow `f` in `S` is covered by `S`. -/
/-
**CategoryTheory.GrothendieckTopology.arrow_max** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.GrothendieckTopology`。
形式化陈述：arrow_max (f : Y ⟶ X) (S : Sieve X) (hf : S f) : J.Covers S f
参数：f : Y ⟶ X；S : Sieve X；hf : S f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.GrothendieckTopology.Covers.eq_1`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] {X Y : C} (J : CategoryTheory.GrothendieckTopo
logy C)   (S : CategoryTheory.Sieve X…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Sieve.mem_iff_pullback_eq_top`：mem_iff_pullback_eq_top (f
 : Y ⟶ X) : S f ↔ S.pullback f = ⊤
· 使用定理 `CategoryTheory.GrothendieckTopology.top_mem`：top_mem (X : C) : ⊤ in J X

--- 原说明 ---
The maximality axiom in 'arrow' form: Any arrow `f` in `S` is covered by `S`.
-/
theorem arrow_max (f : Y ⟶ X) (S : Sieve X) (hf : S f) : J.Covers S f := by
  rw [Covers, (Sieve.mem_iff_pullback_eq_top f).1 hf]
  apply J.top_mem

/-- The stability axiom in 'arrow' form: If `S` covers `f` then `S` covers `g ≫ f` for any `g`. -/
/-
**CategoryTheory.GrothendieckTopology.arrow_stable** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.GrothendieckTopology`。
形式化陈述：arrow_stable (f : Y ⟶ X) (S : Sieve X) (h : J.Covers S f) {Z : C} (g : Z ⟶
 Y) : J.Covers S (g ≫ f)
参数：f : Y ⟶ X；S : Sieve X；h : J.Covers S f；g : Z ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.GrothendieckTopology.covers_iff`：covers_iff (S : Sieve X)
 (f : Y ⟶ X) : J.Covers S f ↔ S.pullback f in J Y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Sieve.pullback_comp`：pullback_comp {f : Y ⟶ X} {g : Z ⟶ Y
} (S : Sieve X) : S.pullback (g ≫ f) = (S.pullback f).pullback g

--- 原说明 ---
The stability axiom in 'arrow' form: If `S` covers `f` then `S` covers `g ≫ f` f
or any `g`.
-/
theorem arrow_stable (f : Y ⟶ X) (S : Sieve X) (h : J.Covers S f) {Z : C} (g : Z ⟶ Y) :
    J.Covers S (g ≫ f) := by
  rw [covers_iff] at h ⊢
  simp [h, Sieve.pullback_comp]

/-- The transitivity axiom in 'arrow' form: If `S` covers `f` and every arrow in `S` is covered by
`R`, then `R` covers `f`.
-/
/-
**CategoryTheory.GrothendieckTopology.arrow_trans** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.GrothendieckTopology`。
形式化陈述：arrow_trans (f : Y ⟶ X) (S R : Sieve X) (h : J.Covers S f) : (forall {Z : 
C} (g : Z ⟶ X), S g -> J.Covers R g) -> J.Covers R f
参数：f : Y ⟶ X；S R : Sieve X；h : J.Covers S f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.transitive`：transitive (hS : S in J 
X) (R : Sieve X) (h : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> R.pullback f in J Y) : R in
 J X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Sieve.pullback_comp`：pullback_comp {f : Y ⟶ X} {g : Z ⟶ Y
} (S : Sieve X) : S.pullback (g ≫ f) = (S.pullback f).pullback g

--- 原说明 ---
The transitivity axiom in 'arrow' form: If `S` covers `f` and every arrow in `S`
 is covered by
`R`, then `R` covers `f`.
-/
theorem arrow_trans (f : Y ⟶ X) (S R : Sieve X) (h : J.Covers S f) :
    (∀ {Z : C} (g : Z ⟶ X), S g → J.Covers R g) → J.Covers R f := by
  intro k
  apply J.transitive h
  intro Z g hg
  rw [← Sieve.pullback_comp]
  apply k (g ≫ f) hg
/-
**CategoryTheory.GrothendieckTopology.arrow_intersect** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.GrothendieckTopology`。
形式化陈述：arrow_intersect (f : Y ⟶ X) (S R : Sieve X) (hS : J.Covers S f) (hR : J.Co
vers R f) : J.Covers (S ⊓ R) f
参数：f : Y ⟶ X；S R : Sieve X；hS : J.Covers S f；hR : J.Covers R f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Sieve.pullback_inter`：pullback_inter {f : Y ⟶ X} (S R : S
ieve X) : (S ⊓ R).pullback f = S.pullback f ⊓ R.pullback f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem arrow_intersect (f : Y ⟶ X) (S R : Sieve X) (hS : J.Covers S f) (hR : J.Covers R f) :
    J.Covers (S ⊓ R) f := by simpa [covers_iff] using And.intro hS hR

variable (C)

/-- The trivial Grothendieck topology, in which only the maximal sieve is covering. This topology is
also known as the indiscrete, coarse, or chaotic topology.

See [MM92] Chapter III, Section 2, example (a), or
https://en.wikipedia.org/wiki/Grothendieck_topology#The_discrete_and_indiscrete_topologies
-/
/-
**CategoryTheory.GrothendieckTopology.trivial** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.GrothendieckTopology`。
形式化陈述：trivial : GrothendieckTopology C where sieves _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trivial Grothendieck topology, in which only the maximal sieve is covering. 
This topology is
also known as the indiscrete, coarse, or chaotic topology.

See [MM92] Chapter III, Section 2, example (a), or
https://en.wikipedia.org/wiki/Grothendieck_topology#The_discrete_and_indiscrete_
topologies
-/
def trivial : GrothendieckTopology C where
  sieves _ := {⊤}
  top_mem' _ := rfl
  pullback_stable' X Y S f hf := by
    rw [Set.mem_singleton_iff] at hf ⊢
    simp [hf]
  transitive' X S hS R hR := by
    rw [Set.mem_singleton_iff, ← Sieve.id_mem_iff_eq_top] at hS
    simpa using hR hS

/-- The discrete Grothendieck topology, in which every sieve is covering.

See https://en.wikipedia.org/wiki/Grothendieck_topology#The_discrete_and_indiscrete_topologies.
-/
/-
**CategoryTheory.GrothendieckTopology.discrete** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.GrothendieckTopology`。
形式化陈述：discrete : GrothendieckTopology C where sieves _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The discrete Grothendieck topology, in which every sieve is covering.

See https://en.wikipedia.org/wiki/Grothendieck_topology#The_discrete_and_indiscr
ete_topologies.
-/
def discrete : GrothendieckTopology C where
  sieves _ := Set.univ
  top_mem' := by simp
  pullback_stable' X Y f := by simp
  transitive' := by simp

variable {C}
/-
**CategoryTheory.GrothendieckTopology.trivial_covering** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.GrothendieckTopology`。
形式化陈述：trivial_covering : S in trivial C X ↔ S = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
-/
theorem trivial_covering : S ∈ trivial C X ↔ S = ⊤ :=
  Set.mem_singleton_iff

@[stacks 00Z6]
/-
**CategoryTheory.GrothendieckTopology.instLEGrothendieckTopology** 是 Mathlib 中的一
个实例，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：instLEGrothendieckTopology : LE (GrothendieckTopology C) where le J₁ J₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLEGrothendieckTopology : LE (GrothendieckTopology C) where
  le J₁ J₂ := (J₁ : ∀ X : C, Set (Sieve X)) ≤ (J₂ : ∀ X : C, Set (Sieve X))
/-
**CategoryTheory.GrothendieckTopology.le_def** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.GrothendieckTopology`。
形式化陈述：le_def {J₁ J₂ : GrothendieckTopology C} : J₁ <= J₂ ↔ (J₁ : forall X : C, S
et (Sieve X)) <= J₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_def {J₁ J₂ : GrothendieckTopology C} : J₁ ≤ J₂ ↔ (J₁ : ∀ X : C, Set (Sieve X)) ≤ J₂ :=
  Iff.rfl

@[stacks 00Z6]
/-
**CategoryTheory.GrothendieckTopology.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.GrothendieckTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (GrothendieckTopology C) :=
  { instLEGrothendieckTopology with
    le_refl := fun _ => le_def.mpr le_rfl
    le_trans := fun _ _ _ h₁₂ h₂₃ => le_def.mpr (le_trans h₁₂ h₂₃)
    le_antisymm := fun _ _ h₁₂ h₂₁ => GrothendieckTopology.ext (le_antisymm h₁₂ h₂₁) }

@[stacks 00Z7]
/-
**CategoryTheory.GrothendieckTopology.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.GrothendieckTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : InfSet (GrothendieckTopology C) where
  sInf T :=
    { sieves := sInf (sieves '' T)
      top_mem' := by
        rintro X S ⟨⟨_, J, hJ, rfl⟩, rfl⟩
        simp
      pullback_stable' := by
        rintro X Y S hS f _ ⟨⟨_, J, hJ, rfl⟩, rfl⟩
        apply J.pullback_stable _ (f _ ⟨⟨_, _, hJ, rfl⟩, rfl⟩)
      transitive' := by
        rintro X S hS R h _ ⟨⟨_, J, hJ, rfl⟩, rfl⟩
        apply
          J.transitive (hS _ ⟨⟨_, _, hJ, rfl⟩, rfl⟩) _ fun Y f hf => h hf _ ⟨⟨_, _, hJ, rfl⟩, rfl⟩ }
/-
**CategoryTheory.GrothendieckTopology.mem_sInf** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.GrothendieckTopology`。
形式化陈述：mem_sInf (s : Set (GrothendieckTopology C)) {X : C} (S : Sieve X) : S in s
Inf s X ↔ forall t in s, S in t X
参数：s : Set (GrothendieckTopology C)；S : Sieve X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iInter_coe_set`：iInter_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋂ i, f i = ⋂ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_exists`：iInter_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋂ x, f x = ⋂ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.biInter_and'`：biInter_and' (p : ι' -> Prop) (q : ι -> ι' -> Prop) (s
 : forall x y, p y ∧ q x y -> Set α) : ⋂ (x : ι) (y : ι') (h : p y ∧ q x y), s x
 y h =…
· 使用定理 `Set.iInter_iInter_eq_right`：iInter_iInter_eq_right {b : β} {s : forall x
 : β, b = x -> Set α} : ⋂ (x) (h : b = x), s x h = s b rfl
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_sInf (s : Set (GrothendieckTopology C)) {X : C} (S : Sieve X) :
    S ∈ sInf s X ↔ ∀ t ∈ s, S ∈ t X := by
  change S ∈ sInf (sieves '' s) X ↔ _
  simp

@[stacks 00Z7]
/-
**CategoryTheory.GrothendieckTopology.isGLB_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.GrothendieckTopology`。
形式化陈述：isGLB_sInf (s : Set (GrothendieckTopology C)) : IsGLB s (sInf s)
参数：s : Set (GrothendieckTopology C)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGLB.of_image`：IsGLB.of_image [Preorder α] [Preorder β] {f : α -> β} (h
f : forall {x y}, f x <= f y ↔ x <= y) {s : Set α} {x : α} (hx : IsGLB (f '' s) 
(f x…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `isGLB_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] (s : Set 
α), IsGLB s (sInf s)
-/
theorem isGLB_sInf (s : Set (GrothendieckTopology C)) : IsGLB s (sInf s) := by
  refine @IsGLB.of_image _ _ _ _ sieves ?_ _ _ ?_
  · rfl
  · exact _root_.isGLB_sInf _

/-- Construct a complete lattice from the `Inf`, but make the trivial and discrete topologies
definitionally equal to the bottom and top respectively.
-/
/-
**CategoryTheory.GrothendieckTopology.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.GrothendieckTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a complete lattice from the `Inf`, but make the trivial and discrete t
opologies
definitionally equal to the bottom and top respectively.
-/
instance : CompleteLattice (GrothendieckTopology C) :=
  fast_instance% CompleteLattice.copy (completeLatticeOfInf _ isGLB_sInf) _ rfl (discrete C)
    (by
      apply le_antisymm
      · exact (completeLatticeOfInf _ isGLB_sInf).le_top (discrete C)
      · intro X S _
        apply Set.mem_univ)
    (trivial C)
    (by
      apply le_antisymm
      · intro X S hS
        rw [trivial_covering] at hS
        apply covering_of_eq_top _ hS
      · exact (completeLatticeOfInf _ isGLB_sInf).bot_le (trivial C))
    _ rfl _ rfl _ rfl sInf rfl
/-
**CategoryTheory.GrothendieckTopology.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.GrothendieckTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (GrothendieckTopology C) :=
  ⟨⊤⟩

@[simp]
/-
**CategoryTheory.GrothendieckTopology.trivial_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.GrothendieckTopology`。
形式化陈述：trivial_eq_bot : trivial C = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trivial_eq_bot : trivial C = ⊥ :=
  rfl

@[simp]
/-
**CategoryTheory.GrothendieckTopology.discrete_eq_top** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.GrothendieckTopology`。
形式化陈述：discrete_eq_top : discrete C = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem discrete_eq_top : discrete C = ⊤ :=
  rfl

@[simp]
/-
**CategoryTheory.GrothendieckTopology.bot_covering** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.GrothendieckTopology`。
形式化陈述：bot_covering : S in (⊥ : GrothendieckTopology C) X ↔ S = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.trivial_covering`：trivial_covering :
 S in trivial C X ↔ S = ⊤
-/
theorem bot_covering : S ∈ (⊥ : GrothendieckTopology C) X ↔ S = ⊤ :=
  trivial_covering

@[simp]
/-
**CategoryTheory.GrothendieckTopology.top_covering** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.GrothendieckTopology`。
形式化陈述：top_covering : S in (⊤ : GrothendieckTopology C) X
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_covering : S ∈ (⊤ : GrothendieckTopology C) X :=
  ⟨⟩
/-
**CategoryTheory.GrothendieckTopology.bot_covers** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.GrothendieckTopology`。
形式化陈述：bot_covers (S : Sieve X) (f : Y ⟶ X) : (⊥ : GrothendieckTopology C).Covers
 S f ↔ S f
参数：S : Sieve X；f : Y ⟶ X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.GrothendieckTopology.covers_iff`：covers_iff (S : Sieve X)
 (f : Y ⟶ X) : J.Covers S f ↔ S.pullback f in J Y
· 使用定理 `CategoryTheory.GrothendieckTopology.bot_covering`：bot_covering : S in (⊥
 : GrothendieckTopology C) X ↔ S = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Sieve.mem_iff_pullback_eq_top`：mem_iff_pullback_eq_top (f
 : Y ⟶ X) : S f ↔ S.pullback f = ⊤
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem bot_covers (S : Sieve X) (f : Y ⟶ X) : (⊥ : GrothendieckTopology C).Covers S f ↔ S f := by
  rw [covers_iff, bot_covering, ← Sieve.mem_iff_pullback_eq_top]

@[simp]
/-
**CategoryTheory.GrothendieckTopology.top_covers** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.GrothendieckTopology`。
形式化陈述：top_covers (S : Sieve X) (f : Y ⟶ X) : (⊤ : GrothendieckTopology C).Covers
 S f
参数：S : Sieve X；f : Y ⟶ X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem top_covers (S : Sieve X) (f : Y ⟶ X) : (⊤ : GrothendieckTopology C).Covers S f := by
  simp [covers_iff]
/-
**CategoryTheory.GrothendieckTopology.eq_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.GrothendieckTopology`。
形式化陈述：eq_top_iff (J : GrothendieckTopology C) : J = ⊤ ↔ forall X, ⊥ in J X
参数：J : GrothendieckTopology C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `CategoryTheory.GrothendieckTopology.superset_covering`：superset_covering
 (Hss : S <= R) (sjx : S in J X) : R in J X
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
lemma eq_top_iff (J : GrothendieckTopology C) : J = ⊤ ↔ ∀ X, ⊥ ∈ J X := by
  refine ⟨fun h ↦ h ▸ by simp, fun h ↦ ?_⟩
  rw [_root_.eq_top_iff]
  intro X S _
  exact J.superset_covering bot_le (h X)
/-
**CategoryTheory.GrothendieckTopology.eq_top_of_isEmpty** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：eq_top_of_isEmpty [IsEmpty C] (J : GrothendieckTopology C) : J = ⊤
参数：J : GrothendieckTopology C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.GrothendieckTopology.eq_top_iff`：eq_top_iff (J : Grothend
ieckTopology C) : J = ⊤ ↔ forall X, ⊥ in J X
-/
lemma eq_top_of_isEmpty [IsEmpty C] (J : GrothendieckTopology C) : J = ⊤ := by
  rw [eq_top_iff]
  intro X
  exact IsEmpty.elim ‹IsEmpty C› X

@[simp]
/-
**CategoryTheory.GrothendieckTopology.bot_eq_top_iff_isEmpty** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：bot_eq_top_iff_isEmpty : (⊥ : GrothendieckTopology C) = ⊤ ↔ IsEmpty C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_ne_top`：bot_ne_top : (⊥ : α) != ⊤
· 使用定理 `CategoryTheory.Sieve.instNontrivial`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {X : C}, Nontrivial (CategoryTheory.Sieve X)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `CategoryTheory.GrothendieckTopology.eq_top_of_isEmpty`：eq_top_of_isEmpty
 [IsEmpty C] (J : GrothendieckTopology C) : J = ⊤
-/
lemma bot_eq_top_iff_isEmpty : (⊥ : GrothendieckTopology C) = ⊤ ↔ IsEmpty C := by
  refine ⟨fun h ↦ ⟨fun X ↦ ?_⟩, fun h ↦ eq_top_of_isEmpty _⟩
  apply bot_ne_top (α := Sieve X)
  simp only [← GrothendieckTopology.bot_covering, h, top_covering]

@[simp]
/-
**CategoryTheory.GrothendieckTopology.bot_lt_top_iff_nonempty** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：bot_lt_top_iff_nonempty : (⊥ : GrothendieckTopology C) < ⊤ ↔ Nonempty C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma bot_lt_top_iff_nonempty : (⊥ : GrothendieckTopology C) < ⊤ ↔ Nonempty C := by
  contrapose!
  simp

/-- The dense Grothendieck topology.

See https://ncatlab.org/nlab/show/dense+topology, or [MM92] Chapter III, Section 2, example (e).
-/
/-
**CategoryTheory.GrothendieckTopology.dense** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.GrothendieckTopology`。
形式化陈述：dense : GrothendieckTopology C where sieves X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The dense Grothendieck topology.

See https://ncatlab.org/nlab/show/dense+topology, or [MM92] Chapter III, Section
 2, example (e).
-/
def dense : GrothendieckTopology C where
  sieves X := {S | ∀ {Y : C} (f : Y ⟶ X), ∃ (Z : _) (g : Z ⟶ Y), S (g ≫ f)}
  top_mem' _ Y _ := ⟨Y, 𝟙 Y, ⟨⟩⟩
  pullback_stable' := by
    intro X Y S h H Z f
    rcases H (f ≫ h) with ⟨W, g, H'⟩
    exact ⟨W, g, by simpa⟩
  transitive' := by
    intro X S H₁ R H₂ Y f
    rcases H₁ f with ⟨Z, g, H₃⟩
    rcases H₂ H₃ (𝟙 Z) with ⟨W, h, H₄⟩
    exact ⟨W, h ≫ g, by simpa using H₄⟩
/-
**CategoryTheory.GrothendieckTopology.dense_covering** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.GrothendieckTopology`。
形式化陈述：dense_covering : S in dense X ↔ forall {Y} (f : Y ⟶ X), exists (Z : _) (g 
: Z ⟶ Y), S (g ≫ f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem dense_covering : S ∈ dense X ↔ ∀ {Y} (f : Y ⟶ X), ∃ (Z : _) (g : Z ⟶ Y), S (g ≫ f) :=
  Iff.rfl

/--
A category satisfies the right Ore condition if any span can be completed to a commutative square.
NB. Any category with pullbacks obviously satisfies the right Ore condition, see
`right_ore_of_pullbacks`.
-/
/-
**CategoryTheory.GrothendieckTopology.RightOreCondition** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：RightOreCondition (C : Type u) [Category.{v} C] : Prop
参数：C : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category satisfies the right Ore condition if any span can be completed to a c
ommutative square.
NB. Any category with pullbacks obviously satisfies the right Ore condition, see
`right_ore_of_pullbacks`.
-/
def RightOreCondition (C : Type u) [Category.{v} C] : Prop :=
  ∀ {X Y Z : C} (yx : Y ⟶ X) (zx : Z ⟶ X), ∃ (W : _) (wy : W ⟶ Y) (wz : W ⟶ Z), wy ≫ yx = wz ≫ zx
/-
**CategoryTheory.GrothendieckTopology.right_ore_of_pullbacks** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：right_ore_of_pullbacks [Limits.HasPullbacks C] : RightOreCondition C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
-/
theorem right_ore_of_pullbacks [Limits.HasPullbacks C] : RightOreCondition C := fun _ _ =>
  ⟨_, _, _, Limits.pullback.condition⟩

/-- The atomic Grothendieck topology: a sieve is covering iff it is nonempty.
For the pullback stability condition, we need the right Ore condition to hold.

See https://ncatlab.org/nlab/show/atomic+site, or [MM92] Chapter III, Section 2, example (f).
-/
/-
**CategoryTheory.GrothendieckTopology.atomic** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.GrothendieckTopology`。
形式化陈述：atomic (hro : RightOreCondition C) : GrothendieckTopology C where sieves X
参数：hro : RightOreCondition C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The atomic Grothendieck topology: a sieve is covering iff it is nonempty.
For the pullback stability condition, we need the right Ore condition to hold.

See https://ncatlab.org/nlab/show/atomic+site, or [MM92] Chapter III, Section 2,
 example (f).
-/
def atomic (hro : RightOreCondition C) : GrothendieckTopology C where
  sieves X := {S | ∃ (Y : _) (f : Y ⟶ X), S f}
  top_mem' _ := ⟨_, 𝟙 _, ⟨⟩⟩
  pullback_stable' := by
    rintro X Y S h ⟨Z, f, hf⟩
    rcases hro h f with ⟨W, g, k, comm⟩
    refine ⟨_, g, ?_⟩
    simp [comm, hf]
  transitive' := by
    rintro X S ⟨Y, f, hf⟩ R h
    rcases h hf with ⟨Z, g, hg⟩
    exact ⟨_, _, hg⟩


/-- `J.Cover X` denotes the poset of covers of `X` with respect to the
Grothendieck topology `J`. -/
/-
**CategoryTheory.GrothendieckTopology.Cover** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.GrothendieckTopology`。
形式化陈述：Cover (X : C) : Type max u v
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`J.Cover X` denotes the poset of covers of `X` with respect to the
Grothendieck topology `J`.
-/
def Cover (X : C) : Type max u v :=
  { S : Sieve X // S ∈ J X }
deriving Preorder

namespace Cover

variable {J}

/-
**CategoryTheory.GrothendieckTopology.Cover.** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.GrothendieckTopology.Cover`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeOut (J.Cover X) (Sieve X) := ⟨fun S => S.1⟩
/-
**CategoryTheory.GrothendieckTopology.Cover.** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.GrothendieckTopology.Cover`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeFun (J.Cover X) fun _ => ∀ ⦃Y⦄ (_ : Y ⟶ X), Prop := ⟨fun S => (S : Sieve X)⟩
/-
**CategoryTheory.GrothendieckTopology.Cover.condition** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.GrothendieckTopology.Cover`。
形式化陈述：condition (S : J.Cover X) : (S : Sieve X) in J X
参数：S : J.Cover X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem condition (S : J.Cover X) : (S : Sieve X) ∈ J X := S.2

@[ext]
/-
**CategoryTheory.GrothendieckTopology.Cover.ext** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.GrothendieckTopology.Cover`。
形式化陈述：ext (S T : J.Cover X) (h : forall ⦃Y⦄ (f : Y ⟶ X), S f ↔ T f) : S = T
参数：S T : J.Cover X；h : forall ⦃Y⦄ (f : Y ⟶ X), S f ↔ T f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `CategoryTheory.Sieve.ext`：∀ {C : Type u₁} [inst : CategoryTheory.Categor
y.{v₁, u₁} C] {X : C} {R S : CategoryTheory.Sieve X},   (∀ ⦃Y : C⦄ (f : Y ⟶ X), 
R.arrows f ↔ S…
-/
theorem ext (S T : J.Cover X) (h : ∀ ⦃Y⦄ (f : Y ⟶ X), S f ↔ T f) : S = T :=
  Subtype.ext <| Sieve.ext h
/-
**CategoryTheory.GrothendieckTopology.Cover.** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.GrothendieckTopology.Cover`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderTop (J.Cover X) :=
  { (inferInstance : Preorder (J.Cover X)) with
    top := ⟨⊤, J.top_mem _⟩
    le_top := fun _ _ _ _ => by tauto }
/-
**CategoryTheory.GrothendieckTopology.Cover.** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.GrothendieckTopology.Cover`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SemilatticeInf (J.Cover X) :=
  { (inferInstance : Preorder _) with
    inf := fun S T => ⟨S ⊓ T, J.intersection_covering S.condition T.condition⟩
    le_antisymm := fun _ _ h1 h2 => ext _ _ fun {Y} f => ⟨by apply h1, by apply h2⟩
    inf_le_left := fun _ _ _ _ hf => hf.1
    inf_le_right := fun _ _ _ _ hf => hf.2
    le_inf := fun _ _ _ h1 h2 _ _ h => ⟨h1 _ h, h2 _ h⟩ }
/-
**CategoryTheory.GrothendieckTopology.Cover.** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.GrothendieckTopology.Cover`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (J.Cover X) :=
  ⟨⊤⟩

/-- An auxiliary structure, used to define `S.index`. -/
@[ext]
/-
**CategoryTheory.GrothendieckTopology.Cover.Arrow** 是 Mathlib 中的一个归纳类型，位于命名空间 `C
ategoryTheory.GrothendieckTopology.Cover`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X : C} →
 {J : CategoryTheory.GrothendieckTopology C} → J.Cover X → Type (max u v)
参数：max u v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary structure, used to define `S.index`.
-/
structure Arrow (S : J.Cover X) where
  /-- The source of the arrow. -/
  Y : C
  /-- The arrow itself. -/
  f : Y ⟶ X
  /-- The given arrow is contained in the given sieve. -/
  hf : S f

/-- Relation between two elements in `S.arrow`, the data of which
involves a commutative square. -/
@[ext]
/-
**CategoryTheory.GrothendieckTopology.Cover.Arrow.Relation** 是 Mathlib 中的一个归纳类型，
位于命名空间 `CategoryTheory.GrothendieckTopology.Cover.Arrow`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X : C} →
 {J : CategoryTheory.GrothendieckTopology C} → {S : J.Cover X} → S.Arrow → S.Arr
ow → Type (max u v)
参数：max u v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Relation between two elements in `S.arrow`, the data of which
involves a commutative square.
-/
structure Arrow.Relation {S : J.Cover X} (I₁ I₂ : S.Arrow) where
  /-- The source of the arrows defining the relation. -/
  Z : C
  /-- The first arrow defining the relation. -/
  g₁ : Z ⟶ I₁.Y
  /-- The second arrow defining the relation. -/
  g₂ : Z ⟶ I₂.Y
  /-- The relation itself. -/
  w : g₁ ≫ I₁.f = g₂ ≫ I₂.f := by cat_disch

attribute [reassoc] Arrow.Relation.w

/-- Given `I : S.Arrow` and a morphism `g : Z ⟶ I.Y`, this is the arrow in `S.Arrow`
corresponding to `g ≫ I.f`. -/
@[simps]
/-
**CategoryTheory.GrothendieckTopology.Cover.Arrow.precomp** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.GrothendieckTopology.Cover.Arrow`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X : C} →
       {J : CategoryTheory.GrothendieckTopology C} → {S : J.Cover X} → (I : S.Ar
row) → {Z : C} → (Z ⟶ I.Y) → S.Arrow
参数：I : S.Arrow；Z ⟶ I.Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `I : S.Arrow` and a morphism `g : Z ⟶ I.Y`, this is the arrow in `S.Arrow`
corresponding to `g ≫ I.f`.
-/
def Arrow.precomp {S : J.Cover X} (I : S.Arrow) {Z : C} (g : Z ⟶ I.Y) : S.Arrow :=
  ⟨Z, g ≫ I.f, S.1.downward_closed I.hf g⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- Given `I : S.Arrow` and a morphism `g : Z ⟶ I.Y`, this is the obvious relation
from `I.precomp g` to `I`. -/
@[simps]
/-
**CategoryTheory.GrothendieckTopology.Cover.Arrow.precompRelation** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.GrothendieckTopology.Cover.Arrow`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X : C} →
       {J : CategoryTheory.GrothendieckTopology C} →         {S : J.Cover X} → (
I : S.Arrow) → {Z : C} → (g : Z ⟶ I.Y) → (I.precomp g).Relation I
参数：I : S.Arrow；g : Z ⟶ I.Y；I.precomp g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `I : S.Arrow` and a morphism `g : Z ⟶ I.Y`, this is the obvious relation
from `I.precomp g` to `I`.
-/
def Arrow.precompRelation {S : J.Cover X} (I : S.Arrow) {Z : C} (g : Z ⟶ I.Y) :
    (I.precomp g).Relation I where
  Z := (I.precomp g).Y
  g₁ := 𝟙 _
  g₂ := g

/-- Map an `Arrow` along a refinement `S ⟶ T`. -/
@[simps]
/-
**CategoryTheory.GrothendieckTopology.Cover.Arrow.map** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.GrothendieckTopology.Cover.Arrow`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X : C} →
 {J : CategoryTheory.GrothendieckTopology C} → {S T : J.Cover X} → S.Arrow → (S 
⟶ T) → T.Arrow
参数：S ⟶ T。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map an `Arrow` along a refinement `S ⟶ T`.
-/
def Arrow.map {S T : J.Cover X} (I : S.Arrow) (f : S ⟶ T) : T.Arrow :=
  ⟨I.Y, I.f, f.le _ I.hf⟩

/-- Map an `Arrow.Relation` along a refinement `S ⟶ T`. -/
@[simps]
/-
**CategoryTheory.GrothendieckTopology.Cover.Arrow.Relation.map** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.GrothendieckTopology.Cover.Arrow.Relation`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X : C} →
       {J : CategoryTheory.GrothendieckTopology C} →         {S T : J.Cover X} →
 {I₁ I₂ : S.Arrow} → I₁.Relation I₂ → (f : S ⟶ T) → (I₁.map f).Relation (I₂.map 
f)
参数：f : S ⟶ T；I₁.map f；I₂.map f。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.Cover.Arrow.Relation.w`：∀ {C : Type 
u} [inst : CategoryTheory.Category.{v, u} C] {X : C} {J : CategoryTheory.Grothen
dieckTopology C}   {S : J.Cover X} {I₁ I₂ : S.Ar…

--- 原说明 ---
Map an `Arrow.Relation` along a refinement `S ⟶ T`.
-/
def Arrow.Relation.map {S T : J.Cover X} {I₁ I₂ : S.Arrow}
    (r : I₁.Relation I₂) (f : S ⟶ T) : (I₁.map f).Relation (I₂.map f) :=
  { r with }

/-- Pull back a cover along a morphism. -/
/-
**CategoryTheory.GrothendieckTopology.Cover.pullback** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.GrothendieckTopology.Cover`。
形式化陈述：pullback (S : J.Cover X) (f : Y ⟶ X) : J.Cover Y
参数：S : J.Cover X；f : Y ⟶ X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pull back a cover along a morphism.
-/
def pullback (S : J.Cover X) (f : Y ⟶ X) : J.Cover Y :=
  ⟨Sieve.pullback f S, J.pullback_stable _ S.condition⟩

/-- An arrow of `S.pullback f` gives rise to an arrow of `S`. -/
@[simps]
/-
**CategoryTheory.GrothendieckTopology.Cover.Arrow.base** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.GrothendieckTopology.Cover.Arrow`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 →       {J : CategoryTheory.GrothendieckTopology C} → {f : Y ⟶ X} → {S : J.Cove
r X} → (S.pullback f).Arrow → S.Arrow
参数：S.pullback f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An arrow of `S.pullback f` gives rise to an arrow of `S`.
-/
def Arrow.base {f : Y ⟶ X} {S : J.Cover X} (I : (S.pullback f).Arrow) : S.Arrow :=
  ⟨I.Y, I.f ≫ f, I.hf⟩

set_option backward.defeqAttrib.useBackward true in
/-- A relation of `S.pullback f` gives rise to a relation of `S`. -/
/-
**CategoryTheory.GrothendieckTopology.Cover.Arrow.Relation.base** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.GrothendieckTopology.Cover.Arrow.Relation`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 →       {J : CategoryTheory.GrothendieckTopology C} →         {f : Y ⟶ X} → {S 
: J.Cover X} → {I₁ I₂ : (S.pullback f).Arrow} → I₁.Relation I₂ → I₁.base.Relatio
n I₂.base
参数：S.pullback f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A relation of `S.pullback f` gives rise to a relation of `S`.
-/
def Arrow.Relation.base
    {f : Y ⟶ X} {S : J.Cover X} {I₁ I₂ : (S.pullback f).Arrow}
    (r : I₁.Relation I₂) : I₁.base.Relation I₂.base :=
  { r with w := by simp [r.w_assoc] }

@[simp]
/-
**CategoryTheory.GrothendieckTopology.Cover.coe_pullback** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.GrothendieckTopology.Cover`。
形式化陈述：coe_pullback {Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) (S : J.Cover X) : (S.pullback
 f) g ↔ S (g ≫ f)
参数：f : Y ⟶ X；g : Z ⟶ Y；S : J.Cover X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_pullback {Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) (S : J.Cover X) :
    (S.pullback f) g ↔ S (g ≫ f) :=
  Iff.rfl

/-- The isomorphism between `S` and the pullback of `S` w.r.t. the identity. -/
/-
**CategoryTheory.GrothendieckTopology.Cover.pullbackId** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.GrothendieckTopology.Cover`。
形式化陈述：pullbackId (S : J.Cover X) : S.pullback (𝟙 X) ≅ S
参数：S : J.Cover X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between `S` and the pullback of `S` w.r.t. the identity.
-/
def pullbackId (S : J.Cover X) : S.pullback (𝟙 X) ≅ S :=
  eqToIso <| Cover.ext _ _ fun Y f => by simp

/-- Pulling back with respect to a composition is the composition of the pullbacks. -/
/-
**CategoryTheory.GrothendieckTopology.Cover.pullbackComp** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.GrothendieckTopology.Cover`。
形式化陈述：pullbackComp {X Y Z : C} (S : J.Cover X) (f : Z ⟶ Y) (g : Y ⟶ X) : S.pullb
ack (f ≫ g) ≅ (S.pullback g).pullback f
参数：S : J.Cover X；f : Z ⟶ Y；g : Y ⟶ X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pulling back with respect to a composition is the composition of the pullbacks.
-/
def pullbackComp {X Y Z : C} (S : J.Cover X) (f : Z ⟶ Y) (g : Y ⟶ X) :
    S.pullback (f ≫ g) ≅ (S.pullback g).pullback f :=
  eqToIso <| Cover.ext _ _ fun Y f => by simp

/-- Combine a family of covers over a cover. -/
/-
**CategoryTheory.GrothendieckTopology.Cover.bind** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.GrothendieckTopology.Cover`。
形式化陈述：bind {X : C} (S : J.Cover X) (T : forall I : S.Arrow, J.Cover I.Y) : J.Cov
er X
参数：S : J.Cover X；T : forall I : S.Arrow, J.Cover I.Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Combine a family of covers over a cover.
-/
def bind {X : C} (S : J.Cover X) (T : ∀ I : S.Arrow, J.Cover I.Y) : J.Cover X :=
  ⟨Sieve.bind S fun Y f hf => T ⟨Y, f, hf⟩,
    J.bind_covering S.condition fun _ _ _ => (T { Y := _, f := _, hf := _ }).condition⟩

/-- The canonical morphism from `S.bind T` to `T`. -/
/-
**CategoryTheory.GrothendieckTopology.Cover.bindToBase** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.GrothendieckTopology.Cover`。
形式化陈述：bindToBase {X : C} (S : J.Cover X) (T : forall I : S.Arrow, J.Cover I.Y) :
 S.bind T ⟶ S
参数：S : J.Cover X；T : forall I : S.Arrow, J.Cover I.Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical morphism from `S.bind T` to `T`.
-/
def bindToBase {X : C} (S : J.Cover X) (T : ∀ I : S.Arrow, J.Cover I.Y) : S.bind T ⟶ S :=
  homOfLE <| by
    rintro Y f ⟨Z, e1, e2, h1, _, h3⟩
    rw [← h3]
    apply Sieve.downward_closed
    exact h1

/-- An arrow in bind has the form `A ⟶ B ⟶ X` where `A ⟶ B` is an arrow in `T I` for some `I`.
and `B ⟶ X` is an arrow of `S`. This is the object `B`. -/
/-
**CategoryTheory.GrothendieckTopology.Cover.Arrow.middle** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.GrothendieckTopology.Cover.Arrow`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {J : Cate
goryTheory.GrothendieckTopology C} →       {X : C} → {S : J.Cover X} → {T : (I :
 S.Arrow) → J.Cover I.Y} → (S.bind T).Arrow → C
参数：I : S.Arrow；S.bind T。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An arrow in bind has the form `A ⟶ B ⟶ X` where `A ⟶ B` is an arrow in `T I` for
 some `I`.
and `B ⟶ X` is an arrow of `S`. This is the object `B`.
-/
noncomputable def Arrow.middle {X : C} {S : J.Cover X} {T : ∀ I : S.Arrow, J.Cover I.Y}
    (I : (S.bind T).Arrow) : C :=
  I.hf.choose

/-- An arrow in bind has the form `A ⟶ B ⟶ X` where `A ⟶ B` is an arrow in `T I` for some `I`.
and `B ⟶ X` is an arrow of `S`. This is the hom `A ⟶ B`. -/
/-
**CategoryTheory.GrothendieckTopology.Cover.Arrow.toMiddleHom** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.GrothendieckTopology.Cover.Arrow`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {J : Cate
goryTheory.GrothendieckTopology C} →       {X : C} → {S : J.Cover X} → {T : (I :
 S.Arrow) → J.Cover I.Y} → (I : (S.bind T).Arrow) → I.Y ⟶ I.middle
参数：I : S.Arrow；I : (S.bind T).Arrow。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An arrow in bind has the form `A ⟶ B ⟶ X` where `A ⟶ B` is an arrow in `T I` for
 some `I`.
and `B ⟶ X` is an arrow of `S`. This is the hom `A ⟶ B`.
-/
noncomputable def Arrow.toMiddleHom {X : C} {S : J.Cover X} {T : ∀ I : S.Arrow, J.Cover I.Y}
    (I : (S.bind T).Arrow) : I.Y ⟶ I.middle :=
  I.hf.choose_spec.choose

/-- An arrow in bind has the form `A ⟶ B ⟶ X` where `A ⟶ B` is an arrow in `T I` for some `I`.
and `B ⟶ X` is an arrow of `S`. This is the hom `B ⟶ X`. -/
/-
**CategoryTheory.GrothendieckTopology.Cover.Arrow.fromMiddleHom** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.GrothendieckTopology.Cover.Arrow`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {J : Cate
goryTheory.GrothendieckTopology C} →       {X : C} → {S : J.Cover X} → {T : (I :
 S.Arrow) → J.Cover I.Y} → (I : (S.bind T).Arrow) → I.middle ⟶ X
参数：I : S.Arrow；I : (S.bind T).Arrow。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An arrow in bind has the form `A ⟶ B ⟶ X` where `A ⟶ B` is an arrow in `T I` for
 some `I`.
and `B ⟶ X` is an arrow of `S`. This is the hom `B ⟶ X`.
-/
noncomputable def Arrow.fromMiddleHom {X : C} {S : J.Cover X} {T : ∀ I : S.Arrow, J.Cover I.Y}
    (I : (S.bind T).Arrow) : I.middle ⟶ X :=
  I.hf.choose_spec.choose_spec.choose
/-
**CategoryTheory.GrothendieckTopology.Cover.Arrow.from_middle_condition** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.GrothendieckTopology.Cover.Arrow`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheo
ry.GrothendieckTopology C} {X : C}   {S : J.Cover X} {T : (I : S.Arrow) → J.Cove
r I.Y} (I : (S.bind T).Arrow), (↑S).arrows I.fromMiddleHom
参数：I : S.Arrow；I : (S.bind T).Arrow；↑S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.Cover.Arrow.hf`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] {X : C} {J : CategoryTheory.GrothendieckTop
ology C}   {S : J.Cover X} (self : S.Arr…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem Arrow.from_middle_condition {X : C} {S : J.Cover X} {T : ∀ I : S.Arrow, J.Cover I.Y}
    (I : (S.bind T).Arrow) : S I.fromMiddleHom :=
  I.hf.choose_spec.choose_spec.choose_spec.choose

/-- An arrow in bind has the form `A ⟶ B ⟶ X` where `A ⟶ B` is an arrow in `T I` for some `I`.
and `B ⟶ X` is an arrow of `S`. This is the hom `B ⟶ X`, as an arrow. -/
/-
**CategoryTheory.GrothendieckTopology.Cover.Arrow.fromMiddle** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.GrothendieckTopology.Cover.Arrow`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {J : Cate
goryTheory.GrothendieckTopology C} →       {X : C} → {S : J.Cover X} → {T : (I :
 S.Arrow) → J.Cover I.Y} → (S.bind T).Arrow → S.Arrow
参数：I : S.Arrow；S.bind T。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.Cover.Arrow.from_middle_condition`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.Grot
hendieckTopology C} {X : C}   {S : J.Cover X} {T : (I : S.A…

--- 原说明 ---
An arrow in bind has the form `A ⟶ B ⟶ X` where `A ⟶ B` is an arrow in `T I` for
 some `I`.
and `B ⟶ X` is an arrow of `S`. This is the hom `B ⟶ X`, as an arrow.
-/
noncomputable def Arrow.fromMiddle {X : C} {S : J.Cover X} {T : ∀ I : S.Arrow, J.Cover I.Y}
    (I : (S.bind T).Arrow) : S.Arrow :=
  ⟨_, I.fromMiddleHom, I.from_middle_condition⟩
/-
**CategoryTheory.GrothendieckTopology.Cover.Arrow.to_middle_condition** 是 Mathli
b 中的一个定理，位于命名空间 `CategoryTheory.GrothendieckTopology.Cover.Arrow`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheo
ry.GrothendieckTopology C} {X : C}   {S : J.Cover X} {T : (I : S.Arrow) → J.Cove
r I.Y} (I : (S.bind T).Arrow), (↑(T I.fromMiddle)).arrows I.toMiddleHom
参数：I : S.Arrow；I : (S.bind T).Arrow；↑(T I.fromMiddle)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `CategoryTheory.GrothendieckTopology.Cover.Arrow.hf`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] {X : C} {J : CategoryTheory.GrothendieckTop
ology C}   {S : J.Cover X} (self : S.Arr…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem Arrow.to_middle_condition {X : C} {S : J.Cover X} {T : ∀ I : S.Arrow, J.Cover I.Y}
    (I : (S.bind T).Arrow) : (T I.fromMiddle) I.toMiddleHom :=
  I.hf.choose_spec.choose_spec.choose_spec.choose_spec.1

/-- An arrow in bind has the form `A ⟶ B ⟶ X` where `A ⟶ B` is an arrow in `T I` for some `I`.
and `B ⟶ X` is an arrow of `S`. This is the hom `A ⟶ B`, as an arrow. -/
/-
**CategoryTheory.GrothendieckTopology.Cover.Arrow.toMiddle** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.GrothendieckTopology.Cover.Arrow`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {J : Cate
goryTheory.GrothendieckTopology C} →       {X : C} → {S : J.Cover X} → {T : (I :
 S.Arrow) → J.Cover I.Y} → (I : (S.bind T).Arrow) → (T I.fromMiddle).Arrow
参数：I : S.Arrow；I : (S.bind T).Arrow；T I.fromMiddle。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.Cover.Arrow.to_middle_condition`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.Grothe
ndieckTopology C} {X : C}   {S : J.Cover X} {T : (I : S.A…

--- 原说明 ---
An arrow in bind has the form `A ⟶ B ⟶ X` where `A ⟶ B` is an arrow in `T I` for
 some `I`.
and `B ⟶ X` is an arrow of `S`. This is the hom `A ⟶ B`, as an arrow.
-/
noncomputable def Arrow.toMiddle {X : C} {S : J.Cover X} {T : ∀ I : S.Arrow, J.Cover I.Y}
    (I : (S.bind T).Arrow) : (T I.fromMiddle).Arrow :=
  ⟨_, I.toMiddleHom, I.to_middle_condition⟩
/-
**CategoryTheory.GrothendieckTopology.Cover.Arrow.middle_spec** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.GrothendieckTopology.Cover.Arrow`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheo
ry.GrothendieckTopology C} {X : C}   {S : J.Cover X} {T : (I : S.Arrow) → J.Cove
r I.Y} (I : (S.bind T).Arrow),   CategoryTheory.CategoryStruct.comp I.toMiddleHo
m I.fromMiddleHom = I.f
参数：I : S.Arrow；I : (S.bind T).Arrow。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `CategoryTheory.GrothendieckTopology.Cover.Arrow.hf`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] {X : C} {J : CategoryTheory.GrothendieckTop
ology C}   {S : J.Cover X} (self : S.Arr…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem Arrow.middle_spec {X : C} {S : J.Cover X} {T : ∀ I : S.Arrow, J.Cover I.Y}
    (I : (S.bind T).Arrow) : I.toMiddleHom ≫ I.fromMiddleHom = I.f :=
  I.hf.choose_spec.choose_spec.choose_spec.choose_spec.2

/-- An auxiliary structure, used to define `S.index`. -/
@[ext]
/-
**CategoryTheory.GrothendieckTopology.Cover.Relation** 是 Mathlib 中的一个归纳类型，位于命名空间
 `CategoryTheory.GrothendieckTopology.Cover`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X : C} →
 {J : CategoryTheory.GrothendieckTopology C} → J.Cover X → Type (max u v)
参数：max u v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary structure, used to define `S.index`.
-/
structure Relation (S : J.Cover X) where
  /-- The first arrow. -/
  {fst : S.Arrow}
  /-- The second arrow. -/
  {snd : S.Arrow}
  /-- The relation between the two arrows. -/
  r : fst.Relation snd

/-- Constructor for `Cover.Relation` which takes as an input
`r : I₁.Relation I₂` with `I₁ I₂ : S.Arrow`. -/
@[simps]
/-
**CategoryTheory.GrothendieckTopology.Cover.Relation.mk'** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.GrothendieckTopology.Cover.Relation`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X : C} →
       {J : CategoryTheory.GrothendieckTopology C} →         {S : J.Cover X} → {
fst snd : S.Arrow} → fst.Relation snd → S.Relation
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for `Cover.Relation` which takes as an input
`r : I₁.Relation I₂` with `I₁ I₂ : S.Arrow`.
-/
def Relation.mk' {S : J.Cover X} {fst snd : S.Arrow} (r : fst.Relation snd) :
    S.Relation where
  fst := fst
  snd := snd
  r := r


/-- The shape of the multiequalizer diagrams associated to `S : J.Cover X`. -/
@[simps]
/-
**CategoryTheory.GrothendieckTopology.Cover.shape** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.GrothendieckTopology.Cover`。
形式化陈述：shape (S : J.Cover X) : Limits.MulticospanShape where L
参数：S : J.Cover X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The shape of the multiequalizer diagrams associated to `S : J.Cover X`.
-/
def shape (S : J.Cover X) : Limits.MulticospanShape where
  L := S.Arrow
  R := S.Relation
  fst I := I.fst
  snd I := I.snd

-- This is used extensively in `Plus.lean`, etc.
-- We place this definition here as it will be used in `Sheaf.lean` as well.
/-- To every `S : J.Cover X` and presheaf `P`, associate a `MulticospanIndex`. -/
@[simps]
/-
**CategoryTheory.GrothendieckTopology.Cover.index** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.GrothendieckTopology.Cover`。
形式化陈述：index {D : Type u₁} [Category.{v₁} D] (S : J.Cover X) (P : Cᵒᵖ ⥤ D) : Limi
ts.MulticospanIndex S.shape D where left I
参数：S : J.Cover X；P : Cᵒᵖ ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To every `S : J.Cover X` and presheaf `P`, associate a `MulticospanIndex`.
-/
def index {D : Type u₁} [Category.{v₁} D] (S : J.Cover X) (P : Cᵒᵖ ⥤ D) :
    Limits.MulticospanIndex S.shape D where
  left I := P.obj (Opposite.op I.Y)
  right I := P.obj (Opposite.op I.r.Z)
  fst I := P.map I.r.g₁.op
  snd I := P.map I.r.g₂.op

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The natural multifork associated to `S : J.Cover X` for a presheaf `P`.
Saying that this multifork is a limit is essentially equivalent to the sheaf condition at the
given object for the given covering sieve. See `Sheaf.lean` for an equivalent sheaf condition
using this.
-/
/-
**CategoryTheory.GrothendieckTopology.Cover.multifork** 是 Mathlib 中的一个缩写定义，位于命名空
间 `CategoryTheory.GrothendieckTopology.Cover`。
形式化陈述：multifork {D : Type u₁} [Category.{v₁} D] (S : J.Cover X) (P : Cᵒᵖ ⥤ D) : 
Limits.Multifork (S.index P)
参数：S : J.Cover X；P : Cᵒᵖ ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural multifork associated to `S : J.Cover X` for a presheaf `P`.
Saying that this multifork is a limit is essentially equivalent to the sheaf con
dition at the
given object for the given covering sieve. See `Sheaf.lean` for an equivalent sh
eaf condition
using this.
-/
abbrev multifork {D : Type u₁} [Category.{v₁} D] (S : J.Cover X) (P : Cᵒᵖ ⥤ D) :
    Limits.Multifork (S.index P) :=
  Limits.Multifork.ofι _ (P.obj (Opposite.op X)) (fun I => P.map I.f.op)
    (by
      intro I
      dsimp
      simp only [← P.map_comp, ← op_comp, I.r.w])

/-- The canonical map from `P.obj (op X)` to the multiequalizer associated to a covering sieve,
assuming such a multiequalizer exists. This will be used in `Sheaf.lean` to provide an equivalent
sheaf condition in terms of multiequalizers. -/
/-
**CategoryTheory.GrothendieckTopology.Cover.toMultiequalizer** 是 Mathlib 中的一个缩写定
义，位于命名空间 `CategoryTheory.GrothendieckTopology.Cover`。
形式化陈述：toMultiequalizer {D : Type u₁} [Category.{v₁} D] (S : J.Cover X) (P : Cᵒᵖ 
⥤ D) [Limits.HasMultiequalizer (S.index P)] : P.obj (Opposite.op X) ⟶ Limits.mul
tiequalizer (S.index P)
参数：S : J.Cover X；P : Cᵒᵖ ⥤ D；S.index P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from `P.obj (op X)` to the multiequalizer associated to a cove
ring sieve,
assuming such a multiequalizer exists. This will be used in `Sheaf.lean` to prov
ide an equivalent
sheaf condition in terms of multiequalizers.
-/
noncomputable abbrev toMultiequalizer {D : Type u₁} [Category.{v₁} D] (S : J.Cover X)
    (P : Cᵒᵖ ⥤ D) [Limits.HasMultiequalizer (S.index P)] :
    P.obj (Opposite.op X) ⟶ Limits.multiequalizer (S.index P) :=
  Limits.Multiequalizer.lift _ _ (fun I => P.map I.f.op)
    (by
      intro I
      dsimp only [shape, index, Relation.fst, Relation.snd]
      simp only [← P.map_comp, ← op_comp, I.r.w])

end Cover

/-- Pull back a cover along a morphism. -/
@[simps obj]
/-
**CategoryTheory.GrothendieckTopology.pullback** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.GrothendieckTopology`。
形式化陈述：pullback (f : Y ⟶ X) : J.Cover X ⥤ J.Cover Y where obj S
参数：f : Y ⟶ X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pull back a cover along a morphism.
-/
def pullback (f : Y ⟶ X) : J.Cover X ⥤ J.Cover Y where
  obj S := S.pullback f
  map f := (Sieve.pullback_monotone _ f.le).hom

/-- Pulling back along the identity is naturally isomorphic to the identity functor. -/
/-
**CategoryTheory.GrothendieckTopology.pullbackId** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.GrothendieckTopology`。
形式化陈述：pullbackId (X : C) : J.pullback (𝟙 X) ≅ 𝟭 _
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pulling back along the identity is naturally isomorphic to the identity functor.
-/
def pullbackId (X : C) : J.pullback (𝟙 X) ≅ 𝟭 _ :=
  NatIso.ofComponents fun S => S.pullbackId

/-- Pulling back along a composition is naturally isomorphic to
the composition of the pullbacks. -/
/-
**CategoryTheory.GrothendieckTopology.pullbackComp** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.GrothendieckTopology`。
形式化陈述：pullbackComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : J.pullback (f ≫ g) ≅ J.
pullback g ⋙ J.pullback f
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pulling back along a composition is naturally isomorphic to
the composition of the pullbacks.
-/
def pullbackComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    J.pullback (f ≫ g) ≅ J.pullback g ⋙ J.pullback f :=
  NatIso.ofComponents fun S => S.pullbackComp f g

end GrothendieckTopology

end CategoryTheory

