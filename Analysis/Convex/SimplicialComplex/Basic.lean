/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import Mathlib.Order.UpperLower.Relative

/-!
# Simplicial complexes

In this file, we define simplicial complexes over `𝕜`-modules.
A (pre-) abstract simplicial complex is a downwards-closed collection of nonempty finite sets,
and a simplicial complex is such a collection identified with simplices
closed by inclusion (of vertices) and intersection (of underlying sets)
whose convex hulls "glue nicely", each finite set and its convex hull corresponding respectively
to the vertices and the underlying set of a simplex.

## Main declarations

* `SimplicialComplex 𝕜 E`: A simplicial complex in the `𝕜`-module `E`.
* `SimplicialComplex.vertices`: The zero-dimensional faces of a simplicial complex.
* `SimplicialComplex.facets`: The maximal faces of a simplicial complex.

## Notation

`K ≤ L` means that the faces of `K` are faces of `L`.

## Implementation notes

"glue nicely" usually means that the intersection of two faces (as sets in the ambient space) is a
face. Given that we store the vertices, not the faces, this would be a bit awkward to spell.
Instead, `SimplicialComplex.inter_subset_convexHull` is an equivalent condition which works on the
vertices.

## TODO

Simplicial complexes can be generalized to affine spaces once `ConvexHull` has been ported.
-/

@[expose] public section


open Finset Set

variable (𝕜 E : Type*) [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]

namespace Geometry

-- TODO: update to new binder order? not sure what binder order is correct for `down_closed`.
/-- A simplicial complex in a `𝕜`-module is a collection of simplices which glue nicely together.
Note that the textbook meaning of "glue nicely" is given in
`Geometry.SimplicialComplex.disjoint_or_exists_inter_eq_convexHull`. It is mostly useless, as
`Geometry.SimplicialComplex.convexHull_inter_convexHull` is enough for all purposes. -/
@[ext]
/-
**Geometry.SimplicialComplex** 是 Mathlib 中的一个归纳类型，位于命名空间 `Geometry`。
形式化陈述：(𝕜 : Type u_1) →   (E : Type u_2) → [inst : Ring 𝕜] → [PartialOrder 𝕜] → [
inst_2 : AddCommGroup E] → [_root_.Module 𝕜 E] → Type u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A simplicial complex in a `𝕜`-module is a collection of simplices which glue nic
ely together.
Note that the textbook meaning of "glue nicely" is given in
`Geometry.SimplicialComplex.disjoint_or_exists_inter_eq_convexHull`. It is mostl
y useless, as
`Geometry.SimplicialComplex.convexHull_inter_convexHull` is enough for all purpo
ses.
-/
structure SimplicialComplex extends PreAbstractSimplicialComplex E where
  /-- the vertices in each face are affine independent: this is an implementation detail -/
  indep : ∀ {s}, s ∈ faces → AffineIndependent 𝕜 ((↑) : s → E)
  inter_subset_convexHull : ∀ {s t}, s ∈ faces → t ∈ faces →
    convexHull 𝕜 ↑s ∩ convexHull 𝕜 ↑t ⊆ convexHull 𝕜 (s ∩ t : Set E)

namespace SimplicialComplex

variable {𝕜 E}
variable {K : SimplicialComplex 𝕜 E} {s t : Finset E} {x : E}

/-
**Geometry.SimplicialComplex.nonempty_of_mem_faces** 是 Mathlib 中的一个引理，位于命名空间 `Ge
ometry.SimplicialComplex`。
形式化陈述：nonempty_of_mem_faces (hs : s in K.faces) : s.Nonempty
参数：hs : s in K.faces。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `PreAbstractSimplicialComplex.isRelLowerSet_faces`：∀ {ι : Type u_1} (self
 : PreAbstractSimplicialComplex ι), IsRelLowerSet self.faces Finset.Nonempty
-/
lemma nonempty_of_mem_faces (hs : s ∈ K.faces) : s.Nonempty :=
  K.isRelLowerSet_faces hs |>.1
/-
**Geometry.SimplicialComplex.empty_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Geometry.Si
mplicialComplex`。
形式化陈述：empty_notMem : ∅ ∉ K.faces
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Geometry.SimplicialComplex.nonempty_of_mem_faces`：nonempty_of_mem_faces 
(hs : s in K.faces) : s.Nonempty
-/
theorem empty_notMem : ∅ ∉ K.faces :=
  fun h => by simpa using nonempty_of_mem_faces h

/-- The underlying space of a simplicial complex is the union of its faces. -/
/-
**Geometry.SimplicialComplex.space** 是 Mathlib 中的一个定义，位于命名空间 `Geometry.Simplicia
lComplex`。
形式化陈述：space (K : SimplicialComplex 𝕜 E) : Set E
参数：K : SimplicialComplex 𝕜 E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying space of a simplicial complex is the union of its faces.
-/
def space (K : SimplicialComplex 𝕜 E) : Set E :=
  ⋃ s ∈ K.faces, convexHull 𝕜 (s : Set E)
/-
**Geometry.SimplicialComplex.mem_space_iff** 是 Mathlib 中的一个定理，位于命名空间 `Geometry.S
implicialComplex`。
形式化陈述：mem_space_iff : x in K.space ↔ exists s in K.faces, x in convexHull 𝕜 (s :
 Set E)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_space_iff : x ∈ K.space ↔ ∃ s ∈ K.faces, x ∈ convexHull 𝕜 (s : Set E) := by
  simp [space]
/-
**Geometry.SimplicialComplex.convexHull_subset_space** 是 Mathlib 中的一个定理，位于命名空间 `
Geometry.SimplicialComplex`。
形式化陈述：convexHull_subset_space (hs : s in K.faces) : convexHull 𝕜 s subseteq K.sp
ace
参数：hs : s in K.faces。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.subset_biUnion_of_mem`：subset_biUnion_of_mem {s : Set α} {u : α -> S
et β} {x : α} (xs : x in s) : u x subseteq ⋃ x in s, u x
-/
theorem convexHull_subset_space (hs : s ∈ K.faces) : convexHull 𝕜 s ⊆ K.space := by
  convert! subset_biUnion_of_mem hs
  rfl
/-
**Geometry.SimplicialComplex.subset_space** 是 Mathlib 中的一个定理，位于命名空间 `Geometry.Si
mplicialComplex`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Ring 𝕜] [inst_1 : PartialOrder 𝕜] 
[inst_2 : AddCommGroup E]   [inst_3 : _root_.Module 𝕜 E] {K : Geometry.Simplicia
lComplex 𝕜 E} {s : Finset E}, s ∈ K.faces → ↑s ⊆ K.space
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `subset_convexHull`：subset_convexHull : s subseteq convexHull 𝕜 s
· 使用定理 `Geometry.SimplicialComplex.convexHull_subset_space`：convexHull_subset_sp
ace (hs : s in K.faces) : convexHull 𝕜 s subseteq K.space
-/
protected theorem subset_space (hs : s ∈ K.faces) : (s : Set E) ⊆ K.space :=
  (subset_convexHull 𝕜 _).trans <| convexHull_subset_space hs
/-
**Geometry.SimplicialComplex.convexHull_inter_convexHull** 是 Mathlib 中的一个定理，位于命名
空间 `Geometry.SimplicialComplex`。
形式化陈述：convexHull_inter_convexHull (hs : s in K.faces) (ht : t in K.faces) : conv
exHull 𝕜 s inter convexHull 𝕜 t = convexHull 𝕜 (s inter t : Set E)
参数：hs : s in K.faces；ht : t in K.faces。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Geometry.SimplicialComplex.inter_subset_convexHull`：∀ {𝕜 : Type u_1} {E 
: Type u_2} [inst : Ring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommGroup E] 
  [inst_3 : _root_.Module 𝕜 E] (self : G…
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `convexHull_mono`：convexHull_mono (hst : s subseteq t) : convexHull 𝕜 s s
ubseteq convexHull 𝕜 t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
theorem convexHull_inter_convexHull (hs : s ∈ K.faces) (ht : t ∈ K.faces) :
    convexHull 𝕜 s ∩ convexHull 𝕜 t = convexHull 𝕜 (s ∩ t : Set E) :=
  (K.inter_subset_convexHull hs ht).antisymm <|
    subset_inter (convexHull_mono Set.inter_subset_left) <|
      convexHull_mono Set.inter_subset_right
/-
**Geometry.SimplicialComplex.down_closed** 是 Mathlib 中的一个定理，位于命名空间 `Geometry.Sim
plicialComplex`。
形式化陈述：down_closed {s t} (hs : s in K.faces) (hst : t subseteq s) (ht : t.Nonempt
y) : t in K.faces
参数：hs : s in K.faces；hst : t subseteq s；ht : t.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `PreAbstractSimplicialComplex.isRelLowerSet_faces`：∀ {ι : Type u_1} (self
 : PreAbstractSimplicialComplex ι), IsRelLowerSet self.faces Finset.Nonempty
-/
theorem down_closed {s t} (hs : s ∈ K.faces) (hst : t ⊆ s) (ht : t.Nonempty) : t ∈ K.faces :=
  (K.isRelLowerSet_faces hs).2 hst ht

/-- The conclusion is the usual meaning of "glue nicely" in textbooks. It turns out to be quite
unusable, as it's about faces as sets in space rather than simplices. Further, additional structure
on `𝕜` means the only choice of `u` is `s ∩ t` (but it's hard to prove). -/
/-
**Geometry.SimplicialComplex.disjoint_or_exists_inter_eq_convexHull** 是 Mathlib 
中的一个定理，位于命名空间 `Geometry.SimplicialComplex`。
形式化陈述：disjoint_or_exists_inter_eq_convexHull (hs : s in K.faces) (ht : t in K.fa
ces) : Disjoint (convexHull 𝕜 (s : Set E)) (convexHull 𝕜 t) ∨ exists u in K.face
s, convexHull 𝕜 (s : Set E) inter convexHull 𝕜 t = convexHull 𝕜 u
参数：hs : s in K.faces；ht : t in K.faces。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.not_disjoint_iff_nonempty_inter`：not_disjoint_iff_nonempty_inter : ¬
 Disjoint s t ↔ (s inter t).Nonempty
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Geometry.SimplicialComplex.down_closed`：down_closed {s t} (hs : s in K.f
aces) (hst : t subseteq s) (ht : t.Nonempty) : t in K.faces
· 使用定理 `Finset.inter_subset_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ∩ s₂ ⊆ s₁
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `convexHull_nonempty_iff`：convexHull_nonempty_iff : (convexHull 𝕜 s).None
mpty ↔ s.Nonempty
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `Geometry.SimplicialComplex.inter_subset_convexHull`：∀ {𝕜 : Type u_1} {E 
: Type u_2} [inst : Ring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommGroup E] 
  [inst_3 : _root_.Module 𝕜 E] (self : G…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.coe_inter`：coe_inter (s₁ s₂ : Finset α) : ↑(s₁ inter s₂) = (s₁ in
ter s₂ : Set α)
· 使用定理 `Geometry.SimplicialComplex.convexHull_inter_convexHull`：convexHull_inter
_convexHull (hs : s in K.faces) (ht : t in K.faces) : convexHull 𝕜 s inter conve
xHull 𝕜 t = convexHull 𝕜 (s inter t : Set E)

--- 原说明 ---
The conclusion is the usual meaning of "glue nicely" in textbooks. It turns out 
to be quite
unusable, as it's about faces as sets in space rather than simplices. Further, a
dditional structure
on `𝕜` means the only choice of `u` is `s ∩ t` (but it's hard to prove).
-/
theorem disjoint_or_exists_inter_eq_convexHull (hs : s ∈ K.faces) (ht : t ∈ K.faces) :
    Disjoint (convexHull 𝕜 (s : Set E)) (convexHull 𝕜 t) ∨
      ∃ u ∈ K.faces, convexHull 𝕜 (s : Set E) ∩ convexHull 𝕜 t = convexHull 𝕜 u := by
  classical
  by_contra! h
  rw [not_disjoint_iff_nonempty_inter] at h
  refine h.2 (s ∩ t) (K.down_closed hs inter_subset_left ?_) ?_
  · simpa [← coe_inter] using convexHull_nonempty_iff.1 (h.1.mono (K.inter_subset_convexHull hs ht))
  · rw [coe_inter, convexHull_inter_convexHull hs ht]

/-- Construct a simplicial complex by removing the empty face for you. -/
@[simps]
/-
**Geometry.SimplicialComplex.ofErase** 是 Mathlib 中的一个定义，位于命名空间 `Geometry.Simplic
ialComplex`。
形式化陈述：ofErase (faces : Set (Finset E)) (indep : forall s in faces, AffineIndepen
dent 𝕜 ((↑) : s -> E)) (down_closed : IsLowerSet faces) (inter_subset_convexHull
 : forallᵉ (s in faces) (t in faces), convexHull 𝕜 ↑s inter convexHull 𝕜 ↑t subs
eteq convexHull 𝕜 (s inter t : Set E)) : SimplicialComplex 𝕜 E where faces
参数：faces : Set (Finset E)；indep : forall s in faces, AffineIndependent 𝕜 ((↑) : 
s -> E)；down_closed : IsLowerSet faces；inter_subset_convexHull : forallᵉ (s in f
aces) (t in faces), convexHull 𝕜 ↑s inter convexHull 𝕜 ↑t subseteq convexHull 𝕜 
(s inter t : Set E)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a simplicial complex by removing the empty face for you.
-/
def ofErase (faces : Set (Finset E)) (indep : ∀ s ∈ faces, AffineIndependent 𝕜 ((↑) : s → E))
    (down_closed : IsLowerSet faces)
    (inter_subset_convexHull : ∀ᵉ (s ∈ faces) (t ∈ faces),
      convexHull 𝕜 ↑s ∩ convexHull 𝕜 ↑t ⊆ convexHull 𝕜 (s ∩ t : Set E)) :
    SimplicialComplex 𝕜 E where
  faces := faces \ {∅}
  indep hs := indep _ hs.1
  isRelLowerSet_faces := by
    have : faces \ {∅} = {f ∈ faces | f.Nonempty} := by grind
    simpa only [this] using down_closed.isRelLowerSet_sep Finset.Nonempty
  inter_subset_convexHull hs ht := inter_subset_convexHull _ hs.1 _ ht.1

/-- Construct a simplicial complex as a subset of a given simplicial complex. -/
@[simps]
/-
**Geometry.SimplicialComplex.ofSubcomplex** 是 Mathlib 中的一个定义，位于命名空间 `Geometry.Si
mplicialComplex`。
形式化陈述：ofSubcomplex (K : SimplicialComplex 𝕜 E) (faces : Set (Finset E)) (subset 
: faces subseteq K.faces) (down_closed : IsLowerSet faces) : SimplicialComplex 𝕜
 E
参数：K : SimplicialComplex 𝕜 E；faces : Set (Finset E)；subset : faces subseteq K.fa
ces；down_closed : IsLowerSet faces。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a simplicial complex as a subset of a given simplicial complex.
-/
def ofSubcomplex (K : SimplicialComplex 𝕜 E) (faces : Set (Finset E)) (subset : faces ⊆ K.faces)
    (down_closed : IsLowerSet faces) : SimplicialComplex 𝕜 E :=
  { faces := faces
    indep := fun hs => K.indep (subset hs)
    isRelLowerSet_faces := K.isRelLowerSet_faces.mono_isLowerSet down_closed subset
    inter_subset_convexHull := fun hs ht => K.inter_subset_convexHull (subset hs) (subset ht) }

/-! ### Vertices -/


/-- The vertices of a simplicial complex are its zero-dimensional faces. -/
/-
**Geometry.SimplicialComplex.vertices** 是 Mathlib 中的一个定义，位于命名空间 `Geometry.Simpli
cialComplex`。
形式化陈述：vertices (K : SimplicialComplex 𝕜 E) : Set E
参数：K : SimplicialComplex 𝕜 E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The vertices of a simplicial complex are its zero-dimensional faces.
-/
def vertices (K : SimplicialComplex 𝕜 E) : Set E :=
  { x | {x} ∈ K.faces }
/-
**Geometry.SimplicialComplex.mem_vertices** 是 Mathlib 中的一个定理，位于命名空间 `Geometry.Si
mplicialComplex`。
形式化陈述：mem_vertices : x in K.vertices ↔ {x} in K.faces
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_vertices : x ∈ K.vertices ↔ {x} ∈ K.faces := Iff.rfl
/-
**Geometry.SimplicialComplex.vertices_eq** 是 Mathlib 中的一个定理，位于命名空间 `Geometry.Sim
plicialComplex`。
形式化陈述：vertices_eq : K.vertices = ⋃ k in K.faces, (k : Set E)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Set.mem_biUnion`：mem_biUnion {s : Set α} {t : α -> Set β} {x : α} {y : β
} (xs : x in s) (ytx : y in t x) : y in ⋃ x in s, t x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `Finset.mem_singleton_self`：mem_singleton_self (a : α) : a in ({a} : Fins
et α)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion₂`：mem_iUnion₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋃ (i) (j), s i j) ↔ exists i j, x in s i j
· 使用定理 `Geometry.SimplicialComplex.down_closed`：down_closed {s t} (hs : s in K.f
aces) (hst : t subseteq s) (ht : t.Nonempty) : t in K.faces
· 使用定理 `Finset.singleton_subset_iff`：singleton_subset_iff {s : Finset α} {a : α}
 : {a} subseteq s ↔ a in s
· 使用定理 `Finset.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Finset α)
.Nonempty
-/
theorem vertices_eq : K.vertices = ⋃ k ∈ K.faces, (k : Set E) := by
  ext x
  refine ⟨fun h => mem_biUnion h <| mem_coe.2 <| mem_singleton_self x, fun h => ?_⟩
  obtain ⟨s, hs, hx⟩ := mem_iUnion₂.1 h
  exact K.down_closed hs (Finset.singleton_subset_iff.2 <| mem_coe.1 hx) (singleton_nonempty _)
/-
**Geometry.SimplicialComplex.vertices_subset_space** 是 Mathlib 中的一个定理，位于命名空间 `Ge
ometry.SimplicialComplex`。
形式化陈述：vertices_subset_space : K.vertices subseteq K.space
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Geometry.SimplicialComplex.vertices_eq`：vertices_eq : K.vertices = ⋃ k i
n K.faces, (k : Set E)
· 使用定理 `Set.iUnion₂_mono`：iUnion₂_mono {s t : forall i, κ i -> Set α} (h : foral
l i j, s i j subseteq t i j) : ⋃ (i) (j), s i j subseteq ⋃ (i) (j), t i j
· 使用定理 `subset_convexHull`：subset_convexHull : s subseteq convexHull 𝕜 s
-/
theorem vertices_subset_space : K.vertices ⊆ K.space :=
  vertices_eq.subset.trans <| iUnion₂_mono fun x _ => subset_convexHull 𝕜 (x : Set E)
/-
**Geometry.SimplicialComplex.vertex_mem_convexHull_iff** 是 Mathlib 中的一个定理，位于命名空间
 `Geometry.SimplicialComplex`。
形式化陈述：vertex_mem_convexHull_iff (hx : x in K.vertices) (hs : s in K.faces) : x i
n convexHull 𝕜 (s : Set E) ↔ x in s
参数：hx : x in K.vertices；hs : s in K.faces。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Geometry.SimplicialComplex.inter_subset_convexHull`：∀ {𝕜 : Type u_1} {E 
: Type u_2} [inst : Ring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommGroup E] 
  [inst_3 : _root_.Module 𝕜 E] (self : G…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `convexHull_singleton`：convexHull_singleton (x : E) : convexHull 𝕜 ({x} :
 Set E) = {x}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `convexHull_empty`：convexHull_empty : convexHull 𝕜 (∅ : Set E) = ∅
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.disjoint_iff_inter_eq_empty`：disjoint_iff_inter_eq_empty : Disjoi
nt s t ↔ s inter t = ∅
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_singleton_right`：disjoint_singleton_right : Disjoint s (
singleton a) ↔ a ∉ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_inter`：coe_inter (s₁ s₂ : Finset α) : ↑(s₁ inter s₂) = (s₁ in
ter s₂ : Set α)
· 使用定理 `subset_convexHull`：subset_convexHull : s subseteq convexHull 𝕜 s
-/
theorem vertex_mem_convexHull_iff (hx : x ∈ K.vertices) (hs : s ∈ K.faces) :
    x ∈ convexHull 𝕜 (s : Set E) ↔ x ∈ s := by
  refine ⟨fun h => ?_, fun h => subset_convexHull 𝕜 _ h⟩
  classical
  have h := K.inter_subset_convexHull hx hs ⟨by simp, h⟩
  by_contra H
  rwa [← coe_inter, Finset.disjoint_iff_inter_eq_empty.1 (Finset.disjoint_singleton_right.2 H).symm,
    coe_empty, convexHull_empty] at h

/-- A face is a subset of another one iff its vertices are. -/
/-
**Geometry.SimplicialComplex.face_subset_face_iff** 是 Mathlib 中的一个定理，位于命名空间 `Geo
metry.SimplicialComplex`。
形式化陈述：face_subset_face_iff (hs : s in K.faces) (ht : t in K.faces) : convexHull 
𝕜 (s : Set E) subseteq convexHull 𝕜 ↑t ↔ s subseteq t
参数：hs : s in K.faces；ht : t in K.faces。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Geometry.SimplicialComplex.vertex_mem_convexHull_iff`：vertex_mem_convexH
ull_iff (hx : x in K.vertices) (hs : s in K.faces) : x in convexHull 𝕜 (s : Set 
E) ↔ x in s
· 使用定理 `Geometry.SimplicialComplex.down_closed`：down_closed {s t} (hs : s in K.f
aces) (hst : t subseteq s) (ht : t.Nonempty) : t in K.faces
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.singleton_subset_iff`：singleton_subset_iff {s : Finset α} {a : α}
 : {a} subseteq s ↔ a in s
· 使用定理 `Finset.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Finset α)
.Nonempty
· 使用定理 `subset_convexHull`：subset_convexHull : s subseteq convexHull 𝕜 s
· 使用定理 `convexHull_mono`：convexHull_mono (hst : s subseteq t) : convexHull 𝕜 s s
ubseteq convexHull 𝕜 t

--- 原说明 ---
A face is a subset of another one iff its vertices are.
-/
theorem face_subset_face_iff (hs : s ∈ K.faces) (ht : t ∈ K.faces) :
    convexHull 𝕜 (s : Set E) ⊆ convexHull 𝕜 ↑t ↔ s ⊆ t :=
  ⟨fun h _ hxs =>
    (vertex_mem_convexHull_iff
          (K.down_closed hs (Finset.singleton_subset_iff.2 hxs) <| singleton_nonempty _) ht).1
      (h (subset_convexHull 𝕜 (E := E) s hxs)),
    convexHull_mono⟩

/-! ### Facets -/


/-- A facet of a simplicial complex is a maximal face. -/
/-
**Geometry.SimplicialComplex.facets** 是 Mathlib 中的一个定义，位于命名空间 `Geometry.Simplici
alComplex`。
形式化陈述：facets (K : SimplicialComplex 𝕜 E) : Set (Finset E)
参数：K : SimplicialComplex 𝕜 E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A facet of a simplicial complex is a maximal face.
-/
def facets (K : SimplicialComplex 𝕜 E) : Set (Finset E) :=
  { s ∈ K.faces | ∀ ⦃t⦄, t ∈ K.faces → s ⊆ t → s = t }
/-
**Geometry.SimplicialComplex.mem_facets** 是 Mathlib 中的一个定理，位于命名空间 `Geometry.Simp
licialComplex`。
形式化陈述：mem_facets : s in K.facets ↔ s in K.faces ∧ forall t in K.faces, s subsete
q t -> s = t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_sep_iff`：mem_sep_iff : x in { x in s | p x } ↔ x in s ∧ p x
-/
theorem mem_facets : s ∈ K.facets ↔ s ∈ K.faces ∧ ∀ t ∈ K.faces, s ⊆ t → s = t :=
  mem_sep_iff
/-
**Geometry.SimplicialComplex.facets_subset** 是 Mathlib 中的一个定理，位于命名空间 `Geometry.S
implicialComplex`。
形式化陈述：facets_subset : K.facets subseteq K.faces
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem facets_subset : K.facets ⊆ K.faces := fun _ hs => hs.1
/-
**Geometry.SimplicialComplex.not_facet_iff_subface** 是 Mathlib 中的一个定理，位于命名空间 `Ge
ometry.SimplicialComplex`。
形式化陈述：not_facet_iff_subface (hs : s in K.faces) : s ∉ K.facets ↔ exists t, t in 
K.faces ∧ s ⊂ t
参数：hs : s in K.faces。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.Subset.antisymm`：∀ {α : Type u_1} {s₁ s₂ : Finset α}, s₁ ⊆ s₂ → s
₂ ⊆ s₁ → s₁ = s₂
· 使用定理 `Finset.Subset.refl`：∀ {α : Type u_1} (s : Finset α), s ⊆ s
-/
theorem not_facet_iff_subface (hs : s ∈ K.faces) : s ∉ K.facets ↔ ∃ t, t ∈ K.faces ∧ s ⊂ t := by
  refine ⟨fun hs' : ¬(_ ∧ _) => ?_, ?_⟩
  · push Not at hs'
    obtain ⟨t, ht⟩ := hs' hs
    exact ⟨t, ht.1, ⟨ht.2.1, fun hts => ht.2.2 (Subset.antisymm ht.2.1 hts)⟩⟩
  · rintro ⟨t, ht⟩ ⟨hs, hs'⟩
    have := hs' ht.1 ht.2.1
    rw [this] at ht
    exact ht.2.2 (Subset.refl t)

/-!
### The semilattice of simplicial complexes

`K ≤ L` means that `K.faces ⊆ L.faces`.
-/


-- `HasSSubset.SSubset.ne` would be handy here
variable (𝕜 E)

/-- The complex consisting of only the faces present in both of its arguments. -/
/-
**Geometry.SimplicialComplex.** 是 Mathlib 中的一个实例，位于命名空间 `Geometry.SimplicialComp
lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The complex consisting of only the faces present in both of its arguments.
-/
instance : Min (SimplicialComplex 𝕜 E) :=
  ⟨fun K L =>
    { faces := K.faces ∩ L.faces
      indep := fun hs => K.indep hs.1
      isRelLowerSet_faces := K.isRelLowerSet_faces.inter L.isRelLowerSet_faces
      inter_subset_convexHull := fun hs ht => K.inter_subset_convexHull hs.1 ht.1 }⟩
/-
**Geometry.SimplicialComplex.** 是 Mathlib 中的一个实例，位于命名空间 `Geometry.SimplicialComp
lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SemilatticeInf (SimplicialComplex 𝕜 E) :=
  { PartialOrder.lift (fun K => K.faces) (fun _ _ => SimplicialComplex.ext) with
    inf := (· ⊓ ·)
    inf_le_left := fun _ _ _ hs => hs.1
    inf_le_right := fun _ _ _ hs => hs.2
    le_inf := fun _ _ _ hKL hKM _ hs => ⟨hKL hs, hKM hs⟩ }
/-
**Geometry.SimplicialComplex.hasBot** 是 Mathlib 中的一个实例，位于命名空间 `Geometry.Simplici
alComplex`。
形式化陈述：hasBot : Bot (SimplicialComplex 𝕜 E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasBot : Bot (SimplicialComplex 𝕜 E) :=
  ⟨{  faces := ∅
      indep := fun hs => (Set.notMem_empty _ hs).elim
      isRelLowerSet_faces := isRelLowerSet_empty
      inter_subset_convexHull := fun hs => (Set.notMem_empty _ hs).elim }⟩
/-
**Geometry.SimplicialComplex.** 是 Mathlib 中的一个实例，位于命名空间 `Geometry.SimplicialComp
lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderBot (SimplicialComplex 𝕜 E) :=
  { SimplicialComplex.hasBot 𝕜 E with bot_le := fun _ => Set.empty_subset _ }
/-
**Geometry.SimplicialComplex.** 是 Mathlib 中的一个实例，位于命名空间 `Geometry.SimplicialComp
lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (SimplicialComplex 𝕜 E) :=
  ⟨⊥⟩

variable {𝕜 E}
/-
**Geometry.SimplicialComplex.faces_bot** 是 Mathlib 中的一个定理，位于命名空间 `Geometry.Simpl
icialComplex`。
形式化陈述：faces_bot : (⊥ : SimplicialComplex 𝕜 E).faces = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem faces_bot : (⊥ : SimplicialComplex 𝕜 E).faces = ∅ := rfl
/-
**Geometry.SimplicialComplex.space_bot** 是 Mathlib 中的一个定理，位于命名空间 `Geometry.Simpl
icialComplex`。
形式化陈述：space_bot : (⊥ : SimplicialComplex 𝕜 E).space = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.biUnion_empty`：biUnion_empty (s : α -> Set β) : ⋃ x in (∅ : Set α), 
s x = ∅
-/
theorem space_bot : (⊥ : SimplicialComplex 𝕜 E).space = ∅ :=
  Set.biUnion_empty _
/-
**Geometry.SimplicialComplex.facets_bot** 是 Mathlib 中的一个定理，位于命名空间 `Geometry.Simp
licialComplex`。
形式化陈述：facets_bot : (⊥ : SimplicialComplex 𝕜 E).facets = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_of_subset_empty`：eq_empty_of_subset_empty {s : Set α} : s s
ubseteq ∅ -> s = ∅
· 使用定理 `Geometry.SimplicialComplex.facets_subset`：facets_subset : K.facets subse
teq K.faces
-/
theorem facets_bot : (⊥ : SimplicialComplex 𝕜 E).facets = ∅ :=
  eq_empty_of_subset_empty facets_subset

end SimplicialComplex

end Geometry

