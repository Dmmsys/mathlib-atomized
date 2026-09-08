/-
Copyright (c) 2026 A. M. Berns. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A. M. Berns
-/
module

public import Mathlib.Analysis.Convex.Between
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Tactic.Continuity

/-!
# Polygons

This file defines polygons in affine spaces.
For the special case `n = 3`, an interconversion is provided with `Affine.Triangle`.

## Main definitions

* `Polygon P n`: A polygon with `n` vertices in a type `P`.

-/

@[expose] public section

open Set

/-- A polygon with `n` vertices in a type `P`. -/
/-
**Polygon** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_1 → ℕ → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A polygon with `n` vertices in a type `P`.
-/
structure Polygon (P : Type*) (n : ℕ) where
  /-- The vertices of the polygon, indexed by `Fin n`. -/
  vertices : Fin n → P

namespace Polygon

variable {R V P : Type*} {n : ℕ}

/-- A coercion to function so that vertices can
be written as `poly i` instead of `poly.vertices i` -/
/-
**Polygon.** 是 Mathlib 中的一个实例，位于命名空间 `Polygon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A coercion to function so that vertices can
be written as `poly i` instead of `poly.vertices i`
-/
instance : CoeFun (Polygon P n) (fun _ => Fin n → P) where
  coe := Polygon.vertices

/-- A polygon has nondegenerate edges if adjacent vertices are distinct. -/
/-
**Polygon.HasNondegenerateEdges** 是 Mathlib 中的一个定义，位于命名空间 `Polygon`。
形式化陈述：HasNondegenerateEdges (poly : Polygon P n) : Prop
参数：poly : Polygon P n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A polygon has nondegenerate edges if adjacent vertices are distinct.
-/
def HasNondegenerateEdges (poly : Polygon P n) : Prop :=
  ∀ i : Fin n, poly i ≠ poly (finRotate n i)
/-
**Polygon.HasNondegenerateEdges.two_le** 是 Mathlib 中的一个定理，位于命名空间 `Polygon.HasNon
degenerateEdges`。
形式化陈述：∀ {P : Type u_3} {n : ℕ} [NeZero n] {poly : Polygon P n}, poly.HasNondegen
erateEdges → 2 ≤ n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `finRotate_one`：finRotate_one : finRotate 1 = Equiv.refl _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Nat.ge_of_not_lt`：∀ {n m : ℕ}, ¬n < m → n ≥ m
· 使用定理 `Mathlib.Tactic.IntervalCases.of_lt_right`：of_lt_right [LinearOrder α] (h
 : (a : α) < b) (eq : b = b') : ¬b' <= a
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
-/
theorem HasNondegenerateEdges.two_le [NeZero n] {poly : Polygon P n}
    (h : poly.HasNondegenerateEdges) : 2 ≤ n := by
  by_contra! hlt
  interval_cases n
  · simp_all only [neZero_zero_iff_false]
  · exact h 0 (by simp)

variable [Ring R] [AddCommGroup V] [Module R V] [AddTorsor V P]

variable (R) in
/-- The `i`-th edge as an affine map `R →ᵃ[R] P`. -/
/-
**Polygon.edgePath** 是 Mathlib 中的一个定义，位于命名空间 `Polygon`。
形式化陈述：edgePath (poly : Polygon P n) (i : Fin n) : R ->ᵃ[R] P
参数：poly : Polygon P n；i : Fin n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `i`-th edge as an affine map `R →ᵃ[R] P`.
-/
def edgePath (poly : Polygon P n) (i : Fin n) : R →ᵃ[R] P :=
  AffineMap.lineMap (poly i) (poly (finRotate n i))

variable (R) in
/-- The `i`-th edge as a set of points using an `affineSegment`. -/
/-
**Polygon.edgeSet** 是 Mathlib 中的一个定义，位于命名空间 `Polygon`。
形式化陈述：edgeSet [PartialOrder R] (poly : Polygon P n) (i : Fin n) : Set P
参数：poly : Polygon P n；i : Fin n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `i`-th edge as a set of points using an `affineSegment`.
-/
def edgeSet [PartialOrder R] (poly : Polygon P n) (i : Fin n) : Set P :=
  affineSegment R (poly i) (poly (finRotate n i))

variable (R) in
/-- The `edgeSet` is equivalent to the image of the `edgePath`. -/
/-
**Polygon.edgeSet_eq_image_edgePath** 是 Mathlib 中的一个定理，位于命名空间 `Polygon`。
形式化陈述：edgeSet_eq_image_edgePath [PartialOrder R] (poly : Polygon P n) (i : Fin n
) : poly.edgeSet R i = poly.edgePath R i '' Icc (0 : R) 1
参数：poly : Polygon P n；i : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `edgeSet` is equivalent to the image of the `edgePath`.
-/
theorem edgeSet_eq_image_edgePath [PartialOrder R] (poly : Polygon P n) (i : Fin n) :
    poly.edgeSet R i = poly.edgePath R i '' Icc (0 : R) 1 := rfl

variable (R) in
/-- The boundary of the polygon is the union of all its edges. -/
/-
**Polygon.boundary** 是 Mathlib 中的一个定义，位于命名空间 `Polygon`。
形式化陈述：boundary [PartialOrder R] (poly : Polygon P n) : Set P
参数：poly : Polygon P n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The boundary of the polygon is the union of all its edges.
-/
def boundary [PartialOrder R] (poly : Polygon P n) : Set P :=
  ⋃ i, poly.edgeSet R i

variable (R) in
/-- A polygon has nondegenerate vertices if any three consecutive vertices
are affinely independent. -/
/-
**Polygon.HasNondegenerateVertices** 是 Mathlib 中的一个定义，位于命名空间 `Polygon`。
形式化陈述：HasNondegenerateVertices [NeZero n] (poly : Polygon P n) : Prop
参数：poly : Polygon P n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A polygon has nondegenerate vertices if any three consecutive vertices
are affinely independent.
-/
def HasNondegenerateVertices [NeZero n] (poly : Polygon P n) : Prop :=
  ∀ i : Fin n, AffineIndependent R ![poly i, poly (i + 1), poly (i + 2)]

/-- Polygons with nondegenerate vertices also have nondegenerate edges. -/
/-
**Polygon.HasNondegenerateVertices.hasNondegenerateEdges** 是 Mathlib 中的一个定理，位于命名
空间 `Polygon.HasNondegenerateVertices`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_3} {n : ℕ} [inst : Ring R] [in
st_1 : AddCommGroup V]   [inst_2 : _root_.Module R V] [inst_3 : AddTorsor V P] [
inst_4 : NeZero n] [Nontrivial R] {poly : Polygon P n},   Polygon.HasNondegenera
teVertices R poly → poly.HasNondegenerateEdges
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_succ_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k.succ
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用引理 `Fin.neZero`：neZero {n : Nat} (i : Fin n) : NeZero n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finRotate_apply`：finRotate_apply (i : Fin n) : haveI
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `AffineIndependent.injective`：∀ {k : Type u_1} {V : Type u_2} {P : Type u
_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [in
st_3 : AddTorsor …
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Polygons with nondegenerate vertices also have nondegenerate edges.
-/
theorem HasNondegenerateVertices.hasNondegenerateEdges [NeZero n] [Nontrivial R]
    {poly : Polygon P n}
    (h : poly.HasNondegenerateVertices R) : poly.HasNondegenerateEdges := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  intro i
  simpa using (h i).injective.ne (by decide : (0 : Fin 3) ≠ 1)
/-
**Polygon.HasNondegenerateVertices.three_le** 是 Mathlib 中的一个定理，位于命名空间 `Polygon.H
asNondegenerateVertices`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_3} {n : ℕ} [inst : Ring R] [in
st_1 : AddCommGroup V]   [inst_2 : _root_.Module R V] [inst_3 : AddTorsor V P] [
inst_4 : NeZero n] [Nontrivial R] {poly : Polygon P n},   Polygon.HasNondegenera
teVertices R poly → 3 ≤ n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polygon.HasNondegenerateEdges.two_le`：∀ {P : Type u_3} {n : ℕ} [NeZero n
] {poly : Polygon P n}, poly.HasNondegenerateEdges → 2 ≤ n
· 使用定理 `Polygon.HasNondegenerateVertices.hasNondegenerateEdges`：∀ {R : Type u_1}
 {V : Type u_2} {P : Type u_3} {n : ℕ} [inst : Ring R] [inst_1 : AddCommGroup V]
   [inst_2 : _root_.Module R V] [inst_3 : Ad…
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `AffineIndependent.injective`：∀ {k : Type u_1} {V : Type u_2} {P : Type u
_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [in
st_3 : AddTorsor …
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Nat.ge_of_not_lt`：∀ {n m : ℕ}, ¬n < m → n ≥ m
· 使用定理 `Mathlib.Tactic.IntervalCases.of_lt_right`：of_lt_right [LinearOrder α] (h
 : (a : α) < b) (eq : b = b') : ¬b' <= a
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.IntervalCases.of_le_left`：of_le_left [LE α] (h : (a : α) 
<= b) (eq : a = a') : a' <= b
-/
theorem HasNondegenerateVertices.three_le [NeZero n] [Nontrivial R] {poly : Polygon P n}
    (h : poly.HasNondegenerateVertices R) : 3 ≤ n := by
  have := h.hasNondegenerateEdges.two_le
  by_contra! hlt
  interval_cases n
  exact (h 0).injective.ne (by decide : (0 : Fin 3) ≠ 2) (by simp)

end Polygon

/-! ### Interconversion with `Affine.Triangle` -/

namespace Affine.Triangle

variable {R V P : Type*}
variable [Ring R] [AddCommGroup V] [Module R V] [AddTorsor V P]

/-- Embedding from affine triangles to polygons with 3 vertices. -/
/-
**Affine.Triangle.toPolygon** 是 Mathlib 中的一个定义，位于命名空间 `Affine.Triangle`。
形式化陈述：toPolygon : Affine.Triangle R P ↪ Polygon P 3 where toFun t
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Embedding from affine triangles to polygons with 3 vertices.
-/
def toPolygon : Affine.Triangle R P ↪ Polygon P 3 where
  toFun t := ⟨t.points⟩
  inj' t₁ t₂ h := by
    apply Simplex.ext
    apply_fun Polygon.vertices at h
    simp_all

@[simp]
/-
**Affine.Triangle.toPolygon_vertices** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Triangle`
。
形式化陈述：toPolygon_vertices (t : Affine.Triangle R P) : (t.toPolygon).vertices = t.
points
参数：t : Affine.Triangle R P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toPolygon_vertices (t : Affine.Triangle R P) : (t.toPolygon).vertices = t.points := rfl

end Affine.Triangle

namespace Polygon

variable {R V P : Type*}
variable [Ring R] [AddCommGroup V] [Module R V] [AddTorsor V P]

variable (R) in
/-- Convert a polygon with 3 nondegenerate vertices to an `Affine.Triangle`. -/
/-
**Polygon.toTriangle** 是 Mathlib 中的一个定义，位于命名空间 `Polygon`。
形式化陈述：toTriangle (p : Polygon P 3) (h : p.HasNondegenerateVertices R) : Affine.T
riangle R P
参数：p : Polygon P 3；h : p.HasNondegenerateVertices R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert a polygon with 3 nondegenerate vertices to an `Affine.Triangle`.
-/
def toTriangle (p : Polygon P 3) (h : p.HasNondegenerateVertices R) :
    Affine.Triangle R P :=
  ⟨p.vertices, by
    have : p.vertices = ![p.vertices 0, p.vertices 1, p.vertices 2] := List.ofFn_inj.mp rfl
    rw [this]
    apply h⟩

@[simp]
/-
**Polygon.toTriangle_points** 是 Mathlib 中的一个引理，位于命名空间 `Polygon`。
形式化陈述：toTriangle_points (p : Polygon P 3) (h : p.HasNondegenerateVertices R) : (
p.toTriangle R h).points = p.vertices
参数：p : Polygon P 3；h : p.HasNondegenerateVertices R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma toTriangle_points (p : Polygon P 3) (h : p.HasNondegenerateVertices R) :
    (p.toTriangle R h).points = p.vertices := rfl

/-- Converting a 3-polygon to a triangle and back yields the original polygon. -/
@[simp]
/-
**Polygon.toTriangle_toPolygon** 是 Mathlib 中的一个引理，位于命名空间 `Polygon`。
形式化陈述：toTriangle_toPolygon (poly : Polygon P 3) (h : poly.HasNondegenerateVertic
es R) : (poly.toTriangle R h).toPolygon = poly
参数：poly : Polygon P 3；h : poly.HasNondegenerateVertices R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)

--- 原说明 ---
Converting a 3-polygon to a triangle and back yields the original polygon.
-/
lemma toTriangle_toPolygon (poly : Polygon P 3) (h : poly.HasNondegenerateVertices R) :
    (poly.toTriangle R h).toPolygon = poly := by
  rfl

end Polygon

namespace Affine.Triangle

variable {R V P : Type*}
variable [Ring R] [AddCommGroup V] [Module R V] [AddTorsor V P]

/-- The polygon obtained from a triangle has nondegenerate vertices. -/
/-
**Affine.Triangle.toPolygon_hasNondegenerateVertices** 是 Mathlib 中的一个定理，位于命名空间 `
Affine.Triangle`。
形式化陈述：toPolygon_hasNondegenerateVertices (t : Affine.Triangle R P) : t.toPolygon
.HasNondegenerateVertices R
参数：t : Affine.Triangle R P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.ofFn_inj`：ofFn_inj {n : Nat} {f g : Fin n -> α} : ofFn f = ofFn g ↔
 f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Affine.Simplex.independent`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [ins
t_3 : AddTorsor …
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `AffineIndependent.comm_right`：AffineIndependent.comm_right {p₁ p₂ p₃ : P
} (h : AffineIndependent k ![p₁, p₂, p₃]) : AffineIndependent k ![p₁, p₃, p₂]
· 使用定理 `AffineIndependent.comm_left`：AffineIndependent.comm_left {p₁ p₂ p₃ : P} 
(h : AffineIndependent k ![p₁, p₂, p₃]) : AffineIndependent k ![p₂, p₁, p₃]
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))

--- 原说明 ---
The polygon obtained from a triangle has nondegenerate vertices.
-/
theorem toPolygon_hasNondegenerateVertices (t : Affine.Triangle R P) :
    t.toPolygon.HasNondegenerateVertices R := by
  have ht : t.points = ![t.points 0, t.points 1, t.points 2] := List.ofFn_inj.mp rfl
  have h : AffineIndependent R ![t.points 0, t.points 1, t.points 2] := by
    simpa [← ht] using t.independent
  intro i
  fin_cases i <;> dsimp
  exacts [h, h.comm_left.comm_right, h.comm_right.comm_left]

/-- Converting a triangle to a polygon and back yields the original triangle. -/
@[simp]
/-
**Affine.Triangle.toPolygon_toTriangle** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Triangl
e`。
形式化陈述：toPolygon_toTriangle (t : Affine.Triangle R P) : t.toPolygon.toTriangle R 
(toPolygon_hasNondegenerateVertices t) = t
参数：t : Affine.Triangle R P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Triangle.toPolygon_hasNondegenerateVertices`：toPolygon_hasNondege
nerateVertices (t : Affine.Triangle R P) : t.toPolygon.HasNondegenerateVertices 
R

--- 原说明 ---
Converting a triangle to a polygon and back yields the original triangle.
-/
lemma toPolygon_toTriangle (t : Affine.Triangle R P) :
    t.toPolygon.toTriangle R (toPolygon_hasNondegenerateVertices t) = t := by
  rfl

end Affine.Triangle

