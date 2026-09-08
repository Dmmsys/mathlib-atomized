/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Data.Finset.Sort
public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import Mathlib.LinearAlgebra.AffineSpace.Restrict

/-!
# Simplex in affine space

This file defines n-dimensional simplices in affine space.

## Main definitions

* `Simplex` is a bundled type with collection of `n + 1` points in affine space that are affinely
  independent, where `n` is the dimension of the simplex.

* `Triangle` is a simplex with three points, defined as an abbreviation for simplex with `n = 2`.

* `face` is a simplex with a subset of the points of the original simplex.

## References

* https://en.wikipedia.org/wiki/Simplex

-/

@[expose] public section

noncomputable section

open Finset Function Module
open scoped Affine

namespace Affine

variable (k : Type*) {V V₂ V₃ : Type*} (P P₂ P₃ : Type*)
variable [Ring k] [AddCommGroup V] [AddCommGroup V₂] [AddCommGroup V₃]
variable [Module k V] [Module k V₂] [Module k V₃]
variable [AffineSpace V P] [AffineSpace V₂ P₂] [AffineSpace V₃ P₃]

/-- A `Simplex k P n` is a collection of `n + 1` affinely
independent points. -/
/-
**Affine.Simplex** 是 Mathlib 中的一个归纳类型，位于命名空间 `Affine`。
形式化陈述：(k : Type u_1) →   {V : Type u_2} →     (P : Type u_5) → [inst : Ring k] →
 [inst_1 : AddCommGroup V] → [_root_.Module k V] → [AddTorsor V P] → ℕ → Type u_
5
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Simplex k P n` is a collection of `n + 1` affinely
independent points.
-/
structure Simplex (n : ℕ) where
  points : Fin (n + 1) → P
  independent : AffineIndependent k points

/-- A `Triangle k P` is a collection of three affinely independent points. -/
/-
**Affine.Triangle** 是 Mathlib 中的一个缩写定义，位于命名空间 `Affine`。
形式化陈述：Triangle
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Triangle k P` is a collection of three affinely independent points.
-/
abbrev Triangle :=
  Simplex k P 2

namespace Simplex

variable {P P₂ P₃}

/-- Construct a 0-simplex from a point. -/
/-
**Affine.Simplex.mkOfPoint** 是 Mathlib 中的一个定义，位于命名空间 `Affine.Simplex`。
形式化陈述：mkOfPoint (p : P) : Simplex k P 0
参数：p : P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a 0-simplex from a point.
-/
def mkOfPoint (p : P) : Simplex k P 0 :=
  have : Subsingleton (Fin (1 + 0)) := by rw [add_zero]; infer_instance
  ⟨fun _ => p, affineIndependent_of_subsingleton k _⟩

/-- The point in a simplex constructed with `mkOfPoint`. -/
@[simp]
/-
**Affine.Simplex.mkOfPoint_points** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：mkOfPoint_points (p : P) (i : Fin 1) : (mkOfPoint k p).points i = p
参数：p : P；i : Fin 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The point in a simplex constructed with `mkOfPoint`.
-/
theorem mkOfPoint_points (p : P) (i : Fin 1) : (mkOfPoint k p).points i = p :=
  rfl
/-
**Affine.Simplex.** 是 Mathlib 中的一个实例，位于命名空间 `Affine.Simplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited P] : Inhabited (Simplex k P 0) :=
  ⟨mkOfPoint k default⟩
/-
**Affine.Simplex.nonempty** 是 Mathlib 中的一个实例，位于命名空间 `Affine.Simplex`。
形式化陈述：nonempty : Nonempty (Simplex k P 0)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
-/
instance nonempty : Nonempty (Simplex k P 0) :=
  ⟨mkOfPoint k <| AddTorsor.nonempty.some⟩

-- Although `simp` can prove this, it is still useful as a `simp` lemma, since the `simp`-generated
-- proof uses `range_eq_singleton_iff`, which does not apply when the LHS of this lemma appears
-- as part of a more complicated expression.
/-- The set of points in a simplex constructed with `mkOfPoint`. -/
/-
**Affine.Simplex.range_mkOfPoint_points** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simple
x`。
形式化陈述：∀ (k : Type u_1) {V : Type u_2} {P : Type u_5} [inst : Ring k] [inst_1 : A
ddCommGroup V] [inst_2 : _root_.Module k V]   [inst_3 : AddTorsor V P] (p : P), 
Set.range (Affine.Simplex.mkOfPoint k p).points = {p}
参数：k : Type u_1；p : P；Affine.Simplex.mkOfPoint k p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
The set of points in a simplex constructed with `mkOfPoint`.
-/
@[simp] lemma range_mkOfPoint_points (p : P) : Set.range (mkOfPoint k p).points = {p} := by
  simp

variable {k}

/-- Two simplices are equal if they have the same points. -/
@[ext]
/-
**Affine.Simplex.ext** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：ext {n : Nat} {s1 s2 : Simplex k P n} (h : forall i, s1.points i = s2.poin
ts i) : s1 = s2
参数：h : forall i, s1.points i = s2.points i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Two simplices are equal if they have the same points.
-/
theorem ext {n : ℕ} {s1 s2 : Simplex k P n} (h : ∀ i, s1.points i = s2.points i) : s1 = s2 := by
  cases s1
  cases s2
  congr with i
  exact h i

/-- Two simplices are equal if and only if they have the same points. -/
add_decl_doc Affine.Simplex.ext_iff

/-- A face of a simplex is a simplex with the given subset of
points. -/
/-
**Affine.Simplex.face** 是 Mathlib 中的一个定义，位于命名空间 `Affine.Simplex`。
形式化陈述：face {n : Nat} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : Nat} (
h : #fs = m + 1) : Simplex k P m
参数：s : Simplex k P n；Fin (n + 1)；h : #fs = m + 1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A face of a simplex is a simplex with the given subset of
points.
-/
def face {n : ℕ} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : ℕ} (h : #fs = m + 1) :
    Simplex k P m :=
  ⟨s.points ∘ fs.orderEmbOfFin h, s.independent.comp_embedding (fs.orderEmbOfFin h).toEmbedding⟩

/-- The points of a face of a simplex are given by `mono_of_fin`. -/
/-
**Affine.Simplex.face_points** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：face_points {n : Nat} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m :
 Nat} (h : #fs = m + 1) (i : Fin (m + 1)) : (s.face h).points i = s.points (fs.o
rderEmbOfFin h i)
参数：s : Simplex k P n；Fin (n + 1)；h : #fs = m + 1；i : Fin (m + 1)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The points of a face of a simplex are given by `mono_of_fin`.
-/
theorem face_points {n : ℕ} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : ℕ}
    (h : #fs = m + 1) (i : Fin (m + 1)) :
    (s.face h).points i = s.points (fs.orderEmbOfFin h i) :=
  rfl

/-- The points of a face of a simplex are given by `mono_of_fin`. -/
/-
**Affine.Simplex.face_points'** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：face_points' {n : Nat} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m 
: Nat} (h : #fs = m + 1) : (s.face h).points = s.points ∘ fs.orderEmbOfFin h
参数：s : Simplex k P n；Fin (n + 1)；h : #fs = m + 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The points of a face of a simplex are given by `mono_of_fin`.
-/
theorem face_points' {n : ℕ} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : ℕ}
    (h : #fs = m + 1) : (s.face h).points = s.points ∘ fs.orderEmbOfFin h :=
  rfl

/-- A single-point face equals the 0-simplex constructed with
`mkOfPoint`. -/
@[simp]
/-
**Affine.Simplex.face_eq_mkOfPoint** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：face_eq_mkOfPoint {n : Nat} (s : Simplex k P n) (i : Fin (n + 1)) : s.face
 (Finset.card_singleton i) = mkOfPoint k (s.points i)
参数：s : Simplex k P n；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.ext`：ext {n : Nat} {s1 s2 : Simplex k P n} (h : forall i,
 s1.points i = s2.points i) : s1 = s2
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.orderEmbOfFin_singleton`：orderEmbOfFin_singleton (a : α) (i : Fin
 1) : orderEmbOfFin {a} (card_singleton a) i = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A single-point face equals the 0-simplex constructed with
`mkOfPoint`.
-/
theorem face_eq_mkOfPoint {n : ℕ} (s : Simplex k P n) (i : Fin (n + 1)) :
    s.face (Finset.card_singleton i) = mkOfPoint k (s.points i) := by
  ext
  simp [Affine.Simplex.mkOfPoint_points, Affine.Simplex.face_points, Finset.orderEmbOfFin_singleton]

/-- The set of points of a face. -/
@[simp]
/-
**Affine.Simplex.range_face_points** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：range_face_points {n : Nat} (s : Simplex k P n) {fs : Finset (Fin (n + 1))
} {m : Nat} (h : #fs = m + 1) : Set.range (s.face h).points = s.points '' ↑fs
参数：s : Simplex k P n；Fin (n + 1)；h : #fs = m + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.face_points'`：face_points' {n : Nat} (s : Simplex k P n) 
{fs : Finset (Fin (n + 1))} {m : Nat} (h : #fs = m + 1) : (s.face h).points = s.
points ∘ fs.order…
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Finset.range_orderEmbOfFin`：range_orderEmbOfFin (s : Finset α) {k : Nat}
 (h : s.card = k) : Set.range (s.orderEmbOfFin h) = s

--- 原说明 ---
The set of points of a face.
-/
theorem range_face_points {n : ℕ} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : ℕ}
    (h : #fs = m + 1) : Set.range (s.face h).points = s.points '' ↑fs := by
  rw [face_points', Set.range_comp, Finset.range_orderEmbOfFin]
/-
**Affine.Simplex.affineSpan_face_le** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simplex`。
形式化陈述：affineSpan_face_le {n : Nat} (s : Simplex k P n) {fs : Finset (Fin (n + 1)
)} {m : Nat} (h : #fs = m + 1) : affineSpan k (Set.range (s.face h).points) <= a
ffineSpan k (Set.range s.points)
参数：s : Simplex k P n；Fin (n + 1)；h : #fs = m + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `affineSpan_mono`：affineSpan_mono {s₁ s₂ : Set P} (h : s₁ subseteq s₂) : 
affineSpan k s₁ <= affineSpan k s₂
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Affine.Simplex.range_face_points`：range_face_points {n : Nat} (s : Simpl
ex k P n) {fs : Finset (Fin (n + 1))} {m : Nat} (h : #fs = m + 1) : Set.range (s
.face h).points = s.po…
-/
lemma affineSpan_face_le {n : ℕ} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : ℕ}
    (h : #fs = m + 1) :
    affineSpan k (Set.range (s.face h).points) ≤ affineSpan k (Set.range s.points) :=
  affineSpan_mono k (s.range_face_points h ▸ Set.image_subset_range _ _)
/-
**Affine.Simplex.points_mem_affineSpan_face** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Si
mplex`。
形式化陈述：points_mem_affineSpan_face [Nontrivial k] {n : Nat} (s : Simplex k P n) {f
s : Finset (Fin (n + 1))} {m : Nat} (h : #fs = m + 1) {i : Fin (n + 1)} : s.poin
ts i in affineSpan k (Set.range (s.face h).points) ↔ i in fs
参数：s : Simplex k P n；Fin (n + 1)；h : #fs = m + 1；n + 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.range_face_points`：range_face_points {n : Nat} (s : Simpl
ex k P n) {fs : Finset (Fin (n + 1))} {m : Nat} (h : #fs = m + 1) : Set.range (s
.face h).points = s.po…
· 使用定理 `AffineIndependent.mem_affineSpan_iff`：∀ {k : Type u_1} {V : Type u_2} {P
 : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k
 V]   [inst_3 : AddTorsor …
· 使用定理 `Affine.Simplex.independent`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [ins
t_3 : AddTorsor …
-/
lemma points_mem_affineSpan_face [Nontrivial k] {n : ℕ} (s : Simplex k P n)
    {fs : Finset (Fin (n + 1))} {m : ℕ} (h : #fs = m + 1) {i : Fin (n + 1)} :
    s.points i ∈ affineSpan k (Set.range (s.face h).points) ↔ i ∈ fs := by
  rw [range_face_points]
  exact s.independent.mem_affineSpan_iff i fs

/-- The face of a simplex with all but one point. -/
/-
**Affine.Simplex.faceOpposite** 是 Mathlib 中的一个定义，位于命名空间 `Affine.Simplex`。
形式化陈述：faceOpposite {n : Nat} [NeZero n] (s : Simplex k P n) (i : Fin (n + 1)) : 
Simplex k P (n - 1)
参数：s : Simplex k P n；i : Fin (n + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The face of a simplex with all but one point.
-/
def faceOpposite {n : ℕ} [NeZero n] (s : Simplex k P n) (i : Fin (n + 1)) : Simplex k P (n - 1) :=
  s.face (fs := {i}ᶜ) (by simp [card_compl, NeZero.one_le])
/-
**Affine.Simplex.range_faceOpposite_points** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Sim
plex`。
形式化陈述：∀ {k : Type u_1} {V : Type u_2} {P : Type u_5} [inst : Ring k] [inst_1 : A
ddCommGroup V] [inst_2 : _root_.Module k V]   [inst_3 : AddTorsor V P] {n : ℕ} [
inst_4 : NeZero n] (s : Affine.Simplex k P n) (i : Fin (n + 1)),   Set.range (s.
faceOpposite i).points = s.points '' {i}ᶜ
参数：s : Affine.Simplex k P n；i : Fin (n + 1)；s.faceOpposite i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.range_face_points`：range_face_points {n : Nat} (s : Simpl
ex k P n) {fs : Finset (Fin (n + 1))} {m : Nat} (h : #fs = m + 1) : Set.range (s
.face h).points = s.po…
· 使用定理 `Finset.coe_compl`：coe_compl (s : Finset α) : ↑sᶜ = (↑s : Set α)ᶜ
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma range_faceOpposite_points {n : ℕ} [NeZero n] (s : Simplex k P n) (i : Fin (n + 1)) :
    Set.range (s.faceOpposite i).points = s.points '' {i}ᶜ := by
  simp [faceOpposite]
/-
**Affine.Simplex.affineSpan_faceOpposite_le** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Si
mplex`。
形式化陈述：affineSpan_faceOpposite_le {n : Nat} [NeZero n] (s : Simplex k P n) (i : F
in (n + 1)) : affineSpan k (Set.range (s.faceOpposite i).points) <= affineSpan k
 (Set.range s.points)
参数：s : Simplex k P n；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Affine.Simplex.affineSpan_face_le`：affineSpan_face_le {n : Nat} (s : Sim
plex k P n) {fs : Finset (Fin (n + 1))} {m : Nat} (h : #fs = m + 1) : affineSpan
 k (Set.range (s.face h…
-/
lemma affineSpan_faceOpposite_le {n : ℕ} [NeZero n] (s : Simplex k P n) (i : Fin (n + 1)) :
    affineSpan k (Set.range (s.faceOpposite i).points) ≤ affineSpan k (Set.range s.points) :=
  s.affineSpan_face_le _
/-
**Affine.Simplex.points_mem_affineSpan_faceOpposite** 是 Mathlib 中的一个引理，位于命名空间 `A
ffine.Simplex`。
形式化陈述：points_mem_affineSpan_faceOpposite [Nontrivial k] {n : Nat} [NeZero n] (s 
: Simplex k P n) {i j : Fin (n + 1)} : s.points j in affineSpan k (Set.range (s.
faceOpposite i).points) ↔ j != i
参数：s : Simplex k P n；n + 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.faceOpposite.eq_1`：∀ {k : Type u_1} {V : Type u_2} {P : T
ype u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V] 
  [inst_3 : AddTorsor …
· 使用引理 `Affine.Simplex.points_mem_affineSpan_face`：points_mem_affineSpan_face [N
ontrivial k] {n : Nat} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : Nat}
 (h : #fs = m + 1) {i : Fin (n …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma points_mem_affineSpan_faceOpposite [Nontrivial k] {n : ℕ} [NeZero n] (s : Simplex k P n)
    {i j : Fin (n + 1)} :
    s.points j ∈ affineSpan k (Set.range (s.faceOpposite i).points) ↔ j ≠ i := by
  rw [faceOpposite, s.points_mem_affineSpan_face]
  simp
/-
**Affine.Simplex.points_notMem_affineSpan_faceOpposite** 是 Mathlib 中的一个引理，位于命名空间
 `Affine.Simplex`。
形式化陈述：points_notMem_affineSpan_faceOpposite [Nontrivial k] {n : Nat} [NeZero n] 
(s : Simplex k P n) (i : Fin (n + 1)) : s.points i ∉ affineSpan k (Set.range (s.
faceOpposite i).points)
参数：s : Simplex k P n；i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Affine.Simplex.points_mem_affineSpan_faceOpposite`：points_mem_affineSpan
_faceOpposite [Nontrivial k] {n : Nat} [NeZero n] (s : Simplex k P n) {i j : Fin
 (n + 1)} : s.points j in affineSpan k …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma points_notMem_affineSpan_faceOpposite [Nontrivial k] {n : ℕ} [NeZero n] (s : Simplex k P n)
    (i : Fin (n + 1)) : s.points i ∉ affineSpan k (Set.range (s.faceOpposite i).points) := by
  rw [points_mem_affineSpan_faceOpposite]
  simp
/-
**Affine.Simplex.faceOpposite_point_eq_point_succAbove** 是 Mathlib 中的一个引理，位于命名空间
 `Affine.Simplex`。
形式化陈述：faceOpposite_point_eq_point_succAbove {n : Nat} [NeZero n] (s : Simplex k 
P n) (i : Fin (n + 1)) (j : Fin (n - 1 + 1)) : (s.faceOpposite i).points j = s.p
oints (Fin.succAbove i (Fin.cast (Nat.sub_one_add_one (NeZero.ne _)) j))
参数：s : Simplex k P n；i : Fin (n + 1)；j : Fin (n - 1 + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.sub_one_add_one`：∀ {a : ℕ}, a ≠ 0 → a - 1 + 1 = a
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.orderEmbOfFin_compl_singleton_apply`：orderEmbOfFin_compl_singleto
n_apply {n : Nat} {i : Fin (n + 1)} {k : Nat} (h : ({i}ᶜ : Finset _).card = k) (
j : Fin k) : ({i}ᶜ : Finset _).o…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma faceOpposite_point_eq_point_succAbove {n : ℕ} [NeZero n] (s : Simplex k P n)
    (i : Fin (n + 1)) (j : Fin (n - 1 + 1)) :
    (s.faceOpposite i).points j =
      s.points (Fin.succAbove i (Fin.cast (Nat.sub_one_add_one (NeZero.ne _)) j)) := by
  simp_rw [faceOpposite, face, comp_apply, Finset.orderEmbOfFin_compl_singleton_apply]
/-
**Affine.Simplex.faceOpposite_point_eq_point_rev** 是 Mathlib 中的一个引理，位于命名空间 `Affi
ne.Simplex`。
形式化陈述：faceOpposite_point_eq_point_rev (s : Simplex k P 1) (i : Fin 2) (n : Fin 1
) : (s.faceOpposite i).points n = s.points i.rev
参数：s : Simplex k P 1；i : Fin 2；n : Fin 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Affine.Simplex.faceOpposite_point_eq_point_succAbove`：faceOpposite_point
_eq_point_succAbove {n : Nat} [NeZero n] (s : Simplex k P n) (i : Fin (n + 1)) (
j : Fin (n - 1 + 1)) : (s.faceOpposite i).…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma faceOpposite_point_eq_point_rev (s : Simplex k P 1) (i : Fin 2) (n : Fin 1) :
    (s.faceOpposite i).points n = s.points i.rev := by
  have h : i.rev = Fin.succAbove i n := by decide +revert
  simp [h, faceOpposite_point_eq_point_succAbove]
/-
**Affine.Simplex.faceOpposite_point_eq_point_one** 是 Mathlib 中的一个定理，位于命名空间 `Affi
ne.Simplex`。
形式化陈述：∀ {k : Type u_1} {V : Type u_2} {P : Type u_5} [inst : Ring k] [inst_1 : A
ddCommGroup V] [inst_2 : _root_.Module k V]   [inst_3 : AddTorsor V P] (s : Affi
ne.Simplex k P 1) (n : Fin 1), (s.faceOpposite 0).points n = s.points 1
参数：s : Affine.Simplex k P 1；n : Fin 1；s.faceOpposite 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Affine.Simplex.faceOpposite_point_eq_point_rev`：faceOpposite_point_eq_po
int_rev (s : Simplex k P 1) (i : Fin 2) (n : Fin 1) : (s.faceOpposite i).points 
n = s.points i.rev
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
@[simp] lemma faceOpposite_point_eq_point_one (s : Simplex k P 1) (n : Fin 1) :
    (s.faceOpposite 0).points n = s.points 1 :=
  s.faceOpposite_point_eq_point_rev _ _
/-
**Affine.Simplex.faceOpposite_point_eq_point_zero** 是 Mathlib 中的一个定理，位于命名空间 `Aff
ine.Simplex`。
形式化陈述：∀ {k : Type u_1} {V : Type u_2} {P : Type u_5} [inst : Ring k] [inst_1 : A
ddCommGroup V] [inst_2 : _root_.Module k V]   [inst_3 : AddTorsor V P] (s : Affi
ne.Simplex k P 1) (n : Fin 1), (s.faceOpposite 1).points n = s.points 0
参数：s : Affine.Simplex k P 1；n : Fin 1；s.faceOpposite 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Affine.Simplex.faceOpposite_point_eq_point_rev`：faceOpposite_point_eq_po
int_rev (s : Simplex k P 1) (i : Fin 2) (n : Fin 1) : (s.faceOpposite i).points 
n = s.points i.rev
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
@[simp] lemma faceOpposite_point_eq_point_zero (s : Simplex k P 1) (n : Fin 1) :
    (s.faceOpposite 1).points n = s.points 0 :=
  s.faceOpposite_point_eq_point_rev _ _

/-- Needed to make `affineSpan (s.points '' {i}ᶜ)` nonempty. -/
/-
**Affine.Simplex.** 是 Mathlib 中的一个实例，位于命名空间 `Affine.Simplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Needed to make `affineSpan (s.points '' {i}ᶜ)` nonempty.
-/
instance {α} [Nontrivial α] (i : α) : Nonempty ({i}ᶜ : Set _) :=
  (Set.nonempty_compl_of_nontrivial i).to_subtype
/-
**Affine.Simplex.mem_affineSpan_image_iff** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simp
lex`。
形式化陈述：∀ {k : Type u_1} {V : Type u_2} {P : Type u_5} [inst : Ring k] [inst_1 : A
ddCommGroup V] [inst_2 : _root_.Module k V]   [inst_3 : AddTorsor V P] [Nontrivi
al k] {n : ℕ} (s : Affine.Simplex k P n) {fs : Set (Fin (n + 1))} {i : Fin (n + 
1)},   s.points i ∈ affineSpan k (s.points '' fs) ↔ i ∈ fs
参数：s : Affine.Simplex k P n；Fin (n + 1)；n + 1；s.points '' fs。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIndependent.mem_affineSpan_iff`：∀ {k : Type u_1} {V : Type u_2} {P
 : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k
 V]   [inst_3 : AddTorsor …
· 使用定理 `Affine.Simplex.independent`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [ins
t_3 : AddTorsor …
-/
@[simp] lemma mem_affineSpan_image_iff [Nontrivial k] {n : ℕ} (s : Simplex k P n)
    {fs : Set (Fin (n + 1))} {i : Fin (n + 1)} :
    s.points i ∈ affineSpan k (s.points '' fs) ↔ i ∈ fs :=
  s.independent.mem_affineSpan_iff _ _
/-
**Affine.Simplex.affineCombination_mem_affineSpan_faceOpposite_iff** 是 Mathlib 中
的一个引理，位于命名空间 `Affine.Simplex`。
形式化陈述：affineCombination_mem_affineSpan_faceOpposite_iff {n : Nat} [NeZero n] {s 
: Simplex k P n} {w : Fin (n + 1) -> k} (hw : ∑ i, w i = 1) {i : Fin (n + 1)} : 
Finset.univ.affineCombination k s.points w in affineSpan k (Set.range (s.faceOpp
osite i).points) ↔ w i = 0
参数：n + 1；hw : ∑ i, w i = 1；n + 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AffineIndependent.eq_zero_of_affineCombination_mem_affineSpan`：AffineInd
ependent.eq_zero_of_affineCombination_mem_affineSpan {p : ι -> P} (ha : AffineIn
dependent k p) {fs : Finset ι} {w : ι -> k} (hw : ∑…
· 使用定理 `Affine.Simplex.independent`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [ins
t_3 : AddTorsor …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.range_faceOpposite_points`：∀ {k : Type u_1} {V : Type u_2
} {P : Type u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Modu
le k V]   [inst_3 : AddTorsor …
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Module.subsingleton`：∀ (R : Type u_5) (M : Type u_6) [inst : MonoidWithZ
ero R] [Subsingleton R] [inst_2 : Zero M] [MulActionWithZero R M],   Subsingleto
n M
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AddTorsor.subsingleton_iff`：∀ (G : Type u_1) (P : Type u_2) [inst : AddG
roup G] [AddTorsor G P], Subsingleton G ↔ Subsingleton P
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `affineSpan_eq_top_iff_nonempty_of_subsingleton`：affineSpan_eq_top_iff_no
nempty_of_subsingleton [Subsingleton P] : affineSpan k s = ⊤ ↔ s.Nonempty
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用引理 `affineCombination_mem_affineSpan_image`：affineCombination_mem_affineSpan
_image [Nontrivial k] {s : Finset ι} {w : ι -> k} (h : ∑ i in s, w i = 1) {s' : 
Set ι} (hs' : forall i in s,…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma affineCombination_mem_affineSpan_faceOpposite_iff {n : ℕ} [NeZero n] {s : Simplex k P n}
    {w : Fin (n + 1) → k} (hw : ∑ i, w i = 1) {i : Fin (n + 1)} :
    Finset.univ.affineCombination k s.points w ∈
      affineSpan k (Set.range (s.faceOpposite i).points) ↔ w i = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [range_faceOpposite_points] at h
    exact s.independent.eq_zero_of_affineCombination_mem_affineSpan hw h (Finset.mem_univ i)
      (by simp)
  · rw [range_faceOpposite_points]
    rcases subsingleton_or_nontrivial k with hk | hk
    · have : Subsingleton V := Module.subsingleton k _
      have : Subsingleton P := (AddTorsor.subsingleton_iff V P).1 inferInstance
      rw [(affineSpan_eq_top_iff_nonempty_of_subsingleton k).2 (by simp)]
      simp
    · exact affineCombination_mem_affineSpan_image hw (by simpa using h) s.points

/-- Push forward an affine simplex under an injective affine map. -/
@[simps -fullyApplied]
/-
**Affine.Simplex.map** 是 Mathlib 中的一个定义，位于命名空间 `Affine.Simplex`。
形式化陈述：map {n : Nat} (s : Affine.Simplex k P n) (f : P ->ᵃ[k] P₂) (hf : Function.
Injective f) : Affine.Simplex k P₂ n where points
参数：s : Affine.Simplex k P n；f : P ->ᵃ[k] P₂；hf : Function.Injective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Push forward an affine simplex under an injective affine map.
-/
def map {n : ℕ} (s : Affine.Simplex k P n) (f : P →ᵃ[k] P₂) (hf : Function.Injective f) :
    Affine.Simplex k P₂ n where
  points := f ∘ s.points
  independent := s.independent.map' f hf

@[simp]
/-
**Affine.Simplex.map_id** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：map_id {n : Nat} (s : Affine.Simplex k P n) : s.map (AffineMap.id _ _) Fun
ction.injective_id = s
参数：s : Affine.Simplex k P n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.ext`：ext {n : Nat} {s1 s2 : Simplex k P n} (h : forall i,
 s1.points i = s2.points i) : s1 = s2
· 使用定理 `Function.injective_id`：∀ {α : Sort u_1}, Function.Injective id
-/
theorem map_id {n : ℕ} (s : Affine.Simplex k P n) :
    s.map (AffineMap.id _ _) Function.injective_id = s :=
  ext fun _ => rfl
/-
**Affine.Simplex.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：map_comp {n : Nat} (s : Affine.Simplex k P n) (f : P ->ᵃ[k] P₂) (hf : Func
tion.Injective f) (g : P₂ ->ᵃ[k] P₃) (hg : Function.Injective g) : s.map (g.comp
 f) (hg.comp hf) = (s.map f hf).map g hg
参数：s : Affine.Simplex k P n；f : P ->ᵃ[k] P₂；hf : Function.Injective f；g : P₂ ->ᵃ
[k] P₃；hg : Function.Injective g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.ext`：ext {n : Nat} {s1 s2 : Simplex k P n} (h : forall i,
 s1.points i = s2.points i) : s1 = s2
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
-/
theorem map_comp {n : ℕ} (s : Affine.Simplex k P n)
    (f : P →ᵃ[k] P₂) (hf : Function.Injective f)
    (g : P₂ →ᵃ[k] P₃) (hg : Function.Injective g) :
    s.map (g.comp f) (hg.comp hf) = (s.map f hf).map g hg :=
  ext fun _ => rfl

@[simp]
/-
**Affine.Simplex.face_map** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：face_map {n : Nat} (s : Simplex k P n) (f : P ->ᵃ[k] P₂) (hf : Function.In
jective f) {fs : Finset (Fin (n + 1))} {m : Nat} (h : #fs = m + 1) : (s.map f hf
).face h = (s.face h).map f hf
参数：s : Simplex k P n；f : P ->ᵃ[k] P₂；hf : Function.Injective f；Fin (n + 1)；h : #
fs = m + 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem face_map {n : ℕ} (s : Simplex k P n) (f : P →ᵃ[k] P₂) (hf : Function.Injective f)
    {fs : Finset (Fin (n + 1))} {m : ℕ} (h : #fs = m + 1) :
    (s.map f hf).face h = (s.face h).map f hf :=
  rfl

@[simp]
/-
**Affine.Simplex.faceOpposite_map** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：faceOpposite_map {n : Nat} [NeZero n] (s : Simplex k P n) (f : P ->ᵃ[k] P₂
) (hf : Function.Injective f) (i : Fin (n + 1)) : (s.map f hf).faceOpposite i = 
(s.faceOpposite i).map f hf
参数：s : Simplex k P n；f : P ->ᵃ[k] P₂；hf : Function.Injective f；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem faceOpposite_map {n : ℕ} [NeZero n] (s : Simplex k P n) (f : P →ᵃ[k] P₂)
    (hf : Function.Injective f) (i : Fin (n + 1)) :
    (s.map f hf).faceOpposite i = (s.faceOpposite i).map f hf :=
  rfl

@[simp]
/-
**Affine.Simplex.map_mkOfPoint** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：map_mkOfPoint (f : P ->ᵃ[k] P₂) (hf : Function.Injective f) (p : P) : (mkO
fPoint k p).map f hf = mkOfPoint k (f p)
参数：f : P ->ᵃ[k] P₂；hf : Function.Injective f；p : P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_mkOfPoint (f : P →ᵃ[k] P₂) (hf : Function.Injective f) (p : P) :
    (mkOfPoint k p).map f hf = mkOfPoint k (f p) :=
  rfl

/-- Remap a simplex along an `Equiv` of index types. -/
@[simps]
/-
**Affine.Simplex.reindex** 是 Mathlib 中的一个定义，位于命名空间 `Affine.Simplex`。
形式化陈述：reindex {m n : Nat} (s : Simplex k P m) (e : Fin (m + 1) ≃ Fin (n + 1)) : 
Simplex k P n
参数：s : Simplex k P m；e : Fin (m + 1) ≃ Fin (n + 1)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Remap a simplex along an `Equiv` of index types.
-/
def reindex {m n : ℕ} (s : Simplex k P m) (e : Fin (m + 1) ≃ Fin (n + 1)) : Simplex k P n :=
  ⟨s.points ∘ e.symm, (affineIndependent_equiv e.symm).2 s.independent⟩

/-- Reindexing by `Equiv.refl` yields the original simplex. -/
@[simp]
/-
**Affine.Simplex.reindex_refl** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：reindex_refl {n : Nat} (s : Simplex k P n) : s.reindex (Equiv.refl (Fin (n
 + 1))) = s
参数：s : Simplex k P n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.ext`：ext {n : Nat} {s1 s2 : Simplex k P n} (h : forall i,
 s1.points i = s2.points i) : s1 = s2
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
Reindexing by `Equiv.refl` yields the original simplex.
-/
theorem reindex_refl {n : ℕ} (s : Simplex k P n) : s.reindex (Equiv.refl (Fin (n + 1))) = s :=
  ext fun _ => rfl

/-- Reindexing by the composition of two equivalences is the same as reindexing twice. -/
@[simp]
/-
**Affine.Simplex.reindex_trans** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：reindex_trans {n₁ n₂ n₃ : Nat} (e₁₂ : Fin (n₁ + 1) ≃ Fin (n₂ + 1)) (e₂₃ : 
Fin (n₂ + 1) ≃ Fin (n₃ + 1)) (s : Simplex k P n₁) : s.reindex (e₁₂.trans e₂₃) = 
(s.reindex e₁₂).reindex e₂₃
参数：e₁₂ : Fin (n₁ + 1) ≃ Fin (n₂ + 1)；e₂₃ : Fin (n₂ + 1) ≃ Fin (n₃ + 1)；s : Simpl
ex k P n₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
Reindexing by the composition of two equivalences is the same as reindexing twic
e.
-/
theorem reindex_trans {n₁ n₂ n₃ : ℕ} (e₁₂ : Fin (n₁ + 1) ≃ Fin (n₂ + 1))
    (e₂₃ : Fin (n₂ + 1) ≃ Fin (n₃ + 1)) (s : Simplex k P n₁) :
    s.reindex (e₁₂.trans e₂₃) = (s.reindex e₁₂).reindex e₂₃ :=
  rfl

/-- Reindexing by an equivalence and its inverse yields the original simplex. -/
@[simp]
/-
**Affine.Simplex.reindex_reindex_symm** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`
。
形式化陈述：reindex_reindex_symm {m n : Nat} (s : Simplex k P m) (e : Fin (m + 1) ≃ Fi
n (n + 1)) : (s.reindex e).reindex e.symm = s
参数：s : Simplex k P m；e : Fin (m + 1) ≃ Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Affine.Simplex.reindex_trans`：reindex_trans {n₁ n₂ n₃ : Nat} (e₁₂ : Fin 
(n₁ + 1) ≃ Fin (n₂ + 1)) (e₂₃ : Fin (n₂ + 1) ≃ Fin (n₃ + 1)) (s : Simplex k P n₁
) : s.reindex (e₁₂…
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.self_trans_symm`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), e.trans 
e.symm = Equiv.refl α
· 使用定理 `Affine.Simplex.reindex_refl`：reindex_refl {n : Nat} (s : Simplex k P n) 
: s.reindex (Equiv.refl (Fin (n + 1))) = s

--- 原说明 ---
Reindexing by an equivalence and its inverse yields the original simplex.
-/
theorem reindex_reindex_symm {m n : ℕ} (s : Simplex k P m) (e : Fin (m + 1) ≃ Fin (n + 1)) :
    (s.reindex e).reindex e.symm = s := by rw [← reindex_trans, Equiv.self_trans_symm, reindex_refl]

/-- Reindexing by the inverse of an equivalence and that equivalence yields the original simplex. -/
@[simp]
/-
**Affine.Simplex.reindex_symm_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`
。
形式化陈述：reindex_symm_reindex {m n : Nat} (s : Simplex k P m) (e : Fin (n + 1) ≃ Fi
n (m + 1)) : (s.reindex e.symm).reindex e = s
参数：s : Simplex k P m；e : Fin (n + 1) ≃ Fin (m + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Affine.Simplex.reindex_trans`：reindex_trans {n₁ n₂ n₃ : Nat} (e₁₂ : Fin 
(n₁ + 1) ≃ Fin (n₂ + 1)) (e₂₃ : Fin (n₂ + 1) ≃ Fin (n₃ + 1)) (s : Simplex k P n₁
) : s.reindex (e₁₂…
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.symm_trans_self`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), e.symm.t
rans e = Equiv.refl β
· 使用定理 `Affine.Simplex.reindex_refl`：reindex_refl {n : Nat} (s : Simplex k P n) 
: s.reindex (Equiv.refl (Fin (n + 1))) = s

--- 原说明 ---
Reindexing by the inverse of an equivalence and that equivalence yields the orig
inal simplex.
-/
theorem reindex_symm_reindex {m n : ℕ} (s : Simplex k P m) (e : Fin (n + 1) ≃ Fin (m + 1)) :
    (s.reindex e.symm).reindex e = s := by rw [← reindex_trans, Equiv.symm_trans_self, reindex_refl]

/-- Reindexing a simplex produces one with the same set of points. -/
@[simp]
/-
**Affine.Simplex.reindex_range_points** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`
。
形式化陈述：reindex_range_points {m n : Nat} (s : Simplex k P m) (e : Fin (m + 1) ≃ Fi
n (n + 1)) : Set.range (s.reindex e).points = Set.range s.points
参数：s : Simplex k P m；e : Fin (m + 1) ≃ Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.reindex.eq_1`：∀ {k : Type u_1} {V : Type u_2} {P : Type u
_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [in
st_3 : AddTorsor …
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Equiv.range_eq_univ`：range_eq_univ (e : α ≃ β) : range e = univ
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f

--- 原说明 ---
Reindexing a simplex produces one with the same set of points.
-/
theorem reindex_range_points {m n : ℕ} (s : Simplex k P m) (e : Fin (m + 1) ≃ Fin (n + 1)) :
    Set.range (s.reindex e).points = Set.range s.points := by
  rw [reindex, Set.range_comp, Equiv.range_eq_univ, Set.image_univ]
/-
**Affine.Simplex.reindex_map** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：reindex_map {m n : Nat} (s : Simplex k P m) (e : Fin (m + 1) ≃ Fin (n + 1)
) (f : P ->ᵃ[k] P₂) (hf : Function.Injective f) : (s.map f hf).reindex e = (s.re
index e).map f hf
参数：s : Simplex k P m；e : Fin (m + 1) ≃ Fin (n + 1)；f : P ->ᵃ[k] P₂；hf : Function
.Injective f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem reindex_map {m n : ℕ} (s : Simplex k P m) (e : Fin (m + 1) ≃ Fin (n + 1))
    (f : P →ᵃ[k] P₂) (hf : Function.Injective f) :
    (s.map f hf).reindex e = (s.reindex e).map f hf :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**Affine.Simplex.range_face_reindex** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simplex`。
形式化陈述：range_face_reindex {m n : Nat} (s : Simplex k P m) (e : Fin (m + 1) ≃ Fin 
(n + 1)) {fs : Finset (Fin (n + 1))} {n' : Nat} (h : #fs = n' + 1) : Set.range (
(s.reindex e).face h).points = Set.range (s.face (fs
参数：s : Simplex k P m；e : Fin (m + 1) ≃ Fin (n + 1)；Fin (n + 1)；h : #fs = n' + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Affine.Simplex.range_face_points`：range_face_points {n : Nat} (s : Simpl
ex k P n) {fs : Finset (Fin (n + 1))} {m : Nat} (h : #fs = m + 1) : Set.range (s
.face h).points = s.po…
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Affine.Simplex.reindex_points`：∀ {k : Type u_1} {V : Type u_2} {P : Type
 u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [
inst_3 : AddTorsor …
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma range_face_reindex {m n : ℕ} (s : Simplex k P m) (e : Fin (m + 1) ≃ Fin (n + 1))
    {fs : Finset (Fin (n + 1))} {n' : ℕ} (h : #fs = n' + 1) :
    Set.range ((s.reindex e).face h).points =
      Set.range (s.face (fs := fs.map e.symm.toEmbedding) (h ▸ Finset.card_map _)).points := by
  simp only [range_face_points, reindex_points, Set.image_comp]
  simp
/-
**Affine.Simplex.range_faceOpposite_reindex** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Si
mplex`。
形式化陈述：range_faceOpposite_reindex {m n : Nat} [NeZero m] [NeZero n] (s : Simplex 
k P m) (e : Fin (m + 1) ≃ Fin (n + 1)) (i : Fin (n + 1)) : Set.range ((s.reindex
 e).faceOpposite i).points = Set.range (s.faceOpposite (e.symm i)).points
参数：s : Simplex k P m；e : Fin (m + 1) ≃ Fin (n + 1)；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.faceOpposite.eq_1`：∀ {k : Type u_1} {V : Type u_2} {P : T
ype u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V] 
  [inst_3 : AddTorsor …
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用引理 `Affine.Simplex.range_face_reindex`：range_face_reindex {m n : Nat} (s : S
implex k P m) (e : Fin (m + 1) ≃ Fin (n + 1)) {fs : Finset (Fin (n + 1))} {n' : 
Nat} (h : #fs = n' + 1)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Affine.Simplex.range_face_points`：range_face_points {n : Nat} (s : Simpl
ex k P n) {fs : Finset (Fin (n + 1))} {m : Nat} (h : #fs = m + 1) : Set.range (s
.face h).points = s.po…
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Finset.coe_compl`：coe_compl (s : Finset α) : ↑sᶜ = (↑s : Set α)ᶜ
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Equiv.image_compl`：∀ {α : Type u_3} {β : Type u_4} (f : α ≃ β) (s : Set 
α), ⇑f '' sᶜ = (⇑f '' s)ᶜ
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Affine.Simplex.range_faceOpposite_points`：∀ {k : Type u_1} {V : Type u_2
} {P : Type u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Modu
le k V]   [inst_3 : AddTorsor …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma range_faceOpposite_reindex {m n : ℕ} [NeZero m] [NeZero n] (s : Simplex k P m)
    (e : Fin (m + 1) ≃ Fin (n + 1)) (i : Fin (n + 1)) :
    Set.range ((s.reindex e).faceOpposite i).points =
      Set.range (s.faceOpposite (e.symm i)).points := by
  rw [faceOpposite, range_face_reindex]
  simp [Equiv.image_compl]

section restrict

/-- Restrict an affine simplex to an affine subspace that contains it. -/
@[simps]
/-
**Affine.Simplex.restrict** 是 Mathlib 中的一个定义，位于命名空间 `Affine.Simplex`。
形式化陈述：restrict {n : Nat} (s : Affine.Simplex k P n) (S : AffineSubspace k P) (hS
 : affineSpan k (Set.range s.points) <= S) : letI
参数：s : Affine.Simplex k P n；S : AffineSubspace k P；hS : affineSpan k (Set.range 
s.points) <= S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict an affine simplex to an affine subspace that contains it.
-/
def restrict {n : ℕ} (s : Affine.Simplex k P n) (S : AffineSubspace k P)
    (hS : affineSpan k (Set.range s.points) ≤ S) :
    letI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    Affine.Simplex (V := S.direction) k S n :=
  letI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  { points i := ⟨s.points i, hS <| mem_affineSpan _ <| Set.mem_range_self _⟩
    independent := AffineIndependent.of_comp S.subtype s.independent }

/-- Restricting to `S₁` then mapping to a larger `S₂` is the same as restricting to `S₂`. -/
@[simp]
/-
**Affine.Simplex.restrict_map_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simple
x`。
形式化陈述：restrict_map_inclusion {n : Nat} (s : Affine.Simplex k P n) (S₁ S₂ : Affin
eSubspace k P) (hS₁) (hS₂ : S₁ <= S₂) : letI
参数：s : Affine.Simplex k P n；S₁ S₂ : AffineSubspace k P；hS₁；hS₂ : S₁ <= S₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Set.inclusion_injective`：inclusion_injective (h : s subseteq t) : (inclu
sion h).Injective

--- 原说明 ---
Restricting to `S₁` then mapping to a larger `S₂` is the same as restricting to 
`S₂`.
-/
theorem restrict_map_inclusion {n : ℕ} (s : Affine.Simplex k P n)
    (S₁ S₂ : AffineSubspace k P) (hS₁) (hS₂ : S₁ ≤ S₂) :
    letI := Nonempty.map (AffineSubspace.inclusion hS₁) inferInstance
    letI := Nonempty.map (Set.inclusion hS₂) ‹_›
    (s.restrict S₁ hS₁).map (AffineSubspace.inclusion hS₂) (Set.inclusion_injective hS₂) =
      s.restrict S₂ (hS₁.trans hS₂) :=
  rfl

@[simp]
/-
**Affine.Simplex.map_subtype_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`
。
形式化陈述：map_subtype_restrict {n : Nat} (S : AffineSubspace k P) [Nonempty S] (s : 
Affine.Simplex k S n) : (s.map (AffineSubspace.subtype _) Subtype.coe_injective)
.restrict S (affineSpan_le.2 <| by rintro x ⟨y, rfl⟩; exact Subtype.prop _) = s
参数：S : AffineSubspace k P；s : Affine.Simplex k S n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `affineSpan_le`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_3} [inst : Ri
ng k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [S : AddTorsor V 
P] …
-/
theorem map_subtype_restrict
    {n : ℕ} (S : AffineSubspace k P) [Nonempty S] (s : Affine.Simplex k S n) :
    (s.map (AffineSubspace.subtype _) Subtype.coe_injective).restrict
      S (affineSpan_le.2 <| by rintro x ⟨y, rfl⟩; exact Subtype.prop _) = s := by
  rfl

/-- Restricting to `S₁` then mapping through the restriction of `f` to `S₁ →ᵃ[k] S₂` is the same
as mapping through unrestricted `f`, then restricting to `S₂`. -/
/-
**Affine.Simplex.restrict_map_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex
`。
形式化陈述：restrict_map_restrict {n : Nat} (s : Affine.Simplex k P n) (f : P ->ᵃ[k] P
₂) (hf : Function.Injective f) (S₁ : AffineSubspace k P) (S₂ : AffineSubspace k 
P₂) (hS₁ : affineSpan k (Set.range s.points) <= S₁) (hfS : AffineSubspace.map f 
S₁ <= S₂) : letI
参数：s : Affine.Simplex k P n；f : P ->ᵃ[k] P₂；hf : Function.Injective f；S₁ : Affin
eSubspace k P；S₂ : AffineSubspace k P₂；hS₁ : affineSpan k (Set.range s.points) <
= S₁；hfS : AffineSubspace.map f S₁ <= S₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `AffineMap.restrict.injective`：AffineMap.restrict.injective {φ : P₁ ->ᵃ[k
] P₂} (hφ : Function.Injective φ) {E : AffineSubspace k P₁} {F : AffineSubspace 
k P₂} [Nonempty E]…

--- 原说明 ---
Restricting to `S₁` then mapping through the restriction of `f` to `S₁ →ᵃ[k] S₂`
 is the same
as mapping through unrestricted `f`, then restricting to `S₂`.
-/
theorem restrict_map_restrict
    {n : ℕ} (s : Affine.Simplex k P n) (f : P →ᵃ[k] P₂) (hf : Function.Injective f)
    (S₁ : AffineSubspace k P) (S₂ : AffineSubspace k P₂)
    (hS₁ : affineSpan k (Set.range s.points) ≤ S₁) (hfS : AffineSubspace.map f S₁ ≤ S₂) :
    letI := Nonempty.map (AffineSubspace.inclusion hS₁) inferInstance
    letI := Nonempty.map (AffineSubspace.inclusion hfS) inferInstance
    (s.restrict S₁ hS₁).map (f.restrict hfS) (AffineMap.restrict.injective hf _) =
      (s.map f hf).restrict S₂ (Eq.trans_le
          (by simp [AffineSubspace.map_span, Set.range_comp])
          (AffineSubspace.map_mono f hS₁) |>.trans hfS) := by
  rfl

/-- Restricting to `affineSpan k (Set.range s.points)` can be reversed by mapping through
`AffineSubspace.subtype`. -/
@[simp]
/-
**Affine.Simplex.restrict_map_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`
。
形式化陈述：restrict_map_subtype {n : Nat} (s : Affine.Simplex k P n) : (s.restrict _ 
le_rfl).map (AffineSubspace.subtype _) Subtype.coe_injective = s
参数：s : Affine.Simplex k P n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))

--- 原说明 ---
Restricting to `affineSpan k (Set.range s.points)` can be reversed by mapping th
rough
`AffineSubspace.subtype`.
-/
theorem restrict_map_subtype {n : ℕ} (s : Affine.Simplex k P n) :
    (s.restrict _ le_rfl).map (AffineSubspace.subtype _) Subtype.coe_injective = s :=
  rfl
/-
**Affine.Simplex.restrict_reindex** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simplex`。
形式化陈述：restrict_reindex {m n : Nat} (s : Affine.Simplex k P n) (e : Fin (n + 1) ≃
 Fin (m + 1)) {S : AffineSubspace k P} (hS : affineSpan k (Set.range s.points) <
= S) : letI
参数：s : Affine.Simplex k P n；e : Fin (n + 1) ≃ Fin (m + 1)；hS : affineSpan k (Set
.range s.points) <= S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Affine.Simplex.reindex_range_points`：reindex_range_points {m n : Nat} (s
 : Simplex k P m) (e : Fin (m + 1) ≃ Fin (n + 1)) : Set.range (s.reindex e).poin
ts = Set.range s.points
-/
lemma restrict_reindex {m n : ℕ} (s : Affine.Simplex k P n) (e : Fin (n + 1) ≃ Fin (m + 1))
    {S : AffineSubspace k P} (hS : affineSpan k (Set.range s.points) ≤ S) :
    letI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.reindex e).restrict S (s.reindex_range_points e ▸ hS) = (s.restrict S hS).reindex e :=
  rfl
/-
**Affine.Simplex.face_restrict** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simplex`。
形式化陈述：face_restrict {n : Nat} (s : Affine.Simplex k P n) {S : AffineSubspace k P
} (hS : affineSpan k (Set.range s.points) <= S) {fs : Finset (Fin (n + 1))} {m :
 Nat} (h : #fs = m + 1) : letI
参数：s : Affine.Simplex k P n；hS : affineSpan k (Set.range s.points) <= S；Fin (n +
 1)；h : #fs = m + 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Affine.Simplex.ext`：ext {n : Nat} {s1 s2 : Simplex k P n} (h : forall i,
 s1.points i = s2.points i) : s1 = s2
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Affine.Simplex.affineSpan_face_le`：affineSpan_face_le {n : Nat} (s : Sim
plex k P n) {fs : Finset (Fin (n + 1))} {m : Nat} (h : #fs = m + 1) : affineSpan
 k (Set.range (s.face h…
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.restrict_points_coe`：∀ {k : Type u_1} {V : Type u_2} {P :
 Type u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V
]   [inst_3 : AddTorsor …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma face_restrict {n : ℕ} (s : Affine.Simplex k P n) {S : AffineSubspace k P}
    (hS : affineSpan k (Set.range s.points) ≤ S) {fs : Finset (Fin (n + 1))} {m : ℕ}
    (h : #fs = m + 1) :
    letI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).face h = (s.face h).restrict S ((s.affineSpan_face_le h).trans hS) := by
  let := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  ext i
  rw [restrict_points_coe]
  simp_rw [Affine.Simplex.face_points]
  simp
/-
**Affine.Simplex.faceOpposite_restrict** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simplex
`。
形式化陈述：faceOpposite_restrict {n : Nat} [NeZero n] (s : Affine.Simplex k P n) {S :
 AffineSubspace k P} (hS : affineSpan k (Set.range s.points) <= S) (i : Fin (n +
 1)) : letI
参数：s : Affine.Simplex k P n；hS : affineSpan k (Set.range s.points) <= S；i : Fin 
(n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Affine.Simplex.face_restrict`：face_restrict {n : Nat} (s : Affine.Simple
x k P n) {S : AffineSubspace k P} (hS : affineSpan k (Set.range s.points) <= S) 
{fs : Finset (Fin …
-/
lemma faceOpposite_restrict {n : ℕ} [NeZero n] (s : Affine.Simplex k P n) {S : AffineSubspace k P}
    (hS : affineSpan k (Set.range s.points) ≤ S) (i : Fin (n + 1)) :
    letI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).faceOpposite i = (s.faceOpposite i).restrict S
      ((s.affineSpan_faceOpposite_le i).trans hS) :=
  s.face_restrict hS _

end restrict

end Simplex

end Affine

namespace Affine

namespace Simplex

variable {k V V₂ P P₂ : Type*} [Ring k] [AddCommGroup V] [Module k V] [AffineSpace V P]
variable [AddCommGroup V₂] [Module k V₂] [AffineSpace V₂ P₂]

/-- The interior of a simplex is the set of points that can be expressed as an affine combination
of the vertices with weights in a set `I`. -/
/-
**Affine.Simplex.setInterior** 是 Mathlib 中的一个定义，位于命名空间 `Affine.Simplex`。
形式化陈述：{k : Type u_1} →   {V : Type u_2} →     {P : Type u_4} →       [inst : Rin
g k] →         [inst_1 : AddCommGroup V] →           [inst_2 : _root_.Module k V
] → [inst_3 : AddTorsor V P] → Set k → {n : ℕ} → Affine.Simplex k P n → Set P
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The interior of a simplex is the set of points that can be expressed as an affin
e combination
of the vertices with weights in a set `I`.
-/
protected def setInterior (I : Set k) {n : ℕ} (s : Simplex k P n) : Set P :=
  {p | ∃ w : Fin (n + 1) → k,
    (∑ i, w i = 1) ∧ (∀ i, w i ∈ I) ∧ Finset.univ.affineCombination k s.points w = p}
/-
**Affine.Simplex.affineCombination_mem_setInterior_iff** 是 Mathlib 中的一个引理，位于命名空间
 `Affine.Simplex`。
形式化陈述：affineCombination_mem_setInterior_iff {I : Set k} {n : Nat} {s : Simplex k
 P n} {w : Fin (n + 1) -> k} (hw : ∑ i, w i = 1) : Finset.univ.affineCombination
 k s.points w in s.setInterior I ↔ forall i, w i in I
参数：n + 1；hw : ∑ i, w i = 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `affineIndependent_iff_eq_of_fintype_affineCombination_eq`：affineIndepend
ent_iff_eq_of_fintype_affineCombination_eq [Fintype ι] (p : ι -> P) : AffineInde
pendent k p ↔ forall w1 w2 : ι -> k, ∑ i, w1 i…
· 使用定理 `Affine.Simplex.independent`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [ins
t_3 : AddTorsor …
-/
lemma affineCombination_mem_setInterior_iff {I : Set k} {n : ℕ} {s : Simplex k P n}
    {w : Fin (n + 1) → k} (hw : ∑ i, w i = 1) :
    Finset.univ.affineCombination k s.points w ∈ s.setInterior I ↔ ∀ i, w i ∈ I := by
  refine ⟨fun ⟨w', hw', hw'01, hww'⟩ ↦ ?_, fun h ↦ ⟨w, hw, h, rfl⟩⟩
  simp_rw [← (affineIndependent_iff_eq_of_fintype_affineCombination_eq k s.points).1
    s.independent w' w hw' hw hww']
  exact hw'01
/-
**Affine.Simplex.setInterior_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：∀ {k : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Ring k] [inst_1 : A
ddCommGroup V] [inst_2 : _root_.Module k V]   [inst_3 : AddTorsor V P] (I : Set 
k) {m n : ℕ} (s : Affine.Simplex k P n) (e : Fin (n + 1) ≃ Fin (m + 1)),   Affin
e.Simplex.setInterior I (s.reindex e) = Affine.Simplex.setInterior I s
参数：I : Set k；s : Affine.Simplex k P n；e : Fin (n + 1) ≃ Fin (m + 1)；s.reindex e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_id`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), f ∘ id = 
f
· 使用定理 `Equiv.self_comp_symm`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e ∘ ⇑e.s
ymm = id
· 使用定理 `Function.comp_assoc`：comp_assoc (f : φ -> δ) (g : β -> φ) (h : α -> β) :
 (f ∘ g) ∘ h = f ∘ g ∘ h
· 使用定理 `Equiv.coe_toEmbedding`：coe_toEmbedding : (f.toEmbedding : α -> β) = f
· 使用定理 `Finset.affineCombination_map`：affineCombination_map (e : ι₂ ↪ ι) (w : ι 
-> k) (p : ι -> P) : (s₂.map e).affineCombination k p w = s₂.affineCombination k
 (p ∘ e) (w ∘ e)
· 使用定理 `Finset.map_univ_equiv`：map_univ_equiv [Fintype β] (f : β ≃ α) : univ.map
 f.toEmbedding = univ
· 使用定理 `Finset.sum_comp_equiv`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} {s
 : Finset ι} [inst : AddCommMonoid M] {f : κ → M} (e : ι ≃ κ),   s.sum (f ∘ ⇑e) 
= (Finset.m…
· 使用引理 `Affine.Simplex.affineCombination_mem_setInterior_iff`：affineCombination_
mem_setInterior_iff {I : Set k} {n : Nat} {s : Simplex k P n} {w : Fin (n + 1) -
> k} (hw : ∑ i, w i = 1) : Finset.univ.aff…
· 使用定理 `Equiv.symm_comp_self`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e.symm ∘
 ⇑e = id
-/
@[simp] lemma setInterior_reindex (I : Set k) {m n : ℕ} (s : Simplex k P n)
    (e : Fin (n + 1) ≃ Fin (m + 1)) : (s.reindex e).setInterior I = s.setInterior I := by
  ext p
  refine ⟨fun ⟨w, hw, hwI, h⟩ ↦ ?_, fun ⟨w, hw, hwI, h⟩ ↦ ?_⟩
  · subst h
    simp_rw [reindex]
    rw [← Function.comp_id w, ← e.self_comp_symm, ← Function.comp_assoc,
      ← Equiv.coe_toEmbedding, ← Finset.univ.affineCombination_map e.symm.toEmbedding,
      map_univ_equiv]
    have hw' : ∑ i, (w ∘ e) i = 1 := by rwa [sum_comp_equiv, map_univ_equiv]
    rw [affineCombination_mem_setInterior_iff hw']
    exact fun i ↦ hwI (e i)
  · subst h
    rw [← Function.comp_id w, ← Function.comp_id s.points, ← e.symm_comp_self,
      ← Function.comp_assoc, ← Function.comp_assoc, ← e.coe_toEmbedding,
      ← Finset.univ.affineCombination_map e.toEmbedding, map_univ_equiv]
    change Finset.univ.affineCombination k (s.reindex e).points _ ∈ _
    have hw' : ∑ i, (w ∘ e.symm) i = 1 := by rwa [sum_comp_equiv, map_univ_equiv]
    rw [affineCombination_mem_setInterior_iff hw']
    exact fun i ↦ hwI (e.symm i)
/-
**Affine.Simplex.setInterior_mono** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simplex`。
形式化陈述：setInterior_mono {I J : Set k} (hij : I subseteq J) {n : Nat} (s : Simplex
 k P n) : s.setInterior I subseteq s.setInterior J
参数：hij : I subseteq J；s : Simplex k P n。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma setInterior_mono {I J : Set k} (hij : I ⊆ J) {n : ℕ} (s : Simplex k P n) :
    s.setInterior I ⊆ s.setInterior J :=
  fun _ ⟨w, hw, hw01, hww⟩ ↦ ⟨w, hw, fun i ↦ hij (hw01 i), hww⟩
/-
**Affine.Simplex.setInterior_subset_affineSpan** 是 Mathlib 中的一个引理，位于命名空间 `Affine
.Simplex`。
形式化陈述：setInterior_subset_affineSpan {I : Set k} {n : Nat} {s : Simplex k P n} : 
s.setInterior I subseteq affineSpan k (Set.range s.points)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `affineCombination_mem_affineSpan_of_nonempty`：affineCombination_mem_affi
neSpan_of_nonempty [Nonempty ι] {s : Finset ι} {w : ι -> k} (h : ∑ i in s, w i =
 1) (p : ι -> P) : s.affineCombina…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma setInterior_subset_affineSpan {I : Set k} {n : ℕ} {s : Simplex k P n} :
    s.setInterior I ⊆ affineSpan k (Set.range s.points) := by
  rintro p ⟨w, hw, hi, rfl⟩
  exact affineCombination_mem_affineSpan_of_nonempty hw _
/-
**Affine.Simplex.setInterior_map** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simplex`。
形式化陈述：setInterior_map (I : Set k) {n : Nat} (s : Simplex k P n) {f : P ->ᵃ[k] P₂
} (hf : Function.Injective f) : (s.map f hf).setInterior I = f '' s.setInterior 
I
参数：I : Set k；s : Simplex k P n；hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `eq_affineCombination_of_mem_affineSpan_of_fintype`：eq_affineCombination_
of_mem_affineSpan_of_fintype [Fintype ι] {p1 : P} {p : ι -> P} (h : p1 in affine
Span k (Set.range p)) : exists w : ι ->…
· 使用引理 `Affine.Simplex.affineCombination_mem_setInterior_iff`：affineCombination_
mem_setInterior_iff {I : Set k} {n : Nat} {s : Simplex k P n} {w : Fin (n + 1) -
> k} (hw : ∑ i, w i = 1) : Finset.univ.aff…
· 使用定理 `Affine.Simplex.map_points`：∀ {k : Type u_1} {V : Type u_2} {V₂ : Type u_
3} {P : Type u_5} {P₂ : Type u_6} [inst : Ring k] [inst_1 : AddCommGroup V]   [i
nst_2 : AddComm…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.map_affineCombination`：map_affineCombination {V₂ P₂ : Type*} [Add
CommGroup V₂] [Module k V₂] [AffineSpace V₂ P₂] (p : ι -> P) (w : ι -> k) (hw : 
s.sum w = 1) (f : …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `iff_of_false`：∀ {a b : Prop}, ¬a → ¬b → (a ↔ b)
· 使用定理 `Set.mem_of_mem_of_subset`：mem_of_mem_of_subset {x : α} {s t : Set α} (hx
 : x in s) (h : s subseteq t) : x in t
· 使用引理 `Affine.Simplex.setInterior_subset_affineSpan`：setInterior_subset_affineS
pan {I : Set k} {n : Nat} {s : Simplex k P n} : s.setInterior I subseteq affineS
pan k (Set.range s.points)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `AffineSubspace.map_span`：map_span (s : Set P₁) : (affineSpan k s).map f 
= affineSpan k (f '' s)
· 使用定理 `AffineSubspace.mem_map`：mem_map {f : P₁ ->ᵃ[k] P₂} {x : P₂} {s : AffineS
ubspace k P₁} : x in s.map f ↔ exists y in s, f y = x
-/
lemma setInterior_map (I : Set k) {n : ℕ} (s : Simplex k P n) {f : P →ᵃ[k] P₂}
    (hf : Function.Injective f) : (s.map f hf).setInterior I = f '' s.setInterior I := by
  ext p
  rw [Set.mem_image]
  by_cases hp : p ∈ affineSpan k (Set.range (s.map f hf).points)
  · obtain ⟨w, hw1, hw⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hp
    rw [hw, Affine.Simplex.affineCombination_mem_setInterior_iff hw1, Simplex.map_points,
      ← Finset.map_affineCombination _ _ _ hw1]
    simp_rw [hf.eq_iff]
    simp [Affine.Simplex.affineCombination_mem_setInterior_iff hw1]
  · apply iff_of_false
    · exact fun h ↦ hp (Set.mem_of_mem_of_subset h (s.map f hf).setInterior_subset_affineSpan)
    · contrapose hp
      obtain ⟨q, hq, hqp⟩ := hp
      rw [s.map_points, Set.range_comp, ← AffineSubspace.map_span, AffineSubspace.mem_map]
      exact ⟨q, (Set.mem_of_mem_of_subset hq s.setInterior_subset_affineSpan), hqp⟩
/-
**Affine.Simplex.setInterior_restrict** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simplex`
。
形式化陈述：setInterior_restrict (I : Set k) {n : Nat} (s : Simplex k P n) {S : Affine
Subspace k P} (hS : affineSpan k (Set.range s.points) <= S) : letI
参数：I : Set k；s : Simplex k P n；hS : affineSpan k (Set.range s.points) <= S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Function.Injective.image_injective`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Injective f → Function.Injective (Set.image f)
· 使用定理 `AffineSubspace.subtype_injective`：subtype_injective (s : AffineSubspace 
k P) [Nonempty s] : Function.Injective s.subtype
· 使用定理 `Set.image_preimage_eq_of_subset`：image_preimage_eq_of_subset {f : α -> β
} {s : Set β} (hs : s subseteq range f) : f '' f ⁻¹' s = s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Affine.Simplex.setInterior_subset_affineSpan`：setInterior_subset_affineS
pan {I : Set k} {n : Nat} {s : Simplex k P n} : s.setInterior I subseteq affineS
pan k (Set.range s.points)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用引理 `Affine.Simplex.setInterior_map`：setInterior_map (I : Set k) {n : Nat} (s
 : Simplex k P n) {f : P ->ᵃ[k] P₂} (hf : Function.Injective f) : (s.map f hf).s
etInterior I = f '' …
-/
lemma setInterior_restrict (I : Set k) {n : ℕ} (s : Simplex k P n) {S : AffineSubspace k P}
    (hS : affineSpan k (Set.range s.points) ≤ S) :
    letI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).setInterior I = S.subtype ⁻¹' (s.setInterior I) := by
  let := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  rw [← S.subtype_injective.image_injective.eq_iff,
    Set.image_preimage_eq_of_subset (s.setInterior_subset_affineSpan.trans (by simpa using! hS)),
    ← (s.restrict S hS).setInterior_map I S.subtype_injective]
  rfl

section PartialOrder
variable [PartialOrder k]

/-- The interior of a simplex is the set of points that can be expressed as an affine combination
of the vertices with weights strictly between 0 and 1. This is equivalent to the intrinsic
interior of the convex hull of the vertices. -/
/-
**Affine.Simplex.interior** 是 Mathlib 中的一个定义，位于命名空间 `Affine.Simplex`。
形式化陈述：{k : Type u_1} →   {V : Type u_2} →     {P : Type u_4} →       [inst : Rin
g k] →         [inst_1 : AddCommGroup V] →           [inst_2 : _root_.Module k V
] →             [inst_3 : AddTorsor V P] → [PartialOrder k] → {n : ℕ} → Affine.S
implex k P n → Set P
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The interior of a simplex is the set of points that can be expressed as an affin
e combination
of the vertices with weights strictly between 0 and 1. This is equivalent to the
 intrinsic
interior of the convex hull of the vertices.
-/
protected def interior {n : ℕ} (s : Simplex k P n) : Set P :=
  s.setInterior (Set.Ioo 0 1)
/-
**Affine.Simplex.interior_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：∀ {k : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Ring k] [inst_1 : A
ddCommGroup V] [inst_2 : _root_.Module k V]   [inst_3 : AddTorsor V P] [inst_4 :
 PartialOrder k] {m n : ℕ} (s : Affine.Simplex k P n)   (e : Fin (n + 1) ≃ Fin (
m + 1)), (s.reindex e).interior = s.interior
参数：s : Affine.Simplex k P n；e : Fin (n + 1) ≃ Fin (m + 1)；s.reindex e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.setInterior_reindex`：∀ {k : Type u_1} {V : Type u_2} {P :
 Type u_4} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V
]   [inst_3 : AddTorsor …
-/
@[simp] lemma interior_reindex {m n : ℕ} (s : Simplex k P n) (e : Fin (n + 1) ≃ Fin (m + 1)) :
    (s.reindex e).interior = s.interior :=
  s.setInterior_reindex _ _
/-
**Affine.Simplex.affineCombination_mem_interior_iff** 是 Mathlib 中的一个引理，位于命名空间 `A
ffine.Simplex`。
形式化陈述：affineCombination_mem_interior_iff {n : Nat} {s : Simplex k P n} {w : Fin 
(n + 1) -> k} (hw : ∑ i, w i = 1) : Finset.univ.affineCombination k s.points w i
n s.interior ↔ forall i, w i in Set.Ioo 0 1
参数：n + 1；hw : ∑ i, w i = 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Affine.Simplex.affineCombination_mem_setInterior_iff`：affineCombination_
mem_setInterior_iff {I : Set k} {n : Nat} {s : Simplex k P n} {w : Fin (n + 1) -
> k} (hw : ∑ i, w i = 1) : Finset.univ.aff…
-/
lemma affineCombination_mem_interior_iff {n : ℕ} {s : Simplex k P n} {w : Fin (n + 1) → k}
    (hw : ∑ i, w i = 1) :
    Finset.univ.affineCombination k s.points w ∈ s.interior ↔ ∀ i, w i ∈ Set.Ioo 0 1 :=
  affineCombination_mem_setInterior_iff hw

/-- `s.closedInterior` is the set of points that can be expressed as an affine combination
of the vertices with weights between 0 and 1 inclusive. This is equivalent to the convex hull of
the vertices or the closure of the interior. -/
/-
**Affine.Simplex.closedInterior** 是 Mathlib 中的一个定义，位于命名空间 `Affine.Simplex`。
形式化陈述：{k : Type u_1} →   {V : Type u_2} →     {P : Type u_4} →       [inst : Rin
g k] →         [inst_1 : AddCommGroup V] →           [inst_2 : _root_.Module k V
] →             [inst_3 : AddTorsor V P] → [PartialOrder k] → {n : ℕ} → Affine.S
implex k P n → Set P
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`s.closedInterior` is the set of points that can be expressed as an affine combi
nation
of the vertices with weights between 0 and 1 inclusive. This is equivalent to th
e convex hull of
the vertices or the closure of the interior.
-/
protected def closedInterior {n : ℕ} (s : Simplex k P n) : Set P :=
  s.setInterior (Set.Icc 0 1)
/-
**Affine.Simplex.closedInterior_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simple
x`。
形式化陈述：∀ {k : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Ring k] [inst_1 : A
ddCommGroup V] [inst_2 : _root_.Module k V]   [inst_3 : AddTorsor V P] [inst_4 :
 PartialOrder k] {m n : ℕ} (s : Affine.Simplex k P n)   (e : Fin (n + 1) ≃ Fin (
m + 1)), (s.reindex e).closedInterior = s.closedInterior
参数：s : Affine.Simplex k P n；e : Fin (n + 1) ≃ Fin (m + 1)；s.reindex e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.setInterior_reindex`：∀ {k : Type u_1} {V : Type u_2} {P :
 Type u_4} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V
]   [inst_3 : AddTorsor …
-/
@[simp] lemma closedInterior_reindex {m n : ℕ} (s : Simplex k P n) (e : Fin (n + 1) ≃ Fin (m + 1)) :
    (s.reindex e).closedInterior = s.closedInterior :=
  s.setInterior_reindex _ _
/-
**Affine.Simplex.affineCombination_mem_closedInterior_iff** 是 Mathlib 中的一个引理，位于命
名空间 `Affine.Simplex`。
形式化陈述：affineCombination_mem_closedInterior_iff {n : Nat} {s : Simplex k P n} {w 
: Fin (n + 1) -> k} (hw : ∑ i, w i = 1) : Finset.univ.affineCombination k s.poin
ts w in s.closedInterior ↔ forall i, w i in Set.Icc 0 1
参数：n + 1；hw : ∑ i, w i = 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Affine.Simplex.affineCombination_mem_setInterior_iff`：affineCombination_
mem_setInterior_iff {I : Set k} {n : Nat} {s : Simplex k P n} {w : Fin (n + 1) -
> k} (hw : ∑ i, w i = 1) : Finset.univ.aff…
-/
lemma affineCombination_mem_closedInterior_iff {n : ℕ} {s : Simplex k P n} {w : Fin (n + 1) → k}
    (hw : ∑ i, w i = 1) :
    Finset.univ.affineCombination k s.points w ∈ s.closedInterior ↔ ∀ i, w i ∈ Set.Icc 0 1 :=
  affineCombination_mem_setInterior_iff hw
/-
**Affine.Simplex.interior_subset_closedInterior** 是 Mathlib 中的一个引理，位于命名空间 `Affin
e.Simplex`。
形式化陈述：interior_subset_closedInterior {n : Nat} (s : Simplex k P n) : s.interior 
subseteq s.closedInterior
参数：s : Simplex k P n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma interior_subset_closedInterior {n : ℕ} (s : Simplex k P n) :
    s.interior ⊆ s.closedInterior :=
  fun _ ⟨w, hw, hw01, hww⟩ ↦ ⟨w, hw, fun i ↦ ⟨(hw01 i).1.le, (hw01 i).2.le⟩, hww⟩
/-
**Affine.Simplex.point_notMem_interior** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simplex
`。
形式化陈述：point_notMem_interior {n : Nat} (s : Simplex k P n) (i : Fin (n + 1)) : s.
points i ∉ s.interior
参数：s : Simplex k P n；i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.affineCombination_piSingle`：affineCombination_piSingle [Decidable
Eq ι] (p : ι -> P) {i : ι} (hi : i in s) : s.affineCombination k p (Pi.single i 
1) = p i
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用引理 `Affine.Simplex.affineCombination_mem_interior_iff`：affineCombination_mem
_interior_iff {n : Nat} {s : Simplex k P n} {w : Fin (n + 1) -> k} (hw : ∑ i, w 
i = 1) : Finset.univ.affineCombination …
· 使用定理 `Fintype.sum_pi_single'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommM
onoid M] [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (i : ι) (a : M),   ∑ j, P
i.single i a…
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma point_notMem_interior {n : ℕ} (s : Simplex k P n) (i : Fin (n + 1)) :
    s.points i ∉ s.interior := by
  rw [← Finset.univ.affineCombination_piSingle k s.points (Finset.mem_univ i),
    affineCombination_mem_interior_iff (Fintype.sum_pi_single' _ _), not_forall]
  exact ⟨i, by simp⟩
/-
**Affine.Simplex.point_mem_closedInterior** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simp
lex`。
形式化陈述：point_mem_closedInterior [ZeroLEOneClass k] {n : Nat} (s : Simplex k P n) 
(i : Fin (n + 1)) : s.points i in s.closedInterior
参数：s : Simplex k P n；i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.affineCombination_piSingle`：affineCombination_piSingle [Decidable
Eq ι] (p : ι -> P) {i : ι} (hi : i in s) : s.affineCombination k p (Pi.single i 
1) = p i
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用引理 `Affine.Simplex.affineCombination_mem_closedInterior_iff`：affineCombinati
on_mem_closedInterior_iff {n : Nat} {s : Simplex k P n} {w : Fin (n + 1) -> k} (
hw : ∑ i, w i = 1) : Finset.univ.affineCombin…
· 使用定理 `Fintype.sum_pi_single'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommM
onoid M] [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (i : ι) (a : M),   ∑ j, P
i.single i a…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma point_mem_closedInterior [ZeroLEOneClass k] {n : ℕ} (s : Simplex k P n) (i : Fin (n + 1)) :
    s.points i ∈ s.closedInterior := by
  rw [← Finset.univ.affineCombination_piSingle k s.points (Finset.mem_univ i),
    affineCombination_mem_closedInterior_iff (Fintype.sum_pi_single' _ _)]
  intro j
  obtain rfl | hj := eq_or_ne j i <;> simp_all
/-
**Affine.Simplex.nonempty_closedInterior** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simpl
ex`。
形式化陈述：nonempty_closedInterior [ZeroLEOneClass k] {n : Nat} (s : Simplex k P n) :
 s.closedInterior.Nonempty
参数：s : Simplex k P n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Affine.Simplex.point_mem_closedInterior`：point_mem_closedInterior [ZeroL
EOneClass k] {n : Nat} (s : Simplex k P n) (i : Fin (n + 1)) : s.points i in s.c
losedInterior
-/
lemma nonempty_closedInterior [ZeroLEOneClass k] {n : ℕ} (s : Simplex k P n) :
    s.closedInterior.Nonempty :=
  ⟨s.points 0, s.point_mem_closedInterior 0⟩
/-
**Affine.Simplex.interior_ssubset_closedInterior** 是 Mathlib 中的一个引理，位于命名空间 `Affi
ne.Simplex`。
形式化陈述：interior_ssubset_closedInterior [ZeroLEOneClass k] {n : Nat} (s : Simplex 
k P n) : s.interior ⊂ s.closedInterior
参数：s : Simplex k P n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ssubset_iff_exists`：ssubset_iff_exists {s t : Set α} : s ⊂ t ↔ s sub
seteq t ∧ exists x in t, x ∉ s
· 使用引理 `Affine.Simplex.interior_subset_closedInterior`：interior_subset_closedInt
erior {n : Nat} (s : Simplex k P n) : s.interior subseteq s.closedInterior
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Affine.Simplex.point_mem_closedInterior`：point_mem_closedInterior [ZeroL
EOneClass k] {n : Nat} (s : Simplex k P n) (i : Fin (n + 1)) : s.points i in s.c
losedInterior
· 使用引理 `Affine.Simplex.point_notMem_interior`：point_notMem_interior {n : Nat} (s
 : Simplex k P n) (i : Fin (n + 1)) : s.points i ∉ s.interior
-/
lemma interior_ssubset_closedInterior [ZeroLEOneClass k] {n : ℕ} (s : Simplex k P n) :
    s.interior ⊂ s.closedInterior := by
  rw [Set.ssubset_iff_exists]
  exact ⟨s.interior_subset_closedInterior, s.points 0, s.point_mem_closedInterior 0,
    s.point_notMem_interior 0⟩
/-
**Affine.Simplex.closedInterior_subset_affineSpan** 是 Mathlib 中的一个引理，位于命名空间 `Aff
ine.Simplex`。
形式化陈述：closedInterior_subset_affineSpan {n : Nat} {s : Simplex k P n} : s.closedI
nterior subseteq affineSpan k (Set.range s.points)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `affineCombination_mem_affineSpan_of_nonempty`：affineCombination_mem_affi
neSpan_of_nonempty [Nonempty ι] {s : Finset ι} {w : ι -> k} (h : ∑ i in s, w i =
 1) (p : ι -> P) : s.affineCombina…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma closedInterior_subset_affineSpan {n : ℕ} {s : Simplex k P n} :
    s.closedInterior ⊆ affineSpan k (Set.range s.points) := by
  rintro p ⟨w, hw, hi, rfl⟩
  exact affineCombination_mem_affineSpan_of_nonempty hw _
/-
**Affine.Simplex.interior_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：∀ {k : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Ring k] [inst_1 : A
ddCommGroup V] [inst_2 : _root_.Module k V]   [inst_3 : AddTorsor V P] [inst_4 :
 PartialOrder k] (s : Affine.Simplex k P 0), s.interior = ∅
参数：s : Affine.Simplex k P 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
@[simp] lemma interior_eq_empty (s : Simplex k P 0) : s.interior = ∅ := by
  ext p
  simp only [Simplex.interior, Simplex.setInterior, Nat.reduceAdd, univ_unique, Fin.default_eq_zero,
    Fin.isValue, sum_singleton, Set.mem_Ioo, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
    not_exists, not_and]
  intro w h hi
  simpa [h] using hi 0
/-
**Affine.Simplex.closedInterior_eq_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Affine.S
implex`。
形式化陈述：∀ {k : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Ring k] [inst_1 : A
ddCommGroup V] [inst_2 : _root_.Module k V]   [inst_3 : AddTorsor V P] [inst_4 :
 PartialOrder k] [ZeroLEOneClass k] (s : Affine.Simplex k P 0),   s.closedInteri
or = {s.points 0}
参数：s : Affine.Simplex k P 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `Finset.weightedVSubOfPoint_apply`：weightedVSubOfPoint_apply (w : ι -> k)
 (p : ι -> P) (b : P) : s.weightedVSubOfPoint p b w = ∑ i in s, w i • (p i -ᵥ b)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma closedInterior_eq_singleton [ZeroLEOneClass k] (s : Simplex k P 0) :
    s.closedInterior = {s.points 0} := by
  ext p
  simp only [Simplex.closedInterior, Simplex.setInterior, Nat.reduceAdd, univ_unique,
    Fin.default_eq_zero, Fin.isValue, sum_singleton, Set.mem_Icc, Set.mem_ofPred_eq,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨w, h0, hi, rfl⟩
    simp [affineCombination_apply, h0]
  · rintro rfl
    exact ⟨1, by simp [affineCombination_apply]⟩

omit [PartialOrder k] in
/-
**Affine.Simplex.affineCombination_mem_setInterior_face_iff_mem** 是 Mathlib 中的一个
引理，位于命名空间 `Affine.Simplex`。
形式化陈述：affineCombination_mem_setInterior_face_iff_mem (I : Set k) {n : Nat} (s : 
Simplex k P n) {fs : Finset (Fin (n + 1))} {m : Nat} (h : #fs = m + 1) {w : Fin 
(n + 1) -> k} (hw : ∑ i, w i = 1) : Finset.univ.affineCombination k s.points w i
n (s.face h).setInterior I ↔ (forall i in fs, w i in I) ∧ (forall i ∉ fs, w i = 
0)
参数：I : Set k；s : Simplex k P n；Fin (n + 1)；h : #fs = m + 1；n + 1；hw : ∑ i, w i =
 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_affineCombination_of_mem_affineSpan_of_fintype`：eq_affineCombination_
of_mem_affineSpan_of_fintype [Fintype ι] {p1 : P} {p : ι -> P} (h : p1 in affine
Span k (Set.range p)) : exists w : ι ->…
· 使用定理 `Set.mem_of_mem_of_subset`：mem_of_mem_of_subset {x : α} {s t : Set α} (hx
 : x in s) (h : s subseteq t) : x in t
· 使用引理 `Affine.Simplex.setInterior_subset_affineSpan`：setInterior_subset_affineS
pan {I : Set k} {n : Nat} {s : Simplex k P n} : s.setInterior I subseteq affineS
pan k (Set.range s.points)
· 使用引理 `AffineIndependent.indicator_extend_eq_of_affineCombination_comp_embeddin
g_eq_of_fintype`：AffineIndependent.indicator_extend_eq_of_affineCombination_comp
_embedding_eq_of_fintype [Fintype ι] {ι₂ : Type*} [Fintype ι₂] {p : ι -> P} (…
· 使用定理 `Affine.Simplex.independent`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [ins
t_3 : AddTorsor …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.range_orderEmbOfFin`：range_orderEmbOfFin (s : Finset α) {k : Nat}
 (h : s.card = k) : Set.range (s.orderEmbOfFin h) = s
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `Function.Injective.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ) (e' : β → γ) (a : α)
, Function.extend f g…
· 使用定理 `RelEmbedding.injective`：injective (f : r ↪r s) : Injective f
· 使用引理 `Affine.Simplex.affineCombination_mem_setInterior_iff`：affineCombination_
mem_setInterior_iff {I : Set k} {n : Nat} {s : Simplex k P n} {w : Fin (n + 1) -
> k} (hw : ∑ i, w i = 1) : Finset.univ.aff…
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fintype.sum_of_injective`：∀ {M : Type u_4} {κ : Type u_6} {ι : Type u_7}
 [inst : Fintype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι → κ
),   Function.…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Finset.map_orderEmbOfFin_univ`：map_orderEmbOfFin_univ (s : Finset α) {k 
: Nat} (h : s.card = k) : Finset.map (s.orderEmbOfFin h).toEmbedding Finset.univ
 = s
· 使用定理 `Finset.affineCombination_indicator_subset`：affineCombination_indicator_s
ubset (w : ι -> k) (p : ι -> P) {s₁ s₂ : Finset ι} (h : s₁ subseteq s₂) : s₁.aff
ineCombination k p w = s₂.affin…
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
（共 31 条，此处仅展示前 30 条）
-/
lemma affineCombination_mem_setInterior_face_iff_mem (I : Set k) {n : ℕ} (s : Simplex k P n)
    {fs : Finset (Fin (n + 1))} {m : ℕ} (h : #fs = m + 1) {w : Fin (n + 1) → k}
    (hw : ∑ i, w i = 1) : Finset.univ.affineCombination k s.points w ∈ (s.face h).setInterior I ↔
      (∀ i ∈ fs, w i ∈ I) ∧ (∀ i ∉ fs, w i = 0) := by
  refine ⟨fun hi ↦ ?_, fun ⟨hii, hi0⟩ ↦ ?_⟩
  · obtain ⟨w', hw', he⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype
      (Set.mem_of_mem_of_subset hi setInterior_subset_affineSpan)
    rw [he, affineCombination_mem_setInterior_iff hw'] at hi
    have he' := s.independent.indicator_extend_eq_of_affineCombination_comp_embedding_eq_of_fintype
      hw hw' (fs.orderEmbOfFin h).toEmbedding he.symm
    simp_rw [he'.symm]
    refine ⟨fun i hi ↦ ?_, fun i hi ↦ by simp [hi]⟩
    simp only [RelEmbedding.coe_toEmbedding, range_orderEmbOfFin, mem_coe, hi, Set.indicator_of_mem]
    rw [← mem_coe, ← fs.range_orderEmbOfFin h] at hi
    obtain ⟨j, rfl⟩ := hi
    simp [(fs.orderEmbOfFin h).injective.extend_apply, hi]
  · let w' : Fin (m + 1) → k := w ∘ fs.orderEmbOfFin h
    have hw' : ∑ i, w' i = 1 := by
      rw [Fintype.sum_of_injective _ (fs.orderEmbOfFin h).injective w' w
        (fun i hi ↦ hi0 _ (by simpa using hi)) (fun _ ↦ rfl), hw]
    have hw'01 (i) : w' i ∈ I := hii (fs.orderEmbOfFin h i) (by simp)
    rw [← (s.face h).affineCombination_mem_setInterior_iff hw'] at hw'01
    convert! hw'01
    convert! Finset.univ.affineCombination_map (fs.orderEmbOfFin h).toEmbedding w s.points using 1
    simp only [map_orderEmbOfFin_univ, Finset.affineCombination_indicator_subset _ _ fs.subset_univ]
    congr
    grind [Set.indicator_eq_self, mem_support]
/-
**Affine.Simplex.affineCombination_mem_interior_face_iff_mem_Ioo** 是 Mathlib 中的一
个引理，位于命名空间 `Affine.Simplex`。
形式化陈述：affineCombination_mem_interior_face_iff_mem_Ioo {n : Nat} (s : Simplex k P
 n) {fs : Finset (Fin (n + 1))} {m : Nat} (h : #fs = m + 1) {w : Fin (n + 1) -> 
k} (hw : ∑ i, w i = 1) : Finset.univ.affineCombination k s.points w in (s.face h
).interior ↔ (forall i in fs, w i in Set.Ioo 0 1) ∧ (forall i ∉ fs, w i = 0)
参数：s : Simplex k P n；Fin (n + 1)；h : #fs = m + 1；n + 1；hw : ∑ i, w i = 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Affine.Simplex.affineCombination_mem_setInterior_face_iff_mem`：affineCom
bination_mem_setInterior_face_iff_mem (I : Set k) {n : Nat} (s : Simplex k P n) 
{fs : Finset (Fin (n + 1))} {m : Nat} (h : #fs = m …
-/
lemma affineCombination_mem_interior_face_iff_mem_Ioo {n : ℕ} (s : Simplex k P n)
    {fs : Finset (Fin (n + 1))} {m : ℕ} (h : #fs = m + 1) {w : Fin (n + 1) → k}
    (hw : ∑ i, w i = 1) : Finset.univ.affineCombination k s.points w ∈ (s.face h).interior ↔
      (∀ i ∈ fs, w i ∈ Set.Ioo 0 1) ∧ (∀ i ∉ fs, w i = 0) :=
  affineCombination_mem_setInterior_face_iff_mem _ _ _ hw
/-
**Affine.Simplex.affineCombination_mem_closedInterior_face_iff_mem_Icc** 是 Mathl
ib 中的一个引理，位于命名空间 `Affine.Simplex`。
形式化陈述：affineCombination_mem_closedInterior_face_iff_mem_Icc {n : Nat} (s : Simpl
ex k P n) {fs : Finset (Fin (n + 1))} {m : Nat} (h : #fs = m + 1) {w : Fin (n + 
1) -> k} (hw : ∑ i, w i = 1) : Finset.univ.affineCombination k s.points w in (s.
face h).closedInterior ↔ (forall i in fs, w i in Set.Icc 0 1) ∧ (forall i ∉ fs, 
w i = 0)
参数：s : Simplex k P n；Fin (n + 1)；h : #fs = m + 1；n + 1；hw : ∑ i, w i = 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Affine.Simplex.affineCombination_mem_setInterior_face_iff_mem`：affineCom
bination_mem_setInterior_face_iff_mem (I : Set k) {n : Nat} (s : Simplex k P n) 
{fs : Finset (Fin (n + 1))} {m : Nat} (h : #fs = m …
-/
lemma affineCombination_mem_closedInterior_face_iff_mem_Icc {n : ℕ} (s : Simplex k P n)
    {fs : Finset (Fin (n + 1))} {m : ℕ} (h : #fs = m + 1) {w : Fin (n + 1) → k}
    (hw : ∑ i, w i = 1) : Finset.univ.affineCombination k s.points w ∈ (s.face h).closedInterior ↔
      (∀ i ∈ fs, w i ∈ Set.Icc 0 1) ∧ (∀ i ∉ fs, w i = 0) :=
  affineCombination_mem_setInterior_face_iff_mem _ _ _ hw
/-
**Affine.Simplex.affineCombination_mem_interior_face_iff_pos** 是 Mathlib 中的一个引理，
位于命名空间 `Affine.Simplex`。
形式化陈述：affineCombination_mem_interior_face_iff_pos [IsOrderedAddMonoid k] {n : Na
t} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : Nat} [NeZero m] (h : #fs
 = m + 1) {w : Fin (n + 1) -> k} (hw : ∑ i, w i = 1) : Finset.univ.affineCombina
tion k s.points w in (s.face h).interior ↔ (forall i in fs, 0 < w i) ∧ (forall i
 ∉ fs, w i = 0)
参数：s : Simplex k P n；Fin (n + 1)；h : #fs = m + 1；n + 1；hw : ∑ i, w i = 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Affine.Simplex.affineCombination_mem_interior_face_iff_mem_Ioo`：affineCo
mbination_mem_interior_face_iff_mem_Ioo {n : Nat} (s : Simplex k P n) {fs : Fins
et (Fin (n + 1))} {m : Nat} (h : #fs = m + 1) {w : F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_subset`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [i
nst : AddCommMonoid M] {f : ι → M},   s₁ ⊆ s₂ → (∀ x ∈ s₂, x ∉ s₁ → f x = 0) → ∑
 x ∈ s₁…
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
· 使用引理 `Finset.exists_mem_ne`：exists_mem_ne (hs : 1 < #s) (a : α) : exists b in 
s, b != a
· 使用定理 `Finset.single_lt_sum`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] [inst_1 : Preorder M] [IsOrderedCancelAddMonoid M] {f : ι → M}   {s : Fin
set ι} [Ad…
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma affineCombination_mem_interior_face_iff_pos [IsOrderedAddMonoid k] {n : ℕ}
    (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : ℕ} [NeZero m] (h : #fs = m + 1)
    {w : Fin (n + 1) → k} (hw : ∑ i, w i = 1) :
    Finset.univ.affineCombination k s.points w ∈ (s.face h).interior ↔
      (∀ i ∈ fs, 0 < w i) ∧ (∀ i ∉ fs, w i = 0) := by
  rw [s.affineCombination_mem_interior_face_iff_mem_Ioo h hw]
  refine ⟨by grind, fun ⟨hii, hi0⟩ ↦ ⟨fun i hi ↦ ⟨hii i hi, ?_⟩, hi0⟩⟩
  rw [← hw, ← Finset.sum_subset (Finset.subset_univ fs) fun j _ ↦ hi0 j]
  obtain ⟨j, hj, hji⟩ := fs.exists_mem_ne (by grind [→ NeZero.ne]) i
  exact Finset.single_lt_sum hji hi hj (hii j hj) fun t ht _ ↦ (hii t ht).le
/-
**Affine.Simplex.affineCombination_mem_closedInterior_face_iff_nonneg** 是 Mathli
b 中的一个引理，位于命名空间 `Affine.Simplex`。
形式化陈述：affineCombination_mem_closedInterior_face_iff_nonneg [IsOrderedAddMonoid k
] {n : Nat} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : Nat} (h : #fs =
 m + 1) {w : Fin (n + 1) -> k} (hw : ∑ i, w i = 1) : Finset.univ.affineCombinati
on k s.points w in (s.face h).closedInterior ↔ (forall i in fs, 0 <= w i) ∧ (for
all i ∉ fs, w i = 0)
参数：s : Simplex k P n；Fin (n + 1)；h : #fs = m + 1；n + 1；hw : ∑ i, w i = 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Affine.Simplex.affineCombination_mem_closedInterior_face_iff_mem_Icc`：af
fineCombination_mem_closedInterior_face_iff_mem_Icc {n : Nat} (s : Simplex k P n
) {fs : Finset (Fin (n + 1))} {m : Nat} (h : #fs = m + 1) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_subset`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [i
nst : AddCommMonoid M] {f : ι → M},   s₁ ⊆ s₂ → (∀ x ∈ s₂, x ∉ s₁ → f x = 0) → ∑
 x ∈ s₁…
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
· 使用定理 `Finset.single_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMon
oid N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i 
∈ s, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
lemma affineCombination_mem_closedInterior_face_iff_nonneg [IsOrderedAddMonoid k] {n : ℕ}
    (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : ℕ} (h : #fs = m + 1)
    {w : Fin (n + 1) → k} (hw : ∑ i, w i = 1) :
    Finset.univ.affineCombination k s.points w ∈ (s.face h).closedInterior ↔
      (∀ i ∈ fs, 0 ≤ w i) ∧ (∀ i ∉ fs, w i = 0) := by
  rw [s.affineCombination_mem_closedInterior_face_iff_mem_Icc h hw]
  refine ⟨by grind, fun ⟨hii, hi0⟩ ↦ ⟨fun i hi ↦ ⟨hii i hi, ?_⟩, hi0⟩⟩
  rw [← hw, ← Finset.sum_subset (Finset.subset_univ fs) fun j _ ↦ hi0 j]
  exact Finset.single_le_sum (fun t ht ↦ (hii t ht)) hi
/-
**Affine.Simplex.interior_map** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simplex`。
形式化陈述：interior_map {n : Nat} (s : Simplex k P n) {f : P ->ᵃ[k] P₂} (hf : Functio
n.Injective f) : (s.map f hf).interior = f '' s.interior
参数：s : Simplex k P n；hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Affine.Simplex.setInterior_map`：setInterior_map (I : Set k) {n : Nat} (s
 : Simplex k P n) {f : P ->ᵃ[k] P₂} (hf : Function.Injective f) : (s.map f hf).s
etInterior I = f '' …
-/
lemma interior_map {n : ℕ} (s : Simplex k P n) {f : P →ᵃ[k] P₂} (hf : Function.Injective f) :
    (s.map f hf).interior = f '' s.interior :=
  s.setInterior_map _ hf
/-
**Affine.Simplex.closedInterior_map** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simplex`。
形式化陈述：closedInterior_map {n : Nat} (s : Simplex k P n) {f : P ->ᵃ[k] P₂} (hf : F
unction.Injective f) : (s.map f hf).closedInterior = f '' s.closedInterior
参数：s : Simplex k P n；hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Affine.Simplex.setInterior_map`：setInterior_map (I : Set k) {n : Nat} (s
 : Simplex k P n) {f : P ->ᵃ[k] P₂} (hf : Function.Injective f) : (s.map f hf).s
etInterior I = f '' …
-/
lemma closedInterior_map {n : ℕ} (s : Simplex k P n) {f : P →ᵃ[k] P₂} (hf : Function.Injective f) :
    (s.map f hf).closedInterior = f '' s.closedInterior :=
  s.setInterior_map _ hf
/-
**Affine.Simplex.interior_restrict** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simplex`。
形式化陈述：interior_restrict {n : Nat} (s : Simplex k P n) {S : AffineSubspace k P} (
hS : affineSpan k (Set.range s.points) <= S) : letI
参数：s : Simplex k P n；hS : affineSpan k (Set.range s.points) <= S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Affine.Simplex.setInterior_restrict`：setInterior_restrict (I : Set k) {n
 : Nat} (s : Simplex k P n) {S : AffineSubspace k P} (hS : affineSpan k (Set.ran
ge s.points) <= S) : letI
-/
lemma interior_restrict {n : ℕ} (s : Simplex k P n) {S : AffineSubspace k P}
    (hS : affineSpan k (Set.range s.points) ≤ S) :
    letI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).interior = S.subtype ⁻¹' s.interior :=
  s.setInterior_restrict _ hS
/-
**Affine.Simplex.closedInterior_restrict** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simpl
ex`。
形式化陈述：closedInterior_restrict {n : Nat} (s : Simplex k P n) {S : AffineSubspace 
k P} (hS : affineSpan k (Set.range s.points) <= S) : letI
参数：s : Simplex k P n；hS : affineSpan k (Set.range s.points) <= S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Affine.Simplex.setInterior_restrict`：setInterior_restrict (I : Set k) {n
 : Nat} (s : Simplex k P n) {S : AffineSubspace k P} (hS : affineSpan k (Set.ran
ge s.points) <= S) : letI
-/
lemma closedInterior_restrict {n : ℕ} (s : Simplex k P n) {S : AffineSubspace k P}
    (hS : affineSpan k (Set.range s.points) ≤ S) :
    letI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).closedInterior = S.subtype ⁻¹' s.closedInterior :=
  s.setInterior_restrict _ hS
/-
**Affine.Simplex.closedInterior_face_subset_closedInterior** 是 Mathlib 中的一个定理，位于
命名空间 `Affine.Simplex`。
形式化陈述：closedInterior_face_subset_closedInterior [ZeroLEOneClass k] {n : Nat} (s 
: Simplex k P n) {fs : Finset (Fin (n + 1))} {m : Nat} (h : #fs = m + 1) : (s.fa
ce h).closedInterior subseteq s.closedInterior
参数：s : Simplex k P n；Fin (n + 1)；h : #fs = m + 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_of_mem_of_subset`：mem_of_mem_of_subset {x : α} {s t : Set α} (hx
 : x in s) (h : s subseteq t) : x in t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Affine.Simplex.closedInterior_subset_affineSpan`：closedInterior_subset_a
ffineSpan {n : Nat} {s : Simplex k P n} : s.closedInterior subseteq affineSpan k
 (Set.range s.points)
· 使用定理 `affineSpan_mono`：affineSpan_mono {s₁ s₂ : Set P} (h : s₁ subseteq s₂) : 
affineSpan k s₁ <= affineSpan k s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.range_face_points`：range_face_points {n : Nat} (s : Simpl
ex k P n) {fs : Finset (Fin (n + 1))} {m : Nat} (h : #fs = m + 1) : Set.range (s
.face h).points = s.po…
· 使用定理 `Set.preimage_range`：preimage_range (f : α -> β) : f ⁻¹' range f = univ
· 使用定理 `eq_affineCombination_of_mem_affineSpan_of_fintype`：eq_affineCombination_
of_mem_affineSpan_of_fintype [Fintype ι] {p1 : P} {p : ι -> P} (h : p1 in affine
Span k (Set.range p)) : exists w : ι ->…
· 使用引理 `Affine.Simplex.affineCombination_mem_closedInterior_iff`：affineCombinati
on_mem_closedInterior_iff {n : Nat} {s : Simplex k P n} {w : Fin (n + 1) -> k} (
hw : ∑ i, w i = 1) : Finset.univ.affineCombin…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用引理 `Affine.Simplex.affineCombination_mem_closedInterior_face_iff_mem_Icc`：af
fineCombination_mem_closedInterior_face_iff_mem_Icc {n : Nat} (s : Simplex k P n
) {fs : Finset (Fin (n + 1))} {m : Nat} (h : #fs = m + 1) …
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem closedInterior_face_subset_closedInterior [ZeroLEOneClass k] {n : ℕ} (s : Simplex k P n)
    {fs : Finset (Fin (n + 1))} {m : ℕ} (h : #fs = m + 1) :
    (s.face h).closedInterior ⊆ s.closedInterior := by
  intro p hp
  have hp' : p ∈ affineSpan k (Set.range s.points) :=
    Set.mem_of_mem_of_subset hp <|
      (s.face h).closedInterior_subset_affineSpan.trans <|
        affineSpan_mono k <| by simp
  obtain ⟨w, hw1, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hp'
  rw [affineCombination_mem_closedInterior_face_iff_mem_Icc _ _ hw1] at hp
  rw [affineCombination_mem_closedInterior_iff hw1]
  intro i
  by_cases hi : i ∈ fs <;> aesop

@[simp]
/-
**Affine.Simplex.point_mem_closedInterior_face_iff** 是 Mathlib 中的一个定理，位于命名空间 `Af
fine.Simplex`。
形式化陈述：point_mem_closedInterior_face_iff [Nontrivial k] [ZeroLEOneClass k] {n : N
at} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : Nat} (h : #fs = m + 1) 
{j : Fin (n + 1)} : s.points j in (s.face h).closedInterior ↔ j in fs
参数：s : Simplex k P n；Fin (n + 1)；h : #fs = m + 1；n + 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_of_mem_of_subset`：mem_of_mem_of_subset {x : α} {s t : Set α} (hx
 : x in s) (h : s subseteq t) : x in t
· 使用定理 `affineCombination_mem_affineSpan`：affineCombination_mem_affineSpan [Nont
rivial k] {s : Finset ι} {w : ι -> k} (h : ∑ i in s, w i = 1) (p : ι -> P) : s.a
ffineCombination k p w…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Affine.Simplex.range_face_points`：range_face_points {n : Nat} (s : Simpl
ex k P n) {fs : Finset (Fin (n + 1))} {m : Nat} (h : #fs = m + 1) : Set.range (s
.face h).points = s.po…
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Finset.range_orderEmbOfFin`：range_orderEmbOfFin (s : Finset α) {k : Nat}
 (h : s.card = k) : Set.range (s.orderEmbOfFin h) = s
· 使用引理 `Affine.Simplex.point_mem_closedInterior`：point_mem_closedInterior [ZeroL
EOneClass k] {n : Nat} (s : Simplex k P n) (i : Fin (n + 1)) : s.points i in s.c
losedInterior
-/
theorem point_mem_closedInterior_face_iff [Nontrivial k] [ZeroLEOneClass k] {n : ℕ}
    (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : ℕ} (h : #fs = m + 1) {j : Fin (n + 1)} :
    s.points j ∈ (s.face h).closedInterior ↔ j ∈ fs := by
  refine ⟨fun hj ↦ ?_, fun hfs ↦ ?_⟩
  · suffices s.points j ∈ affineSpan k (s.points '' fs) by simpa
    obtain ⟨w, hw, hw', hs⟩ := hj
    rw [← hs]
    exact Set.mem_of_mem_of_subset (affineCombination_mem_affineSpan hw _) (by simp)
  · obtain ⟨i, rfl⟩ : ∃ i, fs.orderEmbOfFin h i = j := range_orderEmbOfFin fs h |>.ge hfs
    exact point_mem_closedInterior _ _
/-
**Affine.Simplex.closedInterior_face_ssubset_closedInterior** 是 Mathlib 中的一个定理，位
于命名空间 `Affine.Simplex`。
形式化陈述：closedInterior_face_ssubset_closedInterior [Nontrivial k] [ZeroLEOneClass 
k] {n : Nat} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} (hfs : fs != .univ)
 {m : Nat} (h : #fs = m + 1) : (s.face h).closedInterior ⊂ s.closedInterior
参数：s : Simplex k P n；Fin (n + 1)；hfs : fs != .univ；h : #fs = m + 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Finset.eq_univ_iff_forall`：eq_univ_iff_forall : s = univ ↔ forall x, x i
n s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.ssubset_iff_of_subset`：ssubset_iff_of_subset {s t : Set α} (h : s su
bseteq t) : s ⊂ t ↔ exists x in t, x ∉ s
· 使用定理 `Affine.Simplex.closedInterior_face_subset_closedInterior`：closedInterior
_face_subset_closedInterior [ZeroLEOneClass k] {n : Nat} (s : Simplex k P n) {fs
 : Finset (Fin (n + 1))} {m : Nat} (h : #fs = …
· 使用引理 `Affine.Simplex.point_mem_closedInterior`：point_mem_closedInterior [ZeroL
EOneClass k] {n : Nat} (s : Simplex k P n) (i : Fin (n + 1)) : s.points i in s.c
losedInterior
-/
theorem closedInterior_face_ssubset_closedInterior [Nontrivial k] [ZeroLEOneClass k] {n : ℕ}
    (s : Simplex k P n) {fs : Finset (Fin (n + 1))} (hfs : fs ≠ .univ) {m : ℕ} (h : #fs = m + 1) :
    (s.face h).closedInterior ⊂ s.closedInterior := by
  obtain ⟨a, ha⟩ := Classical.not_forall.mp <| Finset.eq_univ_iff_forall.not.mp hfs
  apply (Set.ssubset_iff_of_subset (s.closedInterior_face_subset_closedInterior h)).mpr
  exact ⟨s.points a, s.point_mem_closedInterior a, fun hs ↦ ha (by simpa using hs)⟩
/-
**Affine.Simplex.disjoint_interior_closedInterior_face** 是 Mathlib 中的一个定理，位于命名空间
 `Affine.Simplex`。
形式化陈述：disjoint_interior_closedInterior_face {n : Nat} (s : Simplex k P n) {fs : 
Finset (Fin (n + 1))} (hfs : fs != .univ) {m : Nat} (h : #fs = m + 1) : Disjoint
 s.interior (s.face h).closedInterior
参数：s : Simplex k P n；Fin (n + 1)；hfs : fs != .univ；h : #fs = m + 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `Set.mem_of_mem_of_subset`：mem_of_mem_of_subset {x : α} {s t : Set α} (hx
 : x in s) (h : s subseteq t) : x in t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Affine.Simplex.interior_subset_closedInterior`：interior_subset_closedInt
erior {n : Nat} (s : Simplex k P n) : s.interior subseteq s.closedInterior
· 使用引理 `Affine.Simplex.closedInterior_subset_affineSpan`：closedInterior_subset_a
ffineSpan {n : Nat} {s : Simplex k P n} : s.closedInterior subseteq affineSpan k
 (Set.range s.points)
-/
theorem disjoint_interior_closedInterior_face {n : ℕ}
    (s : Simplex k P n) {fs : Finset (Fin (n + 1))} (hfs : fs ≠ .univ) {m : ℕ} (h : #fs = m + 1) :
    Disjoint s.interior (s.face h).closedInterior := by
  refine Set.disjoint_left.mpr fun p hleft hright ↦ ?_
  have hp : p ∈ affineSpan k (Set.range s.points) :=
    Set.mem_of_mem_of_subset hleft <| s.interior_subset_closedInterior.trans <|
      s.closedInterior_subset_affineSpan
  grind [affineCombination_mem_interior_iff, affineCombination_mem_closedInterior_face_iff_mem_Icc,
    eq_affineCombination_of_mem_affineSpan_of_fintype]

@[simp]
/-
**Affine.Simplex.point_mem_closedInterior_faceOpposite_iff** 是 Mathlib 中的一个定理，位于
命名空间 `Affine.Simplex`。
形式化陈述：point_mem_closedInterior_faceOpposite_iff [Nontrivial k] [ZeroLEOneClass k
] {n : Nat} [NeZero n] (s : Simplex k P n) {i j : Fin (n + 1)} : s.points j in (
s.faceOpposite i).closedInterior ↔ j != i
参数：s : Simplex k P n；n + 1。
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
theorem point_mem_closedInterior_faceOpposite_iff [Nontrivial k] [ZeroLEOneClass k] {n : ℕ}
    [NeZero n] (s : Simplex k P n) {i j : Fin (n + 1)} :
    s.points j ∈ (s.faceOpposite i).closedInterior ↔ j ≠ i := by
  simp [faceOpposite]
/-
**Affine.Simplex.closedInterior_faceOpposite_subset_closedInterior** 是 Mathlib 中
的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：closedInterior_faceOpposite_subset_closedInterior [ZeroLEOneClass k] {n : 
Nat} [NeZero n] (s : Simplex k P n) (i : Fin (n + 1)) : (s.faceOpposite i).close
dInterior subseteq s.closedInterior
参数：s : Simplex k P n；i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.closedInterior_face_subset_closedInterior`：closedInterior
_face_subset_closedInterior [ZeroLEOneClass k] {n : Nat} (s : Simplex k P n) {fs
 : Finset (Fin (n + 1))} {m : Nat} (h : #fs = …
-/
theorem closedInterior_faceOpposite_subset_closedInterior [ZeroLEOneClass k] {n : ℕ} [NeZero n]
    (s : Simplex k P n) (i : Fin (n + 1)) :
    (s.faceOpposite i).closedInterior ⊆ s.closedInterior :=
  s.closedInterior_face_subset_closedInterior _
/-
**Affine.Simplex.closedInterior_faceOpposite_ssubset_closedInterior** 是 Mathlib 
中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：closedInterior_faceOpposite_ssubset_closedInterior [Nontrivial k] [ZeroLEO
neClass k] {n : Nat} [NeZero n] (s : Simplex k P n) (i : Fin (n + 1)) : (s.faceO
pposite i).closedInterior ⊂ s.closedInterior
参数：s : Simplex k P n；i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.closedInterior_face_ssubset_closedInterior`：closedInterio
r_face_ssubset_closedInterior [Nontrivial k] [ZeroLEOneClass k] {n : Nat} (s : S
implex k P n) {fs : Finset (Fin (n + 1))} (hfs …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem closedInterior_faceOpposite_ssubset_closedInterior [Nontrivial k] [ZeroLEOneClass k] {n : ℕ}
    [NeZero n] (s : Simplex k P n) (i : Fin (n + 1)) :
    (s.faceOpposite i).closedInterior ⊂ s.closedInterior :=
  s.closedInterior_face_ssubset_closedInterior (by simp) _
/-
**Affine.Simplex.disjoint_interior_closedInterior_faceOpposite** 是 Mathlib 中的一个定
理，位于命名空间 `Affine.Simplex`。
形式化陈述：disjoint_interior_closedInterior_faceOpposite {n : Nat} [NeZero n] (s : Si
mplex k P n) (i : Fin (n + 1)) : Disjoint s.interior (s.faceOpposite i).closedIn
terior
参数：s : Simplex k P n；i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.disjoint_interior_closedInterior_face`：disjoint_interior_
closedInterior_face {n : Nat} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} (h
fs : fs != .univ) {m : Nat} (h : #fs = m +…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem disjoint_interior_closedInterior_faceOpposite {n : ℕ} [NeZero n]
    (s : Simplex k P n) (i : Fin (n + 1)) :
    Disjoint s.interior (s.faceOpposite i).closedInterior :=
  s.disjoint_interior_closedInterior_face (by simp) _

end PartialOrder

section LinearOrder
variable [LinearOrder k]

/-- The closed interior is the union of the open interior and the surface. -/
/-
**Affine.Simplex.closedInterior_eq_interior_union** 是 Mathlib 中的一个定理，位于命名空间 `Aff
ine.Simplex`。
形式化陈述：closedInterior_eq_interior_union [IsOrderedAddMonoid k] [ZeroLEOneClass k]
 {n : Nat} [NeZero n] (s : Simplex k P n) : s.closedInterior = s.interior union 
⋃ i : Fin (n + 1), (s.faceOpposite i).closedInterior
参数：s : Simplex k P n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `eq_affineCombination_of_mem_affineSpan_of_fintype`：eq_affineCombination_
of_mem_affineSpan_of_fintype [Fintype ι] {p1 : P} {p : ι -> P} (h : p1 in affine
Span k (Set.range p)) : exists w : ι ->…
· 使用定理 `Set.mem_of_mem_of_subset`：mem_of_mem_of_subset {x : α} {s t : Set α} (hx
 : x in s) (h : s subseteq t) : x in t
· 使用引理 `Affine.Simplex.closedInterior_subset_affineSpan`：closedInterior_subset_a
ffineSpan {n : Nat} {s : Simplex k P n} : s.closedInterior subseteq affineSpan k
 (Set.range s.points)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_union`：mem_union (x : α) (a b : Set α) : x in a union b ↔ x in a
 ∨ x in b
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Mathlib.Tactic.Push.not_and_or_eq`：not_and_or_eq : (¬ (p ∧ q)) = (¬ p ∨ 
¬ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `Affine.Simplex.affineCombination_mem_interior_iff`：affineCombination_mem
_interior_iff {n : Nat} {s : Simplex k P n} {w : Fin (n + 1) -> k} (hw : ∑ i, w 
i = 1) : Finset.univ.affineCombination …
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Affine.Simplex.affineCombination_mem_closedInterior_iff`：affineCombinati
on_mem_closedInterior_iff {n : Nat} {s : Simplex k P n} {w : Fin (n + 1) -> k} (
hw : ∑ i, w i = 1) : Finset.univ.affineCombin…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Finset.sum_eq_zero_iff_of_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst 
: AddCommMonoid N] [inst_1 : PartialOrder N] {f : ι → N} {s : Finset ι}   [AddLe
ftMono N], (∀ i ∈ s, 0…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `add_eq_right`：∀ {M : Type u_4} [inst : AddMonoid M] [IsRightCancelAdd M]
 {a b : M}, a + b = b ↔ a = 0
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_erase_add`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] [inst_1 : DecidableEq ι] (s : Finset ι) (f : ι → M) {a : ι},   a ∈ s → ∑ 
x ∈ s.eras…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
The closed interior is the union of the open interior and the surface.
-/
theorem closedInterior_eq_interior_union [IsOrderedAddMonoid k] [ZeroLEOneClass k] {n : ℕ}
    [NeZero n] (s : Simplex k P n) :
    s.closedInterior = s.interior ∪ ⋃ i : Fin (n + 1), (s.faceOpposite i).closedInterior := by
  apply Set.Subset.antisymm
  · intro p hp
    obtain hp' := Set.mem_of_mem_of_subset hp s.closedInterior_subset_affineSpan
    obtain ⟨w, hw1, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hp'
    rw [Set.mem_union, or_iff_not_imp_left]
    intro h
    rw [affineCombination_mem_closedInterior_iff hw1] at hp
    simp_rw [affineCombination_mem_interior_iff hw1, Set.mem_Ioo] at h
    push +distrib Not at h
    obtain ⟨j, hj⟩ : ∃ j : Fin (n + 1), w j = 0 := by
      obtain ⟨i, hi | hi⟩ := h
      · exact ⟨i, le_antisymm hi (hp i).1⟩
      · have hi1 : w i = 1 := le_antisymm (hp i).2 hi
        rw [← hi1, ← Finset.sum_erase_add _ _ (show i ∈ Finset.univ by simp), add_eq_right,
          Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ (hp j).1)] at hw1
        exact ⟨i + 1, hw1 _ (by simp)⟩
    refine Set.mem_iUnion.mpr ⟨j, ?_⟩
    rw [faceOpposite, affineCombination_mem_closedInterior_face_iff_mem_Icc _ _ hw1]
    exact ⟨fun k _ ↦ hp k, by simpa using hj⟩
  · refine Set.union_subset s.interior_subset_closedInterior (Set.iUnion_subset fun i ↦ ?_)
    exact s.closedInterior_faceOpposite_subset_closedInterior i
/-
**Affine.Simplex.closedInterior_sdiff_interior** 是 Mathlib 中的一个定理，位于命名空间 `Affine
.Simplex`。
形式化陈述：closedInterior_sdiff_interior [IsOrderedAddMonoid k] [ZeroLEOneClass k] {n
 : Nat} [NeZero n] (s : Simplex k P n) : s.closedInterior \ s.interior = ⋃ i : F
in (n + 1), (s.faceOpposite i).closedInterior
参数：s : Simplex k P n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.closedInterior_eq_interior_union`：closedInterior_eq_inter
ior_union [IsOrderedAddMonoid k] [ZeroLEOneClass k] {n : Nat} [NeZero n] (s : Si
mplex k P n) : s.closedInterior = s.i…
· 使用定理 `Set.union_sdiff_left`：union_sdiff_left {s t : Set α} : (s union t) \ s =
 t \ s
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Affine.Simplex.disjoint_interior_closedInterior_faceOpposite`：disjoint_i
nterior_closedInterior_faceOpposite {n : Nat} [NeZero n] (s : Simplex k P n) (i 
: Fin (n + 1)) : Disjoint s.interior (s.faceOpposi…
-/
theorem closedInterior_sdiff_interior [IsOrderedAddMonoid k] [ZeroLEOneClass k]
    {n : ℕ} [NeZero n] (s : Simplex k P n) :
    s.closedInterior \ s.interior = ⋃ i : Fin (n + 1), (s.faceOpposite i).closedInterior := by
  simpa [closedInterior_eq_interior_union] using
    fun i ↦ (s.disjoint_interior_closedInterior_faceOpposite i).symm

@[deprecated (since := "2026-06-03")]
alias closedInterior_diff_interior := closedInterior_sdiff_interior

end LinearOrder

end Simplex

end Affine

