/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Analysis.Convex.Side
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.Geometry.Euclidean.SignedDist
public import Mathlib.Geometry.Euclidean.Sphere.Tangent
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Topology.Instances.Sign

/-!
# Incenters and excenters of simplices.

This file defines the insphere and exspheres of a simplex (tangent to the faces of the simplex),
and the center and radius of such spheres.

The terms "exsphere", "excenter" and "exradius" are used in this file in a general sense where
a `Finset` `signs` of indices is given that determine, up to negating all the signs, which
vertices of the simplex lie on the same side of the opposite face as the excenter and which lie
on the opposite side of that face. This includes the cases of the insphere, incenter and
inradius, when `signs` is `∅` (or `univ`); the insphere always exists. It also includes the case
of an exsphere opposite a vertex, when `signs` is a singleton (or its complement), which always
exists in two or more dimensions. In three or more dimensions, there are further possibilities
for `signs`, and the corresponding excenters may or may not exist, depending on the choice of
simplex. For convenience, the most common definitions `exsphere`, `excenter` and `exradius` have
corresponding `insphere`, `incenter` and `inradius` definitions, and various lemmas are duplicated
for the case of the insphere to avoid needing to pass an `ExcenterExists` hypothesis in that case.
However, other definitions such as `excenterWeights`, `touchpoint` and `touchpointWeights` are not
duplicated.

## Main definitions

* `Affine.Simplex.ExcenterExists` says whether an excenter exists with a given set of indices.
* `Affine.Simplex.excenterWeights` are the weights of the excenter with the given set of
  indices, if it exists, as an affine combination of the vertices.
* `Affine.Simplex.exsphere` is the exsphere with the given set of indices, if it exists, with
  shorthands:
  * `Affine.Simplex.excenter` for the center of this sphere
  * `Affine.Simplex.exradius` for the radius of this sphere
* `Affine.Simplex.insphere` is the insphere, with shorthands:
  * `Affine.Simplex.incenter` for the center of this sphere
  * `Affine.Simplex.inradius` for the radius of this sphere
* `Affine.Simplex.touchpoint` for the point where an exsphere of a simplex is tangent to one of
  the faces.
* `Affine.Simplex.touchpointWeights` for the weights of a touchpoint as an affine combination of
  the vertices.

## References

* https://en.wikipedia.org/wiki/Incircle_and_excircles
* https://en.wikipedia.org/wiki/Incenter

-/

@[expose] public section


open EuclideanGeometry
open scoped Finset RealInnerProductSpace

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P]
variable {V₂ P₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [MetricSpace P₂]
variable [NormedAddTorsor V₂ P₂]

noncomputable section

namespace Affine

namespace Simplex

variable {m n : ℕ} [NeZero m] [NeZero n] (s : Simplex ℝ P n)

/-- The unnormalized weights of the vertices in an affine combination that gives an excenter with
signs determined by the given set of indices (for the empty set, this is the incenter; for a
singleton set, this is the excenter opposite a vertex).  An excenter with those signs exists if
and only if the sum of these weights is nonzero (so the normalized weights sum to 1). -/
/-
**Affine.Simplex.excenterWeightsUnnorm** 是 Mathlib 中的一个定义，位于命名空间 `Affine.Simplex
`。
形式化陈述：excenterWeightsUnnorm (signs : Finset (Fin (n + 1))) (i : Fin (n + 1)) : R
eal
参数：signs : Finset (Fin (n + 1))；i : Fin (n + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unnormalized weights of the vertices in an affine combination that gives an 
excenter with
signs determined by the given set of indices (for the empty set, this is the inc
enter; for a
singleton set, this is the excenter opposite a vertex).  An excenter with those 
signs exists if
and only if the sum of these weights is nonzero (so the normalized weights sum t
o 1).
-/
def excenterWeightsUnnorm (signs : Finset (Fin (n + 1))) (i : Fin (n + 1)) : ℝ :=
  (if i ∈ signs then -1 else 1) * (s.height i)⁻¹
/-
**Affine.Simplex.excenterWeightsUnnorm_reindex** 是 Mathlib 中的一个引理，位于命名空间 `Affine
.Simplex`。
形式化陈述：excenterWeightsUnnorm_reindex (e : Fin (n + 1) ≃ Fin (m + 1)) (signs : Fin
set (Fin (m + 1))) : (s.reindex e).excenterWeightsUnnorm signs = s.excenterWeigh
tsUnnorm (signs.map e.symm) ∘ e.symm
参数：e : Fin (n + 1) ≃ Fin (m + 1)；signs : Finset (Fin (m + 1))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Affine.Simplex.height_reindex`：∀ {V : Type u_1} {P : Type u_2} [inst : N
ormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]  
 [inst_3 : NormedAd…
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma excenterWeightsUnnorm_reindex (e : Fin (n + 1) ≃ Fin (m + 1)) (signs : Finset (Fin (m + 1))) :
    (s.reindex e).excenterWeightsUnnorm signs =
      s.excenterWeightsUnnorm (signs.map e.symm) ∘ e.symm := by
  ext i
  simp [excenterWeightsUnnorm]
/-
**Affine.Simplex.excenterWeightsUnnorm_map** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Sim
plex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
V₂ : Type u_3} {P₂ : Type u_4} [inst_4 : NormedAddCommGroup V₂]   [inst_5 : Inne
rProductSpace ℝ V₂] [inst_6 : MetricSpace P₂] [inst_7 : NormedAddTorsor V₂ P₂] {
n : ℕ}   [inst_8 : NeZero n] (s : Affine.Simplex ℝ P n) (f : P →ᵃⁱ[ℝ] P₂),   (s.
map f.toAffineMap ⋯).excenterWeightsUnnorm = s.excenterWeightsUnnorm
参数：s : Affine.Simplex ℝ P n；f : P →ᵃⁱ[ℝ] P₂；s.map f.toAffineMap ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AffineIsometry.injective`：∀ {𝕜 : Type u_1} {V₁' : Type u_4} {V₂ : Type u
_5} {P₁' : Type u_9} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : Seminor
medAddCommGrou…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.height_map`：∀ {V : Type u_1} {P : Type u_2} [inst : Norme
dAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [in
st_3 : NormedAd…
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma excenterWeightsUnnorm_map (f : P →ᵃⁱ[ℝ] P₂) :
    (s.map f.toAffineMap f.injective).excenterWeightsUnnorm = s.excenterWeightsUnnorm := by
  ext
  simp [excenterWeightsUnnorm]
/-
**Affine.Simplex.excenterWeightsUnnorm_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Affin
e.Simplex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] (s : Affine.Simplex ℝ P n) (S : AffineSubspace ℝ P)  
 (hS : affineSpan ℝ (Set.range s.points) ≤ S), (s.restrict S hS).excenterWeights
Unnorm = s.excenterWeightsUnnorm
参数：s : Affine.Simplex ℝ P n；S : AffineSubspace ℝ P；hS : affineSpan ℝ (Set.range 
s.points) ≤ S；s.restrict S hS。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.height_restrict`：∀ {V : Type u_1} {P : Type u_2} [inst : 
NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] 
  [inst_3 : NormedAd…
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma excenterWeightsUnnorm_restrict (S : AffineSubspace ℝ P)
    (hS : affineSpan ℝ (Set.range s.points) ≤ S) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).excenterWeightsUnnorm = s.excenterWeightsUnnorm := by
  ext
  simp [excenterWeightsUnnorm]
/-
**Affine.Simplex.excenterWeightsUnnorm_empty_apply** 是 Mathlib 中的一个定理，位于命名空间 `Af
fine.Simplex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] (s : Affine.Simplex ℝ P n) (i : Fin (n + 1)),   s.exc
enterWeightsUnnorm ∅ i = (s.height i)⁻¹
参数：s : Affine.Simplex ℝ P n；i : Fin (n + 1)；s.height i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
@[simp] lemma excenterWeightsUnnorm_empty_apply (i : Fin (n + 1)) :
    s.excenterWeightsUnnorm ∅ i = (s.height i)⁻¹ :=
  one_mul _
/-
**Affine.Simplex.excenterWeightsUnnorm_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Affine
.Simplex`。
形式化陈述：excenterWeightsUnnorm_ne_zero (signs : Finset (Fin (n + 1))) (i : Fin (n +
 1)) : s.excenterWeightsUnnorm signs i != 0
参数：signs : Finset (Fin (n + 1))；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.excenterWeightsUnnorm.eq_1`：∀ {V : Type u_1} {P : Type u_
2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Metr
icSpace P]   [inst_3 : NormedAd…
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `Affine.Simplex.height_pos`：height_pos {n : Nat} [NeZero n] (s : Simplex 
Real P n) (i : Fin (n + 1)) : 0 < s.height i
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma excenterWeightsUnnorm_ne_zero (signs : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    s.excenterWeightsUnnorm signs i ≠ 0 := by
  rw [excenterWeightsUnnorm]
  refine mul_ne_zero ?_ ?_
  · grind
  · simp [(s.height_pos i).ne']

/-- Whether an excenter exists with a given choice of signs. -/
/-
**Affine.Simplex.ExcenterExists** 是 Mathlib 中的一个定义，位于命名空间 `Affine.Simplex`。
形式化陈述：ExcenterExists (signs : Finset (Fin (n + 1))) : Prop
参数：signs : Finset (Fin (n + 1))。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Whether an excenter exists with a given choice of signs.
-/
def ExcenterExists (signs : Finset (Fin (n + 1))) : Prop :=
  ∑ i, s.excenterWeightsUnnorm signs i ≠ 0
/-
**Affine.Simplex.excenterExists_reindex** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simple
x`。
形式化陈述：excenterExists_reindex {e : Fin (n + 1) ≃ Fin (m + 1)} {signs : Finset (Fi
n (m + 1))} : (s.reindex e).ExcenterExists signs ↔ s.ExcenterExists (signs.map e
.symm)
参数：n + 1；m + 1；Fin (m + 1)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `Affine.Simplex.excenterWeightsUnnorm_reindex`：excenterWeightsUnnorm_rein
dex (e : Fin (n + 1) ≃ Fin (m + 1)) (signs : Finset (Fin (m + 1))) : (s.reindex 
e).excenterWeightsUnnorm signs = s…
· 使用定理 `Finset.sum_comp_equiv`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} {s
 : Finset ι} [inst : AddCommMonoid M] {f : κ → M} (e : ι ≃ κ),   s.sum (f ∘ ⇑e) 
= (Finset.m…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.map_univ_equiv`：map_univ_equiv [Fintype β] (f : β ≃ α) : univ.map
 f.toEmbedding = univ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma excenterExists_reindex {e : Fin (n + 1) ≃ Fin (m + 1)} {signs : Finset (Fin (m + 1))} :
    (s.reindex e).ExcenterExists signs ↔ s.ExcenterExists (signs.map e.symm) := by
  simp_rw [ExcenterExists, excenterWeightsUnnorm_reindex, Finset.sum_comp_equiv,
    Finset.map_univ_equiv]
/-
**Affine.Simplex.excenterExists_map** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
V₂ : Type u_3} {P₂ : Type u_4} [inst_4 : NormedAddCommGroup V₂]   [inst_5 : Inne
rProductSpace ℝ V₂] [inst_6 : MetricSpace P₂] [inst_7 : NormedAddTorsor V₂ P₂] {
n : ℕ}   [inst_8 : NeZero n] (s : Affine.Simplex ℝ P n) (f : P →ᵃⁱ[ℝ] P₂),   (s.
map f.toAffineMap ⋯).ExcenterExists = s.ExcenterExists
参数：s : Affine.Simplex ℝ P n；f : P →ᵃⁱ[ℝ] P₂；s.map f.toAffineMap ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AffineIsometry.injective`：∀ {𝕜 : Type u_1} {V₁' : Type u_4} {V₂ : Type u
_5} {P₁' : Type u_9} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : Seminor
medAddCommGrou…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Affine.Simplex.excenterWeightsUnnorm_map`：∀ {V : Type u_1} {P : Type u_2
} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Metri
cSpace P]   [inst_3 : NormedAd…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma excenterExists_map (f : P →ᵃⁱ[ℝ] P₂) :
    (s.map f.toAffineMap f.injective).ExcenterExists = s.ExcenterExists := by
  ext
  simp [ExcenterExists]
/-
**Affine.Simplex.excenterExists_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simpl
ex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] (s : Affine.Simplex ℝ P n) (S : AffineSubspace ℝ P)  
 (hS : affineSpan ℝ (Set.range s.points) ≤ S), (s.restrict S hS).ExcenterExists 
= s.ExcenterExists
参数：s : Affine.Simplex ℝ P n；S : AffineSubspace ℝ P；hS : affineSpan ℝ (Set.range 
s.points) ≤ S；s.restrict S hS。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Affine.Simplex.excenterWeightsUnnorm_restrict`：∀ {V : Type u_1} {P : Typ
e u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : 
MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma excenterExists_restrict (S : AffineSubspace ℝ P)
    (hS : affineSpan ℝ (Set.range s.points) ≤ S) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).ExcenterExists = s.ExcenterExists := by
  ext
  simp [ExcenterExists]

/-- The normalized weights of the vertices in an affine combination that gives an excenter with
signs determined by the given set of indices.  An excenter with those signs exists if and only if
the sum of these weights is 1. -/
/-
**Affine.Simplex.excenterWeights** 是 Mathlib 中的一个定义，位于命名空间 `Affine.Simplex`。
形式化陈述：excenterWeights (signs : Finset (Fin (n + 1))) : Fin (n + 1) -> Real
参数：signs : Finset (Fin (n + 1))。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The normalized weights of the vertices in an affine combination that gives an ex
center with
signs determined by the given set of indices.  An excenter with those signs exis
ts if and only if
the sum of these weights is 1.
-/
def excenterWeights (signs : Finset (Fin (n + 1))) : Fin (n + 1) → ℝ :=
  (∑ i, s.excenterWeightsUnnorm signs i)⁻¹ • s.excenterWeightsUnnorm signs
/-
**Affine.Simplex.excenterWeights_reindex** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simpl
ex`。
形式化陈述：excenterWeights_reindex (e : Fin (n + 1) ≃ Fin (m + 1)) (signs : Finset (F
in (m + 1))) : (s.reindex e).excenterWeights signs = s.excenterWeights (signs.ma
p e.symm) ∘ e.symm
参数：e : Fin (n + 1) ≃ Fin (m + 1)；signs : Finset (Fin (m + 1))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `Affine.Simplex.excenterWeightsUnnorm_reindex`：excenterWeightsUnnorm_rein
dex (e : Fin (n + 1) ≃ Fin (m + 1)) (signs : Finset (Fin (m + 1))) : (s.reindex 
e).excenterWeightsUnnorm signs = s…
· 使用定理 `Finset.sum_comp_equiv`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} {s
 : Finset ι} [inst : AddCommMonoid M] {f : κ → M} (e : ι ≃ κ),   s.sum (f ∘ ⇑e) 
= (Finset.m…
· 使用定理 `Finset.map_univ_equiv`：map_univ_equiv [Fintype β] (f : β ≃ α) : univ.map
 f.toEmbedding = univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma excenterWeights_reindex (e : Fin (n + 1) ≃ Fin (m + 1)) (signs : Finset (Fin (m + 1))) :
    (s.reindex e).excenterWeights signs =
      s.excenterWeights (signs.map e.symm) ∘ e.symm := by
  simp_rw [excenterWeights, excenterWeightsUnnorm_reindex, Finset.sum_comp_equiv,
    Finset.map_univ_equiv, Pi.smul_comp]
/-
**Affine.Simplex.excenterWeights_map** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
V₂ : Type u_3} {P₂ : Type u_4} [inst_4 : NormedAddCommGroup V₂]   [inst_5 : Inne
rProductSpace ℝ V₂] [inst_6 : MetricSpace P₂] [inst_7 : NormedAddTorsor V₂ P₂] {
n : ℕ}   [inst_8 : NeZero n] (s : Affine.Simplex ℝ P n) (f : P →ᵃⁱ[ℝ] P₂),   (s.
map f.toAffineMap ⋯).excenterWeights = s.excenterWeights
参数：s : Affine.Simplex ℝ P n；f : P →ᵃⁱ[ℝ] P₂；s.map f.toAffineMap ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AffineIsometry.injective`：∀ {𝕜 : Type u_1} {V₁' : Type u_4} {V₂ : Type u
_5} {P₁' : Type u_9} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : Seminor
medAddCommGrou…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Affine.Simplex.excenterWeightsUnnorm_map`：∀ {V : Type u_1} {P : Type u_2
} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Metri
cSpace P]   [inst_3 : NormedAd…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma excenterWeights_map (f : P →ᵃⁱ[ℝ] P₂) :
    (s.map f.toAffineMap f.injective).excenterWeights = s.excenterWeights := by
  ext
  simp [excenterWeights]
/-
**Affine.Simplex.excenterWeights_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simp
lex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] (s : Affine.Simplex ℝ P n) (S : AffineSubspace ℝ P)  
 (hS : affineSpan ℝ (Set.range s.points) ≤ S), (s.restrict S hS).excenterWeights
 = s.excenterWeights
参数：s : Affine.Simplex ℝ P n；S : AffineSubspace ℝ P；hS : affineSpan ℝ (Set.range 
s.points) ≤ S；s.restrict S hS。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Affine.Simplex.excenterWeightsUnnorm_restrict`：∀ {V : Type u_1} {P : Typ
e u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : 
MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma excenterWeights_restrict (S : AffineSubspace ℝ P)
    (hS : affineSpan ℝ (Set.range s.points) ≤ S) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).excenterWeights = s.excenterWeights := by
  ext
  simp [excenterWeights]

variable {s} in
/-
**Affine.Simplex.ExcenterExists.excenterWeights_ne_zero** 是 Mathlib 中的一个定理，位于命名空
间 `Affine.Simplex.ExcenterExists`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] {s : Affine.Simplex ℝ P n} {signs : Finset (Fin (n + 
1))},   s.ExcenterExists signs → ∀ (i : Fin (n + 1)), s.excenterWeights signs i 
≠ 0
参数：Fin (n + 1)；i : Fin (n + 1)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.excenterWeights.eq_1`：∀ {V : Type u_1} {P : Type u_2} [in
st : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpac
e P]   [inst_3 : NormedAd…
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Affine.Simplex.ExcenterExists.eq_1`：∀ {V : Type u_1} {P : Type u_2} [ins
t : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace
 P]   [inst_3 : NormedAd…
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `Affine.Simplex.excenterWeightsUnnorm_ne_zero`：excenterWeightsUnnorm_ne_z
ero (signs : Finset (Fin (n + 1))) (i : Fin (n + 1)) : s.excenterWeightsUnnorm s
igns i != 0
-/
lemma ExcenterExists.excenterWeights_ne_zero {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) (i : Fin (n + 1)) : s.excenterWeights signs i ≠ 0 := by
  rw [excenterWeights]
  refine mul_ne_zero ?_ (s.excenterWeightsUnnorm_ne_zero _ _)
  rw [ExcenterExists] at h
  simp [h]
/-
**Affine.Simplex.excenterWeightsUnnorm_compl** 是 Mathlib 中的一个定理，位于命名空间 `Affine.S
implex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] (s : Affine.Simplex ℝ P n) (signs : Finset (Fin (n + 
1))),   s.excenterWeightsUnnorm signsᶜ = -s.excenterWeightsUnnorm signs
参数：s : Affine.Simplex ℝ P n；signs : Finset (Fin (n + 1))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
@[simp] lemma excenterWeightsUnnorm_compl (signs : Finset (Fin (n + 1))) :
    s.excenterWeightsUnnorm signsᶜ = -s.excenterWeightsUnnorm signs := by
  ext i
  by_cases h : i ∈ signs <;> simp [excenterWeightsUnnorm, h]
/-
**Affine.Simplex.excenterWeights_compl** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex
`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] (s : Affine.Simplex ℝ P n) (signs : Finset (Fin (n + 
1))),   s.excenterWeights signsᶜ = s.excenterWeights signs
参数：s : Affine.Simplex ℝ P n；signs : Finset (Fin (n + 1))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Affine.Simplex.excenterWeightsUnnorm_compl`：∀ {V : Type u_1} {P : Type u
_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Met
ricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
· 使用引理 `inv_neg`：inv_neg : (-a)⁻¹ = -a⁻¹
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma excenterWeights_compl (signs : Finset (Fin (n + 1))) :
    s.excenterWeights signsᶜ = s.excenterWeights signs := by
  simp [excenterWeights, inv_neg]
/-
**Affine.Simplex.excenterExists_compl** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`
。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] (s : Affine.Simplex ℝ P n) {signs : Finset (Fin (n + 
1))},   s.ExcenterExists signsᶜ ↔ s.ExcenterExists signs
参数：s : Affine.Simplex ℝ P n；Fin (n + 1)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Affine.Simplex.excenterWeightsUnnorm_compl`：∀ {V : Type u_1} {P : Type u
_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Met
ricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma excenterExists_compl {signs : Finset (Fin (n + 1))} :
    s.ExcenterExists signsᶜ ↔ s.ExcenterExists signs := by
  simp [ExcenterExists]
/-
**Affine.Simplex.sum_excenterWeights** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simplex`。
形式化陈述：sum_excenterWeights (signs : Finset (Fin (n + 1))) [Decidable (s.ExcenterE
xists signs)] : ∑ i, s.excenterWeights signs i = if s.ExcenterExists signs then 
1 else 0
参数：signs : Finset (Fin (n + 1))；s.ExcenterExists signs。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
lemma sum_excenterWeights (signs : Finset (Fin (n + 1))) [Decidable (s.ExcenterExists signs)] :
    ∑ i, s.excenterWeights signs i = if s.ExcenterExists signs then 1 else 0 := by
  simp_rw [ExcenterExists, excenterWeights]
  split_ifs with h
  · simp [← Finset.mul_sum, h]
  · simp only [ne_eq, not_not] at h
    simp [h]
/-
**Affine.Simplex.sum_excenterWeights_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Affin
e.Simplex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] (s : Affine.Simplex ℝ P n) {signs : Finset (Fin (n + 
1))},   ∑ i, s.excenterWeights signs i = 1 ↔ s.ExcenterExists signs
参数：s : Affine.Simplex ℝ P n；Fin (n + 1)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Affine.Simplex.sum_excenterWeights`：sum_excenterWeights (signs : Finset 
(Fin (n + 1))) [Decidable (s.ExcenterExists signs)] : ∑ i, s.excenterWeights sig
ns i = if s.ExcenterExis…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma sum_excenterWeights_eq_one_iff {signs : Finset (Fin (n + 1))} :
    ∑ i, s.excenterWeights signs i = 1 ↔ s.ExcenterExists signs := by
  classical
  simp [sum_excenterWeights]

alias ⟨_, ExcenterExists.sum_excenterWeights_eq_one⟩ := sum_excenterWeights_eq_one_iff
/-
**Affine.Simplex.sum_excenterWeightsUnnorm_empty_pos** 是 Mathlib 中的一个引理，位于命名空间 `
Affine.Simplex`。
形式化陈述：sum_excenterWeightsUnnorm_empty_pos : 0 < ∑ i, s.excenterWeightsUnnorm ∅ i
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Affine.Simplex.excenterWeightsUnnorm_empty_apply`：∀ {V : Type u_1} {P : 
Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2
 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Finset.sum_pos`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid M]
 [inst_1 : Preorder M] [IsOrderedCancelAddMonoid M] {f : ι → M}   {s : Finset ι}
 [Ad…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Affine.Simplex.height_pos`：height_pos {n : Nat} [NeZero n] (s : Simplex 
Real P n) (i : Fin (n + 1)) : 0 < s.height i
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma sum_excenterWeightsUnnorm_empty_pos : 0 < ∑ i, s.excenterWeightsUnnorm ∅ i := by
  simp_rw [excenterWeightsUnnorm_empty_apply]
  positivity
/-
**Affine.Simplex.excenterWeights_empty_pos** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Sim
plex`。
形式化陈述：excenterWeights_empty_pos (i : Fin (n + 1)) : 0 < s.excenterWeights ∅ i
参数：i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Affine.Simplex.excenterWeightsUnnorm_empty_apply`：∀ {V : Type u_1} {P : 
Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2
 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `Finset.sum_pos`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid M]
 [inst_1 : Preorder M] [IsOrderedCancelAddMonoid M] {f : ι → M}   {s : Finset ι}
 [Ad…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用引理 `Affine.Simplex.height_pos`：height_pos {n : Nat} [NeZero n] (s : Simplex 
Real P n) (i : Fin (n + 1)) : 0 < s.height i
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma excenterWeights_empty_pos (i : Fin (n + 1)) : 0 < s.excenterWeights ∅ i := by
  simp only [excenterWeights, excenterWeightsUnnorm_empty_apply, Pi.smul_apply, smul_eq_mul]
  positivity

@[simp]
/-
**Affine.Simplex.sign_excenterWeights_empty** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Si
mplex`。
形式化陈述：sign_excenterWeights_empty (i : Fin (n + 1)) : SignType.sign (s.excenterWe
ights ∅ i) = 1
参数：i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sign_eq_one_iff`：sign_eq_one_iff : sign a = 1 ↔ 0 < a
· 使用引理 `Affine.Simplex.excenterWeights_empty_pos`：excenterWeights_empty_pos (i :
 Fin (n + 1)) : 0 < s.excenterWeights ∅ i
-/
lemma sign_excenterWeights_empty (i : Fin (n + 1)) : SignType.sign (s.excenterWeights ∅ i) = 1 := by
  rw [sign_eq_one_iff]
  exact s.excenterWeights_empty_pos i

/-- The existence of the incenter, expressed in terms of `ExcenterExists`. -/
/-
**Affine.Simplex.excenterExists_empty** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`
。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] (s : Affine.Simplex ℝ P n), s.ExcenterExists ∅
参数：s : Affine.Simplex ℝ P n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `Affine.Simplex.sum_excenterWeightsUnnorm_empty_pos`：sum_excenterWeightsU
nnorm_empty_pos : 0 < ∑ i, s.excenterWeightsUnnorm ∅ i

--- 原说明 ---
The existence of the incenter, expressed in terms of `ExcenterExists`.
-/
@[simp] lemma excenterExists_empty : s.ExcenterExists ∅ :=
  s.sum_excenterWeightsUnnorm_empty_pos.ne'
/-
**Affine.Simplex.sum_inv_height_sq_smul_vsub_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `
Affine.Simplex`。
形式化陈述：sum_inv_height_sq_smul_vsub_eq_zero : ∑ i, (s.height i)⁻¹ ^ 2 • (s.points 
i -ᵥ s.altitudeFoot i) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.add_sum_erase`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] [inst_1 : DecidableEq ι] (s : Finset ι) (f : ι → M) {a : ι},   a ∈ s → f 
a + ∑ x ∈ …
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_erase`：mem_erase {a b : α} {s : Finset α} : a in erase s b ↔ 
a != b ∧ a in s
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `real_inner_smul_right`：real_inner_smul_right (x y : F) (r : Real) : ⟪x, 
r • y⟫_Real = r * ⟪x, y⟫_Real
· 使用定理 `Submodule.mem_orthogonal_singleton_iff_inner_right`：mem_orthogonal_singl
eton_iff_inner_right {u v : E} : v in (𝕜 ∙ u)ᗮ ↔ ⟪u, v⟫ = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Submodule.orthogonal_le`：orthogonal_le {K₁ K₂ : Submodule 𝕜 E} (h : K₁ <
= K₂) : K₂ᗮ <= K₁ᗮ
· 使用定理 `Submodule.span_singleton_le_iff_mem`：span_singleton_le_iff_mem (m : M) (
p : Submodule R M) : R ∙ m <= p ↔ m in p
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s
· 使用定理 `vsub_mem_vectorSpan`：vsub_mem_vectorSpan {s : Set P} {p₁ p₂ : P} (hp₁ : 
p₁ in s) (hp₂ : p₂ in s) : p₁ -ᵥ p₂ in vectorSpan k s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Affine.Simplex.range_faceOpposite_points`：∀ {k : Type u_1} {V : Type u_2
} {P : Type u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Modu
le k V]   [inst_3 : AddTorsor …
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal`：vs
ub_orthogonalProjection_mem_direction_orthogonal (s : AffineSubspace 𝕜 P) [Nonem
pty s] [s.direction.HasOrthogonalProjection] (p : P) : p -…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
（共 59 条，此处仅展示前 30 条）
-/
lemma sum_inv_height_sq_smul_vsub_eq_zero :
    ∑ i, (s.height i)⁻¹ ^ 2 • (s.points i -ᵥ s.altitudeFoot i) = 0 := by
  suffices ∀ i, i ≠ 0 →
      ∑ j, ⟪s.points i -ᵥ s.points 0, (s.height j)⁻¹ ^ 2 • (s.points j -ᵥ s.altitudeFoot j)⟫ = 0 by
    rw [← Submodule.mem_bot ℝ,
      ← Submodule.inf_orthogonal_eq_bot (vectorSpan ℝ (Set.range s.points))]
    refine ⟨Submodule.sum_smul_mem _ _ fun i hi ↦
              vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan
                (mem_affineSpan _ (Set.mem_range_self _))
                (altitudeFoot_mem_affineSpan  _ _),
            ?_⟩
    rw [vectorSpan_range_eq_span_range_vsub_right_ne _ _ 0, Submodule.span_range_eq_iSup,
      ← Submodule.iInf_orthogonal, Submodule.coe_iInf, Set.mem_iInter]
    intro i
    rcases i with ⟨i, hi⟩
    simpa only [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sum]
      using this i hi
  intro i hi
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0),
    ← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩), ← add_assoc]
  convert! add_zero _
  · convert! Finset.sum_const_zero with j hj
    rw [real_inner_smul_right]
    convert! mul_zero _
    rw [← Submodule.mem_orthogonal_singleton_iff_inner_right]
    refine SetLike.le_def.1 (Submodule.orthogonal_le ?_)
      (vsub_orthogonalProjection_mem_direction_orthogonal _ _)
    rw [Submodule.span_singleton_le_iff_mem, direction_affineSpan]
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hj
    refine vsub_mem_vectorSpan _ ?_ ?_ <;>
      simp only [range_faceOpposite_points, Set.mem_image]
    · exact ⟨i, hj.1.symm, rfl⟩
    · exact ⟨0, hj.2.symm, rfl⟩
  · rw [inner_smul_right, inner_smul_right, inner_vsub_vsub_altitudeFoot_eq_height_sq _ hi,
      ← neg_vsub_eq_vsub_rev, inner_neg_left, inner_vsub_vsub_altitudeFoot_eq_height_sq _ hi.symm,
      mul_neg, inv_pow]
    simp [height]

/-- The inverse of the distance from one vertex to the opposite face, expressed as a sum of
multiples of that quantity for the other vertices. The multipliers, expressed here in terms of
inner products, are equal to the cosines of angles between faces (informally, the inverse
distances are proportional to the volumes of the faces and this is equivalent to expressing
the volume of a face as the sum of the signed volumes of projections of the other faces onto that
face). -/
/-
**Affine.Simplex.inv_height_eq_sum_mul_inv_dist** 是 Mathlib 中的一个引理，位于命名空间 `Affin
e.Simplex`。
形式化陈述：inv_height_eq_sum_mul_inv_dist (i : Fin (n + 1)) : (s.height i)⁻¹ = ∑ j in
 {k | k != i}, -(⟪s.points i -ᵥ s.altitudeFoot i, s.points j -ᵥ s.altitudeFoot j
⟫ / (s.height i * s.height j)) * (s.height j)⁻¹
参数：i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `Finset.filter_ne'`：filter_ne' [DecidableEq β] (s : Finset β) (b : β) : (
s.filter fun a => a != b) = s.erase b
· 使用定理 `Finset.sum_erase_eq_sub`：∀ {ι : Type u_1} {G : Type u_3} {s : Finset ι} 
[inst : AddCommGroup G] [inst_1 : DecidableEq ι] {f : ι → G} {a : ι},   a ∈ s → 
∑ x ∈ s.erase…
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `real_inner_self_eq_norm_mul_norm`：real_inner_self_eq_norm_mul_norm (x : 
F) : ⟪x, x⟫_Real = ‖x‖ * ‖x‖
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用引理 `Affine.Simplex.sum_inv_height_sq_smul_vsub_eq_zero`：sum_inv_height_sq_sm
ul_vsub_eq_zero : ∑ i, (s.height i)⁻¹ ^ 2 • (s.points i -ᵥ s.altitudeFoot i) = 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
（共 62 条，此处仅展示前 30 条）

--- 原说明 ---
The inverse of the distance from one vertex to the opposite face, expressed as a
 sum of
multiples of that quantity for the other vertices. The multipliers, expressed he
re in terms of
inner products, are equal to the cosines of angles between faces (informally, th
e inverse
distances are proportional to the volumes of the faces and this is equivalent to
 expressing
the volume of a face as the sum of the signed volumes of projections of the othe
r faces onto that
face).
-/
lemma inv_height_eq_sum_mul_inv_dist (i : Fin (n + 1)) :
    (s.height i)⁻¹ =
      ∑ j ∈ {k | k ≠ i},
        -(⟪s.points i -ᵥ s.altitudeFoot i, s.points j -ᵥ s.altitudeFoot j⟫ /
          (s.height i * s.height j)) *
        (s.height j)⁻¹ := by
  rw [← sub_eq_zero]
  simp_rw [neg_mul]
  rw [Finset.sum_neg_distrib, sub_neg_eq_add, Finset.filter_ne',
    Finset.sum_erase_eq_sub (Finset.mem_univ _), real_inner_self_eq_norm_mul_norm,
    ← dist_eq_norm_vsub]
  simp only [height, ne_eq, mul_eq_zero, dist_eq_zero, ne_altitudeFoot, or_self,
    not_false_eq_true, div_self, one_mul, add_sub_cancel]
  have h := s.sum_inv_height_sq_smul_vsub_eq_zero
  apply_fun fun v ↦ (s.height i)⁻¹ * ⟪s.points i -ᵥ s.altitudeFoot i, v⟫ at h
  rw [inner_sum, Finset.mul_sum] at h
  simp only [inner_zero_right, mul_zero, inner_smul_right, height] at h
  convert! h using 2 with j
  ring

/-- The inverse of the distance from one vertex to the opposite face is less than the sum of that
quantity for the other vertices. This implies the existence of the excenter opposite that vertex;
it also gives information about the location of the incenter (see
`excenterWeights_empty_lt_inv_two`). -/
/-
**Affine.Simplex.inv_height_lt_sum_inv_height** 是 Mathlib 中的一个引理，位于命名空间 `Affine.
Simplex`。
形式化陈述：inv_height_lt_sum_inv_height [Nat.AtLeastTwo n] (i : Fin (n + 1)) : (s.hei
ght i)⁻¹ < ∑ j in {k | k != i}, (s.height j)⁻¹
参数：i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Affine.Simplex.inv_height_eq_sum_mul_inv_dist`：inv_height_eq_sum_mul_inv
_dist (i : Fin (n + 1)) : (s.height i)⁻¹ = ∑ j in {k | k != i}, -(⟪s.points i -ᵥ
 s.altitudeFoot i, s.points j -ᵥ s.…
· 使用定理 `Finset.sum_lt_sum_of_nonempty`：∀ {ι : Type u_1} {M : Type u_4} [inst : A
ddCommMonoid M] [inst_1 : Preorder M] [IsOrderedCancelAddMonoid M]   {f g : ι → 
M} {s : Finset ι} […
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Finset.filter_ne'`：filter_ne' [DecidableEq β] (s : Finset β) (b : β) : (
s.filter fun a => a != b) = s.erase b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.card_ne_zero`：card_ne_zero : #s != 0 ↔ s.Nonempty
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.card_erase_of_mem`：card_erase_of_mem : a in s -> #(s.erase a) = #
s - 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `mul_lt_of_lt_one_left`：mul_lt_of_lt_one_left [MulPosStrictMono α] (hb : 
0 < b) (h : a < 1) : a * b < b
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `neg_lt`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStric
tMono α] {a b : α} [AddRightStrictMono α],   -a < b ↔ -b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `Affine.Simplex.neg_one_lt_inner_vsub_altitudeFoot_div`：neg_one_lt_inner_
vsub_altitudeFoot_div (s : Simplex Real P n) (i j : Fin (n + 1)) : -1 < ⟪s.point
s i -ᵥ s.altitudeFoot i, s.points j -ᵥ s.al…

--- 原说明 ---
The inverse of the distance from one vertex to the opposite face is less than th
e sum of that
quantity for the other vertices. This implies the existence of the excenter oppo
site that vertex;
it also gives information about the location of the incenter (see
`excenterWeights_empty_lt_inv_two`).
-/
lemma inv_height_lt_sum_inv_height [Nat.AtLeastTwo n] (i : Fin (n + 1)) :
    (s.height i)⁻¹ < ∑ j ∈ {k | k ≠ i}, (s.height j)⁻¹ := by
  rw [inv_height_eq_sum_mul_inv_dist]
  refine Finset.sum_lt_sum_of_nonempty ?_ ?_
  · rw [Finset.filter_ne', ← Finset.card_ne_zero]
    simp only [Finset.mem_univ, Finset.card_erase_of_mem, Finset.card_univ, Fintype.card_fin,
      add_tsub_cancel_right]
    exact NeZero.ne _
  · rintro j hj
    refine mul_lt_of_lt_one_left ?_ ?_
    · simp [height_pos]
    · rw [neg_lt]
      exact neg_one_lt_inner_vsub_altitudeFoot_div _ _ _
/-
**Affine.Simplex.sum_excenterWeightsUnnorm_singleton_pos** 是 Mathlib 中的一个引理，位于命名
空间 `Affine.Simplex`。
形式化陈述：sum_excenterWeightsUnnorm_singleton_pos [Nat.AtLeastTwo n] (i : Fin (n + 1
)) : 0 < ∑ j, s.excenterWeightsUnnorm {i} j
参数：i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_add_sum_compl`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCom
mMonoid M] [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (s : Finset ι)   (f : ι
 → M), ∑ i ∈ s…
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Affine.Simplex.excenterWeightsUnnorm.eq_1`：∀ {V : Type u_1} {P : Type u_
2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Metr
icSpace P]   [inst_3 : NormedAd…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Finset.mem_filter_univ`：mem_filter_univ {p : α -> Prop} [DecidablePred p
] : forall x, x in univ.filter p ↔ p x
· 使用引理 `Affine.Simplex.inv_height_lt_sum_inv_height`：inv_height_lt_sum_inv_heigh
t [Nat.AtLeastTwo n] (i : Fin (n + 1)) : (s.height i)⁻¹ < ∑ j in {k | k != i}, (
s.height j)⁻¹
-/
lemma sum_excenterWeightsUnnorm_singleton_pos [Nat.AtLeastTwo n] (i : Fin (n + 1)) :
    0 < ∑ j, s.excenterWeightsUnnorm {i} j := by
  rw [← Finset.sum_add_sum_compl {i}, Finset.sum_singleton]
  nth_rw 1 [excenterWeightsUnnorm]
  simp only [Finset.mem_singleton, ↓reduceIte, neg_mul, one_mul, lt_neg_add_iff_add_lt, add_zero]
  convert! s.inv_height_lt_sum_inv_height i using 2 with j h
  · ext j
    simp
  · rw [Finset.mem_filter_univ] at h
    simp [excenterWeightsUnnorm, h]
/-
**Affine.Simplex.sign_excenterWeights_singleton_neg** 是 Mathlib 中的一个引理，位于命名空间 `A
ffine.Simplex`。
形式化陈述：sign_excenterWeights_singleton_neg [Nat.AtLeastTwo n] (i : Fin (n + 1)) : 
SignType.sign (s.excenterWeights {i} i) = -1
参数：i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sign_mul`：sign_mul (x y : α) : sign (x * y) = sign x * sign y
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sign_eq_one_iff`：sign_eq_one_iff : sign a = 1 ↔ 0 < a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Affine.Simplex.sum_excenterWeightsUnnorm_singleton_pos`：sum_excenterWeig
htsUnnorm_singleton_pos [Nat.AtLeastTwo n] (i : Fin (n + 1)) : 0 < ∑ j, s.excent
erWeightsUnnorm {i} j
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `sign_neg`：sign_neg (ha : a < 0) : sign a = -1
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
lemma sign_excenterWeights_singleton_neg [Nat.AtLeastTwo n] (i : Fin (n + 1)) :
    SignType.sign (s.excenterWeights {i} i) = -1 := by
  simp_rw [excenterWeights, Pi.smul_apply, smul_eq_mul, sign_mul]
  convert! one_mul _
  · rw [sign_eq_one_iff, inv_pos]
    exact s.sum_excenterWeightsUnnorm_singleton_pos i
  · simp [excenterWeightsUnnorm]
/-
**Affine.Simplex.sign_excenterWeights_singleton_pos** 是 Mathlib 中的一个引理，位于命名空间 `A
ffine.Simplex`。
形式化陈述：sign_excenterWeights_singleton_pos [Nat.AtLeastTwo n] {i j : Fin (n + 1)} 
(h : i != j) : SignType.sign (s.excenterWeights {i} j) = 1
参数：n + 1；h : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sign_mul`：sign_mul (x y : α) : sign (x * y) = sign x * sign y
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sign_eq_one_iff`：sign_eq_one_iff : sign a = 1 ↔ 0 < a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Affine.Simplex.sum_excenterWeightsUnnorm_singleton_pos`：sum_excenterWeig
htsUnnorm_singleton_pos [Nat.AtLeastTwo n] (i : Fin (n + 1)) : 0 < ∑ j, s.excent
erWeightsUnnorm {i} j
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `sign_pos`：sign_pos (ha : 0 < a) : sign a = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sign_excenterWeights_singleton_pos [Nat.AtLeastTwo n] {i j : Fin (n + 1)} (h : i ≠ j) :
    SignType.sign (s.excenterWeights {i} j) = 1 := by
  simp_rw [excenterWeights, Pi.smul_apply, smul_eq_mul, sign_mul]
  convert! one_mul _
  · rw [sign_eq_one_iff, inv_pos]
    exact s.sum_excenterWeightsUnnorm_singleton_pos i
  · simp [excenterWeightsUnnorm, h.symm]

/-- The existence of the excenter opposite a vertex (in two or more dimensions), expressed in
terms of `ExcenterExists`. -/
/-
**Affine.Simplex.excenterExists_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simp
lex`。
形式化陈述：excenterExists_singleton [Nat.AtLeastTwo n] (i : Fin (n + 1)) : s.Excenter
Exists {i}
参数：i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `Affine.Simplex.sum_excenterWeightsUnnorm_singleton_pos`：sum_excenterWeig
htsUnnorm_singleton_pos [Nat.AtLeastTwo n] (i : Fin (n + 1)) : 0 < ∑ j, s.excent
erWeightsUnnorm {i} j

--- 原说明 ---
The existence of the excenter opposite a vertex (in two or more dimensions), exp
ressed in
terms of `ExcenterExists`.
-/
lemma excenterExists_singleton [Nat.AtLeastTwo n] (i : Fin (n + 1)) : s.ExcenterExists {i} :=
  (s.sum_excenterWeightsUnnorm_singleton_pos i).ne'

open Finset in
/-- The barycentric coordinates of the incenter are less than `2⁻¹` (thus, it lies closer on an
angle bisector to the opposite side than to the vertex, or equivalently the image of the incenter
under a homothety with scale factor 2 about a vertex lies outside the simplex). -/
/-
**Affine.Simplex.excenterWeights_empty_lt_inv_two** 是 Mathlib 中的一个引理，位于命名空间 `Aff
ine.Simplex`。
形式化陈述：excenterWeights_empty_lt_inv_two [n.AtLeastTwo] (i : Fin (n + 1)) : s.exce
nterWeights ∅ i < 2⁻¹
参数：i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Affine.Simplex.inv_height_lt_sum_inv_height`：inv_height_lt_sum_inv_heigh
t [Nat.AtLeastTwo n] (i : Fin (n + 1)) : (s.height i)⁻¹ < ∑ j in {k | k != i}, (
s.height j)⁻¹
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_lt_add_iff_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [Ad
dLeftStrictMono α] [AddLeftReflectLT α] (a : α) {b c : α},   a + b < a + c ↔ b <
 c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Finset.compl_singleton`：compl_singleton (a : α) : ({a} : Finset α)ᶜ = un
iv.erase a
· 使用定理 `Finset.filter_ne'`：filter_ne' [DecidableEq β] (s : Finset β) (b : β) : (
s.filter fun a => a != b) = s.erase b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用引理 `div_lt_iff₀`：div_lt_iff₀ (hc : 0 < c) : b / c < a ↔ b < a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Finset.sum_pos`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid M]
 [inst_1 : Preorder M] [IsOrderedCancelAddMonoid M] {f : ι → M}   {s : Finset ι}
 [Ad…
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Affine.Simplex.height_pos`：height_pos {n : Nat} [NeZero n] (s : Simplex 
Real P n) (i : Fin (n + 1)) : 0 < s.height i
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用引理 `lt_inv_mul_iff₀`：lt_inv_mul_iff₀ (hc : 0 < c) : a < c⁻¹ * b ↔ c * a < b
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
The barycentric coordinates of the incenter are less than `2⁻¹` (thus, it lies c
loser on an
angle bisector to the opposite side than to the vertex, or equivalently the imag
e of the incenter
under a homothety with scale factor 2 about a vertex lies outside the simplex).
-/
lemma excenterWeights_empty_lt_inv_two [n.AtLeastTwo] (i : Fin (n + 1)) :
    s.excenterWeights ∅ i < 2⁻¹ := by
  have h : (s.height i)⁻¹ + (s.height i)⁻¹ < (s.height i)⁻¹ + ∑ j ∈ {i}ᶜ, (s.height j)⁻¹ := by
    have := s.inv_height_lt_sum_inv_height i
    rwa [filter_ne', ← compl_singleton, ← add_lt_add_iff_left (s.height i)⁻¹] at this
  replace h : 2 * (s.height i)⁻¹ < ∑ j ∈ {i}, (s.height j)⁻¹ + ∑ j ∈ {i}ᶜ, (s.height j)⁻¹ := by
    rwa [two_mul, sum_singleton]
  replace h : (s.height i)⁻¹ / ∑ i, (s.height i)⁻¹ < 2⁻¹ := by
    rwa [sum_add_sum_compl, ← lt_inv_mul_iff₀ zero_lt_two, ← div_lt_iff₀ (by positivity)] at h
  convert! h
  simp [excenterWeights, excenterWeightsUnnorm, div_eq_inv_mul]

/-- The exsphere with signs determined by the given set of indices (for the empty set, this is
the insphere; for a singleton set, this is the exsphere opposite a vertex).  This is only
meaningful if `s.ExcenterExists`; otherwise, it is a sphere of radius zero at some arbitrary
point. -/
/-
**Affine.Simplex.exsphere** 是 Mathlib 中的一个定义，位于命名空间 `Affine.Simplex`。
形式化陈述：exsphere (signs : Finset (Fin (n + 1))) : Sphere P where center
参数：signs : Finset (Fin (n + 1))。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The exsphere with signs determined by the given set of indices (for the empty se
t, this is
the insphere; for a singleton set, this is the exsphere opposite a vertex).  Thi
s is only
meaningful if `s.ExcenterExists`; otherwise, it is a sphere of radius zero at so
me arbitrary
point.
-/
def exsphere (signs : Finset (Fin (n + 1))) : Sphere P where
  center := Finset.univ.affineCombination ℝ s.points (s.excenterWeights signs)
  radius := |(∑ i, s.excenterWeightsUnnorm signs i)⁻¹|
/-
**Affine.Simplex.exsphere_reindex** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simplex`。
形式化陈述：exsphere_reindex (e : Fin (n + 1) ≃ Fin (m + 1)) (signs : Finset (Fin (m +
 1))) : (s.reindex e).exsphere signs = s.exsphere (signs.map e.symm)
参数：e : Fin (n + 1) ≃ Fin (m + 1)；signs : Finset (Fin (m + 1))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `Affine.Simplex.excenterWeightsUnnorm_reindex`：excenterWeightsUnnorm_rein
dex (e : Fin (n + 1) ≃ Fin (m + 1)) (signs : Finset (Fin (m + 1))) : (s.reindex 
e).excenterWeightsUnnorm signs = s…
· 使用引理 `Affine.Simplex.excenterWeights_reindex`：excenterWeights_reindex (e : Fin
 (n + 1) ≃ Fin (m + 1)) (signs : Finset (Fin (m + 1))) : (s.reindex e).excenterW
eights signs = s.excenterWei…
· 使用定理 `Finset.sum_comp_equiv`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} {s
 : Finset ι} [inst : AddCommMonoid M] {f : κ → M} (e : ι ≃ κ),   s.sum (f ∘ ⇑e) 
= (Finset.m…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.map_univ_equiv`：map_univ_equiv [Fintype β] (f : β ≃ α) : univ.map
 f.toEmbedding = univ
· 使用定理 `abs_inv`：abs_inv (a : α) : |a⁻¹| = |a|⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma exsphere_reindex (e : Fin (n + 1) ≃ Fin (m + 1)) (signs : Finset (Fin (m + 1))) :
    (s.reindex e).exsphere signs = s.exsphere (signs.map e.symm) := by
  simp_rw [exsphere, excenterWeightsUnnorm_reindex, excenterWeights_reindex, Finset.sum_comp_equiv,
    reindex, ← Equiv.coe_toEmbedding, ← Finset.affineCombination_map]
  simp

/-- The insphere of a simplex. -/
/-
**Affine.Simplex.insphere** 是 Mathlib 中的一个定义，位于命名空间 `Affine.Simplex`。
形式化陈述：insphere : Sphere P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The insphere of a simplex.
-/
def insphere : Sphere P :=
  s.exsphere ∅
/-
**Affine.Simplex.insphere_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
m n : ℕ} [inst_4 : NeZero m] [inst_5 : NeZero n] (s : Affine.Simplex ℝ P n)   (e
 : Fin (n + 1) ≃ Fin (m + 1)), (s.reindex e).insphere = s.insphere
参数：s : Affine.Simplex ℝ P n；e : Fin (n + 1) ≃ Fin (m + 1)；s.reindex e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Affine.Simplex.exsphere_reindex`：exsphere_reindex (e : Fin (n + 1) ≃ Fin
 (m + 1)) (signs : Finset (Fin (m + 1))) : (s.reindex e).exsphere signs = s.exsp
here (signs.map e.sym…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma insphere_reindex (e : Fin (n + 1) ≃ Fin (m + 1)) :
    (s.reindex e).insphere = s.insphere := by
  simp_rw [insphere, exsphere_reindex]
  simp

/-- The excenter with signs determined by the given set of indices (for the empty set, this is
the incenter; for a singleton set, this is the excenter opposite a vertex).  This is only
meaningful if `s.ExcenterExists signs`; otherwise, it is some arbitrary point. -/
/-
**Affine.Simplex.excenter** 是 Mathlib 中的一个定义，位于命名空间 `Affine.Simplex`。
形式化陈述：excenter (signs : Finset (Fin (n + 1))) : P
参数：signs : Finset (Fin (n + 1))。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The excenter with signs determined by the given set of indices (for the empty se
t, this is
the incenter; for a singleton set, this is the excenter opposite a vertex).  Thi
s is only
meaningful if `s.ExcenterExists signs`; otherwise, it is some arbitrary point.
-/
def excenter (signs : Finset (Fin (n + 1))) : P :=
  (s.exsphere signs).center
/-
**Affine.Simplex.excenter_reindex** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simplex`。
形式化陈述：excenter_reindex (e : Fin (n + 1) ≃ Fin (m + 1)) (signs : Finset (Fin (m +
 1))) : (s.reindex e).excenter signs = s.excenter (signs.map e.symm)
参数：e : Fin (n + 1) ≃ Fin (m + 1)；signs : Finset (Fin (m + 1))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Affine.Simplex.exsphere_reindex`：exsphere_reindex (e : Fin (n + 1) ≃ Fin
 (m + 1)) (signs : Finset (Fin (m + 1))) : (s.reindex e).exsphere signs = s.exsp
here (signs.map e.sym…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma excenter_reindex (e : Fin (n + 1) ≃ Fin (m + 1)) (signs : Finset (Fin (m + 1))) :
    (s.reindex e).excenter signs = s.excenter (signs.map e.symm) := by
  simp_rw [excenter, exsphere_reindex]

variable {s} in
/-
**Affine.Simplex.ExcenterExists.excenter_map** 是 Mathlib 中的一个定理，位于命名空间 `Affine.S
implex.ExcenterExists`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
V₂ : Type u_3} {P₂ : Type u_4} [inst_4 : NormedAddCommGroup V₂]   [inst_5 : Inne
rProductSpace ℝ V₂] [inst_6 : MetricSpace P₂] [inst_7 : NormedAddTorsor V₂ P₂] {
n : ℕ}   [inst_8 : NeZero n] {s : Affine.Simplex ℝ P n} {signs : Finset (Fin (n 
+ 1))},   s.ExcenterExists signs → ∀ (f : P →ᵃⁱ[ℝ] P₂), (s.map f.toAffineMap ⋯).
excenter signs = f (s.excenter signs)
参数：Fin (n + 1)；f : P →ᵃⁱ[ℝ] P₂；s.map f.toAffineMap ⋯；s.excenter signs。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AffineIsometry.injective`：∀ {𝕜 : Type u_1} {V₁' : Type u_4} {V₂ : Type u
_5} {P₁' : Type u_9} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : Seminor
medAddCommGrou…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.map_points`：∀ {k : Type u_1} {V : Type u_2} {V₂ : Type u_
3} {P : Type u_5} {P₂ : Type u_6} [inst : Ring k] [inst_1 : AddCommGroup V]   [i
nst_2 : AddComm…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Affine.Simplex.excenterWeights_map`：∀ {V : Type u_1} {P : Type u_2} [ins
t : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace
 P]   [inst_3 : NormedAd…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Affine.Simplex.excenterWeightsUnnorm_map`：∀ {V : Type u_1} {P : Type u_2
} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Metri
cSpace P]   [inst_3 : NormedAd…
· 使用定理 `abs_inv`：abs_inv (a : α) : |a⁻¹| = |a|⁻¹
· 使用定理 `Finset.map_affineCombination`：map_affineCombination {V₂ P₂ : Type*} [Add
CommGroup V₂] [Module k V₂] [AffineSpace V₂ P₂] (p : ι -> P) (w : ι -> k) (hw : 
s.sum w = 1) (f : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Affine.Simplex.ExcenterExists.sum_excenterWeights_eq_one`：∀ {V : Type u_
1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V]
 [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma ExcenterExists.excenter_map {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) (f : P →ᵃⁱ[ℝ] P₂) :
    (s.map f.toAffineMap f.injective).excenter signs = f (s.excenter signs) := by
  simp [excenter, exsphere, ← AffineIsometry.coe_toAffineMap, h.sum_excenterWeights_eq_one,
    Finset.map_affineCombination]

variable {s} in
/-
**Affine.Simplex.ExcenterExists.excenter_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Aff
ine.Simplex.ExcenterExists`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] {s : Affine.Simplex ℝ P n} {signs : Finset (Fin (n + 
1))},   s.ExcenterExists signs →     ∀ (S : AffineSubspace ℝ P) (hS : affineSpan
 ℝ (Set.range s.points) ≤ S),       ↑((s.restrict S hS).excenter signs) = s.exce
nter signs
参数：Fin (n + 1)；S : AffineSubspace ℝ P；hS : affineSpan ℝ (Set.range s.points) ≤ S
；(s.restrict S hS).excenter signs。
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
· 使用定理 `AffineIsometry.injective`：∀ {𝕜 : Type u_1} {V₁' : Type u_4} {V₂ : Type u
_5} {P₁' : Type u_9} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : Seminor
medAddCommGrou…
· 使用定理 `Affine.Simplex.ExcenterExists.excenter_map`：∀ {V : Type u_1} {P : Type u
_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Met
ricSpace P]   [inst_3 : NormedAd…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.excenterExists_restrict`：∀ {V : Type u_1} {P : Type u_2} 
[inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricS
pace P]   [inst_3 : NormedAd…
-/
@[simp] lemma ExcenterExists.excenter_restrict {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) (S : AffineSubspace ℝ P)
    (hS : affineSpan ℝ (Set.range s.points) ≤ S) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).excenter signs = s.excenter signs := by
  rw [← s.excenterExists_restrict S hS] at h
  have := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  exact (h.excenter_map S.subtypeₐᵢ).symm

/-- The incenter of a simplex. -/
/-
**Affine.Simplex.incenter** 是 Mathlib 中的一个定义，位于命名空间 `Affine.Simplex`。
形式化陈述：incenter : P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The incenter of a simplex.
-/
def incenter : P :=
  (s.exsphere ∅).center
/-
**Affine.Simplex.incenter_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
m n : ℕ} [inst_4 : NeZero m] [inst_5 : NeZero n] (s : Affine.Simplex ℝ P n)   (e
 : Fin (n + 1) ≃ Fin (m + 1)), (s.reindex e).incenter = s.incenter
参数：s : Affine.Simplex ℝ P n；e : Fin (n + 1) ≃ Fin (m + 1)；s.reindex e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Affine.Simplex.exsphere_reindex`：exsphere_reindex (e : Fin (n + 1) ≃ Fin
 (m + 1)) (signs : Finset (Fin (m + 1))) : (s.reindex e).exsphere signs = s.exsp
here (signs.map e.sym…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma incenter_reindex (e : Fin (n + 1) ≃ Fin (m + 1)) :
    (s.reindex e).incenter = s.incenter := by
  simp_rw [incenter, exsphere_reindex]
  simp
/-
**Affine.Simplex.incenter_map** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
V₂ : Type u_3} {P₂ : Type u_4} [inst_4 : NormedAddCommGroup V₂]   [inst_5 : Inne
rProductSpace ℝ V₂] [inst_6 : MetricSpace P₂] [inst_7 : NormedAddTorsor V₂ P₂] {
n : ℕ}   [inst_8 : NeZero n] (s : Affine.Simplex ℝ P n) (f : P →ᵃⁱ[ℝ] P₂), (s.ma
p f.toAffineMap ⋯).incenter = f s.incenter
参数：s : Affine.Simplex ℝ P n；f : P →ᵃⁱ[ℝ] P₂；s.map f.toAffineMap ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.ExcenterExists.excenter_map`：∀ {V : Type u_1} {P : Type u
_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Met
ricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.excenterExists_empty`：∀ {V : Type u_1} {P : Type u_2} [in
st : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpac
e P]   [inst_3 : NormedAd…
-/
@[simp] lemma incenter_map (f : P →ᵃⁱ[ℝ] P₂) :
    (s.map f.toAffineMap f.injective).incenter = f s.incenter :=
  s.excenterExists_empty.excenter_map f
/-
**Affine.Simplex.incenter_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] (s : Affine.Simplex ℝ P n) (S : AffineSubspace ℝ P)  
 (hS : affineSpan ℝ (Set.range s.points) ≤ S), ↑(s.restrict S hS).incenter = s.i
ncenter
参数：s : Affine.Simplex ℝ P n；S : AffineSubspace ℝ P；hS : affineSpan ℝ (Set.range 
s.points) ≤ S；s.restrict S hS。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.ExcenterExists.excenter_restrict`：∀ {V : Type u_1} {P : T
ype u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 
: MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.excenterExists_empty`：∀ {V : Type u_1} {P : Type u_2} [in
st : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpac
e P]   [inst_3 : NormedAd…
-/
@[simp] lemma incenter_restrict (S : AffineSubspace ℝ P)
    (hS : affineSpan ℝ (Set.range s.points) ≤ S) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).incenter = s.incenter :=
  s.excenterExists_empty.excenter_restrict S hS

/-- The distance between an excenter and a face of the simplex (zero if no such excenter
exists). -/
/-
**Affine.Simplex.exradius** 是 Mathlib 中的一个定义，位于命名空间 `Affine.Simplex`。
形式化陈述：exradius (signs : Finset (Fin (n + 1))) : Real
参数：signs : Finset (Fin (n + 1))。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The distance between an excenter and a face of the simplex (zero if no such exce
nter
exists).
-/
def exradius (signs : Finset (Fin (n + 1))) : ℝ :=
  (s.exsphere signs).radius
/-
**Affine.Simplex.exradius_reindex** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simplex`。
形式化陈述：exradius_reindex (e : Fin (n + 1) ≃ Fin (m + 1)) (signs : Finset (Fin (m +
 1))) : (s.reindex e).exradius signs = s.exradius (signs.map e.symm)
参数：e : Fin (n + 1) ≃ Fin (m + 1)；signs : Finset (Fin (m + 1))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Affine.Simplex.exsphere_reindex`：exsphere_reindex (e : Fin (n + 1) ≃ Fin
 (m + 1)) (signs : Finset (Fin (m + 1))) : (s.reindex e).exsphere signs = s.exsp
here (signs.map e.sym…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma exradius_reindex (e : Fin (n + 1) ≃ Fin (m + 1)) (signs : Finset (Fin (m + 1))) :
    (s.reindex e).exradius signs = s.exradius (signs.map e.symm) := by
  simp_rw [exradius, exsphere_reindex]
/-
**Affine.Simplex.exradius_map** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
V₂ : Type u_3} {P₂ : Type u_4} [inst_4 : NormedAddCommGroup V₂]   [inst_5 : Inne
rProductSpace ℝ V₂] [inst_6 : MetricSpace P₂] [inst_7 : NormedAddTorsor V₂ P₂] {
n : ℕ}   [inst_8 : NeZero n] (s : Affine.Simplex ℝ P n) (f : P →ᵃⁱ[ℝ] P₂), (s.ma
p f.toAffineMap ⋯).exradius = s.exradius
参数：s : Affine.Simplex ℝ P n；f : P →ᵃⁱ[ℝ] P₂；s.map f.toAffineMap ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AffineIsometry.injective`：∀ {𝕜 : Type u_1} {V₁' : Type u_4} {V₂ : Type u
_5} {P₁' : Type u_9} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : Seminor
medAddCommGrou…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.map_points`：∀ {k : Type u_1} {V : Type u_2} {V₂ : Type u_
3} {P : Type u_5} {P₂ : Type u_6} [inst : Ring k] [inst_1 : AddCommGroup V]   [i
nst_2 : AddComm…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AffineIsometry.coe_toAffineMap`：coe_toAffineMap : ⇑f.toAffineMap = f
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Affine.Simplex.excenterWeights_map`：∀ {V : Type u_1} {P : Type u_2} [ins
t : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace
 P]   [inst_3 : NormedAd…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Affine.Simplex.excenterWeightsUnnorm_map`：∀ {V : Type u_1} {P : Type u_2
} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Metri
cSpace P]   [inst_3 : NormedAd…
· 使用定理 `abs_inv`：abs_inv (a : α) : |a⁻¹| = |a|⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma exradius_map (f : P →ᵃⁱ[ℝ] P₂) :
    (s.map f.toAffineMap f.injective).exradius = s.exradius := by
  ext
  simp [exradius, exsphere]
/-
**Affine.Simplex.exradius_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] (s : Affine.Simplex ℝ P n) (S : AffineSubspace ℝ P)  
 (hS : affineSpan ℝ (Set.range s.points) ≤ S), (s.restrict S hS).exradius = s.ex
radius
参数：s : Affine.Simplex ℝ P n；S : AffineSubspace ℝ P；hS : affineSpan ℝ (Set.range 
s.points) ≤ S；s.restrict S hS。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Affine.Simplex.excenterWeights_restrict`：∀ {V : Type u_1} {P : Type u_2}
 [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Metric
Space P]   [inst_3 : NormedAd…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Affine.Simplex.excenterWeightsUnnorm_restrict`：∀ {V : Type u_1} {P : Typ
e u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : 
MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `abs_inv`：abs_inv (a : α) : |a⁻¹| = |a|⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma exradius_restrict (S : AffineSubspace ℝ P)
    (hS : affineSpan ℝ (Set.range s.points) ≤ S) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).exradius = s.exradius := by
  ext
  simp [exradius, exsphere]

/-- The distance between the incenter and a face of the simplex. -/
/-
**Affine.Simplex.inradius** 是 Mathlib 中的一个定义，位于命名空间 `Affine.Simplex`。
形式化陈述：inradius : Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The distance between the incenter and a face of the simplex.
-/
def inradius : ℝ :=
  (s.exsphere ∅).radius
/-
**Affine.Simplex.inradius_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
m n : ℕ} [inst_4 : NeZero m] [inst_5 : NeZero n] (s : Affine.Simplex ℝ P n)   (e
 : Fin (n + 1) ≃ Fin (m + 1)), (s.reindex e).inradius = s.inradius
参数：s : Affine.Simplex ℝ P n；e : Fin (n + 1) ≃ Fin (m + 1)；s.reindex e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Affine.Simplex.exsphere_reindex`：exsphere_reindex (e : Fin (n + 1) ≃ Fin
 (m + 1)) (signs : Finset (Fin (m + 1))) : (s.reindex e).exsphere signs = s.exsp
here (signs.map e.sym…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma inradius_reindex (e : Fin (n + 1) ≃ Fin (m + 1)) :
    (s.reindex e).inradius = s.inradius := by
  simp_rw [inradius, exsphere_reindex]
  simp
/-
**Affine.Simplex.inradius_map** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
V₂ : Type u_3} {P₂ : Type u_4} [inst_4 : NormedAddCommGroup V₂]   [inst_5 : Inne
rProductSpace ℝ V₂] [inst_6 : MetricSpace P₂] [inst_7 : NormedAddTorsor V₂ P₂] {
n : ℕ}   [inst_8 : NeZero n] (s : Affine.Simplex ℝ P n) (f : P →ᵃⁱ[ℝ] P₂), (s.ma
p f.toAffineMap ⋯).inradius = s.inradius
参数：s : Affine.Simplex ℝ P n；f : P →ᵃⁱ[ℝ] P₂；s.map f.toAffineMap ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `AffineIsometry.injective`：∀ {𝕜 : Type u_1} {V₁' : Type u_4} {V₂ : Type u
_5} {P₁' : Type u_9} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : Seminor
medAddCommGrou…
· 使用定理 `Affine.Simplex.exradius_map`：∀ {V : Type u_1} {P : Type u_2} [inst : Nor
medAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [
inst_3 : NormedAd…
-/
@[simp] lemma inradius_map (f : P →ᵃⁱ[ℝ] P₂) :
    (s.map f.toAffineMap f.injective).inradius = s.inradius :=
  congr_fun (s.exradius_map f) _
/-
**Affine.Simplex.inradius_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] (s : Affine.Simplex ℝ P n) (S : AffineSubspace ℝ P)  
 (hS : affineSpan ℝ (Set.range s.points) ≤ S), (s.restrict S hS).inradius = s.in
radius
参数：s : Affine.Simplex ℝ P n；S : AffineSubspace ℝ P；hS : affineSpan ℝ (Set.range 
s.points) ≤ S；s.restrict S hS。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Affine.Simplex.exradius_restrict`：∀ {V : Type u_1} {P : Type u_2} [inst 
: NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P
]   [inst_3 : NormedAd…
-/
@[simp] lemma inradius_restrict (S : AffineSubspace ℝ P)
    (hS : affineSpan ℝ (Set.range s.points) ≤ S) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).inradius = s.inradius :=
  congr_fun (s.exradius_restrict S hS) _
/-
**Affine.Simplex.exsphere_center** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] (s : Affine.Simplex ℝ P n) (signs : Finset (Fin (n + 
1))),   (s.exsphere signs).center = s.excenter signs
参数：s : Affine.Simplex ℝ P n；signs : Finset (Fin (n + 1))；s.exsphere signs。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma exsphere_center (signs : Finset (Fin (n + 1))) :
    (s.exsphere signs).center = s.excenter signs :=
  rfl
/-
**Affine.Simplex.exsphere_radius** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] (s : Affine.Simplex ℝ P n) (signs : Finset (Fin (n + 
1))),   (s.exsphere signs).radius = s.exradius signs
参数：s : Affine.Simplex ℝ P n；signs : Finset (Fin (n + 1))；s.exsphere signs。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma exsphere_radius (signs : Finset (Fin (n + 1))) :
    (s.exsphere signs).radius = s.exradius signs :=
  rfl
/-
**Affine.Simplex.insphere_center** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] (s : Affine.Simplex ℝ P n), s.insphere.center = s.inc
enter
参数：s : Affine.Simplex ℝ P n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma insphere_center : s.insphere.center = s.incenter :=
  rfl
/-
**Affine.Simplex.insphere_radius** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] (s : Affine.Simplex ℝ P n), s.insphere.radius = s.inr
adius
参数：s : Affine.Simplex ℝ P n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma insphere_radius : s.insphere.radius = s.inradius :=
  rfl
/-
**Affine.Simplex.exsphere_empty** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] (s : Affine.Simplex ℝ P n), s.exsphere ∅ = s.insphere
参数：s : Affine.Simplex ℝ P n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma exsphere_empty : s.exsphere ∅ = s.insphere :=
  rfl
/-
**Affine.Simplex.excenter_empty** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] (s : Affine.Simplex ℝ P n), s.excenter ∅ = s.incenter
参数：s : Affine.Simplex ℝ P n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma excenter_empty : s.excenter ∅ = s.incenter :=
  rfl
/-
**Affine.Simplex.exradius_empty** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] (s : Affine.Simplex ℝ P n), s.exradius ∅ = s.inradius
参数：s : Affine.Simplex ℝ P n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma exradius_empty : s.exradius ∅ = s.inradius :=
  rfl
/-
**Affine.Simplex.exsphere_compl** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] (s : Affine.Simplex ℝ P n) (signs : Finset (Fin (n + 
1))),   s.exsphere signsᶜ = s.exsphere signs
参数：s : Affine.Simplex ℝ P n；signs : Finset (Fin (n + 1))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.excenterWeights_compl`：∀ {V : Type u_1} {P : Type u_2} [i
nst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpa
ce P]   [inst_3 : NormedAd…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Affine.Simplex.excenterWeightsUnnorm_compl`：∀ {V : Type u_1} {P : Type u
_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Met
ricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
· 使用引理 `inv_neg`：inv_neg : (-a)⁻¹ = -a⁻¹
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
· 使用定理 `abs_inv`：abs_inv (a : α) : |a⁻¹| = |a|⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma exsphere_compl (signs : Finset (Fin (n + 1))) :
    s.exsphere signsᶜ = s.exsphere signs := by
  simp [exsphere, excenterWeights_compl, excenterWeightsUnnorm_compl, Pi.neg_apply]
/-
**Affine.Simplex.excenter_compl** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] (s : Affine.Simplex ℝ P n) (signs : Finset (Fin (n + 
1))),   s.excenter signsᶜ = s.excenter signs
参数：s : Affine.Simplex ℝ P n；signs : Finset (Fin (n + 1))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.exsphere_compl`：∀ {V : Type u_1} {P : Type u_2} [inst : N
ormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]  
 [inst_3 : NormedAd…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma excenter_compl (signs : Finset (Fin (n + 1))) :
    s.excenter signsᶜ = s.excenter signs := by
  simp_rw [excenter, exsphere_compl]
/-
**Affine.Simplex.exradius_compl** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] (s : Affine.Simplex ℝ P n) (signs : Finset (Fin (n + 
1))),   s.exradius signsᶜ = s.exradius signs
参数：s : Affine.Simplex ℝ P n；signs : Finset (Fin (n + 1))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.exsphere_compl`：∀ {V : Type u_1} {P : Type u_2} [inst : N
ormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]  
 [inst_3 : NormedAd…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma exradius_compl (signs : Finset (Fin (n + 1))) :
    s.exradius signsᶜ = s.exradius signs := by
  simp_rw [exradius, exsphere_compl]
/-
**Affine.Simplex.exsphere_univ** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] (s : Affine.Simplex ℝ P n),   s.exsphere Finset.univ 
= s.insphere
参数：s : Affine.Simplex ℝ P n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.compl_empty`：compl_empty : (∅ : Finset α)ᶜ = univ
· 使用定理 `Affine.Simplex.exsphere_compl`：∀ {V : Type u_1} {P : Type u_2} [inst : N
ormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]  
 [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.insphere.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
-/
@[simp] lemma exsphere_univ : s.exsphere Finset.univ = s.insphere := by
  rw [← Finset.compl_empty, exsphere_compl, insphere]
/-
**Affine.Simplex.excenter_univ** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] (s : Affine.Simplex ℝ P n),   s.excenter Finset.univ 
= s.incenter
参数：s : Affine.Simplex ℝ P n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.excenter.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.exsphere_univ`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.insphere_center`：∀ {V : Type u_1} {P : Type u_2} [inst : 
NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] 
  [inst_3 : NormedAd…
-/
@[simp] lemma excenter_univ : s.excenter Finset.univ = s.incenter := by
  rw [excenter, exsphere_univ, insphere_center]
/-
**Affine.Simplex.exradius_univ** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] (s : Affine.Simplex ℝ P n),   s.exradius Finset.univ 
= s.inradius
参数：s : Affine.Simplex ℝ P n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.exradius.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.exsphere_univ`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.insphere_radius`：∀ {V : Type u_1} {P : Type u_2} [inst : 
NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] 
  [inst_3 : NormedAd…
-/
@[simp] lemma exradius_univ : s.exradius Finset.univ = s.inradius := by
  rw [exradius, exsphere_univ, insphere_radius]
/-
**Affine.Simplex.excenter_eq_affineCombination** 是 Mathlib 中的一个引理，位于命名空间 `Affine
.Simplex`。
形式化陈述：excenter_eq_affineCombination (signs : Finset (Fin (n + 1))) : s.excenter 
signs = Finset.univ.affineCombination Real s.points (s.excenterWeights signs)
参数：signs : Finset (Fin (n + 1))。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma excenter_eq_affineCombination (signs : Finset (Fin (n + 1))) :
    s.excenter signs = Finset.univ.affineCombination ℝ s.points (s.excenterWeights signs) :=
  rfl
/-
**Affine.Simplex.exradius_eq_abs_inv_sum** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simpl
ex`。
形式化陈述：exradius_eq_abs_inv_sum (signs : Finset (Fin (n + 1))) : s.exradius signs 
= |(∑ i, s.excenterWeightsUnnorm signs i)⁻¹|
参数：signs : Finset (Fin (n + 1))。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exradius_eq_abs_inv_sum (signs : Finset (Fin (n + 1))) :
    s.exradius signs = |(∑ i, s.excenterWeightsUnnorm signs i)⁻¹| :=
  rfl
/-
**Affine.Simplex.incenter_eq_affineCombination** 是 Mathlib 中的一个引理，位于命名空间 `Affine
.Simplex`。
形式化陈述：incenter_eq_affineCombination : s.incenter = Finset.univ.affineCombination
 Real s.points (s.excenterWeights ∅)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma incenter_eq_affineCombination :
    s.incenter = Finset.univ.affineCombination ℝ s.points (s.excenterWeights ∅) :=
  rfl
/-
**Affine.Simplex.inradius_eq_abs_inv_sum** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simpl
ex`。
形式化陈述：inradius_eq_abs_inv_sum : s.inradius = |(∑ i, s.excenterWeightsUnnorm ∅ i)
⁻¹|
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inradius_eq_abs_inv_sum : s.inradius = |(∑ i, s.excenterWeightsUnnorm ∅ i)⁻¹| :=
  rfl
/-
**Affine.Simplex.exradius_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simplex`。
形式化陈述：exradius_nonneg (signs : Finset (Fin (n + 1))) : 0 <= s.exradius signs
参数：signs : Finset (Fin (n + 1))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
lemma exradius_nonneg (signs : Finset (Fin (n + 1))) : 0 ≤ s.exradius signs :=
  abs_nonneg _

variable {s} in
/-
**Affine.Simplex.ExcenterExists.exradius_pos** 是 Mathlib 中的一个定理，位于命名空间 `Affine.S
implex.ExcenterExists`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] {s : Affine.Simplex ℝ P n} {signs : Finset (Fin (n + 
1))},   s.ExcenterExists signs → 0 < s.exradius signs
参数：Fin (n + 1)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_pos`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [
AddLeftMono α] {a : α}, 0 < |a| ↔ a ≠ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
-/
lemma ExcenterExists.exradius_pos {signs : Finset (Fin (n + 1))} (h : s.ExcenterExists signs) :
    0 < s.exradius signs :=
  abs_pos.2 (inv_ne_zero h)
/-
**Affine.Simplex.inradius_pos** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simplex`。
形式化陈述：inradius_pos : 0 < s.inradius
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.ExcenterExists.exradius_pos`：∀ {V : Type u_1} {P : Type u
_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Met
ricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.excenterExists_empty`：∀ {V : Type u_1} {P : Type u_2} [in
st : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpac
e P]   [inst_3 : NormedAd…
-/
lemma inradius_pos : 0 < s.inradius :=
  s.excenterExists_empty.exradius_pos
/-
**Affine.Simplex.exradius_singleton_pos** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simple
x`。
形式化陈述：exradius_singleton_pos [Nat.AtLeastTwo n] (i : Fin (n + 1)) : 0 < s.exradi
us {i}
参数：i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.ExcenterExists.exradius_pos`：∀ {V : Type u_1} {P : Type u
_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Met
ricSpace P]   [inst_3 : NormedAd…
· 使用引理 `Affine.Simplex.excenterExists_singleton`：excenterExists_singleton [Nat.A
tLeastTwo n] (i : Fin (n + 1)) : s.ExcenterExists {i}
-/
lemma exradius_singleton_pos [Nat.AtLeastTwo n] (i : Fin (n + 1)) : 0 < s.exradius {i} :=
  (s.excenterExists_singleton i).exradius_pos

variable {s} in
/-
**Affine.Simplex.ExcenterExists.excenter_mem_affineSpan_range** 是 Mathlib 中的一个定理
，位于命名空间 `Affine.Simplex.ExcenterExists`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] {s : Affine.Simplex ℝ P n} {signs : Finset (Fin (n + 
1))},   s.ExcenterExists signs → s.excenter signs ∈ affineSpan ℝ (Set.range s.po
ints)
参数：Fin (n + 1)；Set.range s.points。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `affineCombination_mem_affineSpan`：affineCombination_mem_affineSpan [Nont
rivial k] {s : Finset ι} {w : ι -> k} (h : ∑ i in s, w i = 1) (p : ι -> P) : s.a
ffineCombination k p w…
· 使用定理 `Affine.Simplex.ExcenterExists.sum_excenterWeights_eq_one`：∀ {V : Type u_
1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V]
 [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
-/
lemma ExcenterExists.excenter_mem_affineSpan_range {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) : s.excenter signs ∈ affineSpan ℝ (Set.range s.points) :=
  affineCombination_mem_affineSpan h.sum_excenterWeights_eq_one _
/-
**Affine.Simplex.incenter_mem_affineSpan_range** 是 Mathlib 中的一个引理，位于命名空间 `Affine
.Simplex`。
形式化陈述：incenter_mem_affineSpan_range : s.incenter in affineSpan Real (Set.range s
.points)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.ExcenterExists.excenter_mem_affineSpan_range`：∀ {V : Type
 u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ
 V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.excenterExists_empty`：∀ {V : Type u_1} {P : Type u_2} [in
st : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpac
e P]   [inst_3 : NormedAd…
-/
lemma incenter_mem_affineSpan_range : s.incenter ∈ affineSpan ℝ (Set.range s.points) :=
  s.excenterExists_empty.excenter_mem_affineSpan_range
/-
**Affine.Simplex.incenter_mem_interior** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simplex
`。
形式化陈述：incenter_mem_interior : s.incenter in s.interior
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.ExcenterExists.sum_excenterWeights_eq_one`：∀ {V : Type u_
1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V]
 [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.excenterExists_empty`：∀ {V : Type u_1} {P : Type u_2} [in
st : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpac
e P]   [inst_3 : NormedAd…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Affine.Simplex.incenter_eq_affineCombination`：incenter_eq_affineCombinat
ion : s.incenter = Finset.univ.affineCombination Real s.points (s.excenterWeight
s ∅)
· 使用引理 `Affine.Simplex.affineCombination_mem_interior_iff`：affineCombination_mem
_interior_iff {n : Nat} {s : Simplex k P n} {w : Fin (n + 1) -> k} (hw : ∑ i, w 
i = 1) : Finset.univ.affineCombination …
· 使用引理 `Affine.Simplex.excenterWeights_empty_pos`：excenterWeights_empty_pos (i :
 Fin (n + 1)) : 0 < s.excenterWeights ∅ i
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `lt_imp_lt_of_le_of_le`：lt_imp_lt_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a < b -> c < d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `lt_add_iff_pos_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 :
 LT α] [AddLeftStrictMono α] [AddLeftReflectLT α] (a : α) {b : α},   a < a + b ↔
 0 < b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `add_pos_of_pos_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst
_1 : Preorder α] [AddLeftMono α] {a b : α}, 0 < a → 0 ≤ b → 0 < a + b
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Finset.sum_pair`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid M
] {f : ι → M} [inst_1 : DecidableEq ι] {a b : ι},   a ≠ b → ∑ x ∈ {a, b}, f x = 
f a +…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_add_sum_compl`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCom
mMonoid M] [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (s : Finset ι)   (f : ι
 → M), ∑ i ∈ s…
-/
lemma incenter_mem_interior : s.incenter ∈ s.interior := by
  have h := s.excenterExists_empty.sum_excenterWeights_eq_one
  rw [incenter_eq_affineCombination, s.affineCombination_mem_interior_iff h]
  intro i
  refine ⟨s.excenterWeights_empty_pos i, ?_⟩
  by_contra! hp
  obtain ⟨j, hj⟩ := exists_ne i
  rw [← Finset.sum_add_sum_compl {j, i}, Finset.sum_pair hj] at h
  revert h
  apply ne_of_gt
  nth_rw 2 [add_comm]
  grw [hp]
  rw [add_assoc, lt_add_iff_pos_right]
  exact add_pos_of_pos_of_nonneg (s.excenterWeights_empty_pos j)
    (Finset.sum_nonneg fun k _ ↦ (s.excenterWeights_empty_pos k).le)
/-
**Affine.Simplex.excenter_singleton_mem_affineSpan_range** 是 Mathlib 中的一个引理，位于命名
空间 `Affine.Simplex`。
形式化陈述：excenter_singleton_mem_affineSpan_range [Nat.AtLeastTwo n] (i : Fin (n + 1
)) : s.excenter {i} in affineSpan Real (Set.range s.points)
参数：i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.ExcenterExists.excenter_mem_affineSpan_range`：∀ {V : Type
 u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ
 V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用引理 `Affine.Simplex.excenterExists_singleton`：excenterExists_singleton [Nat.A
tLeastTwo n] (i : Fin (n + 1)) : s.ExcenterExists {i}
-/
lemma excenter_singleton_mem_affineSpan_range [Nat.AtLeastTwo n] (i : Fin (n + 1)) :
    s.excenter {i} ∈ affineSpan ℝ (Set.range s.points) :=
  (s.excenterExists_singleton i).excenter_mem_affineSpan_range

variable {s} in
/-
**Affine.Simplex.ExcenterExists.signedInfDist_excenter_eq_mul_sum_inv** 是 Mathli
b 中的一个定理，位于命名空间 `Affine.Simplex.ExcenterExists`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] {s : Affine.Simplex ℝ P n} {signs : Finset (Fin (n + 
1))},   s.ExcenterExists signs →     ∀ (i : Fin (n + 1)),       (s.signedInfDist
 i) (s.excenter signs) = (if i ∈ signs then -1 else 1) * (∑ j, s.excenterWeights
Unnorm signs j)⁻¹
参数：Fin (n + 1)；i : Fin (n + 1)；s.signedInfDist i；s.excenter signs；if i ∈ signs t
hen -1 else 1；∑ j, s.excenterWeightsUnnorm signs j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Affine.Simplex.signedInfDist_affineCombination`：signedInfDist_affineComb
ination {w : Fin (n + 1) -> Real} (h : ∑ i, w i = 1) : s.signedInfDist i (Finset
.univ.affineCombination Real s.point…
· 使用定理 `Affine.Simplex.ExcenterExists.sum_excenterWeights_eq_one`：∀ {V : Type u_
1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V]
 [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Affine.Simplex.altitudeFoot.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst 
: NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P
]   [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.height.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : Norm
edAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [i
nst_3 : NormedAd…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `inv_mul_cancel_right₀`：inv_mul_cancel_right₀ (h : b != 0) (a : G₀) : a *
 b⁻¹ * b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `Affine.Simplex.height_pos`：height_pos {n : Nat} [NeZero n] (s : Simplex 
Real P n) (i : Fin (n + 1)) : 0 < s.height i
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ExcenterExists.signedInfDist_excenter_eq_mul_sum_inv {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) (i : Fin (n + 1)) :
    s.signedInfDist i (s.excenter signs) =
      (if i ∈ signs then -1 else 1) * (∑ j, s.excenterWeightsUnnorm signs j)⁻¹ := by
  simp_rw [excenter_eq_affineCombination,
    signedInfDist_affineCombination _ _ h.sum_excenterWeights_eq_one, excenterWeights,
    Pi.smul_apply, ← dist_eq_norm_vsub, excenterWeightsUnnorm]
  rw [← altitudeFoot, ← height]
  simp [(s.height_pos i).ne']

variable {s} in
/-
**Affine.Simplex.ExcenterExists.sign_signedInfDist_excenter** 是 Mathlib 中的一个定理，位
于命名空间 `Affine.Simplex.ExcenterExists`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] {s : Affine.Simplex ℝ P n} {signs : Finset (Fin (n + 
1))},   s.ExcenterExists signs →     ∀ (i : Fin (n + 1)),       SignType.sign ((
s.signedInfDist i) (s.excenter signs)) = SignType.sign (s.excenterWeights signs 
i)
参数：Fin (n + 1)；i : Fin (n + 1)；(s.signedInfDist i) (s.excenter signs)；s.excenter
Weights signs i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Affine.Simplex.excenter_eq_affineCombination`：excenter_eq_affineCombinat
ion (signs : Finset (Fin (n + 1))) : s.excenter signs = Finset.univ.affineCombin
ation Real s.points (s.excenterWei…
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Affine.Simplex.signedInfDist_affineCombination`：signedInfDist_affineComb
ination {w : Fin (n + 1) -> Real} (h : ∑ i, w i = 1) : s.signedInfDist i (Finset
.univ.affineCombination Real s.point…
· 使用定理 `Affine.Simplex.ExcenterExists.sum_excenterWeights_eq_one`：∀ {V : Type u_
1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V]
 [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `sign_mul`：sign_mul (x y : α) : sign (x * y) = sign x * sign y
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sign_eq_one_iff`：sign_eq_one_iff : sign a = 1 ↔ 0 < a
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用引理 `Affine.Simplex.height_pos`：height_pos {n : Nat} [NeZero n] (s : Simplex 
Real P n) (i : Fin (n + 1)) : 0 < s.height i
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma ExcenterExists.sign_signedInfDist_excenter {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) (i : Fin (n + 1)) :
    SignType.sign (s.signedInfDist i (s.excenter signs)) =
      SignType.sign (s.excenterWeights signs i) := by
  rw [excenter_eq_affineCombination,
    signedInfDist_affineCombination _ _ h.sum_excenterWeights_eq_one, sign_mul]
  convert! mul_one _
  rw [sign_eq_one_iff, ← dist_eq_norm_vsub]
  exact s.height_pos _
/-
**Affine.Simplex.sign_signedInfDist_incenter** 是 Mathlib 中的一个引理，位于命名空间 `Affine.S
implex`。
形式化陈述：sign_signedInfDist_incenter (i : Fin (n + 1)) : SignType.sign (s.signedInf
Dist i s.incenter) = 1
参数：i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Affine.Simplex.sign_excenterWeights_empty`：sign_excenterWeights_empty (i
 : Fin (n + 1)) : SignType.sign (s.excenterWeights ∅ i) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Affine.Simplex.ExcenterExists.sign_signedInfDist_excenter`：∀ {V : Type u
_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V
] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.excenterExists_empty`：∀ {V : Type u_1} {P : Type u_2} [in
st : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpac
e P]   [inst_3 : NormedAd…
-/
lemma sign_signedInfDist_incenter (i : Fin (n + 1)) :
    SignType.sign (s.signedInfDist i s.incenter) = 1 := by
  convert! s.excenterExists_empty.sign_signedInfDist_excenter i
  simp

variable {s} in
/-
**Affine.Simplex.ExcenterExists.affineCombination_eq_excenter_iff** 是 Mathlib 中的
一个定理，位于命名空间 `Affine.Simplex.ExcenterExists`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] {s : Affine.Simplex ℝ P n} {signs : Finset (Fin (n + 
1))},   s.ExcenterExists signs →     ∀ {w : Fin (n + 1) → ℝ},       ∑ j, w j = 1
 →         ((Finset.affineCombination ℝ Finset.univ s.points) w = s.excenter sig
ns ↔ w = s.excenterWeights signs)
参数：Fin (n + 1)；n + 1；(Finset.affineCombination ℝ Finset.univ s.points) w = s.exc
enter signs ↔ w = s.excenterWeights signs。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `affineIndependent_iff_eq_of_fintype_affineCombination_eq`：affineIndepend
ent_iff_eq_of_fintype_affineCombination_eq [Fintype ι] (p : ι -> P) : AffineInde
pendent k p ↔ forall w1 w2 : ι -> k, ∑ i, w1 i…
· 使用定理 `Affine.Simplex.independent`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [ins
t_3 : AddTorsor …
· 使用定理 `Affine.Simplex.ExcenterExists.sum_excenterWeights_eq_one`：∀ {V : Type u_
1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V]
 [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.excenter.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.exsphere.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma ExcenterExists.affineCombination_eq_excenter_iff {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) {w : Fin (n + 1) → ℝ} (hw : ∑ j, w j = 1) :
    Finset.univ.affineCombination ℝ s.points w = s.excenter signs ↔
      w = s.excenterWeights signs := by
  constructor
  · simp_rw [excenter, exsphere]
    exact fun he ↦ (affineIndependent_iff_eq_of_fintype_affineCombination_eq ℝ s.points).1
      s.independent _ _ hw h.sum_excenterWeights_eq_one he
  · rintro rfl
    rw [excenter, exsphere]

variable {s} in
/-
**Affine.Simplex.ExcenterExists.excenter_notMem_affineSpan_face** 是 Mathlib 中的一个
定理，位于命名空间 `Affine.Simplex.ExcenterExists`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] {s : Affine.Simplex ℝ P n} {signs : Finset (Fin (n + 
1))},   s.ExcenterExists signs →     ∀ {fs : Finset (Fin (n + 1))} {m : ℕ} (hfs 
: fs.card = m + 1),       m ≠ n → s.excenter signs ∉ affineSpan ℝ (Set.range (s.
face hfs).points)
参数：Fin (n + 1)；Fin (n + 1)；hfs : fs.card = m + 1；Set.range (s.face hfs).points。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
· 使用定理 `Finset.exists_mem_notMem_of_card_lt_card`：exists_mem_notMem_of_card_lt_c
ard (h : #s < #t) : exists e, e in t ∧ e ∉ s
· 使用定理 `Affine.Simplex.ExcenterExists.excenterWeights_ne_zero`：∀ {V : Type u_1} 
{P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [i
nst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用引理 `AffineIndependent.eq_zero_of_affineCombination_mem_affineSpan`：AffineInd
ependent.eq_zero_of_affineCombination_mem_affineSpan {p : ι -> P} (ha : AffineIn
dependent k p) {fs : Finset ι} {w : ι -> k} (hw : ∑…
· 使用定理 `Affine.Simplex.independent`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [ins
t_3 : AddTorsor …
· 使用定理 `Affine.Simplex.ExcenterExists.sum_excenterWeights_eq_one`：∀ {V : Type u_
1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V]
 [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用引理 `Affine.Simplex.excenter_eq_affineCombination`：excenter_eq_affineCombinat
ion (signs : Finset (Fin (n + 1))) : s.excenter signs = Finset.univ.affineCombin
ation Real s.points (s.excenterWei…
· 使用定理 `Affine.Simplex.range_face_points`：range_face_points {n : Nat} (s : Simpl
ex k P n) {fs : Finset (Fin (n + 1))} {m : Nat} (h : #fs = m + 1) : Set.range (s
.face h).points = s.po…
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
-/
lemma ExcenterExists.excenter_notMem_affineSpan_face {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) {fs : Finset (Fin (n + 1))} {m : ℕ} (hfs : #fs = m + 1)
    (hne : m ≠ n) : s.excenter signs ∉ affineSpan ℝ (Set.range (s.face hfs).points) := by
  intro hm
  rw [range_face_points] at hm
  obtain ⟨i, hi⟩ : ∃ i, i ∉ (fs : Set (Fin (n + 1))) := by
    simp only [SetLike.mem_coe]
    have hc : #fs < #(Finset.univ : Finset (Fin (n + 1))) := by
      have : m + 1 ≤ #fs := hfs.ge
      grw [fs.subset_univ] at this
      simp only [Finset.card_univ, Fintype.card_fin] at *
      lia
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
    exact ⟨i, hi⟩
  rw [excenter_eq_affineCombination] at hm
  exact h.excenterWeights_ne_zero i (s.independent.eq_zero_of_affineCombination_mem_affineSpan
    h.sum_excenterWeights_eq_one hm (Finset.mem_univ i) hi)
/-
**Affine.Simplex.incenter_notMem_affineSpan_face** 是 Mathlib 中的一个引理，位于命名空间 `Affi
ne.Simplex`。
形式化陈述：incenter_notMem_affineSpan_face {fs : Finset (Fin (n + 1))} {m : Nat} (hfs
 : #fs = m + 1) (hne : m != n) : s.incenter ∉ affineSpan Real (Set.range (s.face
 hfs).points)
参数：Fin (n + 1)；hfs : #fs = m + 1；hne : m != n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.ExcenterExists.excenter_notMem_affineSpan_face`：∀ {V : Ty
pe u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace
 ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.excenterExists_empty`：∀ {V : Type u_1} {P : Type u_2} [in
st : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpac
e P]   [inst_3 : NormedAd…
-/
lemma incenter_notMem_affineSpan_face {fs : Finset (Fin (n + 1))} {m : ℕ} (hfs : #fs = m + 1)
    (hne : m ≠ n) : s.incenter ∉ affineSpan ℝ (Set.range (s.face hfs).points) :=
  s.excenterExists_empty.excenter_notMem_affineSpan_face hfs hne

variable {s} in
/-
**Affine.Simplex.ExcenterExists.excenter_notMem_affineSpan_faceOpposite** 是 Math
lib 中的一个定理，位于命名空间 `Affine.Simplex.ExcenterExists`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] {s : Affine.Simplex ℝ P n} {signs : Finset (Fin (n + 
1))},   s.ExcenterExists signs → ∀ (i : Fin (n + 1)), s.excenter signs ∉ affineS
pan ℝ (Set.range (s.faceOpposite i).points)
参数：Fin (n + 1)；i : Fin (n + 1)；Set.range (s.faceOpposite i).points。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.ExcenterExists.excenter_notMem_affineSpan_face`：∀ {V : Ty
pe u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace
 ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
-/
lemma ExcenterExists.excenter_notMem_affineSpan_faceOpposite {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) (i : Fin (n + 1)) :
    s.excenter signs ∉ affineSpan ℝ (Set.range (s.faceOpposite i).points) :=
  h.excenter_notMem_affineSpan_face _ (by have := NeZero.ne n; lia)
/-
**Affine.Simplex.incenter_notMem_affineSpan_faceOpposite** 是 Mathlib 中的一个引理，位于命名
空间 `Affine.Simplex`。
形式化陈述：incenter_notMem_affineSpan_faceOpposite (i : Fin (n + 1)) : s.incenter ∉ a
ffineSpan Real (Set.range (s.faceOpposite i).points)
参数：i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.ExcenterExists.excenter_notMem_affineSpan_faceOpposite`：∀
 {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProd
uctSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.excenterExists_empty`：∀ {V : Type u_1} {P : Type u_2} [in
st : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpac
e P]   [inst_3 : NormedAd…
-/
lemma incenter_notMem_affineSpan_faceOpposite (i : Fin (n + 1)) :
    s.incenter ∉ affineSpan ℝ (Set.range (s.faceOpposite i).points) :=
  s.excenterExists_empty.excenter_notMem_affineSpan_faceOpposite i

variable {s} in
/-
**Affine.Simplex.ExcenterExists.excenter_ne_point** 是 Mathlib 中的一个定理，位于命名空间 `Aff
ine.Simplex.ExcenterExists`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] {s : Affine.Simplex ℝ P n} {signs : Finset (Fin (n + 
1))},   s.ExcenterExists signs → ∀ (i : Fin (n + 1)), s.excenter signs ≠ s.point
s i
参数：Fin (n + 1)；i : Fin (n + 1)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Affine.Simplex.ExcenterExists.excenter_notMem_affineSpan_face`：∀ {V : Ty
pe u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace
 ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `NeZero.ne'`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], 0 ≠
 n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Affine.Simplex.face_eq_mkOfPoint`：face_eq_mkOfPoint {n : Nat} (s : Simpl
ex k P n) (i : Fin (n + 1)) : s.face (Finset.card_singleton i) = mkOfPoint k (s.
points i)
· 使用定理 `Affine.Simplex.range_mkOfPoint_points`：∀ (k : Type u_1) {V : Type u_2} {
P : Type u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module 
k V]   [inst_3 : AddTorsor …
-/
lemma ExcenterExists.excenter_ne_point {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) (i : Fin (n + 1)) : s.excenter signs ≠ s.points i := by
  have hf := h.excenter_notMem_affineSpan_face (fs := {i}) (m := 0) (by simp) (NeZero.ne' _)
  simpa using hf
/-
**Affine.Simplex.incenter_ne_point** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simplex`。
形式化陈述：incenter_ne_point (i : Fin (n + 1)) : s.incenter != s.points i
参数：i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.ExcenterExists.excenter_ne_point`：∀ {V : Type u_1} {P : T
ype u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 
: MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.excenterExists_empty`：∀ {V : Type u_1} {P : Type u_2} [in
st : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpac
e P]   [inst_3 : NormedAd…
-/
lemma incenter_ne_point (i : Fin (n + 1)) :
    s.incenter ≠ s.points i :=
  s.excenterExists_empty.excenter_ne_point i

variable {s} in
/-
**Affine.Simplex.ExcenterExists.excenter_notMem_affineSpan_pair** 是 Mathlib 中的一个
定理，位于命名空间 `Affine.Simplex.ExcenterExists`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] {s : Affine.Simplex ℝ P n} [n.AtLeastTwo]   {signs : 
Finset (Fin (n + 1))},   s.ExcenterExists signs → ∀ (i j : Fin (n + 1)), s.excen
ter signs ∉ line[ℝ, s.points i, s.points j]
参数：Fin (n + 1)；i j : Fin (n + 1)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Affine.Simplex.ExcenterExists.excenter_ne_point`：∀ {V : Type u_1} {P : T
ype u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 
: MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Finset.card_insert_of_notMem`：card_insert_of_notMem (h : a ∉ s) : #(inse
rt a s) = #s + 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Affine.Simplex.range_face_points`：range_face_points {n : Nat} (s : Simpl
ex k P n) {fs : Finset (Fin (n + 1))} {m : Nat} (h : #fs = m + 1) : Set.range (s
.face h).points = s.po…
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Set.image_insert_eq`：image_insert_eq {f : α -> β} {a : α} {s : Set α} : 
f '' insert a s = insert (f a) (f '' s)
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Affine.Simplex.ExcenterExists.excenter_notMem_affineSpan_face`：∀ {V : Ty
pe u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace
 ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `Nat.AtLeastTwo.ne_one`：ne_one : n != 1
-/
lemma ExcenterExists.excenter_notMem_affineSpan_pair [Nat.AtLeastTwo n]
    {signs : Finset (Fin (n + 1))} (h : s.ExcenterExists signs) (i j : Fin (n + 1)) :
    s.excenter signs ∉ line[ℝ, s.points i, s.points j] := by
  by_cases hij : i = j
  · simp only [hij, Set.mem_singleton_iff, Set.insert_eq_of_mem,
      AffineSubspace.mem_affineSpan_singleton]
    exact h.excenter_ne_point j
  · convert!
    h.excenter_notMem_affineSpan_face (fs := { i, j }) (m := 1) (by simp_all)
      Nat.AtLeastTwo.ne_one.symm
    simp [Set.image_insert_eq]
/-
**Affine.Simplex.incenter_notMem_affineSpan_pair** 是 Mathlib 中的一个引理，位于命名空间 `Affi
ne.Simplex`。
形式化陈述：incenter_notMem_affineSpan_pair [Nat.AtLeastTwo n] (i j : Fin (n + 1)) : s
.incenter ∉ line[Real, s.points i, s.points j]
参数：i j : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.ExcenterExists.excenter_notMem_affineSpan_pair`：∀ {V : Ty
pe u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace
 ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.excenterExists_empty`：∀ {V : Type u_1} {P : Type u_2} [in
st : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpac
e P]   [inst_3 : NormedAd…
-/
lemma incenter_notMem_affineSpan_pair [Nat.AtLeastTwo n] (i j : Fin (n + 1)) :
    s.incenter ∉ line[ℝ, s.points i, s.points j] :=
  s.excenterExists_empty.excenter_notMem_affineSpan_pair i j

variable {s} in
/-
**Affine.Simplex.ExcenterExists.excenterWeights_eq_excenterWeights_iff** 是 Mathl
ib 中的一个定理，位于命名空间 `Affine.Simplex.ExcenterExists`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] {s : Affine.Simplex ℝ P n}   {signs₁ signs₂ : Finset 
(Fin (n + 1))},   s.ExcenterExists signs₁ →     s.ExcenterExists signs₂ → (s.exc
enterWeights signs₁ = s.excenterWeights signs₂ ↔ signs₁ = signs₂ ∨ signs₁ = sign
s₂ᶜ)
参数：Fin (n + 1)；s.excenterWeights signs₁ = s.excenterWeights signs₂ ↔ signs₁ = si
gns₂ ∨ signs₁ = signs₂ᶜ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `sign_eq_sign_or_eq_neg`：sign_eq_sign_or_eq_neg {b : α} (ha : a != 0) (hb
 : b != 0) : sign a = sign b ∨ sign a = -sign b
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sign_mul`：sign_mul (x y : α) : sign (x * y) = sign x * sign y
· 使用定理 `sign_pos`：sign_pos (ha : 0 < a) : sign a = 1
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `GCDMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : CommMonoidWithZero
 α} [self : GCDMonoid α], IsCancelMulZero α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `sign_neg`：sign_neg (ha : a < 0) : sign a = -1
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
（共 39 条，此处仅展示前 30 条）
-/
lemma ExcenterExists.excenterWeights_eq_excenterWeights_iff {signs₁ signs₂ : Finset (Fin (n + 1))}
    (h₁ : s.ExcenterExists signs₁) (h₂ : s.ExcenterExists signs₂) :
    s.excenterWeights signs₁ = s.excenterWeights signs₂ ↔ signs₁ = signs₂ ∨ signs₁ = signs₂ᶜ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hi : ∀ i, SignType.sign (s.excenterWeights signs₁ i) =
        SignType.sign (s.excenterWeights signs₂ i) := by
      simp [h]
    simp_rw [excenterWeights, Pi.smul_apply, smul_eq_mul, sign_mul] at hi
    have hn₁ : ∑ i, s.excenterWeightsUnnorm signs₁ i ≠ 0 := h₁
    have hn₂ : ∑ i, s.excenterWeightsUnnorm signs₂ i ≠ 0 := h₂
    rcases sign_eq_sign_or_eq_neg (inv_ne_zero hn₁) (inv_ne_zero hn₂) with hs | hs
    · simp only [hs, mul_eq_mul_left_iff, sign_eq_zero_iff, inv_eq_zero, hn₂, or_false] at hi
      simp only [excenterWeightsUnnorm, sign_mul, inv_pos, height_pos, sign_pos, mul_one] at hi
      left
      ext i
      replace hi := hi i
      split_ifs at hi <;> simp_all
    · simp_rw [hs, neg_mul, ← mul_neg, mul_eq_mul_left_iff] at hi
      simp only [sign_eq_zero_iff, inv_eq_zero, hn₂, or_false] at hi
      simp only [excenterWeightsUnnorm, sign_mul, inv_pos, height_pos, sign_pos, mul_one] at hi
      right
      ext i
      replace hi := hi i
      split_ifs at hi <;> simp_all
  · rcases h with rfl | rfl
    · rfl
    · simp

variable {s} in
/-
**Affine.Simplex.ExcenterExists.excenter_eq_excenter_iff** 是 Mathlib 中的一个定理，位于命名
空间 `Affine.Simplex.ExcenterExists`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] {s : Affine.Simplex ℝ P n}   {signs₁ signs₂ : Finset 
(Fin (n + 1))},   s.ExcenterExists signs₁ →     s.ExcenterExists signs₂ → (s.exc
enter signs₁ = s.excenter signs₂ ↔ signs₁ = signs₂ ∨ signs₁ = signs₂ᶜ)
参数：Fin (n + 1)；s.excenter signs₁ = s.excenter signs₂ ↔ signs₁ = signs₂ ∨ signs₁ 
= signs₂ᶜ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Affine.Simplex.excenter_eq_affineCombination`：excenter_eq_affineCombinat
ion (signs : Finset (Fin (n + 1))) : s.excenter signs = Finset.univ.affineCombin
ation Real s.points (s.excenterWei…
· 使用定理 `Affine.Simplex.ExcenterExists.affineCombination_eq_excenter_iff`：∀ {V : 
Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpa
ce ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Affine.Simplex.sum_excenterWeights_eq_one_iff`：∀ {V : Type u_1} {P : Typ
e u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : 
MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.ExcenterExists.excenterWeights_eq_excenterWeights_iff`：∀ 
{V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProdu
ctSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
-/
lemma ExcenterExists.excenter_eq_excenter_iff {signs₁ signs₂ : Finset (Fin (n + 1))}
    (h₁ : s.ExcenterExists signs₁) (h₂ : s.ExcenterExists signs₂) :
    s.excenter signs₁ = s.excenter signs₂ ↔ signs₁ = signs₂ ∨ signs₁ = signs₂ᶜ := by
  rw [excenter_eq_affineCombination,
    h₂.affineCombination_eq_excenter_iff (s.sum_excenterWeights_eq_one_iff.2 h₁)]
  exact h₁.excenterWeights_eq_excenterWeights_iff h₂

variable {s} in
/-
**Affine.Simplex.ExcenterExists.excenter_eq_incenter_iff** 是 Mathlib 中的一个定理，位于命名
空间 `Affine.Simplex.ExcenterExists`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] {s : Affine.Simplex ℝ P n} {signs : Finset (Fin (n + 
1))},   s.ExcenterExists signs → (s.excenter signs = s.incenter ↔ signs = ∅ ∨ si
gns = Finset.univ)
参数：Fin (n + 1)；s.excenter signs = s.incenter ↔ signs = ∅ ∨ signs = Finset.univ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.incenter.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Affine.Simplex.excenter.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.ExcenterExists.excenter_eq_excenter_iff`：∀ {V : Type u_1}
 {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [
inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.excenterExists_empty`：∀ {V : Type u_1} {P : Type u_2} [in
st : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpac
e P]   [inst_3 : NormedAd…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.compl_empty`：compl_empty : (∅ : Finset α)ᶜ = univ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma ExcenterExists.excenter_eq_incenter_iff {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) :
    s.excenter signs = s.incenter ↔ signs = ∅ ∨ signs = Finset.univ := by
  rw [incenter, ← excenter, h.excenter_eq_excenter_iff s.excenterExists_empty]
  simp
/-
**Affine.Simplex.excenter_singleton_ne_incenter** 是 Mathlib 中的一个引理，位于命名空间 `Affin
e.Simplex`。
形式化陈述：excenter_singleton_ne_incenter [Nat.AtLeastTwo n] (i : Fin (n + 1)) : s.ex
center {i} != s.incenter
参数：i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Affine.Simplex.ExcenterExists.excenter_eq_incenter_iff`：∀ {V : Type u_1}
 {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [
inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用引理 `Affine.Simplex.excenterExists_singleton`：excenterExists_singleton [Nat.A
tLeastTwo n] (i : Fin (n + 1)) : s.ExcenterExists {i}
-/
lemma excenter_singleton_ne_incenter [Nat.AtLeastTwo n] (i : Fin (n + 1)) :
    s.excenter {i} ≠ s.incenter := by
  intro h
  rw [(s.excenterExists_singleton i).excenter_eq_incenter_iff] at h
  simp at h
/-
**Affine.Simplex.excenter_singleton_injective** 是 Mathlib 中的一个引理，位于命名空间 `Affine.
Simplex`。
形式化陈述：excenter_singleton_injective [Nat.AtLeastTwo n] : Function.Injective fun i
 => s.excenter {i}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.ExcenterExists.excenter_eq_excenter_iff`：∀ {V : Type u_1}
 {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [
inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用引理 `Affine.Simplex.excenterExists_singleton`：excenterExists_singleton [Nat.A
tLeastTwo n] (i : Fin (n + 1)) : s.ExcenterExists {i}
· 使用定理 `Nat.AtLeastTwo.prop`：∀ {n : ℕ} [self : n.AtLeastTwo], 2 ≤ n
· 使用定理 `Fin.exists_ne_and_ne_of_two_lt`：exists_ne_and_ne_of_two_lt (i j : Fin n)
 (h : 2 < n) : exists k, k != i ∧ k != j
· 使用定理 `Finset.ext_iff`：∀ {α : Type u_1} {s₁ s₂ : Finset α}, s₁ = s₂ ↔ ∀ (a : α)
, a ∈ s₁ ↔ a ∈ s₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
-/
lemma excenter_singleton_injective [Nat.AtLeastTwo n] :
    Function.Injective fun i ↦ s.excenter {i} := by
  intro i j hij
  dsimp only at hij
  rw [(s.excenterExists_singleton i).excenter_eq_excenter_iff (s.excenterExists_singleton j)] at hij
  rcases hij with hij | hij
  · simpa using hij
  · have : 2 ≤ n := Nat.AtLeastTwo.prop
    obtain ⟨k, hki, hkj⟩ : ∃ k, k ≠ i ∧ k ≠ j := Fin.exists_ne_and_ne_of_two_lt i j (by lia)
    rw [Finset.ext_iff] at hij
    replace hij := hij k
    simp_all

variable {s} in
/-
**Affine.Simplex.ExcenterExists.sSameSide_excenter_point_iff** 是 Mathlib 中的一个定理，
位于命名空间 `Affine.Simplex.ExcenterExists`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] {s : Affine.Simplex ℝ P n} {signs : Finset (Fin (n + 
1))},   s.ExcenterExists signs →     ∀ {i : Fin (n + 1)},       (affineSpan ℝ (S
et.range (s.faceOpposite i).points)).SSameSide (s.excenter signs) (s.points i) ↔
         0 < s.excenterWeights signs i
参数：Fin (n + 1)；n + 1；affineSpan ℝ (Set.range (s.faceOpposite i).points)；s.excent
er signs；s.points i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Affine.Simplex.excenter_eq_affineCombination`：excenter_eq_affineCombinat
ion (signs : Finset (Fin (n + 1))) : s.excenter signs = Finset.univ.affineCombin
ation Real s.points (s.excenterWei…
· 使用引理 `Affine.Simplex.sSameSide_affineSpan_faceOpposite_point_right_iff`：sSameS
ide_affineSpan_faceOpposite_point_right_iff {w : Fin (n + 1) -> R} (hw : ∑ j, w 
j = 1) {i : Fin (n + 1)} : (affineSpan R (Set.range (s…
· 使用定理 `Affine.Simplex.ExcenterExists.sum_excenterWeights_eq_one`：∀ {V : Type u_
1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V]
 [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma ExcenterExists.sSameSide_excenter_point_iff {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) {i : Fin (n + 1)} :
    (affineSpan ℝ (Set.range (s.faceOpposite i).points)).SSameSide (s.excenter signs) (s.points i) ↔
      0 < s.excenterWeights signs i := by
  rw [excenter_eq_affineCombination,
    s.sSameSide_affineSpan_faceOpposite_point_right_iff h.sum_excenterWeights_eq_one]

variable {s} in
/-
**Affine.Simplex.ExcenterExists.sSameSide_point_excenter_iff** 是 Mathlib 中的一个定理，
位于命名空间 `Affine.Simplex.ExcenterExists`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] {s : Affine.Simplex ℝ P n} {signs : Finset (Fin (n + 
1))},   s.ExcenterExists signs →     ∀ {i : Fin (n + 1)},       (affineSpan ℝ (S
et.range (s.faceOpposite i).points)).SSameSide (s.points i) (s.excenter signs) ↔
         0 < s.excenterWeights signs i
参数：Fin (n + 1)；n + 1；affineSpan ℝ (Set.range (s.faceOpposite i).points)；s.points
 i；s.excenter signs。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Affine.Simplex.excenter_eq_affineCombination`：excenter_eq_affineCombinat
ion (signs : Finset (Fin (n + 1))) : s.excenter signs = Finset.univ.affineCombin
ation Real s.points (s.excenterWei…
· 使用引理 `Affine.Simplex.sSameSide_affineSpan_faceOpposite_point_left_iff`：sSameSi
de_affineSpan_faceOpposite_point_left_iff {w : Fin (n + 1) -> R} (hw : ∑ j, w j 
= 1) {i : Fin (n + 1)} : (affineSpan R (Set.range (s.…
· 使用定理 `Affine.Simplex.ExcenterExists.sum_excenterWeights_eq_one`：∀ {V : Type u_
1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V]
 [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma ExcenterExists.sSameSide_point_excenter_iff {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) {i : Fin (n + 1)} :
    (affineSpan ℝ (Set.range (s.faceOpposite i).points)).SSameSide (s.points i) (s.excenter signs) ↔
      0 < s.excenterWeights signs i := by
  rw [excenter_eq_affineCombination,
    s.sSameSide_affineSpan_faceOpposite_point_left_iff h.sum_excenterWeights_eq_one]

variable {s} in
/-
**Affine.Simplex.ExcenterExists.sOppSide_excenter_point_iff** 是 Mathlib 中的一个定理，位
于命名空间 `Affine.Simplex.ExcenterExists`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] {s : Affine.Simplex ℝ P n} {signs : Finset (Fin (n + 
1))},   s.ExcenterExists signs →     ∀ {i : Fin (n + 1)},       (affineSpan ℝ (S
et.range (s.faceOpposite i).points)).SOppSide (s.excenter signs) (s.points i) ↔ 
        s.excenterWeights signs i < 0
参数：Fin (n + 1)；n + 1；affineSpan ℝ (Set.range (s.faceOpposite i).points)；s.excent
er signs；s.points i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Affine.Simplex.excenter_eq_affineCombination`：excenter_eq_affineCombinat
ion (signs : Finset (Fin (n + 1))) : s.excenter signs = Finset.univ.affineCombin
ation Real s.points (s.excenterWei…
· 使用引理 `Affine.Simplex.sOppSide_affineSpan_faceOpposite_point_right_iff`：sOppSid
e_affineSpan_faceOpposite_point_right_iff {w : Fin (n + 1) -> R} (hw : ∑ j, w j 
= 1) {i : Fin (n + 1)} : (affineSpan R (Set.range (s.…
· 使用定理 `Affine.Simplex.ExcenterExists.sum_excenterWeights_eq_one`：∀ {V : Type u_
1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V]
 [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma ExcenterExists.sOppSide_excenter_point_iff {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) {i : Fin (n + 1)} :
    (affineSpan ℝ (Set.range (s.faceOpposite i).points)).SOppSide (s.excenter signs) (s.points i) ↔
      s.excenterWeights signs i < 0 := by
  rw [excenter_eq_affineCombination,
    s.sOppSide_affineSpan_faceOpposite_point_right_iff h.sum_excenterWeights_eq_one]

variable {s} in
/-
**Affine.Simplex.ExcenterExists.sOppSide_point_excenter_iff** 是 Mathlib 中的一个定理，位
于命名空间 `Affine.Simplex.ExcenterExists`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] {s : Affine.Simplex ℝ P n} {signs : Finset (Fin (n + 
1))},   s.ExcenterExists signs →     ∀ {i : Fin (n + 1)},       (affineSpan ℝ (S
et.range (s.faceOpposite i).points)).SOppSide (s.points i) (s.excenter signs) ↔ 
        s.excenterWeights signs i < 0
参数：Fin (n + 1)；n + 1；affineSpan ℝ (Set.range (s.faceOpposite i).points)；s.points
 i；s.excenter signs。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Affine.Simplex.excenter_eq_affineCombination`：excenter_eq_affineCombinat
ion (signs : Finset (Fin (n + 1))) : s.excenter signs = Finset.univ.affineCombin
ation Real s.points (s.excenterWei…
· 使用引理 `Affine.Simplex.sOppSide_affineSpan_faceOpposite_point_left_iff`：sOppSide
_affineSpan_faceOpposite_point_left_iff {w : Fin (n + 1) -> R} (hw : ∑ j, w j = 
1) {i : Fin (n + 1)} : (affineSpan R (Set.range (s.f…
· 使用定理 `Affine.Simplex.ExcenterExists.sum_excenterWeights_eq_one`：∀ {V : Type u_
1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V]
 [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma ExcenterExists.sOppSide_point_excenter_iff {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) {i : Fin (n + 1)} :
    (affineSpan ℝ (Set.range (s.faceOpposite i).points)).SOppSide (s.points i) (s.excenter signs) ↔
      s.excenterWeights signs i < 0 := by
  rw [excenter_eq_affineCombination,
    s.sOppSide_affineSpan_faceOpposite_point_left_iff h.sum_excenterWeights_eq_one]
/-
**Affine.Simplex.sSameSide_incenter_point** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simp
lex`。
形式化陈述：sSameSide_incenter_point (i : Fin (n + 1)) : (affineSpan Real (Set.range (
s.faceOpposite i).points)).SSameSide s.incenter (s.points i)
参数：i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Affine.Simplex.ExcenterExists.sSameSide_excenter_point_iff`：∀ {V : Type 
u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ 
V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.excenterExists_empty`：∀ {V : Type u_1} {P : Type u_2} [in
st : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpac
e P]   [inst_3 : NormedAd…
· 使用引理 `Affine.Simplex.excenterWeights_empty_pos`：excenterWeights_empty_pos (i :
 Fin (n + 1)) : 0 < s.excenterWeights ∅ i
-/
lemma sSameSide_incenter_point (i : Fin (n + 1)) :
    (affineSpan ℝ (Set.range (s.faceOpposite i).points)).SSameSide s.incenter (s.points i) :=
  s.excenterExists_empty.sSameSide_excenter_point_iff.2 (s.excenterWeights_empty_pos i)
/-
**Affine.Simplex.sSameSide_point_incenter** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simp
lex`。
形式化陈述：sSameSide_point_incenter (i : Fin (n + 1)) : (affineSpan Real (Set.range (
s.faceOpposite i).points)).SSameSide (s.points i) s.incenter
参数：i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Affine.Simplex.ExcenterExists.sSameSide_point_excenter_iff`：∀ {V : Type 
u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ 
V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.excenterExists_empty`：∀ {V : Type u_1} {P : Type u_2} [in
st : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpac
e P]   [inst_3 : NormedAd…
· 使用引理 `Affine.Simplex.excenterWeights_empty_pos`：excenterWeights_empty_pos (i :
 Fin (n + 1)) : 0 < s.excenterWeights ∅ i
-/
lemma sSameSide_point_incenter (i : Fin (n + 1)) :
    (affineSpan ℝ (Set.range (s.faceOpposite i).points)).SSameSide (s.points i) s.incenter :=
  s.excenterExists_empty.sSameSide_point_excenter_iff.2 (s.excenterWeights_empty_pos i)
/-
**Affine.Simplex.sOppSide_excenter_singleton_point** 是 Mathlib 中的一个引理，位于命名空间 `Af
fine.Simplex`。
形式化陈述：sOppSide_excenter_singleton_point [Nat.AtLeastTwo n] (i : Fin (n + 1)) : (
affineSpan Real (Set.range (s.faceOpposite i).points)).SOppSide (s.excenter {i})
 (s.points i)
参数：i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.ExcenterExists.sOppSide_excenter_point_iff`：∀ {V : Type u
_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V
] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用引理 `Affine.Simplex.excenterExists_singleton`：excenterExists_singleton [Nat.A
tLeastTwo n] (i : Fin (n + 1)) : s.ExcenterExists {i}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sign_eq_neg_one_iff`：sign_eq_neg_one_iff : sign a = -1 ↔ a < 0
· 使用引理 `Affine.Simplex.sign_excenterWeights_singleton_neg`：sign_excenterWeights_
singleton_neg [Nat.AtLeastTwo n] (i : Fin (n + 1)) : SignType.sign (s.excenterWe
ights {i} i) = -1
-/
lemma sOppSide_excenter_singleton_point [Nat.AtLeastTwo n] (i : Fin (n + 1)) :
    (affineSpan ℝ (Set.range (s.faceOpposite i).points)).SOppSide (s.excenter {i})
      (s.points i) := by
  rw [(s.excenterExists_singleton i).sOppSide_excenter_point_iff, ← sign_eq_neg_one_iff,
    s.sign_excenterWeights_singleton_neg i]
/-
**Affine.Simplex.sOppSide_point_excenter_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Af
fine.Simplex`。
形式化陈述：sOppSide_point_excenter_singleton [Nat.AtLeastTwo n] (i : Fin (n + 1)) : (
affineSpan Real (Set.range (s.faceOpposite i).points)).SOppSide (s.points i) (s.
excenter {i})
参数：i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.ExcenterExists.sOppSide_point_excenter_iff`：∀ {V : Type u
_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V
] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用引理 `Affine.Simplex.excenterExists_singleton`：excenterExists_singleton [Nat.A
tLeastTwo n] (i : Fin (n + 1)) : s.ExcenterExists {i}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sign_eq_neg_one_iff`：sign_eq_neg_one_iff : sign a = -1 ↔ a < 0
· 使用引理 `Affine.Simplex.sign_excenterWeights_singleton_neg`：sign_excenterWeights_
singleton_neg [Nat.AtLeastTwo n] (i : Fin (n + 1)) : SignType.sign (s.excenterWe
ights {i} i) = -1
-/
lemma sOppSide_point_excenter_singleton [Nat.AtLeastTwo n] (i : Fin (n + 1)) :
    (affineSpan ℝ (Set.range (s.faceOpposite i).points)).SOppSide (s.points i)
      (s.excenter {i}) := by
  rw [(s.excenterExists_singleton i).sOppSide_point_excenter_iff, ← sign_eq_neg_one_iff,
    s.sign_excenterWeights_singleton_neg i]
/-
**Affine.Simplex.sSameSide_excenter_singleton_point** 是 Mathlib 中的一个引理，位于命名空间 `A
ffine.Simplex`。
形式化陈述：sSameSide_excenter_singleton_point [Nat.AtLeastTwo n] {i j : Fin (n + 1)} 
(h : i != j) : (affineSpan Real (Set.range (s.faceOpposite i).points)).SSameSide
 (s.excenter {j}) (s.points i)
参数：n + 1；h : i != j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.ExcenterExists.sSameSide_excenter_point_iff`：∀ {V : Type 
u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ 
V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用引理 `Affine.Simplex.excenterExists_singleton`：excenterExists_singleton [Nat.A
tLeastTwo n] (i : Fin (n + 1)) : s.ExcenterExists {i}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sign_eq_one_iff`：sign_eq_one_iff : sign a = 1 ↔ 0 < a
· 使用引理 `Affine.Simplex.sign_excenterWeights_singleton_pos`：sign_excenterWeights_
singleton_pos [Nat.AtLeastTwo n] {i j : Fin (n + 1)} (h : i != j) : SignType.sig
n (s.excenterWeights {i} j) = 1
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
lemma sSameSide_excenter_singleton_point [Nat.AtLeastTwo n] {i j : Fin (n + 1)} (h : i ≠ j) :
    (affineSpan ℝ (Set.range (s.faceOpposite i).points)).SSameSide (s.excenter {j})
      (s.points i) := by
  rw [(s.excenterExists_singleton j).sSameSide_excenter_point_iff, ← sign_eq_one_iff,
    s.sign_excenterWeights_singleton_pos h.symm]
/-
**Affine.Simplex.sSameSide_point_excenter_singleton** 是 Mathlib 中的一个引理，位于命名空间 `A
ffine.Simplex`。
形式化陈述：sSameSide_point_excenter_singleton [Nat.AtLeastTwo n] {i j : Fin (n + 1)} 
(h : i != j) : (affineSpan Real (Set.range (s.faceOpposite i).points)).SSameSide
 (s.points i) (s.excenter {j})
参数：n + 1；h : i != j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.ExcenterExists.sSameSide_point_excenter_iff`：∀ {V : Type 
u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ 
V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用引理 `Affine.Simplex.excenterExists_singleton`：excenterExists_singleton [Nat.A
tLeastTwo n] (i : Fin (n + 1)) : s.ExcenterExists {i}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sign_eq_one_iff`：sign_eq_one_iff : sign a = 1 ↔ 0 < a
· 使用引理 `Affine.Simplex.sign_excenterWeights_singleton_pos`：sign_excenterWeights_
singleton_pos [Nat.AtLeastTwo n] {i j : Fin (n + 1)} (h : i != j) : SignType.sig
n (s.excenterWeights {i} j) = 1
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
lemma sSameSide_point_excenter_singleton [Nat.AtLeastTwo n] {i j : Fin (n + 1)} (h : i ≠ j) :
    (affineSpan ℝ (Set.range (s.faceOpposite i).points)).SSameSide (s.points i)
      (s.excenter {j}) := by
  rw [(s.excenterExists_singleton j).sSameSide_point_excenter_iff, ← sign_eq_one_iff,
    s.sign_excenterWeights_singleton_pos h.symm]

/-- A touchpoint is where an exsphere of a simplex is tangent to one of the faces. -/
/-
**Affine.Simplex.touchpoint** 是 Mathlib 中的一个定义，位于命名空间 `Affine.Simplex`。
形式化陈述：touchpoint (signs : Finset (Fin (n + 1))) (i : Fin (n + 1)) : P
参数：signs : Finset (Fin (n + 1))；i : Fin (n + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A touchpoint is where an exsphere of a simplex is tangent to one of the faces.
-/
def touchpoint (signs : Finset (Fin (n + 1))) (i : Fin (n + 1)) : P :=
  (s.faceOpposite i).orthogonalProjectionSpan (s.excenter signs)
/-
**Affine.Simplex.touchpoint_reindex** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simplex`。
形式化陈述：touchpoint_reindex (e : Fin (n + 1) ≃ Fin (m + 1)) (signs : Finset (Fin (m
 + 1))) (i : Fin (m + 1)) : (s.reindex e).touchpoint signs i = s.touchpoint (sig
ns.map e.symm) (e.symm i)
参数：e : Fin (n + 1) ≃ Fin (m + 1)；signs : Finset (Fin (m + 1))；i : Fin (m + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Affine.Simplex.orthogonalProjectionSpan_congr`：orthogonalProjectionSpan_
congr {m n : Nat} {s₁ : Simplex 𝕜 P m} {s₂ : Simplex 𝕜 P n} {p₁ p₂ : P} (h : Set
.range s₁.points = Set.range s₂.poi…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `Affine.Simplex.range_faceOpposite_reindex`：range_faceOpposite_reindex {m
 n : Nat} [NeZero m] [NeZero n] (s : Simplex k P m) (e : Fin (m + 1) ≃ Fin (n + 
1)) (i : Fin (n + 1)) : Set.ran…
· 使用引理 `Affine.Simplex.excenter_reindex`：excenter_reindex (e : Fin (n + 1) ≃ Fin
 (m + 1)) (signs : Finset (Fin (m + 1))) : (s.reindex e).excenter signs = s.exce
nter (signs.map e.sym…
-/
lemma touchpoint_reindex (e : Fin (n + 1) ≃ Fin (m + 1)) (signs : Finset (Fin (m + 1)))
    (i : Fin (m + 1)) :
    (s.reindex e).touchpoint signs i = s.touchpoint (signs.map e.symm) (e.symm i) :=
  orthogonalProjectionSpan_congr (s.range_faceOpposite_reindex _ _) (s.excenter_reindex _ _)

set_option backward.isDefEq.respectTransparency false in
variable {s} in
/-
**Affine.Simplex.ExcenterExists.touchpoint_map** 是 Mathlib 中的一个定理，位于命名空间 `Affine
.Simplex.ExcenterExists`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
V₂ : Type u_3} {P₂ : Type u_4} [inst_4 : NormedAddCommGroup V₂]   [inst_5 : Inne
rProductSpace ℝ V₂] [inst_6 : MetricSpace P₂] [inst_7 : NormedAddTorsor V₂ P₂] {
n : ℕ}   [inst_8 : NeZero n] {s : Affine.Simplex ℝ P n} {signs : Finset (Fin (n 
+ 1))},   s.ExcenterExists signs →     ∀ (f : P →ᵃⁱ[ℝ] P₂) (i : Fin (n + 1)), (s
.map f.toAffineMap ⋯).touchpoint signs i = f (s.touchpoint signs i)
参数：Fin (n + 1)；f : P →ᵃⁱ[ℝ] P₂；i : Fin (n + 1)；s.map f.toAffineMap ⋯；s.touchpoin
t signs i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AffineIsometry.injective`：∀ {𝕜 : Type u_1} {V₁' : Type u_4} {V₂ : Type u
_5} {P₁' : Type u_9} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : Seminor
medAddCommGrou…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.ExcenterExists.excenter_map`：∀ {V : Type u_1} {P : Type u
_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Met
ricSpace P]   [inst_3 : NormedAd…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma ExcenterExists.touchpoint_map {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) (f : P →ᵃⁱ[ℝ] P₂) (i : Fin (n + 1)) :
    (s.map f.toAffineMap f.injective).touchpoint signs i = f (s.touchpoint signs i) := by
  simp [touchpoint, h.excenter_map, ← orthogonalProjectionSpan_map]

variable {s} in
/-
**Affine.Simplex.ExcenterExists.touchpoint_restrict** 是 Mathlib 中的一个定理，位于命名空间 `A
ffine.Simplex.ExcenterExists`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] {s : Affine.Simplex ℝ P n} {signs : Finset (Fin (n + 
1))},   s.ExcenterExists signs →     ∀ (S : AffineSubspace ℝ P) (hS : affineSpan
 ℝ (Set.range s.points) ≤ S) (i : Fin (n + 1)),       ↑((s.restrict S hS).touchp
oint signs i) = s.touchpoint signs i
参数：Fin (n + 1)；S : AffineSubspace ℝ P；hS : affineSpan ℝ (Set.range s.points) ≤ S
；i : Fin (n + 1)；(s.restrict S hS).touchpoint signs i。
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
· 使用定理 `AffineIsometry.injective`：∀ {𝕜 : Type u_1} {V₁' : Type u_4} {V₂ : Type u
_5} {P₁' : Type u_9} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : Seminor
medAddCommGrou…
· 使用定理 `Affine.Simplex.ExcenterExists.touchpoint_map`：∀ {V : Type u_1} {P : Type
 u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : M
etricSpace P]   [inst_3 : NormedAd…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.excenterExists_restrict`：∀ {V : Type u_1} {P : Type u_2} 
[inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricS
pace P]   [inst_3 : NormedAd…
-/
@[simp] lemma ExcenterExists.touchpoint_restrict {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) (S : AffineSubspace ℝ P)
    (hS : affineSpan ℝ (Set.range s.points) ≤ S) (i : Fin (n + 1)) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).touchpoint signs i = s.touchpoint signs i := by
  rw [← s.excenterExists_restrict S hS] at h
  have := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  exact (h.touchpoint_map S.subtypeₐᵢ i).symm
/-
**Affine.Simplex.touchpoint_mem_affineSpan** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Sim
plex`。
形式化陈述：touchpoint_mem_affineSpan (signs : Finset (Fin (n + 1))) (i : Fin (n + 1))
 : s.touchpoint signs i in affineSpan Real (Set.range (s.faceOpposite i).points)
参数：signs : Finset (Fin (n + 1))；i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.orthogonalProjection_mem`：orthogonalProjection_mem {s 
: AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalProjection] (p : P)
 : ↑(orthogonalProjection s p) i…
-/
lemma touchpoint_mem_affineSpan (signs : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    s.touchpoint signs i ∈ affineSpan ℝ (Set.range (s.faceOpposite i).points) :=
  orthogonalProjection_mem _

/-- A weaker version of `touchpoint_mem_affineSpan`. -/
/-
**Affine.Simplex.touchpoint_mem_affineSpan_simplex** 是 Mathlib 中的一个引理，位于命名空间 `Af
fine.Simplex`。
形式化陈述：touchpoint_mem_affineSpan_simplex (signs : Finset (Fin (n + 1))) (i : Fin 
(n + 1)) : s.touchpoint signs i in affineSpan Real (Set.range s.points)
参数：signs : Finset (Fin (n + 1))；i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `affineSpan_mono`：affineSpan_mono {s₁ s₂ : Set P} (h : s₁ subseteq s₂) : 
affineSpan k s₁ <= affineSpan k s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.range_faceOpposite_points`：∀ {k : Type u_1} {V : Type u_2
} {P : Type u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Modu
le k V]   [inst_3 : AddTorsor …
· 使用定理 `Set.preimage_range`：preimage_range (f : α -> β) : f ⁻¹' range f = univ
· 使用引理 `Affine.Simplex.touchpoint_mem_affineSpan`：touchpoint_mem_affineSpan (sig
ns : Finset (Fin (n + 1))) (i : Fin (n + 1)) : s.touchpoint signs i in affineSpa
n Real (Set.range (s.faceOppos…

--- 原说明 ---
A weaker version of `touchpoint_mem_affineSpan`.
-/
lemma touchpoint_mem_affineSpan_simplex (signs : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    s.touchpoint signs i ∈ affineSpan ℝ (Set.range s.points) := by
  refine SetLike.le_def.1 (affineSpan_mono _ ?_) (s.touchpoint_mem_affineSpan signs i)
  simp
/-
**Affine.Simplex.touchpoint_eq_point_rev** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simpl
ex`。
形式化陈述：touchpoint_eq_point_rev (s : Simplex Real P 1) (signs : Finset (Fin 2)) (i
 : Fin 2) : s.touchpoint signs i = s.points i.rev
参数：s : Simplex Real P 1；signs : Finset (Fin 2)；i : Fin 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Affine.Simplex.orthogonalProjectionSpan_faceOpposite_eq_point_rev`：ortho
gonalProjectionSpan_faceOpposite_eq_point_rev (s : Simplex 𝕜 P 1) (i : Fin 2) (p
 : P) : (s.faceOpposite i).orthogonalProjectionSpan p =…
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma touchpoint_eq_point_rev (s : Simplex ℝ P 1) (signs : Finset (Fin 2)) (i : Fin 2) :
    s.touchpoint signs i = s.points i.rev :=
  s.orthogonalProjectionSpan_faceOpposite_eq_point_rev _ _

variable {s} in
/-- The signed distance between the excenter and its projection in the plane of each face is the
exradius. -/
/-
**Affine.Simplex.ExcenterExists.signedInfDist_excenter** 是 Mathlib 中的一个定理，位于命名空间
 `Affine.Simplex.ExcenterExists`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] {s : Affine.Simplex ℝ P n} {signs : Finset (Fin (n + 
1))},   s.ExcenterExists signs →     ∀ (i : Fin (n + 1)),       (s.signedInfDist
 i) (s.excenter signs) =         (if i ∈ signs then -1 else 1) * ↑(SignType.sign
 (∑ j, s.excenterWeightsUnnorm signs j)) * s.exradius signs
参数：Fin (n + 1)；i : Fin (n + 1)；s.signedInfDist i；s.excenter signs；if i ∈ signs t
hen -1 else 1；SignType.sign (∑ j, s.excenterWeightsUnnorm signs j)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.ExcenterExists.signedInfDist_excenter_eq_mul_sum_inv`：∀ {
V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProduc
tSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `Affine.Simplex.exradius_eq_abs_inv_sum`：exradius_eq_abs_inv_sum (signs :
 Finset (Fin (n + 1))) : s.exradius signs = |(∑ i, s.excenterWeightsUnnorm signs
 i)⁻¹|
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `mul_eq_one_iff_inv_eq₀`：mul_eq_one_iff_inv_eq₀ (ha : a != 0) : a * b = 1
 ↔ a⁻¹ = b
· 使用定理 `self_mul_sign`：self_mul_sign (x : α) : x * sign x = |x|
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1

--- 原说明 ---
The signed distance between the excenter and its projection in the plane of each
 face is the
exradius.
-/
lemma ExcenterExists.signedInfDist_excenter {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) (i : Fin (n + 1)) :
    s.signedInfDist i (s.excenter signs) = (if i ∈ signs then -1 else 1) *
      SignType.sign (∑ j, s.excenterWeightsUnnorm signs j) * (s.exradius signs) := by
  rw [h.signedInfDist_excenter_eq_mul_sum_inv, mul_assoc, exradius_eq_abs_inv_sum]
  congr
  rw [← mul_eq_one_iff_inv_eq₀ h, ← mul_assoc, self_mul_sign, ← abs_mul, mul_inv_cancel₀ h, abs_one]

/-- The signed distance between the incenter and its projection in the plane of each face is the
inradius.

In other words, the incenter is _internally_ tangent to the faces. -/
/-
**Affine.Simplex.signedInfDist_incenter** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simple
x`。
形式化陈述：signedInfDist_incenter (i : Fin (n + 1)) : s.signedInfDist i s.incenter = 
s.inradius
参数：i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.incenter.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.exsphere_center`：∀ {V : Type u_1} {P : Type u_2} [inst : 
NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] 
  [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.ExcenterExists.signedInfDist_excenter`：∀ {V : Type u_1} {
P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [in
st_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.excenterExists_empty`：∀ {V : Type u_1} {P : Type u_2} [in
st : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpac
e P]   [inst_3 : NormedAd…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Affine.Simplex.excenterWeightsUnnorm_empty_apply`：∀ {V : Type u_1} {P : 
Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2
 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `sign_pos`：sign_pos (ha : 0 < a) : sign a = 1
· 使用定理 `Finset.sum_pos`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid M]
 [inst_1 : Preorder M] [IsOrderedCancelAddMonoid M] {f : ι → M}   {s : Finset ι}
 [Ad…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Affine.Simplex.height_pos`：height_pos {n : Nat} [NeZero n] (s : Simplex 
Real P n) (i : Fin (n + 1)) : 0 < s.height i
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
The signed distance between the incenter and its projection in the plane of each
 face is the
inradius.

In other words, the incenter is _internally_ tangent to the faces.
-/
lemma signedInfDist_incenter (i : Fin (n + 1)) : s.signedInfDist i s.incenter = s.inradius := by
  rw [incenter, exsphere_center, s.excenterExists_empty.signedInfDist_excenter]
  simp (discharger := positivity)

variable {s} in
/-- The distance between the excenter and its projection in the plane of each face is the
exradius. -/
/-
**Affine.Simplex.ExcenterExists.dist_excenter** 是 Mathlib 中的一个定理，位于命名空间 `Affine.
Simplex.ExcenterExists`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] {s : Affine.Simplex ℝ P n} {signs : Finset (Fin (n + 
1))},   s.ExcenterExists signs → ∀ (i : Fin (n + 1)), dist (s.excenter signs) (s
.touchpoint signs i) = s.exradius signs
参数：Fin (n + 1)；i : Fin (n + 1)；s.excenter signs；s.touchpoint signs i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.touchpoint.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : 
NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] 
  [inst_3 : NormedAd…
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Affine.Simplex.abs_signedInfDist_eq_dist_of_mem_affineSpan_range`：abs_si
gnedInfDist_eq_dist_of_mem_affineSpan_range {p : P} (h : p in affineSpan Real (S
et.range s.points)) : |s.signedInfDist i p| = dist p (…
· 使用定理 `Affine.Simplex.ExcenterExists.excenter_mem_affineSpan_range`：∀ {V : Type
 u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ
 V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.ExcenterExists.signedInfDist_excenter`：∀ {V : Type u_1} {
P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [in
st_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `Affine.Simplex.exradius_nonneg`：exradius_nonneg (signs : Finset (Fin (n 
+ 1))) : 0 <= s.exradius signs
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `abs_ite`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a b 
: α} (p : Prop) [inst_2 : Decidable p],   |if p then a else b| = if p then |a…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `sign_pos`：sign_pos (ha : 0 < a) : sign a = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `sign_neg`：sign_neg (ha : a < 0) : sign a = -1
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
The distance between the excenter and its projection in the plane of each face i
s the
exradius.
-/
lemma ExcenterExists.dist_excenter {signs : Finset (Fin (n + 1))} (h : s.ExcenterExists signs)
    (i : Fin (n + 1)) :
    dist (s.excenter signs) (s.touchpoint signs i) = s.exradius signs := by
  rw [touchpoint,
    ← abs_signedInfDist_eq_dist_of_mem_affineSpan_range i h.excenter_mem_affineSpan_range,
    h.signedInfDist_excenter, abs_mul, abs_mul, abs_of_nonneg (s.exradius_nonneg signs)]
  simp only [abs_ite, abs_neg, abs_one, ite_self, one_mul]
  rcases lt_trichotomy 0 (∑ i, s.excenterWeightsUnnorm signs i) with h' | h' | h'
  · simp [h']
  · simp [h h'.symm]
  · simp [h']

/-- The distance between the incenter and its projection in the plane of each face is the
inradius. -/
/-
**Affine.Simplex.dist_incenter** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simplex`。
形式化陈述：dist_incenter (i : Fin (n + 1)) : dist s.incenter (s.touchpoint ∅ i) = s.i
nradius
参数：i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.ExcenterExists.dist_excenter`：∀ {V : Type u_1} {P : Type 
u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Me
tricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.excenterExists_empty`：∀ {V : Type u_1} {P : Type u_2} [in
st : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpac
e P]   [inst_3 : NormedAd…

--- 原说明 ---
The distance between the incenter and its projection in the plane of each face i
s the
inradius.
-/
lemma dist_incenter (i : Fin (n + 1)) :
    dist s.incenter (s.touchpoint ∅ i) = s.inradius :=
  s.excenterExists_empty.dist_excenter _

variable {s} in
/-- An excenter is equidistant to any two of its touchpoints. -/
/-
**Affine.Simplex.ExcenterExists.dist_excenter_eq_dist_excenter** 是 Mathlib 中的一个定
理，位于命名空间 `Affine.Simplex.ExcenterExists`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] {s : Affine.Simplex ℝ P n} {signs : Finset (Fin (n + 
1))},   s.ExcenterExists signs →     ∀ (i₁ i₂ : Fin (n + 1)),       dist (s.exce
nter signs) (s.touchpoint signs i₁) = dist (s.excenter signs) (s.touchpoint sign
s i₂)
参数：Fin (n + 1)；i₁ i₂ : Fin (n + 1)；s.excenter signs；s.touchpoint signs i₁；s.exce
nter signs；s.touchpoint signs i₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.ExcenterExists.dist_excenter`：∀ {V : Type u_1} {P : Type 
u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Me
tricSpace P]   [inst_3 : NormedAd…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
An excenter is equidistant to any two of its touchpoints.
-/
lemma ExcenterExists.dist_excenter_eq_dist_excenter {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) (i₁ i₂ : Fin (n + 1)) :
    dist (s.excenter signs) (s.touchpoint signs i₁) =
      dist (s.excenter signs) (s.touchpoint signs i₂) := by
  simp_rw [h.dist_excenter]

/-- The incenter is equidistant to any two of its touchpoints. -/
/-
**Affine.Simplex.dist_incenter_eq_dist_incenter** 是 Mathlib 中的一个引理，位于命名空间 `Affin
e.Simplex`。
形式化陈述：dist_incenter_eq_dist_incenter (i₁ i₂ : Fin (n + 1)) : dist s.incenter (s.
touchpoint ∅ i₁) = dist s.incenter (s.touchpoint ∅ i₂)
参数：i₁ i₂ : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.ExcenterExists.dist_excenter_eq_dist_excenter`：∀ {V : Typ
e u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace 
ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.excenterExists_empty`：∀ {V : Type u_1} {P : Type u_2} [in
st : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpac
e P]   [inst_3 : NormedAd…

--- 原说明 ---
The incenter is equidistant to any two of its touchpoints.
-/
lemma dist_incenter_eq_dist_incenter (i₁ i₂ : Fin (n + 1)) :
    dist s.incenter (s.touchpoint ∅ i₁) = dist s.incenter (s.touchpoint ∅ i₂) :=
  s.excenterExists_empty.dist_excenter_eq_dist_excenter _ _

variable {s} in
/-
**Affine.Simplex.ExcenterExists.touchpoint_mem_exsphere** 是 Mathlib 中的一个定理，位于命名空
间 `Affine.Simplex.ExcenterExists`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] {s : Affine.Simplex ℝ P n} {signs : Finset (Fin (n + 
1))},   s.ExcenterExists signs → ∀ (i : Fin (n + 1)), s.touchpoint signs i ∈ s.e
xsphere signs
参数：Fin (n + 1)；i : Fin (n + 1)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EuclideanGeometry.mem_sphere'`：mem_sphere' {p : P} {s : Sphere P} : p in
 s ↔ dist s.center p = s.radius
· 使用定理 `Affine.Simplex.ExcenterExists.dist_excenter`：∀ {V : Type u_1} {P : Type 
u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Me
tricSpace P]   [inst_3 : NormedAd…
-/
lemma ExcenterExists.touchpoint_mem_exsphere {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) (i : Fin (n + 1)) : s.touchpoint signs i ∈ s.exsphere signs :=
  mem_sphere'.2 (h.dist_excenter i)
/-
**Affine.Simplex.touchpoint_mem_insphere** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simpl
ex`。
形式化陈述：touchpoint_mem_insphere (i : Fin (n + 1)) : s.touchpoint ∅ i in s.insphere
参数：i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.ExcenterExists.touchpoint_mem_exsphere`：∀ {V : Type u_1} 
{P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [i
nst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.excenterExists_empty`：∀ {V : Type u_1} {P : Type u_2} [in
st : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpac
e P]   [inst_3 : NormedAd…
-/
lemma touchpoint_mem_insphere (i : Fin (n + 1)) : s.touchpoint ∅ i ∈ s.insphere :=
  s.excenterExists_empty.touchpoint_mem_exsphere _

variable {s} in
/-
**Affine.Simplex.ExcenterExists.isTangentAt_touchpoint** 是 Mathlib 中的一个定理，位于命名空间
 `Affine.Simplex.ExcenterExists`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] {s : Affine.Simplex ℝ P n} {signs : Finset (Fin (n + 
1))},   s.ExcenterExists signs →     ∀ (i : Fin (n + 1)),       (s.exsphere sign
s).IsTangentAt (s.touchpoint signs i) (affineSpan ℝ (Set.range (s.faceOpposite i
).points))
参数：Fin (n + 1)；i : Fin (n + 1)；s.exsphere signs；s.touchpoint signs i；affineSpan 
ℝ (Set.range (s.faceOpposite i).points)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.touchpoint.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : 
NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] 
  [inst_3 : NormedAd…
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Affine.Simplex.orthogonalProjectionSpan.eq_1`：∀ {𝕜 : Type u_1} {V : Type
 u_2} {P : Type u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup V]   [inst_2
 : InnerProductSpace 𝕜 V] [inst_3 …
· 使用定理 `Affine.Simplex.excenter.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `EuclideanGeometry.Sphere.dist_orthogonalProjection_eq_radius_iff_isTange
ntAt`：dist_orthogonalProjection_eq_radius_iff_isTangentAt {s : Sphere P} {as : A
ffineSubspace Real P} [Nonempty as] [as.direction.HasOrthogonalPro…
· 使用定理 `Affine.Simplex.exradius.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.ExcenterExists.dist_excenter`：∀ {V : Type u_1} {P : Type 
u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Me
tricSpace P]   [inst_3 : NormedAd…
-/
lemma ExcenterExists.isTangentAt_touchpoint {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) (i : Fin (n + 1)) :
    (s.exsphere signs).IsTangentAt (s.touchpoint signs i)
      (affineSpan ℝ (Set.range (s.faceOpposite i).points)) := by
  rw [touchpoint, orthogonalProjectionSpan, excenter,
    ← EuclideanGeometry.Sphere.dist_orthogonalProjection_eq_radius_iff_isTangentAt,
    ← orthogonalProjectionSpan, ← excenter, ← exradius, ← touchpoint, h.dist_excenter]
/-
**Affine.Simplex.isTangentAt_insphere_touchpoint** 是 Mathlib 中的一个引理，位于命名空间 `Affi
ne.Simplex`。
形式化陈述：isTangentAt_insphere_touchpoint (i : Fin (n + 1)) : s.insphere.IsTangentAt
 (s.touchpoint ∅ i) (affineSpan Real (Set.range (s.faceOpposite i).points))
参数：i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.ExcenterExists.isTangentAt_touchpoint`：∀ {V : Type u_1} {
P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [in
st_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.excenterExists_empty`：∀ {V : Type u_1} {P : Type u_2} [in
st : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpac
e P]   [inst_3 : NormedAd…
-/
lemma isTangentAt_insphere_touchpoint (i : Fin (n + 1)) :
    s.insphere.IsTangentAt (s.touchpoint ∅ i)
      (affineSpan ℝ (Set.range (s.faceOpposite i).points)) :=
  s.excenterExists_empty.isTangentAt_touchpoint i

variable {s} in
/-
**Affine.Simplex.eq_touchpoint_of_isTangentAt_exsphere** 是 Mathlib 中的一个引理，位于命名空间
 `Affine.Simplex`。
形式化陈述：eq_touchpoint_of_isTangentAt_exsphere {signs : Finset (Fin (n + 1))} {i : 
Fin (n + 1)} {p : P} (ht : (s.exsphere signs).IsTangentAt p (affineSpan Real (Se
t.range (s.faceOpposite i).points))) : p = s.touchpoint signs i
参数：Fin (n + 1)；n + 1；ht : (s.exsphere signs).IsTangentAt p (affineSpan Real (Set
.range (s.faceOpposite i).points))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.Sphere.IsTangentAt.eq_orthogonalProjection`：∀ {V : Typ
e u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace 
ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.touchpoint.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : 
NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] 
  [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.orthogonalProjectionSpan.eq_1`：∀ {𝕜 : Type u_1} {V : Type
 u_2} {P : Type u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup V]   [inst_2
 : InnerProductSpace 𝕜 V] [inst_3 …
· 使用定理 `Affine.Simplex.excenter.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
-/
lemma eq_touchpoint_of_isTangentAt_exsphere {signs : Finset (Fin (n + 1))} {i : Fin (n + 1)} {p : P}
    (ht : (s.exsphere signs).IsTangentAt p (affineSpan ℝ (Set.range (s.faceOpposite i).points))) :
    p = s.touchpoint signs i := by
  rw [ht.eq_orthogonalProjection, touchpoint, orthogonalProjectionSpan, excenter]

variable {s} in
/-
**Affine.Simplex.ExcenterExists.isTangentAt_exsphere_iff_eq_touchpoint** 是 Mathl
ib 中的一个定理，位于命名空间 `Affine.Simplex.ExcenterExists`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] {s : Affine.Simplex ℝ P n} {signs : Finset (Fin (n + 
1))},   s.ExcenterExists signs →     ∀ {i : Fin (n + 1)} {p : P},       (s.exsph
ere signs).IsTangentAt p (affineSpan ℝ (Set.range (s.faceOpposite i).points)) ↔ 
p = s.touchpoint signs i
参数：Fin (n + 1)；n + 1；s.exsphere signs；affineSpan ℝ (Set.range (s.faceOpposite i)
.points)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Affine.Simplex.eq_touchpoint_of_isTangentAt_exsphere`：eq_touchpoint_of_i
sTangentAt_exsphere {signs : Finset (Fin (n + 1))} {i : Fin (n + 1)} {p : P} (ht
 : (s.exsphere signs).IsTangentAt p (affin…
· 使用定理 `Affine.Simplex.ExcenterExists.isTangentAt_touchpoint`：∀ {V : Type u_1} {
P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [in
st_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma ExcenterExists.isTangentAt_exsphere_iff_eq_touchpoint {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) {i : Fin (n + 1)} {p : P} :
    (s.exsphere signs).IsTangentAt p (affineSpan ℝ (Set.range (s.faceOpposite i).points)) ↔
      p = s.touchpoint signs i := by
  refine ⟨eq_touchpoint_of_isTangentAt_exsphere, ?_⟩
  rintro rfl
  exact h.isTangentAt_touchpoint i

variable {s} in
/-
**Affine.Simplex.isTangentAt_insphere_iff_eq_touchpoint** 是 Mathlib 中的一个引理，位于命名空
间 `Affine.Simplex`。
形式化陈述：isTangentAt_insphere_iff_eq_touchpoint {i : Fin (n + 1)} {p : P} : s.insph
ere.IsTangentAt p (affineSpan Real (Set.range (s.faceOpposite i).points)) ↔ p = 
s.touchpoint ∅ i
参数：n + 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.ExcenterExists.isTangentAt_exsphere_iff_eq_touchpoint`：∀ 
{V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProdu
ctSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.excenterExists_empty`：∀ {V : Type u_1} {P : Type u_2} [in
st : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpac
e P]   [inst_3 : NormedAd…
-/
lemma isTangentAt_insphere_iff_eq_touchpoint {i : Fin (n + 1)} {p : P} :
    s.insphere.IsTangentAt p (affineSpan ℝ (Set.range (s.faceOpposite i).points)) ↔
      p = s.touchpoint ∅ i :=
  s.excenterExists_empty.isTangentAt_exsphere_iff_eq_touchpoint

variable {s} in
/-
**Affine.Simplex.ExcenterExists.affineSpan_faceOpposite_eq_orthRadius** 是 Mathli
b 中的一个定理，位于命名空间 `Affine.Simplex.ExcenterExists`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] {s : Affine.Simplex ℝ P n}   [hf : Fact (Module.finra
nk ℝ V = n)] {signs : Finset (Fin (n + 1))},   s.ExcenterExists signs →     ∀ (i
 : Fin (n + 1)),       affineSpan ℝ (Set.range (s.faceOpposite i).points) = (s.e
xsphere signs).orthRadius (s.touchpoint signs i)
参数：Module.finrank ℝ V = n；Fin (n + 1)；i : Fin (n + 1)；Set.range (s.faceOpposite 
i).points；s.exsphere signs；s.touchpoint signs i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.Sphere.IsTangentAt.eq_orthRadius_of_finrank_add_one_eq
`：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerP
roductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.ExcenterExists.isTangentAt_touchpoint`：∀ {V : Type u_1} {
P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [in
st_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Affine.Simplex.ExcenterExists.exradius_pos`：∀ {V : Type u_1} {P : Type u
_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Met
ricSpace P]   [inst_3 : NormedAd…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s
· 使用引理 `AffineIndependent.finrank_vectorSpan_add_one`：AffineIndependent.finrank_
vectorSpan_add_one [Fintype ι] [Nonempty ι] {p : ι -> P} (hi : AffineIndependent
 k p) : finrank k (vectorSpan k (S…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Affine.Simplex.independent`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [ins
t_3 : AddTorsor …
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
-/
lemma ExcenterExists.affineSpan_faceOpposite_eq_orthRadius [hf : Fact (Module.finrank ℝ V = n)]
    {signs : Finset (Fin (n + 1))} (h : s.ExcenterExists signs) (i : Fin (n + 1)) :
    affineSpan ℝ (Set.range (s.faceOpposite i).points) =
      (s.exsphere signs).orthRadius (s.touchpoint signs i) := by
  refine (h.isTangentAt_touchpoint i).eq_orthRadius_of_finrank_add_one_eq (h.exradius_pos.ne') ?_
  rw [direction_affineSpan, (s.faceOpposite i).independent.finrank_vectorSpan_add_one,
    Fintype.card_fin, hf.out]
  have := NeZero.ne n
  lia
/-
**Affine.Simplex.affineSpan_faceOpposite_eq_orthRadius_insphere** 是 Mathlib 中的一个
引理，位于命名空间 `Affine.Simplex`。
形式化陈述：affineSpan_faceOpposite_eq_orthRadius_insphere [Fact (Module.finrank Real 
V = n)] (i : Fin (n + 1)) : affineSpan Real (Set.range (s.faceOpposite i).points
) = s.insphere.orthRadius (s.touchpoint ∅ i)
参数：Module.finrank Real V = n；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.ExcenterExists.affineSpan_faceOpposite_eq_orthRadius`：∀ {
V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProduc
tSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.excenterExists_empty`：∀ {V : Type u_1} {P : Type u_2} [in
st : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpac
e P]   [inst_3 : NormedAd…
-/
lemma affineSpan_faceOpposite_eq_orthRadius_insphere [Fact (Module.finrank ℝ V = n)]
    (i : Fin (n + 1)) :
    affineSpan ℝ (Set.range (s.faceOpposite i).points) = s.insphere.orthRadius (s.touchpoint ∅ i) :=
  s.excenterExists_empty.affineSpan_faceOpposite_eq_orthRadius i
/-
**Affine.Simplex.exists_forall_signedInfDist_eq_iff_excenterExists_and_eq_excent
er** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simplex`。
形式化陈述：exists_forall_signedInfDist_eq_iff_excenterExists_and_eq_excenter {p : P} 
(hp : p in affineSpan Real (Set.range s.points)) {signs : Finset (Fin (n + 1))} 
: (exists r : Real, forall i, s.signedInfDist i p = (if i in signs then -1 else 
1) * r) ↔ s.ExcenterExists signs ∧ p = s.excenter signs
参数：hp : p in affineSpan Real (Set.range s.points)；Fin (n + 1)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_affineCombination_of_mem_affineSpan_of_fintype`：eq_affineCombination_
of_mem_affineSpan_of_fintype [Fintype ι] {p1 : P} {p : ι -> P} (h : p1 in affine
Span k (Set.range p)) : exists w : ι ->…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.altitudeFoot.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst 
: NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P
]   [inst_3 : NormedAd…
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Affine.Simplex.signedInfDist_affineCombination`：signedInfDist_affineComb
ination {w : Fin (n + 1) -> Real} (h : ∑ i, w i = 1) : s.signedInfDist i (Finset
.univ.affineCombination Real s.point…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `eq_div_iff`：eq_div_iff (hb : b != 0) : c = a / b ↔ c * b = a
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `Affine.Simplex.height_pos`：height_pos {n : Nat} [NeZero n] (s : Simplex 
Real P n) (i : Fin (n + 1)) : 0 < s.height i
· 使用定理 `Affine.Simplex.height.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : Norm
edAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [i
nst_3 : NormedAd…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Affine.Simplex.orthogonalProjectionSpan.eq_1`：∀ {𝕜 : Type u_1} {V : Type
 u_2} {P : Type u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup V]   [inst_2
 : InnerProductSpace 𝕜 V] [inst_3 …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_inv_of_mul_eq_one_left`：eq_inv_of_mul_eq_one_left (h : a * b = 1) : a
 = b⁻¹
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Affine.Simplex.sum_excenterWeights_eq_one_iff`：∀ {V : Type u_1} {P : Typ
e u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : 
MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.ExcenterExists.signedInfDist_excenter`：∀ {V : Type u_1} {
P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [in
st_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
（共 33 条，此处仅展示前 30 条）
-/
lemma exists_forall_signedInfDist_eq_iff_excenterExists_and_eq_excenter {p : P}
    (hp : p ∈ affineSpan ℝ (Set.range s.points)) {signs : Finset (Fin (n + 1))} :
    (∃ r : ℝ, ∀ i, s.signedInfDist i p = (if i ∈ signs then -1 else 1) * r) ↔
      s.ExcenterExists signs ∧ p = s.excenter signs := by
  refine ⟨?_, ?_⟩
  · rintro ⟨r, h⟩
    obtain ⟨w, h1, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hp
    have h' : ∀ i, w i * ‖s.points i -ᵥ s.altitudeFoot i‖ = (if i ∈ signs then -1 else 1) * r := by
      intro i
      rw [altitudeFoot, ← s.signedInfDist_affineCombination i h1]
      exact h i
    simp_rw [← dist_eq_norm_vsub] at h'
    have h'' : ∀ i, w i = r * s.excenterWeightsUnnorm signs i := by
      simp_rw [excenterWeightsUnnorm]
      intro i
      replace h' := h' i
      rw [← height, ← eq_div_iff (s.height_pos i).ne'] at h'
      rw [h', mul_comm, div_eq_mul_inv, mul_assoc, height, altitudeFoot, orthogonalProjectionSpan]
    have hw : w = s.excenterWeights signs := by
      simp_rw [h'', ← Finset.mul_sum] at h1
      ext j
      rw [h'', eq_inv_of_mul_eq_one_left h1]
      simp [excenterWeights]
    subst hw
    exact ⟨s.sum_excenterWeights_eq_one_iff.1 h1, rfl⟩
  · rintro ⟨h, rfl⟩
    refine ⟨SignType.sign (∑ j, s.excenterWeightsUnnorm signs j) * (s.exradius signs), fun i ↦ ?_⟩
    rw [h.signedInfDist_excenter]
    simp
/-
**Affine.Simplex.exists_forall_signedInfDist_eq_iff_eq_incenter** 是 Mathlib 中的一个
引理，位于命名空间 `Affine.Simplex`。
形式化陈述：exists_forall_signedInfDist_eq_iff_eq_incenter {p : P} (hp : p in affineSp
an Real (Set.range s.points)) : (exists r : Real, forall i, s.signedInfDist i p 
= r) ↔ p = s.incenter
参数：hp : p in affineSpan Real (Set.range s.points)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `Affine.Simplex.exists_forall_signedInfDist_eq_iff_excenterExists_and_eq_
excenter`：exists_forall_signedInfDist_eq_iff_excenterExists_and_eq_excenter {p :
 P} (hp : p in affineSpan Real (Set.range s.points)) {signs : Finset (…
-/
lemma exists_forall_signedInfDist_eq_iff_eq_incenter {p : P}
    (hp : p ∈ affineSpan ℝ (Set.range s.points)) :
    (∃ r : ℝ, ∀ i, s.signedInfDist i p = r) ↔ p = s.incenter := by
  convert! s.exists_forall_signedInfDist_eq_iff_excenterExists_and_eq_excenter hp (signs := ∅)
  · simp
  · simp [excenterExists_empty]
/-
**Affine.Simplex.exists_forall_dist_eq_iff_exists_excenterExists_and_eq_excenter
** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simplex`。
形式化陈述：exists_forall_dist_eq_iff_exists_excenterExists_and_eq_excenter {p : P} (h
p : p in affineSpan Real (Set.range s.points)) : (exists r : Real, forall i, dis
t p ((s.faceOpposite i).orthogonalProjectionSpan p) = r) ↔ exists signs, s.Excen
terExists signs ∧ p = s.excenter signs
参数：hp : p in affineSpan Real (Set.range s.points)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Affine.Simplex.abs_signedInfDist_eq_dist_of_mem_affineSpan_range`：abs_si
gnedInfDist_eq_dist_of_mem_affineSpan_range {p : P} (h : p in affineSpan Real (S
et.range s.points)) : |s.signedInfDist i p| = dist p (…
· 使用定理 `eq_or_eq_neg_of_abs_eq`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : L
inearOrder α] {a b : α}, |a| = b → a = b ∨ a = -b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Affine.Simplex.exists_forall_signedInfDist_eq_iff_excenterExists_and_eq_
excenter`：exists_forall_signedInfDist_eq_iff_excenterExists_and_eq_excenter {p :
 P} (hp : p in affineSpan Real (Set.range s.points)) {signs : Finset (…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `abs_ite`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a b 
: α} (p : Prop) [inst_2 : Decidable p],   |if p then a else b| = if p then |a…
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma exists_forall_dist_eq_iff_exists_excenterExists_and_eq_excenter {p : P}
    (hp : p ∈ affineSpan ℝ (Set.range s.points)) :
    (∃ r : ℝ, ∀ i, dist p ((s.faceOpposite i).orthogonalProjectionSpan p) = r) ↔
      ∃ signs, s.ExcenterExists signs ∧ p = s.excenter signs := by
  simp_rw [← abs_signedInfDist_eq_dist_of_mem_affineSpan_range _ hp]
  refine ⟨?_, ?_⟩
  · rintro ⟨r, h⟩
    have h' : ∀ i, s.signedInfDist i p = r ∨ s.signedInfDist i p = -r :=
      fun i ↦ eq_or_eq_neg_of_abs_eq (h i)
    refine ⟨{i ∈ (Finset.univ : Finset (Fin (n + 1))) | s.signedInfDist i p = -r}, ?_⟩
    apply (s.exists_forall_signedInfDist_eq_iff_excenterExists_and_eq_excenter hp).1
    refine ⟨r, ?_⟩
    grind
  · rintro ⟨signs, h⟩
    replace h := (s.exists_forall_signedInfDist_eq_iff_excenterExists_and_eq_excenter hp).2 h
    rcases h with ⟨r, h⟩
    refine ⟨|r|, ?_⟩
    simp [h, abs_ite]

variable {s} in
/-
**Affine.Simplex.ExcenterExists.touchpoint_injective** 是 Mathlib 中的一个定理，位于命名空间 `
Affine.Simplex.ExcenterExists`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] {s : Affine.Simplex ℝ P n} {signs : Finset (Fin (n + 
1))},   s.ExcenterExists signs → Function.Injective (s.touchpoint signs)
参数：Fin (n + 1)；s.touchpoint signs。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `AffineIndependent.injective`：∀ {k : Type u_1} {V : Type u_2} {P : Type u
_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [in
st_3 : AddTorsor …
· 使用定理 `Affine.Simplex.independent`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [ins
t_3 : AddTorsor …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Affine.Simplex.touchpoint_eq_point_rev`：touchpoint_eq_point_rev (s : Sim
plex Real P 1) (signs : Finset (Fin 2)) (i : Fin 2) : s.touchpoint signs i = s.p
oints i.rev
· 使用定理 `Fin.exists_ne_and_ne_of_two_lt`：exists_ne_and_ne_of_two_lt (i j : Fin n)
 (h : 2 < n) : exists k, k != i ∧ k != j
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Affine.Simplex.range_faceOpposite_points`：∀ {k : Type u_1} {V : Type u_2
} {P : Type u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Modu
le k V]   [inst_3 : AddTorsor …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.inter_singleton_of_notMem`：∀ {α : Type u_1} {s : Set α} {a : α}, a ∉
 s → s ∩ {a} = ∅
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Set.compl_empty`：compl_empty : (∅ : Set α)ᶜ = univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用引理 `AffineSubspace.vectorSpan_union_of_mem_of_mem`：vectorSpan_union_of_mem_o
f_mem {s₁ s₂ : Set P} {p : P} (hp₁ : p in s₁) (hp₂ : p in s₂) : vectorSpan k (s₁
 union s₂) = vectorSpan k s₁ ⊔ vect…
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Submodule.inf_orthogonal`：inf_orthogonal (K₁ K₂ : Submodule 𝕜 E) : K₁ᗮ ⊓
 K₂ᗮ = (K₁ ⊔ K₂)ᗮ
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s
· 使用定理 `EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal`：vs
ub_orthogonalProjection_mem_direction_orthogonal (s : AffineSubspace 𝕜 P) [Nonem
pty s] [s.direction.HasOrthogonalProjection] (p : P) : p -…
· 使用定理 `AffineSubspace.vsub_mem_direction`：vsub_mem_direction {s : AffineSubspac
e k P} {p₁ p₂ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) : p₁ -ᵥ p₂ in s.direction
· 使用定理 `Affine.Simplex.ExcenterExists.excenter_mem_affineSpan_range`：∀ {V : Type
 u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ
 V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
（共 38 条，此处仅展示前 30 条）
-/
lemma ExcenterExists.touchpoint_injective {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) : Function.Injective (s.touchpoint signs) := by
  intro i j hij
  by_contra hne
  by_cases hn1 : n = 1
  · subst hn1
    rw [s.touchpoint_eq_point_rev signs i, s.touchpoint_eq_point_rev signs j] at hij
    apply s.independent.injective.ne hne
    convert! hij.symm <;> clear hij <;> decide +revert
  · suffices s.excenter signs -ᵥ s.touchpoint signs i ∈ (vectorSpan ℝ (Set.range s.points))ᗮ by
      have h' : s.excenter signs -ᵥ s.touchpoint signs i ∈ (vectorSpan ℝ (Set.range s.points)) := by
        rw [← direction_affineSpan]
        exact AffineSubspace.vsub_mem_direction h.excenter_mem_affineSpan_range
          (s.touchpoint_mem_affineSpan_simplex _ _)
      have h0 : s.excenter signs -ᵥ s.touchpoint signs i = 0 := by
        rw [← Submodule.mem_bot ℝ,
          ← Submodule.inf_orthogonal_eq_bot (vectorSpan ℝ (Set.range s.points))]
        exact ⟨h', this⟩
      rw [← norm_eq_zero, ← dist_eq_norm_vsub, h.dist_excenter] at h0
      exact h.exradius_pos.ne' h0
    obtain ⟨k, hki, hkj⟩ : ∃ k, k ≠ i ∧ k ≠ j := Fin.exists_ne_and_ne_of_two_lt i j (by lia)
    have hu : Set.range s.points =
        Set.range (s.faceOpposite i).points ∪ Set.range (s.faceOpposite j).points := by
      simp only [range_faceOpposite_points, ← Set.image_union, ← Set.compl_inter]
      convert! Set.image_univ.symm
      simp [Ne.symm hne]
    rw [hu, range_faceOpposite_points, range_faceOpposite_points,
      AffineSubspace.vectorSpan_union_of_mem_of_mem ℝ (p := s.points k)
        (Set.mem_image_of_mem _ (by simp [hki])) (Set.mem_image_of_mem _ (by simp [hkj])),
      ← Submodule.inf_orthogonal]
    refine ⟨?_, ?_⟩
    · rw [← direction_affineSpan, ← range_faceOpposite_points]
      exact vsub_orthogonalProjection_mem_direction_orthogonal _ _
    · rw [hij, ← direction_affineSpan, ← range_faceOpposite_points]
      exact vsub_orthogonalProjection_mem_direction_orthogonal _ _
/-
**Affine.Simplex.touchpoint_empty_injective** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Si
mplex`。
形式化陈述：touchpoint_empty_injective : Function.Injective (s.touchpoint ∅)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.ExcenterExists.touchpoint_injective`：∀ {V : Type u_1} {P 
: Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst
_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.excenterExists_empty`：∀ {V : Type u_1} {P : Type u_2} [in
st : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpac
e P]   [inst_3 : NormedAd…
-/
lemma touchpoint_empty_injective : Function.Injective (s.touchpoint ∅) :=
  s.excenterExists_empty.touchpoint_injective

variable {s} in
/-
**Affine.Simplex.ExcenterExists.touchpoint_notMem_affineSpan_of_ne** 是 Mathlib 中
的一个定理，位于命名空间 `Affine.Simplex.ExcenterExists`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] {s : Affine.Simplex ℝ P n} {signs : Finset (Fin (n + 
1))},   s.ExcenterExists signs →     ∀ {i j : Fin (n + 1)}, i ≠ j → s.touchpoint
 signs i ∉ affineSpan ℝ (Set.range (s.faceOpposite j).points)
参数：Fin (n + 1)；n + 1；Set.range (s.faceOpposite j).points。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `Affine.Simplex.ExcenterExists.touchpoint_injective`：∀ {V : Type u_1} {P 
: Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst
_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `EuclideanGeometry.Sphere.IsTangentAt.eq_of_mem_of_mem`：∀ {V : Type u_1} 
{P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [i
nst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.ExcenterExists.isTangentAt_touchpoint`：∀ {V : Type u_1} {
P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [in
st_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.ExcenterExists.touchpoint_mem_exsphere`：∀ {V : Type u_1} 
{P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [i
nst_2 : MetricSpace P]   [inst_3 : NormedAd…
-/
lemma ExcenterExists.touchpoint_notMem_affineSpan_of_ne {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) {i j : Fin (n + 1)} (hne : i ≠ j) :
    s.touchpoint signs i ∉ affineSpan ℝ (Set.range (s.faceOpposite j).points) :=
  fun hm ↦ h.touchpoint_injective.ne hne
    ((h.isTangentAt_touchpoint j).eq_of_mem_of_mem (h.touchpoint_mem_exsphere i) hm)
/-
**Affine.Simplex.touchpoint_empty_notMem_affineSpan_of_ne** 是 Mathlib 中的一个引理，位于命
名空间 `Affine.Simplex`。
形式化陈述：touchpoint_empty_notMem_affineSpan_of_ne {i j : Fin (n + 1)} (hne : i != j
) : s.touchpoint ∅ i ∉ affineSpan Real (Set.range (s.faceOpposite j).points)
参数：n + 1；hne : i != j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.ExcenterExists.touchpoint_notMem_affineSpan_of_ne`：∀ {V :
 Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSp
ace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.excenterExists_empty`：∀ {V : Type u_1} {P : Type u_2} [in
st : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpac
e P]   [inst_3 : NormedAd…
-/
lemma touchpoint_empty_notMem_affineSpan_of_ne {i j : Fin (n + 1)} (hne : i ≠ j) :
    s.touchpoint ∅ i ∉ affineSpan ℝ (Set.range (s.faceOpposite j).points) :=
  s.excenterExists_empty.touchpoint_notMem_affineSpan_of_ne hne

set_option backward.isDefEq.respectTransparency false in
variable {s} in
/-
**Affine.Simplex.ExcenterExists.sign_signedInfDist_lineMap_excenter_touchpoint**
 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex.ExcenterExists`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] {s : Affine.Simplex ℝ P n} {signs : Finset (Fin (n + 
1))},   s.ExcenterExists signs →     ∀ {i j : Fin (n + 1)},       i ≠ j →       
  ∀ {r : ℝ},           r ∈ Set.Icc 0 1 →             SignType.sign ((s.signedInf
Dist j) ((AffineMap.lineMap (s.excenter signs) (s.touchpoint signs i)) r)) =    
           SignType.sign ((s.signedInfDist j) (s.excenter signs))
参数：Fin (n + 1)；n + 1；(s.signedInfDist j) ((AffineMap.lineMap (s.excenter signs) 
(s.touchpoint signs i)) r)；(s.signedInfDist j) (s.excenter signs)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousOn_of_forall_continuousAt`：continuousOn_of_forall_continuousAt
 (hcont : forall x in s, ContinuousAt f x) : ContinuousOn f s
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用定理 `continuousAt_sign_of_ne_zero`：continuousAt_sign_of_ne_zero {a : α} (h : 
a != 0) : ContinuousAt SignType.sign a
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Affine.Simplex.ExcenterExists.touchpoint_notMem_affineSpan_of_ne`：∀ {V :
 Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSp
ace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineMap.lineMap_apply_one`：lineMap_apply_one (p₀ p₁ : P1) : lineMap p₀
 p₁ (1 : k) = p₁
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanGeometry.dist_orthogonalProjection_eq_zero_iff`：dist_orthogonal
Projection_eq_zero_iff {s : AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrt
hogonalProjection] {p : P} : dist p (orthogon…
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Affine.Simplex.orthogonalProjectionSpan.eq_1`：∀ {𝕜 : Type u_1} {V : Type
 u_2} {P : Type u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup V]   [inst_2
 : InnerProductSpace 𝕜 V] [inst_3 …
· 使用引理 `Affine.Simplex.abs_signedInfDist_eq_dist_of_mem_affineSpan_range`：abs_si
gnedInfDist_eq_dist_of_mem_affineSpan_range {p : P} (h : p in affineSpan Real (S
et.range s.points)) : |s.signedInfDist i p| = dist p (…
· 使用定理 `AffineMap.lineMap_mem`：AffineMap.lineMap_mem {k V P : Type*} [Ring k] [A
ddCommGroup V] [Module k V] [AddTorsor V P] {Q : AffineSubspace k P} {p₀ p₁ : P}
 (c : k) (h…
· 使用定理 `Affine.Simplex.ExcenterExists.excenter_mem_affineSpan_range`：∀ {V : Type
 u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ
 V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用引理 `Affine.Simplex.touchpoint_mem_affineSpan_simplex`：touchpoint_mem_affineS
pan_simplex (signs : Finset (Fin (n + 1))) (i : Fin (n + 1)) : s.touchpoint sign
s i in affineSpan Real (Set.range s.po…
· 使用定理 `abs_eq_zero`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder 
α] [AddLeftMono α] {a : α} [AddRightMono α], |a| = 0 ↔ a = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `EuclideanGeometry.Sphere.IsTangent.notMem_of_dist_lt`：∀ {V : Type u_1} {
P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [in
st_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `EuclideanGeometry.Sphere.IsTangentAt.isTangent`：∀ {V : Type u_1} {P : Ty
pe u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 :
 MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.ExcenterExists.isTangentAt_touchpoint`：∀ {V : Type u_1} {
P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [in
st_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_lineMap_left`：dist_lineMap_left (p₁ p₂ : P) (c : 𝕜) : dist (lineMap
 p₁ p₂ c) p₁ = ‖c‖ * dist p₁ p₂
· 使用定理 `Affine.Simplex.ExcenterExists.dist_excenter`：∀ {V : Type u_1} {P : Type 
u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Me
tricSpace P]   [inst_3 : NormedAd…
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
（共 95 条，此处仅展示前 30 条）
-/
lemma ExcenterExists.sign_signedInfDist_lineMap_excenter_touchpoint {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) {i j : Fin (n + 1)} (hne : i ≠ j) {r : ℝ} (hr : r ∈ Set.Icc 0 1) :
    SignType.sign
      (s.signedInfDist j (AffineMap.lineMap (s.excenter signs) (s.touchpoint signs i) r)) =
      SignType.sign (s.signedInfDist j (s.excenter signs)) := by
  have hc : ContinuousOn (fun (t : ℝ) ↦ SignType.sign
      (s.signedInfDist j (AffineMap.lineMap (s.excenter signs) (s.touchpoint signs i) t)))
      (Set.Icc 0 1) := by
    refine continuousOn_of_forall_continuousAt
      fun t ht ↦ ((continuousAt_sign_of_ne_zero ?_).comp
        (((s.signedInfDist j).cont.comp ?_).continuousAt))
    · intro h0
      rw [← abs_eq_zero, abs_signedInfDist_eq_dist_of_mem_affineSpan_range] at h0
      · rw [orthogonalProjectionSpan, dist_orthogonalProjection_eq_zero_iff] at h0
        by_cases ht1 : t = 1
        · subst ht1
          rw [AffineMap.lineMap_apply_one] at h0
          exact h.touchpoint_notMem_affineSpan_of_ne hne h0
        · refine (h.isTangentAt_touchpoint j).isTangent.notMem_of_dist_lt ?_ h0
          simp only [exsphere_center, dist_lineMap_left, Real.norm_eq_abs, h.dist_excenter,
            exsphere_radius, h.exradius_pos, mul_lt_iff_lt_one_left]
          rw [abs_lt]
          rcases ht with ⟨ht0, ht1'⟩
          exact ⟨by linarith, ht1'.lt_of_ne ht1⟩
      · exact AffineMap.lineMap_mem _ h.excenter_mem_affineSpan_range
          (s.touchpoint_mem_affineSpan_simplex _ _)
    · rw [← ContinuousAffineMap.lineMap_toAffineMap]
      exact ContinuousAffineMap.cont _
  refine ((isConnected_Icc zero_le_one).image _ hc).isPreconnected.subsingleton
    (Set.mem_image_of_mem _ hr) ?_
  convert! Set.mem_image_of_mem _ (Set.left_mem_Icc.2 (zero_le_one' ℝ))
  simp

set_option backward.isDefEq.respectTransparency false in
/-
**Affine.Simplex.sign_signedInfDist_lineMap_incenter_touchpoint** 是 Mathlib 中的一个
引理，位于命名空间 `Affine.Simplex`。
形式化陈述：sign_signedInfDist_lineMap_incenter_touchpoint {i j : Fin (n + 1)} (hne : 
i != j) {r : Real} (hr : r in Set.Icc 0 1) : SignType.sign (s.signedInfDist j (A
ffineMap.lineMap s.incenter (s.touchpoint ∅ i) r)) = SignType.sign (s.signedInfD
ist j s.incenter)
参数：n + 1；hne : i != j；hr : r in Set.Icc 0 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.ExcenterExists.sign_signedInfDist_lineMap_excenter_touchp
oint`：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.excenterExists_empty`：∀ {V : Type u_1} {P : Type u_2} [in
st : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpac
e P]   [inst_3 : NormedAd…
-/
lemma sign_signedInfDist_lineMap_incenter_touchpoint {i j : Fin (n + 1)} (hne : i ≠ j) {r : ℝ}
    (hr : r ∈ Set.Icc 0 1) :
    SignType.sign
      (s.signedInfDist j (AffineMap.lineMap s.incenter (s.touchpoint ∅ i) r)) =
      SignType.sign (s.signedInfDist j s.incenter) :=
  s.excenterExists_empty.sign_signedInfDist_lineMap_excenter_touchpoint hne hr

variable {s} in
/-
**Affine.Simplex.ExcenterExists.sign_signedInfDist_touchpoint** 是 Mathlib 中的一个定理
，位于命名空间 `Affine.Simplex.ExcenterExists`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] {s : Affine.Simplex ℝ P n} {signs : Finset (Fin (n + 
1))},   s.ExcenterExists signs →     ∀ {i j : Fin (n + 1)},       i ≠ j →       
  SignType.sign ((s.signedInfDist j) (s.touchpoint signs i)) =           SignTyp
e.sign ((s.signedInfDist j) (s.excenter signs))
参数：Fin (n + 1)；n + 1；(s.signedInfDist j) (s.touchpoint signs i)；(s.signedInfDist
 j) (s.excenter signs)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Affine.Simplex.ExcenterExists.sign_signedInfDist_lineMap_excenter_touchp
oint`：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AffineMap.lineMap_apply_one`：lineMap_apply_one (p₀ p₁ : P1) : lineMap p₀
 p₁ (1 : k) = p₁
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ExcenterExists.sign_signedInfDist_touchpoint {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) {i j : Fin (n + 1)} (hne : i ≠ j) :
    SignType.sign (s.signedInfDist j (s.touchpoint signs i)) =
      SignType.sign (s.signedInfDist j (s.excenter signs)) := by
  rw [← h.sign_signedInfDist_lineMap_excenter_touchpoint hne (r := 1) ⟨zero_le_one, le_rfl⟩]
  simp
/-
**Affine.Simplex.sign_signedInfDist_touchpoint_empty** 是 Mathlib 中的一个引理，位于命名空间 `
Affine.Simplex`。
形式化陈述：sign_signedInfDist_touchpoint_empty {i j : Fin (n + 1)} (hne : i != j) : S
ignType.sign (s.signedInfDist j (s.touchpoint ∅ i)) = SignType.sign (s.signedInf
Dist j s.incenter)
参数：n + 1；hne : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.ExcenterExists.sign_signedInfDist_touchpoint`：∀ {V : Type
 u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ
 V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.excenterExists_empty`：∀ {V : Type u_1} {P : Type u_2} [in
st : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpac
e P]   [inst_3 : NormedAd…
-/
lemma sign_signedInfDist_touchpoint_empty {i j : Fin (n + 1)} (hne : i ≠ j) :
    SignType.sign (s.signedInfDist j (s.touchpoint ∅ i)) =
      SignType.sign (s.signedInfDist j s.incenter) :=
  s.excenterExists_empty.sign_signedInfDist_touchpoint hne

/-- The unique weights of the vertices in an affine combination equal to the given touchpoint. -/
/-
**Affine.Simplex.touchpointWeights** 是 Mathlib 中的一个定义，位于命名空间 `Affine.Simplex`。
形式化陈述：touchpointWeights (signs : Finset (Fin (n + 1))) (i : Fin (n + 1)) : Fin (
n + 1) -> Real
参数：signs : Finset (Fin (n + 1))；i : Fin (n + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unique weights of the vertices in an affine combination equal to the given t
ouchpoint.
-/
def touchpointWeights (signs : Finset (Fin (n + 1))) (i : Fin (n + 1)) : Fin (n + 1) → ℝ :=
  (eq_affineCombination_of_mem_affineSpan_of_fintype
    (s.touchpoint_mem_affineSpan_simplex signs i)).choose
/-
**Affine.Simplex.sum_touchpointWeights** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex
`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] (s : Affine.Simplex ℝ P n) (signs : Finset (Fin (n + 
1)))   (i : Fin (n + 1)), ∑ j, s.touchpointWeights signs i j = 1
参数：s : Affine.Simplex ℝ P n；signs : Finset (Fin (n + 1))；i : Fin (n + 1)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_affineCombination_of_mem_affineSpan_of_fintype`：eq_affineCombination_
of_mem_affineSpan_of_fintype [Fintype ι] {p1 : P} {p : ι -> P} (h : p1 in affine
Span k (Set.range p)) : exists w : ι ->…
· 使用引理 `Affine.Simplex.touchpoint_mem_affineSpan_simplex`：touchpoint_mem_affineS
pan_simplex (signs : Finset (Fin (n + 1))) (i : Fin (n + 1)) : s.touchpoint sign
s i in affineSpan Real (Set.range s.po…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
@[simp] lemma sum_touchpointWeights (signs : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    ∑ j, s.touchpointWeights signs i j = 1 :=
  (eq_affineCombination_of_mem_affineSpan_of_fintype
    (s.touchpoint_mem_affineSpan_simplex signs i)).choose_spec.1
/-
**Affine.Simplex.affineCombination_touchpointWeights** 是 Mathlib 中的一个定理，位于命名空间 `
Affine.Simplex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] (s : Affine.Simplex ℝ P n) (signs : Finset (Fin (n + 
1)))   (i : Fin (n + 1)),   (Finset.affineCombination ℝ Finset.univ s.points) (s
.touchpointWeights signs i) = s.touchpoint signs i
参数：s : Affine.Simplex ℝ P n；signs : Finset (Fin (n + 1))；i : Fin (n + 1)；Finset.
affineCombination ℝ Finset.univ s.points；s.touchpointWeights signs i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_affineCombination_of_mem_affineSpan_of_fintype`：eq_affineCombination_
of_mem_affineSpan_of_fintype [Fintype ι] {p1 : P} {p : ι -> P} (h : p1 in affine
Span k (Set.range p)) : exists w : ι ->…
· 使用引理 `Affine.Simplex.touchpoint_mem_affineSpan_simplex`：touchpoint_mem_affineS
pan_simplex (signs : Finset (Fin (n + 1))) (i : Fin (n + 1)) : s.touchpoint sign
s i in affineSpan Real (Set.range s.po…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
@[simp] lemma affineCombination_touchpointWeights (signs : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    Finset.univ.affineCombination ℝ s.points (s.touchpointWeights signs i) = s.touchpoint signs i :=
  (eq_affineCombination_of_mem_affineSpan_of_fintype
    (s.touchpoint_mem_affineSpan_simplex signs i)).choose_spec.2.symm

variable {s} in
/-
**Affine.Simplex.affineCombination_eq_touchpoint_iff** 是 Mathlib 中的一个定理，位于命名空间 `
Affine.Simplex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] {s : Affine.Simplex ℝ P n} {signs : Finset (Fin (n + 
1))}   {i : Fin (n + 1)} {w : Fin (n + 1) → ℝ},   ∑ j, w j = 1 →     ((Finset.af
fineCombination ℝ Finset.univ s.points) w = s.touchpoint signs i ↔ w = s.touchpo
intWeights signs i)
参数：Fin (n + 1)；n + 1；n + 1；(Finset.affineCombination ℝ Finset.univ s.points) w =
 s.touchpoint signs i ↔ w = s.touchpointWeights signs i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Affine.Simplex.affineCombination_touchpointWeights`：∀ {V : Type u_1} {P 
: Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst
_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `affineIndependent_iff_eq_of_fintype_affineCombination_eq`：affineIndepend
ent_iff_eq_of_fintype_affineCombination_eq [Fintype ι] (p : ι -> P) : AffineInde
pendent k p ↔ forall w1 w2 : ι -> k, ∑ i, w1 i…
· 使用定理 `Affine.Simplex.independent`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [ins
t_3 : AddTorsor …
· 使用定理 `Affine.Simplex.sum_touchpointWeights`：∀ {V : Type u_1} {P : Type u_2} [i
nst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpa
ce P]   [inst_3 : NormedAd…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma affineCombination_eq_touchpoint_iff {signs : Finset (Fin (n + 1))} {i : Fin (n + 1)}
    {w : Fin (n + 1) → ℝ} (hw : ∑ j, w j = 1) :
    Finset.univ.affineCombination ℝ s.points w = s.touchpoint signs i ↔
      w = s.touchpointWeights signs i := by
  constructor
  · rw [← s.affineCombination_touchpointWeights]
    exact fun h ↦ (affineIndependent_iff_eq_of_fintype_affineCombination_eq ℝ s.points).1
      s.independent _ _ hw (s.sum_touchpointWeights _ _) h
  · rintro rfl
    simp
/-
**Affine.Simplex.touchpointWeights_reindex** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Sim
plex`。
形式化陈述：touchpointWeights_reindex (e : Fin (n + 1) ≃ Fin (m + 1)) (signs : Finset 
(Fin (m + 1))) (i : Fin (m + 1)) : (s.reindex e).touchpointWeights signs i = s.t
ouchpointWeights (signs.map e.symm) (e.symm i) ∘ e.symm
参数：e : Fin (n + 1) ≃ Fin (m + 1)；signs : Finset (Fin (m + 1))；i : Fin (m + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Affine.Simplex.affineCombination_eq_touchpoint_iff`：∀ {V : Type u_1} {P 
: Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst
_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Finset.sum_comp_equiv`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} {s
 : Finset ι} [inst : AddCommMonoid M] {f : κ → M} (e : ι ≃ κ),   s.sum (f ∘ ⇑e) 
= (Finset.m…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.map_univ_equiv`：map_univ_equiv [Fintype β] (f : β ≃ α) : univ.map
 f.toEmbedding = univ
· 使用定理 `Affine.Simplex.sum_touchpointWeights`：∀ {V : Type u_1} {P : Type u_2} [i
nst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpa
ce P]   [inst_3 : NormedAd…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Affine.Simplex.touchpoint_reindex`：touchpoint_reindex (e : Fin (n + 1) ≃
 Fin (m + 1)) (signs : Finset (Fin (m + 1))) (i : Fin (m + 1)) : (s.reindex e).t
ouchpoint signs i = s.t…
· 使用定理 `Affine.Simplex.affineCombination_touchpointWeights`：∀ {V : Type u_1} {P 
: Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst
_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.reindex.eq_1`：∀ {k : Type u_1} {V : Type u_2} {P : Type u
_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [in
st_3 : AddTorsor …
· 使用定理 `Equiv.coe_toEmbedding`：coe_toEmbedding : (f.toEmbedding : α -> β) = f
· 使用定理 `Finset.affineCombination_map`：affineCombination_map (e : ι₂ ↪ ι) (w : ι 
-> k) (p : ι -> P) : (s₂.map e).affineCombination k p w = s₂.affineCombination k
 (p ∘ e) (w ∘ e)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
lemma touchpointWeights_reindex (e : Fin (n + 1) ≃ Fin (m + 1)) (signs : Finset (Fin (m + 1)))
    (i : Fin (m + 1)) :
    (s.reindex e).touchpointWeights signs i =
      s.touchpointWeights (signs.map e.symm) (e.symm i) ∘ e.symm := by
  rw [eq_comm, ← affineCombination_eq_touchpoint_iff]
  · rw [touchpoint_reindex, ← affineCombination_touchpointWeights, reindex]
    dsimp only
    rw [← Equiv.coe_toEmbedding, ← Finset.affineCombination_map]
    simp
  · rw [Finset.sum_comp_equiv]
    simp

variable {s} in
/-
**Affine.Simplex.ExcenterExists.touchpointWeights_map** 是 Mathlib 中的一个定理，位于命名空间 
`Affine.Simplex.ExcenterExists`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
V₂ : Type u_3} {P₂ : Type u_4} [inst_4 : NormedAddCommGroup V₂]   [inst_5 : Inne
rProductSpace ℝ V₂] [inst_6 : MetricSpace P₂] [inst_7 : NormedAddTorsor V₂ P₂] {
n : ℕ}   [inst_8 : NeZero n] {s : Affine.Simplex ℝ P n} {signs : Finset (Fin (n 
+ 1))},   s.ExcenterExists signs →     ∀ (f : P →ᵃⁱ[ℝ] P₂), (s.map f.toAffineMap
 ⋯).touchpointWeights signs = s.touchpointWeights signs
参数：Fin (n + 1)；f : P →ᵃⁱ[ℝ] P₂；s.map f.toAffineMap ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AffineIsometry.injective`：∀ {𝕜 : Type u_1} {V₁' : Type u_4} {V₂ : Type u
_5} {P₁' : Type u_9} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : Seminor
medAddCommGrou…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Affine.Simplex.affineCombination_eq_touchpoint_iff`：∀ {V : Type u_1} {P 
: Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst
_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.sum_touchpointWeights`：∀ {V : Type u_1} {P : Type u_2} [i
nst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpa
ce P]   [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.affineCombination_touchpointWeights`：∀ {V : Type u_1} {P 
: Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst
_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `AffineIsometry.map_eq_iff`：map_eq_iff {x y : P₁'} : f₁ x = f₁ y ↔ x = y
· 使用定理 `AffineIsometry.coe_toAffineMap`：coe_toAffineMap : ⇑f.toAffineMap = f
· 使用定理 `Finset.map_affineCombination`：map_affineCombination {V₂ P₂ : Type*} [Add
CommGroup V₂] [Module k V₂] [AffineSpace V₂ P₂] (p : ι -> P) (w : ι -> k) (hw : 
s.sum w = 1) (f : …
· 使用定理 `Affine.Simplex.map_points`：∀ {k : Type u_1} {V : Type u_2} {V₂ : Type u_
3} {P : Type u_5} {P₂ : Type u_6} [inst : Ring k] [inst_1 : AddCommGroup V]   [i
nst_2 : AddComm…
· 使用定理 `Affine.Simplex.ExcenterExists.touchpoint_map`：∀ {V : Type u_1} {P : Type
 u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : M
etricSpace P]   [inst_3 : NormedAd…
-/
@[simp] lemma ExcenterExists.touchpointWeights_map {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) (f : P →ᵃⁱ[ℝ] P₂) :
    (s.map f.toAffineMap f.injective).touchpointWeights signs = s.touchpointWeights signs := by
  ext i : 1
  rw [← affineCombination_eq_touchpoint_iff
    ((s.map f.toAffineMap f.injective).sum_touchpointWeights _ _)]
  have hc := (s.map f.toAffineMap f.injective).affineCombination_touchpointWeights signs i
  rwa [h.touchpoint_map, map_points, ← Finset.univ.map_affineCombination _ _
    ((s.map f.toAffineMap f.injective).sum_touchpointWeights _ _), AffineIsometry.coe_toAffineMap,
    AffineIsometry.map_eq_iff] at hc

variable {s} in
/-
**Affine.Simplex.ExcenterExists.touchpointWeights_restrict** 是 Mathlib 中的一个定理，位于
命名空间 `Affine.Simplex.ExcenterExists`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] {s : Affine.Simplex ℝ P n} {signs : Finset (Fin (n + 
1))},   s.ExcenterExists signs →     ∀ (S : AffineSubspace ℝ P) (hS : affineSpan
 ℝ (Set.range s.points) ≤ S),       (s.restrict S hS).touchpointWeights signs = 
s.touchpointWeights signs
参数：Fin (n + 1)；S : AffineSubspace ℝ P；hS : affineSpan ℝ (Set.range s.points) ≤ S
；s.restrict S hS。
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
· 使用定理 `AffineIsometry.injective`：∀ {𝕜 : Type u_1} {V₁' : Type u_4} {V₂ : Type u
_5} {P₁' : Type u_9} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : Seminor
medAddCommGrou…
· 使用定理 `Affine.Simplex.ExcenterExists.touchpointWeights_map`：∀ {V : Type u_1} {P
 : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [ins
t_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.excenterExists_restrict`：∀ {V : Type u_1} {P : Type u_2} 
[inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricS
pace P]   [inst_3 : NormedAd…
-/
@[simp] lemma ExcenterExists.touchpointWeights_restrict {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) (S : AffineSubspace ℝ P)
    (hS : affineSpan ℝ (Set.range s.points) ≤ S) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).touchpointWeights signs = s.touchpointWeights signs := by
  rw [← s.excenterExists_restrict S hS] at h
  have := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  exact (h.touchpointWeights_map S.subtypeₐᵢ).symm

variable {s} in
/-
**Affine.Simplex.ExcenterExists.sign_touchpointWeights** 是 Mathlib 中的一个定理，位于命名空间
 `Affine.Simplex.ExcenterExists`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] {s : Affine.Simplex ℝ P n} {signs : Finset (Fin (n + 
1))},   s.ExcenterExists signs →     ∀ {i j : Fin (n + 1)},       i ≠ j → SignTy
pe.sign (s.touchpointWeights signs i j) = SignType.sign (s.excenterWeights signs
 j)
参数：Fin (n + 1)；n + 1；s.touchpointWeights signs i j；s.excenterWeights signs j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.ExcenterExists.sign_signedInfDist_touchpoint`：∀ {V : Type
 u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ
 V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Affine.Simplex.signedInfDist_affineCombination`：signedInfDist_affineComb
ination {w : Fin (n + 1) -> Real} (h : ∑ i, w i = 1) : s.signedInfDist i (Finset
.univ.affineCombination Real s.point…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Affine.Simplex.sum_touchpointWeights`：∀ {V : Type u_1} {P : Type u_2} [i
nst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpa
ce P]   [inst_3 : NormedAd…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Affine.Simplex.ExcenterExists.sign_signedInfDist_excenter`：∀ {V : Type u
_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V
] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.affineCombination_touchpointWeights`：∀ {V : Type u_1} {P 
: Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst
_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `sign_mul`：sign_mul (x y : α) : sign (x * y) = sign x * sign y
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `sign_eq_one_iff`：sign_eq_one_iff : sign a = 1 ↔ 0 < a
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用引理 `Affine.Simplex.height_pos`：height_pos {n : Nat} [NeZero n] (s : Simplex 
Real P n) (i : Fin (n + 1)) : 0 < s.height i
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma ExcenterExists.sign_touchpointWeights {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) {i j : Fin (n + 1)} (hne : i ≠ j) :
    SignType.sign (s.touchpointWeights signs i j) = SignType.sign (s.excenterWeights signs j) := by
  have hs := h.sign_signedInfDist_touchpoint hne
  rw [← s.affineCombination_touchpointWeights signs i, h.sign_signedInfDist_excenter,
    s.signedInfDist_affineCombination j (by simp)] at hs
  rw [← hs, sign_mul]
  convert! (mul_one _).symm
  rw [sign_eq_one_iff, ← dist_eq_norm_vsub]
  exact s.height_pos _
/-
**Affine.Simplex.sign_touchpointWeights_empty** 是 Mathlib 中的一个引理，位于命名空间 `Affine.
Simplex`。
形式化陈述：sign_touchpointWeights_empty {i j : Fin (n + 1)} (hne : i != j) : SignType
.sign (s.touchpointWeights ∅ i j) = 1
参数：n + 1；hne : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.ExcenterExists.sign_touchpointWeights`：∀ {V : Type u_1} {
P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [in
st_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.excenterExists_empty`：∀ {V : Type u_1} {P : Type u_2} [in
st : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpac
e P]   [inst_3 : NormedAd…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Affine.Simplex.sign_excenterWeights_empty`：sign_excenterWeights_empty (i
 : Fin (n + 1)) : SignType.sign (s.excenterWeights ∅ i) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sign_touchpointWeights_empty {i j : Fin (n + 1)} (hne : i ≠ j) :
    SignType.sign (s.touchpointWeights ∅ i j) = 1 := by
  rw [s.excenterExists_empty.sign_touchpointWeights hne]
  simp

variable {s} in
/-
**Affine.Simplex.touchpointWeights_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Sim
plex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] {s : Affine.Simplex ℝ P n} {signs : Finset (Fin (n + 
1))}   (i : Fin (n + 1)), s.touchpointWeights signs i i = 0
参数：Fin (n + 1)；i : Fin (n + 1)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AffineIndependent.eq_zero_of_affineCombination_mem_affineSpan`：AffineInd
ependent.eq_zero_of_affineCombination_mem_affineSpan {p : ι -> P} (ha : AffineIn
dependent k p) {fs : Finset ι} {w : ι -> k} (hw : ∑…
· 使用定理 `Affine.Simplex.independent`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [ins
t_3 : AddTorsor …
· 使用定理 `Affine.Simplex.sum_touchpointWeights`：∀ {V : Type u_1} {P : Type u_2} [i
nst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpa
ce P]   [inst_3 : NormedAd…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.affineCombination_touchpointWeights`：∀ {V : Type u_1} {P 
: Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst
_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Affine.Simplex.range_faceOpposite_points`：∀ {k : Type u_1} {V : Type u_2
} {P : Type u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Modu
le k V]   [inst_3 : AddTorsor …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Affine.Simplex.touchpoint_mem_affineSpan`：touchpoint_mem_affineSpan (sig
ns : Finset (Fin (n + 1))) (i : Fin (n + 1)) : s.touchpoint signs i in affineSpa
n Real (Set.range (s.faceOppos…
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.notMem_compl_iff`：notMem_compl_iff {x : α} : x ∉ sᶜ ↔ x in s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
-/
@[simp] lemma touchpointWeights_eq_zero {signs : Finset (Fin (n + 1))} (i : Fin (n + 1)) :
    s.touchpointWeights signs i i = 0 := by
  refine s.independent.eq_zero_of_affineCombination_mem_affineSpan
    (s.sum_touchpointWeights signs i) ?_ (Finset.mem_univ _)
    (Set.notMem_compl_iff.2 (Set.mem_singleton _))
  rw [s.affineCombination_touchpointWeights]
  convert! s.touchpoint_mem_affineSpan _ _
  simp
/-
**Affine.Simplex.touchpointWeights_empty_pos** 是 Mathlib 中的一个引理，位于命名空间 `Affine.S
implex`。
形式化陈述：touchpointWeights_empty_pos {i j : Fin (n + 1)} (hne : i != j) : 0 < s.tou
chpointWeights ∅ i j
参数：n + 1；hne : i != j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Affine.Simplex.sign_touchpointWeights_empty`：sign_touchpointWeights_empt
y {i j : Fin (n + 1)} (hne : i != j) : SignType.sign (s.touchpointWeights ∅ i j)
 = 1
-/
lemma touchpointWeights_empty_pos {i j : Fin (n + 1)} (hne : i ≠ j) :
    0 < s.touchpointWeights ∅ i j := by
  simpa [sign_eq_one_iff] using s.sign_touchpointWeights_empty hne

attribute [local instance] Nat.AtLeastTwo.neZero_sub_one
/-
**Affine.Simplex.touchpoint_empty_mem_interior_faceOpposite** 是 Mathlib 中的一个引理，位
于命名空间 `Affine.Simplex`。
形式化陈述：touchpoint_empty_mem_interior_faceOpposite [Nat.AtLeastTwo n] (i : Fin (n 
+ 1)) : s.touchpoint ∅ i in (s.faceOpposite i).interior
参数：i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.faceOpposite.eq_1`：∀ {k : Type u_1} {V : Type u_2} {P : T
ype u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V] 
  [inst_3 : AddTorsor …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Affine.Simplex.affineCombination_touchpointWeights`：∀ {V : Type u_1} {P 
: Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst
_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用引理 `Affine.Simplex.affineCombination_mem_interior_face_iff_pos`：affineCombin
ation_mem_interior_face_iff_pos [IsOrderedAddMonoid k] {n : Nat} (s : Simplex k 
P n) {fs : Finset (Fin (n + 1))} {m : Nat} [NeZe…
· 使用引理 `Nat.AtLeastTwo.neZero_sub_one`：neZero_sub_one : NeZero (n - 1)
· 使用定理 `Affine.Simplex.sum_touchpointWeights`：∀ {V : Type u_1} {P : Type u_2} [i
nst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpa
ce P]   [inst_3 : NormedAd…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Affine.Simplex.touchpointWeights_eq_zero`：∀ {V : Type u_1} {P : Type u_2
} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Metri
cSpace P]   [inst_3 : NormedAd…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用引理 `Affine.Simplex.touchpointWeights_empty_pos`：touchpointWeights_empty_pos 
{i j : Fin (n + 1)} (hne : i != j) : 0 < s.touchpointWeights ∅ i j
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
lemma touchpoint_empty_mem_interior_faceOpposite [Nat.AtLeastTwo n] (i : Fin (n + 1)) :
    s.touchpoint ∅ i ∈ (s.faceOpposite i).interior := by
  rw [faceOpposite, ← affineCombination_touchpointWeights,
    s.affineCombination_mem_interior_face_iff_pos _ (s.sum_touchpointWeights _ _)]
  simp only [Finset.mem_compl, Finset.mem_singleton, Decidable.not_not, forall_eq,
    touchpointWeights_eq_zero, and_true]
  intro j hj
  exact s.touchpointWeights_empty_pos (Ne.symm hj)
/-
**Affine.Simplex.sign_touchpointWeights_singleton_pos** 是 Mathlib 中的一个引理，位于命名空间 
`Affine.Simplex`。
形式化陈述：sign_touchpointWeights_singleton_pos [Nat.AtLeastTwo n] {i j : Fin (n + 1)
} (hne : i != j) : SignType.sign (s.touchpointWeights {i} i j) = 1
参数：n + 1；hne : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.ExcenterExists.sign_touchpointWeights`：∀ {V : Type u_1} {
P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [in
st_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用引理 `Affine.Simplex.excenterExists_singleton`：excenterExists_singleton [Nat.A
tLeastTwo n] (i : Fin (n + 1)) : s.ExcenterExists {i}
· 使用引理 `Affine.Simplex.sign_excenterWeights_singleton_pos`：sign_excenterWeights_
singleton_pos [Nat.AtLeastTwo n] {i j : Fin (n + 1)} (h : i != j) : SignType.sig
n (s.excenterWeights {i} j) = 1
-/
lemma sign_touchpointWeights_singleton_pos [Nat.AtLeastTwo n] {i j : Fin (n + 1)} (hne : i ≠ j) :
    SignType.sign (s.touchpointWeights {i} i j) = 1 := by
  rw [(s.excenterExists_singleton i).sign_touchpointWeights hne,
    s.sign_excenterWeights_singleton_pos hne]
/-
**Affine.Simplex.touchpointWeights_singleton_pos** 是 Mathlib 中的一个引理，位于命名空间 `Affi
ne.Simplex`。
形式化陈述：touchpointWeights_singleton_pos [Nat.AtLeastTwo n] {i j : Fin (n + 1)} (hn
e : i != j) : 0 < s.touchpointWeights {i} i j
参数：n + 1；hne : i != j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Affine.Simplex.sign_touchpointWeights_singleton_pos`：sign_touchpointWeig
hts_singleton_pos [Nat.AtLeastTwo n] {i j : Fin (n + 1)} (hne : i != j) : SignTy
pe.sign (s.touchpointWeights {i} i j) = 1
-/
lemma touchpointWeights_singleton_pos [Nat.AtLeastTwo n] {i j : Fin (n + 1)} (hne : i ≠ j) :
    0 < s.touchpointWeights {i} i j := by
  simpa [sign_eq_one_iff] using s.sign_touchpointWeights_singleton_pos hne
/-
**Affine.Simplex.touchpoint_singleton_mem_interior_faceOpposite** 是 Mathlib 中的一个
引理，位于命名空间 `Affine.Simplex`。
形式化陈述：touchpoint_singleton_mem_interior_faceOpposite [Nat.AtLeastTwo n] (i : Fin
 (n + 1)) : s.touchpoint {i} i in (s.faceOpposite i).interior
参数：i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.faceOpposite.eq_1`：∀ {k : Type u_1} {V : Type u_2} {P : T
ype u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V] 
  [inst_3 : AddTorsor …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Affine.Simplex.affineCombination_touchpointWeights`：∀ {V : Type u_1} {P 
: Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst
_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用引理 `Affine.Simplex.affineCombination_mem_interior_face_iff_pos`：affineCombin
ation_mem_interior_face_iff_pos [IsOrderedAddMonoid k] {n : Nat} (s : Simplex k 
P n) {fs : Finset (Fin (n + 1))} {m : Nat} [NeZe…
· 使用引理 `Nat.AtLeastTwo.neZero_sub_one`：neZero_sub_one : NeZero (n - 1)
· 使用定理 `Affine.Simplex.sum_touchpointWeights`：∀ {V : Type u_1} {P : Type u_2} [i
nst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpa
ce P]   [inst_3 : NormedAd…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Affine.Simplex.touchpointWeights_eq_zero`：∀ {V : Type u_1} {P : Type u_2
} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Metri
cSpace P]   [inst_3 : NormedAd…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用引理 `Affine.Simplex.touchpointWeights_singleton_pos`：touchpointWeights_single
ton_pos [Nat.AtLeastTwo n] {i j : Fin (n + 1)} (hne : i != j) : 0 < s.touchpoint
Weights {i} i j
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
lemma touchpoint_singleton_mem_interior_faceOpposite [Nat.AtLeastTwo n] (i : Fin (n + 1)) :
    s.touchpoint {i} i ∈ (s.faceOpposite i).interior := by
  rw [faceOpposite, ← affineCombination_touchpointWeights,
    s.affineCombination_mem_interior_face_iff_pos _ (s.sum_touchpointWeights _ _)]
  simp only [Finset.mem_compl, Finset.mem_singleton, Decidable.not_not, forall_eq,
    touchpointWeights_eq_zero, and_true]
  intro j hj
  exact s.touchpointWeights_singleton_pos (Ne.symm hj)
/-
**Affine.Simplex.sign_touchpointWeights_singleton_neg** 是 Mathlib 中的一个引理，位于命名空间 
`Affine.Simplex`。
形式化陈述：sign_touchpointWeights_singleton_neg [Nat.AtLeastTwo n] {i j : Fin (n + 1)
} (hne : i != j) : SignType.sign (s.touchpointWeights {i} j i) = -1
参数：n + 1；hne : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.ExcenterExists.sign_touchpointWeights`：∀ {V : Type u_1} {
P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [in
st_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用引理 `Affine.Simplex.excenterExists_singleton`：excenterExists_singleton [Nat.A
tLeastTwo n] (i : Fin (n + 1)) : s.ExcenterExists {i}
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `Affine.Simplex.sign_excenterWeights_singleton_neg`：sign_excenterWeights_
singleton_neg [Nat.AtLeastTwo n] (i : Fin (n + 1)) : SignType.sign (s.excenterWe
ights {i} i) = -1
-/
lemma sign_touchpointWeights_singleton_neg [Nat.AtLeastTwo n] {i j : Fin (n + 1)} (hne : i ≠ j) :
    SignType.sign (s.touchpointWeights {i} j i) = -1 := by
  rw [(s.excenterExists_singleton i).sign_touchpointWeights hne.symm,
    s.sign_excenterWeights_singleton_neg]
/-
**Affine.Simplex.touchpointWeights_singleton_neg** 是 Mathlib 中的一个引理，位于命名空间 `Affi
ne.Simplex`。
形式化陈述：touchpointWeights_singleton_neg [Nat.AtLeastTwo n] {i j : Fin (n + 1)} (hn
e : i != j) : s.touchpointWeights {i} j i < 0
参数：n + 1；hne : i != j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Affine.Simplex.sign_touchpointWeights_singleton_neg`：sign_touchpointWeig
hts_singleton_neg [Nat.AtLeastTwo n] {i j : Fin (n + 1)} (hne : i != j) : SignTy
pe.sign (s.touchpointWeights {i} j i) = -…
-/
lemma touchpointWeights_singleton_neg [Nat.AtLeastTwo n] {i j : Fin (n + 1)} (hne : i ≠ j) :
    s.touchpointWeights {i} j i < 0 := by
  simpa [sign_eq_neg_one_iff] using s.sign_touchpointWeights_singleton_neg hne

variable {s} in
/-
**Affine.Simplex.ExcenterExists.touchpoint_ne_point** 是 Mathlib 中的一个定理，位于命名空间 `A
ffine.Simplex.ExcenterExists`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] {s : Affine.Simplex ℝ P n} [n.AtLeastTwo]   {signs : 
Finset (Fin (n + 1))}, s.ExcenterExists signs → ∀ (i j : Fin (n + 1)), s.touchpo
int signs i ≠ s.points j
参数：Fin (n + 1)；i j : Fin (n + 1)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.AtLeastTwo.one_lt`：one_lt : 1 < n
· 使用定理 `Fin.exists_ne_and_ne_of_two_lt`：exists_ne_and_ne_of_two_lt (i j : Fin n)
 (h : 2 < n) : exists k, k != i ∧ k != j
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.affineCombination_eq_touchpoint_iff`：∀ {V : Type u_1} {P 
: Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst
_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Fintype.sum_pi_single'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommM
onoid M] [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (i : ι) (a : M),   ∑ j, P
i.single i a…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.affineCombination_piSingle`：affineCombination_piSingle [Decidable
Eq ι] (p : ι -> P) {i : ι} (hi : i in s) : s.affineCombination k p (Pi.single i 
1) = p i
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `Affine.Simplex.height_pos`：height_pos {n : Nat} [NeZero n] (s : Simplex 
Real P n) (i : Fin (n + 1)) : 0 < s.height i
· 使用定理 `Affine.Simplex.excenterWeightsUnnorm.eq_1`：∀ {V : Type u_1} {P : Type u_
2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Metr
icSpace P]   [inst_3 : NormedAd…
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Affine.Simplex.ExcenterExists.eq_1`：∀ {V : Type u_1} {P : Type u_2} [ins
t : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace
 P]   [inst_3 : NormedAd…
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Affine.Simplex.excenterWeights.eq_1`：∀ {V : Type u_1} {P : Type u_2} [in
st : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpac
e P]   [inst_3 : NormedAd…
· 使用定理 `sign_eq_zero_iff`：sign_eq_zero_iff : sign a = 0 ↔ a = 0
· 使用定理 `Affine.Simplex.ExcenterExists.sign_touchpointWeights`：∀ {V : Type u_1} {
P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [in
st_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `sign_zero`：sign_zero : sign (0 : α) = 0
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
-/
lemma ExcenterExists.touchpoint_ne_point [Nat.AtLeastTwo n] {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) (i j : Fin (n + 1)) : s.touchpoint signs i ≠ s.points j := by
  intro he
  rw [eq_comm, ← Finset.univ.affineCombination_piSingle ℝ s.points (Finset.mem_univ _),
    affineCombination_eq_touchpoint_iff (Fintype.sum_pi_single' _ _)] at he
  have : 1 < n := Nat.AtLeastTwo.one_lt
  obtain ⟨k, hki, hkj⟩ : ∃ k, k ≠ i ∧ k ≠ j := Fin.exists_ne_and_ne_of_two_lt i j (by lia)
  have he' := congr(SignType.sign ($he k))
  rw [Pi.single_eq_of_ne hkj, sign_zero, eq_comm, h.sign_touchpointWeights hki.symm,
    sign_eq_zero_iff, excenterWeights] at he'
  rw [ExcenterExists] at h
  simp only [Pi.smul_apply, smul_eq_mul, mul_eq_zero, inv_eq_zero, h, false_or] at he'
  rw [excenterWeightsUnnorm] at he'
  by_cases hk : k ∈ signs <;> simp [hk, (s.height_pos k).ne'] at he'
/-
**Affine.Simplex.touchpoint_empty_ne_point** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Sim
plex`。
形式化陈述：touchpoint_empty_ne_point [Nat.AtLeastTwo n] (i j : Fin (n + 1)) : s.touch
point ∅ i != s.points j
参数：i j : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.ExcenterExists.touchpoint_ne_point`：∀ {V : Type u_1} {P :
 Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_
2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.excenterExists_empty`：∀ {V : Type u_1} {P : Type u_2} [in
st : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpac
e P]   [inst_3 : NormedAd…
-/
lemma touchpoint_empty_ne_point [Nat.AtLeastTwo n] (i j : Fin (n + 1)) :
    s.touchpoint ∅ i ≠ s.points j :=
  s.excenterExists_empty.touchpoint_ne_point i j

end Simplex

namespace Triangle

variable (t : Triangle ℝ P)

/-- All excenters exist for a triangle. -/
/-
**Affine.Triangle.excenterExists** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Triangle`。
形式化陈述：excenterExists (signs : Finset (Fin 3)) : t.ExcenterExists signs
参数：signs : Finset (Fin 3)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Affine.Simplex.excenterExists_empty`：∀ {V : Type u_1} {P : Type u_2} [in
st : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpac
e P]   [inst_3 : NormedAd…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.excenterExists_compl`：∀ {V : Type u_1} {P : Type u_2} [in
st : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpac
e P]   [inst_3 : NormedAd…
· 使用引理 `Affine.Simplex.excenterExists_singleton`：excenterExists_singleton [Nat.A
tLeastTwo n] (i : Fin (n + 1)) : s.ExcenterExists {i}
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo

--- 原说明 ---
All excenters exist for a triangle.
-/
lemma excenterExists (signs : Finset (Fin 3)) : t.ExcenterExists signs := by
  have h : signs = ∅ ∨ signs = ∅ᶜ ∨ ∃ i, signs = {i} ∨ signs = {i}ᶜ := by decide +revert
  rcases h with rfl | rfl | ⟨i, rfl | rfl⟩
  · exact t.excenterExists_empty
  · rw [Simplex.excenterExists_compl]
    exact t.excenterExists_empty
  · exact t.excenterExists_singleton _
  · rw [Simplex.excenterExists_compl]
    exact t.excenterExists_singleton _

/-- An excenter of a triangle is either the incenter or the excenter opposite a vertex. -/
/-
**Affine.Triangle.excenter_eq_incenter_or_excenter_singleton** 是 Mathlib 中的一个引理，
位于命名空间 `Affine.Triangle`。
形式化陈述：excenter_eq_incenter_or_excenter_singleton (signs : Finset (Fin 3)) : t.ex
center signs = t.incenter ∨ exists i, t.excenter signs = t.excenter {i}
参数：signs : Finset (Fin 3)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Affine.Simplex.excenter_univ`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.excenter_compl`：∀ {V : Type u_1} {P : Type u_2} [inst : N
ormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]  
 [inst_3 : NormedAd…

--- 原说明 ---
An excenter of a triangle is either the incenter or the excenter opposite a vert
ex.
-/
lemma excenter_eq_incenter_or_excenter_singleton (signs : Finset (Fin 3)) :
    t.excenter signs = t.incenter ∨ ∃ i, t.excenter signs = t.excenter {i} := by
  have h : signs = ∅ ∨ signs = Finset.univ ∨ ∃ i, signs = {i} ∨ signs = {i}ᶜ := by decide +revert
  rcases h with rfl | rfl | ⟨i, rfl | rfl⟩
  · exact .inl rfl
  · exact .inl t.excenter_univ
  · exact .inr ⟨i, rfl⟩
  · refine .inr ⟨i, ?_⟩
    rw [t.excenter_compl]

/-- An excenter of a triangle is either the incenter or the excenter opposite one of three
enumerated different vertices. This is intended for when it is known a point is an excenter and
it is to be proved which excenter it is by elimination of the other cases. -/
/-
**Affine.Triangle.excenter_eq_incenter_or_excenter_singleton_of_ne** 是 Mathlib 中
的一个引理，位于命名空间 `Affine.Triangle`。
形式化陈述：excenter_eq_incenter_or_excenter_singleton_of_ne (signs : Finset (Fin 3)) 
{i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) : t.excent
er signs = t.incenter ∨ t.excenter signs = t.excenter {i₁} ∨ t.excenter signs = 
t.excenter {i₂} ∨ t.excenter signs = t.excenter {i₃}
参数：signs : Finset (Fin 3)；h₁₂ : i₁ != i₂；h₁₃ : i₁ != i₃；h₂₃ : i₂ != i₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Affine.Triangle.excenter_eq_incenter_or_excenter_singleton`：excenter_eq_
incenter_or_excenter_singleton (signs : Finset (Fin 3)) : t.excenter signs = t.i
ncenter ∨ exists i, t.excenter signs = t.excente…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p

--- 原说明 ---
An excenter of a triangle is either the incenter or the excenter opposite one of
 three
enumerated different vertices. This is intended for when it is known a point is 
an excenter and
it is to be proved which excenter it is by elimination of the other cases.
-/
lemma excenter_eq_incenter_or_excenter_singleton_of_ne (signs : Finset (Fin 3)) {i₁ i₂ i₃ : Fin 3}
    (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    t.excenter signs = t.incenter ∨ t.excenter signs = t.excenter {i₁} ∨
      t.excenter signs = t.excenter {i₂} ∨ t.excenter signs = t.excenter {i₃} := by
  rcases t.excenter_eq_incenter_or_excenter_singleton signs with h | ⟨i, h⟩
  · exact .inl h
  · refine .inr ?_
    rw [h]
    have : i = i₁ ∨ i = i₂ ∨ i = i₃ := by clear h; decide +revert
    grind
/-
**Affine.Triangle.sSameSide_affineSpan_pair_incenter_point** 是 Mathlib 中的一个引理，位于
命名空间 `Affine.Triangle`。
形式化陈述：sSameSide_affineSpan_pair_incenter_point {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i
₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) : line[Real, t.points i₂, t.points i₃].SSam
eSide t.incenter (t.points i₁)
参数：h₁₂ : i₁ != i₂；h₁₃ : i₁ != i₃；h₂₃ : i₂ != i₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.range_faceOpposite_points`：∀ {k : Type u_1} {V : Type u_2
} {P : Type u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Modu
le k V]   [inst_3 : AddTorsor …
· 使用引理 `Affine.Simplex.sSameSide_incenter_point`：sSameSide_incenter_point (i : F
in (n + 1)) : (affineSpan Real (Set.range (s.faceOpposite i).points)).SSameSide 
s.incenter (s.points i)
-/
lemma sSameSide_affineSpan_pair_incenter_point {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃)
    (h₂₃ : i₂ ≠ i₃) :
    line[ℝ, t.points i₂, t.points i₃].SSameSide t.incenter (t.points i₁) := by
  convert! t.sSameSide_incenter_point i₁
  simp
  grind
/-
**Affine.Triangle.sSameSide_affineSpan_pair_point_incenter** 是 Mathlib 中的一个引理，位于
命名空间 `Affine.Triangle`。
形式化陈述：sSameSide_affineSpan_pair_point_incenter {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i
₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) : line[Real, t.points i₂, t.points i₃].SSam
eSide (t.points i₁) t.incenter
参数：h₁₂ : i₁ != i₂；h₁₃ : i₁ != i₃；h₂₃ : i₂ != i₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.range_faceOpposite_points`：∀ {k : Type u_1} {V : Type u_2
} {P : Type u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Modu
le k V]   [inst_3 : AddTorsor …
· 使用引理 `Affine.Simplex.sSameSide_point_incenter`：sSameSide_point_incenter (i : F
in (n + 1)) : (affineSpan Real (Set.range (s.faceOpposite i).points)).SSameSide 
(s.points i) s.incenter
-/
lemma sSameSide_affineSpan_pair_point_incenter {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃)
    (h₂₃ : i₂ ≠ i₃) :
    line[ℝ, t.points i₂, t.points i₃].SSameSide (t.points i₁) t.incenter := by
  convert! t.sSameSide_point_incenter i₁
  simp
  grind
/-
**Affine.Triangle.sOppSide_affineSpan_pair_excenter_singleton_point** 是 Mathlib 
中的一个引理，位于命名空间 `Affine.Triangle`。
形式化陈述：sOppSide_affineSpan_pair_excenter_singleton_point {i₁ i₂ i₃ : Fin 3} (h₁₂ 
: i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) : line[Real, t.points i₂, t.points
 i₃].SOppSide (t.excenter {i₁}) (t.points i₁)
参数：h₁₂ : i₁ != i₂；h₁₃ : i₁ != i₃；h₂₃ : i₂ != i₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.range_faceOpposite_points`：∀ {k : Type u_1} {V : Type u_2
} {P : Type u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Modu
le k V]   [inst_3 : AddTorsor …
· 使用引理 `Affine.Simplex.sOppSide_excenter_singleton_point`：sOppSide_excenter_sing
leton_point [Nat.AtLeastTwo n] (i : Fin (n + 1)) : (affineSpan Real (Set.range (
s.faceOpposite i).points)).SOppSide (s…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
-/
lemma sOppSide_affineSpan_pair_excenter_singleton_point {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂)
    (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    line[ℝ, t.points i₂, t.points i₃].SOppSide (t.excenter {i₁}) (t.points i₁) := by
  convert! t.sOppSide_excenter_singleton_point i₁
  simp
  grind
/-
**Affine.Triangle.sOppSide_affineSpan_pair_point_excenter_singleton** 是 Mathlib 
中的一个引理，位于命名空间 `Affine.Triangle`。
形式化陈述：sOppSide_affineSpan_pair_point_excenter_singleton {i₁ i₂ i₃ : Fin 3} (h₁₂ 
: i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) : line[Real, t.points i₂, t.points
 i₃].SOppSide (t.points i₁) (t.excenter {i₁})
参数：h₁₂ : i₁ != i₂；h₁₃ : i₁ != i₃；h₂₃ : i₂ != i₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.range_faceOpposite_points`：∀ {k : Type u_1} {V : Type u_2
} {P : Type u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Modu
le k V]   [inst_3 : AddTorsor …
· 使用引理 `Affine.Simplex.sOppSide_point_excenter_singleton`：sOppSide_point_excente
r_singleton [Nat.AtLeastTwo n] (i : Fin (n + 1)) : (affineSpan Real (Set.range (
s.faceOpposite i).points)).SOppSide (s…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
-/
lemma sOppSide_affineSpan_pair_point_excenter_singleton {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂)
    (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    line[ℝ, t.points i₂, t.points i₃].SOppSide (t.points i₁) (t.excenter {i₁}) := by
  convert! t.sOppSide_point_excenter_singleton i₁
  simp
  grind
/-
**Affine.Triangle.sSameSide_affineSpan_pair_excenter_singleton_point** 是 Mathlib
 中的一个引理，位于命名空间 `Affine.Triangle`。
形式化陈述：sSameSide_affineSpan_pair_excenter_singleton_point {i₁ i₂ i₃ : Fin 3} (h₁₂
 : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) : line[Real, t.points i₂, t.point
s i₃].SSameSide (t.excenter {i₂}) (t.points i₁)
参数：h₁₂ : i₁ != i₂；h₁₃ : i₁ != i₃；h₂₃ : i₂ != i₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.range_faceOpposite_points`：∀ {k : Type u_1} {V : Type u_2
} {P : Type u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Modu
le k V]   [inst_3 : AddTorsor …
· 使用引理 `Affine.Simplex.sSameSide_excenter_singleton_point`：sSameSide_excenter_si
ngleton_point [Nat.AtLeastTwo n] {i j : Fin (n + 1)} (h : i != j) : (affineSpan 
Real (Set.range (s.faceOpposite i).poin…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
-/
lemma sSameSide_affineSpan_pair_excenter_singleton_point {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂)
    (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    line[ℝ, t.points i₂, t.points i₃].SSameSide (t.excenter {i₂}) (t.points i₁) := by
  convert! t.sSameSide_excenter_singleton_point h₁₂
  simp
  grind
/-
**Affine.Triangle.sSameSide_affineSpan_pair_point_excenter_singleton** 是 Mathlib
 中的一个引理，位于命名空间 `Affine.Triangle`。
形式化陈述：sSameSide_affineSpan_pair_point_excenter_singleton {i₁ i₂ i₃ : Fin 3} (h₁₂
 : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) : line[Real, t.points i₂, t.point
s i₃].SSameSide (t.points i₁) (t.excenter {i₂})
参数：h₁₂ : i₁ != i₂；h₁₃ : i₁ != i₃；h₂₃ : i₂ != i₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.range_faceOpposite_points`：∀ {k : Type u_1} {V : Type u_2
} {P : Type u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Modu
le k V]   [inst_3 : AddTorsor …
· 使用引理 `Affine.Simplex.sSameSide_point_excenter_singleton`：sSameSide_point_excen
ter_singleton [Nat.AtLeastTwo n] {i j : Fin (n + 1)} (h : i != j) : (affineSpan 
Real (Set.range (s.faceOpposite i).poin…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
-/
lemma sSameSide_affineSpan_pair_point_excenter_singleton {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂)
    (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    line[ℝ, t.points i₂, t.points i₃].SSameSide (t.points i₁) (t.excenter {i₂}) := by
  convert! t.sSameSide_point_excenter_singleton h₁₂
  simp
  grind
/-
**Affine.Triangle.affineSpan_pair_eq_orthRadius** 是 Mathlib 中的一个引理，位于命名空间 `Affin
e.Triangle`。
形式化陈述：affineSpan_pair_eq_orthRadius [Fact (Module.finrank Real V = 2)] (signs : 
Finset (Fin 3)) {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ !
= i₃) : line[Real, t.points i₂, t.points i₃] = (t.exsphere signs).orthRadius (t.
touchpoint signs i₁)
参数：Module.finrank Real V = 2；signs : Finset (Fin 3)；h₁₂ : i₁ != i₂；h₁₃ : i₁ != i
₃；h₂₃ : i₂ != i₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.range_faceOpposite_points`：∀ {k : Type u_1} {V : Type u_2
} {P : Type u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Modu
le k V]   [inst_3 : AddTorsor …
· 使用定理 `Set.image_insert_eq`：image_insert_eq {f : α -> β} {a : α} {s : Set α} : 
f '' insert a s = insert (f a) (f '' s)
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Affine.Simplex.ExcenterExists.affineSpan_faceOpposite_eq_orthRadius`：∀ {
V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProduc
tSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用引理 `Affine.Triangle.excenterExists`：excenterExists (signs : Finset (Fin 3)) 
: t.ExcenterExists signs
-/
lemma affineSpan_pair_eq_orthRadius [Fact (Module.finrank ℝ V = 2)] (signs : Finset (Fin 3))
    {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    line[ℝ, t.points i₂, t.points i₃] =
      (t.exsphere signs).orthRadius (t.touchpoint signs i₁) := by
  convert! (t.excenterExists signs).affineSpan_faceOpposite_eq_orthRadius i₁
  have hc : {i₁}ᶜ = ({i₂, i₃} : Set (Fin 3)) := by grind
  simp [Simplex.range_faceOpposite_points, hc, Set.image_insert_eq]
/-
**Affine.Triangle.affineSpan_pair_eq_orthRadius_insphere** 是 Mathlib 中的一个引理，位于命名
空间 `Affine.Triangle`。
形式化陈述：affineSpan_pair_eq_orthRadius_insphere [Fact (Module.finrank Real V = 2)] 
{i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) : line[Rea
l, t.points i₂, t.points i₃] = t.insphere.orthRadius (t.touchpoint ∅ i₁)
参数：Module.finrank Real V = 2；h₁₂ : i₁ != i₂；h₁₃ : i₁ != i₃；h₂₃ : i₂ != i₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Affine.Triangle.affineSpan_pair_eq_orthRadius`：affineSpan_pair_eq_orthRa
dius [Fact (Module.finrank Real V = 2)] (signs : Finset (Fin 3)) {i₁ i₂ i₃ : Fin
 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i…
-/
lemma affineSpan_pair_eq_orthRadius_insphere [Fact (Module.finrank ℝ V = 2)]
    {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    line[ℝ, t.points i₂, t.points i₃] = t.insphere.orthRadius (t.touchpoint ∅ i₁) :=
  t.affineSpan_pair_eq_orthRadius ∅ h₁₂ h₁₃ h₂₃
/-
**Affine.Triangle.sbtw_touchpoint_empty** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Triang
le`。
形式化陈述：sbtw_touchpoint_empty {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃)
 (h₂₃ : i₂ != i₃) : Sbtw Real (t.points i₁) (t.touchpoint ∅ i₂) (t.points i₃)
参数：h₁₂ : i₁ != i₂；h₁₃ : i₁ != i₃；h₂₃ : i₂ != i₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Finset.card_pair`：∀ {α : Type u_1} {a b : α} [inst : DecidableEq α], a ≠
 b → {a, b}.card = 2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Affine.Simplex.mem_interior_face_iff_sbtw`：mem_interior_face_iff_sbtw [I
sDomain R] [IsTorsionFree R V] {n : Nat} (s : Simplex R P n) {p : P} {i j : Fin 
(n + 1)} (h : i != j) : p in (s…
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Affine.Simplex.faceOpposite.eq_1`：∀ {k : Type u_1} {V : Type u_2} {P : T
ype u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V] 
  [inst_3 : AddTorsor …
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用引理 `Affine.Simplex.touchpoint_empty_mem_interior_faceOpposite`：touchpoint_em
pty_mem_interior_faceOpposite [Nat.AtLeastTwo n] (i : Fin (n + 1)) : s.touchpoin
t ∅ i in (s.faceOpposite i).interior
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
-/
lemma sbtw_touchpoint_empty {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    Sbtw ℝ (t.points i₁) (t.touchpoint ∅ i₂) (t.points i₃) := by
  rw [← t.mem_interior_face_iff_sbtw h₁₃]
  convert! t.touchpoint_empty_mem_interior_faceOpposite i₂
  rw [Affine.Simplex.faceOpposite]
  convert! rfl using 2
  decide +revert
/-
**Affine.Triangle.sbtw_touchpoint_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Tr
iangle`。
形式化陈述：sbtw_touchpoint_singleton {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ !=
 i₃) (h₂₃ : i₂ != i₃) : Sbtw Real (t.points i₁) (t.touchpoint {i₂} i₂) (t.points
 i₃)
参数：h₁₂ : i₁ != i₂；h₁₃ : i₁ != i₃；h₂₃ : i₂ != i₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Finset.card_pair`：∀ {α : Type u_1} {a b : α} [inst : DecidableEq α], a ≠
 b → {a, b}.card = 2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Affine.Simplex.mem_interior_face_iff_sbtw`：mem_interior_face_iff_sbtw [I
sDomain R] [IsTorsionFree R V] {n : Nat} (s : Simplex R P n) {p : P} {i j : Fin 
(n + 1)} (h : i != j) : p in (s…
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Affine.Simplex.faceOpposite.eq_1`：∀ {k : Type u_1} {V : Type u_2} {P : T
ype u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V] 
  [inst_3 : AddTorsor …
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用引理 `Affine.Simplex.touchpoint_singleton_mem_interior_faceOpposite`：touchpoin
t_singleton_mem_interior_faceOpposite [Nat.AtLeastTwo n] (i : Fin (n + 1)) : s.t
ouchpoint {i} i in (s.faceOpposite i).interior
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
-/
lemma sbtw_touchpoint_singleton {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    Sbtw ℝ (t.points i₁) (t.touchpoint {i₂} i₂) (t.points i₃) := by
  rw [← t.mem_interior_face_iff_sbtw h₁₃]
  convert! t.touchpoint_singleton_mem_interior_faceOpposite i₂
  rw [Affine.Simplex.faceOpposite]
  convert! rfl using 2
  decide +revert
/-
**Affine.Triangle.touchpoint_singleton_sbtw** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Tr
iangle`。
形式化陈述：touchpoint_singleton_sbtw {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ !=
 i₃) (h₂₃ : i₂ != i₃) : Sbtw Real (t.touchpoint {i₁} i₂) (t.points i₃) (t.points
 i₁)
参数：h₁₂ : i₁ != i₂；h₁₃ : i₁ != i₃；h₂₃ : i₂ != i₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Affine.Simplex.affineCombination_touchpointWeights`：∀ {V : Type u_1} {P 
: Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst
_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.sum_touchpointWeights`：∀ {V : Type u_1} {P : Type u_2} [i
nst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpa
ce P]   [inst_3 : NormedAd…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Finset.affineCombinationLineMapWeights_apply_left`：affineCombinationLine
MapWeights_apply_left [DecidableEq ι] {i j : ι} (h : i != j) (c : k) : affineCom
binationLineMapWeights i j c i = 1 - c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Affine.Simplex.touchpointWeights_eq_zero`：∀ {V : Type u_1} {P : Type u_2
} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Metri
cSpace P]   [inst_3 : NormedAd…
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Finset.affineCombinationLineMapWeights_apply_of_ne`：affineCombinationLin
eMapWeights_apply_of_ne [DecidableEq ι] {i j t : ι} (hi : t != i) (hj : t != j) 
(c : k) : affineCombinationLineMapWeight…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Finset.affineCombinationLineMapWeights_apply_right`：affineCombinationLin
eMapWeights_apply_right [DecidableEq ι] {i j : ι} (h : i != j) (c : k) : affineC
ombinationLineMapWeights i j c j = c
· 使用定理 `Finset.affineCombination_affineCombinationLineMapWeights`：affineCombinat
ion_affineCombinationLineMapWeights [DecidableEq ι] (p : ι -> P) {i j : ι} (hi :
 i in s) (hj : j in s) (c : k) : s.affineCombi…
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `sbtw_iff_right_ne_and_left_mem_image_Ioi`：sbtw_iff_right_ne_and_left_mem
_image_Ioi {x y z : P} : Sbtw R x y z ↔ z != y ∧ x in lineMap z y '' Set.Ioi (1 
: R)
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `AffineIndependent.injective`：∀ {k : Type u_1} {V : Type u_2} {P : Type u
_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [in
st_3 : AddTorsor …
（共 47 条，此处仅展示前 30 条）
-/
lemma touchpoint_singleton_sbtw {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    Sbtw ℝ (t.touchpoint {i₁} i₂) (t.points i₃) (t.points i₁) := by
  rw [← Affine.Simplex.affineCombination_touchpointWeights]
  have hw := t.sum_touchpointWeights {i₁} i₂
  rw [(by clear hw; decide +revert : (Finset.univ : Finset (Fin 3)) = {i₁, i₂, i₃})] at hw
  simp only [Nat.reduceAdd, Finset.mem_insert, h₁₂, Finset.mem_singleton, h₁₃, or_self,
    not_false_eq_true, Finset.sum_insert, h₂₃, Simplex.touchpointWeights_eq_zero,
    Finset.sum_singleton, zero_add] at hw
  have h : t.touchpointWeights {i₁} i₂ =
      Finset.affineCombinationLineMapWeights i₁ i₃ (t.touchpointWeights {i₁} i₂ i₃) := by
    ext i
    have h : i = i₁ ∨ i = i₂ ∨ i = i₃ := by clear hw; decide +revert
    rcases h with rfl | rfl | rfl
    · rw [Finset.affineCombinationLineMapWeights_apply_left h₁₃]
      simp [← hw]
    · simp [h₁₂.symm, h₂₃]
    · simp [h₁₃]
  rw [h, Finset.univ.affineCombination_affineCombinationLineMapWeights _ (Finset.mem_univ _)
    (Finset.mem_univ _), sbtw_iff_right_ne_and_left_mem_image_Ioi]
  simp [t.independent.injective.ne h₁₃, ← hw, t.touchpointWeights_singleton_neg h₁₂]

end Triangle

end Affine

