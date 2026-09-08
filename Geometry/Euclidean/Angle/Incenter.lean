/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Geometry.Euclidean.Angle.Bisector
public import Mathlib.Geometry.Euclidean.Incenter

/-!
# Angles and incenters and excenters.

This file proves lemmas relating incenters and excenters of a simplex to angle bisection.

-/

public section


open EuclideanGeometry Module
open scoped Real

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P]

namespace Affine

namespace Simplex

variable {n : ℕ} [NeZero n] (s : Simplex ℝ P n)

variable {s} in
/-- An excenter of a simplex bisects the angle at a point shared between two faces, as measured
between that excenter and its touchpoints on those faces. -/
/-
**Affine.Simplex.ExcenterExists.angle_excenter_touchpoint_eq** 是 Mathlib 中的一个定理，
位于命名空间 `Affine.Simplex.ExcenterExists`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] {s : Affine.Simplex ℝ P n} {signs : Finset (Fin (n + 
1))},   s.ExcenterExists signs →     ∀ {p : P} {i₁ i₂ : Fin (n + 1)},       p ∈ 
affineSpan ℝ (Set.range (s.faceOpposite i₁).points) →         p ∈ affineSpan ℝ (
Set.range (s.faceOpposite i₂).points) →           EuclideanGeometry.angle (s.exc
enter signs) p (s.touchpoint signs i₁) =             EuclideanGeometry.angle (s.
excenter signs) p (s.touchpoint signs i₂)
参数：Fin (n + 1)；n + 1；Set.range (s.faceOpposite i₁).points；Set.range (s.faceOppos
ite i₂).points；s.excenter signs；s.touchpoint signs i₁；s.excenter signs；s.touchpo
int signs i₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `EuclideanGeometry.dist_orthogonalProjection_eq_iff_angle_eq`：dist_orthog
onalProjection_eq_iff_angle_eq {p p' : P} {s₁ s₂ : AffineSubspace Real P} [s₁.di
rection.HasOrthogonalProjection] [s₂.direction.Ha…
· 使用定理 `Affine.Simplex.ExcenterExists.dist_excenter_eq_dist_excenter`：∀ {V : Typ
e u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace 
ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…

--- 原说明 ---
An excenter of a simplex bisects the angle at a point shared between two faces, 
as measured
between that excenter and its touchpoints on those faces.
-/
lemma ExcenterExists.angle_excenter_touchpoint_eq {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) {p : P} {i₁ i₂ : Fin (n + 1)}
    (hp₁ : p ∈ affineSpan ℝ (Set.range (s.faceOpposite i₁).points))
    (hp₂ : p ∈ affineSpan ℝ (Set.range (s.faceOpposite i₂).points)) :
    ∠ (s.excenter signs) p (s.touchpoint signs i₁) =
      ∠ (s.excenter signs) p (s.touchpoint signs i₂) :=
  (dist_orthogonalProjection_eq_iff_angle_eq hp₁ hp₂).1 (h.dist_excenter_eq_dist_excenter i₁ i₂)

variable {s} in
/-- The incenter of a simplex bisects the angle at a point shared between two faces, as measured
between the incenter and its touchpoints on those faces. -/
/-
**Affine.Simplex.angle_incenter_touchpoint_eq** 是 Mathlib 中的一个引理，位于命名空间 `Affine.
Simplex`。
形式化陈述：angle_incenter_touchpoint_eq {p : P} {i₁ i₂ : Fin (n + 1)} (hp₁ : p in aff
ineSpan Real (Set.range (s.faceOpposite i₁).points)) (hp₂ : p in affineSpan Real
 (Set.range (s.faceOpposite i₂).points)) : ∠ s.incenter p (s.touchpoint ∅ i₁) = 
∠ s.incenter p (s.touchpoint ∅ i₂)
参数：n + 1；hp₁ : p in affineSpan Real (Set.range (s.faceOpposite i₁).points)；hp₂ :
 p in affineSpan Real (Set.range (s.faceOpposite i₂).points)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.ExcenterExists.angle_excenter_touchpoint_eq`：∀ {V : Type 
u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ 
V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.excenterExists_empty`：∀ {V : Type u_1} {P : Type u_2} [in
st : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpac
e P]   [inst_3 : NormedAd…

--- 原说明 ---
The incenter of a simplex bisects the angle at a point shared between two faces,
 as measured
between the incenter and its touchpoints on those faces.
-/
lemma angle_incenter_touchpoint_eq {p : P} {i₁ i₂ : Fin (n + 1)}
    (hp₁ : p ∈ affineSpan ℝ (Set.range (s.faceOpposite i₁).points))
    (hp₂ : p ∈ affineSpan ℝ (Set.range (s.faceOpposite i₂).points)) :
    ∠ s.incenter p (s.touchpoint ∅ i₁) =
      ∠ s.incenter p (s.touchpoint ∅ i₂) :=
  s.excenterExists_empty.angle_excenter_touchpoint_eq hp₁ hp₂

variable {s} in
/-- Given a face of a simplex, if a point bisects the angle between that face and each other face,
as measured at points shared between those faces between that point and its projections onto the
faces, that point is an excenter of the simplex. -/
/-
**Affine.Simplex.exists_excenterExists_and_eq_excenter_of_forall_angle_orthogona
lProjectionSpan_eq** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simplex`。
形式化陈述：exists_excenterExists_and_eq_excenter_of_forall_angle_orthogonalProjection
Span_eq {p : P} (hp : p in affineSpan Real (Set.range s.points)) {i₁ : Fin (n + 
1)} (h : forall i₂, i₂ != i₁ -> exists p' : P, p' in affineSpan Real (Set.range 
(s.faceOpposite i₁).points) ∧ p' in affineSpan Real (Set.range (s.faceOpposite i
₂).points) ∧ ∠ p p' ((s.faceOpposite i₁).orthogonalProjectionSpan p) = ∠ p p' ((
s.faceOpposite i₂).orthogonalProjectionSpan p)) : exists signs, s.ExcenterExists
 signs ∧ p = s.excenter si
参数：hp : p in affineSpan Real (Set.range s.points)；n + 1；h : forall i₂, i₂ != i₁ 
-> exists p' : P, p' in affineSpan Real (Set.range (s.faceOpposite i₁).points) ∧
 p' in affineSpan Real (Set.range (s.faceOpposite i₂).points) ∧ ∠ p p' ((s.faceO
pposite i₁).orthogonalProjectionSpan p) = ∠ p p' ((s.faceOpposite i₂).orthogonal
ProjectionSpan p)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Affine.Simplex.exists_forall_dist_eq_iff_exists_excenterExists_and_eq_ex
center`：exists_forall_dist_eq_iff_exists_excenterExists_and_eq_excenter {p : P} 
(hp : p in affineSpan Real (Set.range s.points)) : (exists r : Real,…
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `EuclideanGeometry.dist_orthogonalProjection_eq_iff_angle_eq`：dist_orthog
onalProjection_eq_iff_angle_eq {p p' : P} {s₁ s₂ : AffineSubspace Real P} [s₁.di
rection.HasOrthogonalProjection] [s₂.direction.Ha…

--- 原说明 ---
Given a face of a simplex, if a point bisects the angle between that face and ea
ch other face,
as measured at points shared between those faces between that point and its proj
ections onto the
faces, that point is an excenter of the simplex.
-/
lemma exists_excenterExists_and_eq_excenter_of_forall_angle_orthogonalProjectionSpan_eq {p : P}
    (hp : p ∈ affineSpan ℝ (Set.range s.points)) {i₁ : Fin (n + 1)}
    (h : ∀ i₂, i₂ ≠ i₁ → ∃ p' : P, p' ∈ affineSpan ℝ (Set.range (s.faceOpposite i₁).points) ∧
      p' ∈ affineSpan ℝ (Set.range (s.faceOpposite i₂).points) ∧
      ∠ p p' ((s.faceOpposite i₁).orthogonalProjectionSpan p) =
        ∠ p p' ((s.faceOpposite i₂).orthogonalProjectionSpan p)) :
    ∃ signs, s.ExcenterExists signs ∧ p = s.excenter signs := by
  rw [← s.exists_forall_dist_eq_iff_exists_excenterExists_and_eq_excenter hp]
  refine ⟨dist p ((s.faceOpposite i₁).orthogonalProjectionSpan p), ?_⟩
  intro i
  by_cases hi : i = i₁
  · rw [hi]
  obtain ⟨p', hp'₁, hp'₂, ha⟩ := h i hi
  exact ((dist_orthogonalProjection_eq_iff_angle_eq hp'₁ hp'₂).2 ha).symm

end Simplex

namespace Triangle

open Simplex

variable [hd2 : Fact (finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]
variable (t : Triangle ℝ P) {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃)
include h₁₂ h₁₃ h₂₃

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable {t} in
/-- A point `p` is equidistant to two sides of a triangle if and only if the oriented angles at
their common vertex are equal modulo `π`. -/
/-
**Affine.Triangle.dist_orthogonalProjectionSpan_faceOpposite_eq_iff_two_zsmul_oa
ngle_eq** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Triangle`。
形式化陈述：dist_orthogonalProjectionSpan_faceOpposite_eq_iff_two_zsmul_oangle_eq {p :
 P} : dist p ((t.faceOpposite i₃).orthogonalProjectionSpan p) = dist p ((t.faceO
pposite i₂).orthogonalProjectionSpan p) ↔ (2 : Int) • ∡ (t.points i₂) (t.points 
i₁) p = (2 : Int) • ∡ p (t.points i₁) (t.points i₃)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib_1`：∀ (n : ℕ) [NeZero n], NeZero 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `eq_false_of_decide`：∀ {p : Prop} {x : Decidable p}, decide p = false → p
 = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AffineIndependent.comp_embedding`：AffineIndependent.comp_embedding {ι2 :
 Type*} (f : ι2 ↪ ι) {p : ι -> P} (ha : AffineIndependent k p) : AffineIndepende
nt k (p ∘ f)
· 使用定理 `Affine.Simplex.independent`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [ins
t_3 : AddTorsor …
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Affine.Simplex.orthogonalProjectionSpan.eq_1`：∀ {𝕜 : Type u_1} {V : Type
 u_2} {P : Type u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup V]   [inst_2
 : InnerProductSpace 𝕜 V] [inst_3 …
· 使用定理 `Set.instNonemptyElemInsert`：∀ {α : Type u_1} (a : α) (s : Set α), Nonemp
ty ↑(insert a s)
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用引理 `EuclideanGeometry.dist_orthogonalProjection_line_eq_iff_two_zsmul_oangle
_eq`：dist_orthogonalProjection_line_eq_iff_two_zsmul_oangle_eq {p p₁ p₂ p₃ : P} 
(ha : AffineIndependent Real ![p₁, p₂, p₃]) : dist p (orthogonalP…
· 使用定理 `Affine.Simplex.range_faceOpposite_points`：∀ {k : Type u_1} {V : Type u_2
} {P : Type u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Modu
le k V]   [inst_3 : AddTorsor …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
A point `p` is equidistant to two sides of a triangle if and only if the oriente
d angles at
their common vertex are equal modulo `π`.
-/
lemma dist_orthogonalProjectionSpan_faceOpposite_eq_iff_two_zsmul_oangle_eq {p : P} :
    dist p ((t.faceOpposite i₃).orthogonalProjectionSpan p) =
      dist p ((t.faceOpposite i₂).orthogonalProjectionSpan p) ↔
        (2 : ℤ) • ∡ (t.points i₂) (t.points i₁) p = (2 : ℤ) • ∡ p (t.points i₁) (t.points i₃) := by
  have ha : AffineIndependent ℝ ![t.points i₁, t.points i₂, t.points i₃] := by
    convert!
      t.independent.comp_embedding
        ⟨![i₁, i₂, i₃], by
          intro i j hij
          fin_cases i <;> fin_cases j <;> simp_all⟩
    ext i
    fin_cases i <;> rfl
  rw [orthogonalProjectionSpan, orthogonalProjectionSpan,
    ← dist_orthogonalProjection_line_eq_iff_two_zsmul_oangle_eq ha]
  simp only [range_faceOpposite_points]
  simp_rw [(by grind : ({i₃}ᶜ : Set (Fin 3)) = {i₁, i₂}),
    (by grind : ({i₂}ᶜ : Set (Fin 3)) = {i₁, i₃}), Set.image_insert_eq, Set.image_singleton]

/-- An excenter of a triangle bisects the angle at a vertex modulo `π`. -/
/-
**Affine.Triangle.two_zsmul_oangle_excenter_eq** 是 Mathlib 中的一个引理，位于命名空间 `Affine
.Triangle`。
形式化陈述：two_zsmul_oangle_excenter_eq (signs : Finset (Fin 3)) : (2 : Int) • ∡ (t.p
oints i₂) (t.points i₁) (t.excenter signs) = (2 : Int) • ∡ (t.excenter signs) (t
.points i₁) (t.points i₃)
参数：signs : Finset (Fin 3)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Affine.Triangle.dist_orthogonalProjectionSpan_faceOpposite_eq_iff_two_zs
mul_oangle_eq`：dist_orthogonalProjectionSpan_faceOpposite_eq_iff_two_zsmul_oangl
e_eq {p : P} : dist p ((t.faceOpposite i₃).orthogonalProjectionSpan p) = di…
· 使用定理 `Affine.Simplex.touchpoint.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : 
NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] 
  [inst_3 : NormedAd…
· 使用定理 `Affine.Simplex.ExcenterExists.dist_excenter_eq_dist_excenter`：∀ {V : Typ
e u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace 
ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用引理 `Affine.Triangle.excenterExists`：excenterExists (signs : Finset (Fin 3)) 
: t.ExcenterExists signs

--- 原说明 ---
An excenter of a triangle bisects the angle at a vertex modulo `π`.
-/
lemma two_zsmul_oangle_excenter_eq (signs : Finset (Fin 3)) :
    (2 : ℤ) • ∡ (t.points i₂) (t.points i₁) (t.excenter signs) =
      (2 : ℤ) • ∡ (t.excenter signs) (t.points i₁) (t.points i₃) := by
  rw [← dist_orthogonalProjectionSpan_faceOpposite_eq_iff_two_zsmul_oangle_eq h₁₂ h₁₃ h₂₃,
    ← touchpoint, ← touchpoint, (t.excenterExists signs).dist_excenter_eq_dist_excenter]

/-- The incenter of a triangle bisects the angle at a vertex. -/
/-
**Affine.Triangle.oangle_incenter_eq** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Triangle`
。
形式化陈述：oangle_incenter_eq : ∡ (t.points i₂) (t.points i₁) t.incenter = ∡ t.incent
er (t.points i₁) (t.points i₃)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Sbtw.oangle_eq_left`：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCo
mmGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 :
 NormedAd…
· 使用引理 `Affine.Triangle.sbtw_touchpoint_empty`：sbtw_touchpoint_empty {i₁ i₂ i₃ :
 Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) : Sbtw Real (t.points
 i₁) (t.touchpoint ∅ i₂) (t…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Sbtw.oangle_eq_right`：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddC
ommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 
: NormedAd…
· 使用引理 `Affine.Simplex.dist_incenter_eq_dist_incenter`：dist_incenter_eq_dist_inc
enter (i₁ i₂ : Fin (n + 1)) : dist s.incenter (s.touchpoint ∅ i₁) = dist s.incen
ter (s.touchpoint ∅ i₂)
· 使用引理 `EuclideanGeometry.oangle_eq_of_dist_orthogonalProjection_eq`：oangle_eq_o
f_dist_orthogonalProjection_eq {p p' : P} {s₁ s₂ : AffineSubspace Real P} (hp'₁ 
: p' in s₁) (hp'₂ : p' in s₂) : haveI : Nonempty …
· 使用定理 `mem_affineSpan`：mem_affineSpan {p : P} {s : Set P} (hp : p in s) : p in 
affineSpan k s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Affine.Simplex.range_faceOpposite_points`：∀ {k : Type u_1} {V : Type u_2
} {P : Type u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Modu
le k V]   [inst_3 : AddTorsor …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用引理 `Affine.Simplex.touchpoint_empty_injective`：touchpoint_empty_injective : 
Function.Injective (s.touchpoint ∅)

--- 原说明 ---
The incenter of a triangle bisects the angle at a vertex.
-/
lemma oangle_incenter_eq :
    ∡ (t.points i₂) (t.points i₁) t.incenter = ∡ t.incenter (t.points i₁) (t.points i₃) := by
  rw [← (t.sbtw_touchpoint_empty h₁₃ h₁₂ h₂₃.symm).oangle_eq_left,
    ← (t.sbtw_touchpoint_empty h₁₂ h₁₃ h₂₃).oangle_eq_right]
  have hd := t.dist_incenter_eq_dist_incenter i₃ i₂
  simp_rw [touchpoint, orthogonalProjectionSpan] at hd ⊢
  refine oangle_eq_of_dist_orthogonalProjection_eq (mem_affineSpan _ ?_) (mem_affineSpan _ ?_)
    (t.touchpoint_empty_injective.ne h₂₃.symm) hd
  · simp
    grind
  · simp
    grind

/-- The excenter of a triangle opposite a vertex bisects the angle at that vertex. -/
/-
**Affine.Triangle.oangle_excenter_singleton_eq** 是 Mathlib 中的一个引理，位于命名空间 `Affine
.Triangle`。
形式化陈述：oangle_excenter_singleton_eq : ∡ (t.points i₂) (t.points i₁) (t.excenter {
i₁}) = ∡ (t.excenter {i₁}) (t.points i₁) (t.points i₃)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sbtw.oangle_eq_left`：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCo
mmGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 :
 NormedAd…
· 使用定理 `Sbtw.symm`：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Ring R
] [inst_1 : PartialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module…
· 使用引理 `Affine.Triangle.touchpoint_singleton_sbtw`：touchpoint_singleton_sbtw {i₁
 i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) : Sbtw Real (
t.touchpoint {i₁} i₂) (t.points…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Sbtw.oangle_eq_right`：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddC
ommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 
: NormedAd…
· 使用定理 `Affine.Simplex.ExcenterExists.dist_excenter_eq_dist_excenter`：∀ {V : Typ
e u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace 
ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用引理 `Affine.Simplex.excenterExists_singleton`：excenterExists_singleton [Nat.A
tLeastTwo n] (i : Fin (n + 1)) : s.ExcenterExists {i}
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用引理 `EuclideanGeometry.oangle_eq_of_dist_orthogonalProjection_eq`：oangle_eq_o
f_dist_orthogonalProjection_eq {p p' : P} {s₁ s₂ : AffineSubspace Real P} (hp'₁ 
: p' in s₁) (hp'₂ : p' in s₂) : haveI : Nonempty …
· 使用定理 `mem_affineSpan`：mem_affineSpan {p : P} {s : Set P} (hp : p in s) : p in 
affineSpan k s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Affine.Simplex.range_faceOpposite_points`：∀ {k : Type u_1} {V : Type u_2
} {P : Type u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Modu
le k V]   [inst_3 : AddTorsor …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `Affine.Simplex.ExcenterExists.touchpoint_injective`：∀ {V : Type u_1} {P 
: Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst
_2 : MetricSpace P]   [inst_3 : NormedAd…

--- 原说明 ---
The excenter of a triangle opposite a vertex bisects the angle at that vertex.
-/
lemma oangle_excenter_singleton_eq :
    ∡ (t.points i₂) (t.points i₁) (t.excenter {i₁}) =
      ∡ (t.excenter {i₁}) (t.points i₁) (t.points i₃) := by
  rw [(t.touchpoint_singleton_sbtw h₁₃ h₁₂ h₂₃.symm).symm.oangle_eq_left,
    (t.touchpoint_singleton_sbtw h₁₂ h₁₃ h₂₃).symm.oangle_eq_right]
  have hd := (t.excenterExists_singleton i₁).dist_excenter_eq_dist_excenter i₃ i₂
  simp_rw [touchpoint, orthogonalProjectionSpan] at hd ⊢
  refine oangle_eq_of_dist_orthogonalProjection_eq (mem_affineSpan _ ?_) (mem_affineSpan _ ?_)
    ((t.excenterExists_singleton i₁).touchpoint_injective.ne h₂₃.symm) hd
  · simp
    grind
  · simp
    grind

/-- The excenter of a triangle opposite a vertex bisects the exterior angle at another vertex
(that is, the interior angles between vertices and the excenter differ by `π`). -/
/-
**Affine.Triangle.oangle_excenter_singleton_eq_add_pi** 是 Mathlib 中的一个引理，位于命名空间 
`Affine.Triangle`。
形式化陈述：oangle_excenter_singleton_eq_add_pi : ∡ (t.points i₁) (t.points i₂) (t.exc
enter {i₁}) = ∡ (t.excenter {i₁}) (t.points i₂) (t.points i₃) + π
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sbtw.oangle_eq_add_pi_left`：∀ {V : Type u_1} {P : Type u_2} [inst : Norm
edAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [i
nst_3 : NormedAd…
· 使用定理 `Sbtw.symm`：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Ring R
] [inst_1 : PartialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module…
· 使用引理 `Affine.Triangle.touchpoint_singleton_sbtw`：touchpoint_singleton_sbtw {i₁
 i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) : Sbtw Real (
t.touchpoint {i₁} i₂) (t.points…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Affine.Simplex.ExcenterExists.excenter_ne_point`：∀ {V : Type u_1} {P : T
ype u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 
: MetricSpace P]   [inst_3 : NormedAd…
· 使用引理 `Affine.Simplex.excenterExists_singleton`：excenterExists_singleton [Nat.A
tLeastTwo n] (i : Fin (n + 1)) : s.ExcenterExists {i}
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Sbtw.oangle_eq_right`：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddC
ommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 
: NormedAd…
· 使用引理 `Affine.Triangle.sbtw_touchpoint_singleton`：sbtw_touchpoint_singleton {i₁
 i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) : Sbtw Real (
t.points i₁) (t.touchpoint {i₂}…
· 使用定理 `add_left_inj`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G] (a : 
G) {b c : G}, b + a = c + a ↔ b = c
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Affine.Simplex.ExcenterExists.dist_excenter_eq_dist_excenter`：∀ {V : Typ
e u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace 
ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用引理 `EuclideanGeometry.oangle_eq_of_dist_orthogonalProjection_eq`：oangle_eq_o
f_dist_orthogonalProjection_eq {p p' : P} {s₁ s₂ : AffineSubspace Real P} (hp'₁ 
: p' in s₁) (hp'₂ : p' in s₂) : haveI : Nonempty …
· 使用定理 `mem_affineSpan`：mem_affineSpan {p : P} {s : Set P} (hp : p in s) : p in 
affineSpan k s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Affine.Simplex.range_faceOpposite_points`：∀ {k : Type u_1} {V : Type u_2
} {P : Type u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Modu
le k V]   [inst_3 : AddTorsor …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `Affine.Simplex.ExcenterExists.touchpoint_injective`：∀ {V : Type u_1} {P 
: Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst
_2 : MetricSpace P]   [inst_3 : NormedAd…

--- 原说明 ---
The excenter of a triangle opposite a vertex bisects the exterior angle at anoth
er vertex
(that is, the interior angles between vertices and the excenter differ by `π`).
-/
lemma oangle_excenter_singleton_eq_add_pi :
    ∡ (t.points i₁) (t.points i₂) (t.excenter {i₁}) =
      ∡ (t.excenter {i₁}) (t.points i₂) (t.points i₃) + π := by
  rw [(t.touchpoint_singleton_sbtw h₁₃ h₁₂ h₂₃.symm).symm.oangle_eq_add_pi_left
        ((t.excenterExists_singleton _).excenter_ne_point _),
    ← (t.sbtw_touchpoint_singleton h₁₂.symm h₂₃ h₁₃).oangle_eq_right, add_left_inj]
  have hd := (t.excenterExists_singleton i₁).dist_excenter_eq_dist_excenter i₃ i₁
  simp_rw [touchpoint, orthogonalProjectionSpan] at hd ⊢
  refine oangle_eq_of_dist_orthogonalProjection_eq (mem_affineSpan _ ?_) (mem_affineSpan _ ?_)
    ((t.excenterExists_singleton i₁).touchpoint_injective.ne h₁₃.symm) hd
  · simp
    grind
  · simp
    grind

variable {t} in
/-- A point lying on angle bisectors from two vertices is an excenter. -/
/-
**Affine.Triangle.eq_excenter_of_two_zsmul_oangle_eq** 是 Mathlib 中的一个引理，位于命名空间 `
Affine.Triangle`。
形式化陈述：eq_excenter_of_two_zsmul_oangle_eq {p : P} (h₁ : (2 : Int) • ∡ (t.points i
₂) (t.points i₁) p = (2 : Int) • ∡ p (t.points i₁) (t.points i₃)) (h₂ : (2 : Int
) • ∡ (t.points i₃) (t.points i₂) p = (2 : Int) • ∡ p (t.points i₂) (t.points i₁
)) : exists signs : Finset (Fin 3), p = t.excenter signs
参数：h₁ : (2 : Int) • ∡ (t.points i₂) (t.points i₁) p = (2 : Int) • ∡ p (t.points 
i₁) (t.points i₃)；h₂ : (2 : Int) • ∡ (t.points i₃) (t.points i₂) p = (2 : Int) •
 ∡ p (t.points i₂) (t.points i₁)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one`：AffineI
ndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one [FiniteDimensional k V]
 [Fintype ι] {p : ι -> P} (hi : AffineIndependent k p…
· 使用引理 `FiniteDimensional.of_fact_finrank_eq_two`：of_fact_finrank_eq_two [Fact (
finrank K V = 2)] : FiniteDimensional K V
· 使用定理 `Affine.Simplex.independent`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [ins
t_3 : AddTorsor …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AffineSubspace.mem_top`：mem_top (p : P) : p in (⊤ : AffineSubspace k P)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用引理 `Affine.Triangle.dist_orthogonalProjectionSpan_faceOpposite_eq_iff_two_zs
mul_oangle_eq`：dist_orthogonalProjectionSpan_faceOpposite_eq_iff_two_zsmul_oangl
e_eq {p : P} : dist p ((t.faceOpposite i₃).orthogonalProjectionSpan p) = di…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Affine.Simplex.exists_forall_dist_eq_iff_exists_excenterExists_and_eq_ex
center`：exists_forall_dist_eq_iff_exists_excenterExists_and_eq_excenter {p : P} 
(hp : p in affineSpan Real (Set.range s.points)) : (exists r : Real,…

--- 原说明 ---
A point lying on angle bisectors from two vertices is an excenter.
-/
lemma eq_excenter_of_two_zsmul_oangle_eq {p : P}
    (h₁ : (2 : ℤ) • ∡ (t.points i₂) (t.points i₁) p = (2 : ℤ) • ∡ p (t.points i₁) (t.points i₃))
    (h₂ : (2 : ℤ) • ∡ (t.points i₃) (t.points i₂) p = (2 : ℤ) • ∡ p (t.points i₂) (t.points i₁)) :
    ∃ signs : Finset (Fin 3), p = t.excenter signs := by
  rw [← dist_orthogonalProjectionSpan_faceOpposite_eq_iff_two_zsmul_oangle_eq h₁₂ h₁₃ h₂₃] at h₁
  rw [← dist_orthogonalProjectionSpan_faceOpposite_eq_iff_two_zsmul_oangle_eq h₂₃ h₁₂.symm h₁₃.symm]
    at h₂
  have hp : p ∈ affineSpan ℝ (Set.range t.points) := by
    convert! AffineSubspace.mem_top ℝ V p
    rw [t.independent.affineSpan_eq_top_iff_card_eq_finrank_add_one]
    simp [hd2.out]
  have hr : ∃ r : ℝ, ∀ i, dist p ((t.faceOpposite i).orthogonalProjectionSpan p) = r := by
    refine ⟨dist p ((faceOpposite t i₃).orthogonalProjectionSpan p), ?_⟩
    intro i
    have h : i = i₁ ∨ i = i₂ ∨ i = i₃ := by clear! p t; decide +revert
    rcases h with rfl | rfl | rfl <;> grind
  obtain ⟨signs, -, hp⟩ :=
    (t.exists_forall_dist_eq_iff_exists_excenterExists_and_eq_excenter hp).1 hr
  exact ⟨signs, hp⟩

variable {t} in
/-- An excenter lying on the internal angle bisector from a vertex is either the incenter or the
excenter opposite that vertex. -/
/-
**Affine.Triangle.eq_incenter_or_eq_excenter_singleton_of_oangle_eq** 是 Mathlib 
中的一个引理，位于命名空间 `Affine.Triangle`。
形式化陈述：eq_incenter_or_eq_excenter_singleton_of_oangle_eq {signs : Finset (Fin 3)}
 (h : ∡ (t.points i₂) (t.points i₁) (t.excenter signs) = ∡ (t.excenter signs) (t
.points i₁) (t.points i₃)) : t.excenter signs = t.incenter ∨ t.excenter signs = 
t.excenter {i₁}
参数：Fin 3；h : ∡ (t.points i₂) (t.points i₁) (t.excenter signs) = ∡ (t.excenter si
gns) (t.points i₁) (t.points i₃)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Affine.Triangle.excenter_eq_incenter_or_excenter_singleton_of_ne`：excent
er_eq_incenter_or_excenter_singleton_of_ne (signs : Finset (Fin 3)) {i₁ i₂ i₃ : 
Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Affine.Triangle.oangle_excenter_singleton_eq_add_pi`：oangle_excenter_sin
gleton_eq_add_pi : ∡ (t.points i₁) (t.points i₂) (t.excenter {i₁}) = ∡ (t.excent
er {i₁}) (t.points i₂) (t.points i₃) + π
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.Angle.neg_coe_pi`：neg_coe_pi : -(π : Angle) = π
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `EuclideanGeometry.oangle_rev`：oangle_rev (p₁ p₂ p₃ : P) : ∡ p₃ p₂ p₁ = -
∡ p₁ p₂ p₃

--- 原说明 ---
An excenter lying on the internal angle bisector from a vertex is either the inc
enter or the
excenter opposite that vertex.
-/
lemma eq_incenter_or_eq_excenter_singleton_of_oangle_eq {signs : Finset (Fin 3)}
    (h : ∡ (t.points i₂) (t.points i₁) (t.excenter signs) =
      ∡ (t.excenter signs) (t.points i₁) (t.points i₃)) :
    t.excenter signs = t.incenter ∨ t.excenter signs = t.excenter {i₁} := by
  have hs := t.excenter_eq_incenter_or_excenter_singleton_of_ne signs h₁₂ h₁₃ h₂₃
  rcases hs with hs | hs | hs | hs
  · exact .inl hs
  · exact .inr hs
  · rw [hs, t.oangle_excenter_singleton_eq_add_pi h₁₂.symm h₂₃ h₁₃] at h
    simp [Real.Angle.pi_ne_zero] at h
  · rw [hs, oangle_rev (t.points i₃), t.oangle_excenter_singleton_eq_add_pi h₁₃.symm h₂₃.symm h₁₂,
      oangle_rev] at h
    simp [Real.Angle.pi_ne_zero] at h

variable {t} in
/-- An excenter lying on the external angle bisector from a vertex is the excenter opposite
another vertex. -/
/-
**Affine.Triangle.eq_excenter_singleton_of_oangle_eq_add_pi** 是 Mathlib 中的一个引理，位
于命名空间 `Affine.Triangle`。
形式化陈述：eq_excenter_singleton_of_oangle_eq_add_pi {signs : Finset (Fin 3)} (h : ∡ 
(t.points i₂) (t.points i₁) (t.excenter signs) = ∡ (t.excenter signs) (t.points 
i₁) (t.points i₃) + π) : t.excenter signs = t.excenter {i₂} ∨ t.excenter signs =
 t.excenter {i₃}
参数：Fin 3；h : ∡ (t.points i₂) (t.points i₁) (t.excenter signs) = ∡ (t.excenter si
gns) (t.points i₁) (t.points i₃) + π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Affine.Triangle.excenter_eq_incenter_or_excenter_singleton_of_ne`：excent
er_eq_incenter_or_excenter_singleton_of_ne (signs : Finset (Fin 3)) {i₁ i₂ i₃ : 
Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Affine.Triangle.oangle_incenter_eq`：oangle_incenter_eq : ∡ (t.points i₂)
 (t.points i₁) t.incenter = ∡ t.incenter (t.points i₁) (t.points i₃)
· 使用引理 `Affine.Triangle.oangle_excenter_singleton_eq`：oangle_excenter_singleton_
eq : ∡ (t.points i₂) (t.points i₁) (t.excenter {i₁}) = ∡ (t.excenter {i₁}) (t.po
ints i₁) (t.points i₃)

--- 原说明 ---
An excenter lying on the external angle bisector from a vertex is the excenter o
pposite
another vertex.
-/
lemma eq_excenter_singleton_of_oangle_eq_add_pi {signs : Finset (Fin 3)}
    (h : ∡ (t.points i₂) (t.points i₁) (t.excenter signs) =
      ∡ (t.excenter signs) (t.points i₁) (t.points i₃) + π) :
    t.excenter signs = t.excenter {i₂} ∨ t.excenter signs = t.excenter {i₃} := by
  have hs := t.excenter_eq_incenter_or_excenter_singleton_of_ne signs h₁₂ h₁₃ h₂₃
  rcases hs with hs | hs | hs | hs
  · rw [hs, t.oangle_incenter_eq h₁₂ h₁₃ h₂₃] at h
    simp [Real.Angle.pi_ne_zero] at h
  · rw [hs, t.oangle_excenter_singleton_eq h₁₂ h₁₃ h₂₃] at h
    simp [Real.Angle.pi_ne_zero] at h
  · exact .inl hs
  · exact .inr hs

variable {t} in
/-- A point lying on two internal angle bisectors is the incenter. -/
/-
**Affine.Triangle.eq_incenter_of_oangle_eq** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Tri
angle`。
形式化陈述：eq_incenter_of_oangle_eq {p : P} (h₁ : ∡ (t.points i₂) (t.points i₁) p = ∡
 p (t.points i₁) (t.points i₃)) (h₂ : ∡ (t.points i₃) (t.points i₂) p = ∡ p (t.p
oints i₂) (t.points i₁)) : p = t.incenter
参数：h₁ : ∡ (t.points i₂) (t.points i₁) p = ∡ p (t.points i₁) (t.points i₃)；h₂ : ∡
 (t.points i₃) (t.points i₂) p = ∡ p (t.points i₂) (t.points i₁)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Affine.Triangle.eq_excenter_of_two_zsmul_oangle_eq`：eq_excenter_of_two_z
smul_oangle_eq {p : P} (h₁ : (2 : Int) • ∡ (t.points i₂) (t.points i₁) p = (2 : 
Int) • ∡ p (t.points i₁) (t.points i₃)) …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Affine.Triangle.eq_incenter_or_eq_excenter_singleton_of_oangle_eq`：eq_in
center_or_eq_excenter_singleton_of_oangle_eq {signs : Finset (Fin 3)} (h : ∡ (t.
points i₂) (t.points i₁) (t.excenter signs) = ∡ (t.exce…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用引理 `Affine.Simplex.excenter_singleton_injective`：excenter_singleton_injectiv
e [Nat.AtLeastTwo n] : Function.Injective fun i => s.excenter {i}
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A point lying on two internal angle bisectors is the incenter.
-/
lemma eq_incenter_of_oangle_eq {p : P}
    (h₁ : ∡ (t.points i₂) (t.points i₁) p = ∡ p (t.points i₁) (t.points i₃))
    (h₂ : ∡ (t.points i₃) (t.points i₂) p = ∡ p (t.points i₂) (t.points i₁)) :
    p = t.incenter := by
  obtain ⟨signs, rfl⟩ := t.eq_excenter_of_two_zsmul_oangle_eq h₁₂ h₁₃ h₂₃ (by rw [h₁]) (by rw [h₂])
  have h₁' := t.eq_incenter_or_eq_excenter_singleton_of_oangle_eq h₁₂ h₁₃ h₂₃ h₁
  have h₂' := t.eq_incenter_or_eq_excenter_singleton_of_oangle_eq h₂₃ h₁₂.symm h₁₃.symm h₂
  rcases h₁' with h₁' | h₁'
  · exact h₁'
  rcases h₂' with h₂' | h₂'
  · exact h₂'
  rw [h₁'] at h₂'
  exfalso
  exact t.excenter_singleton_injective.ne h₁₂ h₂'

variable {t} in
/-- A point lying on the internal angle bisector from vertex `i₁` and the external angle bisector
from another vertex is the excenter opposite vertex `i₁`. -/
/-
**Affine.Triangle.eq_excenter_singleton_of_oangle_eq_of_oangle_eq_add_pi** 是 Mat
hlib 中的一个引理，位于命名空间 `Affine.Triangle`。
形式化陈述：eq_excenter_singleton_of_oangle_eq_of_oangle_eq_add_pi {p : P} (h₁ : ∡ (t.
points i₂) (t.points i₁) p = ∡ p (t.points i₁) (t.points i₃)) (h₂ : ∡ (t.points 
i₃) (t.points i₂) p = ∡ p (t.points i₂) (t.points i₁) + π) : p = t.excenter {i₁}
参数：h₁ : ∡ (t.points i₂) (t.points i₁) p = ∡ p (t.points i₁) (t.points i₃)；h₂ : ∡
 (t.points i₃) (t.points i₂) p = ∡ p (t.points i₂) (t.points i₁) + π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Affine.Triangle.eq_excenter_of_two_zsmul_oangle_eq`：eq_excenter_of_two_z
smul_oangle_eq {p : P} (h₁ : (2 : Int) • ∡ (t.points i₂) (t.points i₁) p = (2 : 
Int) • ∡ p (t.points i₁) (t.points i₃)) …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `Real.Angle.two_zsmul_coe_pi`：two_zsmul_coe_pi : (2 : Int) • (π : Angle) 
= 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Affine.Triangle.eq_incenter_or_eq_excenter_singleton_of_oangle_eq`：eq_in
center_or_eq_excenter_singleton_of_oangle_eq {signs : Finset (Fin 3)} (h : ∡ (t.
points i₂) (t.points i₁) (t.excenter signs) = ∡ (t.exce…
· 使用引理 `Affine.Triangle.eq_excenter_singleton_of_oangle_eq_add_pi`：eq_excenter_s
ingleton_of_oangle_eq_add_pi {signs : Finset (Fin 3)} (h : ∡ (t.points i₂) (t.po
ints i₁) (t.excenter signs) = ∡ (t.excenter sig…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `Affine.Simplex.excenter_singleton_ne_incenter`：excenter_singleton_ne_inc
enter [Nat.AtLeastTwo n] (i : Fin (n + 1)) : s.excenter {i} != s.incenter
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A point lying on the internal angle bisector from vertex `i₁` and the external a
ngle bisector
from another vertex is the excenter opposite vertex `i₁`.
-/
lemma eq_excenter_singleton_of_oangle_eq_of_oangle_eq_add_pi {p : P}
    (h₁ : ∡ (t.points i₂) (t.points i₁) p = ∡ p (t.points i₁) (t.points i₃))
    (h₂ : ∡ (t.points i₃) (t.points i₂) p = ∡ p (t.points i₂) (t.points i₁) + π) :
    p = t.excenter {i₁} := by
  obtain ⟨signs, rfl⟩ := t.eq_excenter_of_two_zsmul_oangle_eq h₁₂ h₁₃ h₂₃ (by rw [h₁])
    (by rw [h₂]; simp)
  have h₁' := t.eq_incenter_or_eq_excenter_singleton_of_oangle_eq h₁₂ h₁₃ h₂₃ h₁
  have h₂' := t.eq_excenter_singleton_of_oangle_eq_add_pi h₂₃ h₁₂.symm h₁₃.symm h₂
  rcases h₁' with h₁' | h₁'
  · rcases h₂' with h₂' | h₂'
    · rw [h₁'] at h₂'
      exfalso
      exact (t.excenter_singleton_ne_incenter _).symm h₂'
    · exact h₂'
  · exact h₁'

variable {t} in
/-- A point lying on two external angle bisectors is the excenter opposite the third vertex. -/
/-
**Affine.Triangle.eq_excenter_singleton_of_oangle_eq_add_pi_of_oangle_eq_add_pi*
* 是 Mathlib 中的一个引理，位于命名空间 `Affine.Triangle`。
形式化陈述：eq_excenter_singleton_of_oangle_eq_add_pi_of_oangle_eq_add_pi {p : P} (h₁ 
: ∡ (t.points i₂) (t.points i₁) p = ∡ p (t.points i₁) (t.points i₃) + π) (h₂ : ∡
 (t.points i₃) (t.points i₂) p = ∡ p (t.points i₂) (t.points i₁) + π) : p = t.ex
center {i₃}
参数：h₁ : ∡ (t.points i₂) (t.points i₁) p = ∡ p (t.points i₁) (t.points i₃) + π；h₂
 : ∡ (t.points i₃) (t.points i₂) p = ∡ p (t.points i₂) (t.points i₁) + π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Affine.Triangle.eq_excenter_of_two_zsmul_oangle_eq`：eq_excenter_of_two_z
smul_oangle_eq {p : P} (h₁ : (2 : Int) • ∡ (t.points i₂) (t.points i₁) p = (2 : 
Int) • ∡ p (t.points i₁) (t.points i₃)) …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `Real.Angle.two_zsmul_coe_pi`：two_zsmul_coe_pi : (2 : Int) • (π : Angle) 
= 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Affine.Triangle.eq_excenter_singleton_of_oangle_eq_add_pi`：eq_excenter_s
ingleton_of_oangle_eq_add_pi {signs : Finset (Fin 3)} (h : ∡ (t.points i₂) (t.po
ints i₁) (t.excenter signs) = ∡ (t.excenter sig…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用引理 `Affine.Simplex.excenter_singleton_injective`：excenter_singleton_injectiv
e [Nat.AtLeastTwo n] : Function.Injective fun i => s.excenter {i}
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A point lying on two external angle bisectors is the excenter opposite the third
 vertex.
-/
lemma eq_excenter_singleton_of_oangle_eq_add_pi_of_oangle_eq_add_pi {p : P}
    (h₁ : ∡ (t.points i₂) (t.points i₁) p = ∡ p (t.points i₁) (t.points i₃) + π)
    (h₂ : ∡ (t.points i₃) (t.points i₂) p = ∡ p (t.points i₂) (t.points i₁) + π) :
    p = t.excenter {i₃} := by
  obtain ⟨signs, rfl⟩ := t.eq_excenter_of_two_zsmul_oangle_eq h₁₂ h₁₃ h₂₃ (by rw [h₁]; simp)
    (by rw [h₂]; simp)
  have h₁' := t.eq_excenter_singleton_of_oangle_eq_add_pi h₁₂ h₁₃ h₂₃ h₁
  have h₂' := t.eq_excenter_singleton_of_oangle_eq_add_pi h₂₃ h₁₂.symm h₁₃.symm h₂
  rcases h₁' with h₁' | h₁'
  · rcases h₂' with h₂' | h₂'
    · exact h₂'
    rw [h₂'] at h₁'
    exfalso
    exact t.excenter_singleton_injective.ne h₁₂ h₁'
  · exact h₁'

end Triangle

end Affine

