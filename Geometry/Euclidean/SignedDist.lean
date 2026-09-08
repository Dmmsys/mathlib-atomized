/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Geometry.Euclidean.Projection
public import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Signed distance to an affine subspace in a Euclidean space.

This file defines the signed distance between two points, in the direction of a given vector, and
the signed distance between an affine subspace and a point, in the direction of a given
reference point.

## Main definitions

* `signedDist` is the signed distance between two points
* `AffineSubspace.signedInfDist` is the signed distance between an affine subspace and a point.
* `Affine.Simplex.signedInfDist` is the signed distance between a face of a simplex and a point.
  In the case of a triangle, these distances are trilinear coordinates.

## References

* https://en.wikipedia.org/wiki/Trilinear_coordinates

-/

@[expose] public section


open EuclideanGeometry NormedSpace
open scoped RealInnerProductSpace

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P]

section signedDist

/--
The signed distance between two points `p` and `q`, in the direction of a reference vector `v`.
It is the size of `q - p` in the direction of `v`.
In the degenerate case `v = 0`, it returns `0`.

TODO: once we have a topology on `P →ᴬ[ℝ] ℝ`, the type should be `P →ᴬ[ℝ] P →ᴬ[ℝ] ℝ`.
-/
/-
**signedDist** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：signedDist (v : V) : P ->ᵃ[Real] P ->ᴬ[Real] Real where toFun p
参数：v : V。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ

--- 原说明 ---
The signed distance between two points `p` and `q`, in the direction of a refere
nce vector `v`.
It is the size of `q - p` in the direction of `v`.
In the degenerate case `v = 0`, it returns `0`.

TODO: once we have a topology on `P →ᴬ[ℝ] ℝ`, the type should be `P →ᴬ[ℝ] P →ᴬ[ℝ
] ℝ`.
-/
noncomputable def signedDist (v : V) : P →ᵃ[ℝ] P →ᴬ[ℝ] ℝ where
  toFun p := (innerSL ℝ (normalize v)).toContinuousAffineMap.comp
    (ContinuousAffineMap.id ℝ P -ᵥ .const ℝ P p)
  linear := {
    toFun w := .const ℝ P ⟪-normalize v, w⟫
    map_add' x y := by ext; simp [inner_add_right]
    map_smul' r x := by ext; simp [inner_smul_right] }
  map_vadd' p v' := by
    ext q
    simp [vsub_vadd_eq_vsub_sub, inner_sub_right, ← sub_eq_neg_add]

variable (v w : V) (p q r : P)

-- Lemmas about the definition of `signedDist`
/-
**signedDist_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：signedDist_apply : signedDist v p = (innerSL Real (normalize v)).toContinu
ousAffineMap.comp (ContinuousAffineMap.id Real P -ᵥ .const Real P p)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
-/
lemma signedDist_apply : signedDist v p = (innerSL ℝ (normalize v)).toContinuousAffineMap.comp
    (ContinuousAffineMap.id ℝ P -ᵥ .const ℝ P p) :=
  rfl
/-
**signedDist_apply_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：signedDist_apply_apply : signedDist v p q = ⟪normalize v, q -ᵥ p⟫
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
-/
lemma signedDist_apply_apply : signedDist v p q = ⟪normalize v, q -ᵥ p⟫ :=
  rfl
/-
**signedDist_apply_linear** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：signedDist_apply_linear : (signedDist v p).linear = innerₗ V (normalize v)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma signedDist_apply_linear : (signedDist v p).linear = innerₗ V (normalize v) := by
  change (innerₗ V (normalize v)).comp (LinearMap.id - 0) = _
  simp
/-
**signedDist_apply_linear_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：signedDist_apply_linear_apply : (signedDist v p).linear w = ⟪normalize v, 
w⟫
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `signedDist_apply_linear`：signedDist_apply_linear : (signedDist v p).line
ar = innerₗ V (normalize v)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma signedDist_apply_linear_apply : (signedDist v p).linear w = ⟪normalize v, w⟫ := by
  simp [signedDist_apply_linear]
/-
**signedDist_linear_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：signedDist_linear_apply : (signedDist v).linear w = .const Real P ⟪-normal
ize v, w⟫
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
-/
lemma signedDist_linear_apply : (signedDist v).linear w = .const ℝ P ⟪-normalize v, w⟫ :=
  rfl
/-
**signedDist_linear_apply_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：signedDist_linear_apply_apply : (signedDist v).linear w p = ⟪-normalize v,
 w⟫
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
-/
lemma signedDist_linear_apply_apply : (signedDist v).linear w p = ⟪-normalize v, w⟫ :=
  rfl

-- Lemmas about the vector argument of `signedDist`
/-
**signedDist_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：signedDist_smul (r : Real) : signedDist (r • v) p q = SignType.sign r * si
gnedDist v p q
参数：r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedSpace.normalize_smul`：normalize_smul (r : Real) (x : V) : normaliz
e (r • x) = (SignType.sign r : Real) • normalize x
· 使用定理 `real_inner_smul_left`：real_inner_smul_left (x y : F) (r : Real) : ⟪r • x
, y⟫_Real = r * ⟪x, y⟫_Real
-/
lemma signedDist_smul (r : ℝ) : signedDist (r • v) p q = SignType.sign r * signedDist v p q := by
  simp only [signedDist_apply_apply]
  rw [normalize_smul, real_inner_smul_left]
/-
**signedDist_smul_of_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：signedDist_smul_of_pos {r : Real} (h : 0 < r) : signedDist (r • v) p q = s
ignedDist v p q
参数：h : 0 < r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `signedDist_smul`：signedDist_smul (r : Real) : signedDist (r • v) p q = S
ignType.sign r * signedDist v p q
· 使用定理 `sign_pos`：sign_pos (ha : 0 < a) : sign a = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma signedDist_smul_of_pos {r : ℝ} (h : 0 < r) : signedDist (r • v) p q = signedDist v p q := by
  simp [signedDist_smul, h]
/-
**signedDist_smul_of_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：signedDist_smul_of_neg {r : Real} (h : r < 0) : signedDist (r • v) p q = -
signedDist v p q
参数：h : r < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `signedDist_smul`：signedDist_smul (r : Real) : signedDist (r • v) p q = S
ignType.sign r * signedDist v p q
· 使用定理 `sign_neg`：sign_neg (ha : a < 0) : sign a = -1
· 使用引理 `SignType.coe_neg`：coe_neg {α : Type*} [One α] [SubtractionMonoid α] (s :
 SignType) : (↑(-s) : α) = -↑s
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma signedDist_smul_of_neg {r : ℝ} (h : r < 0) : signedDist (r • v) p q = -signedDist v p q := by
  simp [signedDist_smul, h]
/-
**signedDist_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] (
p q : P), ((signedDist 0) p) q = 0
参数：p q : P；(signedDist 0) p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sign_zero`：sign_zero : sign (0 : α) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用引理 `signedDist_smul`：signedDist_smul (r : Real) : signedDist (r • v) p q = S
ignType.sign r * signedDist v p q
-/
@[simp] lemma signedDist_zero : signedDist 0 p q = 0 := by
  simpa using signedDist_smul 0 p q 0
/-
**signedDist_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] (
v : V) (p q : P), ((signedDist (-v)) p) q = -((signedDist v) p) q
参数：v : V；p q : P；(signedDist (-v)) p；(signedDist v) p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `sign_neg`：sign_neg (ha : a < 0) : sign a = -1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
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
· 使用引理 `SignType.coe_neg`：coe_neg {α : Type*} [One α] [SubtractionMonoid α] (s :
 SignType) : (↑(-s) : α) = -↑s
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `signedDist_smul`：signedDist_smul (r : Real) : signedDist (r • v) p q = S
ignType.sign r * signedDist v p q
-/
@[simp] lemma signedDist_neg : signedDist (-v) p q = -signedDist v p q := by
  simpa using signedDist_smul v p q (-1)
/-
**signedDist_congr** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：signedDist_congr (h : exists r > (0 : Real), r • v = w) : signedDist (P
参数：h : exists r > (0 : Real), r • v = w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `AffineMap.ext`：ext {f g : P1 ->ᵃ[k] P2} (h : forall p, f p = g p) : f = 
g
· 使用定理 `ContinuousAffineMap.ext`：ext {f g : P ->ᴬ[R] Q} (h : forall x, f x = g x
) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sign_pos`：sign_pos (ha : 0 < a) : sign a = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `signedDist_smul`：signedDist_smul (r : Real) : signedDist (r • v) p q = S
ignType.sign r * signedDist v p q
-/
lemma signedDist_congr (h : ∃ r > (0 : ℝ), r • v = w) : signedDist (P := P) v = signedDist w := by
  obtain ⟨r, _, _⟩ := h
  ext p q
  simpa [*] using (signedDist_smul v p q r).symm

-- Lemmas about permuting the point arguments of `signedDist`, analogous to lemmas about `dist`
/-
**signedDist_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] (
v : V) (p : P), ((signedDist v) p) p = 0
参数：v : V；p : P；(signedDist v) p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `inner_zero_right`：inner_zero_right (x : E) : ⟪x, 0⟫ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma signedDist_self : signedDist v p p = 0 := by
  simp [signedDist_apply_apply]
/-
**signedDist_anticomm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] (
v : V) (p q : P), -((signedDist v) p) q = ((signedDist v) q) p
参数：v : V；p q : P；(signedDist v) p；(signedDist v) q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma signedDist_anticomm : -signedDist v p q = signedDist v q p := by
  simp [signedDist_apply_apply, ← inner_neg_right]

@[simp]
/-
**signedDist_triangle** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：signedDist_triangle : signedDist v p q + signedDist v q r = signedDist v p
 r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_add_right`：inner_add_right (x y z : E) : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x,
 z⟫
· 使用定理 `vsub_add_vsub_cancel`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₂ + (p₂ -ᵥ p₃) = p₁ -ᵥ p₃
-/
lemma signedDist_triangle : signedDist v p q + signedDist v q r = signedDist v p r := by
  simp only [signedDist_apply_apply]
  rw [add_comm, ← inner_add_right, vsub_add_vsub_cancel]

@[simp]
/-
**signedDist_triangle_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：signedDist_triangle_left : signedDist v p q - signedDist v p r = signedDis
t v r q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_iff_eq_add'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G}
, a - b = c ↔ a = b + c
· 使用引理 `signedDist_triangle`：signedDist_triangle : signedDist v p q + signedDist
 v q r = signedDist v p r
-/
lemma signedDist_triangle_left : signedDist v p q - signedDist v p r = signedDist v r q := by
  rw [sub_eq_iff_eq_add', signedDist_triangle]

@[simp]
/-
**signedDist_triangle_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：signedDist_triangle_right : signedDist v p r - signedDist v q r = signedDi
st v p q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_iff_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a -
 b = c ↔ a = c + b
· 使用引理 `signedDist_triangle`：signedDist_triangle : signedDist v p q + signedDist
 v q r = signedDist v p r
-/
lemma signedDist_triangle_right : signedDist v p r - signedDist v q r = signedDist v p q := by
  rw [sub_eq_iff_eq_add, signedDist_triangle]

-- Lemmas about offsetting the point arguments of `signedDist` (with `+ᵥ` or `-ᵥ`)
/-
**signedDist_vadd_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：signedDist_vadd_left : signedDist v (w +ᵥ p) q = -⟪normalize v, w⟫ + signe
dDist v p q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineMap.map_vadd`：map_vadd (f : P1 ->ᵃ[k] P2) (p : P1) (v : V1) : f (v
 +ᵥ p) = f.linear v +ᵥ f p
· 使用定理 `inner_neg_left`：inner_neg_left (x y : E) : ⟪-x, y⟫ = -⟪x, y⟫
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma signedDist_vadd_left : signedDist v (w +ᵥ p) q = -⟪normalize v, w⟫ + signedDist v p q := by
  simp [signedDist_linear_apply_apply]
/-
**signedDist_vadd_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：signedDist_vadd_right : signedDist v p (w +ᵥ q) = ⟪normalize v, w⟫ + signe
dDist v p q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAffineMap.map_vadd`：map_vadd (f : P ->ᴬ[R] Q) (p : P) (v : V) 
: f (v +ᵥ p) = f.contLinear v +ᵥ f p
· 使用引理 `signedDist_apply_linear_apply`：signedDist_apply_linear_apply : (signedDi
st v p).linear w = ⟪normalize v, w⟫
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma signedDist_vadd_right : signedDist v p (w +ᵥ q) = ⟪normalize v, w⟫ + signedDist v p q := by
  simp [signedDist_apply_linear_apply]

-- TODO: find a better name for these 2 lemmas
/-
**signedDist_vadd_left_swap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：signedDist_vadd_left_swap : signedDist v (w +ᵥ p) q = signedDist v p (-w +
ᵥ q)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `signedDist_vadd_left`：signedDist_vadd_left : signedDist v (w +ᵥ p) q = -
⟪normalize v, w⟫ + signedDist v p q
· 使用引理 `signedDist_vadd_right`：signedDist_vadd_right : signedDist v p (w +ᵥ q) =
 ⟪normalize v, w⟫ + signedDist v p q
· 使用定理 `inner_neg_right`：inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫
-/
lemma signedDist_vadd_left_swap : signedDist v (w +ᵥ p) q = signedDist v p (-w +ᵥ q) := by
  rw [signedDist_vadd_left, signedDist_vadd_right, inner_neg_right]
/-
**signedDist_vadd_right_swap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：signedDist_vadd_right_swap : signedDist v p (w +ᵥ q) = signedDist v (-w +ᵥ
 p) q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `signedDist_vadd_left_swap`：signedDist_vadd_left_swap : signedDist v (w +
ᵥ p) q = signedDist v p (-w +ᵥ q)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
lemma signedDist_vadd_right_swap : signedDist v p (w +ᵥ q) = signedDist v (-w +ᵥ p) q := by
  rw [signedDist_vadd_left_swap, neg_neg]
/-
**signedDist_vadd_vadd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：signedDist_vadd_vadd : signedDist v (w +ᵥ p) (w +ᵥ q) = signedDist v p q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `signedDist_vadd_left_swap`：signedDist_vadd_left_swap : signedDist v (w +
ᵥ p) q = signedDist v p (-w +ᵥ q)
· 使用定理 `neg_vadd_vadd`：∀ {G : Type u_3} {α : Type u_5} [inst : AddGroup G] [inst
_1 : AddAction G α] (g : G) (a : α), -g +ᵥ g +ᵥ a = a
-/
lemma signedDist_vadd_vadd : signedDist v (w +ᵥ p) (w +ᵥ q) = signedDist v p q := by
  rw [signedDist_vadd_left_swap, neg_vadd_vadd]

variable {v p q} in
/-
**signedDist_left_congr** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：signedDist_left_congr (h : ⟪v, p -ᵥ q⟫ = 0) : signedDist v p = signedDist 
v q
参数：h : ⟪v, p -ᵥ q⟫ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAffineMap.ext`：ext {f g : P ->ᴬ[R] Q} (h : forall x, f x = g x
) : f = g
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `real_inner_smul_left`：real_inner_smul_left (x y : F) (r : Real) : ⟪r • x
, y⟫_Real = r * ⟪x, y⟫_Real
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `signedDist_vadd_left`：signedDist_vadd_left : signedDist v (w +ᵥ p) q = -
⟪normalize v, w⟫ + signedDist v p q
-/
lemma signedDist_left_congr (h : ⟪v, p -ᵥ q⟫ = 0) : signedDist v p = signedDist v q := by
  ext r
  simpa [NormedSpace.normalize, real_inner_smul_left, h] using signedDist_vadd_left v (p -ᵥ q) q r

variable {v q r} in
/-
**signedDist_right_congr** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：signedDist_right_congr (h : ⟪v, q -ᵥ r⟫ = 0) : signedDist v p q = signedDi
st v p r
参数：h : ⟪v, q -ᵥ r⟫ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `real_inner_smul_left`：real_inner_smul_left (x y : F) (r : Real) : ⟪r • x
, y⟫_Real = r * ⟪x, y⟫_Real
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `signedDist_vadd_right`：signedDist_vadd_right : signedDist v p (w +ᵥ q) =
 ⟪normalize v, w⟫ + signedDist v p q
-/
lemma signedDist_right_congr (h : ⟪v, q -ᵥ r⟫ = 0) : signedDist v p q = signedDist v p r := by
  simpa [NormedSpace.normalize, real_inner_smul_left, h] using signedDist_vadd_right v (q -ᵥ r) p r

variable {v p q} in
/-
**signedDist_eq_zero_of_orthogonal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：signedDist_eq_zero_of_orthogonal (h : ⟪v, q -ᵥ p⟫ = 0) : signedDist v p q 
= 0
参数：h : ⟪v, q -ᵥ p⟫ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `signedDist_self`：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGr
oup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : Nor
medAd…
· 使用引理 `signedDist_right_congr`：signedDist_right_congr (h : ⟪v, q -ᵥ r⟫ = 0) : s
ignedDist v p q = signedDist v p r
-/
lemma signedDist_eq_zero_of_orthogonal (h : ⟪v, q -ᵥ p⟫ = 0) : signedDist v p q = 0 := by
  simpa using signedDist_right_congr p h

-- Lemmas relating `signedDist` to `dist`
/-
**abs_signedDist_le_dist** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：abs_signedDist_le_dist : |signedDist v p q| <= dist p q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `signedDist_apply_apply`：signedDist_apply_apply : signedDist v p q = ⟪nor
malize v, q -ᵥ p⟫
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NormedSpace.normalize_zero_eq_zero`：normalize_zero_eq_zero : normalize (
0 : V) = 0
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `abs_real_inner_le_norm`：abs_real_inner_le_norm (x y : F) : |⟪x, y⟫_Real|
 <= ‖x‖ * ‖y‖
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NormedSpace.norm_normalize`：∀ {V : Type u_1} [inst : NormedAddCommGroup 
V] [inst_1 : NormedSpace ℝ V] {x : V}, x ≠ 0 → ‖NormedSpace.normalize x‖ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `dist_eq_norm_vsub'`：dist_eq_norm_vsub' (x y : P) : dist x y = ‖y -ᵥ x‖
-/
lemma abs_signedDist_le_dist : |signedDist v p q| ≤ dist p q := by
  rw [signedDist_apply_apply]
  by_cases h : v = 0
  · simp [h]
  · grw [abs_real_inner_le_norm]
    simp [norm_normalize h, dist_eq_norm_vsub']
/-
**signedDist_le_dist** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：signedDist_le_dist : signedDist v p q <= dist p q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用引理 `abs_signedDist_le_dist`：abs_signedDist_le_dist : |signedDist v p q| <= d
ist p q
-/
lemma signedDist_le_dist : signedDist v p q ≤ dist p q :=
  le_trans (le_abs_self _) (abs_signedDist_le_dist _ _ _)
/-
**abs_signedDist_eq_dist_iff_vsub_mem_span** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：abs_signedDist_eq_dist_iff_vsub_mem_span : |signedDist v p q| = dist p q ↔
 q -ᵥ p in Real ∙ v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x
· 使用引理 `signedDist_apply_apply`：signedDist_apply_apply : signedDist v p q = ⟪nor
malize v, q -ᵥ p⟫
· 使用定理 `dist_eq_norm_vsub'`：dist_eq_norm_vsub' (x y : P) : dist x y = ‖y -ᵥ x‖
· 使用定理 `NormedSpace.normalize.eq_1`：∀ {V : Type u_1} [inst : NormedAddCommGroup 
V] [inst_1 : NormedSpace ℝ V] (x : V), NormedSpace.normalize x = ‖x‖⁻¹ • x
· 使用定理 `real_inner_smul_left`：real_inner_smul_left (x y : F) (r : Real) : ⟪r • x
, y⟫_Real = r * ⟪x, y⟫_Real
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `abs_inv`：abs_inv (a : α) : |a⁻¹| = |a|⁻¹
· 使用定理 `abs_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (z : E), |‖z‖| 
= ‖z‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
（共 41 条，此处仅展示前 30 条）
-/
lemma abs_signedDist_eq_dist_iff_vsub_mem_span :
    |signedDist v p q| = dist p q ↔ q -ᵥ p ∈ ℝ ∙ v := by
  rw [Submodule.mem_span_singleton]
  rw [signedDist_apply_apply, dist_eq_norm_vsub', NormedSpace.normalize, real_inner_smul_left,
    abs_mul, abs_inv, abs_norm]
  by_cases h : v = 0
  · simp [h, eq_comm (a := (0 : ℝ)), eq_comm (a := (0 : V))]
  rw [inv_mul_eq_iff_eq_mul₀ (by positivity)]
  rw [← Real.norm_eq_abs, ((norm_inner_eq_norm_tfae ℝ v (q -ᵥ p)).out 0 2 :)]
  simp [h, eq_comm]

open NNReal in
/-
**signedDist_eq_dist_iff_vsub_mem_span** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：signedDist_eq_dist_iff_vsub_mem_span : signedDist v p q = dist p q ↔ q -ᵥ 
p in Real>=0 ∙ v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x
· 使用引理 `signedDist_apply_apply`：signedDist_apply_apply : signedDist v p q = ⟪nor
malize v, q -ᵥ p⟫
· 使用定理 `dist_eq_norm_vsub'`：dist_eq_norm_vsub' (x y : P) : dist x y = ‖y -ᵥ x‖
· 使用定理 `NormedSpace.normalize.eq_1`：∀ {V : Type u_1} [inst : NormedAddCommGroup 
V] [inst_1 : NormedSpace ℝ V] (x : V), NormedSpace.normalize x = ‖x‖⁻¹ • x
· 使用定理 `real_inner_smul_left`：real_inner_smul_left (x y : F) (r : Real) : ⟪r • x
, y⟫_Real = r * ⟪x, y⟫_Real
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `inv_mul_eq_iff_eq_mul₀`：inv_mul_eq_iff_eq_mul₀ (ha : a != 0) : a⁻¹ * b =
 c ↔ b = a * c
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
（共 48 条，此处仅展示前 30 条）
-/
lemma signedDist_eq_dist_iff_vsub_mem_span : signedDist v p q = dist p q ↔ q -ᵥ p ∈ ℝ≥0 ∙ v := by
  rw [Submodule.mem_span_singleton]
  rw [signedDist_apply_apply, dist_eq_norm_vsub', NormedSpace.normalize, real_inner_smul_left]
  by_cases h : v = 0
  · simp [h, eq_comm (a := (0 : ℝ)), eq_comm (a := (0 : V))]
  rw [inv_mul_eq_iff_eq_mul₀ (by positivity)]
  rw [inner_eq_norm_mul_iff_real]
  simp only [smul_def]
  refine ⟨fun h => ?_, fun ⟨c, h⟩ => ?_⟩
  · simp only [NNReal.exists, coe_mk, exists_prop]
    use ‖v‖⁻¹ * ‖q -ᵥ p‖
    constructor
    · positivity
    · rw [← smul_smul, h, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
  · rw [← h, norm_smul, smul_smul, mul_comm]
    simp
/-
**signedDist_vsub_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] (
p q : P), ((signedDist (q -ᵥ p)) p) q = dist p q
参数：p q : P；(signedDist (q -ᵥ p)) p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `signedDist_eq_dist_iff_vsub_mem_span`：signedDist_eq_dist_iff_vsub_mem_sp
an : signedDist v p q = dist p q ↔ q -ᵥ p in Real>=0 ∙ v
· 使用定理 `Submodule.mem_span_singleton_self`：mem_span_singleton_self (x : M) : x i
n R ∙ x
-/
@[simp] lemma signedDist_vsub_self : signedDist (q -ᵥ p) p q = dist p q := by
  rw [signedDist_eq_dist_iff_vsub_mem_span]
  apply Submodule.mem_span_singleton_self
/-
**signedDist_vsub_self_rev** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] (
p q : P), ((signedDist (p -ᵥ q)) p) q = -dist p q
参数：p q : P；(signedDist (p -ᵥ q)) p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_eq_iff_eq_neg`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, 
-a = b ↔ a = -b
· 使用定理 `signedDist_neg`：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGro
up V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : Norm
edAd…
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `signedDist_vsub_self`：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddC
ommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 
: NormedAd…
-/
@[simp] lemma signedDist_vsub_self_rev : signedDist (p -ᵥ q) p q = -dist p q := by
  rw [← neg_eq_iff_eq_neg, ← signedDist_neg, neg_vsub_eq_vsub_rev]
  apply signedDist_vsub_self

set_option backward.isDefEq.respectTransparency false in
/-
**signedDist_lineMap_lineMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：signedDist_lineMap_lineMap (c₁ c₂ : Real) : signedDist v (AffineMap.lineMa
p p q c₁) (AffineMap.lineMap p q c₂) = (c₂ - c₁) * signedDist v p q
参数：c₁ c₂ : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineMap.apply_lineMap`：apply_lineMap (f : P1 ->ᵃ[k] P2) (p₀ p₁ : P1) (
c : k) : f (lineMap p₀ p₁ c) = lineMap (f p₀) (f p₁) c
· 使用定理 `ContinuousAffineMap.apply_lineMap`：apply_lineMap (f : P ->ᴬ[R] Q) (p₀ p₁
 : P) (c : R) : f (AffineMap.lineMap p₀ p₁ c) = AffineMap.lineMap (f p₀) (f p₁) 
c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `ContinuousAffineMap.lineMap_apply'`：lineMap_apply' [ContinuousConstSMul 
R W] [SMulCommClass R R W] (f g : P ->ᴬ[R] Q) (c : R) (p : P) : AffineMap.lineMa
p f g c p = AffineMap.li…
· 使用定理 `signedDist_self`：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGr
oup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : Nor
medAd…
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `signedDist_anticomm`：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCo
mmGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 :
 NormedAd…
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
lemma signedDist_lineMap_lineMap (c₁ c₂ : ℝ) :
    signedDist v (AffineMap.lineMap p q c₁) (AffineMap.lineMap p q c₂) =
      (c₂ - c₁) * signedDist v p q := by
  trans c₂ * signedDist v p q + c₁ * signedDist v q p
  · simp [AffineMap.lineMap_apply_ring']
  · rw [sub_mul, ← signedDist_anticomm v p, mul_neg, sub_eq_add_neg]

set_option backward.isDefEq.respectTransparency false in
/-
**signedDist_lineMap_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：signedDist_lineMap_left (c : Real) : signedDist v (AffineMap.lineMap p q c
) p = -c * signedDist v p q
参数：c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AffineMap.apply_lineMap`：apply_lineMap (f : P1 ->ᵃ[k] P2) (p₀ p₁ : P1) (
c : k) : f (lineMap p₀ p₁ c) = lineMap (f p₀) (f p₁) c
· 使用引理 `ContinuousAffineMap.lineMap_apply'`：lineMap_apply' [ContinuousConstSMul 
R W] [SMulCommClass R R W] (f g : P ->ᴬ[R] Q) (c : R) (p : P) : AffineMap.lineMa
p f g c p = AffineMap.li…
· 使用定理 `signedDist_self`：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGr
oup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : Nor
medAd…
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `AffineMap.lineMap_apply_zero`：lineMap_apply_zero (p₀ p₁ : P1) : lineMap 
p₀ p₁ (0 : k) = p₀
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用引理 `signedDist_lineMap_lineMap`：signedDist_lineMap_lineMap (c₁ c₂ : Real) : 
signedDist v (AffineMap.lineMap p q c₁) (AffineMap.lineMap p q c₂) = (c₂ - c₁) *
 signedDist v p …
-/
lemma signedDist_lineMap_left (c : ℝ) :
    signedDist v (AffineMap.lineMap p q c) p = -c * signedDist v p q := by
  simpa using signedDist_lineMap_lineMap v p q c 0

set_option backward.isDefEq.respectTransparency false in
/-
**signedDist_left_lineMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：signedDist_left_lineMap (c : Real) : signedDist v p (AffineMap.lineMap p q
 c) = c * signedDist v p q
参数：c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ContinuousAffineMap.apply_lineMap`：apply_lineMap (f : P ->ᴬ[R] Q) (p₀ p₁
 : P) (c : R) : f (AffineMap.lineMap p₀ p₁ c) = AffineMap.lineMap (f p₀) (f p₁) 
c
· 使用定理 `signedDist_self`：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGr
oup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : Nor
medAd…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AffineMap.lineMap_apply_zero`：lineMap_apply_zero (p₀ p₁ : P1) : lineMap 
p₀ p₁ (0 : k) = p₀
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用引理 `signedDist_lineMap_lineMap`：signedDist_lineMap_lineMap (c₁ c₂ : Real) : 
signedDist v (AffineMap.lineMap p q c₁) (AffineMap.lineMap p q c₂) = (c₂ - c₁) *
 signedDist v p …
-/
lemma signedDist_left_lineMap (c : ℝ) :
    signedDist v p (AffineMap.lineMap p q c) = c * signedDist v p q := by
  simpa using signedDist_lineMap_lineMap v p q 0 c

set_option backward.isDefEq.respectTransparency false in
/-
**signedDist_lineMap_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：signedDist_lineMap_right (c : Real) : signedDist v (AffineMap.lineMap p q 
c) q = (1 - c) * signedDist v p q
参数：c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AffineMap.apply_lineMap`：apply_lineMap (f : P1 ->ᵃ[k] P2) (p₀ p₁ : P1) (
c : k) : f (lineMap p₀ p₁ c) = lineMap (f p₀) (f p₁) c
· 使用引理 `ContinuousAffineMap.lineMap_apply'`：lineMap_apply' [ContinuousConstSMul 
R W] [SMulCommClass R R W] (f g : P ->ᴬ[R] Q) (c : R) (p : P) : AffineMap.lineMa
p f g c p = AffineMap.li…
· 使用定理 `signedDist_self`：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGr
oup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : Nor
medAd…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AffineMap.lineMap_apply_one`：lineMap_apply_one (p₀ p₁ : P1) : lineMap p₀
 p₁ (1 : k) = p₁
· 使用引理 `signedDist_lineMap_lineMap`：signedDist_lineMap_lineMap (c₁ c₂ : Real) : 
signedDist v (AffineMap.lineMap p q c₁) (AffineMap.lineMap p q c₂) = (c₂ - c₁) *
 signedDist v p …
-/
lemma signedDist_lineMap_right (c : ℝ) :
    signedDist v (AffineMap.lineMap p q c) q = (1 - c) * signedDist v p q := by
  simpa using signedDist_lineMap_lineMap v p q c 1

set_option backward.isDefEq.respectTransparency false in
/-
**signedDist_right_lineMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：signedDist_right_lineMap (c : Real) : signedDist v q (AffineMap.lineMap p 
q c) = (c - 1) * signedDist v p q
参数：c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ContinuousAffineMap.apply_lineMap`：apply_lineMap (f : P ->ᴬ[R] Q) (p₀ p₁
 : P) (c : R) : f (AffineMap.lineMap p₀ p₁ c) = AffineMap.lineMap (f p₀) (f p₁) 
c
· 使用定理 `signedDist_self`：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGr
oup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : Nor
medAd…
· 使用定理 `AffineMap.lineMap_apply_one`：lineMap_apply_one (p₀ p₁ : P1) : lineMap p₀
 p₁ (1 : k) = p₁
· 使用引理 `signedDist_lineMap_lineMap`：signedDist_lineMap_lineMap (c₁ c₂ : Real) : 
signedDist v (AffineMap.lineMap p q c₁) (AffineMap.lineMap p q c₂) = (c₂ - c₁) *
 signedDist v p …
-/
lemma signedDist_right_lineMap (c : ℝ) :
    signedDist v q (AffineMap.lineMap p q c) = (c - 1) * signedDist v p q := by
  simpa using signedDist_lineMap_lineMap v p q 1 c

end signedDist

namespace AffineSubspace

variable (s : AffineSubspace ℝ P) [Nonempty s] [s.direction.HasOrthogonalProjection] (p q : P)

/-- The signed distance between `s` and a point, in the direction of the reference point `p`.
This is expected to be used when `p` does not lie in `s` (in the degenerate case where `p` lies
in `s`, this yields 0) and when the point at which the distance is evaluated lies in the affine
span of `s` and `p` (any component of the distance orthogonal to that span is disregarded). -/
/-
**AffineSubspace.signedInfDist** 是 Mathlib 中的一个定义，位于命名空间 `AffineSubspace`。
形式化陈述：signedInfDist : P ->ᴬ[Real] Real
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ

--- 原说明 ---
The signed distance between `s` and a point, in the direction of the reference p
oint `p`.
This is expected to be used when `p` does not lie in `s` (in the degenerate case
 where `p` lies
in `s`, this yields 0) and when the point at which the distance is evaluated lie
s in the affine
span of `s` and `p` (any component of the distance orthogonal to that span is di
sregarded).
-/
noncomputable def signedInfDist : P →ᴬ[ℝ] ℝ :=
  signedDist (p -ᵥ orthogonalProjection s p) (Classical.ofNonempty : s)
/-
**AffineSubspace.signedInfDist_def** 是 Mathlib 中的一个引理，位于命名空间 `AffineSubspace`。
形式化陈述：signedInfDist_def : s.signedInfDist p = signedDist (p -ᵥ orthogonalProject
ion s p) ↑(Classical.ofNonempty : s)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma signedInfDist_def :
    s.signedInfDist p = signedDist (p -ᵥ orthogonalProjection s p) ↑(Classical.ofNonempty : s) :=
  rfl

variable {s p q} in
/-
**AffineSubspace.signedInfDist_eq_signedDist_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `A
ffineSubspace`。
形式化陈述：signedInfDist_eq_signedDist_of_mem (h : q in s) : s.signedInfDist p = sign
edDist (p -ᵥ orthogonalProjection s p) q
参数：h : q in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `signedDist_left_congr`：signedDist_left_congr (h : ⟪v, p -ᵥ q⟫ = 0) : sig
nedDist v p = signedDist v q
· 使用定理 `Submodule.inner_left_of_mem_orthogonal`：inner_left_of_mem_orthogonal {u 
v : E} (hu : u in K) (hv : v in Kᗮ) : ⟪v, u⟫ = 0
· 使用定理 `AffineSubspace.vsub_mem_direction`：vsub_mem_direction {s : AffineSubspac
e k P} {p₁ p₂ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) : p₁ -ᵥ p₂ in s.direction
· 使用定理 `SetLike.coe_mem`：coe_mem (x : p) : (x : B) in p
· 使用定理 `EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal`：vs
ub_orthogonalProjection_mem_direction_orthogonal (s : AffineSubspace 𝕜 P) [Nonem
pty s] [s.direction.HasOrthogonalProjection] (p : P) : p -…
-/
lemma signedInfDist_eq_signedDist_of_mem (h : q ∈ s) :
    s.signedInfDist p = signedDist (p -ᵥ orthogonalProjection s p) q := by
  apply signedDist_left_congr
  apply s.direction.inner_left_of_mem_orthogonal
  · exact vsub_mem_direction (SetLike.coe_mem _) h
  · exact vsub_orthogonalProjection_mem_direction_orthogonal s p
/-
**AffineSubspace.signedInfDist_eq_signedDist_orthogonalProjection** 是 Mathlib 中的
一个引理，位于命名空间 `AffineSubspace`。
形式化陈述：signedInfDist_eq_signedDist_orthogonalProjection {x : P} : s.signedInfDist
 p x = signedDist (p -ᵥ orthogonalProjection s p) ↑(orthogonalProjection s x) x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AffineSubspace.signedInfDist_eq_signedDist_of_mem`：signedInfDist_eq_sign
edDist_of_mem (h : q in s) : s.signedInfDist p = signedDist (p -ᵥ orthogonalProj
ection s p) q
· 使用定理 `EuclideanGeometry.orthogonalProjection_mem`：orthogonalProjection_mem {s 
: AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalProjection] (p : P)
 : ↑(orthogonalProjection s p) i…
-/
lemma signedInfDist_eq_signedDist_orthogonalProjection {x : P} : s.signedInfDist p x =
    signedDist (p -ᵥ orthogonalProjection s p) ↑(orthogonalProjection s x) x := by
  rw [signedInfDist_eq_signedDist_of_mem (orthogonalProjection_mem x)]
/-
**AffineSubspace.signedInfDist_apply_self** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubsp
ace`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] (
s : AffineSubspace ℝ P) [inst_4 : Nonempty ↥s]   [inst_5 : s.direction.HasOrthog
onalProjection] (p : P),   (s.signedInfDist p) p = ‖p -ᵥ ↑((EuclideanGeometry.or
thogonalProjection s) p)‖
参数：s : AffineSubspace ℝ P；p : P；s.signedInfDist p；(EuclideanGeometry.orthogonalP
rojection s) p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AffineSubspace.signedInfDist_eq_signedDist_orthogonalProjection`：signedI
nfDist_eq_signedDist_orthogonalProjection {x : P} : s.signedInfDist p x = signed
Dist (p -ᵥ orthogonalProjection s p) ↑(orthogonalProj…
· 使用定理 `signedDist_vsub_self`：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddC
ommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 
: NormedAd…
· 使用定理 `dist_eq_norm_vsub'`：dist_eq_norm_vsub' (x y : P) : dist x y = ‖y -ᵥ x‖
-/
@[simp] lemma signedInfDist_apply_self : s.signedInfDist p p = ‖p -ᵥ orthogonalProjection s p‖ := by
  rw [signedInfDist_eq_signedDist_orthogonalProjection, signedDist_vsub_self, dist_eq_norm_vsub']

variable {s} in
/-
**AffineSubspace.signedInfDist_apply_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `AffineSub
space`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
s : AffineSubspace ℝ P} [inst_4 : Nonempty ↥s]   [inst_5 : s.direction.HasOrthog
onalProjection] (p : P) {x : P}, x ∈ s → (s.signedInfDist p) x = 0
参数：p : P；s.signedInfDist p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用引理 `AffineSubspace.signedInfDist_eq_signedDist_orthogonalProjection`：signedI
nfDist_eq_signedDist_orthogonalProjection {x : P} : s.signedInfDist p x = signed
Dist (p -ᵥ orthogonalProjection s p) ↑(orthogonalProj…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EuclideanGeometry.orthogonalProjection_eq_self_iff`：orthogonalProjection
_eq_self_iff {s : AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalPro
jection] {p : P} : ↑(orthogonalProjectio…
· 使用定理 `signedDist_self`：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGr
oup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : Nor
medAd…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma signedInfDist_apply_of_mem {x : P} (hx : x ∈ s) : s.signedInfDist p x = 0 := by
  simp [signedInfDist_eq_signedDist_orthogonalProjection, orthogonalProjection_eq_self_iff.2 hx]

variable {s p} in
/-
**AffineSubspace.signedInfDist_eq_const_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Affine
Subspace`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
s : AffineSubspace ℝ P} [inst_4 : Nonempty ↥s]   [inst_5 : s.direction.HasOrthog
onalProjection] {p : P}, p ∈ s → ↑(s.signedInfDist p) = AffineMap.const ℝ P 0
参数：s.signedInfDist p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.ext`：ext {f g : P1 ->ᵃ[k] P2} (h : forall p, f p = g p) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EuclideanGeometry.orthogonalProjection_eq_self_iff`：orthogonalProjection
_eq_self_iff {s : AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalPro
jection] {p : P} : ↑(orthogonalProjectio…
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `signedDist_zero`：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGr
oup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : Nor
medAd…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma signedInfDist_eq_const_of_mem (h : p ∈ s) :
    s.signedInfDist p = AffineMap.const ℝ P (0 : ℝ) := by
  ext x
  simp [signedInfDist_def, orthogonalProjection_eq_self_iff.2 h]

variable {s p} in
/-
**AffineSubspace.abs_signedInfDist_eq_dist_of_mem_affineSpan_insert** 是 Mathlib 
中的一个引理，位于命名空间 `AffineSubspace`。
形式化陈述：abs_signedInfDist_eq_dist_of_mem_affineSpan_insert {x : P} (h : x in affin
eSpan Real (insert p s)) : |s.signedInfDist p x| = dist x (orthogonalProjection 
s x)
参数：h : x in affineSpan Real (insert p s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.mem_affineSpan_insert_iff`：mem_affineSpan_insert_iff {s :
 AffineSubspace k P} {p₁ : P} (hp₁ : p₁ in s) (p₂ p : P) : p in affineSpan k (in
sert p₂ (s : Set P)) ↔ exists …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `ContinuousAffineMap.map_vadd`：map_vadd (f : P ->ᴬ[R] Q) (p : P) (v : V) 
: f (v +ᵥ p) = f.contLinear v +ᵥ f p
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousAffineMap.contLinear_map_vsub`：contLinear_map_vsub (f : P ->ᴬ[
R] Q) (p₁ p₂ : P) : f.contLinear (p₁ -ᵥ p₂) = f p₁ -ᵥ f p₂
· 使用定理 `AffineSubspace.signedInfDist_apply_self`：∀ {V : Type u_1} {P : Type u_2}
 [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Metric
Space P]   [inst_3 : NormedAd…
· 使用定理 `AffineSubspace.signedInfDist_apply_of_mem`：∀ {V : Type u_1} {P : Type u_
2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Metr
icSpace P]   [inst_3 : NormedAd…
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `abs_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (z : E), |‖z‖| 
= ‖z‖
· 使用定理 `AffineSubspace.instIsTopologicalAddTorsorSubtypeMemSubmoduleDirection`：∀
 {R : Type u_1} {V : Type u_2} {P : Type u_3} [inst : Ring R] [inst_1 : AddCommG
roup V] [inst_2 : _root_.Module R V]   [inst_3 : Topologica…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `EuclideanGeometry.orthogonalProjection_vsub_orthogonalProjection`：orthog
onalProjection_vsub_orthogonalProjection (s : AffineSubspace 𝕜 P) [Nonempty s] [
s.direction.HasOrthogonalProjection] (p : P) : s.direc…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `zero_vadd`：∀ (M : Type u_1) {α : Type u_5} [inst : AddMonoid M] [inst_1 
: AddAction M α] (b : α), 0 +ᵥ b = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EuclideanGeometry.orthogonalProjection_eq_self_iff`：orthogonalProjection
_eq_self_iff {s : AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalPro
jection] {p : P} : ↑(orthogonalProjectio…
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 31 条，此处仅展示前 30 条）
-/
lemma abs_signedInfDist_eq_dist_of_mem_affineSpan_insert {x : P}
    (h : x ∈ affineSpan ℝ (insert p s)) :
    |s.signedInfDist p x| = dist x (orthogonalProjection s x) := by
  rw [mem_affineSpan_insert_iff (orthogonalProjection s p).property] at h
  rcases h with ⟨r, p₀, hp₀, rfl⟩
  simp [hp₀, dist_eq_norm_vsub, orthogonalProjection_eq_self_iff.2 hp₀,
    orthogonalProjection_vsub_orthogonalProjection, norm_smul, abs_mul]
/-
**AffineSubspace.signedInfDist_singleton** 是 Mathlib 中的一个引理，位于命名空间 `AffineSubspa
ce`。
形式化陈述：signedInfDist_singleton : (affineSpan Real ({q} : Set P)).signedInfDist p 
= signedDist (p -ᵥ q) q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `EuclideanGeometry.orthogonalProjection_affineSpan_singleton`：∀ {𝕜 : Type
 u_1} {V : Type u_2} {P : Type u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGro
up V]   [inst_2 : InnerProductSpace 𝕜 V] [inst_3 …
· 使用引理 `AffineSubspace.signedInfDist_eq_signedDist_of_mem`：signedInfDist_eq_sign
edDist_of_mem (h : q in s) : s.signedInfDist p = signedDist (p -ᵥ orthogonalProj
ection s p) q
· 使用定理 `mem_affineSpan`：mem_affineSpan {p : P} {s : Set P} (hp : p in s) : p in 
affineSpan k s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
-/
lemma signedInfDist_singleton :
    (affineSpan ℝ ({q} : Set P)).signedInfDist p = signedDist (p -ᵥ q) q := by
  simpa using signedInfDist_eq_signedDist_of_mem (mem_affineSpan ℝ (Set.mem_singleton q))

end AffineSubspace

namespace Affine

namespace Simplex

variable {n : ℕ} [NeZero n] (s : Simplex ℝ P n) (i : Fin (n + 1))

/-- The signed distance between the face of `s` excluding point `i` of that simplex and a point,
in the direction of the reference point `i`. This is expected to be used when the point at which
the distance is evaluated lies in the affine span of the simplex (any component of the distance
orthogonal to that span is disregarded). In the case of a triangle, these distances are
trilinear coordinates; in a tetrahedron, they are quadriplanar coordinates. -/
/-
**Affine.Simplex.signedInfDist** 是 Mathlib 中的一个定义，位于命名空间 `Affine.Simplex`。
形式化陈述：signedInfDist : P ->ᴬ[Real] Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The signed distance between the face of `s` excluding point `i` of that simplex 
and a point,
in the direction of the reference point `i`. This is expected to be used when th
e point at which
the distance is evaluated lies in the affine span of the simplex (any component 
of the distance
orthogonal to that span is disregarded). In the case of a triangle, these distan
ces are
trilinear coordinates; in a tetrahedron, they are quadriplanar coordinates.
-/
noncomputable def signedInfDist : P →ᴬ[ℝ] ℝ :=
  AffineSubspace.signedInfDist (affineSpan ℝ (s.points '' {i}ᶜ)) (s.points i)

set_option backward.isDefEq.respectTransparency false in
/-
**Affine.Simplex.signedInfDist_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex
`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} [inst_4 : NeZero n] (s : Affine.Simplex ℝ P n) {m : ℕ} [inst_5 : NeZero m
]   (e : Fin (n + 1) ≃ Fin (m + 1)) (j : Fin (m + 1)), (s.reindex e).signedInfDi
st j = s.signedInfDist (e.symm j)
参数：s : Affine.Simplex ℝ P n；e : Fin (n + 1) ≃ Fin (m + 1)；j : Fin (m + 1)；s.rein
dex e；e.symm j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Affine.Simplex.reindex_points`：∀ {k : Type u_1} {V : Type u_2} {P : Type
 u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [
inst_3 : AddTorsor …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AffineSubspace.signedInfDist.congr_simp`：∀ {V : Type u_1} {P : Type u_2}
 [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Metric
Space P]   [inst_3 : NormedAd…
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `Set.image_compl_eq`：image_compl_eq {f : α -> β} {s : Set α} (H : Bijecti
ve f) : f '' sᶜ = (f '' s)ᶜ
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma signedInfDist_reindex {m : ℕ} [NeZero m] (e : Fin (n + 1) ≃ Fin (m + 1))
    (j : Fin (m + 1)) : (s.reindex e).signedInfDist j = s.signedInfDist (e.symm j) := by
  simp_rw [signedInfDist, reindex_points, Set.image_comp, Set.image_compl_eq e.symm.bijective,
    Set.image_singleton, Function.comp_apply]
/-
**Affine.Simplex.signedInfDist_apply_self** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simp
lex`。
形式化陈述：signedInfDist_apply_self : s.signedInfDist i (s.points i) = ‖s.points i -ᵥ
 (s.faceOpposite i).orthogonalProjectionSpan (s.points i)‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `AffineSubspace.signedInfDist_apply_self`：∀ {V : Type u_1} {P : Type u_2}
 [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Metric
Space P]   [inst_3 : NormedAd…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.range_faceOpposite_points`：∀ {k : Type u_1} {V : Type u_2
} {P : Type u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Modu
le k V]   [inst_3 : AddTorsor …
· 使用定理 `EuclideanGeometry.orthogonalProjection_congr`：orthogonalProjection_congr
 {s₁ s₂ : AffineSubspace 𝕜 P} {p₁ p₂ : P} [Nonempty s₁] [s₁.direction.HasOrthogo
nalProjection] (h : s₁ = s₂) (hp :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma signedInfDist_apply_self :
    s.signedInfDist i (s.points i) =
      ‖s.points i -ᵥ (s.faceOpposite i).orthogonalProjectionSpan (s.points i)‖ :=
  (AffineSubspace.signedInfDist_apply_self _ _).trans <| by simp [orthogonalProjectionSpan]

variable {i} in
/-
**Affine.Simplex.signedInfDist_apply_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Sim
plex`。
形式化陈述：signedInfDist_apply_of_ne {j : Fin (n + 1)} (h : j != i) : s.signedInfDist
 i (s.points j) = 0
参数：n + 1；h : j != i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.signedInfDist_apply_of_mem`：∀ {V : Type u_1} {P : Type u_
2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Metr
icSpace P]   [inst_3 : NormedAd…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Affine.Simplex.mem_affineSpan_image_iff`：∀ {k : Type u_1} {V : Type u_2}
 {P : Type u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Modul
e k V]   [inst_3 : AddTorsor …
-/
lemma signedInfDist_apply_of_ne {j : Fin (n + 1)} (h : j ≠ i) :
    s.signedInfDist i (s.points j) = 0 :=
  AffineSubspace.signedInfDist_apply_of_mem _ (s.mem_affineSpan_image_iff.2 h)
/-
**Affine.Simplex.signedInfDist_affineCombination** 是 Mathlib 中的一个引理，位于命名空间 `Affi
ne.Simplex`。
形式化陈述：signedInfDist_affineCombination {w : Fin (n + 1) -> Real} (h : ∑ i, w i = 
1) : s.signedInfDist i (Finset.univ.affineCombination Real s.points w) = w i * ‖
s.points i -ᵥ (s.faceOpposite i).orthogonalProjectionSpan (s.points i)‖
参数：n + 1；h : ∑ i, w i = 1。
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
· 使用定理 `ContinuousAffineMap.coe_toAffineMap`：coe_toAffineMap (f : P ->ᴬ[R] Q) : 
((f : P ->ᵃ[R] Q) : P -> Q) = f
· 使用定理 `Finset.map_affineCombination`：map_affineCombination {V₂ P₂ : Type*} [Add
CommGroup V₂] [Module k V₂] [AffineSpace V₂ P₂] (p : ι -> P) (w : ι -> k) (hw : 
s.sum w = 1) (f : …
· 使用引理 `Finset.affineCombination_apply_eq_lineMap_sum`：affineCombination_apply_e
q_lineMap_sum [DecidableEq ι] (w : ι -> k) (p : ι -> P) (p₁ p₂ : P) (s' : Finset
 ι) (h : ∑ i in s, w i = 1) (hp₂ : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.inter_singleton_of_mem`：inter_singleton_of_mem {a : α} {s : Finse
t α} (h : a in s) : s inter {a} = {a}
· 使用引理 `Affine.Simplex.signedInfDist_apply_self`：signedInfDist_apply_self : s.si
gnedInfDist i (s.points i) = ‖s.points i -ᵥ (s.faceOpposite i).orthogonalProject
ionSpan (s.points i)‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用引理 `Affine.Simplex.signedInfDist_apply_of_ne`：signedInfDist_apply_of_ne {j :
 Fin (n + 1)} (h : j != i) : s.signedInfDist i (s.points j) = 0
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma signedInfDist_affineCombination {w : Fin (n + 1) → ℝ} (h : ∑ i, w i = 1) :
    s.signedInfDist i (Finset.univ.affineCombination ℝ s.points w) = w i * ‖s.points i -ᵥ
      (s.faceOpposite i).orthogonalProjectionSpan (s.points i)‖ := by
  rw [← ContinuousAffineMap.coe_toAffineMap, Finset.map_affineCombination _ _ _ h,
    Finset.univ.affineCombination_apply_eq_lineMap_sum w
      ((s.signedInfDist i).toAffineMap ∘ s.points) 0
      ‖s.points i -ᵥ (s.faceOpposite i).orthogonalProjectionSpan (s.points i)‖
      {i} h]
  · simp [AffineMap.lineMap_apply]
  · simp [signedInfDist_apply_self]
  · simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and,
      Function.comp_apply]
    intro j hj
    exact s.signedInfDist_apply_of_ne hj

variable {s} in
/-
**Affine.Simplex.abs_signedInfDist_eq_dist_of_mem_affineSpan_range** 是 Mathlib 中
的一个引理，位于命名空间 `Affine.Simplex`。
形式化陈述：abs_signedInfDist_eq_dist_of_mem_affineSpan_range {p : P} (h : p in affine
Span Real (Set.range s.points)) : |s.signedInfDist i p| = dist p ((s.faceOpposit
e i).orthogonalProjectionSpan p)
参数：h : p in affineSpan Real (Set.range s.points)。
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
· 使用定理 `Affine.Simplex.signedInfDist.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst
 : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace 
P]   [inst_3 : NormedAd…
· 使用引理 `AffineSubspace.abs_signedInfDist_eq_dist_of_mem_affineSpan_insert`：abs_s
ignedInfDist_eq_dist_of_mem_affineSpan_insert {x : P} (h : x in affineSpan Real 
(insert p s)) : |s.signedInfDist p x| = dist x (orthogo…
· 使用定理 `affineSpan_insert_affineSpan`：affineSpan_insert_affineSpan (p : P) (ps :
 Set P) : affineSpan k (insert p (affineSpan k ps : Set P)) = affineSpan k (inse
rt p ps)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.insert_image_compl_eq_range`：insert_image_compl_eq_range (f : α -> β
) (x : α) : insert (f x) (f '' {x}ᶜ) = range f
· 使用定理 `Affine.Simplex.orthogonalProjectionSpan.eq_1`：∀ {𝕜 : Type u_1} {V : Type
 u_2} {P : Type u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup V]   [inst_2
 : InnerProductSpace 𝕜 V] [inst_3 …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Affine.Simplex.range_faceOpposite_points`：∀ {k : Type u_1} {V : Type u_2
} {P : Type u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Modu
le k V]   [inst_3 : AddTorsor …
· 使用定理 `EuclideanGeometry.orthogonalProjection_congr`：orthogonalProjection_congr
 {s₁ s₂ : AffineSubspace 𝕜 P} {p₁ p₂ : P} [Nonempty s₁] [s₁.direction.HasOrthogo
nalProjection] (h : s₁ = s₂) (hp :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma abs_signedInfDist_eq_dist_of_mem_affineSpan_range {p : P}
    (h : p ∈ affineSpan ℝ (Set.range s.points)) :
    |s.signedInfDist i p| =
      dist p ((s.faceOpposite i).orthogonalProjectionSpan p) := by
  rw [signedInfDist, AffineSubspace.abs_signedInfDist_eq_dist_of_mem_affineSpan_insert,
    orthogonalProjectionSpan]
  · simp_rw [range_faceOpposite_points]
  rw [affineSpan_insert_affineSpan]
  convert! h
  exact Set.insert_image_compl_eq_range s.points i

end Simplex

end Affine

