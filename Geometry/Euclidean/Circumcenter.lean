/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Geometry.Euclidean.Projection
public import Mathlib.Geometry.Euclidean.Sphere.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Centroid
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Tactic.DeriveFintype

/-!
# Circumcenter and circumradius

This file proves some lemmas on points equidistant from a set of
points, and defines the circumradius and circumcenter of a simplex.
There are also some definitions for use in calculations where it is
convenient to work with affine combinations of vertices together with
the circumcenter.

## Main definitions

* `circumcenter` and `circumradius` are the circumcenter and
  circumradius of a simplex.

## References

* https://en.wikipedia.org/wiki/Circumscribed_circle

-/

@[expose] public section

noncomputable section

open RealInnerProductSpace

namespace EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

open AffineSubspace

/-- The induction step for the existence and uniqueness of the
circumcenter.  Given a nonempty set of points in a nonempty affine
subspace whose direction is complete, such that there is a unique
(circumcenter, circumradius) pair for those points in that subspace,
and a point `p` not in that subspace, there is a unique (circumcenter,
circumradius) pair for the set with `p` added, in the span of the
subspace with `p` added. -/
/-
**EuclideanGeometry.existsUnique_dist_eq_of_insert** 是 Mathlib 中的一个定理，位于命名空间 `Eu
clideanGeometry`。
形式化陈述：existsUnique_dist_eq_of_insert {s : AffineSubspace Real P} [s.direction.Ha
sOrthogonalProjection] {ps : Set P} (hnps : ps.Nonempty) {p : P} (hps : ps subse
teq s) (hp : p ∉ s) (hu : exists! cs : Sphere P, cs.center in s ∧ ps subseteq (c
s : Set P)) : exists! cs₂ : Sphere P, cs₂.center in affineSpan Real (insert p (s
 : Set P)) ∧ insert p ps subseteq (cs₂ : Set P)
参数：hnps : ps.Nonempty；hps : ps subseteq s；hp : p ∉ s；hu : exists! cs : Sphere P,
 cs.center in s ∧ ps subseteq (cs : Set P)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `EuclideanGeometry.dist_orthogonalProjection_ne_zero_of_notMem`：dist_orth
ogonalProjection_ne_zero_of_notMem {s : AffineSubspace 𝕜 P} [Nonempty s] [s.dire
ction.HasOrthogonalProjection] {p : P} (hp : p ∉ s)…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AffineSubspace.vadd_mem_of_mem_direction`：vadd_mem_of_mem_direction {s :
 AffineSubspace k P} {v : V} (hv : v in s.direction) {p : P} (hp : p in s) : v +
ᵥ p in s
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `vsub_mem_vectorSpan`：vsub_mem_vectorSpan {s : Set P} {p₁ p₂ : P} (hp₁ : 
p₁ in s) (hp₂ : p₂ in s) : p₁ -ᵥ p₂ in vectorSpan k s
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `Set.mem_insert_of_mem`：mem_insert_of_mem {x : α} {s : Set α} (y : α) : x
 in s -> x in insert y s
· 使用定理 `EuclideanGeometry.orthogonalProjection_mem`：orthogonalProjection_mem {s 
: AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalProjection] (p : P)
 : ↑(orthogonalProjection s p) i…
· 使用定理 `mem_affineSpan`：mem_affineSpan {p : P} {s : Set P} (hp : p in s) : p in 
affineSpan k s
· 使用定理 `EuclideanGeometry.Sphere.mem_coe`：∀ {P : Type u_2} [inst : MetricSpace P
] {p : P} {s : EuclideanGeometry.Sphere P},   p ∈ Metric.sphere s.center s.radiu
s ↔ p ∈ s
· 使用定理 `EuclideanGeometry.mem_sphere`：mem_sphere {p : P} {s : Sphere P} : p in s
 ↔ dist p s.center = s.radius
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_self_inj_of_nonneg`：mul_self_inj_of_nonneg {α : Type*} [CommRing α] 
[NoZeroDivisors α] [PartialOrder α] [IsStrictOrderedRing α] {a b : α} (a0 : 0 <=
 a) (b0 : 0 …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `Real.sqrt_nonneg`：∀ (x : ℝ), 0 ≤ √x
· 使用定理 `Real.mul_self_sqrt`：mul_self_sqrt (h : 0 <= x) : √x * √x = x
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
（共 141 条，此处仅展示前 30 条）

--- 原说明 ---
The induction step for the existence and uniqueness of the
circumcenter.  Given a nonempty set of points in a nonempty affine
subspace whose direction is complete, such that there is a unique
(circumcenter, circumradius) pair for those points in that subspace,
and a point `p` not in that subspace, there is a unique (circumcenter,
circumradius) pair for the set with `p` added, in the span of the
subspace with `p` added.
-/
theorem existsUnique_dist_eq_of_insert {s : AffineSubspace ℝ P}
    [s.direction.HasOrthogonalProjection] {ps : Set P} (hnps : ps.Nonempty) {p : P} (hps : ps ⊆ s)
    (hp : p ∉ s) (hu : ∃! cs : Sphere P, cs.center ∈ s ∧ ps ⊆ (cs : Set P)) :
    ∃! cs₂ : Sphere P,
      cs₂.center ∈ affineSpan ℝ (insert p (s : Set P)) ∧ insert p ps ⊆ (cs₂ : Set P) := by
  have : Nonempty s := Set.Nonempty.to_subtype (hnps.mono hps)
  rcases hu with ⟨⟨cc, cr⟩, ⟨hcc, hcr⟩, hcccru⟩
  simp only at hcc hcr hcccru
  let x := dist cc (orthogonalProjection s p)
  let y := dist p (orthogonalProjection s p)
  have hy0 : y ≠ 0 := dist_orthogonalProjection_ne_zero_of_notMem hp
  let ycc₂ := (x * x + y * y - cr * cr) / (2 * y)
  let cc₂ := (ycc₂ / y) • (p -ᵥ orthogonalProjection s p : V) +ᵥ cc
  let cr₂ := √(cr * cr + ycc₂ * ycc₂)
  use ⟨cc₂, cr₂⟩
  simp -zeta -proj only
  have hpo : p = (1 : ℝ) • (p -ᵥ orthogonalProjection s p : V) +ᵥ
    (orthogonalProjection s p : P) := by
    simp
  constructor
  · constructor
    · refine vadd_mem_of_mem_direction ?_ (mem_affineSpan ℝ (Set.mem_insert_of_mem _ hcc))
      rw [direction_affineSpan]
      exact
        Submodule.smul_mem _ _
          (vsub_mem_vectorSpan ℝ (Set.mem_insert _ _)
            (Set.mem_insert_of_mem _ (orthogonalProjection_mem _)))
    · intro p₁ hp₁
      rw [Sphere.mem_coe, mem_sphere, ← mul_self_inj_of_nonneg dist_nonneg (Real.sqrt_nonneg _),
        Real.mul_self_sqrt (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))]
      rcases hp₁ with hp₁ | hp₁
      · rw [hp₁, hpo,
          dist_sq_smul_orthogonal_vadd_smul_orthogonal_vadd (orthogonalProjection_mem p) hcc _ _
            (vsub_orthogonalProjection_mem_direction_orthogonal s p),
          Real.norm_eq_abs, abs_mul_abs_self, ← dist_eq_norm_vsub V p, dist_comm _ cc]
        simp only [ycc₂]
        field
      · rw [dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq _ (hps hp₁),
          orthogonalProjection_vadd_smul_vsub_orthogonalProjection _ _ hcc, Subtype.coe_mk,
          dist_of_mem_subset_mk_sphere hp₁ hcr, dist_eq_norm_vsub V cc₂ cc, vadd_vsub, norm_smul, ←
          dist_eq_norm_vsub V, Real.norm_eq_abs, abs_div, abs_of_nonneg dist_nonneg,
          div_mul_cancel₀ _ hy0, abs_mul_abs_self]
  · rintro ⟨cc₃, cr₃⟩ ⟨hcc₃, hcr₃⟩
    simp only at hcc₃ hcr₃
    obtain ⟨t₃, cc₃', hcc₃', hcc₃''⟩ :
      ∃ r : ℝ, ∃ p0 ∈ s, cc₃ = r • (p -ᵥ ↑((orthogonalProjection s) p)) +ᵥ p0 := by
      rwa [mem_affineSpan_insert_iff (orthogonalProjection_mem p)] at hcc₃
    have hcr₃' : ∃ r, ∀ p₁ ∈ ps, dist p₁ cc₃ = r :=
      ⟨cr₃, fun p₁ hp₁ => dist_of_mem_subset_mk_sphere (Set.mem_insert_of_mem _ hp₁) hcr₃⟩
    rw [exists_dist_eq_iff_exists_dist_orthogonalProjection_eq hps cc₃, hcc₃'',
      orthogonalProjection_vadd_smul_vsub_orthogonalProjection _ _ hcc₃'] at hcr₃'
    obtain ⟨cr₃', hcr₃'⟩ := hcr₃'
    have hu := hcccru ⟨cc₃', cr₃'⟩
    simp only at hu
    replace hu := hu ⟨hcc₃', hcr₃'⟩
    cases hu
    have hcr₃val : cr₃ = √(cr * cr + t₃ * y * (t₃ * y)) := by
      obtain ⟨p0, hp0⟩ := hnps
      have h' : ↑(⟨cc, hcc₃'⟩ : s) = cc := rfl
      rw [← dist_of_mem_subset_mk_sphere (Set.mem_insert_of_mem _ hp0) hcr₃, hcc₃'', ←
        mul_self_inj_of_nonneg dist_nonneg (Real.sqrt_nonneg _),
        Real.mul_self_sqrt (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)),
        dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq _ (hps hp0),
        orthogonalProjection_vadd_smul_vsub_orthogonalProjection _ _ hcc₃', h',
        dist_of_mem_subset_mk_sphere hp0 hcr, dist_eq_norm_vsub V _ cc, vadd_vsub, norm_smul, ←
        dist_eq_norm_vsub V p, Real.norm_eq_abs, ← mul_assoc, mul_comm _ |t₃|, ← mul_assoc,
        abs_mul_abs_self]
      ring
    replace hcr₃ := dist_of_mem_subset_mk_sphere (Set.mem_insert _ _) hcr₃
    rw [hpo, hcc₃'', hcr₃val, ← mul_self_inj_of_nonneg dist_nonneg (Real.sqrt_nonneg _),
      dist_sq_smul_orthogonal_vadd_smul_orthogonal_vadd (orthogonalProjection_mem p) hcc₃' _ _
        (vsub_orthogonalProjection_mem_direction_orthogonal s p),
      Real.norm_eq_abs, abs_mul_abs_self, dist_comm, ← dist_eq_norm_vsub V p,
      Real.mul_self_sqrt (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))] at hcr₃
    have : t₃ * y = ycc₂ := by grind
    grind

/-- Given a finite nonempty affinely independent family of points,
there is a unique (circumcenter, circumradius) pair for those points
in the affine subspace they span. -/
/-
**EuclideanGeometry._root_.AffineIndependent.existsUnique_dist_eq** 是 Mathlib 中的
一个定理，位于命名空间 `EuclideanGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a finite nonempty affinely independent family of points,
there is a unique (circumcenter, circumradius) pair for those points
in the affine subspace they span.
-/
theorem _root_.AffineIndependent.existsUnique_dist_eq {ι : Type*} [hne : Nonempty ι] [Finite ι]
    {p : ι → P} (ha : AffineIndependent ℝ p) :
    ∃! cs : Sphere P, cs.center ∈ affineSpan ℝ (Set.range p) ∧ Set.range p ⊆ (cs : Set P) := by
  cases nonempty_fintype ι
  induction hn : Fintype.card ι generalizing ι with
  | zero =>
    exfalso
    have h := Fintype.card_pos_iff.2 hne
    lia
  | succ m hm =>
    rcases m with - | m
    · rw [Fintype.card_eq_one_iff] at hn
      obtain ⟨i, hi⟩ := hn
      have : Unique ι := ⟨⟨i⟩, hi⟩
      use ⟨p i, 0⟩
      simp only [Set.range_unique, AffineSubspace.mem_affineSpan_singleton]
      constructor
      · simp_rw [hi default, Set.singleton_subset_iff]
        exact ⟨⟨⟩, by simp only [Metric.sphere_zero, Set.mem_singleton_iff]⟩
      · rintro ⟨cc, cr⟩
        rintro ⟨rfl, hdist⟩
        replace hdist : 0 = cr := by simpa using hdist
        rw [hi default, hdist]
    · have i := hne.some
      let ι2 := { x // x ≠ i }
      classical
      have hc : Fintype.card ι2 = m + 1 := by
        rw [Fintype.card_of_subtype {x | x ≠ i}]
        · rw [Finset.filter_not, Finset.filter_eq' _ i, if_pos (Finset.mem_univ _),
            Finset.card_sdiff, Finset.card_univ, hn]
          simp
        · simp
      have : Nonempty ι2 := Fintype.card_pos_iff.1 (hc.symm ▸ Nat.zero_lt_succ _)
      have ha2 : AffineIndependent ℝ fun i2 : ι2 => p i2 := ha.subtype _
      replace hm := hm ha2 _ hc
      have hr : Set.range p = insert (p i) (Set.range fun i2 : ι2 => p i2) := by
        change _ = insert _ (Set.range fun i2 : { x | x ≠ i } => p i2)
        rw [← Set.image_eq_range, ← Set.image_univ, ← Set.image_insert_eq]
        congr with j
        simp [Classical.em]
      rw [hr, ← affineSpan_insert_affineSpan]
      refine existsUnique_dist_eq_of_insert (Set.range_nonempty _) (subset_affineSpan ℝ _) ?_ hm
      convert! ha.notMem_affineSpan_sdiff i Set.univ
      change (Set.range fun i2 : { x | x ≠ i } => p i2) = _
      rw [← Set.image_eq_range]
      congr 1 with j
      simp

end EuclideanGeometry

namespace Affine

namespace Simplex

open Finset AffineSubspace EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- The circumsphere of a simplex. -/
/-
**Affine.Simplex.circumsphere** 是 Mathlib 中的一个定义，位于命名空间 `Affine.Simplex`。
形式化陈述：circumsphere {n : Nat} (s : Simplex Real P n) : Sphere P
参数：s : Simplex Real P n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The circumsphere of a simplex.
-/
def circumsphere {n : ℕ} (s : Simplex ℝ P n) : Sphere P :=
  s.independent.existsUnique_dist_eq.choose

/-- The property satisfied by the circumsphere. -/
/-
**Affine.Simplex.circumsphere_unique_dist_eq** 是 Mathlib 中的一个定理，位于命名空间 `Affine.S
implex`。
形式化陈述：circumsphere_unique_dist_eq {n : Nat} (s : Simplex Real P n) : (s.circumsp
here.center in affineSpan Real (Set.range s.points) ∧ Set.range s.points subsete
q s.circumsphere) ∧ forall cs : Sphere P, cs.center in affineSpan Real (Set.rang
e s.points) ∧ Set.range s.points subseteq cs -> cs = s.circumsphere
参数：s : Simplex Real P n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `AffineIndependent.existsUnique_dist_eq`：∀ {V : Type u_1} {P : Type u_2} 
[inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricS
pace P]   [inst_3 : NormedAd…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Affine.Simplex.independent`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [ins
t_3 : AddTorsor …

--- 原说明 ---
The property satisfied by the circumsphere.
-/
theorem circumsphere_unique_dist_eq {n : ℕ} (s : Simplex ℝ P n) :
    (s.circumsphere.center ∈ affineSpan ℝ (Set.range s.points) ∧
        Set.range s.points ⊆ s.circumsphere) ∧
      ∀ cs : Sphere P,
        cs.center ∈ affineSpan ℝ (Set.range s.points) ∧ Set.range s.points ⊆ cs →
          cs = s.circumsphere :=
  s.independent.existsUnique_dist_eq.choose_spec

/-- The circumcenter of a simplex. -/
/-
**Affine.Simplex.circumcenter** 是 Mathlib 中的一个定义，位于命名空间 `Affine.Simplex`。
形式化陈述：circumcenter {n : Nat} (s : Simplex Real P n) : P
参数：s : Simplex Real P n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The circumcenter of a simplex.
-/
def circumcenter {n : ℕ} (s : Simplex ℝ P n) : P :=
  s.circumsphere.center

/-- The circumradius of a simplex. -/
/-
**Affine.Simplex.circumradius** 是 Mathlib 中的一个定义，位于命名空间 `Affine.Simplex`。
形式化陈述：circumradius {n : Nat} (s : Simplex Real P n) : Real
参数：s : Simplex Real P n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The circumradius of a simplex.
-/
def circumradius {n : ℕ} (s : Simplex ℝ P n) : ℝ :=
  s.circumsphere.radius

/-- The center of the circumsphere is the circumcenter. -/
@[simp]
/-
**Affine.Simplex.circumsphere_center** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：circumsphere_center {n : Nat} (s : Simplex Real P n) : s.circumsphere.cent
er = s.circumcenter
参数：s : Simplex Real P n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The center of the circumsphere is the circumcenter.
-/
theorem circumsphere_center {n : ℕ} (s : Simplex ℝ P n) : s.circumsphere.center = s.circumcenter :=
  rfl

/-- The radius of the circumsphere is the circumradius. -/
@[simp]
/-
**Affine.Simplex.circumsphere_radius** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：circumsphere_radius {n : Nat} (s : Simplex Real P n) : s.circumsphere.radi
us = s.circumradius
参数：s : Simplex Real P n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The radius of the circumsphere is the circumradius.
-/
theorem circumsphere_radius {n : ℕ} (s : Simplex ℝ P n) : s.circumsphere.radius = s.circumradius :=
  rfl

/-- The circumcenter lies in the affine span. -/
/-
**Affine.Simplex.circumcenter_mem_affineSpan** 是 Mathlib 中的一个定理，位于命名空间 `Affine.S
implex`。
形式化陈述：circumcenter_mem_affineSpan {n : Nat} (s : Simplex Real P n) : s.circumcen
ter in affineSpan Real (Set.range s.points)
参数：s : Simplex Real P n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Affine.Simplex.circumsphere_unique_dist_eq`：circumsphere_unique_dist_eq 
{n : Nat} (s : Simplex Real P n) : (s.circumsphere.center in affineSpan Real (Se
t.range s.points) ∧ Set.range s.…

--- 原说明 ---
The circumcenter lies in the affine span.
-/
theorem circumcenter_mem_affineSpan {n : ℕ} (s : Simplex ℝ P n) :
    s.circumcenter ∈ affineSpan ℝ (Set.range s.points) :=
  s.circumsphere_unique_dist_eq.1.1

/-- All points have distance from the circumcenter equal to the
circumradius. -/
@[simp]
/-
**Affine.Simplex.dist_circumcenter_eq_circumradius** 是 Mathlib 中的一个定理，位于命名空间 `Af
fine.Simplex`。
形式化陈述：dist_circumcenter_eq_circumradius {n : Nat} (s : Simplex Real P n) (i : Fi
n (n + 1)) : dist (s.points i) s.circumcenter = s.circumradius
参数：s : Simplex Real P n；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.dist_of_mem_subset_sphere`：dist_of_mem_subset_sphere {
p : P} {ps : Set P} {s : Sphere P} (hp : p in ps) (hps : ps subseteq (s : Set P)
) : dist p s.center = s.radius
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Affine.Simplex.circumsphere_unique_dist_eq`：circumsphere_unique_dist_eq 
{n : Nat} (s : Simplex Real P n) : (s.circumsphere.center in affineSpan Real (Se
t.range s.points) ∧ Set.range s.…

--- 原说明 ---
All points have distance from the circumcenter equal to the
circumradius.
-/
theorem dist_circumcenter_eq_circumradius {n : ℕ} (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    dist (s.points i) s.circumcenter = s.circumradius :=
  dist_of_mem_subset_sphere (Set.mem_range_self _) s.circumsphere_unique_dist_eq.1.2

/-- All points lie in the circumsphere. -/
/-
**Affine.Simplex.mem_circumsphere** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：mem_circumsphere {n : Nat} (s : Simplex Real P n) (i : Fin (n + 1)) : s.po
ints i in s.circumsphere
参数：s : Simplex Real P n；i : Fin (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.dist_circumcenter_eq_circumradius`：dist_circumcenter_eq_c
ircumradius {n : Nat} (s : Simplex Real P n) (i : Fin (n + 1)) : dist (s.points 
i) s.circumcenter = s.circumradius

--- 原说明 ---
All points lie in the circumsphere.
-/
theorem mem_circumsphere {n : ℕ} (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    s.points i ∈ s.circumsphere :=
  s.dist_circumcenter_eq_circumradius i

/-- All points have distance to the circumcenter equal to the
circumradius. -/
@[simp]
/-
**Affine.Simplex.dist_circumcenter_eq_circumradius'** 是 Mathlib 中的一个定理，位于命名空间 `A
ffine.Simplex`。
形式化陈述：dist_circumcenter_eq_circumradius' {n : Nat} (s : Simplex Real P n) : fora
ll i, dist s.circumcenter (s.points i) = s.circumradius
参数：s : Simplex Real P n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `Affine.Simplex.dist_circumcenter_eq_circumradius`：dist_circumcenter_eq_c
ircumradius {n : Nat} (s : Simplex Real P n) (i : Fin (n + 1)) : dist (s.points 
i) s.circumcenter = s.circumradius

--- 原说明 ---
All points have distance to the circumcenter equal to the
circumradius.
-/
theorem dist_circumcenter_eq_circumradius' {n : ℕ} (s : Simplex ℝ P n) :
    ∀ i, dist s.circumcenter (s.points i) = s.circumradius := by
  intro i
  rw [dist_comm]
  exact dist_circumcenter_eq_circumradius _ _

/-- Given a point in the affine span from which all the points are
equidistant, that point is the circumcenter. -/
/-
**Affine.Simplex.eq_circumcenter_of_dist_eq** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Si
mplex`。
形式化陈述：eq_circumcenter_of_dist_eq {n : Nat} (s : Simplex Real P n) {p : P} (hp : 
p in affineSpan Real (Set.range s.points)) {r : Real} (hr : forall i, dist (s.po
ints i) p = r) : p = s.circumcenter
参数：s : Simplex Real P n；hp : p in affineSpan Real (Set.range s.points)；hr : fora
ll i, dist (s.points i) p = r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Affine.Simplex.circumsphere_unique_dist_eq`：circumsphere_unique_dist_eq 
{n : Nat} (s : Simplex Real P n) : (s.circumsphere.center in affineSpan Real (Se
t.range s.points) ∧ Set.range s.…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `EuclideanGeometry.subset_sphere`：subset_sphere {ps : Set P} {s : Sphere 
P} : ps subseteq s ↔ forall p in ps, p in s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p

--- 原说明 ---
Given a point in the affine span from which all the points are
equidistant, that point is the circumcenter.
-/
theorem eq_circumcenter_of_dist_eq {n : ℕ} (s : Simplex ℝ P n) {p : P}
    (hp : p ∈ affineSpan ℝ (Set.range s.points)) {r : ℝ} (hr : ∀ i, dist (s.points i) p = r) :
    p = s.circumcenter := by
  have h := s.circumsphere_unique_dist_eq.2 ⟨p, r⟩
  simp only [hp, hr, forall_const, subset_sphere (s := ⟨p, r⟩), Sphere.ext_iff,
    Set.forall_mem_range, mem_sphere, true_and] at h
  exact h.1

/-- Given a point in the affine span from which all the points are
equidistant, that distance is the circumradius. -/
/-
**Affine.Simplex.eq_circumradius_of_dist_eq** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Si
mplex`。
形式化陈述：eq_circumradius_of_dist_eq {n : Nat} (s : Simplex Real P n) {p : P} (hp : 
p in affineSpan Real (Set.range s.points)) {r : Real} (hr : forall i, dist (s.po
ints i) p = r) : r = s.circumradius
参数：s : Simplex Real P n；hp : p in affineSpan Real (Set.range s.points)；hr : fora
ll i, dist (s.points i) p = r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Affine.Simplex.circumsphere_unique_dist_eq`：circumsphere_unique_dist_eq 
{n : Nat} (s : Simplex Real P n) : (s.circumsphere.center in affineSpan Real (Se
t.range s.points) ∧ Set.range s.…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `EuclideanGeometry.subset_sphere`：subset_sphere {ps : Set P} {s : Sphere 
P} : ps subseteq s ↔ forall p in ps, p in s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p

--- 原说明 ---
Given a point in the affine span from which all the points are
equidistant, that distance is the circumradius.
-/
theorem eq_circumradius_of_dist_eq {n : ℕ} (s : Simplex ℝ P n) {p : P}
    (hp : p ∈ affineSpan ℝ (Set.range s.points)) {r : ℝ} (hr : ∀ i, dist (s.points i) p = r) :
    r = s.circumradius := by
  have h := s.circumsphere_unique_dist_eq.2 ⟨p, r⟩
  simp only [hp, hr, forall_const, subset_sphere (s := ⟨p, r⟩), Sphere.ext_iff,
    Set.forall_mem_range, mem_sphere, true_and] at h
  exact h.2

/-- The circumradius is non-negative. -/
/-
**Affine.Simplex.circumradius_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：circumradius_nonneg {n : Nat} (s : Simplex Real P n) : 0 <= s.circumradius
参数：s : Simplex Real P n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `Affine.Simplex.dist_circumcenter_eq_circumradius`：dist_circumcenter_eq_c
ircumradius {n : Nat} (s : Simplex Real P n) (i : Fin (n + 1)) : dist (s.points 
i) s.circumcenter = s.circumradius

--- 原说明 ---
The circumradius is non-negative.
-/
theorem circumradius_nonneg {n : ℕ} (s : Simplex ℝ P n) : 0 ≤ s.circumradius :=
  s.dist_circumcenter_eq_circumradius 0 ▸ dist_nonneg

/-- The circumradius of a simplex with at least two points is
positive. -/
/-
**Affine.Simplex.circumradius_pos** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：circumradius_pos {n : Nat} (s : Simplex Real P (n + 1)) : 0 < s.circumradi
us
参数：s : Simplex Real P (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Affine.Simplex.circumradius_nonneg`：circumradius_nonneg {n : Nat} (s : S
implex Real P n) : 0 <= s.circumradius
· 使用定理 `Affine.Simplex.dist_circumcenter_eq_circumradius`：dist_circumcenter_eq_c
ircumradius {n : Nat} (s : Simplex Real P n) (i : Fin (n + 1)) : dist (s.points 
i) s.circumcenter = s.circumradius
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `AffineIndependent.injective`：∀ {k : Type u_1} {V : Type u_2} {P : Type u
_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [in
st_3 : AddTorsor …
· 使用定理 `Affine.Simplex.independent`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [ins
t_3 : AddTorsor …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib`：∀ {n m : ℕ} [NeZero n] [inst : NeZer
o (OfNat.ofNat m)], NeZero (OfNat.ofNat m)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False

--- 原说明 ---
The circumradius of a simplex with at least two points is
positive.
-/
theorem circumradius_pos {n : ℕ} (s : Simplex ℝ P (n + 1)) : 0 < s.circumradius := by
  refine lt_of_le_of_ne s.circumradius_nonneg ?_
  intro h
  have hr := s.dist_circumcenter_eq_circumradius
  simp_rw [← h, dist_eq_zero] at hr
  have h01 := s.independent.injective.ne (by simp : (0 : Fin (n + 2)) ≠ 1)
  simp [hr] at h01

/-- The circumcenter of a 0-simplex equals its unique point. -/
/-
**Affine.Simplex.circumcenter_eq_point** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex
`。
形式化陈述：circumcenter_eq_point (s : Simplex Real P 0) (i : Fin 1) : s.circumcenter 
= s.points i
参数：s : Simplex Real P 0；i : Fin 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.circumcenter_mem_affineSpan`：circumcenter_mem_affineSpan 
{n : Nat} (s : Simplex Real P n) : s.circumcenter in affineSpan Real (Set.range 
s.points)
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.eq_zero`：eq_zero (n : Fin 1) : n = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.range_unique`：range_unique [Unique ι] : range f = {f default}
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α

--- 原说明 ---
The circumcenter of a 0-simplex equals its unique point.
-/
theorem circumcenter_eq_point (s : Simplex ℝ P 0) (i : Fin 1) : s.circumcenter = s.points i := by
  have h := s.circumcenter_mem_affineSpan
  have : Unique (Fin 1) := ⟨⟨0, by decide⟩, fun a => by simp only [Fin.eq_zero]⟩
  simp only [Set.range_unique, AffineSubspace.mem_affineSpan_singleton] at h
  rw [h]
  congr
  simp only [eq_iff_true_of_subsingleton]
/-
**Affine.Simplex.circumcenter_ne_point** 是 Mathlib 中的一个引理，位于命名空间 `Affine.Simplex
`。
形式化陈述：circumcenter_ne_point {n : Nat} (s : Simplex Real P (n + 1)) (i : Fin (n +
 2)) : s.circumcenter != s.points i
参数：s : Simplex Real P (n + 1)；i : Fin (n + 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dist_ne_zero`：dist_ne_zero {x y : γ} : dist x y != 0 ↔ x != y
· 使用定理 `Affine.Simplex.dist_circumcenter_eq_circumradius'`：dist_circumcenter_eq_
circumradius' {n : Nat} (s : Simplex Real P n) : forall i, dist s.circumcenter (
s.points i) = s.circumradius
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Affine.Simplex.circumradius_pos`：circumradius_pos {n : Nat} (s : Simplex
 Real P (n + 1)) : 0 < s.circumradius
-/
lemma circumcenter_ne_point {n : ℕ} (s : Simplex ℝ P (n + 1)) (i : Fin (n + 2)) :
    s.circumcenter ≠ s.points i := by
  rw [← dist_ne_zero, dist_circumcenter_eq_circumradius']
  exact s.circumradius_pos.ne'

/-- The circumcenter of a 1-simplex equals its centroid. -/
/-
**Affine.Simplex.circumcenter_eq_centroid** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simp
lex`。
形式化陈述：circumcenter_eq_centroid (s : Simplex Real P 1) : s.circumcenter = Finset.
univ.centroid Real s.points
参数：s : Simplex Real P 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.centroid_pair_fin`：centroid_pair_fin [Invertible (2 : k)] (p : Fi
n 2 -> P) : univ.centroid k p = (2⁻¹ : k) • (p 1 -ᵥ p 0) +ᵥ p 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `vsub_vadd_eq_vsub_sub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup 
G] [T : AddTorsor G P] (p₁ p₂ : P) (g : G),   p₁ -ᵥ (g +ᵥ p₂) = p₁ -ᵥ p₂ - g
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_eq`：∀ {α : Type u_1} [inst : DivisionSem
iring α] {n d : ℕ} {a n' d' : α},   Mathlib.Meta.NormNum.IsNNRat a n d → ↑n = n'
 → ↑d = d' → a = n' / d'
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
The circumcenter of a 1-simplex equals its centroid.
-/
theorem circumcenter_eq_centroid (s : Simplex ℝ P 1) :
    s.circumcenter = Finset.univ.centroid ℝ s.points := by
  have hr :
    Set.Pairwise Set.univ fun i j : Fin 2 =>
      dist (s.points i) (Finset.univ.centroid ℝ s.points) =
        dist (s.points j) (Finset.univ.centroid ℝ s.points) := by
    intro i hi j hj hij
    rw [Finset.centroid_pair_fin, dist_eq_norm_vsub V (s.points i),
      dist_eq_norm_vsub V (s.points j), vsub_vadd_eq_vsub_sub, vsub_vadd_eq_vsub_sub, ←
      one_smul ℝ (s.points i -ᵥ s.points 0), ← one_smul ℝ (s.points j -ᵥ s.points 0)]
    fin_cases i <;> fin_cases j <;> simp [-one_smul, ← sub_smul] <;> norm_num
  rw [Set.pairwise_eq_iff_exists_eq] at hr
  obtain ⟨r, hr⟩ := hr
  exact
    (s.eq_circumcenter_of_dist_eq
        (centroid_mem_affineSpan_of_card_eq_add_one ℝ _ (Finset.card_fin 2)) fun i =>
        hr i (Set.mem_univ _)).symm

/-- Reindexing a simplex along an `Equiv` of index types does not change the circumsphere. -/
@[simp]
/-
**Affine.Simplex.circumsphere_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`
。
形式化陈述：circumsphere_reindex {m n : Nat} (s : Simplex Real P m) (e : Fin (m + 1) ≃
 Fin (n + 1)) : (s.reindex e).circumsphere = s.circumsphere
参数：s : Simplex Real P m；e : Fin (m + 1) ≃ Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Affine.Simplex.circumsphere_unique_dist_eq`：circumsphere_unique_dist_eq 
{n : Nat} (s : Simplex Real P n) : (s.circumsphere.center in affineSpan Real (Se
t.range s.points) ∧ Set.range s.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Affine.Simplex.reindex_range_points`：reindex_range_points {m n : Nat} (s
 : Simplex k P m) (e : Fin (m + 1) ≃ Fin (n + 1)) : Set.range (s.reindex e).poin
ts = Set.range s.points
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
Reindexing a simplex along an `Equiv` of index types does not change the circums
phere.
-/
theorem circumsphere_reindex {m n : ℕ} (s : Simplex ℝ P m) (e : Fin (m + 1) ≃ Fin (n + 1)) :
    (s.reindex e).circumsphere = s.circumsphere := by
  refine s.circumsphere_unique_dist_eq.2 _ ⟨?_, ?_⟩ <;> rw [← s.reindex_range_points e]
  · exact (s.reindex e).circumsphere_unique_dist_eq.1.1
  · exact (s.reindex e).circumsphere_unique_dist_eq.1.2

/-- Reindexing a simplex along an `Equiv` of index types does not change the circumcenter. -/
@[simp]
/-
**Affine.Simplex.circumcenter_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`
。
形式化陈述：circumcenter_reindex {m n : Nat} (s : Simplex Real P m) (e : Fin (m + 1) ≃
 Fin (n + 1)) : (s.reindex e).circumcenter = s.circumcenter
参数：s : Simplex Real P m；e : Fin (m + 1) ≃ Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.circumsphere_reindex`：circumsphere_reindex {m n : Nat} (s
 : Simplex Real P m) (e : Fin (m + 1) ≃ Fin (n + 1)) : (s.reindex e).circumspher
e = s.circumsphere
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Reindexing a simplex along an `Equiv` of index types does not change the circumc
enter.
-/
theorem circumcenter_reindex {m n : ℕ} (s : Simplex ℝ P m) (e : Fin (m + 1) ≃ Fin (n + 1)) :
    (s.reindex e).circumcenter = s.circumcenter := by simp_rw [circumcenter, circumsphere_reindex]

/-- Reindexing a simplex along an `Equiv` of index types does not change the circumradius. -/
@[simp]
/-
**Affine.Simplex.circumradius_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`
。
形式化陈述：circumradius_reindex {m n : Nat} (s : Simplex Real P m) (e : Fin (m + 1) ≃
 Fin (n + 1)) : (s.reindex e).circumradius = s.circumradius
参数：s : Simplex Real P m；e : Fin (m + 1) ≃ Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.circumsphere_reindex`：circumsphere_reindex {m n : Nat} (s
 : Simplex Real P m) (e : Fin (m + 1) ≃ Fin (n + 1)) : (s.reindex e).circumspher
e = s.circumsphere
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Reindexing a simplex along an `Equiv` of index types does not change the circumr
adius.
-/
theorem circumradius_reindex {m n : ℕ} (s : Simplex ℝ P m) (e : Fin (m + 1) ≃ Fin (n + 1)) :
    (s.reindex e).circumradius = s.circumradius := by simp_rw [circumradius, circumsphere_reindex]
/-
**Affine.Simplex.circumcenter_map** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
V₂ : Type u_3} {P₂ : Type u_4} [inst_4 : NormedAddCommGroup V₂]   [inst_5 : Inne
rProductSpace ℝ V₂] [inst_6 : MetricSpace P₂] [inst_7 : NormedAddTorsor V₂ P₂] {
n : ℕ}   (s : Affine.Simplex ℝ P n) (f : P →ᵃⁱ[ℝ] P₂), (s.map f.toAffineMap ⋯).c
ircumcenter = f s.circumcenter
参数：s : Affine.Simplex ℝ P n；f : P →ᵃⁱ[ℝ] P₂；s.map f.toAffineMap ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIsometry.injective`：∀ {𝕜 : Type u_1} {V₁' : Type u_4} {V₂ : Type u
_5} {P₁' : Type u_9} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : Seminor
medAddCommGrou…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Affine.Simplex.eq_circumcenter_of_dist_eq`：eq_circumcenter_of_dist_eq {n
 : Nat} (s : Simplex Real P n) {p : P} (hp : p in affineSpan Real (Set.range s.p
oints)) {r : Real} (hr : forall…
· 使用定理 `Affine.Simplex.map_points`：∀ {k : Type u_1} {V : Type u_2} {V₂ : Type u_
3} {P : Type u_5} {P₂ : Type u_6} [inst : Ring k] [inst_1 : AddCommGroup V]   [i
nst_2 : AddComm…
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineSubspace.map_span`：map_span (s : Set P₁) : (affineSpan k s).map f 
= affineSpan k (f '' s)
· 使用定理 `AffineSubspace.mem_map_of_mem`：mem_map_of_mem {x : P₁} {s : AffineSubspa
ce k P₁} (h : x in s) : f x in s.map f
· 使用定理 `Affine.Simplex.circumcenter_mem_affineSpan`：circumcenter_mem_affineSpan 
{n : Nat} (s : Simplex Real P n) : s.circumcenter in affineSpan Real (Set.range 
s.points)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `AffineIsometry.coe_toAffineMap`：coe_toAffineMap : ⇑f.toAffineMap = f
· 使用定理 `AffineIsometry.dist_map`：dist_map (x y : P) : dist (f x) (f y) = dist x 
y
· 使用定理 `Affine.Simplex.dist_circumcenter_eq_circumradius`：dist_circumcenter_eq_c
ircumradius {n : Nat} (s : Simplex Real P n) (i : Fin (n + 1)) : dist (s.points 
i) s.circumcenter = s.circumradius
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma circumcenter_map {V₂ P₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]
    [MetricSpace P₂] [NormedAddTorsor V₂ P₂] {n : ℕ} (s : Simplex ℝ P n) (f : P →ᵃⁱ[ℝ] P₂) :
    (s.map f.toAffineMap f.injective).circumcenter = f s.circumcenter := by
  rw [eq_comm]
  refine (s.map f.toAffineMap f.injective).eq_circumcenter_of_dist_eq (r := s.circumradius) ?_
    fun i ↦ by simp
  rw [map_points, Set.range_comp, ← AffineSubspace.map_span]
  exact AffineSubspace.mem_map_of_mem _ s.circumcenter_mem_affineSpan
/-
**Affine.Simplex.circumradius_map** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
V₂ : Type u_3} {P₂ : Type u_4} [inst_4 : NormedAddCommGroup V₂]   [inst_5 : Inne
rProductSpace ℝ V₂] [inst_6 : MetricSpace P₂] [inst_7 : NormedAddTorsor V₂ P₂] {
n : ℕ}   (s : Affine.Simplex ℝ P n) (f : P →ᵃⁱ[ℝ] P₂), (s.map f.toAffineMap ⋯).c
ircumradius = s.circumradius
参数：s : Affine.Simplex ℝ P n；f : P →ᵃⁱ[ℝ] P₂；s.map f.toAffineMap ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIsometry.injective`：∀ {𝕜 : Type u_1} {V₁' : Type u_4} {V₂ : Type u
_5} {P₁' : Type u_9} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : Seminor
medAddCommGrou…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Affine.Simplex.eq_circumradius_of_dist_eq`：eq_circumradius_of_dist_eq {n
 : Nat} (s : Simplex Real P n) {p : P} (hp : p in affineSpan Real (Set.range s.p
oints)) {r : Real} (hr : forall…
· 使用定理 `Affine.Simplex.map_points`：∀ {k : Type u_1} {V : Type u_2} {V₂ : Type u_
3} {P : Type u_5} {P₂ : Type u_6} [inst : Ring k] [inst_1 : AddCommGroup V]   [i
nst_2 : AddComm…
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineSubspace.map_span`：map_span (s : Set P₁) : (affineSpan k s).map f 
= affineSpan k (f '' s)
· 使用定理 `AffineSubspace.mem_map_of_mem`：mem_map_of_mem {x : P₁} {s : AffineSubspa
ce k P₁} (h : x in s) : f x in s.map f
· 使用定理 `Affine.Simplex.circumcenter_mem_affineSpan`：circumcenter_mem_affineSpan 
{n : Nat} (s : Simplex Real P n) : s.circumcenter in affineSpan Real (Set.range 
s.points)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `AffineIsometry.coe_toAffineMap`：coe_toAffineMap : ⇑f.toAffineMap = f
· 使用定理 `AffineIsometry.dist_map`：dist_map (x y : P) : dist (f x) (f y) = dist x 
y
· 使用定理 `Affine.Simplex.dist_circumcenter_eq_circumradius`：dist_circumcenter_eq_c
ircumradius {n : Nat} (s : Simplex Real P n) (i : Fin (n + 1)) : dist (s.points 
i) s.circumcenter = s.circumradius
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma circumradius_map {V₂ P₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]
    [MetricSpace P₂] [NormedAddTorsor V₂ P₂] {n : ℕ} (s : Simplex ℝ P n) (f : P →ᵃⁱ[ℝ] P₂) :
    (s.map f.toAffineMap f.injective).circumradius = s.circumradius := by
  rw [eq_comm]
  refine (s.map f.toAffineMap f.injective).eq_circumradius_of_dist_eq (p := f s.circumcenter) ?_
    fun i ↦ by simp
  rw [map_points, Set.range_comp, ← AffineSubspace.map_span]
  exact AffineSubspace.mem_map_of_mem _ s.circumcenter_mem_affineSpan
/-
**Affine.Simplex.circumcenter_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex
`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} (s : Affine.Simplex ℝ P n) (S : AffineSubspace ℝ P)   (hS : affineSpan ℝ 
(Set.range s.points) ≤ S), ↑(s.restrict S hS).circumcenter = s.circumcenter
参数：s : Affine.Simplex ℝ P n；S : AffineSubspace ℝ P；hS : affineSpan ℝ (Set.range 
s.points) ≤ S；s.restrict S hS。
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
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Affine.Simplex.circumcenter_map`：∀ {V : Type u_1} {P : Type u_2} [inst :
 NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]
   [inst_3 : NormedAd…
-/
@[simp] lemma circumcenter_restrict {n : ℕ} (s : Simplex ℝ P n) (S : AffineSubspace ℝ P)
    (hS : affineSpan ℝ (Set.range s.points) ≤ S) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).circumcenter = s.circumcenter := by
  rw [eq_comm]
  have : Nonempty S := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  exact (s.restrict S hS).circumcenter_map S.subtypeₐᵢ
/-
**Affine.Simplex.circumradius_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex
`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
n : ℕ} (s : Affine.Simplex ℝ P n) (S : AffineSubspace ℝ P)   (hS : affineSpan ℝ 
(Set.range s.points) ≤ S), (s.restrict S hS).circumradius = s.circumradius
参数：s : Affine.Simplex ℝ P n；S : AffineSubspace ℝ P；hS : affineSpan ℝ (Set.range 
s.points) ≤ S；s.restrict S hS。
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
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Affine.Simplex.circumradius_map`：∀ {V : Type u_1} {P : Type u_2} [inst :
 NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]
   [inst_3 : NormedAd…
-/
@[simp] lemma circumradius_restrict {n : ℕ} (s : Simplex ℝ P n) (S : AffineSubspace ℝ P)
    (hS : affineSpan ℝ (Set.range s.points) ≤ S) :
    haveI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).circumradius = s.circumradius := by
  rw [eq_comm]
  have : Nonempty S := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  exact (s.restrict S hS).circumradius_map S.subtypeₐᵢ
/-
**Affine.Simplex.dist_circumcenter_sq_eq_sq_sub_circumradius** 是 Mathlib 中的一个定理，
位于命名空间 `Affine.Simplex`。
形式化陈述：dist_circumcenter_sq_eq_sq_sub_circumradius {n : Nat} {r : Real} (s : Simp
lex Real P n) {p₁ : P} (h₁ : forall i : Fin (n + 1), dist (s.points i) p₁ = r) (
h₁' : ↑(s.orthogonalProjectionSpan p₁) = s.circumcenter) (h : s.points 0 in affi
neSpan Real (Set.range s.points)) : dist p₁ s.circumcenter * dist p₁ s.circumcen
ter = r * r - s.circumradius * s.circumradius
参数：s : Simplex Real P n；h₁ : forall i : Fin (n + 1), dist (s.points i) p₁ = r；h₁
' : ↑(s.orthogonalProjectionSpan p₁) = s.circumcenter；h : s.points 0 in affineSp
an Real (Set.range s.points)。
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
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Affine.Simplex.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogon
alProjection_sq`：dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProj
ection_sq {n : Nat} (s : Simplex 𝕜 P n) {p₁ : P} (p₂ : P) (hp₁ : p₁ in affine…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Affine.Simplex.dist_circumcenter_eq_circumradius`：dist_circumcenter_eq_c
ircumradius {n : Nat} (s : Simplex Real P n) (i : Fin (n + 1)) : dist (s.points 
i) s.circumcenter = s.circumradius
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dist_circumcenter_sq_eq_sq_sub_circumradius {n : ℕ} {r : ℝ} (s : Simplex ℝ P n) {p₁ : P}
    (h₁ : ∀ i : Fin (n + 1), dist (s.points i) p₁ = r)
    (h₁' : ↑(s.orthogonalProjectionSpan p₁) = s.circumcenter)
    (h : s.points 0 ∈ affineSpan ℝ (Set.range s.points)) :
    dist p₁ s.circumcenter * dist p₁ s.circumcenter = r * r - s.circumradius * s.circumradius := by
  rw [dist_comm, ← h₁ 0,
    s.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq p₁ h]
  simp only [h₁', dist_comm p₁, add_sub_cancel_left, Simplex.dist_circumcenter_eq_circumradius]

/-- If there exists a distance that a point has from all vertices of a
simplex, the orthogonal projection of that point onto the subspace
spanned by that simplex is its circumcenter. -/
/-
**Affine.Simplex.orthogonalProjection_eq_circumcenter_of_exists_dist_eq** 是 Math
lib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：orthogonalProjection_eq_circumcenter_of_exists_dist_eq {n : Nat} (s : Simp
lex Real P n) {p : P} (hr : exists r, forall i, dist (s.points i) p = r) : ↑(s.o
rthogonalProjectionSpan p) = s.circumcenter
参数：s : Simplex Real P n；hr : exists r, forall i, dist (s.points i) p = r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
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
· 使用定理 `EuclideanGeometry.exists_dist_eq_iff_exists_dist_orthogonalProjection_eq
`：exists_dist_eq_iff_exists_dist_orthogonalProjection_eq {s : AffineSubspace 𝕜 P
} [Nonempty s] [s.direction.HasOrthogonalProjection] {ps : Set…
· 使用定理 `subset_affineSpan`：subset_affineSpan (s : Set P) : s subseteq affineSpan
 k s
· 使用定理 `Affine.Simplex.eq_circumcenter_of_dist_eq`：eq_circumcenter_of_dist_eq {n
 : Nat} (s : Simplex Real P n) {p : P} (hp : p in affineSpan Real (Set.range s.p
oints)) {r : Real} (hr : forall…
· 使用定理 `EuclideanGeometry.orthogonalProjection_mem`：orthogonalProjection_mem {s 
: AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalProjection] (p : P)
 : ↑(orthogonalProjection s p) i…
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f

--- 原说明 ---
If there exists a distance that a point has from all vertices of a
simplex, the orthogonal projection of that point onto the subspace
spanned by that simplex is its circumcenter.
-/
theorem orthogonalProjection_eq_circumcenter_of_exists_dist_eq {n : ℕ} (s : Simplex ℝ P n) {p : P}
    (hr : ∃ r, ∀ i, dist (s.points i) p = r) :
    ↑(s.orthogonalProjectionSpan p) = s.circumcenter := by
  change ∃ r : ℝ, ∀ i, (fun x => dist x p = r) (s.points i) at hr
  have hr : ∃ (r : ℝ), ∀ (a : P),
      a ∈ Set.range (fun (i : Fin (n + 1)) => s.points i) → dist a p = r := by
    obtain ⟨r, hr⟩ := hr
    use r
    refine Set.forall_mem_range.mpr ?_
    exact hr
  rw [exists_dist_eq_iff_exists_dist_orthogonalProjection_eq (subset_affineSpan ℝ _) p] at hr
  obtain ⟨r, hr⟩ := hr
  exact
    s.eq_circumcenter_of_dist_eq (orthogonalProjection_mem p) fun i => hr _ (Set.mem_range_self i)

/-- If a point has the same distance from all vertices of a simplex,
the orthogonal projection of that point onto the subspace spanned by
that simplex is its circumcenter. -/
/-
**Affine.Simplex.orthogonalProjection_eq_circumcenter_of_dist_eq** 是 Mathlib 中的一
个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：orthogonalProjection_eq_circumcenter_of_dist_eq {n : Nat} (s : Simplex Rea
l P n) {p : P} {r : Real} (hr : forall i, dist (s.points i) p = r) : ↑(s.orthogo
nalProjectionSpan p) = s.circumcenter
参数：s : Simplex Real P n；hr : forall i, dist (s.points i) p = r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.orthogonalProjection_eq_circumcenter_of_exists_dist_eq`：o
rthogonalProjection_eq_circumcenter_of_exists_dist_eq {n : Nat} (s : Simplex Rea
l P n) {p : P} (hr : exists r, forall i, dist (s.points i) …

--- 原说明 ---
If a point has the same distance from all vertices of a simplex,
the orthogonal projection of that point onto the subspace spanned by
that simplex is its circumcenter.
-/
theorem orthogonalProjection_eq_circumcenter_of_dist_eq {n : ℕ} (s : Simplex ℝ P n) {p : P} {r : ℝ}
    (hr : ∀ i, dist (s.points i) p = r) : ↑(s.orthogonalProjectionSpan p) = s.circumcenter :=
  s.orthogonalProjection_eq_circumcenter_of_exists_dist_eq ⟨r, hr⟩

/-- The orthogonal projection of the circumcenter onto a face is the
circumcenter of that face. -/
/-
**Affine.Simplex.orthogonalProjection_circumcenter** 是 Mathlib 中的一个定理，位于命名空间 `Af
fine.Simplex`。
形式化陈述：orthogonalProjection_circumcenter {n : Nat} (s : Simplex Real P n) {fs : F
inset (Fin (n + 1))} {m : Nat} (h : #fs = m + 1) : ↑((s.face h).orthogonalProjec
tionSpan s.circumcenter) = (s.face h).circumcenter
参数：s : Simplex Real P n；Fin (n + 1)；h : #fs = m + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.orthogonalProjection_eq_circumcenter_of_exists_dist_eq`：o
rthogonalProjection_eq_circumcenter_of_exists_dist_eq {n : Nat} (s : Simplex Rea
l P n) {p : P} (hr : exists r, forall i, dist (s.points i) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.dist_circumcenter_eq_circumradius`：dist_circumcenter_eq_c
ircumradius {n : Nat} (s : Simplex Real P n) (i : Fin (n + 1)) : dist (s.points 
i) s.circumcenter = s.circumradius
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
The orthogonal projection of the circumcenter onto a face is the
circumcenter of that face.
-/
theorem orthogonalProjection_circumcenter {n : ℕ} (s : Simplex ℝ P n) {fs : Finset (Fin (n + 1))}
    {m : ℕ} (h : #fs = m + 1) :
    ↑((s.face h).orthogonalProjectionSpan s.circumcenter) = (s.face h).circumcenter :=
  haveI hr : ∃ r, ∀ i, dist ((s.face h).points i) s.circumcenter = r := by
    use s.circumradius
    simp [face_points]
  orthogonalProjection_eq_circumcenter_of_exists_dist_eq _ hr

/-- Two simplices with the same points have the same circumcenter. -/
/-
**Affine.Simplex.circumcenter_eq_of_range_eq** 是 Mathlib 中的一个定理，位于命名空间 `Affine.S
implex`。
形式化陈述：circumcenter_eq_of_range_eq {n : Nat} {s₁ s₂ : Simplex Real P n} (h : Set.
range s₁.points = Set.range s₂.points) : s₁.circumcenter = s₂.circumcenter
参数：h : Set.range s₁.points = Set.range s₂.points。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Affine.Simplex.circumcenter_mem_affineSpan`：circumcenter_mem_affineSpan 
{n : Nat} (s : Simplex Real P n) : s.circumcenter in affineSpan Real (Set.range 
s.points)
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Affine.Simplex.dist_circumcenter_eq_circumradius`：dist_circumcenter_eq_c
ircumradius {n : Nat} (s : Simplex Real P n) (i : Fin (n + 1)) : dist (s.points 
i) s.circumcenter = s.circumradius
· 使用定理 `Affine.Simplex.eq_circumcenter_of_dist_eq`：eq_circumcenter_of_dist_eq {n
 : Nat} (s : Simplex Real P n) {p : P} (hp : p in affineSpan Real (Set.range s.p
oints)) {r : Real} (hr : forall…

--- 原说明 ---
Two simplices with the same points have the same circumcenter.
-/
theorem circumcenter_eq_of_range_eq {n : ℕ} {s₁ s₂ : Simplex ℝ P n}
    (h : Set.range s₁.points = Set.range s₂.points) : s₁.circumcenter = s₂.circumcenter := by
  have hs : s₁.circumcenter ∈ affineSpan ℝ (Set.range s₂.points) :=
    h ▸ s₁.circumcenter_mem_affineSpan
  have hr : ∀ i, dist (s₂.points i) s₁.circumcenter = s₁.circumradius := by
    intro i
    have hi : s₂.points i ∈ Set.range s₂.points := Set.mem_range_self _
    rw [← h, Set.mem_range] at hi
    rcases hi with ⟨j, hj⟩
    rw [← hj, s₁.dist_circumcenter_eq_circumradius j]
  exact s₂.eq_circumcenter_of_dist_eq hs hr

/-- An index type for the vertices of a simplex plus its circumcenter.
This is for use in calculations where it is convenient to work with
affine combinations of vertices together with the circumcenter.  (An
equivalent form sometimes used in the literature is placing the
circumcenter at the origin and working with vectors for the vertices.) -/
/-
**Affine.Simplex.PointsWithCircumcenterIndex** 是 Mathlib 中的一个归纳类型，位于命名空间 `Affine
.Simplex`。
形式化陈述：ℕ → Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An index type for the vertices of a simplex plus its circumcenter.
This is for use in calculations where it is convenient to work with
affine combinations of vertices together with the circumcenter.  (An
equivalent form sometimes used in the literature is placing the
circumcenter at the origin and working with vectors for the vertices.)
-/
inductive PointsWithCircumcenterIndex (n : ℕ)
  | pointIndex : Fin (n + 1) → PointsWithCircumcenterIndex n
  | circumcenterIndex : PointsWithCircumcenterIndex n
  deriving Fintype

open PointsWithCircumcenterIndex
/-
**Affine.Simplex.pointsWithCircumcenterIndexInhabited** 是 Mathlib 中的一个实例，位于命名空间 
`Affine.Simplex`。
形式化陈述：pointsWithCircumcenterIndexInhabited (n : Nat) : Inhabited (PointsWithCirc
umcenterIndex n)
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance pointsWithCircumcenterIndexInhabited (n : ℕ) : Inhabited (PointsWithCircumcenterIndex n) :=
  ⟨circumcenterIndex⟩

/-- `pointIndex` as an embedding. -/
/-
**Affine.Simplex.pointIndexEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `Affine.Simplex`。
形式化陈述：pointIndexEmbedding (n : Nat) : Fin (n + 1) ↪ PointsWithCircumcenterIndex 
n
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`pointIndex` as an embedding.
-/
def pointIndexEmbedding (n : ℕ) : Fin (n + 1) ↪ PointsWithCircumcenterIndex n :=
  ⟨fun i => pointIndex i, fun _ _ h => by injection h⟩

/-- The sum of a function over `PointsWithCircumcenterIndex`. -/
/-
**Affine.Simplex.sum_pointsWithCircumcenter** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Si
mplex`。
形式化陈述：sum_pointsWithCircumcenter {α : Type*} [AddCommMonoid α] {n : Nat} (f : Po
intsWithCircumcenterIndex n -> α) : ∑ i, f i = (∑ i : Fin (n + 1), f (pointIndex
 i)) + f circumcenterIndex
参数：f : PointsWithCircumcenterIndex n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `Finset.mem_map_of_mem`：mem_map_of_mem (f : α ↪ β) {a} {s : Finset α} : a
 in s -> f a in s.map f
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_map`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] (s : Finset ι) (e : ι ↪ κ) (f : κ → M),   ∑ x ∈ Finset.map e s, 
f x …
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))

--- 原说明 ---
The sum of a function over `PointsWithCircumcenterIndex`.
-/
theorem sum_pointsWithCircumcenter {α : Type*} [AddCommMonoid α] {n : ℕ}
    (f : PointsWithCircumcenterIndex n → α) :
    ∑ i, f i = (∑ i : Fin (n + 1), f (pointIndex i)) + f circumcenterIndex := by
  classical
  have h : univ = insert circumcenterIndex (univ.map (pointIndexEmbedding n)) := by
    ext x
    refine ⟨fun h => ?_, fun _ => mem_univ _⟩
    obtain i | - := x
    · exact mem_insert_of_mem (mem_map_of_mem _ (mem_univ i))
    · exact mem_insert_self _ _
  change _ = (∑ i, f (pointIndexEmbedding n i)) + _
  rw [add_comm, h, ← sum_map, sum_insert]
  simp_rw [Finset.mem_map, not_exists]
  rintro x ⟨_, h⟩
  injection h

/-- The vertices of a simplex plus its circumcenter. -/
/-
**Affine.Simplex.pointsWithCircumcenter** 是 Mathlib 中的一个定义，位于命名空间 `Affine.Simple
x`。
形式化陈述：{V : Type u_1} →   {P : Type u_2} →     [inst : NormedAddCommGroup V] →   
    [inst_1 : InnerProductSpace ℝ V] →         [inst_2 : MetricSpace P] →       
    [inst_3 : NormedAddTorsor V P] →             {n : ℕ} → Affine.Simplex ℝ P n 
→ Affine.Simplex.PointsWithCircumcenterIndex n → P
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The vertices of a simplex plus its circumcenter.
-/
def pointsWithCircumcenter {n : ℕ} (s : Simplex ℝ P n) : PointsWithCircumcenterIndex n → P
  | pointIndex i => s.points i
  | circumcenterIndex => s.circumcenter

/-- `pointsWithCircumcenter`, applied to a `pointIndex` value,
equals `points` applied to that value. -/
@[simp]
/-
**Affine.Simplex.pointsWithCircumcenter_point** 是 Mathlib 中的一个定理，位于命名空间 `Affine.
Simplex`。
形式化陈述：pointsWithCircumcenter_point {n : Nat} (s : Simplex Real P n) (i : Fin (n 
+ 1)) : s.pointsWithCircumcenter (pointIndex i) = s.points i
参数：s : Simplex Real P n；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`pointsWithCircumcenter`, applied to a `pointIndex` value,
equals `points` applied to that value.
-/
theorem pointsWithCircumcenter_point {n : ℕ} (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    s.pointsWithCircumcenter (pointIndex i) = s.points i :=
  rfl

/-- `pointsWithCircumcenter`, applied to `circumcenterIndex`, equals the
circumcenter. -/
@[simp]
/-
**Affine.Simplex.pointsWithCircumcenter_eq_circumcenter** 是 Mathlib 中的一个定理，位于命名空
间 `Affine.Simplex`。
形式化陈述：pointsWithCircumcenter_eq_circumcenter {n : Nat} (s : Simplex Real P n) : 
s.pointsWithCircumcenter circumcenterIndex = s.circumcenter
参数：s : Simplex Real P n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`pointsWithCircumcenter`, applied to `circumcenterIndex`, equals the
circumcenter.
-/
theorem pointsWithCircumcenter_eq_circumcenter {n : ℕ} (s : Simplex ℝ P n) :
    s.pointsWithCircumcenter circumcenterIndex = s.circumcenter :=
  rfl

/-- The weights for a single vertex of a simplex, in terms of
`pointsWithCircumcenter`. -/
/-
**Affine.Simplex.pointWeightsWithCircumcenter** 是 Mathlib 中的一个定义，位于命名空间 `Affine.
Simplex`。
形式化陈述：{n : ℕ} → Fin (n + 1) → Affine.Simplex.PointsWithCircumcenterIndex n → ℝ
参数：n + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The weights for a single vertex of a simplex, in terms of
`pointsWithCircumcenter`.
-/
def pointWeightsWithCircumcenter {n : ℕ} (i : Fin (n + 1)) : PointsWithCircumcenterIndex n → ℝ
  | pointIndex j => if j = i then 1 else 0
  | circumcenterIndex => 0

/-- `pointWeightsWithCircumcenter` sums to 1. -/
@[simp]
/-
**Affine.Simplex.sum_pointWeightsWithCircumcenter** 是 Mathlib 中的一个定理，位于命名空间 `Aff
ine.Simplex`。
形式化陈述：sum_pointWeightsWithCircumcenter {n : Nat} (i : Fin (n + 1)) : ∑ j, pointW
eightsWithCircumcenter i j = 1
参数：i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `Affine.Simplex.PointsWithCircumcenterIndex.pointIndex.injEq`：∀ {n : ℕ} (
a a_1 : Fin (n + 1)),   (Affine.Simplex.PointsWithCircumcenterIndex.pointIndex a
 =       Affine.Simplex.PointsWithCircumcenterInd…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…

--- 原说明 ---
`pointWeightsWithCircumcenter` sums to 1.
-/
theorem sum_pointWeightsWithCircumcenter {n : ℕ} (i : Fin (n + 1)) :
    ∑ j, pointWeightsWithCircumcenter i j = 1 := by
  classical
  convert! sum_ite_eq' univ (pointIndex i) (Function.const _ (1 : ℝ)) with j
  · cases j <;> simp [pointWeightsWithCircumcenter]
  · simp

/-- A single vertex, in terms of `pointsWithCircumcenter`. -/
/-
**Affine.Simplex.point_eq_affineCombination_of_pointsWithCircumcenter** 是 Mathli
b 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：point_eq_affineCombination_of_pointsWithCircumcenter {n : Nat} (s : Simple
x Real P n) (i : Fin (n + 1)) : s.points i = (univ : Finset (PointsWithCircumcen
terIndex n)).affineCombination Real s.pointsWithCircumcenter (pointWeightsWithCi
rcumcenter i)
参数：s : Simplex Real P n；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Affine.Simplex.pointsWithCircumcenter_point`：pointsWithCircumcenter_poin
t {n : Nat} (s : Simplex Real P n) (i : Fin (n + 1)) : s.pointsWithCircumcenter 
(pointIndex i) = s.points i
· 使用定理 `Finset.affineCombination_of_eq_one_of_eq_zero`：affineCombination_of_eq_o
ne_of_eq_zero (w : ι -> k) (p : ι -> P) {i : ι} (his : i in s) (hwi : w i = 1) (
hw0 : forall i2 in s, i2 != i -> w …
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False

--- 原说明 ---
A single vertex, in terms of `pointsWithCircumcenter`.
-/
theorem point_eq_affineCombination_of_pointsWithCircumcenter {n : ℕ} (s : Simplex ℝ P n)
    (i : Fin (n + 1)) :
    s.points i =
      (univ : Finset (PointsWithCircumcenterIndex n)).affineCombination ℝ s.pointsWithCircumcenter
        (pointWeightsWithCircumcenter i) := by
  rw [← pointsWithCircumcenter_point]
  symm
  refine
    affineCombination_of_eq_one_of_eq_zero _ _ _ (mem_univ _)
      (by simp [pointWeightsWithCircumcenter]) ?_
  intro i hi hn
  cases i
  · have h : _ ≠ i := fun h => hn (h ▸ rfl)
    simp [pointWeightsWithCircumcenter, h]
  · rfl

/-- The weights for the centroid of some vertices of a simplex, in
terms of `pointsWithCircumcenter`. -/
/-
**Affine.Simplex.centroidWeightsWithCircumcenter** 是 Mathlib 中的一个定义，位于命名空间 `Affi
ne.Simplex`。
形式化陈述：{n : ℕ} → Finset (Fin (n + 1)) → Affine.Simplex.PointsWithCircumcenterInde
x n → ℝ
参数：Fin (n + 1)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The weights for the centroid of some vertices of a simplex, in
terms of `pointsWithCircumcenter`.
-/
def centroidWeightsWithCircumcenter {n : ℕ} (fs : Finset (Fin (n + 1))) :
    PointsWithCircumcenterIndex n → ℝ
  | pointIndex i => if i ∈ fs then (#fs : ℝ)⁻¹ else 0
  | circumcenterIndex => 0

/-- `centroidWeightsWithCircumcenter` sums to 1, if the `Finset` is nonempty. -/
@[simp]
/-
**Affine.Simplex.sum_centroidWeightsWithCircumcenter** 是 Mathlib 中的一个定理，位于命名空间 `
Affine.Simplex`。
形式化陈述：sum_centroidWeightsWithCircumcenter {n : Nat} {fs : Finset (Fin (n + 1))} 
(h : fs.Nonempty) : ∑ i, centroidWeightsWithCircumcenter fs i = 1
参数：Fin (n + 1)；h : fs.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.sum_pointsWithCircumcenter`：sum_pointsWithCircumcenter {α
 : Type*} [AddCommMonoid α] {n : Nat} (f : PointsWithCircumcenterIndex n -> α) :
 ∑ i, f i = (∑ i : Fin (n + 1),…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_centroidWeights_eq_one_of_nonempty`：sum_centroidWeights_eq_on
e_of_nonempty [CharZero k] (h : s.Nonempty) : ∑ i in s, s.centroidWeights k i = 
1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Finset.sum_indicator_subset`：∀ {ι : Type u_1} {β : Type u_4} [inst : Add
CommMonoid β] (f : ι → β) {s t : Finset ι},   s ⊆ t → ∑ i ∈ t, (↑s).indicator f 
i = ∑ i ∈ s, f i
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)

--- 原说明 ---
`centroidWeightsWithCircumcenter` sums to 1, if the `Finset` is nonempty.
-/
theorem sum_centroidWeightsWithCircumcenter {n : ℕ} {fs : Finset (Fin (n + 1))} (h : fs.Nonempty) :
    ∑ i, centroidWeightsWithCircumcenter fs i = 1 := by
  simp_rw [sum_pointsWithCircumcenter, centroidWeightsWithCircumcenter, add_zero, ←
    fs.sum_centroidWeights_eq_one_of_nonempty ℝ h, ← sum_indicator_subset _ fs.subset_univ]
  rcongr

/-- The centroid of some vertices of a simplex, in terms of `pointsWithCircumcenter`. -/
/-
**Affine.Simplex.centroid_eq_affineCombination_of_pointsWithCircumcenter** 是 Mat
hlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：centroid_eq_affineCombination_of_pointsWithCircumcenter {n : Nat} (s : Sim
plex Real P n) (fs : Finset (Fin (n + 1))) : fs.centroid Real s.points = (univ :
 Finset (PointsWithCircumcenterIndex n)).affineCombination Real s.pointsWithCirc
umcenter (centroidWeightsWithCircumcenter fs)
参数：s : Simplex Real P n；fs : Finset (Fin (n + 1))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.weightedVSubOfPoint_apply`：weightedVSubOfPoint_apply (w : ι -> k)
 (p : ι -> P) (b : P) : s.weightedVSubOfPoint p b w = ∑ i in s, w i • (p i -ᵥ b)
· 使用定理 `Affine.Simplex.sum_pointsWithCircumcenter`：sum_pointsWithCircumcenter {α
 : Type*} [AddCommMonoid α] {n : Nat} (f : PointsWithCircumcenterIndex n -> α) :
 ∑ i, f i = (∑ i : Fin (n + 1),…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_indicator_subset_of_eq_zero`：∀ {ι : Type u_1} {α : Type u_3} 
{β : Type u_4} [inst : AddCommMonoid β] [inst_1 : Zero α] (f : ι → α) (g : ι → α
 → β)   {s t : Finset ι}, s …
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Set.indicator_apply`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (s 
: Set α) (f : α → M) (a : α) [inst_1 : Decidable (a ∈ s)],   s.indicator f a = i
f a ∈ s t…

--- 原说明 ---
The centroid of some vertices of a simplex, in terms of `pointsWithCircumcenter`
.
-/
theorem centroid_eq_affineCombination_of_pointsWithCircumcenter {n : ℕ} (s : Simplex ℝ P n)
    (fs : Finset (Fin (n + 1))) :
    fs.centroid ℝ s.points =
      (univ : Finset (PointsWithCircumcenterIndex n)).affineCombination ℝ s.pointsWithCircumcenter
        (centroidWeightsWithCircumcenter fs) := by
  simp_rw [centroid_def, affineCombination_apply, weightedVSubOfPoint_apply,
    sum_pointsWithCircumcenter, centroidWeightsWithCircumcenter,
    pointsWithCircumcenter_point, zero_smul, add_zero, centroidWeights,
    ← sum_indicator_subset_of_eq_zero (Function.const (Fin (n + 1)) (#fs : ℝ)⁻¹)
      (fun i wi => wi • (s.points i -ᵥ Classical.choice AddTorsor.nonempty)) fs.subset_univ fun _ =>
      zero_smul ℝ _,
    Set.indicator_apply]
  congr

/-- The weights for the circumcenter of a simplex, in terms of `pointsWithCircumcenter`. -/
/-
**Affine.Simplex.circumcenterWeightsWithCircumcenter** 是 Mathlib 中的一个定义，位于命名空间 `
Affine.Simplex`。
形式化陈述：(n : ℕ) → Affine.Simplex.PointsWithCircumcenterIndex n → ℝ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The weights for the circumcenter of a simplex, in terms of `pointsWithCircumcent
er`.
-/
def circumcenterWeightsWithCircumcenter (n : ℕ) : PointsWithCircumcenterIndex n → ℝ
  | pointIndex _ => 0
  | circumcenterIndex => 1

/-- `circumcenterWeightsWithCircumcenter` sums to 1. -/
@[simp]
/-
**Affine.Simplex.sum_circumcenterWeightsWithCircumcenter** 是 Mathlib 中的一个定理，位于命名
空间 `Affine.Simplex`。
形式化陈述：sum_circumcenterWeightsWithCircumcenter (n : Nat) : ∑ i, circumcenterWeigh
tsWithCircumcenter n i = 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…

--- 原说明 ---
`circumcenterWeightsWithCircumcenter` sums to 1.
-/
theorem sum_circumcenterWeightsWithCircumcenter (n : ℕ) :
    ∑ i, circumcenterWeightsWithCircumcenter n i = 1 := by
  classical
  convert! sum_ite_eq' univ circumcenterIndex (Function.const _ (1 : ℝ)) with j
  · cases j <;> simp [circumcenterWeightsWithCircumcenter]
  · simp

/-- The circumcenter of a simplex, in terms of `pointsWithCircumcenter`. -/
/-
**Affine.Simplex.circumcenter_eq_affineCombination_of_pointsWithCircumcenter** 是
 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：circumcenter_eq_affineCombination_of_pointsWithCircumcenter {n : Nat} (s :
 Simplex Real P n) : s.circumcenter = (univ : Finset (PointsWithCircumcenterInde
x n)).affineCombination Real s.pointsWithCircumcenter (circumcenterWeightsWithCi
rcumcenter n)
参数：s : Simplex Real P n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Affine.Simplex.pointsWithCircumcenter_eq_circumcenter`：pointsWithCircumc
enter_eq_circumcenter {n : Nat} (s : Simplex Real P n) : s.pointsWithCircumcente
r circumcenterIndex = s.circumcenter
· 使用定理 `Finset.affineCombination_of_eq_one_of_eq_zero`：affineCombination_of_eq_o
ne_of_eq_zero (w : ι -> k) (p : ι -> P) {i : ι} (his : i in s) (hwi : w i = 1) (
hw0 : forall i2 in s, i2 != i -> w …
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)

--- 原说明 ---
The circumcenter of a simplex, in terms of `pointsWithCircumcenter`.
-/
theorem circumcenter_eq_affineCombination_of_pointsWithCircumcenter {n : ℕ} (s : Simplex ℝ P n) :
    s.circumcenter =
      (univ : Finset (PointsWithCircumcenterIndex n)).affineCombination ℝ s.pointsWithCircumcenter
        (circumcenterWeightsWithCircumcenter n) := by
  rw [← pointsWithCircumcenter_eq_circumcenter]
  symm
  refine affineCombination_of_eq_one_of_eq_zero _ _ _ (mem_univ _) rfl ?_
  rintro ⟨i⟩ _ hn <;> tauto

/-- The weights for the reflection of the circumcenter in an edge of a
simplex.  This definition is only valid with `i₁ ≠ i₂`. -/
/-
**Affine.Simplex.reflectionCircumcenterWeightsWithCircumcenter** 是 Mathlib 中的一个定
义，位于命名空间 `Affine.Simplex`。
形式化陈述：{n : ℕ} → Fin (n + 1) → Fin (n + 1) → Affine.Simplex.PointsWithCircumcente
rIndex n → ℝ
参数：n + 1；n + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The weights for the reflection of the circumcenter in an edge of a
simplex.  This definition is only valid with `i₁ ≠ i₂`.
-/
def reflectionCircumcenterWeightsWithCircumcenter {n : ℕ} (i₁ i₂ : Fin (n + 1)) :
    PointsWithCircumcenterIndex n → ℝ
  | pointIndex i => if i = i₁ ∨ i = i₂ then 1 else 0
  | circumcenterIndex => -1

/-- `reflectionCircumcenterWeightsWithCircumcenter` sums to 1. -/
@[simp]
/-
**Affine.Simplex.sum_reflectionCircumcenterWeightsWithCircumcenter** 是 Mathlib 中
的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：sum_reflectionCircumcenterWeightsWithCircumcenter {n : Nat} {i₁ i₂ : Fin (
n + 1)} (h : i₁ != i₂) : ∑ i, reflectionCircumcenterWeightsWithCircumcenter i₁ i
₂ i = 1
参数：n + 1；h : i₁ != i₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Affine.Simplex.sum_pointsWithCircumcenter`：sum_pointsWithCircumcenter {α
 : Type*} [AddCommMonoid α] {n : Nat} (f : PointsWithCircumcenterIndex n -> α) :
 ∑ i, f i = (∑ i : Fin (n + 1),…
· 使用定理 `Finset.sum_ite`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid M]
 {s : Finset ι} {p : ι → Prop} [inst_1 : DecidablePred p]   (f g : ι → M), (∑ x 
∈ s,…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.filter_or`：filter_or (s : Finset α) : (s.filter fun a => p a ∨ q 
a) = s.filter p union s.filter q
· 使用定理 `Finset.filter_eq'`：filter_eq' [DecidableEq β] (s : Finset β) (b : β) : (
s.filter fun a => a = b) = ite (b in s) {b} ∅
· 使用定理 `Finset.card_union_of_disjoint`：∀ {α : Type u_1} {s t : Finset α} [inst :
 DecidableEq α], Disjoint s t → (s ∪ t).card = s.card + t.card
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_eq`：∀ {α : Type u} [inst : AddMonoidWithOn
e α] {n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.IsNat a n → ↑n = a' → a = a'
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.isNat_natCast`：isNat_natCast {R} [AddMonoidWithOne 
R] (n m : Nat) : IsNat n m -> IsNat (n : R) m
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `nsmul_zero`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ), n • 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
`reflectionCircumcenterWeightsWithCircumcenter` sums to 1.
-/
theorem sum_reflectionCircumcenterWeightsWithCircumcenter {n : ℕ} {i₁ i₂ : Fin (n + 1)}
    (h : i₁ ≠ i₂) : ∑ i, reflectionCircumcenterWeightsWithCircumcenter i₁ i₂ i = 1 := by
  simp_rw [sum_pointsWithCircumcenter, reflectionCircumcenterWeightsWithCircumcenter, sum_ite,
    sum_const, filter_or, filter_eq']
  rw [card_union_of_disjoint]
  · norm_num
  · simpa only [if_true, mem_univ, disjoint_singleton] using h

/-- The reflection of the circumcenter of a simplex in an edge, in
terms of `pointsWithCircumcenter`. -/
/-
**Affine.Simplex.reflection_circumcenter_eq_affineCombination_of_pointsWithCircu
mcenter** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：reflection_circumcenter_eq_affineCombination_of_pointsWithCircumcenter {n 
: Nat} (s : Simplex Real P n) {i₁ i₂ : Fin (n + 1)} (h : i₁ != i₂) : reflection 
(affineSpan Real (s.points '' {i₁, i₂})) s.circumcenter = (univ : Finset (Points
WithCircumcenterIndex n)).affineCombination Real s.pointsWithCircumcenter (refle
ctionCircumcenterWeightsWithCircumcenter i₁ i₂)
参数：s : Simplex Real P n；n + 1；h : i₁ != i₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_insert_of_notMem`：card_insert_of_notMem (h : a ∉ s) : #(inse
rt a s) = #s + 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `Set.instNonemptyElemImage`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (
s : Set α) [Nonempty ↑s], Nonempty ↑(f '' s)
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
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `EuclideanGeometry.eq_orthogonalProjection_of_eq_subspace`：eq_orthogonalP
rojection_of_eq_subspace {s s' : AffineSubspace 𝕜 P} [Nonempty s] [Nonempty s'] 
[s.direction.HasOrthogonalProjection] [s'.dire…
· 使用定理 `Affine.Simplex.range_face_points`：range_face_points {n : Nat} (s : Simpl
ex k P n) {fs : Finset (Fin (n + 1))} {m : Nat} (h : #fs = m + 1) : Set.range (s
.face h).points = s.po…
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `EuclideanGeometry.reflection_apply'`：reflection_apply' (s : AffineSubspa
ce 𝕜 P) [Nonempty s] [s.direction.HasOrthogonalProjection] (p : P) : reflection 
s p = (↑(orthogonalProjec…
· 使用定理 `Affine.Simplex.orthogonalProjection_circumcenter`：orthogonalProjection_c
ircumcenter {n : Nat} (s : Simplex Real P n) {fs : Finset (Fin (n + 1))} {m : Na
t} (h : #fs = m + 1) : ↑((s.face h).or…
· 使用定理 `Affine.Simplex.circumcenter_eq_centroid`：circumcenter_eq_centroid (s : S
implex Real P 1) : s.circumcenter = Finset.univ.centroid Real s.points
· 使用定理 `Affine.Simplex.face_centroid_eq_centroid`：face_centroid_eq_centroid {n :
 Nat} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : Nat} (h : #fs = m + 1
) : Finset.univ.centroid k (s.…
· 使用定理 `Affine.Simplex.centroid_eq_affineCombination_of_pointsWithCircumcenter`：
centroid_eq_affineCombination_of_pointsWithCircumcenter {n : Nat} (s : Simplex R
eal P n) (fs : Finset (Fin (n + 1))) : fs.centroid Real s.po…
· 使用定理 `Affine.Simplex.circumcenter_eq_affineCombination_of_pointsWithCircumcent
er`：circumcenter_eq_affineCombination_of_pointsWithCircumcenter {n : Nat} (s : S
implex Real P n) : s.circumcenter = (univ : Finset (PointsWithCi…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 63 条，此处仅展示前 30 条）

--- 原说明 ---
The reflection of the circumcenter of a simplex in an edge, in
terms of `pointsWithCircumcenter`.
-/
theorem reflection_circumcenter_eq_affineCombination_of_pointsWithCircumcenter {n : ℕ}
    (s : Simplex ℝ P n) {i₁ i₂ : Fin (n + 1)} (h : i₁ ≠ i₂) :
    reflection (affineSpan ℝ (s.points '' {i₁, i₂})) s.circumcenter =
      (univ : Finset (PointsWithCircumcenterIndex n)).affineCombination ℝ s.pointsWithCircumcenter
        (reflectionCircumcenterWeightsWithCircumcenter i₁ i₂) := by
  have hc : #{i₁, i₂} = 2 := by simp [h]
  -- Making the next line a separate definition helps the elaborator:
  set W : AffineSubspace ℝ P := affineSpan ℝ (s.points '' {i₁, i₂})
  have h_faces :
    (orthogonalProjection W s.circumcenter : P) =
      ↑((s.face hc).orthogonalProjectionSpan s.circumcenter) := by
    apply eq_orthogonalProjection_of_eq_subspace
    simp [W]
  rw [reflection_apply', h_faces, s.orthogonalProjection_circumcenter hc,
    circumcenter_eq_centroid, s.face_centroid_eq_centroid hc,
    centroid_eq_affineCombination_of_pointsWithCircumcenter,
    circumcenter_eq_affineCombination_of_pointsWithCircumcenter, ← @vsub_eq_zero_iff_eq V,
    affineCombination_vsub, weightedVSub_vadd_affineCombination, affineCombination_vsub,
    weightedVSub_apply, sum_pointsWithCircumcenter]
  simp_rw [Pi.sub_apply, Pi.add_apply, Pi.sub_apply, sub_smul, add_smul, sub_smul,
    centroidWeightsWithCircumcenter, circumcenterWeightsWithCircumcenter,
    reflectionCircumcenterWeightsWithCircumcenter, ite_smul, zero_smul, sub_zero,
    apply_ite₂ (· + ·), add_zero, ← add_smul, hc, zero_sub, neg_smul, sub_self, add_zero]
  convert! sum_const_zero
  norm_num

end Simplex

end Affine

namespace EuclideanGeometry

open Affine AffineSubspace Module

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- Given a nonempty affine subspace, whose direction is complete,
that contains a set of points, those points are cospherical if and
only if they are equidistant from some point in that subspace. -/
/-
**EuclideanGeometry.cospherical_iff_exists_mem_of_complete** 是 Mathlib 中的一个定理，位于
命名空间 `EuclideanGeometry`。
形式化陈述：cospherical_iff_exists_mem_of_complete {s : AffineSubspace Real P} {ps : S
et P} (h : ps subseteq s) [Nonempty s] [s.direction.HasOrthogonalProjection] : C
ospherical ps ↔ exists center in s, exists radius : Real, forall p in ps, dist p
 center = radius
参数：h : ps subseteq s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.orthogonalProjection_mem`：orthogonalProjection_mem {s 
: AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalProjection] (p : P)
 : ↑(orthogonalProjection s p) i…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.exists_dist_eq_iff_exists_dist_orthogonalProjection_eq
`：exists_dist_eq_iff_exists_dist_orthogonalProjection_eq {s : AffineSubspace 𝕜 P
} [Nonempty s] [s.direction.HasOrthogonalProjection] {ps : Set…

--- 原说明 ---
Given a nonempty affine subspace, whose direction is complete,
that contains a set of points, those points are cospherical if and
only if they are equidistant from some point in that subspace.
-/
theorem cospherical_iff_exists_mem_of_complete {s : AffineSubspace ℝ P} {ps : Set P} (h : ps ⊆ s)
    [Nonempty s] [s.direction.HasOrthogonalProjection] :
    Cospherical ps ↔ ∃ center ∈ s, ∃ radius : ℝ, ∀ p ∈ ps, dist p center = radius := by
  constructor
  · rintro ⟨c, hcr⟩
    rw [exists_dist_eq_iff_exists_dist_orthogonalProjection_eq h c] at hcr
    exact ⟨orthogonalProjection s c, orthogonalProjection_mem _, hcr⟩
  · exact fun ⟨c, _, hd⟩ => ⟨c, hd⟩

/-- Given a nonempty affine subspace, whose direction is
finite-dimensional, that contains a set of points, those points are
cospherical if and only if they are equidistant from some point in
that subspace. -/
/-
**EuclideanGeometry.cospherical_iff_exists_mem_of_finiteDimensional** 是 Mathlib 
中的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：cospherical_iff_exists_mem_of_finiteDimensional {s : AffineSubspace Real P
} {ps : Set P} (h : ps subseteq s) [Nonempty s] [FiniteDimensional Real s.direct
ion] : Cospherical ps ↔ exists center in s, exists radius : Real, forall p in ps
, dist p center = radius
参数：h : ps subseteq s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.cospherical_iff_exists_mem_of_complete`：cospherical_if
f_exists_mem_of_complete {s : AffineSubspace Real P} {ps : Set P} (h : ps subset
eq s) [Nonempty s] [s.direction.HasOrthogonalP…
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…

--- 原说明 ---
Given a nonempty affine subspace, whose direction is
finite-dimensional, that contains a set of points, those points are
cospherical if and only if they are equidistant from some point in
that subspace.
-/
theorem cospherical_iff_exists_mem_of_finiteDimensional {s : AffineSubspace ℝ P} {ps : Set P}
    (h : ps ⊆ s) [Nonempty s] [FiniteDimensional ℝ s.direction] :
    Cospherical ps ↔ ∃ center ∈ s, ∃ radius : ℝ, ∀ p ∈ ps, dist p center = radius :=
  cospherical_iff_exists_mem_of_complete h

/-- All n-simplices among cospherical points in an n-dimensional
subspace have the same circumradius. -/
/-
**EuclideanGeometry.exists_circumradius_eq_of_cospherical_subset** 是 Mathlib 中的一
个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：exists_circumradius_eq_of_cospherical_subset {s : AffineSubspace Real P} {
ps : Set P} (h : ps subseteq s) [Nonempty s] {n : Nat} [FiniteDimensional Real s
.direction] (hd : finrank Real s.direction = n) (hc : Cospherical ps) : exists r
 : Real, forall sx : Simplex Real P n, Set.range sx.points subseteq ps -> sx.cir
cumradius = r
参数：h : ps subseteq s；hd : finrank Real s.direction = n；hc : Cospherical ps。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.cospherical_iff_exists_mem_of_finiteDimensional`：cosph
erical_iff_exists_mem_of_finiteDimensional {s : AffineSubspace Real P} {ps : Set
 P} (h : ps subseteq s) [Nonempty s] [FiniteDimensional…
· 使用定理 `AffineIndependent.affineSpan_eq_of_le_of_card_eq_finrank_add_one`：Affine
Independent.affineSpan_eq_of_le_of_card_eq_finrank_add_one [Fintype ι] {p : ι ->
 P} (hi : AffineIndependent k p) {sp : AffineSubspace …
· 使用定理 `Affine.Simplex.independent`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [ins
t_3 : AddTorsor …
· 使用定理 `affineSpan_le_of_subset_coe`：affineSpan_le_of_subset_coe {s : Set P} {s₁
 : AffineSubspace k P} (h : s subseteq s₁) : affineSpan k s <= s₁
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Affine.Simplex.eq_circumradius_of_dist_eq`：eq_circumradius_of_dist_eq {n
 : Nat} (s : Simplex Real P n) {p : P} (hp : p in affineSpan Real (Set.range s.p
oints)) {r : Real} (hr : forall…
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f

--- 原说明 ---
All n-simplices among cospherical points in an n-dimensional
subspace have the same circumradius.
-/
theorem exists_circumradius_eq_of_cospherical_subset {s : AffineSubspace ℝ P} {ps : Set P}
    (h : ps ⊆ s) [Nonempty s] {n : ℕ} [FiniteDimensional ℝ s.direction]
    (hd : finrank ℝ s.direction = n) (hc : Cospherical ps) :
    ∃ r : ℝ, ∀ sx : Simplex ℝ P n, Set.range sx.points ⊆ ps → sx.circumradius = r := by
  rw [cospherical_iff_exists_mem_of_finiteDimensional h] at hc
  rcases hc with ⟨c, hc, r, hcr⟩
  use r
  intro sx hsxps
  have hsx : affineSpan ℝ (Set.range sx.points) = s := by
    refine
      sx.independent.affineSpan_eq_of_le_of_card_eq_finrank_add_one
        (affineSpan_le_of_subset_coe (hsxps.trans h)) ?_
    simp [hd]
  have hc : c ∈ affineSpan ℝ (Set.range sx.points) := hsx.symm ▸ hc
  exact
    (sx.eq_circumradius_of_dist_eq hc fun i =>
        hcr (sx.points i) (hsxps (Set.mem_range_self i))).symm

/-- Two n-simplices among cospherical points in an n-dimensional
subspace have the same circumradius. -/
/-
**EuclideanGeometry.circumradius_eq_of_cospherical_subset** 是 Mathlib 中的一个定理，位于命
名空间 `EuclideanGeometry`。
形式化陈述：circumradius_eq_of_cospherical_subset {s : AffineSubspace Real P} {ps : Se
t P} (h : ps subseteq s) [Nonempty s] {n : Nat} [FiniteDimensional Real s.direct
ion] (hd : finrank Real s.direction = n) (hc : Cospherical ps) {sx₁ sx₂ : Simple
x Real P n} (hsx₁ : Set.range sx₁.points subseteq ps) (hsx₂ : Set.range sx₂.poin
ts subseteq ps) : sx₁.circumradius = sx₂.circumradius
参数：h : ps subseteq s；hd : finrank Real s.direction = n；hc : Cospherical ps；hsx₁ 
: Set.range sx₁.points subseteq ps；hsx₂ : Set.range sx₂.points subseteq ps。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.exists_circumradius_eq_of_cospherical_subset`：exists_c
ircumradius_eq_of_cospherical_subset {s : AffineSubspace Real P} {ps : Set P} (h
 : ps subseteq s) [Nonempty s] {n : Nat} [FiniteDime…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
Two n-simplices among cospherical points in an n-dimensional
subspace have the same circumradius.
-/
theorem circumradius_eq_of_cospherical_subset {s : AffineSubspace ℝ P} {ps : Set P} (h : ps ⊆ s)
    [Nonempty s] {n : ℕ} [FiniteDimensional ℝ s.direction] (hd : finrank ℝ s.direction = n)
    (hc : Cospherical ps) {sx₁ sx₂ : Simplex ℝ P n} (hsx₁ : Set.range sx₁.points ⊆ ps)
    (hsx₂ : Set.range sx₂.points ⊆ ps) : sx₁.circumradius = sx₂.circumradius := by
  rcases exists_circumradius_eq_of_cospherical_subset h hd hc with ⟨r, hr⟩
  rw [hr sx₁ hsx₁, hr sx₂ hsx₂]

/-- All n-simplices among cospherical points in n-space have the same
circumradius. -/
/-
**EuclideanGeometry.exists_circumradius_eq_of_cospherical** 是 Mathlib 中的一个定理，位于命
名空间 `EuclideanGeometry`。
形式化陈述：exists_circumradius_eq_of_cospherical {ps : Set P} {n : Nat} [FiniteDimens
ional Real V] (hd : finrank Real V = n) (hc : Cospherical ps) : exists r : Real,
 forall sx : Simplex Real P n, Set.range sx.points subseteq ps -> sx.circumradiu
s = r
参数：hd : finrank Real V = n；hc : Cospherical ps。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.exists_circumradius_eq_of_cospherical_subset`：exists_c
ircumradius_eq_of_cospherical_subset {s : AffineSubspace Real P} {ps : Set P} (h
 : ps subseteq s) [Nonempty s] {n : Nat} [FiniteDime…
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `AffineSubspace.instNonemptySubtypeMemTop`：∀ (k : Type u_1) (V : Type u_2
) (P : Type u_3) [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Modu
le k V]   [S : AddTorsor V P],…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineSubspace.direction_top`：direction_top : (⊤ : AffineSubspace k P).d
irection = ⊤
· 使用定理 `finrank_top`：finrank_top : finrank R (⊤ : Submodule R M) = finrank R M

--- 原说明 ---
All n-simplices among cospherical points in n-space have the same
circumradius.
-/
theorem exists_circumradius_eq_of_cospherical {ps : Set P} {n : ℕ} [FiniteDimensional ℝ V]
    (hd : finrank ℝ V = n) (hc : Cospherical ps) :
    ∃ r : ℝ, ∀ sx : Simplex ℝ P n, Set.range sx.points ⊆ ps → sx.circumradius = r := by
  rw [← finrank_top, ← direction_top ℝ V P] at hd
  refine exists_circumradius_eq_of_cospherical_subset ?_ hd hc
  exact Set.subset_univ _

/-- Two n-simplices among cospherical points in n-space have the same
circumradius. -/
/-
**EuclideanGeometry.circumradius_eq_of_cospherical** 是 Mathlib 中的一个定理，位于命名空间 `Eu
clideanGeometry`。
形式化陈述：circumradius_eq_of_cospherical {ps : Set P} {n : Nat} [FiniteDimensional R
eal V] (hd : finrank Real V = n) (hc : Cospherical ps) {sx₁ sx₂ : Simplex Real P
 n} (hsx₁ : Set.range sx₁.points subseteq ps) (hsx₂ : Set.range sx₂.points subse
teq ps) : sx₁.circumradius = sx₂.circumradius
参数：hd : finrank Real V = n；hc : Cospherical ps；hsx₁ : Set.range sx₁.points subse
teq ps；hsx₂ : Set.range sx₂.points subseteq ps。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.exists_circumradius_eq_of_cospherical`：exists_circumra
dius_eq_of_cospherical {ps : Set P} {n : Nat} [FiniteDimensional Real V] (hd : f
inrank Real V = n) (hc : Cospherical ps) : ex…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
Two n-simplices among cospherical points in n-space have the same
circumradius.
-/
theorem circumradius_eq_of_cospherical {ps : Set P} {n : ℕ} [FiniteDimensional ℝ V]
    (hd : finrank ℝ V = n) (hc : Cospherical ps) {sx₁ sx₂ : Simplex ℝ P n}
    (hsx₁ : Set.range sx₁.points ⊆ ps) (hsx₂ : Set.range sx₂.points ⊆ ps) :
    sx₁.circumradius = sx₂.circumradius := by
  rcases exists_circumradius_eq_of_cospherical hd hc with ⟨r, hr⟩
  rw [hr sx₁ hsx₁, hr sx₂ hsx₂]

/-- All n-simplices among cospherical points in an n-dimensional
subspace have the same circumcenter. -/
/-
**EuclideanGeometry.exists_circumcenter_eq_of_cospherical_subset** 是 Mathlib 中的一
个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：exists_circumcenter_eq_of_cospherical_subset {s : AffineSubspace Real P} {
ps : Set P} (h : ps subseteq s) [Nonempty s] {n : Nat} [FiniteDimensional Real s
.direction] (hd : finrank Real s.direction = n) (hc : Cospherical ps) : exists c
 : P, forall sx : Simplex Real P n, Set.range sx.points subseteq ps -> sx.circum
center = c
参数：h : ps subseteq s；hd : finrank Real s.direction = n；hc : Cospherical ps。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.cospherical_iff_exists_mem_of_finiteDimensional`：cosph
erical_iff_exists_mem_of_finiteDimensional {s : AffineSubspace Real P} {ps : Set
 P} (h : ps subseteq s) [Nonempty s] [FiniteDimensional…
· 使用定理 `AffineIndependent.affineSpan_eq_of_le_of_card_eq_finrank_add_one`：Affine
Independent.affineSpan_eq_of_le_of_card_eq_finrank_add_one [Fintype ι] {p : ι ->
 P} (hi : AffineIndependent k p) {sp : AffineSubspace …
· 使用定理 `Affine.Simplex.independent`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [ins
t_3 : AddTorsor …
· 使用定理 `affineSpan_le_of_subset_coe`：affineSpan_le_of_subset_coe {s : Set P} {s₁
 : AffineSubspace k P} (h : s subseteq s₁) : affineSpan k s <= s₁
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Affine.Simplex.eq_circumcenter_of_dist_eq`：eq_circumcenter_of_dist_eq {n
 : Nat} (s : Simplex Real P n) {p : P} (hp : p in affineSpan Real (Set.range s.p
oints)) {r : Real} (hr : forall…
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f

--- 原说明 ---
All n-simplices among cospherical points in an n-dimensional
subspace have the same circumcenter.
-/
theorem exists_circumcenter_eq_of_cospherical_subset {s : AffineSubspace ℝ P} {ps : Set P}
    (h : ps ⊆ s) [Nonempty s] {n : ℕ} [FiniteDimensional ℝ s.direction]
    (hd : finrank ℝ s.direction = n) (hc : Cospherical ps) :
    ∃ c : P, ∀ sx : Simplex ℝ P n, Set.range sx.points ⊆ ps → sx.circumcenter = c := by
  rw [cospherical_iff_exists_mem_of_finiteDimensional h] at hc
  rcases hc with ⟨c, hc, r, hcr⟩
  use c
  intro sx hsxps
  have hsx : affineSpan ℝ (Set.range sx.points) = s := by
    refine
      sx.independent.affineSpan_eq_of_le_of_card_eq_finrank_add_one
        (affineSpan_le_of_subset_coe (hsxps.trans h)) ?_
    simp [hd]
  have hc : c ∈ affineSpan ℝ (Set.range sx.points) := hsx.symm ▸ hc
  exact
    (sx.eq_circumcenter_of_dist_eq hc fun i =>
        hcr (sx.points i) (hsxps (Set.mem_range_self i))).symm

/-- Two n-simplices among cospherical points in an n-dimensional
subspace have the same circumcenter. -/
/-
**EuclideanGeometry.circumcenter_eq_of_cospherical_subset** 是 Mathlib 中的一个定理，位于命
名空间 `EuclideanGeometry`。
形式化陈述：circumcenter_eq_of_cospherical_subset {s : AffineSubspace Real P} {ps : Se
t P} (h : ps subseteq s) [Nonempty s] {n : Nat} [FiniteDimensional Real s.direct
ion] (hd : finrank Real s.direction = n) (hc : Cospherical ps) {sx₁ sx₂ : Simple
x Real P n} (hsx₁ : Set.range sx₁.points subseteq ps) (hsx₂ : Set.range sx₂.poin
ts subseteq ps) : sx₁.circumcenter = sx₂.circumcenter
参数：h : ps subseteq s；hd : finrank Real s.direction = n；hc : Cospherical ps；hsx₁ 
: Set.range sx₁.points subseteq ps；hsx₂ : Set.range sx₂.points subseteq ps。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.exists_circumcenter_eq_of_cospherical_subset`：exists_c
ircumcenter_eq_of_cospherical_subset {s : AffineSubspace Real P} {ps : Set P} (h
 : ps subseteq s) [Nonempty s] {n : Nat} [FiniteDime…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
Two n-simplices among cospherical points in an n-dimensional
subspace have the same circumcenter.
-/
theorem circumcenter_eq_of_cospherical_subset {s : AffineSubspace ℝ P} {ps : Set P} (h : ps ⊆ s)
    [Nonempty s] {n : ℕ} [FiniteDimensional ℝ s.direction] (hd : finrank ℝ s.direction = n)
    (hc : Cospherical ps) {sx₁ sx₂ : Simplex ℝ P n} (hsx₁ : Set.range sx₁.points ⊆ ps)
    (hsx₂ : Set.range sx₂.points ⊆ ps) : sx₁.circumcenter = sx₂.circumcenter := by
  rcases exists_circumcenter_eq_of_cospherical_subset h hd hc with ⟨r, hr⟩
  rw [hr sx₁ hsx₁, hr sx₂ hsx₂]

/-- All n-simplices among cospherical points in n-space have the same
circumcenter. -/
/-
**EuclideanGeometry.exists_circumcenter_eq_of_cospherical** 是 Mathlib 中的一个定理，位于命
名空间 `EuclideanGeometry`。
形式化陈述：exists_circumcenter_eq_of_cospherical {ps : Set P} {n : Nat} [FiniteDimens
ional Real V] (hd : finrank Real V = n) (hc : Cospherical ps) : exists c : P, fo
rall sx : Simplex Real P n, Set.range sx.points subseteq ps -> sx.circumcenter =
 c
参数：hd : finrank Real V = n；hc : Cospherical ps。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.exists_circumcenter_eq_of_cospherical_subset`：exists_c
ircumcenter_eq_of_cospherical_subset {s : AffineSubspace Real P} {ps : Set P} (h
 : ps subseteq s) [Nonempty s] {n : Nat} [FiniteDime…
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `AffineSubspace.instNonemptySubtypeMemTop`：∀ (k : Type u_1) (V : Type u_2
) (P : Type u_3) [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Modu
le k V]   [S : AddTorsor V P],…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineSubspace.direction_top`：direction_top : (⊤ : AffineSubspace k P).d
irection = ⊤
· 使用定理 `finrank_top`：finrank_top : finrank R (⊤ : Submodule R M) = finrank R M

--- 原说明 ---
All n-simplices among cospherical points in n-space have the same
circumcenter.
-/
theorem exists_circumcenter_eq_of_cospherical {ps : Set P} {n : ℕ} [FiniteDimensional ℝ V]
    (hd : finrank ℝ V = n) (hc : Cospherical ps) :
    ∃ c : P, ∀ sx : Simplex ℝ P n, Set.range sx.points ⊆ ps → sx.circumcenter = c := by
  rw [← finrank_top, ← direction_top ℝ V P] at hd
  refine exists_circumcenter_eq_of_cospherical_subset ?_ hd hc
  exact Set.subset_univ _

/-- Two n-simplices among cospherical points in n-space have the same
circumcenter. -/
/-
**EuclideanGeometry.circumcenter_eq_of_cospherical** 是 Mathlib 中的一个定理，位于命名空间 `Eu
clideanGeometry`。
形式化陈述：circumcenter_eq_of_cospherical {ps : Set P} {n : Nat} [FiniteDimensional R
eal V] (hd : finrank Real V = n) (hc : Cospherical ps) {sx₁ sx₂ : Simplex Real P
 n} (hsx₁ : Set.range sx₁.points subseteq ps) (hsx₂ : Set.range sx₂.points subse
teq ps) : sx₁.circumcenter = sx₂.circumcenter
参数：hd : finrank Real V = n；hc : Cospherical ps；hsx₁ : Set.range sx₁.points subse
teq ps；hsx₂ : Set.range sx₂.points subseteq ps。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.exists_circumcenter_eq_of_cospherical`：exists_circumce
nter_eq_of_cospherical {ps : Set P} {n : Nat} [FiniteDimensional Real V] (hd : f
inrank Real V = n) (hc : Cospherical ps) : ex…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
Two n-simplices among cospherical points in n-space have the same
circumcenter.
-/
theorem circumcenter_eq_of_cospherical {ps : Set P} {n : ℕ} [FiniteDimensional ℝ V]
    (hd : finrank ℝ V = n) (hc : Cospherical ps) {sx₁ sx₂ : Simplex ℝ P n}
    (hsx₁ : Set.range sx₁.points ⊆ ps) (hsx₂ : Set.range sx₂.points ⊆ ps) :
    sx₁.circumcenter = sx₂.circumcenter := by
  rcases exists_circumcenter_eq_of_cospherical hd hc with ⟨r, hr⟩
  rw [hr sx₁ hsx₁, hr sx₂ hsx₂]

/-- All n-simplices among cospherical points in an n-dimensional
subspace have the same circumsphere. -/
/-
**EuclideanGeometry.exists_circumsphere_eq_of_cospherical_subset** 是 Mathlib 中的一
个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：exists_circumsphere_eq_of_cospherical_subset {s : AffineSubspace Real P} {
ps : Set P} (h : ps subseteq s) [Nonempty s] {n : Nat} [FiniteDimensional Real s
.direction] (hd : finrank Real s.direction = n) (hc : Cospherical ps) : exists c
 : Sphere P, forall sx : Simplex Real P n, Set.range sx.points subseteq ps -> sx
.circumsphere = c
参数：h : ps subseteq s；hd : finrank Real s.direction = n；hc : Cospherical ps。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.exists_circumradius_eq_of_cospherical_subset`：exists_c
ircumradius_eq_of_cospherical_subset {s : AffineSubspace Real P} {ps : Set P} (h
 : ps subseteq s) [Nonempty s] {n : Nat} [FiniteDime…
· 使用定理 `EuclideanGeometry.exists_circumcenter_eq_of_cospherical_subset`：exists_c
ircumcenter_eq_of_cospherical_subset {s : AffineSubspace Real P} {ps : Set P} (h
 : ps subseteq s) [Nonempty s] {n : Nat} [FiniteDime…
· 使用定理 `EuclideanGeometry.Sphere.ext`：∀ {P : Type u_2} {inst : MetricSpace P} {x
 y : EuclideanGeometry.Sphere P},   x.center = y.center → x.radius = y.radius → 
x = y

--- 原说明 ---
All n-simplices among cospherical points in an n-dimensional
subspace have the same circumsphere.
-/
theorem exists_circumsphere_eq_of_cospherical_subset {s : AffineSubspace ℝ P} {ps : Set P}
    (h : ps ⊆ s) [Nonempty s] {n : ℕ} [FiniteDimensional ℝ s.direction]
    (hd : finrank ℝ s.direction = n) (hc : Cospherical ps) :
    ∃ c : Sphere P, ∀ sx : Simplex ℝ P n, Set.range sx.points ⊆ ps → sx.circumsphere = c := by
  obtain ⟨r, hr⟩ := exists_circumradius_eq_of_cospherical_subset h hd hc
  obtain ⟨c, hc⟩ := exists_circumcenter_eq_of_cospherical_subset h hd hc
  exact ⟨⟨c, r⟩, fun sx hsx => Sphere.ext (hc sx hsx) (hr sx hsx)⟩

/-- Two n-simplices among cospherical points in an n-dimensional
subspace have the same circumsphere. -/
/-
**EuclideanGeometry.circumsphere_eq_of_cospherical_subset** 是 Mathlib 中的一个定理，位于命
名空间 `EuclideanGeometry`。
形式化陈述：circumsphere_eq_of_cospherical_subset {s : AffineSubspace Real P} {ps : Se
t P} (h : ps subseteq s) [Nonempty s] {n : Nat} [FiniteDimensional Real s.direct
ion] (hd : finrank Real s.direction = n) (hc : Cospherical ps) {sx₁ sx₂ : Simple
x Real P n} (hsx₁ : Set.range sx₁.points subseteq ps) (hsx₂ : Set.range sx₂.poin
ts subseteq ps) : sx₁.circumsphere = sx₂.circumsphere
参数：h : ps subseteq s；hd : finrank Real s.direction = n；hc : Cospherical ps；hsx₁ 
: Set.range sx₁.points subseteq ps；hsx₂ : Set.range sx₂.points subseteq ps。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.exists_circumsphere_eq_of_cospherical_subset`：exists_c
ircumsphere_eq_of_cospherical_subset {s : AffineSubspace Real P} {ps : Set P} (h
 : ps subseteq s) [Nonempty s] {n : Nat} [FiniteDime…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
Two n-simplices among cospherical points in an n-dimensional
subspace have the same circumsphere.
-/
theorem circumsphere_eq_of_cospherical_subset {s : AffineSubspace ℝ P} {ps : Set P} (h : ps ⊆ s)
    [Nonempty s] {n : ℕ} [FiniteDimensional ℝ s.direction] (hd : finrank ℝ s.direction = n)
    (hc : Cospherical ps) {sx₁ sx₂ : Simplex ℝ P n} (hsx₁ : Set.range sx₁.points ⊆ ps)
    (hsx₂ : Set.range sx₂.points ⊆ ps) : sx₁.circumsphere = sx₂.circumsphere := by
  rcases exists_circumsphere_eq_of_cospherical_subset h hd hc with ⟨r, hr⟩
  rw [hr sx₁ hsx₁, hr sx₂ hsx₂]

/-- All n-simplices among cospherical points in n-space have the same
circumsphere. -/
/-
**EuclideanGeometry.exists_circumsphere_eq_of_cospherical** 是 Mathlib 中的一个定理，位于命
名空间 `EuclideanGeometry`。
形式化陈述：exists_circumsphere_eq_of_cospherical {ps : Set P} {n : Nat} [FiniteDimens
ional Real V] (hd : finrank Real V = n) (hc : Cospherical ps) : exists c : Spher
e P, forall sx : Simplex Real P n, Set.range sx.points subseteq ps -> sx.circums
phere = c
参数：hd : finrank Real V = n；hc : Cospherical ps。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.exists_circumsphere_eq_of_cospherical_subset`：exists_c
ircumsphere_eq_of_cospherical_subset {s : AffineSubspace Real P} {ps : Set P} (h
 : ps subseteq s) [Nonempty s] {n : Nat} [FiniteDime…
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `AffineSubspace.instNonemptySubtypeMemTop`：∀ (k : Type u_1) (V : Type u_2
) (P : Type u_3) [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Modu
le k V]   [S : AddTorsor V P],…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineSubspace.direction_top`：direction_top : (⊤ : AffineSubspace k P).d
irection = ⊤
· 使用定理 `finrank_top`：finrank_top : finrank R (⊤ : Submodule R M) = finrank R M

--- 原说明 ---
All n-simplices among cospherical points in n-space have the same
circumsphere.
-/
theorem exists_circumsphere_eq_of_cospherical {ps : Set P} {n : ℕ} [FiniteDimensional ℝ V]
    (hd : finrank ℝ V = n) (hc : Cospherical ps) :
    ∃ c : Sphere P, ∀ sx : Simplex ℝ P n, Set.range sx.points ⊆ ps → sx.circumsphere = c := by
  rw [← finrank_top, ← direction_top ℝ V P] at hd
  refine exists_circumsphere_eq_of_cospherical_subset ?_ hd hc
  exact Set.subset_univ _

/-- Two n-simplices among cospherical points in n-space have the same
circumsphere. -/
/-
**EuclideanGeometry.circumsphere_eq_of_cospherical** 是 Mathlib 中的一个定理，位于命名空间 `Eu
clideanGeometry`。
形式化陈述：circumsphere_eq_of_cospherical {ps : Set P} {n : Nat} [FiniteDimensional R
eal V] (hd : finrank Real V = n) (hc : Cospherical ps) {sx₁ sx₂ : Simplex Real P
 n} (hsx₁ : Set.range sx₁.points subseteq ps) (hsx₂ : Set.range sx₂.points subse
teq ps) : sx₁.circumsphere = sx₂.circumsphere
参数：hd : finrank Real V = n；hc : Cospherical ps；hsx₁ : Set.range sx₁.points subse
teq ps；hsx₂ : Set.range sx₂.points subseteq ps。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.exists_circumsphere_eq_of_cospherical`：exists_circumsp
here_eq_of_cospherical {ps : Set P} {n : Nat} [FiniteDimensional Real V] (hd : f
inrank Real V = n) (hc : Cospherical ps) : ex…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
Two n-simplices among cospherical points in n-space have the same
circumsphere.
-/
theorem circumsphere_eq_of_cospherical {ps : Set P} {n : ℕ} [FiniteDimensional ℝ V]
    (hd : finrank ℝ V = n) (hc : Cospherical ps) {sx₁ sx₂ : Simplex ℝ P n}
    (hsx₁ : Set.range sx₁.points ⊆ ps) (hsx₂ : Set.range sx₂.points ⊆ ps) :
    sx₁.circumsphere = sx₂.circumsphere := by
  rcases exists_circumsphere_eq_of_cospherical hd hc with ⟨r, hr⟩
  rw [hr sx₁ hsx₁, hr sx₂ hsx₂]

/-- Suppose all distances from `p₁` and `p₂` to the points of a
simplex are equal, and that `p₁` and `p₂` lie in the affine span of
`p` with the vertices of that simplex.  Then `p₁` and `p₂` are equal
or reflections of each other in the affine span of the vertices of the
simplex. -/
/-
**EuclideanGeometry.eq_or_eq_reflection_of_dist_eq** 是 Mathlib 中的一个定理，位于命名空间 `Eu
clideanGeometry`。
形式化陈述：eq_or_eq_reflection_of_dist_eq {n : Nat} {s : Simplex Real P n} {p p₁ p₂ :
 P} {r : Real} (hp₁ : p₁ in affineSpan Real (insert p (Set.range s.points))) (hp
₂ : p₂ in affineSpan Real (insert p (Set.range s.points))) (h₁ : forall i, dist 
(s.points i) p₁ = r) (h₂ : forall i, dist (s.points i) p₂ = r) : p₁ = p₂ ∨ p₁ = 
reflection (affineSpan Real (Set.range s.points)) p₂
参数：hp₁ : p₁ in affineSpan Real (insert p (Set.range s.points))；hp₂ : p₂ in affin
eSpan Real (insert p (Set.range s.points))；h₁ : forall i, dist (s.points i) p₁ =
 r；h₂ : forall i, dist (s.points i) p₂ = r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptySubtypeMemAffineSubspaceAffineSpanOfElem`：∀ (k : Type u_1) {
V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 :
 _root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Affine.Simplex.orthogonalProjection_eq_circumcenter_of_dist_eq`：orthogon
alProjection_eq_circumcenter_of_dist_eq {n : Nat} (s : Simplex Real P n) {p : P}
 {r : Real} (hr : forall i, dist (s.points i) p = r)…
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
· 使用定理 `AffineSubspace.mem_affineSpan_insert_iff`：mem_affineSpan_insert_iff {s :
 AffineSubspace k P} {p₁ : P} (hp₁ : p₁ in s) (p₂ p : P) : p in affineSpan k (in
sert p₂ (s : Set P)) ↔ exists …
· 使用定理 `EuclideanGeometry.orthogonalProjection_mem`：orthogonalProjection_mem {s 
: AffineSubspace 𝕜 P} [Nonempty s] [s.direction.HasOrthogonalProjection] (p : P)
 : ↑(orthogonalProjection s p) i…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `affineSpan_insert_affineSpan`：affineSpan_insert_affineSpan (p : P) (ps :
 Set P) : affineSpan k (insert p (affineSpan k ps : Set P)) = affineSpan k (inse
rt p ps)
· 使用定理 `mem_affineSpan`：mem_affineSpan {p : P} {s : Set P} (hp : p in s) : p in 
affineSpan k s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Affine.Simplex.dist_circumcenter_sq_eq_sq_sub_circumradius`：dist_circumc
enter_sq_eq_sq_sub_circumradius {n : Nat} {r : Real} (s : Simplex Real P n) {p₁ 
: P} (h₁ : forall i : Fin (n + 1), dist (s.point…
· 使用定理 `Affine.Simplex.orthogonalProjectionSpan.eq_1`：∀ {𝕜 : Type u_1} {V : Type
 u_2} {P : Type u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup V]   [inst_2
 : InnerProductSpace 𝕜 V] [inst_3 …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `mul_self_eq_mul_self_iff`：mul_self_eq_mul_self_iff [NonUnitalNonAssocCom
mRing R] [NoZeroDivisors R] {a b : R} : a * a = b * b ↔ a = b ∨ a = -b
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用引理 `mul_left_inj'`：mul_left_inj' (hc : c != 0) : a * c = b * c ↔ a = b
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
Suppose all distances from `p₁` and `p₂` to the points of a
simplex are equal, and that `p₁` and `p₂` lie in the affine span of
`p` with the vertices of that simplex.  Then `p₁` and `p₂` are equal
or reflections of each other in the affine span of the vertices of the
simplex.
-/
theorem eq_or_eq_reflection_of_dist_eq {n : ℕ} {s : Simplex ℝ P n} {p p₁ p₂ : P} {r : ℝ}
    (hp₁ : p₁ ∈ affineSpan ℝ (insert p (Set.range s.points)))
    (hp₂ : p₂ ∈ affineSpan ℝ (insert p (Set.range s.points))) (h₁ : ∀ i, dist (s.points i) p₁ = r)
    (h₂ : ∀ i, dist (s.points i) p₂ = r) :
    p₁ = p₂ ∨ p₁ = reflection (affineSpan ℝ (Set.range s.points)) p₂ := by
  set span_s := affineSpan ℝ (Set.range s.points)
  have h₁' := s.orthogonalProjection_eq_circumcenter_of_dist_eq h₁
  have h₂' := s.orthogonalProjection_eq_circumcenter_of_dist_eq h₂
  rw [← affineSpan_insert_affineSpan, mem_affineSpan_insert_iff (orthogonalProjection_mem p)]
    at hp₁ hp₂
  obtain ⟨r₁, p₁o, hp₁o, hp₁⟩ := hp₁
  obtain ⟨r₂, p₂o, hp₂o, hp₂⟩ := hp₂
  obtain rfl : ↑(s.orthogonalProjectionSpan p₁) = p₁o := by
    subst hp₁
    exact s.coe_orthogonalProjection_vadd_smul_vsub_orthogonalProjection hp₁o
  rw [h₁'] at hp₁
  obtain rfl : ↑(s.orthogonalProjectionSpan p₂) = p₂o := by
    subst hp₂
    exact s.coe_orthogonalProjection_vadd_smul_vsub_orthogonalProjection hp₂o
  rw [h₂'] at hp₂
  have h : s.points 0 ∈ span_s := mem_affineSpan ℝ (Set.mem_range_self _)
  have hd₁ :
    dist p₁ s.circumcenter * dist p₁ s.circumcenter = r * r - s.circumradius * s.circumradius :=
    s.dist_circumcenter_sq_eq_sq_sub_circumradius h₁ h₁' h
  have hd₂ :
    dist p₂ s.circumcenter * dist p₂ s.circumcenter = r * r - s.circumradius * s.circumradius :=
    s.dist_circumcenter_sq_eq_sq_sub_circumradius h₂ h₂' h
  rw [← hd₂, hp₁, hp₂, dist_eq_norm_vsub V _ s.circumcenter, dist_eq_norm_vsub V _ s.circumcenter,
    vadd_vsub, vadd_vsub, ← real_inner_self_eq_norm_mul_norm, ← real_inner_self_eq_norm_mul_norm,
    real_inner_smul_left, real_inner_smul_left, real_inner_smul_right, real_inner_smul_right, ←
    mul_assoc, ← mul_assoc] at hd₁
  by_cases hp : p = s.orthogonalProjectionSpan p
  · rw [Simplex.orthogonalProjectionSpan] at hp
    rw [hp₁, hp₂, ← hp]
    simp only [true_or, smul_zero, vsub_self]
  · have hz : ⟪p -ᵥ orthogonalProjection span_s p, p -ᵥ orthogonalProjection span_s p⟫ ≠ 0 := by
      simpa only [Ne, vsub_eq_zero_iff_eq, inner_self_eq_zero] using! hp
    rw [mul_left_inj' hz, mul_self_eq_mul_self_iff] at hd₁
    rw [hp₁, hp₂]
    rcases hd₁ with hd₁ | hd₁
    · left
      rw [hd₁]
    · right
      rw [hd₁, reflection_vadd_smul_vsub_orthogonalProjection p r₂ s.circumcenter_mem_affineSpan,
        neg_smul]

end EuclideanGeometry

