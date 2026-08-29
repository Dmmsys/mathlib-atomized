/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Rat
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Topology.Order.Lattice

/-!
# Normed lattice ordered groups

Motivated by the theory of Banach Lattices, we then define `NormedLatticeAddCommGroup` as a
lattice with a covariant normed group addition satisfying the solid axiom.

## Main statements

We show that a normed lattice ordered group is a topological lattice with respect to the norm
topology.

## References

* [Meyer-Nieberg, Banach lattices][MeyerNieberg1991]

## Tags

normed, lattice, ordered, group
-/

public section


/-!
### Normed lattice ordered groups

Motivated by the theory of Banach Lattices, this section introduces normed lattice ordered groups.
-/

section SolidNorm

/--
Definition of `HasSolidNorm` / `HasSolidNorm` 的定义

English:
class HasSolidNorm
  parameters: (α : Type*) [NormedAddCommGroup α] [Lattice α]
  axioms and operations (1):
    - solid : forall ⦃x y : α⦄, |x| <= |y| -> ‖x‖ <= ‖y‖

中文:
类 HasSolidNorm
  参数: (α : 类型) [NormedAddCommGroup α] [Lattice α]
  公理与运算 (1 个):
    - solid : 对任意 ⦃x y : α⦄, |x| <= |y| -> ‖x‖ <= ‖y‖
-/
class HasSolidNorm (α : Type*) [NormedAddCommGroup α] [Lattice α] : Prop where
  solid : forall ⦃x y : α⦄, |x| <= |y| -> ‖x‖ <= ‖y‖

variable {α : Type*} [NormedAddCommGroup α] [Lattice α] [HasSolidNorm α]

/--
theorem `norm_le_norm_of_abs_le_abs` / 定理 `norm_le_norm_of_abs_le_abs`

English:
theorem norm_le_norm_of_abs_le_abs
  given: {a b : α} (h : |a| <= |b|)
  statement: ‖a‖ <= ‖b‖
  proof: HasSolidNorm.solid h

中文:
定理 norm_le_norm_of_abs_le_abs
  条件: {a b : α} (h : |a| <= |b|)
  结论: ‖a‖ <= ‖b‖
  证明: HasSolidNorm.solid h

Depends on / 依赖: HasSolidNorm, HasSolidNorm.solid
-/
theorem norm_le_norm_of_abs_le_abs {a b : α} (h : |a| <= |b|) : ‖a‖ <= ‖b‖ :=
  HasSolidNorm.solid h

/--
theorem `LatticeOrderedAddCommGroup.isSolid_ball` / 定理 `LatticeOrderedAddCommGroup.isSolid_ball`

English:
theorem LatticeOrderedAddCommGroup.isSolid_ball
  given: (r : Real)
  proof: fun _ hx _ hxy =>
  mem_ball_zero_iff.mpr ((HasSolidNorm.solid hxy).trans_lt (mem_ball_zero_iff.mp hx))

中文:
定理 LatticeOrderedAddCommGroup.isSolid_ball
  条件: (r : 实数)
  证明: fun _ hx _ hxy =>
  mem_ball_zero_iff.mpr ((HasSolidNorm.solid hxy).trans_lt (mem_ball_zero_iff.mp hx))
-/
theorem LatticeOrderedAddCommGroup.isSolid_ball (r : Real) :
    LatticeOrderedAddCommGroup.IsSolid (Metric.ball (0 : α) r) := fun _ hx _ hxy =>
  mem_ball_zero_iff.mpr ((HasSolidNorm.solid hxy).trans_lt (mem_ball_zero_iff.mp hx))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasSolidNorm Real
  body: ⟨fun _ _ => id⟩

中文:
实例 :
  签名: HasSolidNorm 实数
  定义体: ⟨fun _ _ => id⟩
-/
instance : HasSolidNorm Real := ⟨fun _ _ => id⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasSolidNorm Rat
  body: ⟨fun _ _ _ => by simpa only [norm, ← Rat.cast_abs, Rat.cast_le]⟩

中文:
实例 :
  签名: HasSolidNorm Rat
  定义体: ⟨fun _ _ _ => by simpa only [norm, ← Rat.cast_abs, Rat.cast_le]⟩

Depends on / 依赖: Rat.cast_abs, Rat.cast_le, cast_abs, cast_le
-/
instance : HasSolidNorm Rat := ⟨fun _ _ _ => by simpa only [norm, ← Rat.cast_abs, Rat.cast_le]⟩

/--
Instance `Int.hasSolidNorm` / 实例 `Int.hasSolidNorm`

English:
instance Int.hasSolidNorm
  signature: : HasSolidNorm Int where
  body: by simpa [← Int.norm_cast_real, ← Int.cast_abs] using h

中文:
实例 Int.hasSolidNorm
  签名: : HasSolidNorm 整数 where
  定义体: by simpa [← Int.norm_cast_real, ← Int.cast_abs] using h

Depends on / 依赖: Int.cast_abs, Int.norm_cast_real, cast_abs, norm_cast_real
-/
instance Int.hasSolidNorm : HasSolidNorm Int where
  solid x y h := by simpa [← Int.norm_cast_real, ← Int.cast_abs] using h

end SolidNorm

variable {α : Type*} [NormedAddCommGroup α] [Lattice α] [HasSolidNorm α] [IsOrderedAddMonoid α]

open HasSolidNorm

/--
theorem `dual_solid` / 定理 `dual_solid`

English:
theorem dual_solid
  given: (a b : α) (h : b ⊓ -b <= a ⊓ -a)
  statement: ‖a‖ <= ‖b‖
  proof: by
  apply solid
  rw [abs]
  nth_rw 1 [← neg_neg a]
  rw [← neg_inf]
  rw [abs]
  nth_rw 1 [← neg_neg b]
  rwa [← neg_inf, neg_le_neg_iff, inf_comm _ b, inf_comm _ a]

中文:
定理 dual_solid
  条件: (a b : α) (h : b ⊓ -b <= a ⊓ -a)
  结论: ‖a‖ <= ‖b‖
  证明: by
  apply solid
  rw [abs]
  nth_rw 1 [← neg_neg a]
  rw [← neg_inf]
  rw [abs]
  nth_rw 1 [← neg_neg b]
  rwa [← neg_inf, neg_le_neg_iff, inf_comm _ b, inf_comm _ a]

Depends on / 依赖: inf_comm, neg_inf, neg_le_neg_iff, neg_neg, nth_rw
-/
theorem dual_solid (a b : α) (h : b ⊓ -b <= a ⊓ -a) : ‖a‖ <= ‖b‖ := by
  apply solid
  rw [abs]
  nth_rw 1 [← neg_neg a]
  rw [← neg_inf]
  rw [abs]
  nth_rw 1 [← neg_neg b]
  rwa [← neg_inf, neg_le_neg_iff, inf_comm _ b, inf_comm _ a]

-- see Note [lower instance priority]
/-- Let `α` be a normed lattice ordered group, then the order dual is also a
normed lattice ordered group.
-/
instance (priority := 100) OrderDual.instHasSolidNorm :
    HasSolidNorm αᵒᵈ :=
  { solid := dual_solid (α := α) }

/--
theorem `norm_abs_eq_norm` / 定理 `norm_abs_eq_norm`

English:
theorem norm_abs_eq_norm
  given: (a : α)
  statement: ‖|a|‖ = ‖a‖
  proof: (solid (abs_abs a).le).antisymm (solid (abs_abs a).symm.le)

中文:
定理 norm_abs_eq_norm
  条件: (a : α)
  结论: ‖|a|‖ = ‖a‖
  证明: (solid (abs_abs a).le).antisymm (solid (abs_abs a).symm.le)

Depends on / 依赖: abs_abs, antisymm, symm.le
-/
theorem norm_abs_eq_norm (a : α) : ‖|a|‖ = ‖a‖ :=
  (solid (abs_abs a).le).antisymm (solid (abs_abs a).symm.le)

/--
theorem `norm_inf_sub_inf_le_add_norm` / 定理 `norm_inf_sub_inf_le_add_norm`

English:
theorem norm_inf_sub_inf_le_add_norm
  given: (a b c d : α)
  statement: ‖a ⊓ b - c ⊓ d‖ <= ‖a - c‖ + ‖b - d‖
  proof: by
  rw [← norm_abs_eq_norm (a - c)]; rw [← norm_abs_eq_norm (b - d)]
  refine le_trans (solid ?_) (norm_add_le |a - c| |b - d|)
  rw [abs_of_nonneg (add_nonneg (abs_nonneg (a - c)) (abs_nonneg (b - d)))]
  calc
    |a ⊓ b - c ⊓ d| = |a ⊓ b - c ⊓ b + (c ⊓ b - c ⊓ d)| := by rw [sub_add_sub_cancel]
  

中文:
定理 norm_inf_sub_inf_le_add_norm
  条件: (a b c d : α)
  结论: ‖a ⊓ b - c ⊓ d‖ <= ‖a - c‖ + ‖b - d‖
  证明: by
  rw [← norm_abs_eq_norm (a - c)]; rw [← norm_abs_eq_norm (b - d)]
  refine le_trans (solid ?_) (norm_add_le |a - c| |b - d|)
  rw [abs_of_nonneg (add_nonneg (abs_nonneg (a - c)) (abs_nonneg (b - d)))]
  calc
    |a ⊓ b - c ⊓ d| = |a ⊓ b - c ⊓ b + (c ⊓ b - c ⊓ d)| := by rw [sub_add_sub_cancel]
  

Depends on / 依赖: abs_add_le, abs_inf_sub_inf_le_abs, abs_nonneg, abs_of_nonneg, add_nonneg, inf_comm, le_trans, norm_abs_eq_norm, norm_add_le, sub_add_sub_cancel
-/
theorem norm_inf_sub_inf_le_add_norm (a b c d : α) : ‖a ⊓ b - c ⊓ d‖ <= ‖a - c‖ + ‖b - d‖ := by
  rw [← norm_abs_eq_norm (a - c)]; rw [← norm_abs_eq_norm (b - d)]
  refine le_trans (solid ?_) (norm_add_le |a - c| |b - d|)
  rw [abs_of_nonneg (add_nonneg (abs_nonneg (a - c)) (abs_nonneg (b - d)))]
  calc
    |a ⊓ b - c ⊓ d| = |a ⊓ b - c ⊓ b + (c ⊓ b - c ⊓ d)| := by rw [sub_add_sub_cancel]
    _ <= |a ⊓ b - c ⊓ b| + |c ⊓ b - c ⊓ d| := abs_add_le _ _
    _ <= |a - c| + |b - d| := by
      gcongr ?_ + ?_
      · exact abs_inf_sub_inf_le_abs _ _ _
      · rw [inf_comm c, inf_comm c]
        exact abs_inf_sub_inf_le_abs _ _ _

/--
theorem `norm_sup_sub_sup_le_add_norm` / 定理 `norm_sup_sub_sup_le_add_norm`

English:
theorem norm_sup_sub_sup_le_add_norm
  given: (a b c d : α)
  statement: ‖a ⊔ b - c ⊔ d‖ <= ‖a - c‖ + ‖b - d‖
  proof: by
  rw [← norm_abs_eq_norm (a - c)]; rw [← norm_abs_eq_norm (b - d)]
  refine le_trans (solid ?_) (norm_add_le |a - c| |b - d|)
  rw [abs_of_nonneg (add_nonneg (abs_nonneg (a - c)) (abs_nonneg (b - d)))]
  calc
    |a ⊔ b - c ⊔ d| = |a ⊔ b - c ⊔ b + (c ⊔ b - c ⊔ d)| := by rw [sub_add_sub_cancel]
  

中文:
定理 norm_sup_sub_sup_le_add_norm
  条件: (a b c d : α)
  结论: ‖a ⊔ b - c ⊔ d‖ <= ‖a - c‖ + ‖b - d‖
  证明: by
  rw [← norm_abs_eq_norm (a - c)]; rw [← norm_abs_eq_norm (b - d)]
  refine le_trans (solid ?_) (norm_add_le |a - c| |b - d|)
  rw [abs_of_nonneg (add_nonneg (abs_nonneg (a - c)) (abs_nonneg (b - d)))]
  calc
    |a ⊔ b - c ⊔ d| = |a ⊔ b - c ⊔ b + (c ⊔ b - c ⊔ d)| := by rw [sub_add_sub_cancel]
  

Depends on / 依赖: abs_add_le, abs_nonneg, abs_of_nonneg, abs_sup_sub_sup_le_abs, add_nonneg, le_trans, norm_abs_eq_norm, norm_add_le, sub_add_sub_cancel, sup_comm
-/
theorem norm_sup_sub_sup_le_add_norm (a b c d : α) : ‖a ⊔ b - c ⊔ d‖ <= ‖a - c‖ + ‖b - d‖ := by
  rw [← norm_abs_eq_norm (a - c)]; rw [← norm_abs_eq_norm (b - d)]
  refine le_trans (solid ?_) (norm_add_le |a - c| |b - d|)
  rw [abs_of_nonneg (add_nonneg (abs_nonneg (a - c)) (abs_nonneg (b - d)))]
  calc
    |a ⊔ b - c ⊔ d| = |a ⊔ b - c ⊔ b + (c ⊔ b - c ⊔ d)| := by rw [sub_add_sub_cancel]
    _ <= |a ⊔ b - c ⊔ b| + |c ⊔ b - c ⊔ d| := abs_add_le _ _
    _ <= |a - c| + |b - d| := by
      gcongr ?_ + ?_
      · exact abs_sup_sub_sup_le_abs _ _ _
      · rw [sup_comm c, sup_comm c]
        exact abs_sup_sub_sup_le_abs _ _ _

/--
theorem `norm_inf_le_add` / 定理 `norm_inf_le_add`

English:
theorem norm_inf_le_add
  given: (x y : α)
  statement: ‖x ⊓ y‖ <= ‖x‖ + ‖y‖
  proof: by
  have h : ‖x ⊓ y - 0 ⊓ 0‖ <= ‖x - 0‖ + ‖y - 0‖ := norm_inf_sub_inf_le_add_norm x y 0 0
  simpa only [inf_idem, sub_zero] using h

中文:
定理 norm_inf_le_add
  条件: (x y : α)
  结论: ‖x ⊓ y‖ <= ‖x‖ + ‖y‖
  证明: by
  have h : ‖x ⊓ y - 0 ⊓ 0‖ <= ‖x - 0‖ + ‖y - 0‖ := norm_inf_sub_inf_le_add_norm x y 0 0
  simpa only [inf_idem, sub_zero] using h

Depends on / 依赖: inf_idem, norm_inf_sub_inf_le_add_norm, sub_zero
-/
theorem norm_inf_le_add (x y : α) : ‖x ⊓ y‖ <= ‖x‖ + ‖y‖ := by
  have h : ‖x ⊓ y - 0 ⊓ 0‖ <= ‖x - 0‖ + ‖y - 0‖ := norm_inf_sub_inf_le_add_norm x y 0 0
  simpa only [inf_idem, sub_zero] using h

/--
theorem `norm_sup_le_add` / 定理 `norm_sup_le_add`

English:
theorem norm_sup_le_add
  given: (x y : α)
  statement: ‖x ⊔ y‖ <= ‖x‖ + ‖y‖
  proof: by
  have h : ‖x ⊔ y - 0 ⊔ 0‖ <= ‖x - 0‖ + ‖y - 0‖ := norm_sup_sub_sup_le_add_norm x y 0 0
  simpa only [sup_idem, sub_zero] using h

中文:
定理 norm_sup_le_add
  条件: (x y : α)
  结论: ‖x ⊔ y‖ <= ‖x‖ + ‖y‖
  证明: by
  have h : ‖x ⊔ y - 0 ⊔ 0‖ <= ‖x - 0‖ + ‖y - 0‖ := norm_sup_sub_sup_le_add_norm x y 0 0
  simpa only [sup_idem, sub_zero] using h

Depends on / 依赖: norm_sup_sub_sup_le_add_norm, sub_zero, sup_idem
-/
theorem norm_sup_le_add (x y : α) : ‖x ⊔ y‖ <= ‖x‖ + ‖y‖ := by
  have h : ‖x ⊔ y - 0 ⊔ 0‖ <= ‖x - 0‖ + ‖y - 0‖ := norm_sup_sub_sup_le_add_norm x y 0 0
  simpa only [sup_idem, sub_zero] using h

-- see Note [lower instance priority]
/-- Let `α` be a normed lattice ordered group. Then the infimum is jointly continuous.
-/
instance (priority := 100) HasSolidNorm.continuousInf : ContinuousInf α := by
refine ⟨continuous_iff_continuousAt.2 fun q => tendsto_iff_norm_sub_tendsto_zero.2 ?_⟩
  have : forall p : α × α, ‖p.1 ⊓ p.2 - q.1 ⊓ q.2‖ <= ‖p.1 - q.1‖ + ‖p.2 - q.2‖ := fun _ =>
    norm_inf_sub_inf_le_add_norm _ _ _ _
  refine squeeze_zero (fun e => norm_nonneg _) this ?_
  convert!
    ((continuous_fst.tendsto q).sub <| tendsto_const_nhds).norm.add
      ((continuous_snd.tendsto q).sub <| tendsto_const_nhds).norm
  simp

-- see Note [lower instance priority]
instance (priority := 100) HasSolidNorm.continuousSup {α : Type*}
    [NormedAddCommGroup α] [Lattice α] [HasSolidNorm α] [IsOrderedAddMonoid α] : ContinuousSup α :=
  OrderDual.continuousSup αᵒᵈ

-- see Note [lower instance priority]
/--
Let `α` be a normed lattice ordered group. Then `α` is a topological lattice in the norm topology.
-/
instance (priority := 100) HasSolidNorm.toTopologicalLattice : TopologicalLattice α :=
  TopologicalLattice.mk

/--
theorem `norm_abs_sub_abs` / 定理 `norm_abs_sub_abs`

English:
theorem norm_abs_sub_abs
  given: (a b : α)
  statement: ‖|a| - |b|‖ <= ‖a - b‖
  proof: solid (abs_abs_sub_abs_le _ _)

中文:
定理 norm_abs_sub_abs
  条件: (a b : α)
  结论: ‖|a| - |b|‖ <= ‖a - b‖
  证明: solid (abs_abs_sub_abs_le _ _)

Depends on / 依赖: abs_abs_sub_abs_le
-/
theorem norm_abs_sub_abs (a b : α) : ‖|a| - |b|‖ <= ‖a - b‖ := solid (abs_abs_sub_abs_le _ _)

/--
theorem `norm_sup_sub_sup_le_norm` / 定理 `norm_sup_sub_sup_le_norm`

English:
theorem norm_sup_sub_sup_le_norm
  given: (x y z : α)
  statement: ‖x ⊔ z - y ⊔ z‖ <= ‖x - y‖
  proof: solid (abs_sup_sub_sup_le_abs x y z)

中文:
定理 norm_sup_sub_sup_le_norm
  条件: (x y z : α)
  结论: ‖x ⊔ z - y ⊔ z‖ <= ‖x - y‖
  证明: solid (abs_sup_sub_sup_le_abs x y z)

Depends on / 依赖: abs_sup_sub_sup_le_abs
-/
theorem norm_sup_sub_sup_le_norm (x y z : α) : ‖x ⊔ z - y ⊔ z‖ <= ‖x - y‖ :=
  solid (abs_sup_sub_sup_le_abs x y z)

/--
theorem `norm_inf_sub_inf_le_norm` / 定理 `norm_inf_sub_inf_le_norm`

English:
theorem norm_inf_sub_inf_le_norm
  given: (x y z : α)
  statement: ‖x ⊓ z - y ⊓ z‖ <= ‖x - y‖
  proof: solid (abs_inf_sub_inf_le_abs x y z)

中文:
定理 norm_inf_sub_inf_le_norm
  条件: (x y z : α)
  结论: ‖x ⊓ z - y ⊓ z‖ <= ‖x - y‖
  证明: solid (abs_inf_sub_inf_le_abs x y z)

Depends on / 依赖: abs_inf_sub_inf_le_abs
-/
theorem norm_inf_sub_inf_le_norm (x y z : α) : ‖x ⊓ z - y ⊓ z‖ <= ‖x - y‖ :=
  solid (abs_inf_sub_inf_le_abs x y z)

/--
theorem `lipschitzWith_sup_right` / 定理 `lipschitzWith_sup_right`

English:
theorem lipschitzWith_sup_right
  given: (z : α)
  statement: LipschitzWith 1 fun x => x ⊔ z
  proof: LipschitzWith.of_dist_le_mul fun x y => by
    rw [NNReal.coe_one]; rw [one_mul]; rw [dist_eq_norm]; rw [dist_eq_norm]
    exact norm_sup_sub_sup_le_norm x y z

中文:
定理 lipschitzWith_sup_right
  条件: (z : α)
  结论: LipschitzWith 1 fun x => x ⊔ z
  证明: LipschitzWith.of_dist_le_mul fun x y => by
    rw [NNReal.coe_one]; rw [one_mul]; rw [dist_eq_norm]; rw [dist_eq_norm]
    exact norm_sup_sub_sup_le_norm x y z

Depends on / 依赖: LipschitzWith, LipschitzWith.of_dist_le_mul, NNReal, NNReal.coe_one, coe_one, dist_eq_norm, norm_sup_sub_sup_le_norm, of_dist_le_mul, one_mul
-/
theorem lipschitzWith_sup_right (z : α) : LipschitzWith 1 fun x => x ⊔ z :=
  LipschitzWith.of_dist_le_mul fun x y => by
    rw [NNReal.coe_one]; rw [one_mul]; rw [dist_eq_norm]; rw [dist_eq_norm]
    exact norm_sup_sub_sup_le_norm x y z

/--
lemma `lipschitzWith_posPart` / 引理 `lipschitzWith_posPart`

English:
lemma lipschitzWith_posPart
  statement: LipschitzWith 1 (posPart : α -> α)
  proof: lipschitzWith_sup_right 0

中文:
引理 lipschitzWith_posPart
  结论: LipschitzWith 1 (posPart : α -> α)
  证明: lipschitzWith_sup_right 0

Depends on / 依赖: lipschitzWith_sup_right
-/
lemma lipschitzWith_posPart : LipschitzWith 1 (posPart : α -> α) :=
  lipschitzWith_sup_right 0

/--
lemma `lipschitzWith_negPart` / 引理 `lipschitzWith_negPart`

English:
lemma lipschitzWith_negPart
  statement: LipschitzWith 1 (negPart : α -> α)
  proof: by
  simpa [Function.comp] using! lipschitzWith_posPart.comp LipschitzWith.id.neg

@[fun_prop]

中文:
引理 lipschitzWith_negPart
  结论: LipschitzWith 1 (negPart : α -> α)
  证明: by
  simpa [Function.comp] using! lipschitzWith_posPart.comp LipschitzWith.id.neg

@[fun_prop]

Depends on / 依赖: Function, Function.comp, LipschitzWith, LipschitzWith.id.neg, lipschitzWith_posPart, lipschitzWith_posPart.comp
-/
lemma lipschitzWith_negPart : LipschitzWith 1 (negPart : α -> α) := by
  simpa [Function.comp] using! lipschitzWith_posPart.comp LipschitzWith.id.neg

@[fun_prop]
/--
lemma `continuous_posPart` / 引理 `continuous_posPart`

English:
lemma continuous_posPart
  statement: Continuous (posPart : α -> α)
  proof: lipschitzWith_posPart.continuous

@[fun_prop]

中文:
引理 continuous_posPart
  结论: Continuous (posPart : α -> α)
  证明: lipschitzWith_posPart.continuous

@[fun_prop]

Depends on / 依赖: continuous, lipschitzWith_posPart, lipschitzWith_posPart.continuous
-/
lemma continuous_posPart : Continuous (posPart : α -> α) := lipschitzWith_posPart.continuous

@[fun_prop]
/--
lemma `continuous_negPart` / 引理 `continuous_negPart`

English:
lemma continuous_negPart
  statement: Continuous (negPart : α -> α)
  proof: lipschitzWith_negPart.continuous

中文:
引理 continuous_negPart
  结论: Continuous (negPart : α -> α)
  证明: lipschitzWith_negPart.continuous

Depends on / 依赖: continuous, lipschitzWith_negPart, lipschitzWith_negPart.continuous
-/
lemma continuous_negPart : Continuous (negPart : α -> α) := lipschitzWith_negPart.continuous

/--
lemma `isClosed_nonneg` / 引理 `isClosed_nonneg`

English:
lemma isClosed_nonneg
  statement: IsClosed {x : α | 0 <= x}
  proof: by
  have : {x : α | 0 <= x} = negPart ⁻¹' {0} := by ext; simp [negPart_eq_zero]
  rw [this]
  exact isClosed_singleton.preimage continuous_negPart

中文:
引理 isClosed_nonneg
  结论: IsClosed {x : α | 0 <= x}
  证明: by
  have : {x : α | 0 <= x} = negPart ⁻¹' {0} := by ext; simp [negPart_eq_zero]
  rw [this]
  exact isClosed_singleton.preimage continuous_negPart

Depends on / 依赖: continuous_negPart, isClosed_singleton, isClosed_singleton.preimage, negPart, negPart_eq_zero, preimage
-/
lemma isClosed_nonneg : IsClosed {x : α | 0 <= x} := by
  have : {x : α | 0 <= x} = negPart ⁻¹' {0} := by ext; simp [negPart_eq_zero]
  rw [this]
  exact isClosed_singleton.preimage continuous_negPart

/--
theorem `isClosed_le_of_isClosed_nonneg` / 定理 `isClosed_le_of_isClosed_nonneg`

English:
theorem isClosed_le_of_isClosed_nonneg
  statement: {G}
  proof: by
  have : { p : G × G | p.fst <= p.snd } = (fun p : G × G => p.snd - p.fst) ⁻¹' { x : G | 0 <= x } := by
    ext1 p; simp only [sub_nonneg, Set.preimage_ofPred_eq]
  rw [this]
  exact IsClosed.preimage (continuous_snd.sub continuous_fst) h

中文:
定理 isClosed_le_of_isClosed_nonneg
  结论: {G}
  证明: by
  have : { p : G × G | p.fst <= p.snd } = (fun p : G × G => p.snd - p.fst) ⁻¹' { x : G | 0 <= x } := by
    ext1 p; simp only [sub_nonneg, Set.preimage_ofPred_eq]
  rw [this]
  exact IsClosed.preimage (continuous_snd.sub continuous_fst) h

Depends on / 依赖: IsClosed, IsClosed.preimage, Set.preimage_ofPred_eq, continuous_fst, continuous_snd, continuous_snd.sub, p.fst, p.snd, preimage, preimage_ofPred_eq, sub_nonneg
-/
theorem isClosed_le_of_isClosed_nonneg {G}
    [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G] [TopologicalSpace G]
    [ContinuousSub G] (h : IsClosed { x : G | 0 <= x }) :
    IsClosed { p : G × G | p.fst <= p.snd } := by
  have : { p : G × G | p.fst <= p.snd } = (fun p : G × G => p.snd - p.fst) ⁻¹' { x : G | 0 <= x } := by
    ext1 p; simp only [sub_nonneg, Set.preimage_ofPred_eq]
  rw [this]
  exact IsClosed.preimage (continuous_snd.sub continuous_fst) h

-- See note [lower instance priority]
instance (priority := 100) HasSolidNorm.orderClosedTopology {E}
    [NormedAddCommGroup E] [Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E] :
    OrderClosedTopology E :=
  ⟨isClosed_le_of_isClosed_nonneg isClosed_nonneg⟩
