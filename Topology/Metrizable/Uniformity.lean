/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.NNReal.Basic
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.Metrizable.Basic

/-!
# Metrizable uniform spaces

In this file we prove that a uniform space with countably generated uniformity filter is
pseudometrizable: there exists a `PseudoMetricSpace` structure that generates the same uniformity.
The proof follows [Sergey Melikhov, Metrizable uniform spaces][melikhov2011].

## Main definitions

* `PseudoMetricSpace.ofPreNNDist`: given a function `d : X → X → ℝ≥0` such that `d x x = 0` and
  `d x y = d y x` for all `x y : X`, constructs the maximal pseudometric space structure such that
  `NNDist x y ≤ d x y` for all `x y : X`.

* `UniformSpace.pseudoMetricSpace`: given a uniform space `X` with countably generated `𝓤 X`,
  constructs a `PseudoMetricSpace X` instance that is compatible with the uniform space structure.

* `UniformSpace.metricSpace`: given a T₀ uniform space `X` with countably generated `𝓤 X`,
  constructs a `MetricSpace X` instance that is compatible with the uniform space structure.

## Main statements

* `UniformSpace.metrizable_uniformity`: if `X` is a uniform space with countably generated `𝓤 X`,
  then there exists a `PseudoMetricSpace` structure that is compatible with this `UniformSpace`
  structure. Use `UniformSpace.pseudoMetricSpace` or `UniformSpace.metricSpace` instead.

* `UniformSpace.pseudoMetrizableSpace`: a uniform space with countably generated `𝓤 X` is
  pseudometrizable.

* `UniformSpace.metrizableSpace`: a T₀ uniform space with countably generated `𝓤 X` is
  metrizable. This is not an instance to avoid loops.

## Tags

metrizable space, uniform space
-/

@[expose] public section


open Set Function Metric List Filter
open scoped NNReal SetRel Uniformity

variable {X : Type*}

namespace PseudoMetricSpace

/-- The maximal pseudometric space structure on `X` such that `dist x y ≤ d x y` for all `x y`,
where `d : X → X → ℝ≥0` is a function such that `d x x = 0` and `d x y = d y x` for all `x`, `y`. -/
@[instance_reducible]
/-
**PseudoMetricSpace.ofPreNNDist** 是 Mathlib 中的一个定义，位于命名空间 `PseudoMetricSpace`。
形式化陈述：ofPreNNDist (d : X -> X -> Real>=0) (dist_self : forall x, d x x = 0) (dis
t_comm : forall x y, d x y = d y x) : PseudoMetricSpace X where dist x y
参数：d : X -> X -> Real>=0；dist_self : forall x, d x x = 0；dist_comm : forall x y,
 d x y = d y x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The maximal pseudometric space structure on `X` such that `dist x y ≤ d x y` for
 all `x y`,
where `d : X → X → ℝ≥0` is a function such that `d x x = 0` and `d x y = d y x` 
for all `x`, `y`.
-/
noncomputable def ofPreNNDist (d : X → X → ℝ≥0) (dist_self : ∀ x, d x x = 0)
    (dist_comm : ∀ x y, d x y = d y x) : PseudoMetricSpace X where
  dist x y := ↑(⨅ l : List X, ((x::l).zipWith d (l ++ [y])).sum : ℝ≥0)
  dist_self x := NNReal.coe_eq_zero.2 <|
      nonpos_iff_eq_zero.1 <| (ciInf_le (OrderBot.bddBelow _) []).trans_eq <| by simp [dist_self]
  dist_comm x y :=
    NNReal.coe_inj.2 <| by
      refine reverse_surjective.iInf_congr _ fun l ↦ ?_
      rw [← sum_reverse, reverse_zipWith, reverse_append, reverse_reverse,
        reverse_singleton, singleton_append, reverse_cons, reverse_reverse,
        zipWith_comm_of_comm dist_comm]
      simp only [length, length_append]
  dist_triangle x y z := by
    rw [← NNReal.coe_add, NNReal.coe_le_coe]
    refine NNReal.le_iInf_add_iInf fun lxy lyz ↦ ?_
    calc
      ⨅ l, (zipWith d (x::l) (l ++ [z])).sum ≤
          (zipWith d (x::lxy ++ y::lyz) ((lxy ++ y::lyz) ++ [z])).sum :=
        ciInf_le (OrderBot.bddBelow _) (lxy ++ y::lyz)
      _ = (zipWith d (x::lxy) (lxy ++ [y])).sum + (zipWith d (y::lyz) (lyz ++ [z])).sum := by
        rw [← sum_append, ← zipWith_append, cons_append, ← @singleton_append _ y, append_assoc,
          append_assoc, append_assoc]
        rw [length_cons, length_append, length_singleton]
/-
**PseudoMetricSpace.dist_ofPreNNDist** 是 Mathlib 中的一个定理，位于命名空间 `PseudoMetricSpac
e`。
形式化陈述：dist_ofPreNNDist (d : X -> X -> Real>=0) (dist_self : forall x, d x x = 0)
 (dist_comm : forall x y, d x y = d y x) (x y : X) : @dist X (@PseudoMetricSpace
.toDist X (PseudoMetricSpace.ofPreNNDist d dist_self dist_comm)) x y = ↑(⨅ l : L
ist X, ((x::l).zipWith d (l ++ [y])).sum : Real>=0)
参数：d : X -> X -> Real>=0；dist_self : forall x, d x x = 0；dist_comm : forall x y,
 d x y = d y x；x y : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dist_ofPreNNDist (d : X → X → ℝ≥0) (dist_self : ∀ x, d x x = 0)
    (dist_comm : ∀ x y, d x y = d y x) (x y : X) :
    @dist X (@PseudoMetricSpace.toDist X (PseudoMetricSpace.ofPreNNDist d dist_self dist_comm)) x
        y =
      ↑(⨅ l : List X, ((x::l).zipWith d (l ++ [y])).sum : ℝ≥0) :=
  rfl
/-
**PseudoMetricSpace.dist_ofPreNNDist_le** 是 Mathlib 中的一个定理，位于命名空间 `PseudoMetricS
pace`。
形式化陈述：dist_ofPreNNDist_le (d : X -> X -> Real>=0) (dist_self : forall x, d x x =
 0) (dist_comm : forall x y, d x y = d y x) (x y : X) : @dist X (@PseudoMetricSp
ace.toDist X (PseudoMetricSpace.ofPreNNDist d dist_self dist_comm)) x y <= d x y
参数：d : X -> X -> Real>=0；dist_self : forall x, d x x = 0；dist_comm : forall x y,
 d x y = d y x；x y : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `ciInf_le`：ciInf_le {f : ι -> α} (H : BddBelow (range f)) (c : ι) : iInf 
f <= f c
· 使用定理 `OrderBot.bddBelow`：∀ {α : Type u_1} [inst : Preorder α] [OrderBot α] (s 
: Set α), BddBelow s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.zipWith_self`：∀ {α : Type u_1} {δ : Type u_2} {f : α → α → δ} {l : 
List α}, List.zipWith f l l = List.map (fun a => f a a) l
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dist_ofPreNNDist_le (d : X → X → ℝ≥0) (dist_self : ∀ x, d x x = 0)
    (dist_comm : ∀ x y, d x y = d y x) (x y : X) :
    @dist X (@PseudoMetricSpace.toDist X (PseudoMetricSpace.ofPreNNDist d dist_self dist_comm)) x
        y ≤
      d x y :=
  NNReal.coe_le_coe.2 <| (ciInf_le (OrderBot.bddBelow _) []).trans_eq <| by simp

/-- Consider a function `d : X → X → ℝ≥0` such that `d x x = 0` and `d x y = d y x` for all `x`,
`y`. Let `dist` be the largest pseudometric distance such that `dist x y ≤ d x y`, see
`PseudoMetricSpace.ofPreNNDist`. Suppose that `d` satisfies the following triangle-like
inequality: `d x₁ x₄ ≤ 2 * max (d x₁ x₂, d x₂ x₃, d x₃ x₄)`. Then `d x y ≤ 2 * dist x y` for all
`x`, `y`. -/
/-
**PseudoMetricSpace.le_two_mul_dist_ofPreNNDist** 是 Mathlib 中的一个定理，位于命名空间 `Pseud
oMetricSpace`。
形式化陈述：le_two_mul_dist_ofPreNNDist (d : X -> X -> Real>=0) (dist_self : forall x,
 d x x = 0) (dist_comm : forall x y, d x y = d y x) (hd : forall x₁ x₂ x₃ x₄, d 
x₁ x₄ <= 2 * max (d x₁ x₂) (max (d x₂ x₃) (d x₃ x₄))) (x y : X) : ↑(d x y) <= 2 
* @dist X (@PseudoMetricSpace.toDist X (PseudoMetricSpace.ofPreNNDist d dist_sel
f dist_comm)) x y
参数：d : X -> X -> Real>=0；dist_self : forall x, d x x = 0；dist_comm : forall x y,
 d x y = d y x；hd : forall x₁ x₂ x₃ x₄, d x₁ x₄ <= 2 * max (d x₁ x₂) (max (d x₂ 
x₃) (d x₃ x₄))；x y : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PseudoMetricSpace.dist_ofPreNNDist`：dist_ofPreNNDist (d : X -> X -> Real
>=0) (dist_self : forall x, d x x = 0) (dist_comm : forall x y, d x y = d y x) (
x y : X) : @dist X (@Pse…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_two`：↑2 = 2
· 使用定理 `NNReal.coe_mul`：∀ (r₁ r₂ : NNReal), ↑(r₁ * r₂) = ↑r₁ * ↑r₂
· 使用定理 `NNReal.mul_iInf`：mul_iInf (f : ι -> Real>=0) (a : Real>=0) : a * iInf f 
= ⨅ i, a * f i
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
· 使用定理 `le_ciInf`：le_ciInf [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, c <=
 f x) : c <= iInf f
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `max_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), max a a = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.length_zipWith`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β → γ} {l₁ : List α} {l₂ : List β},   (List.zipWith f l₁ l₂).length = min l
₁.length …
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `min_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), min a a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Nat.lt_iff_add_one_le`：∀ {m n : ℕ}, m < n ↔ m + 1 ≤ n
· 使用定理 `List.IsChain.rel_cons`：∀ {α : Type u_1} {R : α → α → Prop} {l : List α} 
{a b : α} [Trans R R R], List.IsChain R (a :: l) → b ∈ l → R a b
· 使用定理 `List.isChain_cons_append_singleton_iff_forall₂`：isChain_cons_append_sing
leton_iff_forall₂ : IsChain R (a :: l ++ [b]) ↔ Forall₂ R (a :: l) (l ++ [b])
（共 100 条，此处仅展示前 30 条）

--- 原说明 ---
Consider a function `d : X → X → ℝ≥0` such that `d x x = 0` and `d x y = d y x` 
for all `x`,
`y`. Let `dist` be the largest pseudometric distance such that `dist x y ≤ d x y
`, see
`PseudoMetricSpace.ofPreNNDist`. Suppose that `d` satisfies the following triang
le-like
inequality: `d x₁ x₄ ≤ 2 * max (d x₁ x₂, d x₂ x₃, d x₃ x₄)`. Then `d x y ≤ 2 * d
ist x y` for all
`x`, `y`.
-/
theorem le_two_mul_dist_ofPreNNDist (d : X → X → ℝ≥0) (dist_self : ∀ x, d x x = 0)
    (dist_comm : ∀ x y, d x y = d y x)
    (hd : ∀ x₁ x₂ x₃ x₄, d x₁ x₄ ≤ 2 * max (d x₁ x₂) (max (d x₂ x₃) (d x₃ x₄))) (x y : X) :
    ↑(d x y) ≤ 2 * @dist X
      (@PseudoMetricSpace.toDist X (PseudoMetricSpace.ofPreNNDist d dist_self dist_comm)) x y := by
  /- We need to show that `d x y` is at most twice the sum `L` of `d xᵢ xᵢ₊₁` over a path
    `x₀=x, ..., xₙ=y`. We prove it by induction on the length `n` of the sequence. Find an edge that
    splits the path into two parts of almost equal length: both `d x₀ x₁ + ... + d xₖ₋₁ xₖ` and
    `d xₖ₊₁ xₖ₊₂ + ... + d xₙ₋₁ xₙ` are less than or equal to `L / 2`.
    Then `d x₀ xₖ ≤ L`, `d xₖ xₖ₊₁ ≤ L`, and `d xₖ₊₁ xₙ ≤ L`, thus `d x₀ xₙ ≤ 2 * L`. -/
  rw [dist_ofPreNNDist, ← NNReal.coe_two, ← NNReal.coe_mul, NNReal.mul_iInf, NNReal.coe_le_coe]
  refine le_ciInf fun l => ?_
  have : IsTrans X fun x y => d x y = 0 := by
    refine ⟨fun a b c hab hbc ↦ ?_⟩
    rw [← nonpos_iff_eq_zero]
    simpa only [nonpos_iff_eq_zero, hab, hbc, dist_self c, max_self, mul_zero] using hd a b c c
  suffices ∀ n, length l = n → d x y ≤ 2 * (zipWith d (x :: l) (l ++ [y])).sum by exact this _ rfl
  intro n hn
  induction n using Nat.strong_induction_on generalizing x y l with | h n ihn =>
  subst n
  set L := zipWith d (x::l) (l ++ [y])
  have hL_len : length L = length l + 1 := by simp [L]
  rcases eq_or_ne (d x y) 0 with hd₀ | hd₀
  · simp only [hd₀, zero_le]
  rsuffices ⟨z, z', hxz, hzz', hz'y⟩ : ∃ z z' : X, d x z ≤ L.sum ∧ d z z' ≤ L.sum ∧ d z' y ≤ L.sum
  · grw [hd x z z' y, max_le hxz (max_le hzz' hz'y)]
  set s : Set ℕ := { m : ℕ | 2 * (take m L).sum ≤ L.sum }
  have hs₀ : 0 ∈ s := by simp [s]
  have hsne : s.Nonempty := ⟨0, hs₀⟩
  obtain ⟨M, hMl, hMs⟩ : ∃ M ≤ length l, IsGreatest s M := by
    have hs_ub : length l ∈ upperBounds s := by
      intro m hm
      rw [← not_lt, Nat.lt_iff_add_one_le, ← hL_len]
      intro hLm
      rw [mem_ofPred_eq, take_of_length_le hLm, two_mul, add_le_iff_nonpos_left, nonpos_iff_eq_zero,
          sum_eq_zero_iff, ← forall_iff_forall_mem, forall_zipWith,
          ← isChain_cons_append_singleton_iff_forall₂]
          at hm <;>
        [skip; simp]
      exact hd₀ (hm.rel_cons (mem_append.2 <| Or.inr <| mem_singleton_self _))
    have hs_bdd : BddAbove s := ⟨length l, hs_ub⟩
    exact ⟨sSup s, csSup_le hsne hs_ub, ⟨Nat.sSup_mem hsne hs_bdd, fun k => le_csSup hs_bdd⟩⟩
  have hM_lt : M < length L := by rwa [hL_len, Nat.lt_succ_iff]
  have hM_ltx : M < length (x::l) := lt_length_left_of_zipWith hM_lt
  have hM_lty : M < length (l ++ [y]) := lt_length_right_of_zipWith hM_lt
  refine ⟨(x::l)[M], (l ++ [y])[M], ?_, ?_, ?_⟩
  · cases M with
    | zero =>
      simp [dist_self]
    | succ M =>
      rw [Nat.succ_le_iff] at hMl
      have hMl' : length (take M l) = M := length_take.trans (min_eq_left hMl.le)
      refine (ihn _ hMl _ _ _ hMl').trans ?_
      convert! hMs.1.out
      rw [take_zipWith, take, take_add_one, getElem?_append_left hMl, getElem?_eq_getElem hMl,
        ← Option.coe_def, Option.toList_some, take_append_of_le_length hMl.le, getElem_cons_succ]
  · exact single_le_sum (fun x _ => zero_le) _ (mem_iff_get.2 ⟨⟨M, hM_lt⟩, getElem_zipWith⟩)
  · rcases hMl.eq_or_lt with (rfl | hMl)
    · simp only [getElem_append_right le_rfl, getElem_singleton, dist_self, zero_le]
    rw [getElem_append_left hMl]
    have hlen : length (drop (M + 1) l) = length l - (M + 1) := length_drop
    have hlen_lt : length l - (M + 1) < length l := Nat.sub_lt_of_pos_le M.succ_pos hMl
    refine (ihn _ hlen_lt _ y _ hlen).trans ?_
    rw [cons_getElem_drop_succ]
    have hMs' : L.sum ≤ 2 * (L.take (M + 1)).sum :=
      not_lt.1 fun h => (hMs.2 h.le).not_gt M.lt_succ_self
    rw [← sum_take_add_sum_drop L (M + 1), two_mul, add_le_add_iff_left, ← add_le_add_iff_right,
      sum_take_add_sum_drop, ← two_mul] at hMs'
    convert! hMs'
    rwa [drop_zipWith, drop, drop_append_of_le_length]

end PseudoMetricSpace

/-- If `X` is a uniform space with countably generated uniformity filter, there exists a
`PseudoMetricSpace` structure compatible with the `UniformSpace` structure. Use
`UniformSpace.pseudoMetricSpace` or `UniformSpace.metricSpace` instead. -/
/-
**UniformSpace.metrizable_uniformity** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace`。
形式化陈述：∀ (X : Type u_2) [inst : UniformSpace X] [(uniformity X).IsCountablyGenera
ted],   ∃ I, PseudoMetricSpace.toUniformSpace = inst
参数：X : Type u_2；uniformity X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.has_seq_basis`：UniformSpace.has_seq_basis [IsCountablyGener
ated <| 𝓤 α] : exists V : Nat -> SetRel α α, HasAntitoneBasis (𝓤 α) V ∧ forall n
, SetRel.IsSymm …
· 使用定理 `Filter.HasAntitoneBasis.subbasis_with_rel`：∀ {α : Type u_3} {f : Filter 
α} {s : ℕ → Set α},   f.HasAntitoneBasis s →     ∀ {r : ℕ → ℕ → Prop},       (∀ 
(m : ℕ), ∀ᶠ (n : ℕ) in Filter.a…
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.HasAntitoneBasis.tendsto_smallSets`：∀ {α : Type u_1} {l : Filter 
α} {ι : Type u_4} [inst : Preorder ι] {s : ι → Set α},   l.HasAntitoneBasis s → 
Filter.Tendsto s Filter.atTop l…
· 使用定理 `eventually_uniformity_iterate_comp_subset`：eventually_uniformity_iterate
_comp_subset {s : SetRel α α} (hs : s in 𝓤 α) (n : Nat) : forallᶠ t in (𝓤 α).sma
llSets, (t ○ ·)^[n] t subseteq …
· 使用定理 `Filter.HasAntitoneBasis.mem`：∀ {α : Type u_1} {ι : Type u_4} [inst : Pre
order ι] {l : Filter α} {s : ι → Set α},   l.HasAntitoneBasis s → ∀ (i : ι), s i
 ∈ l
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NNReal.instNoZeroDivisors`：NoZeroDivisors NNReal
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Filter.HasBasis.inseparable_iff_uniformity`：Filter.HasBasis.inseparable_
iff_uniformity {ι : Sort*} {p : ι -> Prop} {s : ι -> Set (α × α)} (h : (𝓤 α).Has
Basis p s) {x y : α} : Inseparab…
（共 97 条，此处仅展示前 30 条）

--- 原说明 ---
If `X` is a uniform space with countably generated uniformity filter, there exis
ts a
`PseudoMetricSpace` structure compatible with the `UniformSpace` structure. Use
`UniformSpace.pseudoMetricSpace` or `UniformSpace.metricSpace` instead.
-/
protected theorem UniformSpace.metrizable_uniformity (X : Type*) [UniformSpace X]
    [IsCountablyGenerated (𝓤 X)] : ∃ I : PseudoMetricSpace X, I.toUniformSpace = ‹_› := by
  classical
  /- Choose a fast decreasing antitone basis `U : ℕ → SetRel X X` of the uniformity filter `𝓤 X`.
    Define `d x y : ℝ≥0` to be `(1 / 2) ^ n`, where `n` is the minimal index of `U n` that
    separates `x` and `y`: `(x, y) ∉ U n`, or `0` if `x` is not separated from `y`. This function
    satisfies the assumptions of `PseudoMetricSpace.ofPreNNDist` and
    `PseudoMetricSpace.le_two_mul_dist_ofPreNNDist`, hence the distance given by the former
    pseudometric space structure is Lipschitz equivalent to the `d`. Thus the uniformities generated
    by `d` and `dist` are equal. Since the former uniformity is equal to `𝓤 X`, the latter is equal
    to `𝓤 X` as well. -/
  obtain ⟨U, hU_symm, hU_comp, hB⟩ :
    ∃ U : ℕ → SetRel X X,
      (∀ n, (U n).IsSymm) ∧
        (∀ ⦃m n⦄, m < n → U n ○ (U n ○ U n) ⊆ U m) ∧ (𝓤 X).HasAntitoneBasis U := by
    rcases UniformSpace.has_seq_basis X with ⟨V, hB, hV_symm⟩
    rcases hB.subbasis_with_rel fun m =>
        hB.tendsto_smallSets.eventually
          (eventually_uniformity_iterate_comp_subset (hB.mem m) 2) with
      ⟨φ, -, hφ_comp, hφB⟩
    exact ⟨V ∘ φ, fun n => hV_symm _, hφ_comp, hφB⟩
  set d : X → X → ℝ≥0 := fun x y => if h : ∃ n, (x, y) ∉ U n then (1 / 2) ^ Nat.find h else 0
  have hd₀ : ∀ {x y}, d x y = 0 ↔ Inseparable x y := by
    intro x y
    refine Iff.trans ?_ hB.inseparable_iff_uniformity.symm
    simp only [d, true_imp_iff]
    split_ifs with h
    · simp [h, pow_eq_zero_iff']
    · simpa only [not_exists, Classical.not_not, eq_self_iff_true, true_iff] using h
  have hd_symm x y : d x y = d y x := by simp only [d, (U _).comm]
  have hr : (1 / 2 : ℝ≥0) ∈ Ioo (0 : ℝ≥0) 1 := ⟨half_pos one_pos, NNReal.half_lt_self one_ne_zero⟩
  let I := PseudoMetricSpace.ofPreNNDist d (fun x => hd₀.2 rfl) hd_symm
  have hdist_le : ∀ x y, dist x y ≤ d x y := PseudoMetricSpace.dist_ofPreNNDist_le _ _ _
  have hle_d : ∀ {x y : X} {n : ℕ}, (1 / 2) ^ n ≤ d x y ↔ (x, y) ∉ U n := by
    intro x y n
    dsimp only [d]
    split_ifs with h
    · rw [(pow_right_strictAnti₀ hr.1 hr.2).le_iff_ge, Nat.find_le_iff]
      exact ⟨fun ⟨m, hmn, hm⟩ hn => hm (hB.antitone hmn hn), fun h => ⟨n, le_rfl, h⟩⟩
    · push Not at h
      simp only [h, not_true, (pow_pos hr.1 _).not_ge]
  have hd_le : ∀ x y, ↑(d x y) ≤ 2 * dist x y := by
    refine PseudoMetricSpace.le_two_mul_dist_ofPreNNDist _ _ _ fun x₁ x₂ x₃ x₄ => ?_
    by_cases H : ∃ n, (x₁, x₄) ∉ U n
    · refine (dif_pos H).trans_le ?_
      rw [← div_le_iff₀' zero_lt_two, ← mul_one_div (_ ^ _), ← pow_succ]
      simp only [le_max_iff, hle_d, ← not_and_or]
      rintro ⟨h₁₂, h₂₃, h₃₄⟩
      refine Nat.find_spec H (hU_comp (lt_add_one <| Nat.find H) ?_)
      exact ⟨x₂, h₁₂, x₃, h₂₃, h₃₄⟩
    · exact (dif_neg H).trans_le zero_le
  -- Porting note: without the next line, `uniformity_basis_dist_pow` ends up introducing some
  -- `Subtype.val` applications instead of `NNReal.toReal`.
  rw [mem_Ioo, ← NNReal.coe_lt_coe, ← NNReal.coe_lt_coe] at hr
  refine ⟨I, UniformSpace.ext <| (uniformity_basis_dist_pow hr.1 hr.2).ext hB.toHasBasis ?_ ?_⟩
  · refine fun n hn => ⟨n, hn, fun x hx => (hdist_le _ _).trans_lt ?_⟩
    rwa [← NNReal.coe_pow, NNReal.coe_lt_coe, ← not_le, hle_d, Classical.not_not]
  · refine fun n _ => ⟨n + 1, trivial, fun x hx => ?_⟩
    rw [mem_ofPred_eq] at hx
    contrapose! hx
    refine le_trans ?_ ((div_le_iff₀' zero_lt_two).2 (hd_le x.1 x.2))
    rwa [← NNReal.coe_two, ← NNReal.coe_div, ← NNReal.coe_pow, NNReal.coe_le_coe, pow_succ,
      mul_one_div, div_le_iff₀ zero_lt_two, div_mul_cancel₀ _ two_ne_zero, hle_d]

/-- A `PseudoMetricSpace` instance compatible with a given `UniformSpace` structure. -/
-- see note [reducible non-instances]
/-
**UniformSpace.pseudoMetricSpace** 是 Mathlib 中的一个定义，位于命名空间 `UniformSpace`。
形式化陈述：(X : Type u_2) → [inst : UniformSpace X] → [(uniformity X).IsCountablyGene
rated] → PseudoMetricSpace X
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.metrizable_uniformity`：∀ (X : Type u_2) [inst : UniformSpac
e X] [(uniformity X).IsCountablyGenerated],   ∃ I, PseudoMetricSpace.toUniformSp
ace = inst
-/
protected noncomputable abbrev UniformSpace.pseudoMetricSpace (X : Type*) [UniformSpace X]
    [IsCountablyGenerated (𝓤 X)] : PseudoMetricSpace X :=
  (UniformSpace.metrizable_uniformity X).choose.replaceUniformity <|
    congr_arg _ (UniformSpace.metrizable_uniformity X).choose_spec.symm

/-- A `MetricSpace` instance compatible with a given `UniformSpace` structure. -/
-- see note [reducible non-instances]
/-
**UniformSpace.metricSpace** 是 Mathlib 中的一个定义，位于命名空间 `UniformSpace`。
形式化陈述：(X : Type u_2) → [inst : UniformSpace X] → [(uniformity X).IsCountablyGene
rated] → [T0Space X] → MetricSpace X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected noncomputable abbrev UniformSpace.metricSpace (X : Type*) [UniformSpace X]
    [IsCountablyGenerated (𝓤 X)] [T0Space X] : MetricSpace X :=
  @MetricSpace.ofT0PseudoMetricSpace X (UniformSpace.pseudoMetricSpace X) _

/-- A T₀ uniform space with countably generated `𝓤 X` is metrizable. This is not an instance to
avoid loops. -/
/-
**UniformSpace.metrizableSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformSpace.metrizableSpace [UniformSpace X] [IsCountablyGenerated (𝓤 X)]
 [T0Space X] : TopologicalSpace.MetrizableSpace X
参数：𝓤 X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.toMetrizableSpace`：∀ {X : Type u_
2} [inst : TopologicalSpace X] [T0Space X] [h : TopologicalSpace.PseudoMetrizabl
eSpace X],   TopologicalSpace.MetrizableSpace …
· 使用定理 `UniformSpace.pseudoMetrizableSpace`：∀ {X : Type u_5} [u : UniformSpace X
] [hu : (uniformity X).IsCountablyGenerated],   TopologicalSpace.PseudoMetrizabl
eSpace X

--- 原说明 ---
A T₀ uniform space with countably generated `𝓤 X` is metrizable. This is not an 
instance to
avoid loops.
-/
theorem UniformSpace.metrizableSpace [UniformSpace X] [IsCountablyGenerated (𝓤 X)] [T0Space X] :
    TopologicalSpace.MetrizableSpace X := inferInstance

/-- Construct on a pseudometrizable space a pseudometric compatible with the topology. -/
-- see note [reducible non-instances]
/-
**TopologicalSpace.pseudoMetrizableSpacePseudoMetric** 是 Mathlib 中的一个缩写定义，位于命名空间
 ``。
形式化陈述：TopologicalSpace.pseudoMetrizableSpacePseudoMetric (X : Type*) [Topologica
lSpace X] [TopologicalSpace.PseudoMetrizableSpace X] : PseudoMetricSpace X
参数：X : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.pseudoMetrizableSpaceUniformity_countably_generated`：ps
eudoMetrizableSpaceUniformity_countably_generated (X : Type*) [TopologicalSpace 
X] [h : PseudoMetrizableSpace X] : 𝓤[pseudoMetrizableSpace…
-/
noncomputable abbrev TopologicalSpace.pseudoMetrizableSpacePseudoMetric (X : Type*)
    [TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X] : PseudoMetricSpace X :=
  letI := TopologicalSpace.pseudoMetrizableSpaceUniformity X
  haveI := TopologicalSpace.pseudoMetrizableSpaceUniformity_countably_generated X
  UniformSpace.pseudoMetricSpace X
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {X : Type*} [t : TopologicalSpace X] [t.PseudoMetrizableSpace] :
    t.pseudoMetrizableSpacePseudoMetric.toUniformSpace = t.pseudoMetrizableSpaceUniformity := by
  with_reducible_and_instances rfl

/-- Construct on a metrizable space a metric compatible with the topology. -/
/-
**TopologicalSpace.metrizableSpaceMetric** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：TopologicalSpace.metrizableSpaceMetric (X : Type*) [TopologicalSpace X] [T
opologicalSpace.MetrizableSpace X] : MetricSpace X
参数：X : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X

--- 原说明 ---
Construct on a metrizable space a metric compatible with the topology.
-/
noncomputable abbrev TopologicalSpace.metrizableSpaceMetric (X : Type*) [TopologicalSpace X]
    [TopologicalSpace.MetrizableSpace X] : MetricSpace X :=
  letI := pseudoMetrizableSpacePseudoMetric X
  .ofT0PseudoMetricSpace X
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {X : Type*} [t : TopologicalSpace X] [t.MetrizableSpace] :
    t.metrizableSpaceMetric.toPseudoMetricSpace = t.pseudoMetrizableSpacePseudoMetric := by
  with_reducible_and_instances rfl

variable {α : Type*}
open TopologicalSpace
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) PseudoEMetricSpace.pseudoMetrizableSpace
    [PseudoEMetricSpace α] : PseudoMetrizableSpace α :=
  inferInstance
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) EMetricSpace.metrizableSpace
    [EMetricSpace α] : MetrizableSpace α :=
  inferInstance
