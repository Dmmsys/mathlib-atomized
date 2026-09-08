/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Topology.UnitInterval

/-!
# Topological study of spaces `Π (n : ℕ), E n`

When `E n` are topological spaces, the space `Π (n : ℕ), E n` is naturally a topological space
(with the product topology). When `E n` are uniform spaces, it also inherits a uniform structure.
However, it does not inherit a canonical metric space structure of the `E n`. Nevertheless, one
can put a noncanonical metric space structure (or rather, several of them). This is done in this
file.

## Main definitions and results

One can define a combinatorial distance on `Π (n : ℕ), E n`, as follows:

* `PiNat.cylinder x n` is the set of points `y` with `x i = y i` for `i < n`.
* `PiNat.firstDiff x y` is the first index at which `x i ≠ y i`.
* `PiNat.dist x y` is equal to `(1/2) ^ (firstDiff x y)`. It defines a distance
  on `Π (n : ℕ), E n`, compatible with the topology when the `E n` have the discrete topology.
* `PiNat.metricSpace`: the metric space structure, given by this distance. Not registered as an
  instance. This space is a complete metric space.
* `PiNat.metricSpaceOfDiscreteUniformity`: the same metric space structure, but adjusting the
  uniformity defeqness when the `E n` already have the discrete uniformity. Not registered as an
  instance
* `PiNat.metricSpaceNatNat`: the particular case of `ℕ → ℕ`, not registered as an instance.

These results are used to construct continuous functions on `Π n, E n`:

* `PiNat.exists_retraction_of_isClosed`: given a nonempty closed subset `s` of `Π (n : ℕ), E n`,
  there exists a retraction onto `s`, i.e., a continuous map from the whole space to `s`
  restricting to the identity on `s`.
* `exists_nat_nat_continuous_surjective_of_completeSpace`: given any nonempty complete metric
  space with second-countable topology, there exists a continuous surjection from `ℕ → ℕ` onto
  this space.

One can also put distances on `Π (i : ι), E i` when the spaces `E i` are metric spaces (not discrete
in general), and `ι` is countable.

* `PiCountable.dist` is the distance on `Π i, E i` given by
    `dist x y = ∑' i, min (1/2)^(encode i) (dist (x i) (y i))`.
* `PiCountable.metricSpace` is the corresponding metric space structure, adjusted so that
  the uniformity is definitionally the product uniformity. Not registered as an instance.
* `PiNatEmbed` gives an equivalence between a space and itself in a sequence of spaces
* `Metric.PiNatEmbed.metricSpace` proves that a topological `X` separated by countably many
  continuous functions to metric spaces, can be embedded inside their product.

-/

@[expose] public section

noncomputable section

open Topology TopologicalSpace Set Metric Filter Function

attribute [local simp] pow_le_pow_iff_right₀ one_lt_two inv_le_inv₀ zero_le_two zero_lt_two

variable {E : ℕ → Type*}

namespace PiNat

/-! ### The firstDiff function -/

open scoped Classical in
/-- In a product space `Π n, E n`, then `firstDiff x y` is the first index at which `x` and `y`
differ. If `x = y`, then by convention we set `firstDiff x x = 0`. -/
irreducible_def firstDiff (x y : ∀ n, E n) : ℕ :=
  if h : x ≠ y then Nat.find (ne_iff.1 h) else 0

/-
**PiNat.apply_firstDiff_ne** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：apply_firstDiff_ne {x y : forall n, E n} (h : x != y) : x (firstDiff x y) 
!= y (firstDiff x y)
参数：h : x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiNat.firstDiff_def`：∀ {E : ℕ → Type u_2} (x y : (n : ℕ) → E n), PiNat.f
irstDiff x y = if h : x ≠ y then Nat.find ⋯ else 0
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.ne_iff`：ne_iff {β : α -> Sort*} {f₁ f₂ : forall a, β a} : f₁ !=
 f₂ ↔ exists a, f₁ a != f₂ a
-/
theorem apply_firstDiff_ne {x y : ∀ n, E n} (h : x ≠ y) :
    x (firstDiff x y) ≠ y (firstDiff x y) := by
  rw [firstDiff_def, dif_pos h]
  classical
  exact Nat.find_spec (ne_iff.1 h)
/-
**PiNat.apply_eq_of_lt_firstDiff** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：apply_eq_of_lt_firstDiff {x y : forall n, E n} {n : Nat} (hn : n < firstDi
ff x y) : x n = y n
参数：hn : n < firstDiff x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Classical.dite_not`：∀ {p : Prop} {α : Sort u_1} [hn : Decidable ¬p] (x :
 ¬p → α) (y : ¬¬p → α), dite (¬p) x y = dite p (fun h => y ⋯) x
· 使用定理 `PiNat.firstDiff_def`：∀ {E : ℕ → Type u_2} (x y : (n : ℕ) → E n), PiNat.f
irstDiff x y = if h : x ≠ y then Nat.find ⋯ else 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem apply_eq_of_lt_firstDiff {x y : ∀ n, E n} {n : ℕ} (hn : n < firstDiff x y) : x n = y n := by
  rw [firstDiff_def] at hn
  aesop
/-
**PiNat.firstDiff_comm** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：firstDiff_comm (x y : forall n, E n) : firstDiff x y = firstDiff y x
参数：x y : forall n, E n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiNat.firstDiff_def`：∀ {E : ℕ → Type u_2} (x y : (n : ℕ) → E n), PiNat.f
irstDiff x y = if h : x ≠ y then Nat.find ⋯ else 0
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Nat.find.congr_simp`：∀ {p p_1 : ℕ → Prop} (e_p : p = p_1) {inst : Decida
blePred p} [inst_1 : DecidablePred p_1] (H : ∃ n, p n),   Nat.find H = Nat.find 
⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem firstDiff_comm (x y : ∀ n, E n) : firstDiff x y = firstDiff y x := by
  classical
  simp only [firstDiff_def, ne_comm]
/-
**PiNat.min_firstDiff_le** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：min_firstDiff_le (x y z : forall n, E n) (h : x != z) : min (firstDiff x y
) (firstDiff y z) <= firstDiff x z
参数：x y z : forall n, E n；h : x != z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `PiNat.apply_firstDiff_ne`：apply_firstDiff_ne {x y : forall n, E n} (h : 
x != y) : x (firstDiff x y) != y (firstDiff x y)
· 使用定理 `PiNat.apply_eq_of_lt_firstDiff`：apply_eq_of_lt_firstDiff {x y : forall n
, E n} {n : Nat} (hn : n < firstDiff x y) : x n = y n
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lt_min_iff`：lt_min_iff : a < min b c ↔ a < b ∧ a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem min_firstDiff_le (x y z : ∀ n, E n) (h : x ≠ z) :
    min (firstDiff x y) (firstDiff y z) ≤ firstDiff x z := by
  by_contra! H
  rw [lt_min_iff] at H
  refine apply_firstDiff_ne h ?_
  calc
    x (firstDiff x z) = y (firstDiff x z) := apply_eq_of_lt_firstDiff H.1
    _ = z (firstDiff x z) := apply_eq_of_lt_firstDiff H.2

/-! ### Cylinders -/

/-- In a product space `Π n, E n`, the cylinder set of length `n` around `x`, denoted
`cylinder x n`, is the set of sequences `y` that coincide with `x` on the first `n` symbols, i.e.,
such that `y i = x i` for all `i < n`.
-/
/-
**PiNat.cylinder** 是 Mathlib 中的一个定义，位于命名空间 `PiNat`。
形式化陈述：cylinder (x : forall n, E n) (n : Nat) : Set (forall n, E n)
参数：x : forall n, E n；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a product space `Π n, E n`, the cylinder set of length `n` around `x`, denote
d
`cylinder x n`, is the set of sequences `y` that coincide with `x` on the first 
`n` symbols, i.e.,
such that `y i = x i` for all `i < n`.
-/
def cylinder (x : ∀ n, E n) (n : ℕ) : Set (∀ n, E n) :=
  { y | ∀ i, i < n → y i = x i }
/-
**PiNat.cylinder_eq_pi** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：cylinder_eq_pi (x : forall n, E n) (n : Nat) : cylinder x n = Set.pi (Fins
et.range n : Set Nat) fun i : Nat => {x i}
参数：x : forall n, E n；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_range`：coe_range (n : Nat) : (range n : Set Nat) = Set.Iio n
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cylinder_eq_pi (x : ∀ n, E n) (n : ℕ) :
    cylinder x n = Set.pi (Finset.range n : Set ℕ) fun i : ℕ => {x i} := by
  ext y
  simp [cylinder]

@[simp]
/-
**PiNat.cylinder_zero** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：cylinder_zero (x : forall n, E n) : cylinder x 0 = univ
参数：x : forall n, E n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiNat.cylinder_eq_pi`：cylinder_eq_pi (x : forall n, E n) (n : Nat) : cyl
inder x n = Set.pi (Finset.range n : Set Nat) fun i : Nat => {x i}
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `Set.empty_pi`：empty_pi (s : forall i, Set (α i)) : pi ∅ s = univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cylinder_zero (x : ∀ n, E n) : cylinder x 0 = univ := by simp [cylinder_eq_pi]
/-
**PiNat.cylinder_anti** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：cylinder_anti (x : forall n, E n) {m n : Nat} (h : m <= n) : cylinder x n 
subseteq cylinder x m
参数：x : forall n, E n；h : m <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
-/
theorem cylinder_anti (x : ∀ n, E n) {m n : ℕ} (h : m ≤ n) : cylinder x n ⊆ cylinder x m :=
  fun _y hy i hi => hy i (hi.trans_le h)

@[simp]
/-
**PiNat.mem_cylinder_iff** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：mem_cylinder_iff {x y : forall n, E n} {n : Nat} : y in cylinder x n ↔ for
all i < n, y i = x i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_cylinder_iff {x y : ∀ n, E n} {n : ℕ} : y ∈ cylinder x n ↔ ∀ i < n, y i = x i :=
  Iff.rfl
/-
**PiNat.self_mem_cylinder** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：self_mem_cylinder (x : forall n, E n) (n : Nat) : x in cylinder x n
参数：x : forall n, E n；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem self_mem_cylinder (x : ∀ n, E n) (n : ℕ) : x ∈ cylinder x n := by simp
/-
**PiNat.mem_cylinder_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：mem_cylinder_iff_eq {x y : forall n, E n} {n : Nat} : y in cylinder x n ↔ 
cylinder y n = cylinder x n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PiNat.self_mem_cylinder`：self_mem_cylinder (x : forall n, E n) (n : Nat)
 : x in cylinder x n
-/
theorem mem_cylinder_iff_eq {x y : ∀ n, E n} {n : ℕ} :
    y ∈ cylinder x n ↔ cylinder y n = cylinder x n := by
  constructor
  · intro hy
    apply Subset.antisymm
    · intro z hz i hi
      rw [← hy i hi]
      exact hz i hi
    · intro z hz i hi
      rw [hy i hi]
      exact hz i hi
  · intro h
    rw [← h]
    exact self_mem_cylinder _ _
/-
**PiNat.mem_cylinder_comm** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：mem_cylinder_comm (x y : forall n, E n) (n : Nat) : y in cylinder x n ↔ x 
in cylinder y n
参数：x y : forall n, E n；n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_cylinder_comm (x y : ∀ n, E n) (n : ℕ) : y ∈ cylinder x n ↔ x ∈ cylinder y n := by
  simp [eq_comm]
/-
**PiNat.mem_cylinder_iff_le_firstDiff** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：mem_cylinder_iff_le_firstDiff {x y : forall n, E n} (hne : x != y) (i : Na
t) : x in cylinder y i ↔ i <= firstDiff x y
参数：hne : x != y；i : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `PiNat.apply_firstDiff_ne`：apply_firstDiff_ne {x y : forall n, E n} (h : 
x != y) : x (firstDiff x y) != y (firstDiff x y)
· 使用定理 `PiNat.apply_eq_of_lt_firstDiff`：apply_eq_of_lt_firstDiff {x y : forall n
, E n} {n : Nat} (hn : n < firstDiff x y) : x n = y n
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
-/
theorem mem_cylinder_iff_le_firstDiff {x y : ∀ n, E n} (hne : x ≠ y) (i : ℕ) :
    x ∈ cylinder y i ↔ i ≤ firstDiff x y := by
  constructor
  · intro h
    by_contra!
    exact apply_firstDiff_ne hne (h _ this)
  · intro hi j hj
    exact apply_eq_of_lt_firstDiff (hj.trans_le hi)
/-
**PiNat.mem_cylinder_firstDiff** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：mem_cylinder_firstDiff (x y : forall n, E n) : x in cylinder y (firstDiff 
x y)
参数：x y : forall n, E n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiNat.apply_eq_of_lt_firstDiff`：apply_eq_of_lt_firstDiff {x y : forall n
, E n} {n : Nat} (hn : n < firstDiff x y) : x n = y n
-/
theorem mem_cylinder_firstDiff (x y : ∀ n, E n) : x ∈ cylinder y (firstDiff x y) := fun _i hi =>
  apply_eq_of_lt_firstDiff hi
/-
**PiNat.cylinder_eq_cylinder_of_le_firstDiff** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：cylinder_eq_cylinder_of_le_firstDiff (x y : forall n, E n) {n : Nat} (hn :
 n <= firstDiff x y) : cylinder x n = cylinder y n
参数：x y : forall n, E n；hn : n <= firstDiff x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PiNat.mem_cylinder_iff_eq`：mem_cylinder_iff_eq {x y : forall n, E n} {n 
: Nat} : y in cylinder x n ↔ cylinder y n = cylinder x n
· 使用定理 `PiNat.apply_eq_of_lt_firstDiff`：apply_eq_of_lt_firstDiff {x y : forall n
, E n} {n : Nat} (hn : n < firstDiff x y) : x n = y n
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
-/
theorem cylinder_eq_cylinder_of_le_firstDiff (x y : ∀ n, E n) {n : ℕ} (hn : n ≤ firstDiff x y) :
    cylinder x n = cylinder y n := by
  rw [← mem_cylinder_iff_eq]
  intro i hi
  exact apply_eq_of_lt_firstDiff (hi.trans_le hn)
/-
**PiNat.iUnion_cylinder_update** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：iUnion_cylinder_update (x : forall n, E n) (n : Nat) : ⋃ k, cylinder (upda
te x n k) (n + 1) = cylinder x n
参数：x : forall n, E n；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Nat.lt_succ_of_lt`：∀ {a b : ℕ}, a < b → a < b.succ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.lt_succ_iff_lt_or_eq`：∀ {m n : ℕ}, m < n.succ ↔ m < n ∨ m = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
-/
theorem iUnion_cylinder_update (x : ∀ n, E n) (n : ℕ) :
    ⋃ k, cylinder (update x n k) (n + 1) = cylinder x n := by
  ext y
  simp only [mem_cylinder_iff, mem_iUnion]
  constructor
  · rintro ⟨k, hk⟩ i hi
    simpa [hi.ne] using hk i (Nat.lt_succ_of_lt hi)
  · intro H
    refine ⟨y n, fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with (h'i | rfl)
    · simp [H i h'i, h'i.ne]
    · simp
/-
**PiNat.update_mem_cylinder** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：update_mem_cylinder (x : forall n, E n) (n : Nat) (y : E n) : update x n y
 in cylinder x n
参数：x : forall n, E n；n : Nat；y : E n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PiNat.mem_cylinder_iff`：mem_cylinder_iff {x y : forall n, E n} {n : Nat}
 : y in cylinder x n ↔ forall i < n, y i = x i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem update_mem_cylinder (x : ∀ n, E n) (n : ℕ) (y : E n) : update x n y ∈ cylinder x n :=
  mem_cylinder_iff.2 fun i hi => by simp [hi.ne]

section Res

variable {α : Type*}

open List

/-- In the case where `E` has constant value `α`,
the cylinder `cylinder x n` can be identified with the element of `List α`
consisting of the first `n` entries of `x`. See `cylinder_eq_res`.
We call this list `res x n`, the restriction of `x` to `n`. -/
/-
**PiNat.res** 是 Mathlib 中的一个定义，位于命名空间 `PiNat`。
形式化陈述：{α : Type u_2} → (ℕ → α) → ℕ → List α
参数：ℕ → α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In the case where `E` has constant value `α`,
the cylinder `cylinder x n` can be identified with the element of `List α`
consisting of the first `n` entries of `x`. See `cylinder_eq_res`.
We call this list `res x n`, the restriction of `x` to `n`.
-/
def res (x : ℕ → α) : ℕ → List α
  | 0 => nil
  | Nat.succ n => x n :: res x n

@[simp]
/-
**PiNat.res_zero** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：res_zero (x : Nat -> α) : res x 0 = @nil α
参数：x : Nat -> α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem res_zero (x : ℕ → α) : res x 0 = @nil α :=
  rfl

@[simp]
/-
**PiNat.res_succ** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：res_succ (x : Nat -> α) (n : Nat) : res x n.succ = x n :: res x n
参数：x : Nat -> α；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem res_succ (x : ℕ → α) (n : ℕ) : res x n.succ = x n :: res x n :=
  rfl

@[simp]
/-
**PiNat.res_length** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：res_length (x : Nat -> α) (n : Nat) : (res x n).length = n
参数：x : Nat -> α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem res_length (x : ℕ → α) (n : ℕ) : (res x n).length = n := by induction n <;> simp [*]

/-- The restrictions of `x` and `y` to `n` are equal if and only if `x m = y m` for all `m < n`. -/
/-
**PiNat.res_eq_res** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：res_eq_res {x y : Nat -> α} {n : Nat} : res x n = res y n ↔ forall ⦃m⦄, m 
< n -> x m = y m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.lt_succ_iff_lt_or_eq`：∀ {m n : ℕ}, m < n.succ ↔ m < n ∨ m = n
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c

--- 原说明 ---
The restrictions of `x` and `y` to `n` are equal if and only if `x m = y m` for 
all `m < n`.
-/
theorem res_eq_res {x y : ℕ → α} {n : ℕ} :
    res x n = res y n ↔ ∀ ⦃m⦄, m < n → x m = y m := by
  constructor <;> intro h
  · induction n with
    | zero => simp
    | succ n ih =>
      intro m hm
      rw [Nat.lt_succ_iff_lt_or_eq] at hm
      simp only [res_succ, cons.injEq] at h
      rcases hm with hm | hm
      · exact ih h.2 hm
      rw [hm]
      exact h.1
  · induction n with
    | zero => simp
    | succ n ih =>
      simp only [res_succ, cons.injEq]
      refine ⟨h (Nat.lt_succ_self _), ih fun m hm => ?_⟩
      exact h (hm.trans (Nat.lt_succ_self _))
/-
**PiNat.res_injective** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：res_injective : Injective (@res α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PiNat.res_eq_res`：res_eq_res {x y : Nat -> α} {n : Nat} : res x n = res 
y n ↔ forall ⦃m⦄, m < n -> x m = y m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
-/
theorem res_injective : Injective (@res α) := by
  intro x y h
  ext n
  apply res_eq_res.mp _ (Nat.lt_succ_self _)
  rw [h]

/-- `cylinder x n` is equal to the set of sequences `y` with the same restriction to `n` as `x`. -/
/-
**PiNat.cylinder_eq_res** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：cylinder_eq_res (x : Nat -> α) (n : Nat) : cylinder x n = { y | res y n = 
res x n }
参数：x : Nat -> α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiNat.res_eq_res`：res_eq_res {x y : Nat -> α} {n : Nat} : res x n = res 
y n ↔ forall ⦃m⦄, m < n -> x m = y m
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`cylinder x n` is equal to the set of sequences `y` with the same restriction to
 `n` as `x`.
-/
theorem cylinder_eq_res (x : ℕ → α) (n : ℕ) :
    cylinder x n = { y | res y n = res x n } := by
  ext y
  dsimp [cylinder]
  rw [res_eq_res]

end Res

/-!
### A distance function on `Π n, E n`

We define a distance function on `Π n, E n`, given by `dist x y = (1/2)^n` where `n` is the first
index at which `x` and `y` differ. When each `E n` has the discrete topology, this distance will
define the right topology on the product space. We do not record a global `Dist` instance nor
a `MetricSpace` instance, as other distances may be used on these spaces, but we register them as
local instances in this section.
-/

open scoped Classical in
/-- The distance function on a product space `Π n, E n`, given by `dist x y = (1/2)^n` where `n` is
the first index at which `x` and `y` differ. -/
@[instance_reducible]
/-
**PiNat.dist** 是 Mathlib 中的一个定义，位于命名空间 `PiNat`。
形式化陈述：{E : ℕ → Type u_1} → Dist ((n : ℕ) → E n)
参数：(n : ℕ) → E n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The distance function on a product space `Π n, E n`, given by `dist x y = (1/2)^
n` where `n` is
the first index at which `x` and `y` differ.
-/
protected def dist : Dist (∀ n, E n) :=
  ⟨fun x y => if x ≠ y then (1 / 2 : ℝ) ^ firstDiff x y else 0⟩

attribute [local instance] PiNat.dist
/-
**PiNat.dist_eq_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：dist_eq_of_ne {x y : forall n, E n} (h : x != y) : dist x y = (1 / 2 : Rea
l) ^ firstDiff x y
参数：h : x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dist_eq_of_ne {x y : ∀ n, E n} (h : x ≠ y) : dist x y = (1 / 2 : ℝ) ^ firstDiff x y := by
  simp [dist, h]
/-
**PiNat.dist_self** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：∀ {E : ℕ → Type u_1} (x : (n : ℕ) → E n), dist x x = 0
参数：x : (n : ℕ) → E n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
protected theorem dist_self (x : ∀ n, E n) : dist x x = 0 := by simp [dist]
/-
**PiNat.dist_comm** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：∀ {E : ℕ → Type u_1} (x y : (n : ℕ) → E n), dist x y = dist y x
参数：x y : (n : ℕ) → E n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `ite_not`：∀ {α : Sort u_1} (p : Prop) [inst : Decidable p] (x y : α), (if
 ¬p then x else y) = if p then y else x
· 使用定理 `PiNat.firstDiff_comm`：firstDiff_comm (x y : forall n, E n) : firstDiff x
 y = firstDiff y x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem dist_comm (x y : ∀ n, E n) : dist x y = dist y x := by
  classical
  simp [dist, @eq_comm _ x y, firstDiff_comm]
/-
**PiNat.dist_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：∀ {E : ℕ → Type u_1} (x y : (n : ℕ) → E n), 0 ≤ dist x y
参数：x y : (n : ℕ) → E n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
protected theorem dist_nonneg (x y : ∀ n, E n) : 0 ≤ dist x y := by
  rcases eq_or_ne x y with (rfl | h)
  · simp [dist]
  · simp [dist, h]
/-
**PiNat.dist_le_one** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：∀ {E : ℕ → Type u_1} (x y : (n : ℕ) → E n), dist x y ≤ 1
参数：x y : (n : ℕ) → E n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用引理 `inv_le_one_of_one_le₀`：inv_le_one_of_one_le₀ (ha : 1 <= a) : a⁻¹ <= 1
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `one_le_pow₀`：one_le_pow₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 <= 
a) {n : Nat} : 1 <= a ^ n
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Mathlib.Meta.NormNum.isNat_le_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] {a b : α} {a' b' : ℕ},   Mathlib.Me
ta.NormNum.IsNat a a' → …
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
-/
protected theorem dist_le_one (x y : ∀ n, E n) : dist x y ≤ 1 := by
  rcases eq_or_ne x y with (rfl | h)
  · simp [dist]
  · simp only [dist, ne_eq, h, not_false_eq_true, ↓reduceIte, one_div, inv_pow]
    bound
/-
**PiNat.dist_triangle_nonarch** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：dist_triangle_nonarch (x y z : forall n, E n) : dist x z <= max (dist x y)
 (dist y z)
参数：x y z : forall n, E n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiNat.dist_self`：∀ {E : ℕ → Type u_1} (x : (n : ℕ) → E n), dist x x = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `PiNat.dist_eq_of_ne`：dist_eq_of_ne {x y : forall n, E n} (h : x != y) : 
dist x y = (1 / 2 : Real) ^ firstDiff x y
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `min_le_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, min b c ≤
 a ↔ b ≤ a ∨ c ≤ a
· 使用定理 `PiNat.min_firstDiff_le`：min_firstDiff_le (x y z : forall n, E n) (h : x 
!= z) : min (firstDiff x y) (firstDiff y z) <= firstDiff x z
-/
theorem dist_triangle_nonarch (x y z : ∀ n, E n) : dist x z ≤ max (dist x y) (dist y z) := by
  rcases eq_or_ne x z with (rfl | hxz)
  · simp [PiNat.dist_self x, PiNat.dist_nonneg]
  rcases eq_or_ne x y with (rfl | hxy)
  · simp
  rcases eq_or_ne y z with (rfl | hyz)
  · simp
  simp only [dist_eq_of_ne, hxz, hxy, hyz, inv_le_inv₀, one_div, inv_pow, zero_lt_two, Ne,
    not_false_iff, le_max_iff, pow_le_pow_iff_right₀, one_lt_two, pow_pos,
    min_le_iff.1 (min_firstDiff_le x y z hxz)]
/-
**PiNat.dist_triangle** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：∀ {E : ℕ → Type u_1} (x y z : (n : ℕ) → E n), dist x z ≤ dist x y + dist y
 z
参数：x y z : (n : ℕ) → E n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiNat.dist_triangle_nonarch`：dist_triangle_nonarch (x y z : forall n, E 
n) : dist x z <= max (dist x y) (dist y z)
· 使用定理 `max_le_add_of_nonneg`：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : 
AddZeroClass α] [AddLeftMono α] [AddRightMono α] {a b : α},   0 ≤ a → 0 ≤ b → ma
x a b ≤ a …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `PiNat.dist_nonneg`：∀ {E : ℕ → Type u_1} (x y : (n : ℕ) → E n), 0 ≤ dist 
x y
-/
protected theorem dist_triangle (x y z : ∀ n, E n) : dist x z ≤ dist x y + dist y z :=
  calc
    dist x z ≤ max (dist x y) (dist y z) := dist_triangle_nonarch x y z
    _ ≤ dist x y + dist y z := max_le_add_of_nonneg (PiNat.dist_nonneg _ _) (PiNat.dist_nonneg _ _)
/-
**PiNat.eq_of_dist_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：∀ {E : ℕ → Type u_1} (x y : (n : ℕ) → E n), dist x y = 0 → x = y
参数：x y : (n : ℕ) → E n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiNat.dist_eq_of_ne`：dist_eq_of_ne {x y : forall n, E n} (h : x != y) : 
dist x y = (1 / 2 : Real) ^ firstDiff x y
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
-/
protected theorem eq_of_dist_eq_zero (x y : ∀ n, E n) (hxy : dist x y = 0) : x = y := by
  rcases eq_or_ne x y with (rfl | h); · rfl
  simp [dist_eq_of_ne h] at hxy
/-
**PiNat.mem_cylinder_iff_dist_le** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：mem_cylinder_iff_dist_le {x y : forall n, E n} {n : Nat} : y in cylinder x
 n ↔ dist y x <= (1 / 2) ^ n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `PiNat.dist_self`：∀ {E : ℕ → Type u_1} (x : (n : ℕ) → E n), dist x x = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `PiNat.apply_firstDiff_ne`：apply_firstDiff_ne {x y : forall n, E n} (h : 
x != y) : x (firstDiff x y) != y (firstDiff x y)
· 使用定理 `PiNat.apply_eq_of_lt_firstDiff`：apply_eq_of_lt_firstDiff {x y : forall n
, E n} {n : Nat} (hn : n < firstDiff x y) : x n = y n
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `PiNat.dist_eq_of_ne`：dist_eq_of_ne {x y : forall n, E n} (h : x != y) : 
dist x y = (1 / 2 : Real) ^ firstDiff x y
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem mem_cylinder_iff_dist_le {x y : ∀ n, E n} {n : ℕ} :
    y ∈ cylinder x n ↔ dist y x ≤ (1 / 2) ^ n := by
  rcases eq_or_ne y x with (rfl | hne)
  · simp [PiNat.dist_self]
  suffices (∀ i : ℕ, i < n → y i = x i) ↔ n ≤ firstDiff y x by simpa [dist_eq_of_ne hne]
  constructor
  · intro hy
    by_contra! H
    exact apply_firstDiff_ne hne (hy _ H)
  · intro h i hi
    exact apply_eq_of_lt_firstDiff (hi.trans_le h)
/-
**PiNat.apply_eq_of_dist_lt** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：apply_eq_of_dist_lt {x y : forall n, E n} {n : Nat} (h : dist x y < (1 / 2
) ^ n) {i : Nat} (hi : i <= n) : x i = y i
参数：h : dist x y < (1 / 2) ^ n；hi : i <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiNat.dist_eq_of_ne`：dist_eq_of_ne {x y : forall n, E n} (h : x != y) : 
dist x y = (1 / 2 : Real) ^ firstDiff x y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `PiNat.apply_eq_of_lt_firstDiff`：apply_eq_of_lt_firstDiff {x y : forall n
, E n} {n : Nat} (hn : n < firstDiff x y) : x n = y n
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
-/
theorem apply_eq_of_dist_lt {x y : ∀ n, E n} {n : ℕ} (h : dist x y < (1 / 2) ^ n) {i : ℕ}
    (hi : i ≤ n) : x i = y i := by
  rcases eq_or_ne x y with (rfl | hne)
  · rfl
  have : n < firstDiff x y := by
    simpa [dist_eq_of_ne hne, inv_lt_inv₀, pow_lt_pow_iff_right₀, one_lt_two] using h
  exact apply_eq_of_lt_firstDiff (hi.trans_lt this)

/-- A function to a pseudo-metric-space is `1`-Lipschitz if and only if points in the same cylinder
of length `n` are sent to points within distance `(1/2)^n`.
Not expressed using `LipschitzWith` as we don't have a metric space structure -/
/-
**PiNat.lipschitz_with_one_iff_forall_dist_image_le_of_mem_cylinder** 是 Mathlib 
中的一个定理，位于命名空间 `PiNat`。
形式化陈述：lipschitz_with_one_iff_forall_dist_image_le_of_mem_cylinder {α : Type*} [P
seudoMetricSpace α] {f : (forall n, E n) -> α} : (forall x y : forall n, E n, di
st (f x) (f y) <= dist x y) ↔ forall x y n, y in cylinder x n -> dist (f x) (f y
) <= (1 / 2) ^ n
参数：forall n, E n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiNat.dist_comm`：∀ {E : ℕ → Type u_1} (x y : (n : ℕ) → E n), dist x y = 
dist y x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PiNat.mem_cylinder_iff_dist_le`：mem_cylinder_iff_dist_le {x y : forall n
, E n} {n : Nat} : y in cylinder x n ↔ dist y x <= (1 / 2) ^ n
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `PiNat.dist_eq_of_ne`：dist_eq_of_ne {x y : forall n, E n} (h : x != y) : 
dist x y = (1 / 2 : Real) ^ firstDiff x y
· 使用定理 `PiNat.firstDiff_comm`：firstDiff_comm (x y : forall n, E n) : firstDiff x
 y = firstDiff y x
· 使用定理 `PiNat.mem_cylinder_firstDiff`：mem_cylinder_firstDiff (x y : forall n, E 
n) : x in cylinder y (firstDiff x y)

--- 原说明 ---
A function to a pseudo-metric-space is `1`-Lipschitz if and only if points in th
e same cylinder
of length `n` are sent to points within distance `(1/2)^n`.
Not expressed using `LipschitzWith` as we don't have a metric space structure
-/
theorem lipschitz_with_one_iff_forall_dist_image_le_of_mem_cylinder {α : Type*}
    [PseudoMetricSpace α] {f : (∀ n, E n) → α} :
    (∀ x y : ∀ n, E n, dist (f x) (f y) ≤ dist x y) ↔
      ∀ x y n, y ∈ cylinder x n → dist (f x) (f y) ≤ (1 / 2) ^ n := by
  constructor
  · intro H x y n hxy
    apply (H x y).trans
    rw [PiNat.dist_comm]
    exact mem_cylinder_iff_dist_le.1 hxy
  · intro H x y
    rcases eq_or_ne x y with (rfl | hne)
    · simp [PiNat.dist_nonneg]
    rw [dist_eq_of_ne hne]
    apply H x y (firstDiff x y)
    rw [firstDiff_comm]
    exact mem_cylinder_firstDiff _ _

variable (E)
variable [∀ n, TopologicalSpace (E n)] [∀ n, DiscreteTopology (E n)]
/-
**PiNat.isOpen_cylinder** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：isOpen_cylinder (x : forall n, E n) (n : Nat) : IsOpen (cylinder x n)
参数：x : forall n, E n；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiNat.cylinder_eq_pi`：cylinder_eq_pi (x : forall n, E n) (n : Nat) : cyl
inder x n = Set.pi (Finset.range n : Set Nat) fun i : Nat => {x i}
· 使用定理 `isOpen_set_pi`：isOpen_set_pi {i : Set ι} {s : forall a, Set (A a)} (hi :
 i.Finite) (hs : forall a in i, IsOpen (s a)) : IsOpen (pi i s)
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `isOpen_discrete`：isOpen_discrete (s : Set α) : IsOpen s
-/
theorem isOpen_cylinder (x : ∀ n, E n) (n : ℕ) : IsOpen (cylinder x n) := by
  rw [PiNat.cylinder_eq_pi]
  exact isOpen_set_pi (Finset.range n).finite_toSet fun a _ => isOpen_discrete _
/-
**PiNat.isTopologicalBasis_cylinders** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：isTopologicalBasis_cylinders : IsTopologicalBasis { s : Set (forall n, E n
) | exists (x : forall n, E n) (n : Nat), s = cylinder x n }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds`：isTopologicalBasi
s_of_isOpen_of_nhds {s : Set (Set α)} (h_open : forall u in s, IsOpen u) (h_nhds
 : forall (a : α) (u : Set α), a in u -> Is…
· 使用定理 `PiNat.isOpen_cylinder`：isOpen_cylinder (x : forall n, E n) (n : Nat) : I
sOpen (cylinder x n)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`：∀ {α : Ty
pe u} [t : TopologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologic
alBasis b → ∀ {a : α} {u : Set α}, a ∈ u → IsOpen u…
· 使用定理 `isTopologicalBasis_pi`：isTopologicalBasis_pi {ι : Type*} {X : ι -> Type*
} [forall i, TopologicalSpace (X i)] {T : forall i, Set (Set (X i))} (cond : for
all i, IsTo…
· 使用定理 `TopologicalSpace.isTopologicalBasis_opens`：isTopologicalBasis_opens : Is
TopologicalBasis { U : Set α | IsOpen U }
· 使用定理 `Finset.bddAbove`：∀ {α : Type u} [inst : SemilatticeSup α] [Nonempty α] (
s : Finset α), BddAbove ↑s
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `PiNat.self_mem_cylinder`：self_mem_cylinder (x : forall n, E n) (n : Nat)
 : x in cylinder x n
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PiNat.mem_cylinder_iff`：mem_cylinder_iff {x y : forall n, E n} {n : Nat}
 : y in cylinder x n ↔ forall i < n, y i = x i
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem isTopologicalBasis_cylinders :
    IsTopologicalBasis { s : Set (∀ n, E n) | ∃ (x : ∀ n, E n) (n : ℕ), s = cylinder x n } := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · rintro u ⟨x, n, rfl⟩
    apply isOpen_cylinder
  · intro x u hx u_open
    obtain ⟨v, ⟨U, F, -, rfl⟩, xU, Uu⟩ :
        ∃ v ∈ { S : Set (∀ i : ℕ, E i) | ∃ (U : ∀ i : ℕ, Set (E i)) (F : Finset ℕ),
          (∀ i : ℕ, i ∈ F → U i ∈ { s : Set (E i) | IsOpen s }) ∧ S = (F : Set ℕ).pi U },
        x ∈ v ∧ v ⊆ u :=
      (isTopologicalBasis_pi fun n : ℕ => isTopologicalBasis_opens).exists_subset_of_mem_open hx
        u_open
    rcases Finset.bddAbove F with ⟨n, hn⟩
    refine ⟨cylinder x (n + 1), ⟨x, n + 1, rfl⟩, self_mem_cylinder _ _, Subset.trans ?_ Uu⟩
    intro y hy
    suffices ∀ i : ℕ, i ∈ F → y i ∈ U i by simpa
    intro i hi
    have : y i = x i := mem_cylinder_iff.1 hy i ((hn hi).trans_lt (lt_add_one n))
    rw [this]
    simp only [Set.mem_pi, Finset.mem_coe] at xU
    exact xU i hi

variable {E}
/-
**PiNat.isOpen_iff_dist** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：isOpen_iff_dist (s : Set (forall n, E n)) : IsOpen s ↔ forall x in s, exis
ts ε > 0, forall y, dist x y < ε -> y in s
参数：s : Set (forall n, E n)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`：∀ {α : Ty
pe u} [t : TopologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologic
alBasis b → ∀ {a : α} {u : Set α}, a ∈ u → IsOpen u…
· 使用定理 `PiNat.isTopologicalBasis_cylinders`：isTopologicalBasis_cylinders : IsTop
ologicalBasis { s : Set (forall n, E n) | exists (x : forall n, E n) (n : Nat), 
s = cylinder x n }
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PiNat.mem_cylinder_iff_eq`：mem_cylinder_iff_eq {x y : forall n, E n} {n 
: Nat} : y in cylinder x n ↔ cylinder y n = cylinder x n
· 使用定理 `PiNat.apply_eq_of_dist_lt`：apply_eq_of_dist_lt {x y : forall n, E n} {n 
: Nat} (h : dist x y < (1 / 2) ^ n) {i : Nat} (hi : i <= n) : x i = y i
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `TopologicalSpace.IsTopologicalBasis.isOpen_iff`：∀ {α : Type u} [t : Topo
logicalSpace α] {s : Set α} {b : Set (Set α)},   TopologicalSpace.IsTopologicalB
asis b → (IsOpen s ↔ ∀ a ∈ s, ∃ t ∈ …
· 使用定理 `exists_pow_lt_of_lt_one`：exists_pow_lt_of_lt_one (hx : 0 < x) (hy : y < 
1) : exists n : Nat, y ^ n < x
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `one_half_lt_one`：one_half_lt_one : (1 / 2 : α) < 1
· 使用定理 `PiNat.self_mem_cylinder`：self_mem_cylinder (x : forall n, E n) (n : Nat)
 : x in cylinder x n
· 使用定理 `PiNat.dist_comm`：∀ {E : ℕ → Type u_1} (x y : (n : ℕ) → E n), dist x y = 
dist y x
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `PiNat.mem_cylinder_iff_dist_le`：mem_cylinder_iff_dist_le {x y : forall n
, E n} {n : Nat} : y in cylinder x n ↔ dist y x <= (1 / 2) ^ n
-/
theorem isOpen_iff_dist (s : Set (∀ n, E n)) :
    IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, dist x y < ε → y ∈ s := by
  constructor
  · intro hs x hx
    obtain ⟨v, ⟨y, n, rfl⟩, h'x, h's⟩ :
        ∃ v ∈ { s | ∃ (x : ∀ n : ℕ, E n) (n : ℕ), s = cylinder x n }, x ∈ v ∧ v ⊆ s :=
      (isTopologicalBasis_cylinders E).exists_subset_of_mem_open hx hs
    rw [← mem_cylinder_iff_eq.1 h'x] at h's
    exact
      ⟨(1 / 2 : ℝ) ^ n, by simp, fun y hy => h's fun i hi => (apply_eq_of_dist_lt hy hi.le).symm⟩
  · intro h
    refine (isTopologicalBasis_cylinders E).isOpen_iff.2 fun x hx => ?_
    rcases h x hx with ⟨ε, εpos, hε⟩
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 / 2 : ℝ) ^ n < ε := exists_pow_lt_of_lt_one εpos one_half_lt_one
    refine ⟨cylinder x n, ⟨x, n, rfl⟩, self_mem_cylinder x n, fun y hy => hε y ?_⟩
    rw [PiNat.dist_comm]
    exact (mem_cylinder_iff_dist_le.1 hy).trans_lt hn

/-- Metric space structure on `Π (n : ℕ), E n` when the spaces `E n` have the discrete topology,
where the distance is given by `dist x y = (1/2)^n`, where `n` is the smallest index where `x` and
`y` differ. Not registered as a global instance by default.
Warning: this definition makes sure that the topology is defeq to the original product topology,
but it does not take care of a possible uniformity. If the `E n` have a uniform structure, then
there will be two non-defeq uniform structures on `Π n, E n`, the product one and the one coming
from the metric structure. In this case, use `metricSpaceOfDiscreteUniformity` instead. -/
@[instance_reducible]
/-
**PiNat.metricSpace** 是 Mathlib 中的一个定义，位于命名空间 `PiNat`。
形式化陈述：{E : ℕ → Type u_1} →   [inst : (n : ℕ) → TopologicalSpace (E n)] → [∀ (n :
 ℕ), DiscreteTopology (E n)] → MetricSpace ((n : ℕ) → E n)
参数：n : ℕ；E n；n : ℕ；E n；(n : ℕ) → E n。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PiNat.dist_self`：∀ {E : ℕ → Type u_1} (x : (n : ℕ) → E n), dist x x = 0
· 使用定理 `PiNat.dist_comm`：∀ {E : ℕ → Type u_1} (x y : (n : ℕ) → E n), dist x y = 
dist y x
· 使用定理 `PiNat.dist_triangle`：∀ {E : ℕ → Type u_1} (x y z : (n : ℕ) → E n), dist 
x z ≤ dist x y + dist y z
· 使用定理 `PiNat.isOpen_iff_dist`：isOpen_iff_dist (s : Set (forall n, E n)) : IsOpe
n s ↔ forall x in s, exists ε > 0, forall y, dist x y < ε -> y in s
· 使用定理 `PiNat.eq_of_dist_eq_zero`：∀ {E : ℕ → Type u_1} (x y : (n : ℕ) → E n), di
st x y = 0 → x = y

--- 原说明 ---
Metric space structure on `Π (n : ℕ), E n` when the spaces `E n` have the discre
te topology,
where the distance is given by `dist x y = (1/2)^n`, where `n` is the smallest i
ndex where `x` and
`y` differ. Not registered as a global instance by default.
Warning: this definition makes sure that the topology is defeq to the original p
roduct topology,
but it does not take care of a possible uniformity. If the `E n` have a uniform 
structure, then
there will be two non-defeq uniform structures on `Π n, E n`, the product one an
d the one coming
from the metric structure. In this case, use `metricSpaceOfDiscreteUniformity` i
nstead.
-/
protected def metricSpace : MetricSpace (∀ n, E n) :=
  MetricSpace.ofDistTopology dist PiNat.dist_self PiNat.dist_comm PiNat.dist_triangle
    isOpen_iff_dist PiNat.eq_of_dist_eq_zero

/-- Metric space structure on `Π (n : ℕ), E n` when the spaces `E n` have the discrete uniformity,
where the distance is given by `dist x y = (1/2)^n`, where `n` is the smallest index where `x` and
`y` differ. Not registered as a global instance by default. -/
@[instance_reducible]
/-
**PiNat.metricSpaceOfDiscreteUniformity** 是 Mathlib 中的一个定义，位于命名空间 `PiNat`。
形式化陈述：{E : ℕ → Type u_2} →   [inst : (n : ℕ) → UniformSpace (E n)] →     (∀ (n :
 ℕ), uniformity (E n) = Filter.principal SetRel.id) → MetricSpace ((n : ℕ) → E n
)
参数：n : ℕ；E n；∀ (n : ℕ), uniformity (E n) = Filter.principal SetRel.id；(n : ℕ) → 
E n。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PiNat.dist_self`：∀ {E : ℕ → Type u_1} (x : (n : ℕ) → E n), dist x x = 0
· 使用定理 `PiNat.dist_comm`：∀ {E : ℕ → Type u_1} (x y : (n : ℕ) → E n), dist x y = 
dist y x
· 使用定理 `PiNat.dist_triangle`：∀ {E : ℕ → Type u_1} (x y z : (n : ℕ) → E n), dist 
x z ≤ dist x y + dist y z
· 使用定理 `PiNat.eq_of_dist_eq_zero`：∀ {E : ℕ → Type u_1} (x y : (n : ℕ) → E n), di
st x y = 0 → x = y

--- 原说明 ---
Metric space structure on `Π (n : ℕ), E n` when the spaces `E n` have the discre
te uniformity,
where the distance is given by `dist x y = (1/2)^n`, where `n` is the smallest i
ndex where `x` and
`y` differ. Not registered as a global instance by default.
-/
protected def metricSpaceOfDiscreteUniformity {E : ℕ → Type*} [∀ n, UniformSpace (E n)]
    (h : ∀ n, uniformity (E n) = 𝓟 SetRel.id) : MetricSpace (∀ n, E n) :=
  haveI : ∀ n, DiscreteTopology (E n) := fun n => discreteTopology_of_discrete_uniformity (h n)
  { dist_triangle := PiNat.dist_triangle
    dist_comm := PiNat.dist_comm
    dist_self := PiNat.dist_self
    eq_of_dist_eq_zero := PiNat.eq_of_dist_eq_zero _ _
    toUniformSpace := Pi.uniformSpace _
    uniformity_dist := by
      simp only [Pi.uniformity, h, SetRel.id, comap_principal, preimage_ofPred_eq]
      apply le_antisymm
      · simp only [le_iInf_iff, le_principal_iff]
        intro ε εpos
        obtain ⟨n, hn⟩ : ∃ n, (1 / 2 : ℝ) ^ n < ε := exists_pow_lt_of_lt_one εpos (by norm_num)
        apply
          @mem_iInf_of_iInter _ _ _ _ _ (Finset.range n).finite_toSet fun i =>
            { p : (∀ n : ℕ, E n) × ∀ n : ℕ, E n | p.fst i = p.snd i }
        · simp only [mem_principal, ofPred_subset_ofPred, imp_self, imp_true_iff]
        · rintro ⟨x, y⟩ hxy
          simp only [Finset.mem_coe, Finset.mem_range, iInter_coe_set, mem_iInter, mem_ofPred_eq]
            at hxy
          apply lt_of_le_of_lt _ hn
          rw [← mem_cylinder_iff_dist_le, mem_cylinder_iff]
          exact hxy
      · simp only [le_iInf_iff, le_principal_iff]
        intro n
        refine mem_iInf_of_mem ((1 / 2) ^ n : ℝ) ?_
        refine mem_iInf_of_mem (by positivity) ?_
        simp only [mem_principal, ofPred_subset_ofPred, Prod.forall]
        intro x y hxy
        exact apply_eq_of_dist_lt hxy le_rfl }

/-- Metric space structure on `ℕ → ℕ` where the distance is given by `dist x y = (1/2)^n`,
where `n` is the smallest index where `x` and `y` differ.
Not registered as a global instance by default. -/
@[instance_reducible]
/-
**PiNat.metricSpaceNatNat** 是 Mathlib 中的一个定义，位于命名空间 `PiNat`。
形式化陈述：metricSpaceNatNat : MetricSpace (Nat -> Nat)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Metric space structure on `ℕ → ℕ` where the distance is given by `dist x y = (1/
2)^n`,
where `n` is the smallest index where `x` and `y` differ.
Not registered as a global instance by default.
-/
def metricSpaceNatNat : MetricSpace (ℕ → ℕ) :=
  PiNat.metricSpaceOfDiscreteUniformity fun _ => rfl

attribute [local instance] PiNat.metricSpace
/-
**PiNat.completeSpace** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：∀ {E : ℕ → Type u_1} [inst : (n : ℕ) → TopologicalSpace (E n)] [inst_1 : ∀
 (n : ℕ), DiscreteTopology (E n)],   CompleteSpace ((n : ℕ) → E n)
参数：n : ℕ；E n；n : ℕ；E n；(n : ℕ) → E n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.complete_of_convergent_controlled_sequences`：Metric.complete_of_c
onvergent_controlled_sequences (B : Nat -> Real) (hB : forall n, 0 < B n) (H : f
orall u : Nat -> α, (forall N n m : Nat,…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_pi_nhds`：tendsto_pi_nhds {f : Y -> forall i, A i} {g : forall i,
 A i} {u : Filter Y} : Tendsto f u (𝓝 g) ↔ forall x, Tendsto (fun i => f i x) u 
(𝓝 (g…
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Ici_mem_atTop`：Ici_mem_atTop [Preorder α] (a : α) : Ici a in (atT
op : Filter α)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `PiNat.apply_eq_of_dist_lt`：apply_eq_of_dist_lt {x y : forall n, E n} {n 
: Nat} (h : dist x y < (1 / 2) ^ n) {i : Nat} (hi : i <= n) : x i = y i
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
protected theorem completeSpace : CompleteSpace (∀ n, E n) := by
  refine Metric.complete_of_convergent_controlled_sequences (fun n => (1 / 2) ^ n) (by simp) ?_
  intro u hu
  refine ⟨fun n => u n n, tendsto_pi_nhds.2 fun i => ?_⟩
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.Ici_mem_atTop i] with n hn
  exact apply_eq_of_dist_lt (hu i i n le_rfl hn) le_rfl
/-
**PiNat.boundedSpace** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：∀ {E : ℕ → Type u_1} [inst : (n : ℕ) → TopologicalSpace (E n)] [inst_1 : ∀
 (n : ℕ), DiscreteTopology (E n)],   BoundedSpace ((n : ℕ) → E n)
参数：n : ℕ；E n；n : ℕ；E n；(n : ℕ) → E n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Metric.boundedSpace_iff`：boundedSpace_iff : BoundedSpace α ↔ exists C, f
orall a b : α, dist a b <= C
· 使用定理 `PiNat.dist_le_one`：∀ {E : ℕ → Type u_1} (x y : (n : ℕ) → E n), dist x y 
≤ 1
-/
protected theorem boundedSpace : BoundedSpace (∀ n, E n) := by
  rw [Metric.boundedSpace_iff]
  use 1
  apply PiNat.dist_le_one

/-!
### Retractions inside product spaces

We show that, in a space `Π (n : ℕ), E n` where each `E n` is discrete, there is a retraction on
any closed nonempty subset `s`, i.e., a continuous map `f` from the whole space to `s` restricting
to the identity on `s`. The map `f` is defined as follows. For `x ∈ s`, let `f x = x`. Otherwise,
consider the longest prefix `w` that `x` shares with an element of `s`, and let `f x = z_w`
where `z_w` is an element of `s` starting with `w`.
-/

/-
**PiNat.exists_disjoint_cylinder** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：exists_disjoint_cylinder {s : Set (forall n, E n)} (hs : IsClosed s) {x : 
forall n, E n} (hx : x ∉ s) : exists n, Disjoint s (cylinder x n)
参数：forall n, E n；hs : IsClosed s；hx : x ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiNat.cylinder_zero`：cylinder_zero (x : forall n, E n) : cylinder x 0 = 
univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsClosed.notMem_iff_infDist_pos`：∀ {α : Type u} [inst : PseudoMetricSpac
e α] {s : Set α} {x : α},   IsClosed s → s.Nonempty → (x ∉ s ↔ 0 < Metric.infDis
t x s)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `exists_pow_lt_of_lt_one`：exists_pow_lt_of_lt_one (hx : 0 < x) (hy : y < 
1) : exists n : Nat, y ^ n < x
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `one_half_lt_one`：one_half_lt_one : (1 / 2 : α) < 1
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `Metric.infDist_le_dist_of_mem`：infDist_le_dist_of_mem (h : y in s) : inf
Dist x s <= dist x y
· 使用定理 `PiNat.mem_cylinder_iff_dist_le`：mem_cylinder_iff_dist_le {x y : forall n
, E n} {n : Nat} : y in cylinder x n ↔ dist y x <= (1 / 2) ^ n
· 使用定理 `PiNat.mem_cylinder_comm`：mem_cylinder_comm (x y : forall n, E n) (n : Na
t) : y in cylinder x n ↔ x in cylinder y n

--- 原说明 ---
### Retractions inside product spaces

We show that, in a space `Π (n : ℕ), E n` where each `E n` is discrete, there is
 a retraction on
any closed nonempty subset `s`, i.e., a continuous map `f` from the whole space 
to `s` restricting
to the identity on `s`. The map `f` is defined as follows. For `x ∈ s`, let `f x
 = x`. Otherwise,
consider the longest prefix `w` that `x` shares with an element of `s`, and let 
`f x = z_w`
where `z_w` is an element of `s` starting with `w`.
-/
theorem exists_disjoint_cylinder {s : Set (∀ n, E n)} (hs : IsClosed s) {x : ∀ n, E n}
    (hx : x ∉ s) : ∃ n, Disjoint s (cylinder x n) := by
  rcases eq_empty_or_nonempty s with (rfl | hne)
  · exact ⟨0, by simp⟩
  have A : 0 < infDist x s := (hs.notMem_iff_infDist_pos hne).1 hx
  obtain ⟨n, hn⟩ : ∃ n, (1 / 2 : ℝ) ^ n < infDist x s := exists_pow_lt_of_lt_one A one_half_lt_one
  refine ⟨n, disjoint_left.2 fun y ys hy => ?_⟩
  apply lt_irrefl (infDist x s)
  calc
    infDist x s ≤ dist x y := infDist_le_dist_of_mem ys
    _ ≤ (1 / 2) ^ n := by
      rw [mem_cylinder_comm] at hy
      exact mem_cylinder_iff_dist_le.1 hy
    _ < infDist x s := hn

open scoped Classical in
/-- Given a point `x` in a product space `Π (n : ℕ), E n`, and `s` a subset of this space, then
`shortestPrefixDiff x s` if the smallest `n` for which there is no element of `s` having the same
prefix of length `n` as `x`. If there is no such `n`, then use `0` by convention. -/
/-
**PiNat.shortestPrefixDiff** 是 Mathlib 中的一个定义，位于命名空间 `PiNat`。
形式化陈述：shortestPrefixDiff {E : Nat -> Type*} (x : forall n, E n) (s : Set (forall
 n, E n)) : Nat
参数：x : forall n, E n；s : Set (forall n, E n)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a point `x` in a product space `Π (n : ℕ), E n`, and `s` a subset of this 
space, then
`shortestPrefixDiff x s` if the smallest `n` for which there is no element of `s
` having the same
prefix of length `n` as `x`. If there is no such `n`, then use `0` by convention
.
-/
def shortestPrefixDiff {E : ℕ → Type*} (x : ∀ n, E n) (s : Set (∀ n, E n)) : ℕ :=
  if h : ∃ n, Disjoint s (cylinder x n) then Nat.find h else 0
/-
**PiNat.firstDiff_lt_shortestPrefixDiff** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：firstDiff_lt_shortestPrefixDiff {s : Set (forall n, E n)} (hs : IsClosed s
) {x y : forall n, E n} (hx : x ∉ s) (hy : y in s) : firstDiff x y < shortestPre
fixDiff x s
参数：forall n, E n；hs : IsClosed s；hx : x ∉ s；hy : y in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiNat.exists_disjoint_cylinder`：exists_disjoint_cylinder {s : Set (foral
l n, E n)} (hs : IsClosed s) {x : forall n, E n} (hx : x ∉ s) : exists n, Disjoi
nt s (cylinder x n)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiNat.shortestPrefixDiff.eq_1`：∀ {E : ℕ → Type u_2} (x : (n : ℕ) → E n) 
(s : Set ((n : ℕ) → E n)),   PiNat.shortestPrefixDiff x s = if h : ∃ n, Disjoint
 s (PiNat.cylinder …
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Set.not_disjoint_iff_nonempty_inter`：not_disjoint_iff_nonempty_inter : ¬
 Disjoint s t ↔ (s inter t).Nonempty
· 使用定理 `PiNat.mem_cylinder_comm`：mem_cylinder_comm (x y : forall n, E n) (n : Na
t) : y in cylinder x n ↔ x in cylinder y n
· 使用定理 `PiNat.cylinder_anti`：cylinder_anti (x : forall n, E n) {m n : Nat} (h : 
m <= n) : cylinder x n subseteq cylinder x m
· 使用定理 `PiNat.mem_cylinder_firstDiff`：mem_cylinder_firstDiff (x y : forall n, E 
n) : x in cylinder y (firstDiff x y)
-/
theorem firstDiff_lt_shortestPrefixDiff {s : Set (∀ n, E n)} (hs : IsClosed s) {x y : ∀ n, E n}
    (hx : x ∉ s) (hy : y ∈ s) : firstDiff x y < shortestPrefixDiff x s := by
  have A := exists_disjoint_cylinder hs hx
  rw [shortestPrefixDiff, dif_pos A]
  classical
  have B := Nat.find_spec A
  contrapose! B
  rw [not_disjoint_iff_nonempty_inter]
  refine ⟨y, hy, ?_⟩
  rw [mem_cylinder_comm]
  exact cylinder_anti y B (mem_cylinder_firstDiff x y)
/-
**PiNat.shortestPrefixDiff_pos** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：shortestPrefixDiff_pos {s : Set (forall n, E n)} (hs : IsClosed s) (hne : 
s.Nonempty) {x : forall n, E n} (hx : x ∉ s) : 0 < shortestPrefixDiff x s
参数：forall n, E n；hs : IsClosed s；hne : s.Nonempty；hx : x ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.pos`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], a < b → 0 < b
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `PiNat.firstDiff_lt_shortestPrefixDiff`：firstDiff_lt_shortestPrefixDiff {
s : Set (forall n, E n)} (hs : IsClosed s) {x y : forall n, E n} (hx : x ∉ s) (h
y : y in s) : firstDiff x y…
-/
theorem shortestPrefixDiff_pos {s : Set (∀ n, E n)} (hs : IsClosed s) (hne : s.Nonempty)
    {x : ∀ n, E n} (hx : x ∉ s) : 0 < shortestPrefixDiff x s := by
  rcases hne with ⟨y, hy⟩
  exact (firstDiff_lt_shortestPrefixDiff hs hx hy).pos

/-- Given a point `x` in a product space `Π (n : ℕ), E n`, and `s` a subset of this space, then
`longestPrefix x s` if the largest `n` for which there is an element of `s` having the same
prefix of length `n` as `x`. If there is no such `n`, use `0` by convention. -/
/-
**PiNat.longestPrefix** 是 Mathlib 中的一个定义，位于命名空间 `PiNat`。
形式化陈述：longestPrefix {E : Nat -> Type*} (x : forall n, E n) (s : Set (forall n, E
 n)) : Nat
参数：x : forall n, E n；s : Set (forall n, E n)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a point `x` in a product space `Π (n : ℕ), E n`, and `s` a subset of this 
space, then
`longestPrefix x s` if the largest `n` for which there is an element of `s` havi
ng the same
prefix of length `n` as `x`. If there is no such `n`, use `0` by convention.
-/
def longestPrefix {E : ℕ → Type*} (x : ∀ n, E n) (s : Set (∀ n, E n)) : ℕ :=
  shortestPrefixDiff x s - 1
/-
**PiNat.firstDiff_le_longestPrefix** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：firstDiff_le_longestPrefix {s : Set (forall n, E n)} (hs : IsClosed s) {x 
y : forall n, E n} (hx : x ∉ s) (hy : y in s) : firstDiff x y <= longestPrefix x
 s
参数：forall n, E n；hs : IsClosed s；hx : x ∉ s；hy : y in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiNat.longestPrefix.eq_1`：∀ {E : ℕ → Type u_2} (x : (n : ℕ) → E n) (s : 
Set ((n : ℕ) → E n)),   PiNat.longestPrefix x s = PiNat.shortestPrefixDiff x s -
 1
· 使用定理 `le_tsub_iff_right`：le_tsub_iff_right (h : a <= c) : b <= c - a ↔ b + a <
= c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `PiNat.shortestPrefixDiff_pos`：shortestPrefixDiff_pos {s : Set (forall n,
 E n)} (hs : IsClosed s) (hne : s.Nonempty) {x : forall n, E n} (hx : x ∉ s) : 0
 < shortestPrefixD…
· 使用定理 `PiNat.firstDiff_lt_shortestPrefixDiff`：firstDiff_lt_shortestPrefixDiff {
s : Set (forall n, E n)} (hs : IsClosed s) {x y : forall n, E n} (hx : x ∉ s) (h
y : y in s) : firstDiff x y…
-/
theorem firstDiff_le_longestPrefix {s : Set (∀ n, E n)} (hs : IsClosed s) {x y : ∀ n, E n}
    (hx : x ∉ s) (hy : y ∈ s) : firstDiff x y ≤ longestPrefix x s := by
  rw [longestPrefix, le_tsub_iff_right]
  · exact firstDiff_lt_shortestPrefixDiff hs hx hy
  · exact shortestPrefixDiff_pos hs ⟨y, hy⟩ hx
/-
**PiNat.inter_cylinder_longestPrefix_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：inter_cylinder_longestPrefix_nonempty {s : Set (forall n, E n)} (hs : IsCl
osed s) (hne : s.Nonempty) (x : forall n, E n) : (s inter cylinder x (longestPre
fix x s)).Nonempty
参数：forall n, E n；hs : IsClosed s；hne : s.Nonempty；x : forall n, E n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiNat.self_mem_cylinder`：self_mem_cylinder (x : forall n, E n) (n : Nat)
 : x in cylinder x n
· 使用定理 `PiNat.exists_disjoint_cylinder`：exists_disjoint_cylinder {s : Set (foral
l n, E n)} (hs : IsClosed s) {x : forall n, E n} (hx : x ∉ s) : exists n, Disjoi
nt s (cylinder x n)
· 使用定理 `Nat.pred_lt`：∀ {n : ℕ}, n ≠ 0 → n.pred < n
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `PiNat.shortestPrefixDiff_pos`：shortestPrefixDiff_pos {s : Set (forall n,
 E n)} (hs : IsClosed s) (hne : s.Nonempty) {x : forall n, E n} (hx : x ∉ s) : 0
 < shortestPrefixD…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiNat.longestPrefix.eq_1`：∀ {E : ℕ → Type u_2} (x : (n : ℕ) → E n) (s : 
Set ((n : ℕ) → E n)),   PiNat.longestPrefix x s = PiNat.shortestPrefixDiff x s -
 1
· 使用定理 `PiNat.shortestPrefixDiff.eq_1`：∀ {E : ℕ → Type u_2} (x : (n : ℕ) → E n) 
(s : Set ((n : ℕ) → E n)),   PiNat.shortestPrefixDiff x s = if h : ∃ n, Disjoint
 s (PiNat.cylinder …
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.find_min`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) {
m : ℕ}, m < Nat.find H → ¬p m
· 使用定理 `PiNat.mem_cylinder_iff_eq`：mem_cylinder_iff_eq {x y : forall n, E n} {n 
: Nat} : y in cylinder x n ↔ cylinder y n = cylinder x n
-/
theorem inter_cylinder_longestPrefix_nonempty {s : Set (∀ n, E n)} (hs : IsClosed s)
    (hne : s.Nonempty) (x : ∀ n, E n) : (s ∩ cylinder x (longestPrefix x s)).Nonempty := by
  by_cases hx : x ∈ s
  · exact ⟨x, hx, self_mem_cylinder _ _⟩
  have A := exists_disjoint_cylinder hs hx
  have B : longestPrefix x s < shortestPrefixDiff x s :=
    Nat.pred_lt (shortestPrefixDiff_pos hs hne hx).ne'
  rw [longestPrefix, shortestPrefixDiff, dif_pos A] at B ⊢
  classical
  obtain ⟨y, ys, hy⟩ : ∃ y : ∀ n : ℕ, E n, y ∈ s ∧ x ∈ cylinder y (Nat.find A - 1) := by
    simpa only [not_disjoint_iff, mem_cylinder_comm] using Nat.find_min A B
  refine ⟨y, ys, ?_⟩
  rw [mem_cylinder_iff_eq] at hy ⊢
  rw [hy]
/-
**PiNat.disjoint_cylinder_of_longestPrefix_lt** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：disjoint_cylinder_of_longestPrefix_lt {s : Set (forall n, E n)} (hs : IsCl
osed s) {x : forall n, E n} (hx : x ∉ s) {n : Nat} (hn : longestPrefix x s < n) 
: Disjoint s (cylinder x n)
参数：forall n, E n；hs : IsClosed s；hx : x ∉ s；hn : longestPrefix x s < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Set.not_disjoint_iff_nonempty_inter`：not_disjoint_iff_nonempty_inter : ¬
 Disjoint s t ↔ (s inter t).Nonempty
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `PiNat.mem_cylinder_iff_le_firstDiff`：mem_cylinder_iff_le_firstDiff {x y 
: forall n, E n} (hne : x != y) (i : Nat) : x in cylinder y i ↔ i <= firstDiff x
 y
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiNat.mem_cylinder_comm`：mem_cylinder_comm (x y : forall n, E n) (n : Na
t) : y in cylinder x n ↔ x in cylinder y n
· 使用定理 `PiNat.firstDiff_le_longestPrefix`：firstDiff_le_longestPrefix {s : Set (f
orall n, E n)} (hs : IsClosed s) {x y : forall n, E n} (hx : x ∉ s) (hy : y in s
) : firstDiff x y <= l…
-/
theorem disjoint_cylinder_of_longestPrefix_lt {s : Set (∀ n, E n)} (hs : IsClosed s) {x : ∀ n, E n}
    (hx : x ∉ s) {n : ℕ} (hn : longestPrefix x s < n) : Disjoint s (cylinder x n) := by
  contrapose! hn
  rcases not_disjoint_iff_nonempty_inter.1 hn with ⟨y, ys, hy⟩
  apply le_trans _ (firstDiff_le_longestPrefix hs hx ys)
  apply (mem_cylinder_iff_le_firstDiff (ne_of_mem_of_not_mem ys hx).symm _).1
  rwa [mem_cylinder_comm]

/-- If two points `x, y` coincide up to length `n`, and the longest common prefix of `x` with `s`
is strictly shorter than `n`, then the longest common prefix of `y` with `s` is the same, and both
cylinders of this length based at `x` and `y` coincide. -/
/-
**PiNat.cylinder_longestPrefix_eq_of_longestPrefix_lt_firstDiff** 是 Mathlib 中的一个
定理，位于命名空间 `PiNat`。
形式化陈述：cylinder_longestPrefix_eq_of_longestPrefix_lt_firstDiff {x y : forall n, E
 n} {s : Set (forall n, E n)} (hs : IsClosed s) (hne : s.Nonempty) (H : longestP
refix x s < firstDiff x y) (xs : x ∉ s) (ys : y ∉ s) : cylinder x (longestPrefix
 x s) = cylinder y (longestPrefix y s)
参数：forall n, E n；hs : IsClosed s；hne : s.Nonempty；H : longestPrefix x s < firstD
iff x y；xs : x ∉ s；ys : y ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `PiNat.inter_cylinder_longestPrefix_nonempty`：inter_cylinder_longestPrefi
x_nonempty {s : Set (forall n, E n)} (hs : IsClosed s) (hne : s.Nonempty) (x : f
orall n, E n) : (s inter cylinder…
· 使用定理 `PiNat.disjoint_cylinder_of_longestPrefix_lt`：disjoint_cylinder_of_longes
tPrefix_lt {s : Set (forall n, E n)} (hs : IsClosed s) {x : forall n, E n} (hx :
 x ∉ s) {n : Nat} (hn : longestPr…
· 使用定理 `Set.Nonempty.not_disjoint`：∀ {α : Type u} {s t : Set α}, (s ∩ t).Nonempt
y → ¬Disjoint s t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiNat.cylinder_eq_cylinder_of_le_firstDiff`：cylinder_eq_cylinder_of_le_f
irstDiff (x y : forall n, E n) {n : Nat} (hn : n <= firstDiff x y) : cylinder x 
n = cylinder y n
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `PiNat.firstDiff_comm`：firstDiff_comm (x y : forall n, E n) : firstDiff x
 y = firstDiff y x
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `Set.inter_subset_inter_right`：inter_subset_inter_right {s t : Set α} (u 
: Set α) (H : s subseteq t) : u inter s subseteq u inter t
· 使用定理 `PiNat.cylinder_anti`：cylinder_anti (x : forall n, E n) {m n : Nat} (h : 
m <= n) : cylinder x n subseteq cylinder x m
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PiNat.mem_cylinder_iff_eq`：mem_cylinder_iff_eq {x y : forall n, E n} {n 
: Nat} : y in cylinder x n ↔ cylinder y n = cylinder x n
· 使用定理 `PiNat.mem_cylinder_firstDiff`：mem_cylinder_firstDiff (x y : forall n, E 
n) : x in cylinder y (firstDiff x y)

--- 原说明 ---
If two points `x, y` coincide up to length `n`, and the longest common prefix of
 `x` with `s`
is strictly shorter than `n`, then the longest common prefix of `y` with `s` is 
the same, and both
cylinders of this length based at `x` and `y` coincide.
-/
theorem cylinder_longestPrefix_eq_of_longestPrefix_lt_firstDiff {x y : ∀ n, E n}
    {s : Set (∀ n, E n)} (hs : IsClosed s) (hne : s.Nonempty)
    (H : longestPrefix x s < firstDiff x y) (xs : x ∉ s) (ys : y ∉ s) :
    cylinder x (longestPrefix x s) = cylinder y (longestPrefix y s) := by
  have l_eq : longestPrefix y s = longestPrefix x s := by
    rcases lt_trichotomy (longestPrefix y s) (longestPrefix x s) with (L | L | L)
    · have Ax : (s ∩ cylinder x (longestPrefix x s)).Nonempty :=
        inter_cylinder_longestPrefix_nonempty hs hne x
      have Z := disjoint_cylinder_of_longestPrefix_lt hs ys L
      rw [firstDiff_comm] at H
      rw [cylinder_eq_cylinder_of_le_firstDiff _ _ H.le] at Z
      exact (Ax.not_disjoint Z).elim
    · exact L
    · have Ay : (s ∩ cylinder y (longestPrefix y s)).Nonempty :=
        inter_cylinder_longestPrefix_nonempty hs hne y
      have A'y : (s ∩ cylinder y (longestPrefix x s).succ).Nonempty :=
        Ay.mono (inter_subset_inter_right s (cylinder_anti _ L))
      have Z := disjoint_cylinder_of_longestPrefix_lt hs xs (Nat.lt_succ_self _)
      rw [cylinder_eq_cylinder_of_le_firstDiff _ _ H] at Z
      exact (A'y.not_disjoint Z).elim
  rw [l_eq, ← mem_cylinder_iff_eq]
  exact cylinder_anti y H.le (mem_cylinder_firstDiff x y)

/-- Given a closed nonempty subset `s` of `Π (n : ℕ), E n`, there exists a Lipschitz retraction
onto this set, i.e., a Lipschitz map with range equal to `s`, equal to the identity on `s`. -/
/-
**PiNat.exists_lipschitz_retraction_of_isClosed** 是 Mathlib 中的一个定理，位于命名空间 `PiNat
`。
形式化陈述：exists_lipschitz_retraction_of_isClosed {s : Set (forall n, E n)} (hs : Is
Closed s) (hne : s.Nonempty) : exists f : (forall n, E n) -> forall n, E n, (for
all x in s, f x = x) ∧ range f = s ∧ LipschitzWith 1 f
参数：forall n, E n；hs : IsClosed s；hne : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiNat.inter_cylinder_longestPrefix_nonempty`：inter_cylinder_longestPrefi
x_nonempty {s : Set (forall n, E n)} (hs : IsClosed s) (hne : s.Nonempty) (x : f
orall n, E n) : (s inter cylinder…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `LipschitzWith.mk_one`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSp
ace α] [inst_1 : PseudoMetricSpace β] {f : α → β},   (∀ (x y : α), dist (f x) (f
 y) ≤ dist…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `PiNat.mem_cylinder_iff_eq`：mem_cylinder_iff_eq {x y : forall n, E n} {n 
: Nat} : y in cylinder x n ↔ cylinder y n = cylinder x n
· 使用定理 `PiNat.mem_cylinder_firstDiff`：mem_cylinder_firstDiff (x y : forall n, E 
n) : x in cylinder y (firstDiff x y)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `PiNat.firstDiff_comm`：firstDiff_comm (x y : forall n, E n) : firstDiff x
 y = firstDiff y x
· 使用定理 `PiNat.cylinder_anti`：cylinder_anti (x : forall n, E n) {m n : Nat} (h : 
m <= n) : cylinder x n subseteq cylinder x m
· 使用定理 `PiNat.firstDiff_le_longestPrefix`：firstDiff_le_longestPrefix {s : Set (f
orall n, E n)} (hs : IsClosed s) {x y : forall n, E n} (hx : x ∉ s) (hy : y in s
) : firstDiff x y <= l…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Nonempty.some_mem`：∀ {α : Type u} {s : Set α} (h : s.Nonempty), h.so
me ∈ s
· 使用定理 `PiNat.mem_cylinder_iff_le_firstDiff`：mem_cylinder_iff_le_firstDiff {x y 
: forall n, E n} (hne : x != y) (i : Nat) : x in cylinder y i ↔ i <= firstDiff x
 y
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `PiNat.cylinder_longestPrefix_eq_of_longestPrefix_lt_firstDiff`：cylinder_
longestPrefix_eq_of_longestPrefix_lt_firstDiff {x y : forall n, E n} {s : Set (f
orall n, E n)} (hs : IsClosed s) (hne : s.Nonempty)…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
Given a closed nonempty subset `s` of `Π (n : ℕ), E n`, there exists a Lipschitz
 retraction
onto this set, i.e., a Lipschitz map with range equal to `s`, equal to the ident
ity on `s`.
-/
theorem exists_lipschitz_retraction_of_isClosed {s : Set (∀ n, E n)} (hs : IsClosed s)
    (hne : s.Nonempty) :
    ∃ f : (∀ n, E n) → ∀ n, E n, (∀ x ∈ s, f x = x) ∧ range f = s ∧ LipschitzWith 1 f := by
  /- The map `f` is defined as follows. For `x ∈ s`, let `f x = x`. Otherwise, consider the longest
    prefix `w` that `x` shares with an element of `s`, and let `f x = z_w` where `z_w` is an element
    of `s` starting with `w`. All the desired properties are clear, except the fact that `f` is
    `1`-Lipschitz: if two points `x, y` belong to a common cylinder of length `n`, one should show
    that their images also belong to a common cylinder of length `n`. This is a case analysis:
    * if both `x, y ∈ s`, then this is clear.
    * if `x ∈ s` but `y ∉ s`, then the longest prefix `w` of `y` shared by an element of `s` is of
    length at least `n` (because of `x`), and then `f y` starts with `w` and therefore stays in the
    same length `n` cylinder.
    * if `x ∉ s`, `y ∉ s`, let `w` be the longest prefix of `x` shared by an element of `s`. If its
    length is `< n`, then it is also the longest prefix of `y`, and we get `f x = f y = z_w`.
    Otherwise, `f x` remains in the same `n`-cylinder as `x`. Similarly for `y`. Finally, `f x` and
    `f y` are again in the same `n`-cylinder, as desired. -/
  classical
  set f := fun x => if x ∈ s then x else (inter_cylinder_longestPrefix_nonempty hs hne x).some
  have fs : ∀ x ∈ s, f x = x := fun x xs => by simp [f, xs]
  refine ⟨f, fs, ?_, ?_⟩
  -- check that the range of `f` is `s`.
  · apply Subset.antisymm
    · rintro x ⟨y, rfl⟩
      by_cases hy : y ∈ s
      · rwa [fs y hy]
      simpa [f, if_neg hy] using! (inter_cylinder_longestPrefix_nonempty hs hne y).choose_spec.1
    · intro x hx
      rw [← fs x hx]
      exact mem_range_self _
  -- check that `f` is `1`-Lipschitz, by a case analysis.
  · refine LipschitzWith.mk_one fun x y => ?_
    -- exclude the trivial cases where `x = y`, or `f x = f y`.
    rcases eq_or_ne x y with (rfl | hxy)
    · simp
    rcases eq_or_ne (f x) (f y) with (h' | hfxfy)
    · simp [h']
    have I2 : cylinder x (firstDiff x y) = cylinder y (firstDiff x y) := by
      rw [← mem_cylinder_iff_eq]
      apply mem_cylinder_firstDiff
    suffices firstDiff x y ≤ firstDiff (f x) (f y) by
      simpa [dist_eq_of_ne hxy, dist_eq_of_ne hfxfy]
    -- case where `x ∈ s`
    by_cases xs : x ∈ s
    · rw [fs x xs] at hfxfy ⊢
      -- case where `y ∈ s`, trivial
      by_cases ys : y ∈ s
      · rw [fs y ys]
      -- case where `y ∉ s`
      have A : (s ∩ cylinder y (longestPrefix y s)).Nonempty :=
        inter_cylinder_longestPrefix_nonempty hs hne y
      have fy : f y = A.some := by simp_rw [f, if_neg ys]
      have I : cylinder A.some (firstDiff x y) = cylinder y (firstDiff x y) := by
        rw [← mem_cylinder_iff_eq, firstDiff_comm]
        apply cylinder_anti y _ A.some_mem.2
        exact firstDiff_le_longestPrefix hs ys xs
      rwa [← fy, ← I2, ← mem_cylinder_iff_eq, mem_cylinder_iff_le_firstDiff hfxfy.symm,
        firstDiff_comm _ x] at I
    -- case where `x ∉ s`
    · by_cases ys : y ∈ s
      -- case where `y ∈ s` (similar to the above)
      · have A : (s ∩ cylinder x (longestPrefix x s)).Nonempty :=
          inter_cylinder_longestPrefix_nonempty hs hne x
        have fx : f x = A.some := by simp_rw [f, if_neg xs]
        have I : cylinder A.some (firstDiff x y) = cylinder x (firstDiff x y) := by
          rw [← mem_cylinder_iff_eq]
          apply cylinder_anti x _ A.some_mem.2
          apply firstDiff_le_longestPrefix hs xs ys
        rw [fs y ys] at hfxfy ⊢
        rwa [← fx, I2, ← mem_cylinder_iff_eq, mem_cylinder_iff_le_firstDiff hfxfy] at I
      -- case where `y ∉ s`
      · have Ax : (s ∩ cylinder x (longestPrefix x s)).Nonempty :=
          inter_cylinder_longestPrefix_nonempty hs hne x
        have fx : f x = Ax.some := by simp_rw [f, if_neg xs]
        have Ay : (s ∩ cylinder y (longestPrefix y s)).Nonempty :=
          inter_cylinder_longestPrefix_nonempty hs hne y
        have fy : f y = Ay.some := by simp_rw [f, if_neg ys]
        -- case where the common prefix to `x` and `s`, or `y` and `s`, is shorter than the
        -- common part to `x` and `y` -- then `f x = f y`.
        by_cases! H : longestPrefix x s < firstDiff x y ∨ longestPrefix y s < firstDiff x y
        · have : cylinder x (longestPrefix x s) = cylinder y (longestPrefix y s) := by
            rcases H with H | H
            · exact cylinder_longestPrefix_eq_of_longestPrefix_lt_firstDiff hs hne H xs ys
            · symm
              rw [firstDiff_comm] at H
              exact cylinder_longestPrefix_eq_of_longestPrefix_lt_firstDiff hs hne H ys xs
          rw [fx, fy] at hfxfy
          apply (hfxfy _).elim
          congr
        -- case where the common prefix to `x` and `s` is long, as well as the common prefix to
        -- `y` and `s`. Then all points remain in the same cylinders.
        · have I1 : cylinder Ax.some (firstDiff x y) = cylinder x (firstDiff x y) := by
            rw [← mem_cylinder_iff_eq]
            exact cylinder_anti x H.1 Ax.some_mem.2
          have I3 : cylinder y (firstDiff x y) = cylinder Ay.some (firstDiff x y) := by
            rw [eq_comm, ← mem_cylinder_iff_eq]
            exact cylinder_anti y H.2 Ay.some_mem.2
          have : cylinder Ax.some (firstDiff x y) = cylinder Ay.some (firstDiff x y) := by
            rw [I1, I2, I3]
          rw [← fx, ← fy, ← mem_cylinder_iff_eq, mem_cylinder_iff_le_firstDiff hfxfy] at this
          exact this

/-- Given a closed nonempty subset `s` of `Π (n : ℕ), E n`, there exists a retraction onto this
set, i.e., a continuous map with range equal to `s`, equal to the identity on `s`. -/
/-
**PiNat.exists_retraction_of_isClosed** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：exists_retraction_of_isClosed {s : Set (forall n, E n)} (hs : IsClosed s) 
(hne : s.Nonempty) : exists f : (forall n, E n) -> forall n, E n, (forall x in s
, f x = x) ∧ range f = s ∧ Continuous f
参数：forall n, E n；hs : IsClosed s；hne : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiNat.exists_lipschitz_retraction_of_isClosed`：exists_lipschitz_retracti
on_of_isClosed {s : Set (forall n, E n)} (hs : IsClosed s) (hne : s.Nonempty) : 
exists f : (forall n, E n) -> foral…
· 使用定理 `LipschitzWith.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMet
ricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   Lipschit
zWith K f → Co…

--- 原说明 ---
Given a closed nonempty subset `s` of `Π (n : ℕ), E n`, there exists a retractio
n onto this
set, i.e., a continuous map with range equal to `s`, equal to the identity on `s
`.
-/
theorem exists_retraction_of_isClosed {s : Set (∀ n, E n)} (hs : IsClosed s) (hne : s.Nonempty) :
    ∃ f : (∀ n, E n) → ∀ n, E n, (∀ x ∈ s, f x = x) ∧ range f = s ∧ Continuous f := by
  rcases exists_lipschitz_retraction_of_isClosed hs hne with ⟨f, fs, frange, hf⟩
  exact ⟨f, fs, frange, hf.continuous⟩
/-
**PiNat.exists_retraction_subtype_of_isClosed** 是 Mathlib 中的一个定理，位于命名空间 `PiNat`。
形式化陈述：exists_retraction_subtype_of_isClosed {s : Set (forall n, E n)} (hs : IsCl
osed s) (hne : s.Nonempty) : exists f : (forall n, E n) -> s, (forall x : s, f x
 = x) ∧ Surjective f ∧ Continuous f
参数：forall n, E n；hs : IsClosed s；hne : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiNat.exists_retraction_of_isClosed`：exists_retraction_of_isClosed {s : 
Set (forall n, E n)} (hs : IsClosed s) (hne : s.Nonempty) : exists f : (forall n
, E n) -> forall n, E n, …
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
theorem exists_retraction_subtype_of_isClosed {s : Set (∀ n, E n)} (hs : IsClosed s)
    (hne : s.Nonempty) :
    ∃ f : (∀ n, E n) → s, (∀ x : s, f x = x) ∧ Surjective f ∧ Continuous f := by
  obtain ⟨f, fs, rfl, f_cont⟩ :
    ∃ f : (∀ n, E n) → ∀ n, E n, (∀ x ∈ s, f x = x) ∧ range f = s ∧ Continuous f :=
    exists_retraction_of_isClosed hs hne
  have A : ∀ x : range f, rangeFactorization f x = x := fun x ↦ Subtype.ext <| fs x x.2
  exact ⟨rangeFactorization f, A, fun x => ⟨x, A x⟩, f_cont.subtype_mk _⟩

end PiNat

open PiNat

/-- Any nonempty complete second countable metric space is the continuous image of the
fundamental space `ℕ → ℕ`. For a version of this theorem in the context of Polish spaces, see
`exists_nat_nat_continuous_surjective_of_polishSpace`. -/
/-
**exists_nat_nat_continuous_surjective_of_completeSpace** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：exists_nat_nat_continuous_surjective_of_completeSpace (α : Type*) [MetricS
pace α] [CompleteSpace α] [SecondCountableTopology α] [Nonempty α] : exists f : 
(Nat -> Nat) -> α, Continuous f ∧ Surjective f
参数：α : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_lt_true`：isNNRat_lt_true [Semiring α] [Line
arOrder α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Nat} -> {da db : Nat}
 -> IsNNRat a na da -> IsN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `TopologicalSpace.exists_dense_seq`：exists_dense_seq [SeparableSpace α] [
Nonempty α] : exists u : Nat -> α, DenseRange u
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iInter`：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ 
forall i, x in s i
· 使用定理 `Set.Nonempty.some_mem`：∀ {α : Type u} {s : Set α} (h : s.Nonempty), h.so
me ∈ s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `continuousAt_of_locally_lipschitz`：continuousAt_of_locally_lipschitz {f 
: α -> β} {x : α} {r : Real} (hr : 0 < r) (K : Real) (h : forall y, dist y x < r
 -> dist (f y) (f x) <=…
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 128 条，此处仅展示前 30 条）

--- 原说明 ---
Any nonempty complete second countable metric space is the continuous image of t
he
fundamental space `ℕ → ℕ`. For a version of this theorem in the context of Polis
h spaces, see
`exists_nat_nat_continuous_surjective_of_polishSpace`.
-/
theorem exists_nat_nat_continuous_surjective_of_completeSpace (α : Type*) [MetricSpace α]
    [CompleteSpace α] [SecondCountableTopology α] [Nonempty α] :
    ∃ f : (ℕ → ℕ) → α, Continuous f ∧ Surjective f := by
  /- First, we define a surjective map from a closed subset `s` of `ℕ → ℕ`. Then, we compose
    this map with a retraction of `ℕ → ℕ` onto `s` to obtain the desired map.
    Let us consider a dense sequence `u` in `α`. Then `s` is the set of sequences `xₙ` such that the
    balls `closedBall (u xₙ) (1/2^n)` have a nonempty intersection. This set is closed,
    and we define `f x` there to be the unique point in the intersection.
    This function is continuous and surjective by design. -/
  let : MetricSpace (ℕ → ℕ) := PiNat.metricSpaceNatNat
  have I0 : (0 : ℝ) < 1 / 2 := by simp
  have I1 : (1 / 2 : ℝ) < 1 := by norm_num
  rcases exists_dense_seq α with ⟨u, hu⟩
  let s : Set (ℕ → ℕ) := { x | (⋂ n : ℕ, closedBall (u (x n)) ((1 / 2) ^ n)).Nonempty }
  let g : s → α := fun x => x.2.some
  have A : ∀ (x : s) (n : ℕ), dist (g x) (u ((x : ℕ → ℕ) n)) ≤ (1 / 2) ^ n := fun x n =>
    (mem_iInter.1 x.2.some_mem n :)
  have g_cont : Continuous g := by
    refine continuous_iff_continuousAt.2 fun y => ?_
    refine continuousAt_of_locally_lipschitz zero_lt_one 4 fun x hxy => ?_
    rcases eq_or_ne x y with (rfl | hne)
    · simp
    have hne' : x.1 ≠ y.1 := Subtype.coe_injective.ne hne
    have dist' : dist x y = dist x.1 y.1 := rfl
    let n := firstDiff x.1 y.1 - 1
    have diff_pos : 0 < firstDiff x.1 y.1 := by
      by_contra! h
      apply apply_firstDiff_ne hne'
      rw [Nat.le_zero.1 h]
      apply apply_eq_of_dist_lt _ le_rfl
      rw [pow_zero]
      exact hxy
    have hn : firstDiff x.1 y.1 = n + 1 := (Nat.succ_pred_eq_of_pos diff_pos).symm
    rw [dist', dist_eq_of_ne hne', hn]
    have B : x.1 n = y.1 n := mem_cylinder_firstDiff x.1 y.1 n (Nat.pred_lt diff_pos.ne')
    calc
      dist (g x) (g y) ≤ dist (g x) (u (x.1 n)) + dist (g y) (u (x.1 n)) :=
        dist_triangle_right _ _ _
      _ = dist (g x) (u (x.1 n)) + dist (g y) (u (y.1 n)) := by rw [← B]
      _ ≤ (1 / 2) ^ n + (1 / 2) ^ n := add_le_add (A x n) (A y n)
      _ = 4 * (1 / 2) ^ (n + 1) := by ring
  have g_surj : Surjective g := fun y ↦ by
    have : ∀ n : ℕ, ∃ j, y ∈ closedBall (u j) ((1 / 2) ^ n) := fun n ↦ by
      rcases hu.exists_dist_lt y (by simp : (0 : ℝ) < (1 / 2) ^ n) with ⟨j, hj⟩
      exact ⟨j, hj.le⟩
    choose x hx using this
    have I : (⋂ n : ℕ, closedBall (u (x n)) ((1 / 2) ^ n)).Nonempty := ⟨y, mem_iInter.2 hx⟩
    refine ⟨⟨x, I⟩, ?_⟩
    refine dist_le_zero.1 ?_
    have J : ∀ n : ℕ, dist (g ⟨x, I⟩) y ≤ (1 / 2) ^ n + (1 / 2) ^ n := fun n =>
      calc
        dist (g ⟨x, I⟩) y ≤ dist (g ⟨x, I⟩) (u (x n)) + dist y (u (x n)) :=
          dist_triangle_right _ _ _
        _ ≤ (1 / 2) ^ n + (1 / 2) ^ n := add_le_add (A ⟨x, I⟩ n) (hx n)
    have L : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n + (1 / 2) ^ n) atTop (𝓝 (0 + 0)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one I0.le I1).add
        (tendsto_pow_atTop_nhds_zero_of_lt_one I0.le I1)
    rw [add_zero] at L
    exact ge_of_tendsto' L J
  have s_closed : IsClosed s := by
    refine isClosed_iff_clusterPt.mpr fun x hx ↦ ?_
    have L : Tendsto (fun n : ℕ => diam (closedBall (u (x n)) ((1 / 2) ^ n))) atTop (𝓝 0) := by
      have : Tendsto (fun n : ℕ => (2 : ℝ) * (1 / 2) ^ n) atTop (𝓝 (2 * 0)) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one I0.le I1).const_mul _
      rw [mul_zero] at this
      exact
        squeeze_zero (fun n => diam_nonneg) (fun n => diam_closedBall (pow_nonneg I0.le _)) this
    refine nonempty_iInter_of_nonempty_biInter (fun n => isClosed_closedBall)
      (fun n => isBounded_closedBall) (fun N ↦ ?_) L
    obtain ⟨y, hxy, ys⟩ : ∃ y, y ∈ ball x ((1 / 2) ^ N) ∩ s :=
      clusterPt_principal_iff.1 hx _ (ball_mem_nhds x (pow_pos I0 N))
    have E :
      ⋂ (n : ℕ) (H : n ≤ N), closedBall (u (x n)) ((1 / 2) ^ n) =
        ⋂ (n : ℕ) (H : n ≤ N), closedBall (u (y n)) ((1 / 2) ^ n) := by
      refine iInter_congr fun n ↦ iInter_congr fun hn ↦ ?_
      have : x n = y n := apply_eq_of_dist_lt (mem_ball'.1 hxy) hn
      rw [this]
    rw [E]
    apply Nonempty.mono _ ys
    apply iInter_subset_iInter₂
  obtain ⟨f, -, f_surj, f_cont⟩ :
    ∃ f : (ℕ → ℕ) → s, (∀ x : s, f x = x) ∧ Surjective f ∧ Continuous f := by
    apply exists_retraction_subtype_of_isClosed s_closed
    simpa only [nonempty_coe_sort] using g_surj.nonempty
  exact ⟨g ∘ f, g_cont.comp f_cont, g_surj.comp f_surj⟩

open Encodable ENNReal
namespace PiCountable

/-!
### Products of (possibly non-discrete) metric spaces
-/

variable {ι : Type*} [Encodable ι] {F : ι → Type*}

section EDist
variable [∀ i, EDist (F i)] {x y : ∀ i, F i} {i : ι} {r : ℝ≥0∞}

/-- Given a countable family of extended metric spaces,
one may put an extended distance on their product `Π i, E i`.

It is highly non-canonical, though, and therefore not registered as a global instance.
The distance we use here is `edist x y = ∑' i, min (1/2)^(encode i) (edist (x i) (y i))`. -/
@[instance_reducible]
/-
**PiCountable.edist** 是 Mathlib 中的一个定义，位于命名空间 `PiCountable`。
形式化陈述：{ι : Type u_2} → [Encodable ι] → {F : ι → Type u_3} → [(i : ι) → EDist (F 
i)] → EDist ((i : ι) → F i)
参数：i : ι；F i；(i : ι) → F i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a countable family of extended metric spaces,
one may put an extended distance on their product `Π i, E i`.

It is highly non-canonical, though, and therefore not registered as a global ins
tance.
The distance we use here is `edist x y = ∑' i, min (1/2)^(encode i) (edist (x i)
 (y i))`.
-/
protected def edist : EDist (∀ i, F i) where
  edist x y := ∑' i, min (2⁻¹ ^ encode i) (edist (x i) (y i))

attribute [scoped instance] PiCountable.edist
/-
**PiCountable.edist_eq_tsum** 是 Mathlib 中的一个引理，位于命名空间 `PiCountable`。
形式化陈述：edist_eq_tsum (x y : forall i, F i) : edist x y = ∑' i, min (2⁻¹ ^ encode 
i) (edist (x i) (y i))
参数：x y : forall i, F i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma edist_eq_tsum (x y : ∀ i, F i) :
    edist x y = ∑' i, min (2⁻¹ ^ encode i) (edist (x i) (y i)) := rfl
/-
**PiCountable.min_edist_le_edist_pi** 是 Mathlib 中的一个引理，位于命名空间 `PiCountable`。
形式化陈述：min_edist_le_edist_pi (x y : forall i, F i) (i : ι) : min (2⁻¹ ^ encode i)
 (edist (x i) (y i)) <= edist x y
参数：x y : forall i, F i；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.le_tsum`：∀ {α : Type u_1} {f : α → ENNReal} (a : α), f a ≤ ∑' (a
 : α), f a
-/
lemma min_edist_le_edist_pi (x y : ∀ i, F i) (i : ι) :
    min (2⁻¹ ^ encode i) (edist (x i) (y i)) ≤ edist x y := ENNReal.le_tsum _
/-
**PiCountable.edist_le_two** 是 Mathlib 中的一个引理，位于命名空间 `PiCountable`。
形式化陈述：edist_le_two : edist x y <= 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a → 
c ≤ b → c ≤ a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `ENNReal.tsum_geometric_two_encode_le_two`：ENNReal.tsum_geometric_two_enc
ode_le_two {ι : Type*} [Encodable ι] : ∑' i : ι, (2⁻¹ : Real>=0∞) ^ encode i <= 
2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PiCountable.edist_eq_tsum`：edist_eq_tsum (x y : forall i, F i) : edist x
 y = ∑' i, min (2⁻¹ ^ encode i) (edist (x i) (y i))
· 使用定理 `Summable.tsum_le_tsum`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFil
ter ι} [inst : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [
inst_3 : To…
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
-/
lemma edist_le_two : edist x y ≤ 2 :=
  (ENNReal.tsum_geometric_two_encode_le_two).trans' <| by
    rw [edist_eq_tsum]; gcongr; exact min_le_left ..
/-
**PiCountable.edist_lt_top** 是 Mathlib 中的一个引理，位于命名空间 `PiCountable`。
形式化陈述：edist_lt_top : edist x y < ∞
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `PiCountable.edist_le_two`：edist_le_two : edist x y <= 2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma edist_lt_top : edist x y < ∞ := edist_le_two.trans_lt (by simp)
/-
**PiCountable.edist_le_edist_pi_of_edist_lt** 是 Mathlib 中的一个引理，位于命名空间 `PiCountab
le`。
形式化陈述：edist_le_edist_pi_of_edist_lt (h : edist x y < 2⁻¹ ^ encode i) : edist (x 
i) (y i) <= edist x y
参数：h : edist x y < 2⁻¹ ^ encode i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `min_le_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, min b c ≤
 a ↔ b ≤ a ∨ c ≤ a
· 使用引理 `PiCountable.min_edist_le_edist_pi`：min_edist_le_edist_pi (x y : forall i
, F i) (i : ι) : min (2⁻¹ ^ encode i) (edist (x i) (y i)) <= edist x y
-/
lemma edist_le_edist_pi_of_edist_lt (h : edist x y < 2⁻¹ ^ encode i) :
    edist (x i) (y i) ≤ edist x y := by
  simpa only [not_le.2 h, false_or] using min_le_iff.1 (min_edist_le_edist_pi x y i)

end EDist

attribute [scoped instance] PiCountable.edist

section PseudoEMetricSpace
variable [∀ i, PseudoEMetricSpace (F i)]

/-- Given a countable family of extended pseudometric spaces,
one may put an extended distance on their product `Π i, E i`.

It is highly non-canonical, though, and therefore not registered as a global instance.
The distance we use here is `edist x y = ∑' i, min (1/2)^(encode i) (edist (x i) (y i))`. -/
@[instance_reducible]
/-
**PiCountable.pseudoEMetricSpace** 是 Mathlib 中的一个定义，位于命名空间 `PiCountable`。
形式化陈述：{ι : Type u_2} →   [Encodable ι] → {F : ι → Type u_3} → [(i : ι) → PseudoE
MetricSpace (F i)] → PseudoEMetricSpace ((i : ι) → F i)
参数：i : ι；F i；(i : ι) → F i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a countable family of extended pseudometric spaces,
one may put an extended distance on their product `Π i, E i`.

It is highly non-canonical, though, and therefore not registered as a global ins
tance.
The distance we use here is `edist x y = ∑' i, min (1/2)^(encode i) (edist (x i)
 (y i))`.
-/
protected def pseudoEMetricSpace : PseudoEMetricSpace (∀ i, F i) where
  edist_self x := by simp [edist_eq_tsum]
  edist_comm x y := by simp [edist_eq_tsum, edist_comm]
  edist_triangle x y z := calc
        ∑' i, min (2⁻¹ ^ encode i) (edist (x i) (z i))
    _ ≤ ∑' i, (min (2⁻¹ ^ encode i) (edist (x i) (y i)) +
         min (2⁻¹ ^ encode i) (edist (y i) (z i))) := by
      gcongr with n; grw [edist_triangle _ (y n), min_add_distrib, min_le_right]
    _ = _ := ENNReal.tsum_add ..
  toUniformSpace := Pi.uniformSpace _
  uniformity_edist := by
    simp only [Pi.uniformity, comap_iInf, gt_iff_lt, preimage_ofPred_eq, comap_principal,
      PseudoEMetricSpace.uniformity_edist, le_antisymm_iff, le_iInf_iff, le_principal_iff]
    constructor
    · intro ε hε
      obtain ⟨K, hK⟩ : ∃ K : Finset ι, ∑' i : {j // j ∉ K}, 2⁻¹ ^ encode (i : ι) < ε / 2 :=
        ((tendsto_order.1 <| ENNReal.tendsto_tsum_compl_atTop_zero
          (tsum_geometric_encode_lt_top ENNReal.one_half_lt_one).ne).2 _
            <| by simpa using hε.ne').exists
      obtain ⟨δ, δpos, hδ⟩ : ∃ δ, 0 < δ ∧ δ * K.card < ε / 2 :=
        ENNReal.exists_pos_mul_lt (by simp) (by simpa using hε.ne')
      apply @mem_iInf_of_iInter _ _ _ _ _ K.finite_toSet fun i =>
          {p : (∀ i : ι, F i) × ∀ i : ι, F i | edist (p.fst i) (p.snd i) < δ}
      · rintro ⟨i, hi⟩
        refine mem_iInf_of_mem δ (mem_iInf_of_mem δpos ?_)
        simp only [mem_principal, Subset.rfl]
      · rintro ⟨x, y⟩ hxy
        simp only [mem_iInter, mem_ofPred_eq, SetCoe.forall, Finset.mem_coe] at hxy
        calc
          edist x y = ∑' i : ι, min (2⁻¹ ^ encode i) (edist (x i) (y i)) := rfl
          _ = ∑ i ∈ K, min (2⁻¹ ^ encode i) (edist (x i) (y i)) +
                ∑' i : ↑(K : Set ι)ᶜ, min (2⁻¹ ^ encode (i : ι)) (edist (x i) (y i)) :=
            (ENNReal.sum_add_tsum_compl ..).symm
          _ ≤ ∑ i ∈ K, edist (x i) (y i) + ∑' i : ↑(K : Set ι)ᶜ, 2⁻¹ ^ encode (i : ι) := by
            gcongr
            · apply min_le_right
            · apply min_le_left
          _ < ∑ _i ∈ K, δ + ε / 2 := by
            refine ENNReal.add_lt_add_of_le_of_lt (by simpa using fun i hi ↦ (hxy i hi).ne_top) ?_
              hK
            gcongr with i hi
            exact (hxy i hi).le
          _ ≤ ε / 2 + ε / 2 := by gcongr; simpa [mul_comm] using hδ.le
          _ = ε := ENNReal.add_halves _
    · intro i ε hε₀
      have : (0 : ℝ≥0∞) < 2⁻¹ ^ encode i := ENNReal.pow_pos (by norm_num) _
      refine mem_iInf_of_mem (min (2⁻¹ ^ encode i) ε) <| mem_iInf_of_mem (by positivity) ?_
      simp only [and_imp, Prod.forall, ofPred_subset_ofPred, lt_min_iff, mem_principal]
      intro x y hn
      exact (edist_le_edist_pi_of_edist_lt hn).trans_lt

end PseudoEMetricSpace

attribute [scoped instance] PiCountable.pseudoEMetricSpace

section EMetricSpace
variable [∀ i, EMetricSpace (F i)]

/-- Given a countable family of extended metric spaces,
one may put an extended distance on their product `Π i, E i`.

It is highly non-canonical, though, and therefore not registered as a global instance.
The distance we use here is `edist x y = ∑' i, min (1/2)^(encode i) (edist (x i) (y i))`. -/
@[instance_reducible]
/-
**PiCountable.emetricSpace** 是 Mathlib 中的一个定义，位于命名空间 `PiCountable`。
形式化陈述：{ι : Type u_2} → [Encodable ι] → {F : ι → Type u_3} → [(i : ι) → EMetricSp
ace (F i)] → EMetricSpace ((i : ι) → F i)
参数：i : ι；F i；(i : ι) → F i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a countable family of extended metric spaces,
one may put an extended distance on their product `Π i, E i`.

It is highly non-canonical, though, and therefore not registered as a global ins
tance.
The distance we use here is `edist x y = ∑' i, min (1/2)^(encode i) (edist (x i)
 (y i))`.
-/
protected def emetricSpace : EMetricSpace (∀ i, F i) where
  eq_of_edist_eq_zero := by simp [edist_eq_tsum, funext_iff]

end EMetricSpace

attribute [scoped instance] PiCountable.emetricSpace

section PseudoMetricSpace
variable [∀ i, PseudoMetricSpace (F i)] {x y : ∀ i, F i} {i : ι}


/-- Given a countable family of metric spaces, one may put a distance on their product `Π i, E i`.

It is highly non-canonical, though, and therefore not registered as a global instance.
The distance we use here is `dist x y = ∑' i, min (1/2)^(encode i) (dist (x i) (y i))`. -/
@[instance_reducible]
/-
**PiCountable.dist** 是 Mathlib 中的一个定义，位于命名空间 `PiCountable`。
形式化陈述：{ι : Type u_2} → [Encodable ι] → {F : ι → Type u_3} → [(i : ι) → PseudoMet
ricSpace (F i)] → Dist ((i : ι) → F i)
参数：i : ι；F i；(i : ι) → F i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a countable family of metric spaces, one may put a distance on their produ
ct `Π i, E i`.

It is highly non-canonical, though, and therefore not registered as a global ins
tance.
The distance we use here is `dist x y = ∑' i, min (1/2)^(encode i) (dist (x i) (
y i))`.
-/
protected def dist : Dist (∀ i, F i) where
  dist x y := ∑' i, min (2⁻¹ ^ encode i) (dist (x i) (y i))

attribute [scoped instance] PiCountable.dist
/-
**PiCountable.dist_eq_tsum** 是 Mathlib 中的一个引理，位于命名空间 `PiCountable`。
形式化陈述：dist_eq_tsum (x y : forall i, F i) : dist x y = ∑' i, min (2⁻¹ ^ encode i)
 (dist (x i) (y i))
参数：x y : forall i, F i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma dist_eq_tsum (x y : ∀ i, F i) : dist x y = ∑' i, min (2⁻¹ ^ encode i) (dist (x i) (y i)) :=
  rfl
/-
**PiCountable.dist_summable** 是 Mathlib 中的一个引理，位于命名空间 `PiCountable`。
形式化陈述：dist_summable (x y : forall i, F i) : Summable fun i => min (2⁻¹ ^ encode 
i) (dist (x i) (y i))
参数：x y : forall i, F i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.of_nonneg_of_le`：Summable.of_nonneg_of_le {f g : β -> Real} (hg
 : forall b, 0 <= g b) (hgf : forall b, g b <= f b) (hf : Summable f) : Summable
 g
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `le_min`：le_min (h₁ : c <= a) (h₂ : c <= b) : c <= min a b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `summable_geometric_two_encode`：summable_geometric_two_encode {ι : Type*}
 [Encodable ι] : Summable fun i : ι => (1 / 2 : Real) ^ Encodable.encode i
-/
lemma dist_summable (x y : ∀ i, F i) :
    Summable fun i ↦ min (2⁻¹ ^ encode i) (dist (x i) (y i)) := by
  refine .of_nonneg_of_le (fun i => ?_) (fun i => min_le_left _ _) <| by
    simpa [one_div] using summable_geometric_two_encode
  exact le_min (by positivity) dist_nonneg
/-
**PiCountable.min_dist_le_dist_pi** 是 Mathlib 中的一个引理，位于命名空间 `PiCountable`。
形式化陈述：min_dist_le_dist_pi (x y : forall i, F i) (i : ι) : min (2⁻¹ ^ encode i) (
dist (x i) (y i)) <= dist x y
参数：x y : forall i, F i；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.le_tsum`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilter ι
} [inst : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [inst_
3 : To…
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用引理 `PiCountable.dist_summable`：dist_summable (x y : forall i, F i) : Summabl
e fun i => min (2⁻¹ ^ encode i) (dist (x i) (y i))
· 使用引理 `le_min`：le_min (h₁ : c <= a) (h₂ : c <= b) : c <= min a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
-/
lemma min_dist_le_dist_pi (x y : ∀ i, F i) (i : ι) :
    min (2⁻¹ ^ encode i) (dist (x i) (y i)) ≤ dist x y :=
  (dist_summable x y).le_tsum i fun j _ => le_min (by simp) dist_nonneg
/-
**PiCountable.dist_le_dist_pi_of_dist_lt** 是 Mathlib 中的一个引理，位于命名空间 `PiCountable`
。
形式化陈述：dist_le_dist_pi_of_dist_lt (h : dist x y < 2⁻¹ ^ encode i) : dist (x i) (y
 i) <= dist x y
参数：h : dist x y < 2⁻¹ ^ encode i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `min_le_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, min b c ≤
 a ↔ b ≤ a ∨ c ≤ a
· 使用引理 `PiCountable.min_dist_le_dist_pi`：min_dist_le_dist_pi (x y : forall i, F 
i) (i : ι) : min (2⁻¹ ^ encode i) (dist (x i) (y i)) <= dist x y
-/
lemma dist_le_dist_pi_of_dist_lt (h : dist x y < 2⁻¹ ^ encode i) : dist (x i) (y i) ≤ dist x y := by
  simpa only [not_le.2 h, false_or] using min_le_iff.1 (min_dist_le_dist_pi x y i)

/-- Given a countable family of metric spaces, one may put a distance on their product `Π i, E i`.

It is highly non-canonical, though, and therefore not registered as a global instance.
The distance we use here is `dist x y = ∑' i, min (1/2)^(encode i) (dist (x i) (y i))`. -/
@[instance_reducible]
/-
**PiCountable.pseudoMetricSpace** 是 Mathlib 中的一个定义，位于命名空间 `PiCountable`。
形式化陈述：{ι : Type u_2} →   [Encodable ι] → {F : ι → Type u_3} → [(i : ι) → PseudoM
etricSpace (F i)] → PseudoMetricSpace ((i : ι) → F i)
参数：i : ι；F i；(i : ι) → F i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a countable family of metric spaces, one may put a distance on their produ
ct `Π i, E i`.

It is highly non-canonical, though, and therefore not registered as a global ins
tance.
The distance we use here is `dist x y = ∑' i, min (1/2)^(encode i) (dist (x i) (
y i))`.
-/
protected def pseudoMetricSpace : PseudoMetricSpace (∀ i, F i) :=
  PseudoEMetricSpace.toPseudoMetricSpaceOfDist dist (fun x y ↦ by rw [dist_eq_tsum]; positivity)
  fun x y ↦ by
    rw [edist_eq_tsum, dist_eq_tsum,
      ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) (dist_summable ..)]
    congr! with a
    simp [edist, ENNReal.inv_pow, PseudoMetricSpace.edist_dist (x a) (y a)]

end PseudoMetricSpace

attribute [scoped instance] PiCountable.pseudoMetricSpace

section MetricSpace
variable [∀ i, MetricSpace (F i)]
/-- Given a countable family of metric spaces, one may put a distance on their product `Π i, E i`.

It is highly non-canonical, though, and therefore not registered as a global instance.
The distance we use here is `edist x y = ∑' i, min (1/2)^(encode i) (edist (x i) (y i))`. -/
@[instance_reducible]
/-
**PiCountable.metricSpace** 是 Mathlib 中的一个定义，位于命名空间 `PiCountable`。
形式化陈述：{ι : Type u_2} → [Encodable ι] → {F : ι → Type u_3} → [(i : ι) → MetricSpa
ce (F i)] → MetricSpace ((i : ι) → F i)
参数：i : ι；F i；(i : ι) → F i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a countable family of metric spaces, one may put a distance on their produ
ct `Π i, E i`.

It is highly non-canonical, though, and therefore not registered as a global ins
tance.
The distance we use here is `edist x y = ∑' i, min (1/2)^(encode i) (edist (x i)
 (y i))`.
-/
protected def metricSpace : MetricSpace (∀ i, F i) :=
  EMetricSpace.toMetricSpaceOfDist dist (by simp) (by simp [edist_dist])

end MetricSpace
end PiCountable

/-! ### Embedding a countably separated space inside a space of sequences -/

namespace Metric

open scoped PiCountable

variable {ι X : Type*} {Y : ι → Type*} {f : ∀ i, X → Y i}

include f in
variable (X Y f) in
/-- Given a type `X` and a sequence `Y` of metric spaces and a sequence `f : : ∀ i, X → Y i` of
separating functions, `PiNatEmbed X Y f` is a type synonym for `X` seen as a subset of `∀ i, Y i`.
-/
/-
**Metric.PiNatEmbed** 是 Mathlib 中的一个归纳类型，位于命名空间 `Metric`。
形式化陈述：{ι : Type u_2} → (X : Type u_5) → (Y : ι → Type u_6) → ((i : ι) → X → Y i)
 → Type u_5
参数：X : Type u_5；Y : ι → Type u_6；(i : ι) → X → Y i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a type `X` and a sequence `Y` of metric spaces and a sequence `f : : ∀ i, 
X → Y i` of
separating functions, `PiNatEmbed X Y f` is a type synonym for `X` seen as a sub
set of `∀ i, Y i`.
-/
structure PiNatEmbed (X : Type*) (Y : ι → Type*) (f : ∀ i, X → Y i) where
  /-- The map from `X` to the subset of `∀ i, Y i`. -/
  toPiNat ::
  /-- The map from the subset of `∀ i, Y i` to `X`. -/
  ofPiNat : X

namespace PiNatEmbed

/-
**Metric.PiNatEmbed.ext** 是 Mathlib 中的一个定理，位于命名空间 `Metric.PiNatEmbed`。
形式化陈述：∀ {ι : Type u_2} {X : Type u_3} {Y : ι → Type u_4} {f : (i : ι) → X → Y i}
 {x y : Metric.PiNatEmbed X Y f},   x.ofPiNat = y.ofPiNat → x = y
参数：i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
-/
@[ext] lemma ext {x y : PiNatEmbed X Y f} (hxy : x.ofPiNat = y.ofPiNat) : x = y := by
  cases x; congr!

variable (X Y f) in
/-- Equivalence between `X` and its embedding into `∀ i, Y i`. -/
@[simps]
/-
**Metric.PiNatEmbed.toPiNatEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Metric.PiNatEmbed`。
形式化陈述：toPiNatEquiv : X ≃ PiNatEmbed X Y f where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence between `X` and its embedding into `∀ i, Y i`.
-/
def toPiNatEquiv : X ≃ PiNatEmbed X Y f where
  toFun := toPiNat
  invFun := ofPiNat
  left_inv _ := rfl
  right_inv _ := rfl
/-
**Metric.PiNatEmbed.ofPiNat_inj** 是 Mathlib 中的一个定理，位于命名空间 `Metric.PiNatEmbed`。
形式化陈述：∀ {ι : Type u_2} {X : Type u_3} {Y : ι → Type u_4} {f : (i : ι) → X → Y i}
 {x y : Metric.PiNatEmbed X Y f},   x.ofPiNat = y.ofPiNat ↔ x = y
参数：i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
@[simp] lemma ofPiNat_inj {x y : PiNatEmbed X Y f} : x.ofPiNat = y.ofPiNat ↔ x = y :=
  (toPiNatEquiv X Y f).symm.injective.eq_iff
/-
**Metric.PiNatEmbed.** 是 Mathlib 中的一个引理，位于命名空间 `Metric.PiNatEmbed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma «forall» {P : PiNatEmbed X Y f → Prop} : (∀ x, P x) ↔ ∀ x, P (toPiNat x) :=
  (toPiNatEquiv X Y f).symm.forall_congr_left

variable (X Y f) in
/-- `X` equipped with the distance coming from `∀ i, Y i` embeds in `∀ i, Y i`. -/
/-
**Metric.PiNatEmbed.embed** 是 Mathlib 中的一个定义，位于命名空间 `Metric.PiNatEmbed`。
形式化陈述：embed : PiNatEmbed X Y f -> forall i, Y i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`X` equipped with the distance coming from `∀ i, Y i` embeds in `∀ i, Y i`.
-/
noncomputable def embed : PiNatEmbed X Y f → ∀ i, Y i := fun x i ↦ f i x.ofPiNat
/-
**Metric.PiNatEmbed.embed_injective** 是 Mathlib 中的一个引理，位于命名空间 `Metric.PiNatEmbed
`。
形式化陈述：embed_injective (separating_f : Pairwise fun x y => exists i, f i x != f i
 y) : Injective (embed X Y f)
参数：separating_f : Pairwise fun x y => exists i, f i x != f i y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Metric.PiNatEmbed.toPiNat.injEq`：∀ {ι : Type u_2} {X : Type u_5} {Y : ι 
→ Type u_6} {f : (i : ι) → X → Y i} (ofPiNat ofPiNat_1 : X),   ({ ofPiNat := ofP
iNat } = { ofPiNat :=…
· 使用定理 `not_imp_comm`：not_imp_comm : ¬a -> b ↔ ¬b -> a
-/
lemma embed_injective (separating_f : Pairwise fun x y ↦ ∃ i, f i x ≠ f i y) :
    Injective (embed X Y f) := by
  simpa [Pairwise, not_imp_comm (a := _ = _), funext_iff, Function.Injective] using! separating_f

variable [Encodable ι]

section PseudoEMetricSpace
variable [∀ i, PseudoEMetricSpace (Y i)]

/-
**Metric.PiNatEmbed.** 是 Mathlib 中的一个实例，位于命名空间 `Metric.PiNatEmbed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : PseudoEMetricSpace (PiNatEmbed X Y f) :=
  .induced (embed X Y f) PiCountable.pseudoEMetricSpace
/-
**Metric.PiNatEmbed.edist_def** 是 Mathlib 中的一个引理，位于命名空间 `Metric.PiNatEmbed`。
形式化陈述：edist_def (x y : PiNatEmbed X Y f) : edist x y = ∑' i, min (2⁻¹ ^ encode i
) (edist (f i x.ofPiNat) (f i y.ofPiNat))
参数：x y : PiNatEmbed X Y f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma edist_def (x y : PiNatEmbed X Y f) :
    edist x y = ∑' i, min (2⁻¹ ^ encode i) (edist (f i x.ofPiNat) (f i y.ofPiNat)) := rfl
/-
**Metric.PiNatEmbed.isometry_embed** 是 Mathlib 中的一个引理，位于命名空间 `Metric.PiNatEmbed`
。
形式化陈述：isometry_embed : Isometry (embed X Y f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PseudoEMetricSpace.isometry_induced`：PseudoEMetricSpace.isometry_induced
 (f : α -> β) [m : PseudoEMetricSpace β] : letI
-/
lemma isometry_embed : Isometry (embed X Y f) := PseudoEMetricSpace.isometry_induced _

end PseudoEMetricSpace

section PseudoMetricSpace
variable [∀ i, PseudoMetricSpace (Y i)]

/-
**Metric.PiNatEmbed.** 是 Mathlib 中的一个实例，位于命名空间 `Metric.PiNatEmbed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : PseudoMetricSpace (PiNatEmbed X Y f) :=
  .induced (embed X Y f) PiCountable.pseudoMetricSpace
/-
**Metric.PiNatEmbed.dist_def** 是 Mathlib 中的一个引理，位于命名空间 `Metric.PiNatEmbed`。
形式化陈述：dist_def (x y : PiNatEmbed X Y f) : dist x y = ∑' i, min (2⁻¹ ^ encode i) 
(dist (f i x.ofPiNat) (f i y.ofPiNat))
参数：x y : PiNatEmbed X Y f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma dist_def (x y : PiNatEmbed X Y f) :
    dist x y = ∑' i, min (2⁻¹ ^ encode i) (dist (f i x.ofPiNat) (f i y.ofPiNat)) := rfl

variable [TopologicalSpace X]
/-
**Metric.PiNatEmbed.continuous_toPiNat** 是 Mathlib 中的一个引理，位于命名空间 `Metric.PiNatEm
bed`。
形式化陈述：continuous_toPiNat (continuous_f : forall i, Continuous (f i)) : Continuou
s (toPiNat : X -> PiNatEmbed X Y f)
参数：continuous_f : forall i, Continuous (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `continuous_iff_continuous_dist`：continuous_iff_continuous_dist [Topologi
calSpace β] {f : β -> α} : Continuous f ↔ Continuous fun x : β × β => dist (f x.
1) (f x.2)
· 使用定理 `continuous_tsum`：continuous_tsum [TopologicalSpace β] {f : α -> β -> F} 
(hf : forall i, Continuous (f i)) (hu : Summable u) (hfu : forall n x, ‖f n x‖ <
= u n…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Continuous.min`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] 
[inst_1 : LinearOrder α] [OrderClosedTopology α] {f g : β → α}   [inst_3 : Topol
ogic…
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Continuous.dist`：∀ {α : Type u_1} {β : Type u_2} [inst : PseudoMetricSpa
ce α] [inst_1 : TopologicalSpace β] {f g : β → α},   Continuous f → Continuous g
 → Co…
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `summable_geometric_two_encode`：summable_geometric_two_encode {ι : Type*}
 [Encodable ι] : Summable fun i : ι => (1 / 2 : Real) ^ Encodable.encode i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma continuous_toPiNat (continuous_f : ∀ i, Continuous (f i)) :
    Continuous (toPiNat : X → PiNatEmbed X Y f) := by
  rw [continuous_iff_continuous_dist]
  simp only [dist_def]
  apply continuous_tsum (by fun_prop) summable_geometric_two_encode <| by simp [abs_of_nonneg]

end PseudoMetricSpace

section EMetricSpace
variable [∀ i, EMetricSpace (Y i)]

/-- If the functions `f i : X → Y i` separate points of `X`, then `X` can be embedded into
`∀ i, Y i`. -/
/-
**Metric.PiNatEmbed.emetricSpace** 是 Mathlib 中的一个缩写定义，位于命名空间 `Metric.PiNatEmbed`
。
形式化陈述：emetricSpace (separating_f : Pairwise fun x y => exists i, f i x != f i y)
 : EMetricSpace (PiNatEmbed X Y f)
参数：separating_f : Pairwise fun x y => exists i, f i x != f i y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Metric.PiNatEmbed.embed_injective`：embed_injective (separating_f : Pairw
ise fun x y => exists i, f i x != f i y) : Injective (embed X Y f)

--- 原说明 ---
If the functions `f i : X → Y i` separate points of `X`, then `X` can be embedde
d into
`∀ i, Y i`.
-/
noncomputable abbrev emetricSpace (separating_f : Pairwise fun x y ↦ ∃ i, f i x ≠ f i y) :
    EMetricSpace (PiNatEmbed X Y f) :=
  .induced (embed X Y f) (embed_injective separating_f) PiCountable.emetricSpace
/-
**Metric.PiNatEmbed.isUniformEmbedding_embed** 是 Mathlib 中的一个引理，位于命名空间 `Metric.P
iNatEmbed`。
形式化陈述：isUniformEmbedding_embed (separating_f : Pairwise fun x y => exists i, f i
 x != f i y) : IsUniformEmbedding (embed X Y f)
参数：separating_f : Pairwise fun x y => exists i, f i x != f i y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Isometry.isUniformEmbedding`：isUniformEmbedding (hf : Isometry f) : IsUn
iformEmbedding f
· 使用引理 `Metric.PiNatEmbed.isometry_embed`：isometry_embed : Isometry (embed X Y f
)
-/
lemma isUniformEmbedding_embed (separating_f : Pairwise fun x y ↦ ∃ i, f i x ≠ f i y) :
    IsUniformEmbedding (embed X Y f) :=
  let := emetricSpace separating_f; isometry_embed.isUniformEmbedding

end EMetricSpace


section MetricSpace
variable [∀ i, MetricSpace (Y i)]

/-- If the functions `f i : X → Y i` separate points of `X`, then `X` can be embedded into
`∀ i, Y i`. -/
/-
**Metric.PiNatEmbed.metricSpace** 是 Mathlib 中的一个缩写定义，位于命名空间 `Metric.PiNatEmbed`。
形式化陈述：metricSpace (separating_f : Pairwise fun x y => exists i, f i x != f i y) 
: MetricSpace (PiNatEmbed X Y f)
参数：separating_f : Pairwise fun x y => exists i, f i x != f i y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the functions `f i : X → Y i` separate points of `X`, then `X` can be embedde
d into
`∀ i, Y i`.
-/
noncomputable abbrev metricSpace (separating_f : Pairwise fun x y ↦ ∃ i, f i x ≠ f i y) :
    MetricSpace (PiNatEmbed X Y f) :=
  (emetricSpace separating_f).toMetricSpace fun x y ↦ by simp [edist_dist]

section CompactSpace
variable [TopologicalSpace X] [CompactSpace X]

/-
**Metric.PiNatEmbed.isHomeomorph_toPiNat** 是 Mathlib 中的一个引理，位于命名空间 `Metric.PiNat
Embed`。
形式化陈述：isHomeomorph_toPiNat (continuous_f : forall i, Continuous (f i)) (separati
ng_f : Pairwise fun x y => exists i, f i x != f i y) : IsHomeomorph (toPiNat : X
 -> PiNatEmbed X Y f)
参数：continuous_f : forall i, Continuous (f i)；separating_f : Pairwise fun x y => 
exists i, f i x != f i y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `isHomeomorph_iff_continuous_bijective`：isHomeomorph_iff_continuous_bijec
tive [CompactSpace X] [T2Space Y] : IsHomeomorph f ↔ Continuous f ∧ Bijective f
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用引理 `Metric.PiNatEmbed.continuous_toPiNat`：continuous_toPiNat (continuous_f :
 forall i, Continuous (f i)) : Continuous (toPiNat : X -> PiNatEmbed X Y f)
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
lemma isHomeomorph_toPiNat (continuous_f : ∀ i, Continuous (f i))
    (separating_f : Pairwise fun x y ↦ ∃ i, f i x ≠ f i y) :
    IsHomeomorph (toPiNat : X → PiNatEmbed X Y f) := by
  let := emetricSpace separating_f
  rw [isHomeomorph_iff_continuous_bijective]
  exact ⟨continuous_toPiNat continuous_f, (toPiNatEquiv X Y f).bijective⟩

variable (X Y f) in
/-- Homeomorphism between `X` and its embedding into `∀ i, Y i` induced by a separating family of
continuous functions `f i : X → Y i`. -/
@[simps!]
/-
**Metric.PiNatEmbed.toPiNatHomeo** 是 Mathlib 中的一个定义，位于命名空间 `Metric.PiNatEmbed`。
形式化陈述：toPiNatHomeo (continuous_f : forall i, Continuous (f i)) (separating_f : P
airwise fun x y => exists i, f i x != f i y) : X ≃ₜ PiNatEmbed X Y f
参数：continuous_f : forall i, Continuous (f i)；separating_f : Pairwise fun x y => 
exists i, f i x != f i y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Homeomorphism between `X` and its embedding into `∀ i, Y i` induced by a separat
ing family of
continuous functions `f i : X → Y i`.
-/
noncomputable def toPiNatHomeo (continuous_f : ∀ i, Continuous (f i))
    (separating_f : Pairwise fun x y ↦ ∃ i, f i x ≠ f i y) :
    X ≃ₜ PiNatEmbed X Y f :=
  (toPiNatEquiv X Y f).toHomeomorphOfIsInducing
    (isHomeomorph_toPiNat continuous_f separating_f).isInducing

/-- If `X` is compact, and there exists a sequence of continuous functions `f i : X → Y i` to
metric spaces `Y i` that separate points on `X`, then `X` is metrizable. -/
/-
**Metric.PiNatEmbed.TopologicalSpace.MetrizableSpace.of_countable_separating** 是
 Mathlib 中的一个定理，位于命名空间 `Metric.PiNatEmbed.TopologicalSpace.MetrizableSpace`。
形式化陈述：∀ {ι : Type u_2} {X : Type u_3} {Y : ι → Type u_4} [Encodable ι] [inst : (
i : ι) → MetricSpace (Y i)]   [inst_1 : TopologicalSpace X] [CompactSpace X] (f 
: (i : ι) → X → Y i),   (∀ (i : ι), Continuous (f i)) → (Pairwise fun x y => ∃ i
, f i x ≠ f i y) → TopologicalSpace.MetrizableSpace X
参数：i : ι；Y i；f : (i : ι) → X → Y i；∀ (i : ι), Continuous (f i)；Pairwise fun x y 
=> ∃ i, f i x ≠ f i y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.metrizableSpace`：∀ {X : Type u_2} {Y : Type u_3} [i
nst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [TopologicalSpace.Metr
izableSpace Y] {f : X → Y}…
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h

--- 原说明 ---
If `X` is compact, and there exists a sequence of continuous functions `f i : X 
→ Y i` to
metric spaces `Y i` that separate points on `X`, then `X` is metrizable.
-/
lemma TopologicalSpace.MetrizableSpace.of_countable_separating (f : ∀ i, X → Y i)
    (continuous_f : ∀ i, Continuous (f i)) (separating_f : Pairwise fun x y ↦ ∃ i, f i x ≠ f i y) :
    MetrizableSpace X :=
  letI := Metric.PiNatEmbed.metricSpace separating_f
  (Metric.PiNatEmbed.toPiNatHomeo X Y f continuous_f separating_f).isEmbedding.metrizableSpace

end CompactSpace

open TopologicalSpace Filter unitInterval

variable [MetricSpace X] [SeparableSpace X]

variable (X) in
/-- Given a separable metric space `X`, `denseSeq X : ℕ → X` gives a countable
dense sequence. This measures the distance between `denseSeq X n` and `x`, truncated to the unit
interval `I` so that the distances remain bounded.

The function `(fun x n ↦ distDenseSeq n x) : X → ℕ → I` is a mapping from `X` to the Hilbert cube.
-/
/-
**Metric.PiNatEmbed.distDenseSeq** 是 Mathlib 中的一个缩写定义，位于命名空间 `Metric.PiNatEmbed`
。
形式化陈述：distDenseSeq (n : Nat) (x : X) : I
参数：n : Nat；x : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a separable metric space `X`, `denseSeq X : ℕ → X` gives a countable
dense sequence. This measures the distance between `denseSeq X n` and `x`, trunc
ated to the unit
interval `I` so that the distances remain bounded.

The function `(fun x n ↦ distDenseSeq n x) : X → ℕ → I` is a mapping from `X` to
 the Hilbert cube.
-/
noncomputable abbrev distDenseSeq (n : ℕ) (x : X) : I :=
  have : Nonempty X := ⟨x⟩
  projIcc _ _ zero_le_one <| dist x (denseSeq X n)
/-
**Metric.PiNatEmbed.continuous_distDenseSeq** 是 Mathlib 中的一个引理，位于命名空间 `Metric.Pi
NatEmbed`。
形式化陈述：continuous_distDenseSeq (n : Nat) : Continuous (distDenseSeq X n)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `continuous_of_discreteTopology`：continuous_of_discreteTopology [Topologi
calSpace β] {f : α -> β} : Continuous f
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_projIcc`：continuous_projIcc : Continuous (projIcc a b h)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Continuous.dist`：∀ {α : Type u_1} {β : Type u_2} [inst : PseudoMetricSpa
ce α] [inst_1 : TopologicalSpace β] {f g : β → α},   Continuous f → Continuous g
 → Co…
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
-/
lemma continuous_distDenseSeq (n : ℕ) : Continuous (distDenseSeq X n) := by
  cases isEmpty_or_nonempty X
  · exact continuous_of_discreteTopology
  refine continuous_projIcc.comp <| Continuous.dist continuous_id' ?_
  convert! continuous_const (y := denseSeq X n)
/-
**Metric.PiNatEmbed.separation** 是 Mathlib 中的一个引理，位于命名空间 `Metric.PiNatEmbed`。
形式化陈述：separation {x : X} {C : Set X} (hxC : C in 𝓝 x) : exists (n : Nat), C in (
𝓝 (distDenseSeq X n x)).comap (distDenseSeq X n)
参数：hxC : C in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `closure_compl`：closure_compl : closure sᶜ = (interior s)ᶜ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.denseRange_iff`：denseRange_iff {f : β -> α} : DenseRange f ↔ fora
ll x, forall r > 0, exists y, dist x (f y) < r
· 使用定理 `TopologicalSpace.denseRange_denseSeq`：denseRange_denseSeq [SeparableSpac
e α] [Nonempty α] : DenseRange (denseSeq α)
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Metric.isOpen_ball`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} 
{ε : ℝ}, IsOpen (Metric.ball x ε)
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_eq_self`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOr
der G] [IsOrderedAddMonoid G] {a : G}, |a| = a ↔ 0 ≤ a
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
（共 53 条，此处仅展示前 30 条）
-/
lemma separation {x : X} {C : Set X} (hxC : C ∈ 𝓝 x) :
    ∃ (n : ℕ), C ∈ (𝓝 (distDenseSeq X n x)).comap (distDenseSeq X n) := by
  let ε : ℝ := min (infDist x (closure Cᶜ)) 1
  obtain hC | hC := (closure Cᶜ).eq_empty_or_nonempty
  · simp_all
  have : Nonempty X := ⟨x⟩
  obtain ⟨n, hn⟩ := denseRange_iff.mp (denseRange_denseSeq X) x (ε / 2)
    (by simp_all [ε, ← IsClosed.notMem_iff_infDist_pos, mem_interior_iff_mem_nhds])
  refine ⟨n, ball 0 (ε / 2), isOpen_ball.mem_nhds ?_, ?_⟩
  · simp [Subtype.dist_eq, abs_eq_self.mpr, coe_projIcc, hn]
  · intro y hy
    replace hy : dist y (denseSeq X n) < ε / 2 := by
      simpa [Subtype.dist_eq, abs_eq_self.mpr, coe_projIcc, not_lt_of_ge, ε, div_le_iff₀] using hy
    have : dist x y < infDist x (closure Cᶜ) :=
      ((dist_triangle_right x y (denseSeq X n)).trans_lt (add_lt_add hn hy)).trans_le (by simp [ε])
    simpa using notMem_of_notMem_closure (mt infDist_le_dist_of_mem this.not_ge)
/-
**Metric.PiNatEmbed.injective_distDenseSeq** 是 Mathlib 中的一个引理，位于命名空间 `Metric.PiN
atEmbed`。
形式化陈述：injective_distDenseSeq (x y : X) (hxy : x != y) : exists n, distDenseSeq X
 n x != distDenseSeq X n y
参数：x y : X；hxy : x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Metric.PiNatEmbed.separation`：separation {x : X} {C : Set X} (hxC : C in
 𝓝 x) : exists (n : Nat), C in (𝓝 (distDenseSeq X n x)).comap (distDenseSeq X n)
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_compl_singleton`：isOpen_compl_singleton [T1Space X] {x : X} : IsO
pen ({x}ᶜ : Set X)
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma injective_distDenseSeq (x y : X) (hxy : x ≠ y) :
    ∃ n, distDenseSeq X n x ≠ distDenseSeq X n y := by
  obtain ⟨n, hn⟩ := separation ((isOpen_compl_singleton (x := y)).mem_nhds hxy)
  exact ⟨n, fun e ↦ by simp +contextual [e, ← exists_prop, mem_of_mem_nhds] at hn⟩

variable (A : Type*) [TopologicalSpace A]
/-
**Metric.PiNatEmbed.continuous_distDenseSeq_inv** 是 Mathlib 中的一个引理，位于命名空间 `Metri
c.PiNatEmbed`。
形式化陈述：continuous_distDenseSeq_inv : Continuous (ofPiNat : PiNatEmbed X (fun _ =>
 I) (distDenseSeq X) -> X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用引理 `Metric.PiNatEmbed.separation`：separation {x : X} {C : Set X} (hxC : C in
 𝓝 x) : exists (n : Nat), C in (𝓝 (distDenseSeq X n x)).comap (distDenseSeq X n)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.IsInducing.nhds_eq_comap`：nhds_eq_comap (hf : IsInducing f) : f
orall x : X, 𝓝 x = comap f (𝓝 <| f x)
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
· 使用定理 `IsUniformEmbedding.isEmbedding`：∀ {α : Type u} {β : Type v} [inst : Unif
ormSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbedding f → Topo
logy.IsEmbedding f
· 使用引理 `Metric.PiNatEmbed.isUniformEmbedding_embed`：isUniformEmbedding_embed (se
parating_f : Pairwise fun x y => exists i, f i x != f i y) : IsUniformEmbedding 
(embed X Y f)
· 使用引理 `Metric.PiNatEmbed.injective_distDenseSeq`：injective_distDenseSeq (x y : 
X) (hxy : x != y) : exists n, distDenseSeq X n x != distDenseSeq X n y
· 使用定理 `nhds_pi`：nhds_pi {a : forall i, A i} : 𝓝 a = pi fun i => 𝓝 (a i)
· 使用定理 `Filter.mem_pi_of_mem`：mem_pi_of_mem (i : ι) {s : Set (α i)} (hs : s in f
 i) : eval i ⁻¹' s in pi f
-/
lemma continuous_distDenseSeq_inv :
    Continuous (ofPiNat : PiNatEmbed X (fun _ => I) (distDenseSeq X) → X) := by
  refine continuous_iff_continuousAt.mpr fun x s hs ↦ ?_
  obtain ⟨i, t, ht, hts⟩ := separation hs
  rw [(isUniformEmbedding_embed injective_distDenseSeq).isEmbedding.nhds_eq_comap, nhds_pi]
  exact ⟨_, Filter.mem_pi_of_mem _ ht, fun x hx ↦ hts hx⟩
/-
**Metric.PiNatEmbed.exists_embedding_to_hilbert_cube** 是 Mathlib 中的一个定理，位于命名空间 `
Metric.PiNatEmbed`。
形式化陈述：exists_embedding_to_hilbert_cube : exists F : X -> Nat -> I, IsEmbedding F
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Metric.PiNatEmbed.continuous_toPiNat`：continuous_toPiNat (continuous_f :
 forall i, Continuous (f i)) : Continuous (toPiNat : X -> PiNatEmbed X Y f)
· 使用引理 `Metric.PiNatEmbed.continuous_distDenseSeq`：continuous_distDenseSeq (n : 
Nat) : Continuous (distDenseSeq X n)
· 使用引理 `Metric.PiNatEmbed.continuous_distDenseSeq_inv`：continuous_distDenseSeq_i
nv : Continuous (ofPiNat : PiNatEmbed X (fun _ => I) (distDenseSeq X) -> X)
· 使用定理 `IsUniformEmbedding.isEmbedding`：∀ {α : Type u} {β : Type v} [inst : Unif
ormSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbedding f → Topo
logy.IsEmbedding f
· 使用引理 `Metric.PiNatEmbed.isUniformEmbedding_embed`：isUniformEmbedding_embed (se
parating_f : Pairwise fun x y => exists i, f i x != f i y) : IsUniformEmbedding 
(embed X Y f)
· 使用引理 `Metric.PiNatEmbed.injective_distDenseSeq`：injective_distDenseSeq (x y : 
X) (hxy : x != y) : exists n, distDenseSeq X n x != distDenseSeq X n y
· 使用定理 `Topology.IsEmbedding.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3
} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpa
ce Y] [inst_2 :…
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
-/
theorem exists_embedding_to_hilbert_cube : ∃ F : X → ℕ → I, IsEmbedding F := by
  let firststep : X ≃ₜ PiNatEmbed X (fun i => I) (distDenseSeq X) := {
    toFun := toPiNat
    invFun := ofPiNat
    left_inv _ := rfl
    right_inv _ := rfl
    continuous_toFun := continuous_toPiNat <| fun i ↦ continuous_distDenseSeq i
    continuous_invFun := continuous_distDenseSeq_inv }
  let secondstep : PiNatEmbed X (fun i => I) (distDenseSeq X) → ℕ → I := embed _ _ _
  let isEmbedding_secondstep : IsEmbedding secondstep :=
      (isUniformEmbedding_embed injective_distDenseSeq).isEmbedding
  exact ⟨_, isEmbedding_secondstep.comp firststep.isEmbedding⟩

end MetricSpace
end PiNatEmbed
end Metric

