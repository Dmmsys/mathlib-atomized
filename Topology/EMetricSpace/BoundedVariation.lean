/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Order.Interval.Set.ProjIcc
public import Mathlib.Data.Finset.Sort
public import Mathlib.Tactic.Finiteness
public import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.Order.LeftRightLim
public import Mathlib.Topology.Semicontinuity.Defs
public import Mathlib.Tactic.Bound

/-!
# Functions of bounded variation

We study functions of bounded variation. In particular, we show that a bounded variation function
is a difference of monotone functions, and differentiable almost everywhere. This implies that
Lipschitz functions from the real line into finite-dimensional vector space are also differentiable
almost everywhere.

## Main definitions and results

* `eVariationOn f s` is the total variation of the function `f` on the set `s`, in `ℝ≥0∞`.
* `BoundedVariationOn f s` registers that the variation of `f` on `s` is finite.
* `LocallyBoundedVariationOn f s` registers that `f` has finite variation on any compact
  subinterval of `s`.
* `variationOnFromTo f s a b` is the signed variation of `f` on `s ∩ Icc a b`, converted to `ℝ`.

* `eVariationOn.Icc_add_Icc` states that the variation of `f` on `[a, c]` is the sum of its
  variations on `[a, b]` and `[b, c]`.
* `LocallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn` proves that a function
  with locally bounded variation is the difference of two monotone functions.
* `LipschitzWith.locallyBoundedVariationOn` shows that a Lipschitz function has locally
  bounded variation.

We also give several variations around these results.

## Implementation

We define the variation as an extended nonnegative real, to allow for infinite variation. This makes
it possible to use the complete linear order structure of `ℝ≥0∞`. The proofs would be much
more tedious with an `ℝ`-valued or `ℝ≥0`-valued variation, since one would always need to check
that the sets one uses are nonempty and bounded above as these are only conditionally complete.
-/

@[expose] public section

open scoped NNReal ENNReal Topology UniformConvergence
open Set Filter OrderDual

variable {α : Type*} [LinearOrder α] {E : Type*} [PseudoEMetricSpace E]

/-- The (extended-real-valued) variation of a function `f` on a set `s` inside a linear order is
the supremum of the sum of `edist (f (u (i+1))) (f (u i))` over all finite increasing
sequences `u` in `s`. -/
/-
**eVariationOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：eVariationOn (f : α -> E) (s : Set α) : Real>=0∞
参数：f : α -> E；s : Set α。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (extended-real-valued) variation of a function `f` on a set `s` inside a lin
ear order is
the supremum of the sum of `edist (f (u (i+1))) (f (u i))` over all finite incre
asing
sequences `u` in `s`.
-/
noncomputable def eVariationOn (f : α → E) (s : Set α) : ℝ≥0∞ :=
  ⨆ p : ℕ × { u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ s },
    ∑ i ∈ Finset.range p.1, edist (f (p.2.1 (i + 1))) (f (p.2.1 i))

/-- A function has bounded variation on a set `s` if its total variation there is finite. -/
/-
**BoundedVariationOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：BoundedVariationOn (f : α -> E) (s : Set α)
参数：f : α -> E；s : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function has bounded variation on a set `s` if its total variation there is fi
nite.
-/
def BoundedVariationOn (f : α → E) (s : Set α) :=
  eVariationOn f s ≠ ∞

/-- A function has locally bounded variation on a set `s` if, given any interval `[a, b]` with
endpoints in `s`, then the function has finite variation on `s ∩ [a, b]`. -/
/-
**LocallyBoundedVariationOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LocallyBoundedVariationOn (f : α -> E) (s : Set α)
参数：f : α -> E；s : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function has locally bounded variation on a set `s` if, given any interval `[a
, b]` with
endpoints in `s`, then the function has finite variation on `s ∩ [a, b]`.
-/
def LocallyBoundedVariationOn (f : α → E) (s : Set α) :=
  ∀ a b, a ∈ s → b ∈ s → BoundedVariationOn f (s ∩ Icc a b)

/-! ### Basic computations of variation -/

namespace eVariationOn

/-
**eVariationOn.nonempty_monotone_mem** 是 Mathlib 中的一个定理，位于命名空间 `eVariationOn`。
形式化陈述：nonempty_monotone_mem {s : Set α} (hs : s.Nonempty) : Nonempty { u // Mono
tone u ∧ forall i : Nat, u i in s }
参数：hs : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem nonempty_monotone_mem {s : Set α} (hs : s.Nonempty) :
    Nonempty { u // Monotone u ∧ ∀ i : ℕ, u i ∈ s } := by
  obtain ⟨x, hx⟩ := hs
  exact ⟨⟨fun _ => x, fun i j _ => le_rfl, fun _ => hx⟩⟩
/-
**eVariationOn.eq_of_edist_zero_on** 是 Mathlib 中的一个定理，位于命名空间 `eVariationOn`。
形式化陈述：eq_of_edist_zero_on {f f' : α -> E} {s : Set α} (h : forall ⦃x⦄, x in s ->
 edist (f x) (f' x) = 0) : eVariationOn f s = eVariationOn f' s
参数：h : forall ⦃x⦄, x in s -> edist (f x) (f' x) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_congr_right`：edist_congr_right {x y z : α} (h : edist x y = 0) : e
dist x z = edist y z
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `edist_congr_left`：edist_congr_left {x y z : α} (h : edist x y = 0) : edi
st z x = edist z y
-/
theorem eq_of_edist_zero_on {f f' : α → E} {s : Set α} (h : ∀ ⦃x⦄, x ∈ s → edist (f x) (f' x) = 0) :
    eVariationOn f s = eVariationOn f' s := by
  dsimp only [eVariationOn]
  congr 1 with p : 1
  congr 1 with i : 1
  rw [edist_congr_right (h <| p.snd.prop.2 (i + 1)), edist_congr_left (h <| p.snd.prop.2 i)]
/-
**eVariationOn.eq_of_eqOn** 是 Mathlib 中的一个定理，位于命名空间 `eVariationOn`。
形式化陈述：eq_of_eqOn {f f' : α -> E} {s : Set α} (h : EqOn f f' s) : eVariationOn f 
s = eVariationOn f' s
参数：h : EqOn f f' s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eVariationOn.eq_of_edist_zero_on`：eq_of_edist_zero_on {f f' : α -> E} {s
 : Set α} (h : forall ⦃x⦄, x in s -> edist (f x) (f' x) = 0) : eVariationOn f s 
= eVariationOn f' s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
-/
theorem eq_of_eqOn {f f' : α → E} {s : Set α} (h : EqOn f f' s) :
    eVariationOn f s = eVariationOn f' s :=
  eq_of_edist_zero_on fun x xs => by rw [h xs, edist_self]
/-
**eVariationOn.sum_le** 是 Mathlib 中的一个定理，位于命名空间 `eVariationOn`。
形式化陈述：sum_le {f : α -> E} {s : Set α} {n : Nat} {u : Nat -> α} (hu : Monotone u)
 (us : forall i, u i in s) : (∑ i in Finset.range n, edist (f (u (i + 1))) (f (u
 i))) <= eVariationOn f s
参数：hu : Monotone u；us : forall i, u i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem sum_le {f : α → E} {s : Set α} {n : ℕ} {u : ℕ → α} (hu : Monotone u) (us : ∀ i, u i ∈ s) :
    (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) ≤ eVariationOn f s :=
  le_iSup_of_le ⟨n, u, hu, us⟩ le_rfl
/-
**eVariationOn.sum_le_of_monotoneOn_Icc** 是 Mathlib 中的一个定理，位于命名空间 `eVariationOn`
。
形式化陈述：sum_le_of_monotoneOn_Icc {f : α -> E} {s : Set α} {m n : Nat} {u : Nat -> 
α} (hu : MonotoneOn u (Icc m n)) (us : forall i in Icc m n, u i in s) : (∑ i in 
Finset.Ico m n, edist (f (u (i + 1))) (f (u i))) <= eVariationOn f s
参数：hu : MonotoneOn u (Icc m n)；us : forall i in Icc m n, u i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.Ico_eq_empty_of_le`：Ico_eq_empty_of_le (h : b <= a) : Ico a b = ∅
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.mem_Ico`：mem_Ico : x in Ico a b ↔ a <= x ∧ x < b
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.projIcc_of_mem`：projIcc_of_mem (hx : x in Icc a b) : projIcc a b h x
 = ⟨x, hx⟩
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_mono_set`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMono
id M] [inst_1 : Preorder M] [CanonicallyOrderedAdd M] (f : ι → M),   Monotone fu
n s => ∑ …
· 使用定理 `Finset.Ico_subset_Iio_self`：Ico_subset_Iio_self : Ico a b subseteq Iio b
· 使用定理 `Nat.Iio_eq_range`：Iio_eq_range : Iio a = range a
· 使用定理 `eVariationOn.sum_le`：sum_le {f : α -> E} {s : Set α} {n : Nat} {u : Nat 
-> α} (hu : Monotone u) (us : forall i, u i in s) : (∑ i in Finset.range n, edis
t (f (u (…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Set.monotone_projIcc`：monotone_projIcc : Monotone (projIcc a b h)
-/
theorem sum_le_of_monotoneOn_Icc {f : α → E} {s : Set α} {m n : ℕ} {u : ℕ → α}
    (hu : MonotoneOn u (Icc m n)) (us : ∀ i ∈ Icc m n, u i ∈ s) :
    (∑ i ∈ Finset.Ico m n, edist (f (u (i + 1))) (f (u i))) ≤ eVariationOn f s := by
  rcases le_total n m with hnm | hmn
  · simp [Finset.Ico_eq_empty_of_le hnm]
  let π := projIcc m n hmn
  let v i := u (π i)
  calc
    ∑ i ∈ Finset.Ico m n, edist (f (u (i + 1))) (f (u i))
        = ∑ i ∈ Finset.Ico m n, edist (f (v (i + 1))) (f (v i)) :=
      Finset.sum_congr rfl fun i hi ↦ by
        rw [Finset.mem_Ico] at hi
        simp only [v, π, projIcc_of_mem hmn ⟨hi.1, hi.2.le⟩,
          projIcc_of_mem hmn ⟨hi.1.trans i.le_succ, hi.2⟩]
    _ ≤ ∑ i ∈ Finset.range n, edist (f (v (i + 1))) (f (v i)) :=
      Finset.sum_mono_set _ (Nat.Iio_eq_range n ▸ Finset.Ico_subset_Iio_self)
    _ ≤ eVariationOn f s :=
      sum_le (fun i j h ↦ hu (π i).2 (π j).2 (monotone_projIcc hmn h)) fun i ↦ us _ (π i).2
/-
**eVariationOn.sum_le_of_monotoneOn_Iic** 是 Mathlib 中的一个定理，位于命名空间 `eVariationOn`
。
形式化陈述：sum_le_of_monotoneOn_Iic {f : α -> E} {s : Set α} {n : Nat} {u : Nat -> α}
 (hu : MonotoneOn u (Iic n)) (us : forall i <= n, u i in s) : (∑ i in Finset.ran
ge n, edist (f (u (i + 1))) (f (u i))) <= eVariationOn f s
参数：hu : MonotoneOn u (Iic n)；us : forall i <= n, u i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Nat.Ico_zero_eq_range`：Ico_zero_eq_range : Ico 0 a = range a
· 使用定理 `eVariationOn.sum_le_of_monotoneOn_Icc`：sum_le_of_monotoneOn_Icc {f : α -
> E} {s : Set α} {m n : Nat} {u : Nat -> α} (hu : MonotoneOn u (Icc m n)) (us : 
forall i in Icc m n, u i in…
· 使用定理 `MonotoneOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s s₂ : Set α} {f : α →
 β} [inst : Preorder α] [inst_1 : Preorder β],   MonotoneOn f s → s₂ ⊆ s → Monot
oneOn…
· 使用定理 `Set.Icc_subset_Iic_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Icc a b ⊆ Set.Iic b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem sum_le_of_monotoneOn_Iic {f : α → E} {s : Set α} {n : ℕ} {u : ℕ → α}
    (hu : MonotoneOn u (Iic n)) (us : ∀ i ≤ n, u i ∈ s) :
    (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) ≤ eVariationOn f s := by
  simpa using sum_le_of_monotoneOn_Icc (m := 0) (hu.mono Icc_subset_Iic_self) fun i hi ↦ us i hi.2

/-- The variation can be expressed using strictly monotone functions. This formulation is
often less convenient than the one with monotone functions as it involves dependent types, but
it is sometimes handy. -/
/-
**eVariationOn.eVariationOn_eq_strictMonoOn** 是 Mathlib 中的一个定理，位于命名空间 `eVariatio
nOn`。
形式化陈述：eVariationOn_eq_strictMonoOn (f : α -> E) (s : Set α) : eVariationOn f s =
 ⨆ p : (n : Nat) × { u : Nat -> α // StrictMonoOn u (Iic n) ∧ forall i in Iic n,
 u i in s }, ∑ i in Finset.range p.1, edist (f (p.2.1 (i + 1))) (f (p.2.1 i))
参数：f : α -> E；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
The variation can be expressed using strictly monotone functions. This formulati
on is
often less convenient than the one with monotone functions as it involves depend
ent types, but
it is sometimes handy.
-/
theorem eVariationOn_eq_strictMonoOn (f : α → E) (s : Set α) :
    eVariationOn f s =
      ⨆ p : (n : ℕ) × { u : ℕ → α // StrictMonoOn u (Iic n) ∧ ∀ i ∈ Iic n, u i ∈ s },
        ∑ i ∈ Finset.range p.1, edist (f (p.2.1 (i + 1))) (f (p.2.1 i)) := by
  apply le_antisymm
  · apply iSup_le
    rintro ⟨n, u, u_mono, u_mem⟩
    have : ∃ p : (n : ℕ) × { u : ℕ → α // StrictMonoOn u (Iic n) ∧ ∀ i ∈ Iic n, u i ∈ s },
        (p.2 : ℕ → α) p.1 = u n ∧
        ∑ x ∈ Finset.range n, edist (f (u (x + 1))) (f (u x)) =
        ∑ i ∈ Finset.range p.1, edist (f ((p.2 : ℕ → α) (i + 1))) (f ((p.2 : ℕ → α) i)) := by
      induction n with
      | zero => exact ⟨⟨0, ⟨u, by grind [StrictMonoOn], fun i hi ↦ u_mem _⟩⟩, by simp⟩
      | succ n ih =>
        rcases ih with ⟨⟨m, v, v_mono, v_mem⟩, hv, h'v⟩
        simp only [Finset.sum_range_succ, Sigma.exists, Subtype.exists, mem_Iic, exists_and_left,
          exists_prop]
        rcases (u_mono (Nat.le_add_right n 1)).eq_or_lt with hn | hn
        · simp only [← hn, edist_self, add_zero]
          exact ⟨m, v, hv, ⟨v_mono, v_mem⟩, h'v⟩
        · refine ⟨m + 1, fun i ↦ if i ≤ m then v i else u (n + 1), by simp,
            by grind [StrictMonoOn], ?_⟩
          simp only [h'v, ← hv, Order.add_one_le_iff, Finset.sum_range_succ, lt_self_iff_false,
            ↓reduceIte, le_refl]
          congr 1
          exact Finset.sum_congr rfl (by grind)
    rcases this with ⟨p, -, hp⟩
    rw [hp]
    apply le_iSup _ p
  · apply iSup_le
    rintro ⟨n, u, u_mono, u_mem⟩
    apply sum_le_of_monotoneOn_Iic (by grind [MonotoneOn, StrictMonoOn]) (by grind)
/-
**eVariationOn.mono** 是 Mathlib 中的一个定理，位于命名空间 `eVariationOn`。
形式化陈述：mono (f : α -> E) {s t : Set α} (hst : t subseteq s) : eVariationOn f t <=
 eVariationOn f s
参数：f : α -> E；hst : t subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `eVariationOn.sum_le`：sum_le {f : α -> E} {s : Set α} {n : Nat} {u : Nat 
-> α} (hu : Monotone u) (us : forall i, u i in s) : (∑ i in Finset.range n, edis
t (f (u (…
-/
theorem mono (f : α → E) {s t : Set α} (hst : t ⊆ s) : eVariationOn f t ≤ eVariationOn f s := by
  apply iSup_le _
  rintro ⟨n, ⟨u, hu, ut⟩⟩
  exact sum_le hu fun i => hst (ut i)
/-
**eVariationOn.eq_biSup_inter_Icc** 是 Mathlib 中的一个定理，位于命名空间 `eVariationOn`。
形式化陈述：eq_biSup_inter_Icc {f : α -> E} {s : Set α} : eVariationOn f s = ⨆ p in {p
 : α × α | p.1 in s ∧ p.2 in s ∧ p.1 <= p.2}, eVariationOn f (s inter Icc p.1 p.
2)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eVariationOn.eq_1`：∀ {α : Type u_1} [inst : LinearOrder α] {E : Type u_2
} [inst_1 : PseudoEMetricSpace E] (f : α → E) (s : Set α),   eVariationOn f s = 
⨆ p, ∑ …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eVariationOn.sum_le_of_monotoneOn_Iic`：sum_le_of_monotoneOn_Iic {f : α -
> E} {s : Set α} {n : Nat} {u : Nat -> α} (hu : MonotoneOn u (Iic n)) (us : fora
ll i <= n, u i in s) : (∑ i…
· 使用定理 `Monotone.monotoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Monotone f → ∀ (s : Set α), MonotoneOn f s
· 使用引理 `le_biSup`：le_biSup {ι : Type*} {s : Set ι} (f : ι -> α) {i : ι} (hi : i 
in s) : f i <= ⨆ i in s, f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eVariationOn.mono`：mono (f : α -> E) {s t : Set α} (hst : t subseteq s) 
: eVariationOn f t <= eVariationOn f s
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem eq_biSup_inter_Icc {f : α → E} {s : Set α} : eVariationOn f s =
    ⨆ p ∈ {p : α × α | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 ≤ p.2}, eVariationOn f (s ∩ Icc p.1 p.2) := by
  apply le_antisymm ?_ (by simp [iSup_le_iff, mono f inter_subset_left])
  rw [eVariationOn]
  simp only [iSup_le_iff, Prod.forall, Subtype.forall, and_imp]
  intro n u hu hus
  calc ∑ x ∈ Finset.range n, edist (f (u (x + 1))) (f (u x))
  _ ≤ eVariationOn f (s ∩ Icc (u 0) (u n)) :=
      sum_le_of_monotoneOn_Iic (hu.monotoneOn _) (by grind [Monotone])
  _ ≤ ⨆ p ∈ {p : α × α | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 ≤ p.2}, eVariationOn f (s ∩ Icc p.1 p.2) := by
    apply le_biSup (f := fun (p : α × α) ↦ eVariationOn f (s ∩ Icc p.1 p.2)) (i := (u 0, u n))
    grind [Monotone]
/-
**eVariationOn._root_.BoundedVariationOn.mono** 是 Mathlib 中的一个定理，位于命名空间 `eVariat
ionOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.BoundedVariationOn.mono {f : α → E} {s : Set α} (h : BoundedVariationOn f s)
    {t : Set α} (ht : t ⊆ s) : BoundedVariationOn f t :=
  ne_top_of_le_ne_top h (eVariationOn.mono f ht)
/-
**eVariationOn._root_.BoundedVariationOn.locallyBoundedVariationOn** 是 Mathlib 中
的一个定理，位于命名空间 `eVariationOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.BoundedVariationOn.locallyBoundedVariationOn {f : α → E} {s : Set α}
    (h : BoundedVariationOn f s) : LocallyBoundedVariationOn f s := fun _ _ _ _ =>
  h.mono inter_subset_left
/-
**eVariationOn.congr** 是 Mathlib 中的一个定理，位于命名空间 `eVariationOn`。
形式化陈述：congr {f g : α -> E} {s : Set α} (h : EqOn f g s) : eVariationOn f s = eVa
riationOn g s
参数：h : EqOn f g s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem congr {f g : α → E} {s : Set α} (h : EqOn f g s) : eVariationOn f s = eVariationOn g s := by
  grind [eVariationOn]
/-
**eVariationOn.edist_le** 是 Mathlib 中的一个定理，位于命名空间 `eVariationOn`。
形式化陈述：edist_le (f : α -> E) {s : Set α} {x y : α} (hx : x in s) (hy : y in s) : 
edist (f x) (f y) <= eVariationOn f s
参数：f : α -> E；hx : x in s；hy : y in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `monotone_nat_of_le_succ`：monotone_nat_of_le_succ {f : Nat -> α} (hf : fo
rall n, f n <= f (n + 1)) : Monotone f
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_range_one`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ →
 M), ∑ k ∈ Finset.range 1, f k = f 0
· 使用定理 `eVariationOn.sum_le`：sum_le {f : α -> E} {s : Set α} {n : Nat} {u : Nat 
-> α} (hu : Monotone u) (us : forall i, u i in s) : (∑ i in Finset.range n, edis
t (f (u (…
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
· 使用定理 `le_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b 
→ b ≤ a
-/
theorem edist_le (f : α → E) {s : Set α} {x y : α} (hx : x ∈ s) (hy : y ∈ s) :
    edist (f x) (f y) ≤ eVariationOn f s := by
  wlog hxy : y ≤ x generalizing x y
  · rw [edist_comm]
    exact this hy hx (le_of_not_ge hxy)
  let u : ℕ → α := fun n => if n = 0 then y else x
  have hu : Monotone u := monotone_nat_of_le_succ fun
  | 0 => hxy
  | (_ + 1) => le_rfl
  have us : ∀ i, u i ∈ s := fun
  | 0 => hy
  | (_ + 1) => hx
  simpa only [Finset.sum_range_one] using! sum_le (n := 1) hu us
/-
**eVariationOn.eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `eVariationOn`。
形式化陈述：eq_zero_iff (f : α -> E) {s : Set α} : eVariationOn f s = 0 ↔ forall x in 
s, forall y in s, edist (f x) (f y) = 0
参数：f : α -> E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `eVariationOn.edist_le`：edist_le (f : α -> E) {s : Set α} {x y : α} (hx :
 x in s) (hy : y in s) : edist (f x) (f y) <= eVariationOn f s
· 使用定理 `ENNReal.iSup_eq_zero`：∀ {ι : Sort u_1} {f : ι → ENNReal}, ⨆ i, f i = 0 ↔
 ∀ (i : ι), f i = 0
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
-/
theorem eq_zero_iff (f : α → E) {s : Set α} :
    eVariationOn f s = 0 ↔ ∀ x ∈ s, ∀ y ∈ s, edist (f x) (f y) = 0 := by
  constructor
  · rintro h x xs y ys
    rw [← nonpos_iff_eq_zero, ← h]
    exact edist_le f xs ys
  · rintro h
    dsimp only [eVariationOn]
    rw [ENNReal.iSup_eq_zero]
    rintro ⟨n, u, um, us⟩
    exact Finset.sum_eq_zero fun i _ => h _ (us i.succ) _ (us i)
/-
**eVariationOn.constant_on** 是 Mathlib 中的一个定理，位于命名空间 `eVariationOn`。
形式化陈述：constant_on {f : α -> E} {s : Set α} (hf : (f '' s).Subsingleton) : eVaria
tionOn f s = 0
参数：hf : (f '' s).Subsingleton。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eVariationOn.eq_zero_iff`：eq_zero_iff (f : α -> E) {s : Set α} : eVariat
ionOn f s = 0 ↔ forall x in s, forall y in s, edist (f x) (f y) = 0
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
-/
theorem constant_on {f : α → E} {s : Set α} (hf : (f '' s).Subsingleton) :
    eVariationOn f s = 0 := by
  rw [eq_zero_iff]
  rintro x xs y ys
  rw [hf ⟨x, xs, rfl⟩ ⟨y, ys, rfl⟩, edist_self]

@[simp]
/-
**eVariationOn.subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `eVariationOn`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {E : Type u_2} [inst_1 : PseudoEMe
tricSpace E] (f : α → E) {s : Set α},   s.Subsingleton → eVariationOn f s = 0
参数：f : α → E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eVariationOn.constant_on`：constant_on {f : α -> E} {s : Set α} (hf : (f 
'' s).Subsingleton) : eVariationOn f s = 0
· 使用定理 `Set.Subsingleton.image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s.S
ubsingleton → ∀ (f : α → β), (f '' s).Subsingleton
-/
protected theorem subsingleton (f : α → E) {s : Set α} (hs : s.Subsingleton) :
    eVariationOn f s = 0 :=
  constant_on (hs.image f)

@[simp]
/-
**eVariationOn._root_.BoundedVariationOn.of_subsingleton** 是 Mathlib 中的一个定理，位于命名
空间 `eVariationOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.BoundedVariationOn.of_subsingleton {f : α → E} {s : Set α} (hs : s.Subsingleton) :
    BoundedVariationOn f s := by
  simp [BoundedVariationOn, hs]
/-
**eVariationOn.lowerSemicontinuous_aux** 是 Mathlib 中的一个定理，位于命名空间 `eVariationOn`。
形式化陈述：lowerSemicontinuous_aux {ι : Type*} {F : ι -> α -> E} {p : Filter ι} {f : 
α -> E} {s : Set α} (Ffs : forall x in s, Tendsto (fun i => F i x) p (𝓝 (f x))) 
{v : Real>=0∞} (hv : v < eVariationOn f s) : forallᶠ n : ι in p, v < eVariationO
n (F n) s
参数：Ffs : forall x in s, Tendsto (fun i => F i x) p (𝓝 (f x))；hv : v < eVariation
On f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `lt_iSup_iff`：lt_iSup_iff : a < iSup f ↔ exists i, a < f i
· 使用定理 `tendsto_finsetSum`：∀ {ι : Type u_1} {α : Type u_2} {M : Type u_3} [inst 
: TopologicalSpace M] [inst_1 : AddCommMonoid M] [ContinuousAdd M]   {f : ι → α 
→ M} {x…
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `Filter.Tendsto.edist`：Filter.Tendsto.edist {f g : β -> α} {x : Filter β}
 {a b : α} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (fun x =>
 edist (f …
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Tendsto.eventually_const_lt`：Filter.Tendsto.eventually_const_lt {
l : Filter γ} {f : γ -> α} {u v : α} (hv : u < v) (h : Filter.Tendsto f l (𝓝 v))
 : forallᶠ a in l, u < f…
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `eVariationOn.sum_le`：sum_le {f : α -> E} {s : Set α} {n : Nat} {u : Nat 
-> α} (hu : Monotone u) (us : forall i, u i in s) : (∑ i in Finset.range n, edis
t (f (u (…
-/
theorem lowerSemicontinuous_aux {ι : Type*} {F : ι → α → E} {p : Filter ι} {f : α → E} {s : Set α}
    (Ffs : ∀ x ∈ s, Tendsto (fun i => F i x) p (𝓝 (f x))) {v : ℝ≥0∞} (hv : v < eVariationOn f s) :
    ∀ᶠ n : ι in p, v < eVariationOn (F n) s := by
  obtain ⟨⟨n, ⟨u, um, us⟩⟩, hlt⟩ :
    ∃ p : ℕ × { u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ s },
      v < ∑ i ∈ Finset.range p.1, edist (f ((p.2 : ℕ → α) (i + 1))) (f ((p.2 : ℕ → α) i)) :=
    lt_iSup_iff.mp hv
  have : Tendsto (fun j => ∑ i ∈ Finset.range n, edist (F j (u (i + 1))) (F j (u i))) p
      (𝓝 (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)))) := by
    apply tendsto_finsetSum
    exact fun i _ => Tendsto.edist (Ffs (u i.succ) (us i.succ)) (Ffs (u i) (us i))
  exact (this.eventually_const_lt hlt).mono fun i h => h.trans_le (sum_le um us)

/-- The map `(eVariationOn · s)` is lower semicontinuous for pointwise convergence *on `s`*.
Pointwise convergence on `s` is encoded here as uniform convergence on the family consisting of the
singletons of elements of `s`.
-/
/-
**eVariationOn.lowerSemicontinuous** 是 Mathlib 中的一个定理，位于命名空间 `eVariationOn`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {E : Type u_2} [inst_1 : PseudoEMe
tricSpace E] (s : Set α),   LowerSemicontinuous fun f => eVariationOn f s
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eVariationOn.lowerSemicontinuous_aux`：lowerSemicontinuous_aux {ι : Type*
} {F : ι -> α -> E} {p : Filter ι} {f : α -> E} {s : Set α} (Ffs : forall x in s
, Tendsto (fun i => F i x)…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x

--- 原说明 ---
The map `(eVariationOn · s)` is lower semicontinuous for pointwise convergence *
on `s`*.
Pointwise convergence on `s` is encoded here as uniform convergence on the famil
y consisting of the
singletons of elements of `s`.
-/
protected theorem lowerSemicontinuous (s : Set α) :
    LowerSemicontinuous fun f : α →ᵤ[s.image singleton] E => eVariationOn f s := fun f ↦ by
  apply @lowerSemicontinuous_aux _ _ _ _ (UniformOnFun α E (s.image singleton)) id (𝓝 f) f s _
  simpa only [UniformOnFun.tendsto_iff_tendstoUniformlyOn, mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, tendstoUniformlyOn_singleton_iff_tendsto] using! @tendsto_id _ (𝓝 f)

set_option backward.isDefEq.respectTransparency false in
/-- The map `(eVariationOn · s)` is lower semicontinuous for uniform convergence on `s`. -/
/-
**eVariationOn.lowerSemicontinuous_uniformOn** 是 Mathlib 中的一个定理，位于命名空间 `eVariati
onOn`。
形式化陈述：lowerSemicontinuous_uniformOn (s : Set α) : LowerSemicontinuous fun f : α 
->ᵤ[{s}] E => eVariationOn f s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eVariationOn.lowerSemicontinuous_aux`：lowerSemicontinuous_aux {ι : Type*
} {F : ι -> α -> E} {p : Filter ι} {f : α -> E} {s : Set α} (Ffs : forall x in s
, Tendsto (fun i => F i x)…
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `TendstoUniformlyOn.mono`：TendstoUniformlyOn.mono (h : TendstoUniformlyOn
 F f p s) (h' : s' subseteq s) : TendstoUniformlyOn F f p s'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformOnFun.tendsto_iff_tendstoUniformlyOn`：∀ {α : Type u_1} {β : Type 
u_2} {ι : Type u_4} {p : Filter ι} [inst : UniformSpace β] {𝔖 : Set (Set α)}   {
F : ι → UniformOnFun α β 𝔖} {f : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s

--- 原说明 ---
The map `(eVariationOn · s)` is lower semicontinuous for uniform convergence on 
`s`.
-/
theorem lowerSemicontinuous_uniformOn (s : Set α) :
    LowerSemicontinuous fun f : α →ᵤ[{s}] E => eVariationOn f s := fun f ↦ by
  apply @lowerSemicontinuous_aux _ _ _ _ (UniformOnFun α E {s}) id (𝓝 f) f s _
  have := @tendsto_id _ (𝓝 f)
  rw [UniformOnFun.tendsto_iff_tendstoUniformlyOn] at this
  simp_rw [← tendstoUniformlyOn_singleton_iff_tendsto]
  exact fun x xs => (this s rfl).mono (singleton_subset_iff.mpr xs)
/-
**eVariationOn._root_.BoundedVariationOn.dist_le** 是 Mathlib 中的一个定理，位于命名空间 `eVar
iationOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.BoundedVariationOn.dist_le {E : Type*} [PseudoMetricSpace E] {f : α → E}
    {s : Set α} (h : BoundedVariationOn f s) {x y : α} (hx : x ∈ s) (hy : y ∈ s) :
    dist (f x) (f y) ≤ (eVariationOn f s).toReal := by
  rw [← ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg, ENNReal.ofReal_toReal h, ← edist_dist]
  exact edist_le f hx hy
/-
**eVariationOn._root_.BoundedVariationOn.sub_le** 是 Mathlib 中的一个定理，位于命名空间 `eVari
ationOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.BoundedVariationOn.sub_le {f : α → ℝ} {s : Set α} (h : BoundedVariationOn f s)
    {x y : α} (hx : x ∈ s) (hy : y ∈ s) : f x - f y ≤ (eVariationOn f s).toReal := by
  apply (le_abs_self _).trans
  rw [← Real.dist_eq]
  exact h.dist_le hx hy

/-- Consider a monotone function `u` parameterizing some points of a set `s`. Given `x ∈ s`, then
one can find another monotone function `v` parameterizing the same points as `u`, with `x` added.
In particular, the variation of a function along `u` is bounded by its variation along `v`. -/
/-
**eVariationOn.add_point** 是 Mathlib 中的一个定理，位于命名空间 `eVariationOn`。
形式化陈述：add_point (f : α -> E) {s : Set α} {x : α} (hx : x in s) (u : Nat -> α) (h
u : Monotone u) (us : forall i, u i in s) (n : Nat) : exists (v : Nat -> α) (m :
 Nat), Monotone v ∧ (forall i, v i in s) ∧ x in v '' Iio m ∧ (∑ i in Finset.rang
e n, edist (f (u (i + 1))) (f (u i))) <= ∑ j in Finset.range m, edist (f (v (j +
 1))) (f (v j))
参数：f : α -> E；hx : x in s；u : Nat -> α；hu : Monotone u；us : forall i, u i in s；n
 : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `Finset.sum_le_sum_of_subset_of_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [
inst : AddCommMonoid N] [inst_1 : Preorder N] {f : ι → N} {s t : Finset ι}   [Ad
dLeftMono N], s ⊆ t → (∀ i …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `Finset.range_subset_range._gcongr_1`：∀ {n m : ℕ}, n ≤ m → Finset.range n
 ⊆ Finset.range m
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
· 使用定理 `monotone_nat_of_le_succ`：monotone_nat_of_le_succ {f : Nat -> α} (hf : fo
rall n, f n <= f (n + 1)) : Monotone f
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `Nat.find_min`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) {
m : ℕ}, m < Nat.find H → ¬p m
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.range_eq_Ico`：∀ (a : ℕ), Finset.range a = Finset.Ico 0 a
· 使用定理 `Finset.sum_Ico_add`：∀ {α : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : AddCommMonoid α] [inst_2 : PartialOrder α]   [IsOrderedCancelAddM
onoid α]…
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Finset.Ico_subset_Ico`：Ico_subset_Ico (ha : a₂ <= a₁) (hb : b₁ <= b₂) : 
Ico a₁ b₁ subseteq Ico a₂ b₂
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Finset.sum_Ico_consecutive`：∀ {M : Type u_3} [inst : AddCommMonoid M] (f
 : ℕ → M) {m n k : ℕ},   m ≤ n → n ≤ k → ∑ i ∈ Finset.Ico m n, f i + ∑ i ∈ Finse
t.Ico n k, f i =…
· 使用定理 `Nat.succ_pred_eq_of_pos`：∀ {n : ℕ}, 0 < n → n.pred.succ = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.Ico_succ_singleton`：Ico_succ_singleton : Ico a (a + 1) = {a}
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
Consider a monotone function `u` parameterizing some points of a set `s`. Given 
`x ∈ s`, then
one can find another monotone function `v` parameterizing the same points as `u`
, with `x` added.
In particular, the variation of a function along `u` is bounded by its variation
 along `v`.
-/
theorem add_point (f : α → E) {s : Set α} {x : α} (hx : x ∈ s) (u : ℕ → α) (hu : Monotone u)
    (us : ∀ i, u i ∈ s) (n : ℕ) :
    ∃ (v : ℕ → α) (m : ℕ), Monotone v ∧ (∀ i, v i ∈ s) ∧ x ∈ v '' Iio m ∧
      (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) ≤
        ∑ j ∈ Finset.range m, edist (f (v (j + 1))) (f (v j)) := by
  rcases le_or_gt (u n) x with (h | h)
  · let v i := if i ≤ n then u i else x
    refine ⟨v, n + 2, by grind [Monotone], by grind, (mem_image _ _ _).2 ⟨n + 1, by grind⟩, ?_⟩
    calc
      (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) =
          ∑ i ∈ Finset.range n, edist (f (v (i + 1))) (f (v i)) := by grind [Finset.sum_congr]
      _ ≤ ∑ j ∈ Finset.range (n + 2), edist (f (v (j + 1))) (f (v j)) := by
        gcongr
        apply Nat.le_add_right
  have exists_N : ∃ N, N ≤ n ∧ x < u N := ⟨n, le_rfl, h⟩
  let N := Nat.find exists_N
  have hN : N ≤ n ∧ x < u N := Nat.find_spec exists_N
  let w : ℕ → α := fun i => if i < N then u i else if i = N then x else u (i - 1)
  have hw : Monotone w := by
    apply monotone_nat_of_le_succ fun i => ?_
    rcases lt_trichotomy (i + 1) N with (hi | hi | hi)
    · grind [Monotone]
    · have A : i < N := hi ▸ i.lt_succ_self
      have := Nat.find_min exists_N A
      grind
    · grind [Monotone]
  refine ⟨w, n + 1, hw, by grind, (mem_image _ _ _).2 ⟨N, by grind⟩, ?_⟩
  rcases eq_zero_or_pos N with (Npos | Npos)
  · calc
      (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) =
          ∑ i ∈ Finset.range n, edist (f (w (1 + i + 1))) (f (w (1 + i))) := by grind
      _ = ∑ i ∈ Finset.Ico 1 (n + 1), edist (f (w (i + 1))) (f (w i)) := by
        rw [Finset.range_eq_Ico]
        exact Finset.sum_Ico_add (fun i => edist (f (w (i + 1))) (f (w i))) 0 n 1
      _ ≤ ∑ j ∈ Finset.range (n + 1), edist (f (w (j + 1))) (f (w j)) := by
        rw [Finset.range_eq_Ico]
        gcongr
        exact zero_le_one
  · calc
      (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) =
          ((∑ i ∈ Finset.Ico 0 (N - 1), edist (f (u (i + 1))) (f (u i))) +
              ∑ i ∈ Finset.Ico (N - 1) N, edist (f (u (i + 1))) (f (u i))) +
            ∑ i ∈ Finset.Ico N n, edist (f (u (i + 1))) (f (u i)) := by
        rw [Finset.sum_Ico_consecutive, Finset.sum_Ico_consecutive, Finset.range_eq_Ico] <;> grind
      _ = (∑ i ∈ Finset.Ico 0 (N - 1), edist (f (w (i + 1))) (f (w i))) +
              edist (f (u N)) (f (u (N - 1))) +
            ∑ i ∈ Finset.Ico N n, edist (f (w (1 + i + 1))) (f (w (1 + i))) := by
        congr 1
        · congr 1
          · grind [Finset.sum_congr]
          · have A : N - 1 + 1 = N := Nat.succ_pred_eq_of_pos Npos
            have : Finset.Ico (N - 1) N = {N - 1} := by rw [← Nat.Ico_succ_singleton, A]
            simp only [this, A, Finset.sum_singleton]
        · grind [Finset.sum_congr]
      _ = (∑ i ∈ Finset.Ico 0 (N - 1), edist (f (w (i + 1))) (f (w i))) +
              edist (f (w (N + 1))) (f (w (N - 1))) +
            ∑ i ∈ Finset.Ico (N + 1) (n + 1), edist (f (w (i + 1))) (f (w i)) := by
        congr 1
        · grind
        · exact Finset.sum_Ico_add (fun i => edist (f (w (i + 1))) (f (w i))) N n 1
      _ ≤ ((∑ i ∈ Finset.Ico 0 (N - 1), edist (f (w (i + 1))) (f (w i))) +
              ∑ i ∈ Finset.Ico (N - 1) (N + 1), edist (f (w (i + 1))) (f (w i))) +
            ∑ i ∈ Finset.Ico (N + 1) (n + 1), edist (f (w (i + 1))) (f (w i)) := by
        refine add_le_add (add_le_add le_rfl ?_) le_rfl
        have A : N - 1 + 1 = N := Nat.succ_pred_eq_of_pos Npos
        have B : N - 1 + 1 < N + 1 := A.symm ▸ N.lt_succ_self
        have C : N - 1 < N + 1 := lt_of_le_of_lt N.pred_le N.lt_succ_self
        rw [Finset.sum_eq_sum_Ico_succ_bot C, Finset.sum_eq_sum_Ico_succ_bot B, A, Finset.Ico_self,
          Finset.sum_empty, add_zero, add_comm (edist _ _)]
        exact edist_triangle _ _ _
      _ = ∑ j ∈ Finset.range (n + 1), edist (f (w (j + 1))) (f (w j)) := by
        rw [Finset.sum_Ico_consecutive, Finset.sum_Ico_consecutive, Finset.range_eq_Ico] <;> grind

/-- The variation of a function on the union of two sets `s` and `t`, with `s` to the left of `t`,
bounds the sum of the variations along `s` and `t`. -/
/-
**eVariationOn.add_le_union** 是 Mathlib 中的一个定理，位于命名空间 `eVariationOn`。
形式化陈述：add_le_union (f : α -> E) {s t : Set α} (h : forall x in s, forall y in t,
 x <= y) : eVariationOn f s + eVariationOn f t <= eVariationOn f (s union t)
参数：f : α -> E；h : forall x in s, forall y in t, x <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eVariationOn.subsingleton`：∀ {α : Type u_1} [inst : LinearOrder α] {E : 
Type u_2} [inst_1 : PseudoEMetricSpace E] (f : α → E) {s : Set α},   s.Subsingle
ton → eVariatio…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Set.empty_union`：empty_union (a : Set α) : ∅ union a = a
· 使用定理 `eVariationOn.nonempty_monotone_mem`：nonempty_monotone_mem {s : Set α} (h
s : s.Nonempty) : Nonempty { u // Monotone u ∧ forall i : Nat, u i in s }
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用引理 `ENNReal.iSup_add_iSup_le`：iSup_add_iSup_le [Nonempty ι] [Nonempty κ] {g 
: κ -> Real>=0∞} (h : forall i j, f i + g j <= a) : iSup f + iSup g <= a
· 使用定理 `instNonemptyProd`：∀ {α : Type u_1} {β : Type u_2} [h1 : Nonempty α] [h2 
: Nonempty β], Nonempty (α × β)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Finset.range_eq_Ico`：∀ (a : ℕ), Finset.range a = Finset.Ico 0 a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `_private.Mathlib.Topology.EMetricSpace.BoundedVariation.0.eVariationOn.a
dd_le_union._abel_1_3`：∀ (n : ℕ), n + 1 = 0 + (n + 1)
· 使用定理 `_private.Mathlib.Topology.EMetricSpace.BoundedVariation.0.eVariationOn.a
dd_le_union._abel_1_4`：∀ (n m : ℕ), n + 1 + m = m + (n + 1)
· 使用定理 `Finset.sum_Ico_add`：∀ {α : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : AddCommMonoid α] [inst_2 : PartialOrder α]   [IsOrderedCancelAddM
onoid α]…
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Finset.sum_union`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   Disjoint s₁ s₂ → ∑
 x ∈ s…
· 使用定理 `Finset.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s 
-> a ∉ t
· 使用定理 `Finset.sum_le_sum_of_subset_of_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [
inst : AddCommMonoid N] [inst_1 : Preorder N] {f : ι → N} {s t : Finset ι}   [Ad
dLeftMono N], s ⊆ t → (∀ i …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
The variation of a function on the union of two sets `s` and `t`, with `s` to th
e left of `t`,
bounds the sum of the variations along `s` and `t`.
-/
theorem add_le_union (f : α → E) {s t : Set α} (h : ∀ x ∈ s, ∀ y ∈ t, x ≤ y) :
    eVariationOn f s + eVariationOn f t ≤ eVariationOn f (s ∪ t) := by
  by_cases hs : s = ∅
  · simp [hs]
  have : Nonempty { u // Monotone u ∧ ∀ i : ℕ, u i ∈ s } :=
    nonempty_monotone_mem (nonempty_iff_ne_empty.2 hs)
  by_cases ht : t = ∅
  · simp [ht]
  have : Nonempty { u // Monotone u ∧ ∀ i : ℕ, u i ∈ t } :=
    nonempty_monotone_mem (nonempty_iff_ne_empty.2 ht)
  refine ENNReal.iSup_add_iSup_le ?_
  /- We start from two sequences `u` and `v` along `s` and `t` respectively, and we build a new
    sequence `w` along `s ∪ t` by juxtaposing them. Its variation is larger than the sum of the
    variations. -/
  rintro ⟨n, ⟨u, hu, us⟩⟩ ⟨m, ⟨v, hv, vt⟩⟩
  let w i := if i ≤ n then u i else v (i - (n + 1))
  calc
    ((∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) +
          ∑ i ∈ Finset.range m, edist (f (v (i + 1))) (f (v i))) =
        (∑ i ∈ Finset.range n, edist (f (w (i + 1))) (f (w i))) +
          ∑ i ∈ Finset.range m, edist (f (w (n + 1 + i + 1))) (f (w (n + 1 + i))) := by
      dsimp only [w]
      congr 1
      · grind [Finset.sum_congr]
      · grind
    _ = (∑ i ∈ Finset.range n, edist (f (w (i + 1))) (f (w i))) +
          ∑ i ∈ Finset.Ico (n + 1) (n + 1 + m), edist (f (w (i + 1))) (f (w i)) := by
      congr 1
      rw [Finset.range_eq_Ico]
      convert!
          Finset.sum_Ico_add (fun i : ℕ => edist (f (w (i + 1))) (f (w i))) 0 m (n + 1) using 3 <;>
        abel
    _ ≤ ∑ i ∈ Finset.range (n + 1 + m), edist (f (w (i + 1))) (f (w i)) := by
      rw [← Finset.sum_union]
      · gcongr; grind
      · exact Finset.disjoint_left.2 (by grind)
    _ ≤ eVariationOn f (s ∪ t) := sum_le (by grind [Monotone]) (by grind)

/-- If a set `s` is to the left of a set `t`, and both contain the boundary point `x`, then
the variation of `f` along `s ∪ t` is the sum of the variations. -/
/-
**eVariationOn.union** 是 Mathlib 中的一个定理，位于命名空间 `eVariationOn`。
形式化陈述：union (f : α -> E) {s t : Set α} {x : α} (hs : IsGreatest s x) (ht : IsLea
st t x) : eVariationOn f (s union t) = eVariationOn f s + eVariationOn f t
参数：f : α -> E；hs : IsGreatest s x；ht : IsLeast t x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `eVariationOn.add_le_union`：add_le_union (f : α -> E) {s t : Set α} (h : 
forall x in s, forall y in t, x <= y) : eVariationOn f s + eVariationOn f t <= e
VariationOn f (…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `eVariationOn.add_point`：add_point (f : α -> E) {s : Set α} {x : α} (hx :
 x in s) (u : Nat -> α) (hu : Monotone u) (us : forall i, u i in s) (n : Nat) : 
exists (v : …
· 使用定理 `Set.mem_union_left`：mem_union_left {x : α} {a : Set α} (b : Set α) : x i
n a -> x in a union b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.range_eq_Ico`：∀ (a : ℕ), Finset.range a = Finset.Ico 0 a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_Ico_consecutive`：∀ {M : Type u_3} [inst : AddCommMonoid M] (f
 : ℕ → M) {m n k : ℕ},   m ≤ n → n ≤ k → ∑ i ∈ Finset.Ico m n, f i + ∑ i ∈ Finse
t.Ico n k, f i =…
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `eVariationOn.sum_le_of_monotoneOn_Icc`：sum_le_of_monotoneOn_Icc {f : α -
> E} {s : Set α} {m n : Nat} {u : Nat -> α} (hu : MonotoneOn u (Icc m n)) (us : 
forall i in Icc m n, u i in…
· 使用定理 `Monotone.monotoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Monotone f → ∀ (s : Set α), MonotoneOn f s
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b

--- 原说明 ---
If a set `s` is to the left of a set `t`, and both contain the boundary point `x
`, then
the variation of `f` along `s ∪ t` is the sum of the variations.
-/
theorem union (f : α → E) {s t : Set α} {x : α} (hs : IsGreatest s x) (ht : IsLeast t x) :
    eVariationOn f (s ∪ t) = eVariationOn f s + eVariationOn f t := by
  apply (eVariationOn.add_le_union f fun a ha b hb ↦ (hs.2 ha).trans (ht.2 hb)).antisymm'
  refine iSup_le fun ⟨n, ⟨u, hu, ust⟩⟩ ↦ ?_
  obtain ⟨v, m, hv, vst, ⟨N, hN, rfl⟩, huv⟩ :=
    eVariationOn.add_point f (mem_union_left t hs.1) u hu ust n
  apply huv.trans
  rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ zero_le hN.le]
  apply add_le_add <;> refine sum_le_of_monotoneOn_Icc (hv.monotoneOn _) fun i hi ↦ ?_
  · exact (vst i).elim id (fun h ↦ (hv hi.2).antisymm (ht.2 h) ▸ hs.1)
  · exact (vst i).elim (fun h ↦ (hs.2 h).antisymm (hv hi.1) ▸ ht.1) id
/-
**eVariationOn.Icc_add_Icc** 是 Mathlib 中的一个定理，位于命名空间 `eVariationOn`。
形式化陈述：Icc_add_Icc (f : α -> E) {s : Set α} {a b c : α} (hab : a <= b) (hbc : b <
= c) (hb : b in s) : eVariationOn f (s inter Icc a b) + eVariationOn f (s inter 
Icc b c) = eVariationOn f (s inter Icc a c)
参数：f : α -> E；hab : a <= b；hbc : b <= c；hb : b in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Set.Icc_subset_Iic_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Icc a b ⊆ Set.Iic b
· 使用定理 `Set.Icc_subset_Ici_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Icc b a ⊆ Set.Ici b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eVariationOn.union`：union (f : α -> E) {s t : Set α} {x : α} (hs : IsGre
atest s x) (ht : IsLeast t x) : eVariationOn f (s union t) = eVariationOn f s + 
eVariati…
· 使用定理 `Set.inter_union_distrib_left`：inter_union_distrib_left (s t u : Set α) :
 s inter (t union u) = s inter t union s inter u
· 使用定理 `Set.Icc_union_Icc_eq_Icc`：Icc_union_Icc_eq_Icc (h₁ : a <= b) (h₂ : b <= 
c) : Icc a b union Icc b c = Icc a c
-/
theorem Icc_add_Icc (f : α → E) {s : Set α} {a b c : α} (hab : a ≤ b) (hbc : b ≤ c) (hb : b ∈ s) :
    eVariationOn f (s ∩ Icc a b) + eVariationOn f (s ∩ Icc b c) = eVariationOn f (s ∩ Icc a c) := by
  have A : IsGreatest (s ∩ Icc a b) b :=
    ⟨⟨hb, hab, le_rfl⟩, inter_subset_right.trans Icc_subset_Iic_self⟩
  have B : IsLeast (s ∩ Icc b c) b :=
    ⟨⟨hb, le_rfl, hbc⟩, inter_subset_right.trans Icc_subset_Ici_self⟩
  rw [← eVariationOn.union f A B, ← inter_union_distrib_left, Icc_union_Icc_eq_Icc hab hbc]
/-
**eVariationOn.sum** 是 Mathlib 中的一个定理，位于命名空间 `eVariationOn`。
形式化陈述：sum (f : α -> E) {s : Set α} {E : Nat -> α} (hE : Monotone E) {n : Nat} (h
n : forall i, 0 < i -> i < n -> E i in s) : ∑ i in Finset.range n, eVariationOn 
f (s inter Icc (E i) (E (i + 1))) = eVariationOn f (s inter Icc (E 0) (E n))
参数：f : α -> E；hE : Monotone E；hn : forall i, 0 < i -> i < n -> E i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `eVariationOn.subsingleton`：∀ {α : Type u_1} [inst : LinearOrder α] {E : 
Type u_2} [inst_1 : PseudoEMetricSpace E] (f : α → E) {s : Set α},   s.Subsingle
ton → eVariatio…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eVariationOn.Icc_add_Icc`：Icc_add_Icc (f : α -> E) {s : Set α} {a b c : 
α} (hab : a <= b) (hbc : b <= c) (hb : b in s) : eVariationOn f (s inter Icc a b
) + eVariation…
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
-/
theorem sum (f : α → E) {s : Set α} {E : ℕ → α} (hE : Monotone E) {n : ℕ}
    (hn : ∀ i, 0 < i → i < n → E i ∈ s) :
    ∑ i ∈ Finset.range n, eVariationOn f (s ∩ Icc (E i) (E (i + 1))) =
      eVariationOn f (s ∩ Icc (E 0) (E n)) := by
  induction n with
  | zero => simp [Subsingleton.inter_singleton]
  | succ n ih =>
    by_cases hn₀ : n = 0
    · simp [hn₀]
    rw [← Icc_add_Icc (b := E n)]
    · rw [← ih (by intros; apply hn <;> omega), Finset.sum_range_succ]
    · apply hE; lia
    · apply hE; lia
    · apply hn <;> omega
/-
**eVariationOn.sum'** 是 Mathlib 中的一个定理，位于命名空间 `eVariationOn`。
形式化陈述：sum' (f : α -> E) {I : Nat -> α} (hI : Monotone I) {n : Nat} : ∑ i in Fins
et.range n, eVariationOn f (Icc (I i) (I (i + 1))) = eVariationOn f (Icc (I 0) (
I n))
参数：f : α -> E；hI : Monotone I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Set.Icc_subset_Icc`：Icc_subset_Icc (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Icc
 a₁ b₁ subseteq Icc a₂ b₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eVariationOn.sum`：sum (f : α -> E) {s : Set α} {E : Nat -> α} (hE : Mono
tone E) {n : Nat} (hn : forall i, 0 < i -> i < n -> E i in s) : ∑ i in Finset.ra
nge n,…
· 使用定理 `Set.mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
cc a b ↔ a ≤ x ∧ x ≤ b
-/
theorem sum' (f : α → E) {I : ℕ → α} (hI : Monotone I) {n : ℕ} :
    ∑ i ∈ Finset.range n, eVariationOn f (Icc (I i) (I (i + 1)))
     = eVariationOn f (Icc (I 0) (I n)) := by
  convert!
      sum f hI (s := Icc (I 0) (I n)) (n := n)
        (hn := by intros; rw [mem_Icc]; constructor <;> (apply hI; lia))
    with i hi
  · simp only [right_eq_inter]
    gcongr <;> (apply hI; rw [Finset.mem_range] at hi; lia)
  · simp

/-- The variation of `f` on a two-point set `{a, b}` is the distance between its two values. -/
@[simp]
/-
**eVariationOn.pair** 是 Mathlib 中的一个定理，位于命名空间 `eVariationOn`。
形式化陈述：pair (f : α -> E) (a b : α) : eVariationOn f {a, b} = edist (f a) (f b)
参数：f : α -> E；a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eVariationOn.eVariationOn_eq_strictMonoOn`：eVariationOn_eq_strictMonoOn 
(f : α -> E) (s : Set α) : eVariationOn f s = ⨆ p : (n : Nat) × { u : Nat -> α /
/ StrictMonoOn u (Iic n) ∧ fora…
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用引理 `one_lt_two`：one_lt_two [AddLeftStrictMono α] : (1 : α) < 2
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
· 使用定理 `eVariationOn.edist_le`：edist_le (f : α -> E) {s : Set α} {x y : α} (hx :
 x in s) (hy : y in s) : edist (f x) (f y) <= eVariationOn f s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Set.pair_comm`：pair_comm (a b : α) : ({a, b} : Set α) = {b, a}
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
The variation of `f` on a two-point set `{a, b}` is the distance between its two
 values.
-/
theorem pair (f : α → E) (a b : α) : eVariationOn f {a, b} = edist (f a) (f b) := by
  wlog hab : a ≤ b generalizing a b
  · simpa [edist_comm, pair_comm] using this b a (le_of_not_ge hab)
  · apply le_antisymm _ (edist_le f (by simp) (by simp))
    simp only [eVariationOn_eq_strictMonoOn, iSup_le_iff]
    rintro ⟨n, u, hmono, hi⟩
    rcases (by omega : n = 0 ∨ n = 1 ∨ 2 ≤ n) with rfl | rfl | hn
    · simp
    · have := hmono (by simp) (by simp) zero_lt_one
      simp [(by grind : u 0 = a), (by grind : u 1 = b), edist_comm]
    · have := hmono (by simp) (by grind) zero_lt_one
      have := hmono (by grind) (by grind) one_lt_two
      grind

/-- A generalization of `eVariationOn.union` in which the greatest element of `s` is allowed to lie
to the left of the least element of `t`. -/
/-
**eVariationOn.union'** 是 Mathlib 中的一个定理，位于命名空间 `eVariationOn`。
形式化陈述：union' (f : α -> E) {s t : Set α} {x y : α} (hs : IsGreatest s x) (ht : Is
Least t y) (hxy : x <= y) : eVariationOn f (s union t) = eVariationOn f s + edis
t (f x) (f y) + eVariationOn f t
参数：f : α -> E；hs : IsGreatest s x；ht : IsLeast t y；hxy : x <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eVariationOn.union`：union (f : α -> E) {s t : Set α} {x : α} (hs : IsGre
atest s x) (ht : IsLeast t x) : eVariationOn f (s union t) = eVariationOn f s + 
eVariati…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.union_insert`：union_insert : s union insert a t = insert a (s union 
t)
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `upperBounds_insert`：upperBounds_insert (a : α) (s : Set α) : upperBounds
 (insert a s) = Ici a inter upperBounds s
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `upperBounds_mono_mem`：upperBounds_mono_mem ⦃a b⦄ (hab : a <= b) : a in u
pperBounds s -> b in upperBounds s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `lowerBounds_insert`：∀ {α : Type u_1} [inst : Preorder α] (a : α) (s : Se
t α), lowerBounds (insert a s) = Set.Iic a ∩ lowerBounds s
· 使用定理 `lowerBounds_singleton`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, low
erBounds {a} = Set.Iic a
· 使用定理 `Set.Iic_inter_Iic`：Iic_inter_Iic {a b : α} : Iic a inter Iic b = Iic (a 
⊓ b)
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `eVariationOn.pair`：pair (f : α -> E) (a b : α) : eVariationOn f {a, b} =
 edist (f a) (f b)

--- 原说明 ---
A generalization of `eVariationOn.union` in which the greatest element of `s` is
 allowed to lie
to the left of the least element of `t`.
-/
theorem union' (f : α → E) {s t : Set α} {x y : α} (hs : IsGreatest s x) (ht : IsLeast t y)
    (hxy : x ≤ y) :
    eVariationOn f (s ∪ t) = eVariationOn f s + edist (f x) (f y) + eVariationOn f t := by
  rw [(by grind [hs.1, ht.1] : s ∪ t = (s ∪ {x, y}) ∪ t), union f _ ht, union f hs]
  <;> simp [IsLeast, IsGreatest, hxy, upperBounds_mono_mem hxy hs.2]

/-- The variation of `f` along the image of `{0, …, n}` under a monotone sequence `u` is the sum of
the distances between consecutive values. -/
/-
**eVariationOn.image_range_of_monotone** 是 Mathlib 中的一个定理，位于命名空间 `eVariationOn`。
形式化陈述：image_range_of_monotone (f : α -> E) {u : Nat -> α} (hu : Monotone u) (n :
 Nat) : eVariationOn f (u '' Iic n) = ∑ i in .range n, edist (f (u i)) (f (u (i 
+ 1)))
参数：f : α -> E；hu : Monotone u；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `eVariationOn.subsingleton`：∀ {α : Type u_1} [inst : LinearOrder α] {E : 
Type u_2} [inst_1 : PseudoEMetricSpace E] (f : α → E) {s : Set α},   s.Subsingle
ton → eVariatio…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eVariationOn.union`：union (f : α -> E) {s t : Set α} {x : α} (hs : IsGre
atest s x) (ht : IsLeast t x) : eVariationOn f (s union t) = eVariationOn f s + 
eVariati…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `lowerBounds_insert`：∀ {α : Type u_1} [inst : Preorder α] (a : α) (s : Se
t α), lowerBounds (insert a s) = Set.Iic a ∩ lowerBounds s
· 使用定理 `lowerBounds_singleton`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, low
erBounds {a} = Set.Iic a
· 使用定理 `Set.Iic_inter_Iic`：Iic_inter_Iic {a b : α} : Iic a inter Iic b = Iic (a 
⊓ b)
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `eVariationOn.pair`：pair (f : α -> E) (a b : α) : eVariationOn f {a, b} =
 edist (f a) (f b)
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n

--- 原说明 ---
The variation of `f` along the image of `{0, …, n}` under a monotone sequence `u
` is the sum of
the distances between consecutive values.
-/
theorem image_range_of_monotone (f : α → E) {u : ℕ → α} (hu : Monotone u) (n : ℕ) :
    eVariationOn f (u '' Iic n) = ∑ i ∈ .range n, edist (f (u i)) (f (u (i + 1))) := by
  induction n with
  | zero => simp [Iic]
  | succ n ih =>
    rw [(by grind : u '' Iic (n + 1) = u '' Iic n ∪ {u n, u (n + 1)}), union f]
    · simp [Finset.sum_range_succ, ih]
    · simpa [IsGreatest, upperBounds] using ⟨⟨n, by simp⟩, fun a ha ↦ hu ha⟩
    · simp [IsLeast, hu n.le_succ]
/-
**eVariationOn._root_.BoundedVariationOn.of_finset** 是 Mathlib 中的一个定理，位于命名空间 `eV
ariationOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem _root_.BoundedVariationOn.of_finset {E} [PseudoMetricSpace E] (f : α → E)
    (s : Finset α) : BoundedVariationOn f s := by
  obtain rfl | hne := s.eq_empty_or_nonempty
  · simp [BoundedVariationOn]
  have := s.card_pos.2 hne
  let u : ℕ → α := fun n ↦ s.orderEmbOfFin rfl ⟨min n (s.card - 1), by grind⟩
  have : s = u '' Iic (s.card - 1) := by
    ext
    simp only [← s.range_orderEmbOfFin rfl, mem_image, mem_Iic, mem_range, u]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨i.val, by grind⟩
    · rintro ⟨i, hi, rfl⟩; use ⟨i, by omega⟩; congr; omega
  have hmono : Monotone u := fun _ _ _ ↦ OrderEmbedding.monotone _ (by grind)
  simp [BoundedVariationOn, this, image_range_of_monotone f hmono _]

/-- A function valued in a metric space has bounded variation on any `Finset` (the finiteness of
the space's distances makes the total variation finite). -/
@[simp]
/-
**eVariationOn._root_.BoundedVariationOn.of_finite** 是 Mathlib 中的一个定理，位于命名空间 `eV
ariationOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function valued in a metric space has bounded variation on any `Finset` (the f
initeness of
the space's distances makes the total variation finite).
-/
theorem _root_.BoundedVariationOn.of_finite {E} [PseudoMetricSpace E] (f : α → E) (s : Set α)
[Finite s] : BoundedVariationOn f s := by
  simpa using BoundedVariationOn.of_finset f s.toFinite.toFinset

/-! ### Composition of bounded variation functions with monotone functions -/

section Monotone

variable {β : Type*} [LinearOrder β]

/-
**eVariationOn.comp_le_of_monotoneOn** 是 Mathlib 中的一个定理，位于命名空间 `eVariationOn`。
形式化陈述：comp_le_of_monotoneOn (f : α -> E) {s : Set α} {t : Set β} (φ : β -> α) (h
φ : MonotoneOn φ t) (φst : MapsTo φ t s) : eVariationOn (f ∘ φ) t <= eVariationO
n f s
参数：f : α -> E；φ : β -> α；hφ : MonotoneOn φ t；φst : MapsTo φ t s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem comp_le_of_monotoneOn (f : α → E) {s : Set α} {t : Set β} (φ : β → α) (hφ : MonotoneOn φ t)
    (φst : MapsTo φ t s) : eVariationOn (f ∘ φ) t ≤ eVariationOn f s :=
  iSup_le fun ⟨n, u, hu, ut⟩ =>
    le_iSup_of_le ⟨n, φ ∘ u, fun x y xy => hφ (ut x) (ut y) (hu xy), fun i => φst (ut i)⟩ le_rfl
/-
**eVariationOn.comp_le_of_antitoneOn** 是 Mathlib 中的一个定理，位于命名空间 `eVariationOn`。
形式化陈述：comp_le_of_antitoneOn (f : α -> E) {s : Set α} {t : Set β} (φ : β -> α) (h
φ : AntitoneOn φ t) (φst : MapsTo φ t s) : eVariationOn (f ∘ φ) t <= eVariationO
n f s
参数：f : α -> E；φ : β -> α；hφ : AntitoneOn φ t；φst : MapsTo φ t s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_range_reflect`：sum_range_reflect {δ : Type*} [AddCommMonoid δ
] (f : Nat -> δ) (n : Nat) : (∑ j in range n, f (n - 1 - j)) = ∑ j in range n, f
 j
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Nat.sub_le_sub_left`：∀ {n m : ℕ}, n ≤ m → ∀ (k : ℕ), k - m ≤ k - n
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem comp_le_of_antitoneOn (f : α → E) {s : Set α} {t : Set β} (φ : β → α) (hφ : AntitoneOn φ t)
    (φst : MapsTo φ t s) : eVariationOn (f ∘ φ) t ≤ eVariationOn f s := by
  refine iSup_le ?_
  rintro ⟨n, u, hu, ut⟩
  rw [← Finset.sum_range_reflect]
  refine (Finset.sum_congr rfl fun x hx => ?_).trans_le <| le_iSup_of_le
    ⟨n, fun i => φ (u <| n - i), fun x y xy => hφ (ut _) (ut _) (hu <| Nat.sub_le_sub_left xy n),
      fun i => φst (ut _)⟩
    le_rfl
  rw [Finset.mem_range] at hx
  dsimp only [Subtype.coe_mk, Function.comp_apply]
  rw [edist_comm]
  congr 4 <;> lia
/-
**eVariationOn.comp_eq_of_monotoneOn** 是 Mathlib 中的一个定理，位于命名空间 `eVariationOn`。
形式化陈述：comp_eq_of_monotoneOn (f : α -> E) {t : Set β} (φ : β -> α) (hφ : Monotone
On φ t) : eVariationOn (f ∘ φ) t = eVariationOn f (φ '' t)
参数：f : α -> E；φ : β -> α；hφ : MonotoneOn φ t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `eVariationOn.comp_le_of_monotoneOn`：comp_le_of_monotoneOn (f : α -> E) {
s : Set α} {t : Set β} (φ : β -> α) (hφ : MonotoneOn φ t) (φst : MapsTo φ t s) :
 eVariationOn (f ∘ φ) t …
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.eq_empty_of_isEmpty`：eq_empty_of_isEmpty (s : Set α) [IsEmpty s] : s
 = ∅
· 使用定理 `instIsEmptySubtype`：∀ {α : Sort u} [IsEmpty α] (p : α → Prop), IsEmpty (
Subtype p)
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eVariationOn.subsingleton`：∀ {α : Type u_1} [inst : LinearOrder α] {E : 
Type u_2} [inst_1 : PseudoEMetricSpace E] (f : α → E) {s : Set α},   s.Subsingle
ton → eVariatio…
· 使用定理 `Set.SurjOn.rightInvOn_invFunOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set
 α} {t : Set β} {f : α → β} [inst : Nonempty α],   Set.SurjOn f s t → Set.RightI
nvOn (Function.invFu…
· 使用定理 `Set.surjOn_image`：surjOn_image (f : α -> β) (s : Set α) : SurjOn f s (f 
'' s)
· 使用定理 `Set.SurjOn.mapsTo_invFunOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} 
{t : Set β} {f : α → β} [inst : Nonempty α],   Set.SurjOn f s t → Set.MapsTo (Fu
nction.invFunOn …
· 使用定理 `Function.monotoneOn_of_rightInvOn_of_mapsTo`：monotoneOn_of_rightInvOn_of
_mapsTo {α β : Type*} [PartialOrder α] [LinearOrder β] {φ : β -> α} {ψ : α -> β}
 {t : Set β} {s : Set α} (hφ : Mo…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eVariationOn.eq_of_eqOn`：eq_of_eqOn {f f' : α -> E} {s : Set α} (h : EqO
n f f' s) : eVariationOn f s = eVariationOn f' s
· 使用定理 `Set.EqOn.comp_left`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : 
Set α} {f₁ f₂ : α → β} {g : β → γ},   Set.EqOn f₁ f₂ s → Set.EqOn (g ∘ f₁) (g ∘ 
f₂) s
-/
theorem comp_eq_of_monotoneOn (f : α → E) {t : Set β} (φ : β → α) (hφ : MonotoneOn φ t) :
    eVariationOn (f ∘ φ) t = eVariationOn f (φ '' t) := by
  apply le_antisymm (comp_le_of_monotoneOn f φ hφ (mapsTo_image φ t))
  cases isEmpty_or_nonempty β
  · simp [Set.eq_empty_of_isEmpty]
  let ψ := φ.invFunOn t
  have ψφs : EqOn (φ ∘ ψ) id (φ '' t) := (surjOn_image φ t).rightInvOn_invFunOn
  have ψts : MapsTo ψ (φ '' t) t := (surjOn_image φ t).mapsTo_invFunOn
  have hψ : MonotoneOn ψ (φ '' t) := Function.monotoneOn_of_rightInvOn_of_mapsTo hφ ψφs ψts
  change eVariationOn (f ∘ id) (φ '' t) ≤ eVariationOn (f ∘ φ) t
  rw [← eq_of_eqOn (ψφs.comp_left : EqOn (f ∘ φ ∘ ψ) (f ∘ id) (φ '' t))]
  exact comp_le_of_monotoneOn _ ψ hψ ψts
/-
**eVariationOn.comp_inter_Icc_eq_of_monotoneOn** 是 Mathlib 中的一个定理，位于命名空间 `eVaria
tionOn`。
形式化陈述：comp_inter_Icc_eq_of_monotoneOn (f : α -> E) {t : Set β} (φ : β -> α) (hφ 
: MonotoneOn φ t) {x y : β} (hx : x in t) (hy : y in t) : eVariationOn (f ∘ φ) (
t inter Icc x y) = eVariationOn f (φ '' t inter Icc (φ x) (φ y))
参数：f : α -> E；φ : β -> α；hφ : MonotoneOn φ t；hx : x in t；hy : y in t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `eVariationOn.comp_eq_of_monotoneOn`：comp_eq_of_monotoneOn (f : α -> E) {
t : Set β} (φ : β -> α) (hφ : MonotoneOn φ t) : eVariationOn (f ∘ φ) t = eVariat
ionOn f (φ '' t)
· 使用定理 `MonotoneOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s s₂ : Set α} {f : α →
 β} [inst : Preorder α] [inst_1 : Preorder β],   MonotoneOn f s → s₂ ⊆ s → Monot
oneOn…
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `eVariationOn.subsingleton`：∀ {α : Type u_1} [inst : LinearOrder α] {E : 
Type u_2} [inst_1 : PseudoEMetricSpace E] (f : α → E) {s : Set α},   s.Subsingle
ton → eVariatio…
· 使用定理 `Set.Subsingleton.anti`：∀ {α : Type u} {s t : Set α}, t.Subsingleton → s 
⊆ t → s.Subsingleton
· 使用引理 `Set.subsingleton_Icc_of_ge`：subsingleton_Icc_of_ge (hba : b <= a) : Set.
Subsingleton (Icc a b)
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
theorem comp_inter_Icc_eq_of_monotoneOn (f : α → E) {t : Set β} (φ : β → α) (hφ : MonotoneOn φ t)
    {x y : β} (hx : x ∈ t) (hy : y ∈ t) :
    eVariationOn (f ∘ φ) (t ∩ Icc x y) = eVariationOn f (φ '' t ∩ Icc (φ x) (φ y)) := by
  rcases le_total x y with (h | h)
  · convert! comp_eq_of_monotoneOn f φ (hφ.mono Set.inter_subset_left)
    apply le_antisymm
    · rintro _ ⟨⟨u, us, rfl⟩, vφx, vφy⟩
      rcases le_total x u with (xu | ux)
      · rcases le_total u y with (uy | yu)
        · exact ⟨u, ⟨us, ⟨xu, uy⟩⟩, rfl⟩
        · rw [le_antisymm vφy (hφ hy us yu)]
          exact ⟨y, ⟨hy, ⟨h, le_rfl⟩⟩, rfl⟩
      · rw [← le_antisymm vφx (hφ us hx ux)]
        exact ⟨x, ⟨hx, ⟨le_rfl, h⟩⟩, rfl⟩
    · rintro _ ⟨u, ⟨⟨hu, xu, uy⟩, rfl⟩⟩
      exact ⟨⟨u, hu, rfl⟩, ⟨hφ hx hu xu, hφ hu hy uy⟩⟩
  · rw [eVariationOn.subsingleton, eVariationOn.subsingleton]
    exacts [(Set.subsingleton_Icc_of_ge (hφ hy hx h)).anti Set.inter_subset_right,
      (Set.subsingleton_Icc_of_ge h).anti Set.inter_subset_right]
/-
**eVariationOn.comp_eq_of_antitoneOn** 是 Mathlib 中的一个定理，位于命名空间 `eVariationOn`。
形式化陈述：comp_eq_of_antitoneOn (f : α -> E) {t : Set β} (φ : β -> α) (hφ : Antitone
On φ t) : eVariationOn (f ∘ φ) t = eVariationOn f (φ '' t)
参数：f : α -> E；φ : β -> α；hφ : AntitoneOn φ t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `eVariationOn.comp_le_of_antitoneOn`：comp_le_of_antitoneOn (f : α -> E) {
s : Set α} {t : Set β} (φ : β -> α) (hφ : AntitoneOn φ t) (φst : MapsTo φ t s) :
 eVariationOn (f ∘ φ) t …
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.eq_empty_of_isEmpty`：eq_empty_of_isEmpty (s : Set α) [IsEmpty s] : s
 = ∅
· 使用定理 `instIsEmptySubtype`：∀ {α : Sort u} [IsEmpty α] (p : α → Prop), IsEmpty (
Subtype p)
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eVariationOn.subsingleton`：∀ {α : Type u_1} [inst : LinearOrder α] {E : 
Type u_2} [inst_1 : PseudoEMetricSpace E] (f : α → E) {s : Set α},   s.Subsingle
ton → eVariatio…
· 使用定理 `Set.SurjOn.rightInvOn_invFunOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set
 α} {t : Set β} {f : α → β} [inst : Nonempty α],   Set.SurjOn f s t → Set.RightI
nvOn (Function.invFu…
· 使用定理 `Set.surjOn_image`：surjOn_image (f : α -> β) (s : Set α) : SurjOn f s (f 
'' s)
· 使用定理 `Set.SurjOn.mapsTo_invFunOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} 
{t : Set β} {f : α → β} [inst : Nonempty α],   Set.SurjOn f s t → Set.MapsTo (Fu
nction.invFunOn …
· 使用定理 `Function.antitoneOn_of_rightInvOn_of_mapsTo`：antitoneOn_of_rightInvOn_of
_mapsTo [PartialOrder α] [LinearOrder β] {φ : β -> α} {ψ : α -> β} {t : Set β} {
s : Set α} (hφ : AntitoneOn φ t) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eVariationOn.eq_of_eqOn`：eq_of_eqOn {f f' : α -> E} {s : Set α} (h : EqO
n f f' s) : eVariationOn f s = eVariationOn f' s
· 使用定理 `Set.EqOn.comp_left`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : 
Set α} {f₁ f₂ : α → β} {g : β → γ},   Set.EqOn f₁ f₂ s → Set.EqOn (g ∘ f₁) (g ∘ 
f₂) s
-/
theorem comp_eq_of_antitoneOn (f : α → E) {t : Set β} (φ : β → α) (hφ : AntitoneOn φ t) :
    eVariationOn (f ∘ φ) t = eVariationOn f (φ '' t) := by
  apply le_antisymm (comp_le_of_antitoneOn f φ hφ (mapsTo_image φ t))
  cases isEmpty_or_nonempty β
  · simp [Set.eq_empty_of_isEmpty]
  let ψ := φ.invFunOn t
  have ψφs : EqOn (φ ∘ ψ) id (φ '' t) := (surjOn_image φ t).rightInvOn_invFunOn
  have ψts := (surjOn_image φ t).mapsTo_invFunOn
  have hψ : AntitoneOn ψ (φ '' t) := Function.antitoneOn_of_rightInvOn_of_mapsTo hφ ψφs ψts
  change eVariationOn (f ∘ id) (φ '' t) ≤ eVariationOn (f ∘ φ) t
  rw [← eq_of_eqOn (ψφs.comp_left : EqOn (f ∘ φ ∘ ψ) (f ∘ id) (φ '' t))]
  exact comp_le_of_antitoneOn _ ψ hψ ψts

open OrderDual
/-
**eVariationOn.comp_ofDual** 是 Mathlib 中的一个定理，位于命名空间 `eVariationOn`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {E : Type u_2} [inst_1 : PseudoEMe
tricSpace E] (f : α → E) (s : Set α),   eVariationOn (f ∘ ⇑OrderDual.ofDual) (⇑O
rderDual.ofDual ⁻¹' s) = eVariationOn f s
参数：f : α → E；s : Set α；f ∘ ⇑OrderDual.ofDual；⇑OrderDual.ofDual ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.image_preimage`：image_preimage {α β} (e : α ≃ β) (s : Set β) : e '
' e ⁻¹' s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eVariationOn.comp_eq_of_antitoneOn`：comp_eq_of_antitoneOn (f : α -> E) {
t : Set β} (φ : β -> α) (hφ : AntitoneOn φ t) : eVariationOn (f ∘ φ) t = eVariat
ionOn f (φ '' t)
-/
@[simp] theorem comp_ofDual (f : α → E) (s : Set α) :
    eVariationOn (f ∘ ofDual) (ofDual ⁻¹' s) = eVariationOn f s := by
  convert! comp_eq_of_antitoneOn f ofDual fun _ _ _ _ => id
  simp only [Equiv.image_preimage]
/-
**eVariationOn._root_.BoundedVariationOn.ofDual** 是 Mathlib 中的一个引理，位于命名空间 `eVari
ationOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma _root_.BoundedVariationOn.ofDual
    {f : α → E} {s : Set α} (hf : BoundedVariationOn f s) :
    BoundedVariationOn (f ∘ ofDual) (ofDual ⁻¹' s) := by
  simpa [BoundedVariationOn] using hf
/-
**eVariationOn.boundedVariation_ofDual** 是 Mathlib 中的一个定理，位于命名空间 `eVariationOn`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {E : Type u_2} [inst_1 : PseudoEMe
tricSpace E] {f : α → E} {s : Set α},   BoundedVariationOn (f ∘ ⇑OrderDual.ofDua
l) (⇑OrderDual.ofDual ⁻¹' s) ↔ BoundedVariationOn f s
参数：f ∘ ⇑OrderDual.ofDual；⇑OrderDual.ofDual ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedVariationOn.ofDual`：∀ {α : Type u_1} [inst : LinearOrder α] {E : 
Type u_2} [inst_1 : PseudoEMetricSpace E] {f : α → E} {s : Set α},   BoundedVari
ationOn f s → B…
-/
@[simp] lemma boundedVariation_ofDual {f : α → E} {s : Set α} :
    BoundedVariationOn (f ∘ ofDual) (ofDual ⁻¹' s) ↔ BoundedVariationOn f s :=
  ⟨fun h ↦ h.ofDual, fun h ↦ h.ofDual⟩
/-
**eVariationOn._root_.LocallyBoundedVariationOn.ofDual** 是 Mathlib 中的一个引理，位于命名空间
 `eVariationOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma _root_.LocallyBoundedVariationOn.ofDual {f : α → E} {s : Set α}
    (hf : LocallyBoundedVariationOn f s) :
    LocallyBoundedVariationOn (f ∘ ofDual) (ofDual ⁻¹' s) := by
  intro x y hx hy
  rw [← toDual_ofDual x, ← toDual_ofDual y, Icc_toDual, ← preimage_inter]
  apply BoundedVariationOn.ofDual (hf (ofDual y) (ofDual x) hy hx)
/-
**eVariationOn.locallyBoundedVariation_ofDual** 是 Mathlib 中的一个定理，位于命名空间 `eVariat
ionOn`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {E : Type u_2} [inst_1 : PseudoEMe
tricSpace E] {f : α → E} {s : Set α},   LocallyBoundedVariationOn (f ∘ ⇑OrderDua
l.ofDual) (⇑OrderDual.ofDual ⁻¹' s) ↔ LocallyBoundedVariationOn f s
参数：f ∘ ⇑OrderDual.ofDual；⇑OrderDual.ofDual ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyBoundedVariationOn.ofDual`：∀ {α : Type u_1} [inst : LinearOrder α
] {E : Type u_2} [inst_1 : PseudoEMetricSpace E] {f : α → E} {s : Set α},   Loca
llyBoundedVariationOn …
-/
@[simp] lemma locallyBoundedVariation_ofDual {f : α → E} {s : Set α} :
    LocallyBoundedVariationOn (f ∘ ofDual) (ofDual ⁻¹' s) ↔ LocallyBoundedVariationOn f s :=
  ⟨fun h ↦ h.ofDual, fun h ↦ h.ofDual⟩

end Monotone

/-! ### Left and right limits of bounded variation functions -/

/-- The variation of a function on `Iic a` is the sum of the variation on `Iio a` and the
contribution of `a`, i.e., the distance between the left limit and the value at `a`.
We give a version relative to a set `s`. -/
/-
**eVariationOn.eVariationOn_on_inter_Iic_eq_Iio_add_edist** 是 Mathlib 中的一个定理，位于命
名空间 `eVariationOn`。
形式化陈述：eVariationOn_on_inter_Iic_eq_Iio_add_edist [TopologicalSpace α] [OrderTopo
logy α] {f : α -> E} {s : Set α} {a : α} {l : E} (h : (𝓝[s inter Iio a] a).NeBot
) (ha : a in s) (h'f : Tendsto f (𝓝[s inter Iio a] a) (𝓝 l)) : eVariationOn f (s
 inter Iic a) = eVariationOn f (s inter Iio a) + edist (f a) l
参数：h : (𝓝[s inter Iio a] a).NeBot；ha : a in s；h'f : Tendsto f (𝓝[s inter Iio a] 
a) (𝓝 l)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eVariationOn.eVariationOn_eq_strictMonoOn`：eVariationOn_eq_strictMonoOn 
(f : α -> E) (s : Set α) : eVariationOn f s = ⨆ p : (n : Nat) × { u : Nat -> α /
/ StrictMonoOn u (Iic n) ∧ fora…
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.Tendsto.const_add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [
inst_1 : Add M] [SeparatelyContinuousAdd M] {α : Type u_2} {f : α → M}   {x : Fi
lter α} {a : M…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `Filter.Tendsto.edist`：Filter.Tendsto.edist {f g : β -> α} {x : Filter β}
 {a b : α} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (fun x =>
 edist (f …
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `ge_of_tendsto`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] [
inst_1 : Preorder α] [ClosedIciTopology α] {f : β → α}   {a b : α} {x : Filter β
} […
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用引理 `inter_mem_nhdsWithin_inter`：inter_mem_nhdsWithin_inter {a b c d : Set α}
 {x : α} (h : a in 𝓝[b] x) (h' : c in 𝓝[d] x) : a inter c in 𝓝[b inter d] x
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Ioo_mem_nhdsLT`：Ioo_mem_nhdsLT (H : a < b) : Ioo a b in 𝓝[<] b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
（共 50 条，此处仅展示前 30 条）

--- 原说明 ---
The variation of a function on `Iic a` is the sum of the variation on `Iio a` an
d the
contribution of `a`, i.e., the distance between the left limit and the value at 
`a`.
We give a version relative to a set `s`.
-/
theorem eVariationOn_on_inter_Iic_eq_Iio_add_edist
    [TopologicalSpace α] [OrderTopology α] {f : α → E} {s : Set α} {a : α} {l : E}
    (h : (𝓝[s ∩ Iio a] a).NeBot) (ha : a ∈ s)
    (h'f : Tendsto f (𝓝[s ∩ Iio a] a) (𝓝 l)) :
    eVariationOn f (s ∩ Iic a) = eVariationOn f (s ∩ Iio a) + edist (f a) l := by
  refine le_antisymm ?_ ?_
  · rw [eVariationOn_eq_strictMonoOn]
    apply iSup_le
    rintro ⟨n, u, u_mono, u_mem⟩
    have : u n ≤ a := (u_mem n (by simp)).2
    rcases this.eq_or_lt with hn | hn; swap
    · exact (sum_le_of_monotoneOn_Iic u_mono.monotoneOn (by grind [StrictMonoOn])).trans le_self_add
    cases n with
    | zero => simp
    | succ n =>
      have : Tendsto (fun y ↦ eVariationOn f (s ∩ Iio a) + edist (f a) (f y)) (𝓝[s ∩ Iio a] a)
          (𝓝 (eVariationOn f (s ∩ Iio a) + edist (f a) l)) :=
        (Tendsto.edist tendsto_const_nhds h'f).const_add _
      apply ge_of_tendsto this
      have : s ∩ Ioo (u n) a ∈ 𝓝[s ∩ Iio a] a :=
        inter_mem_nhdsWithin_inter self_mem_nhdsWithin (Ioo_mem_nhdsLT (by grind [StrictMonoOn]))
      filter_upwards [this] with y hy
      let v i := if i ≤ n then u i else if i = n + 1 then y else a
      have A : ∑ i ∈ Finset.range (n + 1), edist (f (u (i + 1))) (f (u i))
          ≤ ∑ i ∈ Finset.range (n + 2), edist (f (v (i + 1))) (f (v i)) := by
        simp only [Finset.sum_range_succ, add_assoc]
        gcongr with i h
        · grind
        · grw [add_comm (edist _ _), ← edist_triangle]
          grind
      have B : ∑ i ∈ Finset.range (n + 2), edist (f (v (i + 1))) (f (v i)) ≤
            eVariationOn f (s ∩ Iio a) + edist (f a) (f y) := by
        rw [Finset.sum_range_succ]
        gcongr
        · apply sum_le_of_monotoneOn_Iic <;> grind [MonotoneOn, StrictMonoOn]
        · grind
      exact A.trans B
  · obtain ⟨b, hb⟩ : (s ∩ Iio a).Nonempty := by contrapose! h; simp [h]
    have : Nonempty ((n : ℕ) × { u // StrictMonoOn u (Iic n) ∧ ∀ i ∈ Iic n, u i ∈ s ∩ Iio a }) :=
      ⟨0, ⟨fun i ↦ b, by grind [StrictMonoOn]⟩⟩
    rw [eVariationOn_eq_strictMonoOn, ENNReal.iSup_add]
    apply iSup_le
    rintro ⟨n, u, u_mono, u_mem⟩
    have : Tendsto (fun y ↦ ∑ i ∈ Finset.range n,
        edist (f (u (i + 1))) (f (u i)) + edist (f a) (f y)) (𝓝[s ∩ Iio a] a)
        (𝓝 (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) + edist (f a) l)) :=
      (Tendsto.edist tendsto_const_nhds h'f).const_add _
    apply le_of_tendsto this
    have : s ∩ Ioo (u n) a ∈ 𝓝[s ∩ Iio a] a :=
      inter_mem_nhdsWithin_inter self_mem_nhdsWithin (Ioo_mem_nhdsLT (by grind [StrictMonoOn]))
    filter_upwards [this, self_mem_nhdsWithin] with y hy h'y
    let v i := if i ≤ n then u i else if i = n + 1 then y else a
    have A : ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) + edist (f a) (f y)
        ≤ ∑ i ∈ Finset.range (n + 2), edist (f (v (i + 1))) (f (v i)) := by
      simp only [Finset.sum_range_succ, add_assoc]
      gcongr with i h
      · grind
      · exact le_add_left (by grind)
    have B : ∑ i ∈ Finset.range (n + 2), edist (f (v (i + 1))) (f (v i)) ≤
        eVariationOn f (s ∩ Iic a) :=
      sum_le_of_monotoneOn_Iic (by grind [MonotoneOn, StrictMonoOn]) (by grind)
    exact A.trans B

/-- The variation of a function on `Ici a` is the sum of the variation on `Ioi a` and the
contribution of `a`, i.e., the distance between the right limit and the value at `a`.
We give a version relative to a set `s`. -/
/-
**eVariationOn.eVariationOn_on_inter_Ici_eq_Ioi_add_edist** 是 Mathlib 中的一个定理，位于命
名空间 `eVariationOn`。
形式化陈述：eVariationOn_on_inter_Ici_eq_Ioi_add_edist [TopologicalSpace α] [OrderTopo
logy α] {f : α -> E} {s : Set α} {a : α} {l : E} (h : (𝓝[s inter Ioi a] a).NeBot
) (ha : a in s) (h'f : Tendsto f (𝓝[s inter Ioi a] a) (𝓝 l)) : eVariationOn f (s
 inter Ici a) = eVariationOn f (s inter Ioi a) + edist (f a) l
参数：h : (𝓝[s inter Ioi a] a).NeBot；ha : a in s；h'f : Tendsto f (𝓝[s inter Ioi a] 
a) (𝓝 l)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eVariationOn.comp_ofDual`：∀ {α : Type u_1} [inst : LinearOrder α] {E : T
ype u_2} [inst_1 : PseudoEMetricSpace E] (f : α → E) (s : Set α),   eVariationOn
 (f ∘ ⇑OrderDu…
· 使用定理 `eVariationOn.eVariationOn_on_inter_Iic_eq_Iio_add_edist`：eVariationOn_on
_inter_Iic_eq_Iio_add_edist [TopologicalSpace α] [OrderTopology α] {f : α -> E} 
{s : Set α} {a : α} {l : E} (h : (𝓝[s inter I…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ

--- 原说明 ---
The variation of a function on `Ici a` is the sum of the variation on `Ioi a` an
d the
contribution of `a`, i.e., the distance between the right limit and the value at
 `a`.
We give a version relative to a set `s`.
-/
theorem eVariationOn_on_inter_Ici_eq_Ioi_add_edist
    [TopologicalSpace α] [OrderTopology α] {f : α → E} {s : Set α} {a : α} {l : E}
    (h : (𝓝[s ∩ Ioi a] a).NeBot) (ha : a ∈ s)
    (h'f : Tendsto f (𝓝[s ∩ Ioi a] a) (𝓝 l)) :
    eVariationOn f (s ∩ Ici a) = eVariationOn f (s ∩ Ioi a) + edist (f a) l := by
  rw [← comp_ofDual f, ← comp_ofDual f]
  exact eVariationOn_on_inter_Iic_eq_Iio_add_edist h ha h'f

/-- If a function is continuous on the left at a point `a`, then its variations on `Iio a` and
on `Iic a` coincide. We give a version relative to a set `s`. -/
/-
**eVariationOn.eVariationOn_inter_Iio_eq_inter_Iic_of_continuousWithinAt** 是 Mat
hlib 中的一个引理，位于命名空间 `eVariationOn`。
形式化陈述：eVariationOn_inter_Iio_eq_inter_Iic_of_continuousWithinAt [TopologicalSpac
e α] [OrderTopology α] {f : α -> E} {s : Set α} {a : α} (h : (𝓝[s inter Iio a] a
).NeBot) (h' : ContinuousWithinAt f (s inter Iic a) a) : eVariationOn f (s inter
 Iio a) = eVariationOn f (s inter Iic a)
参数：h : (𝓝[s inter Iio a] a).NeBot；h' : ContinuousWithinAt f (s inter Iic a) a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.mono`：ContinuousWithinAt.mono (h : ContinuousWithinAt
 f t x) (hs : s subseteq t) : ContinuousWithinAt f s x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eVariationOn.eVariationOn_on_inter_Iic_eq_Iio_add_edist`：eVariationOn_on
_inter_Iic_eq_Iio_add_edist [TopologicalSpace α] [OrderTopology α] {f : α -> E} 
{s : Set α} {a : α} {l : E} (h : (𝓝[s inter I…
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If a function is continuous on the left at a point `a`, then its variations on `
Iio a` and
on `Iic a` coincide. We give a version relative to a set `s`.
-/
lemma eVariationOn_inter_Iio_eq_inter_Iic_of_continuousWithinAt
    [TopologicalSpace α] [OrderTopology α] {f : α → E} {s : Set α} {a : α}
    (h : (𝓝[s ∩ Iio a] a).NeBot) (h' : ContinuousWithinAt f (s ∩ Iic a) a) :
    eVariationOn f (s ∩ Iio a) = eVariationOn f (s ∩ Iic a) := by
  by_cases ha : a ∈ s
  · have : Tendsto f (𝓝[s ∩ Iio a] a) (𝓝 (f a)) := h'.mono (by grind)
    simp [eVariationOn_on_inter_Iic_eq_Iio_add_edist h ha this]
  · congr 1
    grind

/-- If a function is continuous on the right at a point `a`, then its variations on `Ioi a` and
on `Ici a` coincide. We give a version relative to a set `s`. -/
/-
**eVariationOn.eVariationOn_inter_Ioi_eq_inter_Ici_of_continuousWithinAt** 是 Mat
hlib 中的一个引理，位于命名空间 `eVariationOn`。
形式化陈述：eVariationOn_inter_Ioi_eq_inter_Ici_of_continuousWithinAt [TopologicalSpac
e α] [OrderTopology α] {f : α -> E} {s : Set α} {a : α} (h : (𝓝[s inter Ioi a] a
).NeBot) (h' : ContinuousWithinAt f (s inter Ici a) a) : eVariationOn f (s inter
 Ioi a) = eVariationOn f (s inter Ici a)
参数：h : (𝓝[s inter Ioi a] a).NeBot；h' : ContinuousWithinAt f (s inter Ici a) a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eVariationOn.comp_ofDual`：∀ {α : Type u_1} [inst : LinearOrder α] {E : T
ype u_2} [inst_1 : PseudoEMetricSpace E] (f : α → E) (s : Set α),   eVariationOn
 (f ∘ ⇑OrderDu…
· 使用引理 `eVariationOn.eVariationOn_inter_Iio_eq_inter_Iic_of_continuousWithinAt`：
eVariationOn_inter_Iio_eq_inter_Iic_of_continuousWithinAt [TopologicalSpace α] [
OrderTopology α] {f : α -> E} {s : Set α} {a : α} (h : (𝓝[s …
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ

--- 原说明 ---
If a function is continuous on the right at a point `a`, then its variations on 
`Ioi a` and
on `Ici a` coincide. We give a version relative to a set `s`.
-/
lemma eVariationOn_inter_Ioi_eq_inter_Ici_of_continuousWithinAt
    [TopologicalSpace α] [OrderTopology α] {f : α → E} {s : Set α} {a : α}
    (h : (𝓝[s ∩ Ioi a] a).NeBot) (h' : ContinuousWithinAt f (s ∩ Ici a) a) :
    eVariationOn f (s ∩ Ioi a) = eVariationOn f (s ∩ Ici a) := by
  rw [← comp_ofDual f, ← comp_ofDual f]
  exact eVariationOn_inter_Iio_eq_inter_Iic_of_continuousWithinAt h h'
/-
**eVariationOn.eVariationOn_Ioc_eq_Icc_of_continuousWithinAt'** 是 Mathlib 中的一个引理
，位于命名空间 `eVariationOn`。
形式化陈述：eVariationOn_Ioc_eq_Icc_of_continuousWithinAt' [TopologicalSpace α] [Order
Topology α] {f : α -> E} {a b : α} [h : (𝓝[>] a).NeBot] (h' : ContinuousWithinAt
 f (Ici a) a) : eVariationOn f (Ioc a b) = eVariationOn f (Icc a b)
参数：𝓝[>] a；h' : ContinuousWithinAt f (Ici a) a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Ioc_eq_empty`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, ¬b < a
 → Set.Ioc b a = ∅
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eVariationOn.subsingleton`：∀ {α : Type u_1} [inst : LinearOrder α] {E : 
Type u_2} [inst_1 : PseudoEMetricSpace E] (f : α → E) {s : Set α},   s.Subsingle
ton → eVariatio…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_inter_of_mem`：nhdsWithin_inter_of_mem {a : α} {s t : Set α} (
h : s in 𝓝[t] a) : 𝓝[s inter t] a = 𝓝[t] a
· 使用定理 `mem_nhdsWithin_of_mem_nhds`：mem_nhdsWithin_of_mem_nhds {s t : Set α} {a 
: α} (h : s in 𝓝 a) : s in 𝓝[t] a
· 使用定理 `Iic_mem_nhds`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Linea
rOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Iic a ∈ nhds b
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用引理 `eVariationOn.eVariationOn_inter_Ioi_eq_inter_Ici_of_continuousWithinAt`：
eVariationOn_inter_Ioi_eq_inter_Ici_of_continuousWithinAt [TopologicalSpace α] [
OrderTopology α] {f : α -> E} {s : Set α} {a : α} (h : (𝓝[s …
· 使用定理 `ContinuousWithinAt.mono`：ContinuousWithinAt.mono (h : ContinuousWithinAt
 f t x) (hs : s subseteq t) : ContinuousWithinAt f s x
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
lemma eVariationOn_Ioc_eq_Icc_of_continuousWithinAt'
    [TopologicalSpace α] [OrderTopology α] {f : α → E} {a b : α}
    [h : (𝓝[>] a).NeBot] (h' : ContinuousWithinAt f (Ici a) a) :
    eVariationOn f (Ioc a b) = eVariationOn f (Icc a b) := by
  rcases le_or_gt b a with hab | hab
  · simp [hab]
  have : (𝓝[Iic b ∩ Ioi a] a).NeBot := by
    convert h using 1
    exact nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hab))
  convert eVariationOn_inter_Ioi_eq_inter_Ici_of_continuousWithinAt this
    (h'.mono inter_subset_right) <;> grind
/-
**eVariationOn.eVariationOn_Ioc_eq_Icc_of_continuousWithinAt** 是 Mathlib 中的一个引理，
位于命名空间 `eVariationOn`。
形式化陈述：eVariationOn_Ioc_eq_Icc_of_continuousWithinAt [TopologicalSpace α] [OrderT
opology α] [DenselyOrdered α] {f : α -> E} {a b : α} (h' : ContinuousWithinAt f 
(Ici a) a) : eVariationOn f (Ioc a b) = eVariationOn f (Icc a b)
参数：h' : ContinuousWithinAt f (Ici a) a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Ioc_eq_empty`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, ¬b < a
 → Set.Ioc b a = ∅
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eVariationOn.subsingleton`：∀ {α : Type u_1} [inst : LinearOrder α] {E : 
Type u_2} [inst_1 : PseudoEMetricSpace E] (f : α → E) {s : Set α},   s.Subsingle
ton → eVariatio…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `nhdsGT_neBot_of_exists_gt`：nhdsGT_neBot_of_exists_gt {a : α} (H : exists
 b, a < b) : NeBot (𝓝[>] a)
· 使用引理 `eVariationOn.eVariationOn_Ioc_eq_Icc_of_continuousWithinAt'`：eVariationO
n_Ioc_eq_Icc_of_continuousWithinAt' [TopologicalSpace α] [OrderTopology α] {f : 
α -> E} {a b : α} [h : (𝓝[>] a).NeBot] (h' : Cont…
-/
lemma eVariationOn_Ioc_eq_Icc_of_continuousWithinAt
    [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α] {f : α → E} {a b : α}
    (h' : ContinuousWithinAt f (Ici a) a) :
    eVariationOn f (Ioc a b) = eVariationOn f (Icc a b) := by
  rcases le_or_gt b a with hab | hab
  · simp [hab]
  have : (𝓝[Ioi a] a).NeBot := nhdsGT_neBot_of_exists_gt ⟨b, hab⟩
  exact eVariationOn_Ioc_eq_Icc_of_continuousWithinAt' h'
/-
**eVariationOn.eVariationOn_Ico_eq_Icc_of_continuousWithinAt'** 是 Mathlib 中的一个引理
，位于命名空间 `eVariationOn`。
形式化陈述：eVariationOn_Ico_eq_Icc_of_continuousWithinAt' [TopologicalSpace α] [Order
Topology α] {f : α -> E} {a b : α} [h : (𝓝[<] a).NeBot] (h' : ContinuousWithinAt
 f (Iic a) a) : eVariationOn f (Ico b a) = eVariationOn f (Icc b a)
参数：𝓝[<] a；h' : ContinuousWithinAt f (Iic a) a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eVariationOn.comp_ofDual`：∀ {α : Type u_1} [inst : LinearOrder α] {E : T
ype u_2} [inst_1 : PseudoEMetricSpace E] (f : α → E) (s : Set α),   eVariationOn
 (f ∘ ⇑OrderDu…
· 使用定理 `Set.Ioc_toDual`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},   Set.Io
c (OrderDual.toDual b) (OrderDual.toDual a) = ⇑OrderDual.ofDual ⁻¹' Set.Ico a b
· 使用定理 `Set.Icc_toDual`：Icc_toDual : Icc (toDual a) (toDual b) = ofDual ⁻¹' Icc 
b a
· 使用引理 `eVariationOn.eVariationOn_Ioc_eq_Icc_of_continuousWithinAt'`：eVariationO
n_Ioc_eq_Icc_of_continuousWithinAt' [TopologicalSpace α] [OrderTopology α] {f : 
α -> E} {a b : α} [h : (𝓝[>] a).NeBot] (h' : Cont…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
-/
lemma eVariationOn_Ico_eq_Icc_of_continuousWithinAt'
    [TopologicalSpace α] [OrderTopology α] {f : α → E} {a b : α}
    [h : (𝓝[<] a).NeBot] (h' : ContinuousWithinAt f (Iic a) a) :
    eVariationOn f (Ico b a) = eVariationOn f (Icc b a) := by
  rw [← comp_ofDual f, ← comp_ofDual f, ← Ioc_toDual, ← Icc_toDual]
  exact eVariationOn_Ioc_eq_Icc_of_continuousWithinAt' h'
/-
**eVariationOn.eVariationOn_Ico_eq_Icc_of_continuousWithinAt** 是 Mathlib 中的一个引理，
位于命名空间 `eVariationOn`。
形式化陈述：eVariationOn_Ico_eq_Icc_of_continuousWithinAt [TopologicalSpace α] [OrderT
opology α] [DenselyOrdered α] {f : α -> E} {a b : α} (h' : ContinuousWithinAt f 
(Iic a) a) : eVariationOn f (Ico b a) = eVariationOn f (Icc b a)
参数：h' : ContinuousWithinAt f (Iic a) a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eVariationOn.comp_ofDual`：∀ {α : Type u_1} [inst : LinearOrder α] {E : T
ype u_2} [inst_1 : PseudoEMetricSpace E] (f : α → E) (s : Set α),   eVariationOn
 (f ∘ ⇑OrderDu…
· 使用定理 `Set.Ioc_toDual`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},   Set.Io
c (OrderDual.toDual b) (OrderDual.toDual a) = ⇑OrderDual.ofDual ⁻¹' Set.Ico a b
· 使用定理 `Set.Icc_toDual`：Icc_toDual : Icc (toDual a) (toDual b) = ofDual ⁻¹' Icc 
b a
· 使用引理 `eVariationOn.eVariationOn_Ioc_eq_Icc_of_continuousWithinAt`：eVariationOn
_Ioc_eq_Icc_of_continuousWithinAt [TopologicalSpace α] [OrderTopology α] [Densel
yOrdered α] {f : α -> E} {a b : α} (h' : Continu…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
-/
lemma eVariationOn_Ico_eq_Icc_of_continuousWithinAt
    [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α] {f : α → E} {a b : α}
    (h' : ContinuousWithinAt f (Iic a) a) :
    eVariationOn f (Ico b a) = eVariationOn f (Icc b a) := by
  rw [← comp_ofDual f, ← comp_ofDual f, ← Ioc_toDual, ← Icc_toDual]
  exact eVariationOn_Ioc_eq_Icc_of_continuousWithinAt h'
/-
**eVariationOn.exists_lt_eVariationOn_inter_Icc** 是 Mathlib 中的一个引理，位于命名空间 `eVari
ationOn`。
形式化陈述：exists_lt_eVariationOn_inter_Icc {f : α -> E} {ε : Real>=0∞} {s : Set α} (
h : ε < eVariationOn f s) : exists a in s, exists b in s, a < b ∧ ε < eVariation
On f (s inter Icc a b)
参数：h : ε < eVariationOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `eVariationOn.sum_le_of_monotoneOn_Iic`：sum_le_of_monotoneOn_Iic {f : α -
> E} {s : Set α} {n : Nat} {u : Nat -> α} (hu : MonotoneOn u (Iic n)) (us : fora
ll i <= n, u i in s) : (∑ i…
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `eVariationOn.subsingleton`：∀ {α : Type u_1} [inst : LinearOrder α] {E : 
Type u_2} [inst_1 : PseudoEMetricSpace E] (f : α → E) {s : Set α},   s.Subsingle
ton → eVariatio…
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
lemma exists_lt_eVariationOn_inter_Icc {f : α → E} {ε : ℝ≥0∞} {s : Set α}
    (h : ε < eVariationOn f s) : ∃ a ∈ s, ∃ b ∈ s, a < b ∧ ε < eVariationOn f (s ∩ Icc a b) := by
  obtain ⟨n, u, ⟨u_mono, u_mem⟩, hu⟩ : ∃ n u, (Monotone u ∧ ∀ (i : ℕ), u i ∈ s) ∧
      ε < ∑ x ∈ Finset.range n, edist (f (u (x + 1))) (f (u x)) := by
    simpa [eVariationOn, lt_iSup_iff] using h
  have A : ε < eVariationOn f (s ∩ Icc (u 0) (u n)) := by
    apply hu.trans_le
    simp only [Monotone] at u_mono
    let v (i : ℕ) := min (u i) (u n)
    calc ∑ x ∈ Finset.range n, edist (f (u (x + 1))) (f (u x))
    _ = ∑ i ∈ Finset.range n, edist (f (v (i + 1))) (f (v i)) := by grind [Finset.sum_congr]
    _ ≤ eVariationOn f (s ∩ Icc (u 0) (u n)) :=
      sum_le_of_monotoneOn_Iic (by grind [MonotoneOn]) (by grind)
  refine ⟨u 0, u_mem _, u n, u_mem _, ?_, A⟩
  by_contra!
  have : Set.Subsingleton (s ∩ Icc (u 0) (u n)) := by
    intro a ha b hb
    simp only [mem_inter_iff, mem_Icc] at ha hb
    order
  simp [this] at A

/-- If a function has bounded variation, then the variation on closed semi-infinite intervals
tends to `0`. We give a version with a generic filter, that applies both to left-neighborhoods of
points and to `atTop`. -/
/-
**eVariationOn._root_.BoundedVariationOn.tendsto_eVariationOn_Ici_zero_of_filter
** 是 Mathlib 中的一个定理，位于命名空间 `eVariationOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a function has bounded variation, then the variation on closed semi-infinite 
intervals
tends to `0`. We give a version with a generic filter, that applies both to left
-neighborhoods of
points and to `atTop`.
-/
theorem _root_.BoundedVariationOn.tendsto_eVariationOn_Ici_zero_of_filter
    {f : α → E} {s : Set α} (hf : BoundedVariationOn f s)
    (L : Filter α) (hL : ∀ y ∈ s, s ∩ Ici y ∈ L) :
    Tendsto (fun y ↦ eVariationOn f (s ∩ Ici y)) L (𝓝 0) := by
  rcases eq_empty_or_nonempty s with rfl | ⟨x₀, hx₀⟩
  · simpa using tendsto_const_nhds
  /- The variation is monotone, therefore it converges. If the limit were positive, say `ε`,
  then one would get variation `ε` between two points `x₀` and `x₁`. But also between two points
  `x₁` and `x₂`, and so on. Adding up these variations would be arbitrarily large, contradicting
  the finite variation of the function. -/
  apply tendsto_order.2 ⟨by simp, fun ε εpos ↦ ?_⟩
  obtain ⟨δ, δpos, hδ⟩ : ∃ δ, δ ∈ Ioo 0 ε := exists_between εpos
  by_contra! H
  have B (y) (hy : y ∈ s) : ∃ y' ∈ s ∩ Ici y, δ ≤ eVariationOn f (s ∩ Icc y y') := by
    obtain ⟨y', hy', y'_mem⟩ : ∃ y', ε ≤ eVariationOn f (s ∩ Ici y') ∧ y' ∈ s ∩ Ici y :=
      (H.and_eventually (hL y hy)).exists
    obtain ⟨a, ha, b, hb, hab, h⟩ : ∃ a ∈ s ∩ Ici y', ∃ b ∈ s ∩ Ici y', a < b ∧
      δ < eVariationOn f ((s ∩ Ici y') ∩ Icc a b) :=
        exists_lt_eVariationOn_inter_Icc (hδ.trans_le hy')
    refine ⟨b, ⟨hb.1, le_trans y'_mem.2 hb.2⟩, ?_⟩
    have : Ici y' ∩ Icc a b = Icc a b := by grind
    rw [inter_assoc, this] at h
    exact h.le.trans (mono _ (by grind))
  choose! y y_mem le_y using B
  let v (n : ℕ) := y^[n] x₀
  have I n : v n ∈ s := by
    induction n with
    | zero => simpa [v] using hx₀
    | succ n ih =>
      simp only [Function.iterate_succ', Function.comp_apply, v]
      exact (y_mem _ ih).1
  have J (n : ℕ) : n * δ ≤ eVariationOn f s := calc
    n * δ
    _ = ∑ i ∈ Finset.range n, δ := by simp
    _ ≤ ∑ i ∈ Finset.range n, eVariationOn f (s ∩ Icc (v i) (v (i + 1))) := by
      gcongr with i hi
      simp only [Function.iterate_succ', Function.comp_apply, v]
      grind
    _ = eVariationOn f (s ∩ Icc (v 0) (v n)) := by
      apply eVariationOn.sum
      · apply monotone_nat_of_le_succ (fun n ↦ ?_)
        simp only [Function.iterate_succ', Function.comp_apply, v]
        exact (y_mem _ (I n)).2
      · grind
    _ ≤ eVariationOn f s := mono _ inter_subset_left
  have : Tendsto (fun (n : ℕ) ↦ n * δ) atTop (𝓝 (∞ * δ)) :=
    ENNReal.Tendsto.mul_const ENNReal.tendsto_nat_nhds_top (by simp)
  rw [ENNReal.top_mul δpos.ne'] at this
  have : ∞ ≤ eVariationOn f s := le_of_tendsto this (Eventually.of_forall J)
  simp only [BoundedVariationOn] at hf
  order

/-- A bounded variation function has a limit on its left within a set. Version with a general
filter, covering both left neighborhoods of points and `atTop`. -/
/-
**eVariationOn._root_.BoundedVariationOn.exists_tendsto_left_of_filter** 是 Mathl
ib 中的一个定理，位于命名空间 `eVariationOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bounded variation function has a limit on its left within a set. Version with 
a general
filter, covering both left neighborhoods of points and `atTop`.
-/
theorem _root_.BoundedVariationOn.exists_tendsto_left_of_filter [CompleteSpace E]
    {f : α → E} {s : Set α} (hf : BoundedVariationOn f s)
    (L : Filter α) (hL : ∀ y ∈ s, s ∩ Ici y ∈ L) (hs : s.Nonempty) :
    ∃ l, Tendsto f L (𝓝 l) := by
  rcases hs with ⟨x₀, hx₀⟩
  rcases Filter.eq_or_neBot L with h | h
  · simp only [h, tendsto_bot, exists_const_iff, and_true]
    exact ⟨f x₀⟩
  apply CompleteSpace.complete
  apply EMetric.cauchy_iff.2 ⟨by simp [neBot_iff.mp h], fun ε εpos ↦ ?_⟩
  obtain ⟨y, y_mem, hy⟩ : ∃ y ∈ s, eVariationOn f (s ∩ Ici y) < ε := by
    have W := hf.tendsto_eVariationOn_Ici_zero_of_filter L hL
    rcases (((tendsto_order.1 W).2 ε εpos).and (hL x₀ hx₀)).exists with ⟨y, hy, h'y⟩
    exact ⟨y, h'y.1, hy⟩
  refine ⟨f '' (s ∩ Ici y), ?_, ?_⟩
  · simp only [mem_map]
    apply mem_of_superset (hL y y_mem) (subset_preimage_image _ _)
  · rintro - ⟨a, ha, rfl⟩ - ⟨b, hb, rfl⟩
    exact (eVariationOn.edist_le _ ha hb).trans_lt hy

/-- If a function has bounded variation, then the variation on small closed-open
intervals to the left of any point tends to `0`. -/
/-
**eVariationOn._root_.BoundedVariationOn.tendsto_eVariationOn_Ico_zero** 是 Mathl
ib 中的一个定理，位于命名空间 `eVariationOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a function has bounded variation, then the variation on small closed-open
intervals to the left of any point tends to `0`.
-/
theorem _root_.BoundedVariationOn.tendsto_eVariationOn_Ico_zero
    [TopologicalSpace α] [OrderTopology α]
    {f : α → E} {s : Set α} (hf : BoundedVariationOn f s) (x : α) :
    Tendsto (fun y ↦ eVariationOn f (s ∩ Ico y x)) (𝓝[s] x) (𝓝 0) := by
  have A : Tendsto (fun y ↦ eVariationOn f (s ∩ Ico y x)) (𝓝[s ∩ Iio x] x) (𝓝 0) := by
    simp_rw [← Iio_inter_Ici, ← inter_assoc]
    exact (hf.mono inter_subset_left).tendsto_eVariationOn_Ici_zero_of_filter (𝓝[s ∩ Iio x] x)
      (fun y hy ↦ inter_mem_nhdsWithin _ (Ici_mem_nhds hy.2))
  have B : Tendsto (fun y ↦ eVariationOn f (s ∩ Ico y x)) (𝓝[s ∩ Ici x] x) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with a ha using by simp [show Ico a x = ∅ by grind]
  nth_rewrite 2 [show s = (s ∩ Iio x) ∪ (s ∩ Ici x) by grind]
  rw [nhdsWithin_union, tendsto_sup]
  simp [A, B]

/-- If a function has bounded variation, then the variation on small open-closed
intervals to the right of any point tends to `0`. -/
/-
**eVariationOn._root_.BoundedVariationOn.tendsto_eVariationOn_Ioc_zero** 是 Mathl
ib 中的一个定理，位于命名空间 `eVariationOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a function has bounded variation, then the variation on small open-closed
intervals to the right of any point tends to `0`.
-/
theorem _root_.BoundedVariationOn.tendsto_eVariationOn_Ioc_zero [TopologicalSpace α]
    [OrderTopology α] {f : α → E} {s : Set α} (hf : BoundedVariationOn f s) (x : α) :
    Tendsto (fun y ↦ eVariationOn f (s ∩ Ioc x y)) (𝓝[s] x) (𝓝 0) := by
  have : (fun y ↦ eVariationOn f (s ∩ Ioc x y)) =
      (fun y ↦ eVariationOn (f ∘ ofDual) (ofDual ⁻¹' s ∩ Ico (toDual y) (toDual x))) := by
    ext y
    rw [Ico_toDual, ← preimage_inter, comp_ofDual]
  rw [this]
  exact hf.ofDual.tendsto_eVariationOn_Ico_zero (toDual x)

/-- A bounded variation function has a limit on its left within a set. -/
/-
**eVariationOn._root_.BoundedVariationOn.exists_tendsto_left** 是 Mathlib 中的一个定理，
位于命名空间 `eVariationOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bounded variation function has a limit on its left within a set.
-/
theorem _root_.BoundedVariationOn.exists_tendsto_left [CompleteSpace E] [TopologicalSpace α]
    [OrderTopology α] {f : α → E} {s : Set α} (hf : BoundedVariationOn f s) (x : α) :
    ∃ l, Tendsto f (𝓝[s ∩ Iio x] x) (𝓝 l) := by
  rcases eq_empty_or_nonempty (s ∩ Iio x) with hs | hs
  · simp only [hs, nhdsWithin_empty, tendsto_bot, exists_const_iff, and_true]
    exact ⟨f x⟩
  exact BoundedVariationOn.exists_tendsto_left_of_filter (s := s ∩ Iio x)
    (hf.mono inter_subset_left) _ (fun y hy ↦ inter_mem_nhdsWithin _ (Ici_mem_nhds hy.2)) hs

/-- A bounded variation function has a limit on its right within a set. -/
/-
**eVariationOn._root_.BoundedVariationOn.exists_tendsto_right** 是 Mathlib 中的一个定理
，位于命名空间 `eVariationOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bounded variation function has a limit on its right within a set.
-/
theorem _root_.BoundedVariationOn.exists_tendsto_right [CompleteSpace E] [TopologicalSpace α]
    [OrderTopology α] {f : α → E} {s : Set α} (hf : BoundedVariationOn f s) (x : α) :
    ∃ l, Tendsto f (𝓝[s ∩ Ioi x] x) (𝓝 l) :=
  hf.ofDual.exists_tendsto_left (toDual x)

/-- A bounded variation function tends to its left-limit on its left. -/
/-
**eVariationOn._root_.BoundedVariationOn.tendsto_leftLim** 是 Mathlib 中的一个定理，位于命名
空间 `eVariationOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bounded variation function tends to its left-limit on its left.
-/
theorem _root_.BoundedVariationOn.tendsto_leftLim [CompleteSpace E] [TopologicalSpace α]
    [OrderTopology α] {f : α → E} (hf : BoundedVariationOn f univ) (x : α) :
    Tendsto f (𝓝[<] x) (𝓝 (f.leftLim x)) := by
  apply tendsto_leftLim_of_tendsto
  convert! hf.exists_tendsto_left x
  simp

/-- A bounded variation function tends to its right-limit on its right. -/
/-
**eVariationOn._root_.BoundedVariationOn.tendsto_rightLim** 是 Mathlib 中的一个定理，位于命
名空间 `eVariationOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bounded variation function tends to its right-limit on its right.
-/
theorem _root_.BoundedVariationOn.tendsto_rightLim [CompleteSpace E] [TopologicalSpace α]
    [OrderTopology α] {f : α → E} (hf : BoundedVariationOn f univ) (x : α) :
    Tendsto f (𝓝[>] x) (𝓝 (f.rightLim x)) :=
  hf.ofDual.tendsto_leftLim x
/-
**eVariationOn._root_.BoundedVariationOn.eVariationOn_Iic_eq_Iio_add_edist** 是 M
athlib 中的一个定理，位于命名空间 `eVariationOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.BoundedVariationOn.eVariationOn_Iic_eq_Iio_add_edist [CompleteSpace E]
    [DenselyOrdered α] {f : α → E} {a : α} (hf : BoundedVariationOn f univ) :
    eVariationOn f (Iic a) = eVariationOn f (Iio a) + edist (f a) (f.leftLim a) := by
  let : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  by_cases ha : IsBot a
  · have A : Iic a = {a} := by ext x; grind [ha x]
    have B : Iio a = ∅ := by simp [ha.isMin]
    simp [A, B, leftLim_eq_of_isBot ha]
  have : (𝓝[<] a).NeBot := nhdsLT_neBot_of_exists_lt (by simpa [IsBot] using ha)
  have : eVariationOn f (univ ∩ Iic a) = eVariationOn f (univ ∩ Iio a)
      + edist (f a) (f.leftLim a) := by
    apply eVariationOn_on_inter_Iic_eq_Iio_add_edist (by simpa) (mem_univ _)
    simpa only [univ_inter] using hf.tendsto_leftLim _
  simpa using this
/-
**eVariationOn._root_.BoundedVariationOn.eVariationOn_Ici_eq_Ioi_add_edist** 是 M
athlib 中的一个定理，位于命名空间 `eVariationOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.BoundedVariationOn.eVariationOn_Ici_eq_Ioi_add_edist [CompleteSpace E]
    [DenselyOrdered α] {f : α → E} {a : α} (hf : BoundedVariationOn f univ) :
    eVariationOn f (Ici a) = eVariationOn f (Ioi a) + edist (f a) (f.rightLim a) := by
  rw [← eVariationOn.comp_ofDual f, ← eVariationOn.comp_ofDual f]
  exact hf.ofDual.eVariationOn_Iic_eq_Iio_add_edist (a := toDual a)

/-- If a function has bounded variation, then the variation on
small closed intervals to the left of this point tends to the contribution of the point, i.e.,
the distance between the left limit and the value at the point -/
/-
**eVariationOn._root_.BoundedVariationOn.tendsto_eVariationOn_Icc_left** 是 Mathl
ib 中的一个定理，位于命名空间 `eVariationOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a function has bounded variation, then the variation on
small closed intervals to the left of this point tends to the contribution of th
e point, i.e.,
the distance between the left limit and the value at the point
-/
theorem _root_.BoundedVariationOn.tendsto_eVariationOn_Icc_left
    [TopologicalSpace α] [OrderTopology α] {f : α → E} {s : Set α} {l : E}
    (hf : BoundedVariationOn f s) {x : α} (h'f : Tendsto f (𝓝[s ∩ Iio x] x) (𝓝 l)) (hx : x ∈ s) :
    Tendsto (fun y ↦ eVariationOn f (s ∩ Icc y x)) (𝓝[s ∩ Iio x] x) (𝓝 (edist (f x) l)) := by
  rcases eq_or_neBot (𝓝[s ∩ Iio x] x) with h | h
  · simp [h]
  suffices H : Tendsto (fun y ↦ eVariationOn f (s ∩ Ico y x) + edist (f x) l)
      (𝓝[s ∩ Iio x] x) (𝓝 (0 + edist (f x) l)) by
    simp only [zero_add] at H
    apply Tendsto.congr' _ H
    filter_upwards [self_mem_nhdsWithin] with y hy
    have N : 𝓝[s ∩ Ici y ∩ Iio x] x = 𝓝[s ∩ Iio x] x := by
      rw [show s ∩ Ici y ∩ Iio x = s ∩ Iio x ∩ Ici y by grind, nhdsWithin_inter_of_mem']
      exact mem_nhdsWithin_of_mem_nhds (Ici_mem_nhds hy.2)
    rw [show s ∩ Icc y x = (s ∩ Ici y) ∩ Iic x by grind,
      eVariationOn_on_inter_Iic_eq_Iio_add_edist (l := l)]
    · congr 2; grind
    · convert h using 1
    · exact ⟨hx, hy.2.le⟩
    · convert h'f
  apply Tendsto.add ?_ tendsto_const_nhds
  exact (hf.tendsto_eVariationOn_Ico_zero x).mono_left (nhdsWithin_mono _ inter_subset_left)

/-- If a function has bounded variation, then the variation on
small closed intervals to the right of this point tends to the contribution of the point, i.e.,
the distance between the right limit and the value at the point -/
/-
**eVariationOn._root_.BoundedVariationOn.tendsto_eVariationOn_Icc_right** 是 Math
lib 中的一个定理，位于命名空间 `eVariationOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a function has bounded variation, then the variation on
small closed intervals to the right of this point tends to the contribution of t
he point, i.e.,
the distance between the right limit and the value at the point
-/
theorem _root_.BoundedVariationOn.tendsto_eVariationOn_Icc_right
    [TopologicalSpace α] [OrderTopology α] {f : α → E} {s : Set α} {l : E}
    (hf : BoundedVariationOn f s) {x : α} (h'f : Tendsto f (𝓝[s ∩ Ioi x] x) (𝓝 l)) (hx : x ∈ s) :
    Tendsto (fun y ↦ eVariationOn f (s ∩ Icc x y)) (𝓝[s ∩ Ioi x] x) (𝓝 (edist (f x) l)) := by
  have : (fun y ↦ eVariationOn f (s ∩ Icc x y)) =
      (fun y ↦ eVariationOn (f ∘ ofDual) (ofDual ⁻¹' s ∩ Icc (toDual y) (toDual x))) := by
    ext y
    rw [Icc_toDual, ← preimage_inter, comp_ofDual]
  rw [this]
  exact hf.ofDual.tendsto_eVariationOn_Icc_left h'f hx

/-- If a function has locally bounded variation, then the variation on
small closed intervals to the left of this point tends to the contribution of the point, i.e.,
the distance between the left limit and the value at the point -/
/-
**eVariationOn._root_.LocallyBoundedVariationOn.tendsto_eVariationOn_Icc_left** 
是 Mathlib 中的一个定理，位于命名空间 `eVariationOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a function has locally bounded variation, then the variation on
small closed intervals to the left of this point tends to the contribution of th
e point, i.e.,
the distance between the left limit and the value at the point
-/
theorem _root_.LocallyBoundedVariationOn.tendsto_eVariationOn_Icc_left
    [TopologicalSpace α] [OrderTopology α] {f : α → E} {s : Set α} {l : E}
    (hf : LocallyBoundedVariationOn f s) {x : α}
    (h'f : Tendsto f (𝓝[s ∩ Iio x] x) (𝓝 l)) (hx : x ∈ s) :
    Tendsto (fun y ↦ eVariationOn f (s ∩ Icc y x)) (𝓝[s ∩ Iio x] x) (𝓝 (edist (f x) l)) := by
  rcases eq_or_neBot (𝓝[s ∩ Iio x] x) with h | h
  · simp [h]
  obtain ⟨y, hy⟩ : (s ∩ Iio x).Nonempty := by contrapose! h; simp [h]
  have : 𝓝[s ∩ Iio x] x = 𝓝[(s ∩ Icc y x) ∩ Iio x] x := by
    rw [show (s ∩ Icc y x) ∩ Iio x = (s ∩ Iio x) ∩ Icc y x by grind, eq_comm]
    apply nhdsWithin_inter_of_mem' (nhdsWithin_mono _ inter_subset_right (Icc_mem_nhdsLT hy.2))
  rw [this] at h'f ⊢
  have : BoundedVariationOn f (s ∩ Icc y x) := hf _ _ hy.1 hx
  apply Tendsto.congr' _ (this.tendsto_eVariationOn_Icc_left h'f ⟨hx, by grind⟩)
  filter_upwards [self_mem_nhdsWithin] with z hz
  congr 1
  grind

/-- If a function has locally bounded variation, then the variation on
small closed intervals to the right of this point tends to the contribution of the point, i.e.,
the distance between the right limit and the value at the point -/
/-
**eVariationOn._root_.LocallyBoundedVariationOn.tendsto_eVariationOn_Icc_right**
 是 Mathlib 中的一个定理，位于命名空间 `eVariationOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a function has locally bounded variation, then the variation on
small closed intervals to the right of this point tends to the contribution of t
he point, i.e.,
the distance between the right limit and the value at the point
-/
theorem _root_.LocallyBoundedVariationOn.tendsto_eVariationOn_Icc_right
    [TopologicalSpace α] [OrderTopology α] {f : α → E} {s : Set α} {l : E}
    (hf : LocallyBoundedVariationOn f s) {x : α}
    (h'f : Tendsto f (𝓝[s ∩ Ioi x] x) (𝓝 l)) (hx : x ∈ s) :
    Tendsto (fun y ↦ eVariationOn f (s ∩ Icc x y)) (𝓝[s ∩ Ioi x] x) (𝓝 (edist (f x) l)) := by
  have : (fun y ↦ eVariationOn f (s ∩ Icc x y)) =
      (fun y ↦ eVariationOn (f ∘ ofDual) (ofDual ⁻¹' s ∩ Icc (toDual y) (toDual x))) := by
    ext y
    rw [Icc_toDual, ← preimage_inter, comp_ofDual]
  rw [this]
  exact hf.ofDual.tendsto_eVariationOn_Icc_left h'f hx

/-- If a function has bounded variation and is left-continuous at a point, then the variation on
small closed intervals to the left of this point tends to `0`. -/
/-
**eVariationOn._root_.BoundedVariationOn.tendsto_eVariationOn_Icc_zero_left** 是 
Mathlib 中的一个定理，位于命名空间 `eVariationOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a function has bounded variation and is left-continuous at a point, then the 
variation on
small closed intervals to the left of this point tends to `0`.
-/
theorem _root_.BoundedVariationOn.tendsto_eVariationOn_Icc_zero_left
    [TopologicalSpace α] [OrderTopology α] {f : α → E} {s : Set α}
    (hf : BoundedVariationOn f s) {x : α} (h : ContinuousWithinAt f (s ∩ Iic x) x) :
    Tendsto (fun y ↦ eVariationOn f (s ∩ Icc y x)) (𝓝[s] x) (𝓝 0) := by
  rcases eq_or_neBot (𝓝[s ∩ Iio x] x) with h' | h'
  · apply tendsto_const_nhds.congr'
    have : s = (s ∩ Iio x) ∪ (s ∩ Ici x) := by grind
    nth_rewrite 1 [this]
    simp only [nhdsWithin_union, h', bot_le, sup_of_le_right]
    filter_upwards [self_mem_nhdsWithin] with y hy
    apply (eVariationOn.subsingleton _ (by grind [Set.Subsingleton])).symm
  apply (hf.tendsto_eVariationOn_Ico_zero x).congr (fun y ↦ ?_)
  rcases le_or_gt x y with hy | hy
  · rw [eVariationOn.subsingleton, eVariationOn.subsingleton] <;>
      grind [Set.Subsingleton]
  have W := eVariationOn_inter_Iio_eq_inter_Iic_of_continuousWithinAt (f := f)
    (s := s ∩ Icc y x) (a := x) ?_ ?_
  · convert! W using 2 <;> grind
  · rwa [show s ∩ Icc y x ∩ Iio x = (s ∩ Iio x) ∩ Ici y by grind, nhdsWithin_inter_of_mem']
    apply mem_nhdsWithin_of_mem_nhds
    exact Ici_mem_nhds hy
  · apply h.mono (by grind)

/-- If a function has bounded variation and is right-continuous at a point, then the variation on
small closed intervals to the right of this point tends to `0`. -/
/-
**eVariationOn._root_.BoundedVariationOn.tendsto_eVariationOn_Icc_zero_right** 是
 Mathlib 中的一个定理，位于命名空间 `eVariationOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a function has bounded variation and is right-continuous at a point, then the
 variation on
small closed intervals to the right of this point tends to `0`.
-/
theorem _root_.BoundedVariationOn.tendsto_eVariationOn_Icc_zero_right
    [TopologicalSpace α] [OrderTopology α] {f : α → E} {s : Set α}
    (hf : BoundedVariationOn f s) (x : α) (h : ContinuousWithinAt f (s ∩ Ici x) x) :
    Tendsto (fun y ↦ eVariationOn f (s ∩ Icc x y)) (𝓝[s] x) (𝓝 0) := by
  have : (fun y ↦ eVariationOn f (s ∩ Icc x y)) =
      (fun y ↦ eVariationOn (f ∘ ofDual) (ofDual ⁻¹' s ∩ Icc (toDual y) (toDual x))) := by
    ext y
    rw [Icc_toDual, ← preimage_inter, comp_ofDual]
  rw [this]
  exact hf.ofDual.tendsto_eVariationOn_Icc_zero_left h

/-- If a function `g` is at each point `x` a limit of `f` to the left or to the right (or more
generally a cluster point of the values of `f` around `x`) then the variation of `g` is bounded
by that of `f`. -/
/-
**eVariationOn.eVariationOn_le_of_mapClusterPt** 是 Mathlib 中的一个引理，位于命名空间 `eVaria
tionOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a function `g` is at each point `x` a limit of `f` to the left or to the righ
t (or more
generally a cluster point of the values of `f` around `x`) then the variation of
 `g` is bounded
by that of `f`.
-/
private lemma eVariationOn_le_of_mapClusterPt
    [TopologicalSpace α] [OrderTopology α] {f g : α → E}
    {s : Set α} (hg : ∀ x ∈ s, MapClusterPt (g x) (𝓝[s] x) f) :
    eVariationOn g s ≤ eVariationOn f s := by
  rw [eVariationOn_eq_strictMonoOn]
  apply iSup_le
  rintro ⟨n, u, u_mono, u_mem⟩
  simp only
  have : Nonempty α := ⟨u 0⟩
  apply le_of_forall_lt (fun c hc ↦ ?_)
  have : ∀ᶠ (b : ℕ → E) in 𝓝 (fun i ↦ g (u i)),
      c < ∑ i ∈ Finset.range n, edist (b (i + 1)) (b i) := by
    have : Continuous (fun (v : ℕ → E) ↦ ∑ i ∈ Finset.range n, edist (v (i + 1)) (v i)) := by
      fun_prop
    exact (tendsto_order.1 (this.continuousAt (x := fun i ↦ g (u i))).tendsto).1 c hc
  rw [nhds_pi] at this
  obtain ⟨I, I_fin, t, t_mem, ht⟩ : ∃ (I : Set ℕ), I.Finite ∧ ∃ t, (∀ (i : ℕ), t i ∈ 𝓝 (g (u i))) ∧
      I.pi t ⊆ {b : ℕ → E | c < ∑ i ∈ Finset.range n, edist (b (i + 1)) (b i)} := mem_pi.1 this
  have : ∀ᶠ b in 𝓝 u, ∀ i ∈ ((Finset.Iic n) ×ˢ (Finset.Iic n)).filter
      (fun i ↦ i.1 < i.2), b i.1 < b i.2 := by
    rw [Filter.eventually_all_finset]
    intro i hi
    apply IsOpen.mem_nhds ?_ (by grind [StrictMonoOn])
    exact isOpen_lt (by fun_prop) (by fun_prop)
  rw [nhds_pi] at this
  obtain ⟨J, J_fin, k, k_mem, hk⟩ : ∃ (J : Set ℕ), J.Finite ∧ ∃ k, (∀ (i : ℕ), k i ∈ 𝓝 (u i)) ∧
    J.pi k ⊆ _ := mem_pi.1 this
  have A i (hi : i ∈ Iic n) : ∃ x, (f x ∈ t i ∧ x ∈ k i) ∧ x ∈ s :=
    ((((mapClusterPt_iff_frequently.1 (hg (u i) (u_mem i hi)) (t i) (t_mem i))).and_eventually
      (mem_nhdsWithin_of_mem_nhds (k_mem i))).and_eventually self_mem_nhdsWithin).exists
  choose! v hv h'v using A
  have : c < ∑ i ∈ Finset.range n, edist (f (v (i + 1))) (f (v i)) := by
    let f' i := if i ∈ Iic n then f (v i) else g (u i)
    have : ∑ i ∈ Finset.range n, edist (f (v (i + 1))) (f (v i)) =
        ∑ i ∈ Finset.range n, edist (f' (i + 1)) (f' i) :=
      Finset.sum_congr rfl (fun i hi ↦ by grind)
    rw [this]
    suffices H : f' ∈ I.pi t from ht H
    have A i : g (u i) ∈ t i := mem_of_mem_nhds (t_mem i)
    grind
  apply this.trans_le
  have v_mono : StrictMonoOn v (Iic n) := by
    let w i := if i ∈ Iic n then v i else u i
    suffices w ∈ J.pi k by
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Iic, and_imp, Prod.forall] at hk
      grind [StrictMonoOn]
    have A i : u i ∈ k i := mem_of_mem_nhds (k_mem i)
    grind
  exact sum_le_of_monotoneOn_Iic v_mono.monotoneOn (by grind)
/-
**eVariationOn.eVariationOn_leftLim_le** 是 Mathlib 中的一个引理，位于命名空间 `eVariationOn`。
形式化陈述：eVariationOn_leftLim_le [TopologicalSpace α] [OrderTopology α] {f : α -> E
} {s : Set α} (hs : IsOpen s) : eVariationOn f.leftLim s <= eVariationOn f s
参数：hs : IsOpen s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Topology.EMetricSpace.BoundedVariation.0.eVariationOn.e
VariationOn_le_of_mapClusterPt`：∀ {α : Type u_1} [inst : LinearOrder α] {E : Typ
e u_2} [inst_1 : PseudoEMetricSpace E] [inst_2 : TopologicalSpace α]   [OrderTop
ology α] {f …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOpen.nhdsWithin_eq`：IsOpen.nhdsWithin_eq {a : α} {s : Set α} (h : IsOp
en s) (ha : a in s) : 𝓝[s] a = 𝓝 a
· 使用定理 `MapClusterPt.mono`：MapClusterPt.mono {G : Filter α} (h : MapClusterPt x 
F u) (hle : F <= G) : MapClusterPt x G u
· 使用定理 `mapClusterPt_leftLim`：mapClusterPt_leftLim [TopologicalSpace α] [OrderTo
pology α] (f : α -> β) (a : α) : MapClusterPt (f.leftLim a) (𝓝[<=] a) f
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
-/
lemma eVariationOn_leftLim_le [TopologicalSpace α] [OrderTopology α] {f : α → E}
    {s : Set α} (hs : IsOpen s) :
    eVariationOn f.leftLim s ≤ eVariationOn f s := by
  apply eVariationOn_le_of_mapClusterPt (fun x hx ↦ ?_)
  rw [IsOpen.nhdsWithin_eq hs hx]
  exact (mapClusterPt_leftLim f x).mono nhdsWithin_le_nhds
/-
**eVariationOn.eVariationOn_rightLim_le** 是 Mathlib 中的一个引理，位于命名空间 `eVariationOn`
。
形式化陈述：eVariationOn_rightLim_le [TopologicalSpace α] [OrderTopology α] {f : α -> 
E} {s : Set α} (hs : IsOpen s) : eVariationOn f.rightLim s <= eVariationOn f s
参数：hs : IsOpen s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Topology.EMetricSpace.BoundedVariation.0.eVariationOn.e
VariationOn_le_of_mapClusterPt`：∀ {α : Type u_1} [inst : LinearOrder α] {E : Typ
e u_2} [inst_1 : PseudoEMetricSpace E] [inst_2 : TopologicalSpace α]   [OrderTop
ology α] {f …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOpen.nhdsWithin_eq`：IsOpen.nhdsWithin_eq {a : α} {s : Set α} (h : IsOp
en s) (ha : a in s) : 𝓝[s] a = 𝓝 a
· 使用定理 `MapClusterPt.mono`：MapClusterPt.mono {G : Filter α} (h : MapClusterPt x 
F u) (hle : F <= G) : MapClusterPt x G u
· 使用定理 `mapClusterPt_rightLim`：mapClusterPt_rightLim [TopologicalSpace α] [Order
Topology α] (f : α -> β) (a : α) : MapClusterPt (f.rightLim a) (𝓝[>=] a) f
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
-/
lemma eVariationOn_rightLim_le [TopologicalSpace α] [OrderTopology α] {f : α → E}
    {s : Set α} (hs : IsOpen s) :
    eVariationOn f.rightLim s ≤ eVariationOn f s := by
  apply eVariationOn_le_of_mapClusterPt (fun x hx ↦ ?_)
  rw [IsOpen.nhdsWithin_eq hs hx]
  exact (mapClusterPt_rightLim f x).mono nhdsWithin_le_nhds
/-
**eVariationOn._root_.BoundedVariationOn.leftLim** 是 Mathlib 中的一个引理，位于命名空间 `eVar
iationOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.BoundedVariationOn.leftLim [TopologicalSpace α] [OrderTopology α] {f : α → E}
    (hf : BoundedVariationOn f univ) : BoundedVariationOn f.leftLim univ :=
  ((eVariationOn_leftLim_le isOpen_univ).trans_lt hf.lt_top).ne
/-
**eVariationOn._root_.BoundedVariationOn.rightLim** 是 Mathlib 中的一个引理，位于命名空间 `eVa
riationOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.BoundedVariationOn.rightLim [TopologicalSpace α] [OrderTopology α] {f : α → E}
    (hf : BoundedVariationOn f univ) : BoundedVariationOn f.rightLim univ :=
  ((eVariationOn_rightLim_le isOpen_univ).trans_lt hf.lt_top).ne
/-
**eVariationOn._root_.BoundedVariationOn.continuousWithinAt_leftLim** 是 Mathlib 
中的一个引理，位于命名空间 `eVariationOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.BoundedVariationOn.continuousWithinAt_leftLim [TopologicalSpace α] [OrderTopology α]
    [CompleteSpace E] [T3Space E] {f : α → E} (hf : BoundedVariationOn f univ) {x : α} :
    ContinuousWithinAt f.leftLim (Iic x) x := by
  have : Tendsto f.leftLim (𝓝[<] x) (𝓝 (f.leftLim.leftLim x)) := hf.leftLim.tendsto_leftLim x
  rw [leftLim_leftLim (hf.tendsto_leftLim x)] at this
  exact continuousWithinAt_Iio_iff_Iic.1 this
/-
**eVariationOn._root_.BoundedVariationOn.continuousWithinAt_rightLim** 是 Mathlib
 中的一个引理，位于命名空间 `eVariationOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.BoundedVariationOn.continuousWithinAt_rightLim [TopologicalSpace α] [OrderTopology α]
    [CompleteSpace E] [T3Space E] {f : α → E} (hf : BoundedVariationOn f univ) {x : α} :
    ContinuousWithinAt f.rightLim (Ici x) x :=
  BoundedVariationOn.continuousWithinAt_leftLim hf.ofDual

/-! ### Limits of bounded variation functions as `± ∞` -/

/-- If a function has bounded variation, then the variation on closed semi-infinite
intervals tends to `0` at `+∞`. -/
/-
**eVariationOn._root_.BoundedVariationOn.tendsto_eVariationOn_Ici_zero** 是 Mathl
ib 中的一个定理，位于命名空间 `eVariationOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a function has bounded variation, then the variation on closed semi-infinite
intervals tends to `0` at `+∞`.
-/
theorem _root_.BoundedVariationOn.tendsto_eVariationOn_Ici_zero
    {f : α → E} {s : Set α} (hf : BoundedVariationOn f s) :
    Tendsto (fun y ↦ eVariationOn f (s ∩ Ici y)) (𝓟 s ⊓ atTop) (𝓝 0) :=
  hf.tendsto_eVariationOn_Ici_zero_of_filter _
    (fun y _ ↦ inter_mem_inf (mem_principal_self s) (Ici_mem_atTop y))

/-- If a function has bounded variation, then the variation on semi-infinite closed
intervals tends to `0` at `-∞`. -/
/-
**eVariationOn._root_.BoundedVariationOn.tendsto_eVariationOn_Iic_zero** 是 Mathl
ib 中的一个定理，位于命名空间 `eVariationOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a function has bounded variation, then the variation on semi-infinite closed
intervals tends to `0` at `-∞`.
-/
theorem _root_.BoundedVariationOn.tendsto_eVariationOn_Iic_zero
    {f : α → E} {s : Set α} (hf : BoundedVariationOn f s) :
    Tendsto (fun y ↦ eVariationOn f (s ∩ Iic y)) (𝓟 s ⊓ atBot) (𝓝 0) := by
  have : (fun y ↦ eVariationOn f (s ∩ Iic y)) =
      (fun y ↦ eVariationOn (f ∘ ofDual) (ofDual ⁻¹' s ∩ Ici (toDual y))) := by
    ext y
    rw [Ici_toDual, ← preimage_inter, comp_ofDual]
  rw [this]
  exact hf.ofDual.tendsto_eVariationOn_Ici_zero

/-- A bounded variation function has a limit at `+∞`. -/
/-
**eVariationOn._root_.BoundedVariationOn.exists_tendsto_atTop** 是 Mathlib 中的一个定理
，位于命名空间 `eVariationOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bounded variation function has a limit at `+∞`.
-/
theorem _root_.BoundedVariationOn.exists_tendsto_atTop [CompleteSpace E] [hE : Nonempty E]
    {f : α → E} {s : Set α} (hf : BoundedVariationOn f s) :
    ∃ l, Tendsto f (𝓟 s ⊓ atTop) (𝓝 l) := by
  rcases eq_empty_or_nonempty s with rfl | hs
  · simp
  · exact hf.exists_tendsto_left_of_filter _
      (fun y hy ↦ inter_mem_inf (mem_principal_self s) (Ici_mem_atTop _)) hs

/-- A bounded variation function has a limit at `-∞`. -/
/-
**eVariationOn._root_.BoundedVariationOn.exists_tendsto_atBot** 是 Mathlib 中的一个定理
，位于命名空间 `eVariationOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bounded variation function has a limit at `-∞`.
-/
theorem _root_.BoundedVariationOn.exists_tendsto_atBot [CompleteSpace E] [hE : Nonempty E]
    {f : α → E} {s : Set α} (hf : BoundedVariationOn f s) :
    ∃ l, Tendsto f (𝓟 s ⊓ atBot) (𝓝 l) :=
  hf.ofDual.exists_tendsto_atTop
/-
**eVariationOn._root_.BoundedVariationOn.tendsto_atTop_limUnder** 是 Mathlib 中的一个
定理，位于命名空间 `eVariationOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.BoundedVariationOn.tendsto_atTop_limUnder [CompleteSpace E] [hE : Nonempty E]
    {f : α → E} (hf : BoundedVariationOn f univ) :
    Tendsto f atTop (𝓝 (limUnder atTop f)) :=
  tendsto_nhds_limUnder (by simpa using hf.exists_tendsto_atTop)
/-
**eVariationOn._root_.BoundedVariationOn.tendsto_atBot_limUnder** 是 Mathlib 中的一个
定理，位于命名空间 `eVariationOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.BoundedVariationOn.tendsto_atBot_limUnder [CompleteSpace E] [hE : Nonempty E]
    {f : α → E} (hf : BoundedVariationOn f univ) :
    Tendsto f atBot (𝓝 (limUnder atBot f)) :=
  tendsto_nhds_limUnder (by simpa using hf.exists_tendsto_atBot)

end eVariationOn

section Monotone

/-! ### Variation of monotone functions -/

open ENNReal Finset

variable {f : α → ℝ} {s : Set α} {C : ℝ} {a b : α}

/-- The variation of a monotone real-valued function on `s ∩ Icc a b` equals its increment
`f b - f a`. -/
/-
**MonotoneOn.eVariationOn_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.eVariationOn_eq (hf : MonotoneOn f s) (as : a in s) (bs : b in 
s) : eVariationOn f (s inter Icc a b) = .ofReal (f b - f a)
参数：hf : MonotoneOn f s；as : a in s；bs : b in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_dist`：edist_dist (x y : α) : edist x y = ENNReal.ofReal (dist x y)
· 使用定理 `Real.dist_eq`：Real.dist_eq (x y : Real) : dist x y = |x - y|
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `sub_nonneg_of_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Ad
dRightMono α] {a b : α}, b ≤ a → 0 ≤ a - b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `ENNReal.ofReal_sum_of_nonneg`：ofReal_sum_of_nonneg {s : Finset α} {f : α
 -> Real} (hf : forall i, i in s -> 0 <= f i) : ENNReal.ofReal (∑ i in s, f i) =
 ∑ i in s, ENNReal…
· 使用定理 `Finset.sum_range_sub`：∀ {G : Type u_3} [inst : AddCommGroup G] (f : ℕ → 
G) (n : ℕ), ∑ i ∈ Finset.range n, (f (i + 1) - f i) = f n - f 0
· 使用定理 `ENNReal.ofReal_le_ofReal`：ofReal_le_ofReal {p q : Real} (h : p <= q) : E
NNReal.ofReal p <= ENNReal.ofReal q
· 使用定理 `sub_le_sub`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : Preorder α]
 [AddLeftMono α] {a b c d : α},   a ≤ b → c ≤ d → a - d ≤ b - c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `ENNReal.ofReal_lt_top`：∀ {r : ℝ}, ENNReal.ofReal r < ⊤
· 使用定理 `eq_of_le_of_ge`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `ENNReal.ofReal_le_of_le_toReal`：ofReal_le_of_le_toReal {a : Real} {b : R
eal>=0∞} (h : a <= ENNReal.toReal b) : ENNReal.ofReal a <= b
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `BoundedVariationOn.dist_le`：∀ {α : Type u_1} [inst : LinearOrder α] {E :
 Type u_3} [inst_1 : PseudoMetricSpace E] {f : α → E} {s : Set α},   BoundedVari
ationOn f s → ∀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Icc_eq_empty`：Icc_eq_empty (h : ¬a <= b) : Icc a b = ∅
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
The variation of a monotone real-valued function on `s ∩ Icc a b` equals its inc
rement
`f b - f a`.
-/
theorem MonotoneOn.eVariationOn_eq (hf : MonotoneOn f s) (as : a ∈ s) (bs : b ∈ s) :
    eVariationOn f (s ∩ Icc a b) = .ofReal (f b - f a) := by
  rcases le_or_gt a b with hab | hab
  · have hle : eVariationOn f (s ∩ Icc a b) ≤ .ofReal (f b - f a) := by
      apply iSup_le _
      rintro ⟨n, ⟨u, hu, us⟩⟩
      calc
        _ = ∑ i ∈ range n, .ofReal (f (u (i + 1)) - f (u i)) := by
          refine sum_congr rfl fun i hi => ?_
          simp only [Finset.mem_range] at hi
          rw [edist_dist, Real.dist_eq, abs_of_nonneg]
          exact sub_nonneg_of_le (hf (us i).1 (us (i + 1)).1 (hu (Nat.le_succ _)))
        _ = .ofReal (∑ i ∈ range n, (f (u (i + 1)) - f (u i))) := by
          rw [ofReal_sum_of_nonneg]
          exact fun i _ ↦ sub_nonneg_of_le (hf (us i).1 (us (i + 1)).1 (hu (Nat.le_succ _)))
        _ = .ofReal (f (u n) - f (u 0)) := by rw [sum_range_sub (f <| u ·)]
        _ ≤ _ :=
          ofReal_le_ofReal (sub_le_sub (hf (us n).1 bs (us n).2.2) (hf as (us 0).1 (us 0).2.1))
    have h : BoundedVariationOn f (s ∩ Icc a b) := (hle.trans_lt ofReal_lt_top).ne
    apply eq_of_le_of_ge hle (ofReal_le_of_le_toReal _)
    grw [← h.dist_le (x := a) (y := b)] <;> grind [Real.dist_eq]
  · simp [hab, hf bs as hab.le]

@[deprecated MonotoneOn.eVariationOn_eq (since := "2026-07-08")]
/-
**MonotoneOn.eVariationOn_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.eVariationOn_le (hf : MonotoneOn f s) (as : a in s) (bs : b in 
s) : eVariationOn f (s inter Icc a b) <= .ofReal (f b - f a)
参数：hf : MonotoneOn f s；as : a in s；bs : b in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MonotoneOn.eVariationOn_eq`：MonotoneOn.eVariationOn_eq (hf : MonotoneOn 
f s) (as : a in s) (bs : b in s) : eVariationOn f (s inter Icc a b) = .ofReal (f
 b - f a)
-/
theorem MonotoneOn.eVariationOn_le (hf : MonotoneOn f s) (as : a ∈ s) (bs : b ∈ s) :
    eVariationOn f (s ∩ Icc a b) ≤ .ofReal (f b - f a) := (hf.eVariationOn_eq as bs).le
/-
**MonotoneOn.locallyBoundedVariationOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.locallyBoundedVariationOn (hf : MonotoneOn f s) : LocallyBounde
dVariationOn f s
参数：hf : MonotoneOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `ENNReal.ofReal_lt_top`：∀ {r : ℝ}, ENNReal.ofReal r < ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonotoneOn.eVariationOn_eq`：MonotoneOn.eVariationOn_eq (hf : MonotoneOn 
f s) (as : a in s) (bs : b in s) : eVariationOn f (s inter Icc a b) = .ofReal (f
 b - f a)
-/
theorem MonotoneOn.locallyBoundedVariationOn (hf : MonotoneOn f s) :
    LocallyBoundedVariationOn f s := fun _ _ as bs =>
  ((hf.eVariationOn_eq as bs) ▸ ofReal_lt_top).ne
/-
**MonotoneOn.boundedVariationOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.boundedVariationOn (hf : MonotoneOn f s) (h : forall x in s, |f
 x| <= C) : BoundedVariationOn f s
参数：hf : MonotoneOn f s；h : forall x in s, |f x| <= C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eVariationOn.eq_biSup_inter_Icc`：eq_biSup_inter_Icc {f : α -> E} {s : Se
t α} : eVariationOn f s = ⨆ p in {p : α × α | p.1 in s ∧ p.2 in s ∧ p.1 <= p.2},
 eVariationOn f (s in…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `MonotoneOn.eVariationOn_eq`：MonotoneOn.eVariationOn_eq (hf : MonotoneOn 
f s) (as : a in s) (bs : b in s) : eVariationOn f (s inter Icc a b) = .ofReal (f
 b - f a)
· 使用引理 `ENNReal.ofReal_mono`：ofReal_mono : Monotone ENNReal.ofReal
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.ofReal_mul`：ofReal_mul {p q : Real} (hp : 0 <= p) : ENNReal.ofRe
al (p * q) = ENNReal.ofReal p * ENNReal.ofReal q
· 使用定理 `ENNReal.ofReal_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], ENNReal.ofReal (O
fNat.ofNat n) = OfNat.ofNat n
-/
theorem MonotoneOn.boundedVariationOn (hf : MonotoneOn f s) (h : ∀ x ∈ s, |f x| ≤ C) :
    BoundedVariationOn f s := by
  suffices eVariationOn f s ≤ .ofReal (2 * C) from
    ne_of_lt (this.trans_lt (by simp [mul_lt_top]))
  rw [eVariationOn.eq_biSup_inter_Icc]
  simp only [mem_ofPred_eq, iSup_le_iff, and_imp, Prod.forall]
  intro a b as bs hab
  grw [hf.eVariationOn_eq as bs]
  exact ofReal_mono (by grind)

/-- The variation of the identity on `s ∩ Icc a b` is `b - a`. -/
/-
**eVariationOn_id** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eVariationOn_id {a b : Real} {s : Set Real} (as : a in s) (bs : b in s) : 
eVariationOn id (s inter Icc a b) = .ofReal (b - a)
参数：as : a in s；bs : b in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.eVariationOn_eq`：MonotoneOn.eVariationOn_eq (hf : MonotoneOn 
f s) (as : a in s) (bs : b in s) : eVariationOn f (s inter Icc a b) = .ofReal (f
 b - f a)
· 使用定理 `Monotone.monotoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Monotone f → ∀ (s : Set α), MonotoneOn f s
· 使用定理 `monotone_id`：monotone_id [Preorder α] : Monotone (id : α -> α)

--- 原说明 ---
The variation of the identity on `s ∩ Icc a b` is `b - a`.
-/
lemma eVariationOn_id {a b : ℝ} {s : Set ℝ} (as : a ∈ s) (bs : b ∈ s) :
    eVariationOn id (s ∩ Icc a b) = .ofReal (b - a) :=
  (monotone_id.monotoneOn _).eVariationOn_eq as bs

/-- The variation of the identity on `Icc a b` is `b - a`. -/
@[simp]
/-
**eVariationOn_id_Icc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eVariationOn_id_Icc (a b : Real) : eVariationOn id (Icc a b) = .ofReal (b 
- a)
参数：a b : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用引理 `eVariationOn_id`：eVariationOn_id {a b : Real} {s : Set Real} (as : a in 
s) (bs : b in s) : eVariationOn id (s inter Icc a b) = .ofReal (b - a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
The variation of the identity on `Icc a b` is `b - a`.
-/
lemma eVariationOn_id_Icc (a b : ℝ) : eVariationOn id (Icc a b) = .ofReal (b - a) := by
  simpa using eVariationOn_id (s := univ) (by simp) (by simp)

/-- The identity function has bounded variation on every interval `Icc a b`. -/
@[simp]
/-
**BoundedVariationOn.id_Icc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：BoundedVariationOn.id_Icc (a b : Real) : BoundedVariationOn id (Icc a b)
参数：a b : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `eVariationOn_id_Icc`：eVariationOn_id_Icc (a b : Real) : eVariationOn id 
(Icc a b) = .ofReal (b - a)
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
The identity function has bounded variation on every interval `Icc a b`.
-/
lemma BoundedVariationOn.id_Icc (a b : ℝ) : BoundedVariationOn id (Icc a b) := by
  simp [BoundedVariationOn]

end Monotone

/-! ### Lipschitz functions and bounded variation -/

section LipschitzOnWith

variable {F : Type*} [PseudoEMetricSpace F]

/-
**LipschitzOnWith.comp_eVariationOn_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LipschitzOnWith.comp_eVariationOn_le {f : E -> F} {C : Real>=0} {t : Set E
} (h : LipschitzOnWith C f t) {g : α -> E} {s : Set α} (hg : MapsTo g s t) : eVa
riationOn (f ∘ g) s <= C * eVariationOn g s
参数：h : LipschitzOnWith C f t；hg : MapsTo g s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `eVariationOn.sum_le`：sum_le {f : α -> E} {s : Set α} {n : Nat} {u : Nat 
-> α} (hu : Monotone u) (us : forall i, u i in s) : (∑ i in Finset.range n, edis
t (f (u (…
-/
theorem LipschitzOnWith.comp_eVariationOn_le {f : E → F} {C : ℝ≥0} {t : Set E}
    (h : LipschitzOnWith C f t) {g : α → E} {s : Set α} (hg : MapsTo g s t) :
    eVariationOn (f ∘ g) s ≤ C * eVariationOn g s := by
  apply iSup_le _
  rintro ⟨n, ⟨u, hu, us⟩⟩
  calc
    (∑ i ∈ Finset.range n, edist (f (g (u (i + 1)))) (f (g (u i)))) ≤
        ∑ i ∈ Finset.range n, C * edist (g (u (i + 1))) (g (u i)) :=
      Finset.sum_le_sum fun i _ => h (hg (us _)) (hg (us _))
    _ = C * ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i)) := by rw [Finset.mul_sum]
    _ ≤ C * eVariationOn g s := by grw [eVariationOn.sum_le hu us]
/-
**LipschitzOnWith.comp_boundedVariationOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LipschitzOnWith.comp_boundedVariationOn {f : E -> F} {C : Real>=0} {t : Se
t E} (hf : LipschitzOnWith C f t) {g : α -> E} {s : Set α} (hg : MapsTo g s t) (
h : BoundedVariationOn g s) : BoundedVariationOn (f ∘ g) s
参数：hf : LipschitzOnWith C f t；hg : MapsTo g s t；h : BoundedVariationOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `ENNReal.mul_ne_top`：mul_ne_top : a != ∞ -> b != ∞ -> a * b != ∞
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `LipschitzOnWith.comp_eVariationOn_le`：LipschitzOnWith.comp_eVariationOn_
le {f : E -> F} {C : Real>=0} {t : Set E} (h : LipschitzOnWith C f t) {g : α -> 
E} {s : Set α} (hg : MapsT…
-/
theorem LipschitzOnWith.comp_boundedVariationOn {f : E → F} {C : ℝ≥0} {t : Set E}
    (hf : LipschitzOnWith C f t) {g : α → E} {s : Set α} (hg : MapsTo g s t)
    (h : BoundedVariationOn g s) : BoundedVariationOn (f ∘ g) s :=
  ne_top_of_le_ne_top (by finiteness) (hf.comp_eVariationOn_le hg)
/-
**LipschitzOnWith.comp_locallyBoundedVariationOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LipschitzOnWith.comp_locallyBoundedVariationOn {f : E -> F} {C : Real>=0} 
{t : Set E} (hf : LipschitzOnWith C f t) {g : α -> E} {s : Set α} (hg : MapsTo g
 s t) (h : LocallyBoundedVariationOn g s) : LocallyBoundedVariationOn (f ∘ g) s
参数：hf : LipschitzOnWith C f t；hg : MapsTo g s t；h : LocallyBoundedVariationOn g 
s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzOnWith.comp_boundedVariationOn`：LipschitzOnWith.comp_boundedVar
iationOn {f : E -> F} {C : Real>=0} {t : Set E} (hf : LipschitzOnWith C f t) {g 
: α -> E} {s : Set α} (hg : M…
· 使用定理 `Set.MapsTo.mono_left`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t
 : Set β} {f : α → β}, Set.MapsTo f s₁ t → s₂ ⊆ s₁ → Set.MapsTo f s₂ t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
theorem LipschitzOnWith.comp_locallyBoundedVariationOn {f : E → F} {C : ℝ≥0} {t : Set E}
    (hf : LipschitzOnWith C f t) {g : α → E} {s : Set α} (hg : MapsTo g s t)
    (h : LocallyBoundedVariationOn g s) : LocallyBoundedVariationOn (f ∘ g) s :=
  fun x y xs ys =>
  hf.comp_boundedVariationOn (hg.mono_left inter_subset_left) (h x y xs ys)
/-
**LipschitzWith.comp_boundedVariationOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LipschitzWith.comp_boundedVariationOn {f : E -> F} {C : Real>=0} (hf : Lip
schitzWith C f) {g : α -> E} {s : Set α} (h : BoundedVariationOn g s) : BoundedV
ariationOn (f ∘ g) s
参数：hf : LipschitzWith C f；h : BoundedVariationOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzOnWith.comp_boundedVariationOn`：LipschitzOnWith.comp_boundedVar
iationOn {f : E -> F} {C : Real>=0} {t : Set E} (hf : LipschitzOnWith C f t) {g 
: α -> E} {s : Set α} (hg : M…
· 使用定理 `LipschitzWith.lipschitzOnWith`：∀ {α : Type u} {β : Type v} [inst : Pseud
oEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β}   {s :
 Set α}, LipschitzW…
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ
-/
theorem LipschitzWith.comp_boundedVariationOn {f : E → F} {C : ℝ≥0} (hf : LipschitzWith C f)
    {g : α → E} {s : Set α} (h : BoundedVariationOn g s) : BoundedVariationOn (f ∘ g) s :=
  hf.lipschitzOnWith.comp_boundedVariationOn (mapsTo_univ _ _) h
/-
**LipschitzWith.comp_locallyBoundedVariationOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LipschitzWith.comp_locallyBoundedVariationOn {f : E -> F} {C : Real>=0} (h
f : LipschitzWith C f) {g : α -> E} {s : Set α} (h : LocallyBoundedVariationOn g
 s) : LocallyBoundedVariationOn (f ∘ g) s
参数：hf : LipschitzWith C f；h : LocallyBoundedVariationOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzOnWith.comp_locallyBoundedVariationOn`：LipschitzOnWith.comp_loc
allyBoundedVariationOn {f : E -> F} {C : Real>=0} {t : Set E} (hf : LipschitzOnW
ith C f t) {g : α -> E} {s : Set α} …
· 使用定理 `LipschitzWith.lipschitzOnWith`：∀ {α : Type u} {β : Type v} [inst : Pseud
oEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β}   {s :
 Set α}, LipschitzW…
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ
-/
theorem LipschitzWith.comp_locallyBoundedVariationOn {f : E → F} {C : ℝ≥0}
    (hf : LipschitzWith C f) {g : α → E} {s : Set α} (h : LocallyBoundedVariationOn g s) :
    LocallyBoundedVariationOn (f ∘ g) s :=
  hf.lipschitzOnWith.comp_locallyBoundedVariationOn (mapsTo_univ _ _) h
/-
**LipschitzOnWith.locallyBoundedVariationOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LipschitzOnWith.locallyBoundedVariationOn {f : Real -> E} {C : Real>=0} {s
 : Set Real} (hf : LipschitzOnWith C f s) : LocallyBoundedVariationOn f s
参数：hf : LipschitzOnWith C f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzOnWith.comp_locallyBoundedVariationOn`：LipschitzOnWith.comp_loc
allyBoundedVariationOn {f : E -> F} {C : Real>=0} {t : Set E} (hf : LipschitzOnW
ith C f t) {g : α -> E} {s : Set α} …
· 使用定理 `Set.mapsTo_id`：mapsTo_id (s : Set α) : MapsTo id s s
· 使用定理 `MonotoneOn.locallyBoundedVariationOn`：MonotoneOn.locallyBoundedVariation
On (hf : MonotoneOn f s) : LocallyBoundedVariationOn f s
· 使用定理 `monotoneOn_id`：monotoneOn_id [Preorder α] {s : Set α} : MonotoneOn id s
-/
theorem LipschitzOnWith.locallyBoundedVariationOn {f : ℝ → E} {C : ℝ≥0} {s : Set ℝ}
    (hf : LipschitzOnWith C f s) : LocallyBoundedVariationOn f s :=
  hf.comp_locallyBoundedVariationOn (mapsTo_id _)
    (@monotoneOn_id ℝ _ s).locallyBoundedVariationOn
/-
**LipschitzWith.locallyBoundedVariationOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LipschitzWith.locallyBoundedVariationOn {f : Real -> E} {C : Real>=0} (hf 
: LipschitzWith C f) (s : Set Real) : LocallyBoundedVariationOn f s
参数：hf : LipschitzWith C f；s : Set Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzOnWith.locallyBoundedVariationOn`：LipschitzOnWith.locallyBounde
dVariationOn {f : Real -> E} {C : Real>=0} {s : Set Real} (hf : LipschitzOnWith 
C f s) : LocallyBoundedVariatio…
· 使用定理 `LipschitzWith.lipschitzOnWith`：∀ {α : Type u} {β : Type v} [inst : Pseud
oEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β}   {s :
 Set α}, LipschitzW…
-/
theorem LipschitzWith.locallyBoundedVariationOn {f : ℝ → E} {C : ℝ≥0} (hf : LipschitzWith C f)
    (s : Set ℝ) : LocallyBoundedVariationOn f s :=
  hf.lipschitzOnWith.locallyBoundedVariationOn

end LipschitzOnWith

