/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.RingTheory.PowerSeries.PiTopology

/-!
# Generating functions for partitions

This file defines generating functions related to partitions. Given a character function $f(i, c)$
of a part $i$ and the number of occurrences of the part $c$, the related generating function is
$$
G_f(X) = \sum_{n = 0}^{\infty} \left(\sum_{p \in P_{n}} \prod_{i \in p} f(i, \#i)\right) X^n
= \prod_{i = 1}^{\infty}\left(1 + \sum_{j = 1}^{\infty} f(i, j) X^{ij}\right)
$$
where $P_n$ is all partitions of $n$, $\#i$ is the count of $i$ in the partition $p$.
We give the definition `Nat.Partition.genFun` using the first equation, and prove the second
equation in `Nat.Partition.hasProd_genFun` (with shifted indices).

This generating function can be specialized to
* When $f(i, c) = 1$, this is the generating function for partition function $p(n)$
  (TODO: prove this).
* When $f(i, 1) = 1$ and $f(i, c) = 0$ for $c > 1$, this is the generating function for
  `#(Nat.Partition.distincts n)`. More generally, setting $f(i, c) = 1$ only for $c < m$ gives
  the generating function for `#(Nat.Partition.countRestricted n m)`.
  (See `Nat.Partition.hasProd_powerSeriesMk_card_countRestricted`).
* When $f(i, c) = 1$ for odd $i$ and $f(i, c) = 0$ for even $i$, this is the generating function for
  `#(Nat.Partition.odds n)`. More generally, setting $f(i, c) = 1$ only for $i$ satisfying certain
  `p : Prop` gives the generating function for `#(Nat.Partition.restricted n p)`.
  (See `Nat.Partition.hasProd_powerSeriesMk_card_restricted`)

The definition of `Nat.Partition.genFun` ignores the value of $f(0, c)$ and $f(i, 0)$. The formula
can be interpreted as assuming $f(i, 0) = 1$ and $f(0, c) = 0$ for $c \ne 0$. In theory we could
respect the actual value of $f(0, c)$ and $f(i, 0)$, but it makes the otherwise finite sum and
product potentially infinite.
-/

@[expose] public section

open Finset PowerSeries
open scoped PowerSeries.WithPiTopology

namespace Nat.Partition
variable {R : Type*} [CommSemiring R]

/-- Generating function associated with character $f(i, c)$ for partition functions, where $i$ is a
part of the partition, and $c$ is the count of that part in the partition. The character function is
multiplied within one `n.Partition`, and summed among all `n.Partition` for a fixed `n`. This way,
each `n` is assigned a value, which we use as the coefficients of the power series.

See the module docstring of `Combinatorics.Enumerative.Partition.GenFun` for more details. -/
/-
**Nat.Partition.genFun** 是 Mathlib 中的一个定义，位于命名空间 `Nat.Partition`。
形式化陈述：genFun (f : Nat -> Nat -> R) : R⟦X⟧
参数：f : Nat -> Nat -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Generating function associated with character $f(i, c)$ for partition functions,
 where $i$ is a
part of the partition, and $c$ is the count of that part in the partition. The c
haracter function is
multiplied within one `n.Partition`, and summed among all `n.Partition` for a fi
xed `n`. This way,
each `n` is assigned a value, which we use as the coefficients of the power seri
es.

See the module docstring of `Combinatorics.Enumerative.Partition.GenFun` for mor
e details.
-/
noncomputable def genFun (f : ℕ → ℕ → R) : R⟦X⟧ :=
  PowerSeries.mk fun n ↦ ∑ p : n.Partition, p.parts.toFinsupp.prod f

@[simp]
/-
**Nat.Partition.coeff_genFun** 是 Mathlib 中的一个引理，位于命名空间 `Nat.Partition`。
形式化陈述：coeff_genFun (f : Nat -> Nat -> R) (n : Nat) : (genFun f).coeff n = ∑ p : 
n.Partition, p.parts.toFinsupp.prod f
参数：f : Nat -> Nat -> R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.coeff_mk`：coeff_mk (n : Nat) (f : Nat -> R) : coeff n (mk f)
 = f n
-/
lemma coeff_genFun (f : ℕ → ℕ → R) (n : ℕ) :
    (genFun f).coeff n = ∑ p : n.Partition, p.parts.toFinsupp.prod f :=
  PowerSeries.coeff_mk _ _

/-- The summands in the formula `Nat.Partition.hasProd_genFun` tends to infinity in their order. -/
/-
**Nat.Partition.tendsto_order_genFun_term_atTop_nhds_top** 是 Mathlib 中的一个定理，位于命名
空间 `Nat.Partition`。
形式化陈述：tendsto_order_genFun_term_atTop_nhds_top (f : Nat -> Nat -> R) (i : Nat) :
 Filter.Tendsto (fun j => (f (i + 1) (j + 1) • (X : R⟦X⟧) ^ ((i + 1) * (j + 1)))
.order) Filter.atTop (nhds ⊤)
参数：f : Nat -> Nat -> R；i : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENat.tendsto_nhds_top_iff_natCast_lt`：tendsto_nhds_top_iff_natCast_lt {α
 : Type*} {l : Filter α} {f : α -> Nat∞} : Tendsto f l (𝓝 ⊤) ↔ forall n : Nat, f
orallᶠ a in l, n < f a
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.smul_eq_C_mul`：smul_eq_C_mul (f : R⟦X⟧) (a : R) : a • f = C 
a * f
· 使用定理 `lt_imp_lt_of_le_of_le`：lt_imp_lt_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a < b -> c < d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `PowerSeries.le_order_mul`：le_order_mul (φ ψ : R⟦X⟧) : order φ + order ψ 
<= order (φ * ψ)
· 使用定理 `lt_add_of_nonneg_of_lt`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1
 : Preorder α] [AddRightMono α] {a b c : α}, 0 ≤ a → b < c → b < a + c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subsingleton.eq_zero`：∀ {α : Type u} [inst : Zero α] [Subsingleton α] (a
 : α), a = 0
· 使用定理 `PowerSeries.instSubsingleton`：∀ {R : Type u_1} [Semiring R] [Subsingleto
n R], Subsingleton (PowerSeries R)
· 使用定理 `PowerSeries.order_zero`：order_zero : order (0 : R⟦X⟧) = ⊤
· 使用定理 `PowerSeries.order_X_pow`：order_X_pow (n : Nat) : order ((X : R⟦X⟧) ^ n) 
= n
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞

--- 原说明 ---
The summands in the formula `Nat.Partition.hasProd_genFun` tends to infinity in 
their order.
-/
theorem tendsto_order_genFun_term_atTop_nhds_top (f : ℕ → ℕ → R) (i : ℕ) :
    Filter.Tendsto (fun j ↦ (f (i + 1) (j + 1) • (X : R⟦X⟧) ^ ((i + 1) * (j + 1))).order)
    Filter.atTop (nhds ⊤) := by
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr (fun n ↦ Filter.eventually_atTop.mpr ⟨n, ?_⟩)
  intro m hm
  grw [PowerSeries.smul_eq_C_mul, ← le_order_mul]
  refine lt_add_of_nonneg_of_lt (by simp) ?_
  nontriviality R using Subsingleton.eq_zero (α := R⟦X⟧)
  rw [order_X_pow]
  norm_cast
  grind

variable [TopologicalSpace R]

/-- The infinite sum in the formula `Nat.Partition.hasProd_genFun` always converges. -/
/-
**Nat.Partition.summable_genFun_term** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partition`。
形式化陈述：summable_genFun_term (f : Nat -> Nat -> R) (i : Nat) : Summable fun j => f
 (i + 1) (j + 1) • (X : R⟦X⟧) ^ ((i + 1) * (j + 1))
参数：f : Nat -> Nat -> R；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.WithPiTopology.summable_of_tendsto_order_atTop_nhds_top`：sum
mable_of_tendsto_order_atTop_nhds_top [LinearOrder ι] [LocallyFiniteOrderBot ι] 
(h : Tendsto (fun i => (f i).order) atTop (𝓝 ⊤)) : Summab…
· 使用定理 `Nat.Partition.tendsto_order_genFun_term_atTop_nhds_top`：tendsto_order_ge
nFun_term_atTop_nhds_top (f : Nat -> Nat -> R) (i : Nat) : Filter.Tendsto (fun j
 => (f (i + 1) (j + 1) • (X : R⟦X⟧) ^ ((i + …

--- 原说明 ---
The infinite sum in the formula `Nat.Partition.hasProd_genFun` always converges.
-/
theorem summable_genFun_term (f : ℕ → ℕ → R) (i : ℕ) :
    Summable fun j ↦ f (i + 1) (j + 1) • (X : R⟦X⟧) ^ ((i + 1) * (j + 1)) := by
  apply WithPiTopology.summable_of_tendsto_order_atTop_nhds_top
  apply tendsto_order_genFun_term_atTop_nhds_top

/-- Alternative form of `summable_genFun_term` that unshifts the first index. -/
/-
**Nat.Partition.summable_genFun_term'** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partition`。
形式化陈述：summable_genFun_term' (f : Nat -> Nat -> R) {i : Nat} (hi : i != 0) : Summ
able fun j => f i (j + 1) • (X : R⟦X⟧) ^ (i * (j + 1))
参数：f : Nat -> Nat -> R；hi : i != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_add_one_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k + 1
· 使用定理 `Nat.Partition.summable_genFun_term`：summable_genFun_term (f : Nat -> Nat
 -> R) (i : Nat) : Summable fun j => f (i + 1) (j + 1) • (X : R⟦X⟧) ^ ((i + 1) *
 (j + 1))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Alternative form of `summable_genFun_term` that unshifts the first index.
-/
theorem summable_genFun_term' (f : ℕ → ℕ → R) {i : ℕ} (hi : i ≠ 0) :
    Summable fun j ↦ f i (j + 1) • (X : R⟦X⟧) ^ (i * (j + 1)) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hi
  apply summable_genFun_term

variable [T2Space R]
/-
**Nat.Partition.aux_dvd_of_coeff_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partitio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem aux_dvd_of_coeff_ne_zero {f : ℕ → ℕ → R} {d : ℕ} {s : Finset ℕ} (hs0 : 0 ∉ s)
    {g : ℕ →₀ ℕ} (hg : g ∈ s.finsuppAntidiag d)
    (hprod : ∀ i ∈ s, (coeff (g i)) (1 + ∑' j, f i (j + 1) • X ^ (i * (j + 1))) ≠ (0 : R)) (x : ℕ) :
    x ∣ g x := by
  by_cases hx : x ∈ s
  · specialize hprod x hx
    contrapose hprod
    have hx0 : x ≠ 0 := fun h ↦ hs0 (h ▸ hx)
    rw [map_add, (summable_genFun_term' f hx0).map_tsum _ (WithPiTopology.continuous_coeff _ _)]
    rw [show (0 : R) = 0 + ∑' (i : ℕ), 0 by simp]
    congrm (?_ + ∑' (i : ℕ), ?_)
    · suffices g x ≠ 0 by simp [this]
      contrapose hprod
      simp [hprod]
    · rw [map_smul, coeff_X_pow]
      apply smul_eq_zero_of_right
      suffices g x ≠ x * (i + 1) by simp [this]
      contrapose hprod
      simp [hprod]
  · suffices g x = 0 by simp [this]
    contrapose! hx
    exact mem_of_subset (mem_finsuppAntidiag.mp hg).2 <| by simpa using hx
/-
**Nat.Partition.aux_prod_coeff_eq_zero_of_notMem_range** 是 Mathlib 中的一个定理，位于命名空间
 `Nat.Partition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem aux_prod_coeff_eq_zero_of_notMem_range (f : ℕ → ℕ → R) {d : ℕ} {s : Finset ℕ}
    (hs0 : 0 ∉ s) {g : ℕ →₀ ℕ} (hg : g ∈ s.finsuppAntidiag d)
    (hg' : g ∉ Set.range (toFinsuppAntidiag (n := d))) :
    ∏ i ∈ s, (coeff (g i)) (1 + ∑' j, f i (j + 1) • X ^ (i * (j + 1)) : R⟦X⟧) = 0 := by
  suffices ∃ i ∈ s, (coeff (g i)) ((1 : R⟦X⟧) + ∑' j, f i (j + 1) • X ^ (i * (j + 1))) = 0 by
    obtain ⟨i, hi, hi'⟩ := this
    apply prod_eq_zero hi hi'
  contrapose! hg' with hprod
  rw [Set.mem_range]
  have hgne0 (i : ℕ) : g i ≠ 0 ↔ i ≠ 0 ∧ i ≤ g i := by
    refine ⟨fun h ↦ ⟨?_, ?_⟩, by grind⟩
    · contrapose hs0 with rfl
      exact mem_of_subset (mem_finsuppAntidiag.mp hg).2 (by simpa using h)
    · exact Nat.le_of_dvd (Nat.pos_of_ne_zero h) <| aux_dvd_of_coeff_ne_zero hs0 hg hprod _
  refine ⟨Nat.Partition.mk (Finsupp.mk g.support (fun i ↦ g i / i) ?_).toMultiset ?_ ?_, ?_⟩
  · simpa using hgne0
  · suffices ∀ i, g i ≠ 0 → i ≠ 0 by simpa [Nat.pos_iff_ne_zero]
    exact fun i h ↦ ((hgne0 i).mp h).1
  · obtain ⟨h1, h2⟩ := mem_finsuppAntidiag.mp hg
    refine Eq.trans ?_ h1
    suffices ∑ x ∈ g.support, g x / x * x = ∑ x ∈ s, g x by simpa [Finsupp.sum]
    apply sum_subset_zero_on_sdiff h2 (by simp)
    exact fun x hx ↦ Nat.div_mul_cancel <| aux_dvd_of_coeff_ne_zero hs0 hg hprod x
  · ext x
    simpa [toFinsuppAntidiag] using Nat.div_mul_cancel <| aux_dvd_of_coeff_ne_zero hs0 hg hprod x
/-
**Nat.Partition.aux_prod_f_eq_prod_coeff** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partitio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem aux_prod_f_eq_prod_coeff (f : ℕ → ℕ → R) {n : ℕ} (p : Partition n) {s : Finset ℕ}
    (hs : Icc 1 n ⊆ s) (hs0 : 0 ∉ s) :
    p.parts.toFinsupp.prod f =
    ∏ i ∈ s, coeff (p.toFinsuppAntidiag i) (1 + ∑' j, f i (j + 1) • X ^ (i * (j + 1))) := by
  simp_rw [Finsupp.prod, Multiset.toFinsupp_support, Multiset.toFinsupp_apply]
  apply prod_subset_one_on_sdiff
  · grind
  · intro x hx
    rw [mem_sdiff, Multiset.mem_toFinset] at hx
    have hx0 : x ≠ 0 := fun h ↦ hs0 (h ▸ hx.1)
    have hsum := (summable_genFun_term' f hx0).map_tsum _
      (WithPiTopology.continuous_constantCoeff R)
    simp [toFinsuppAntidiag, hsum, hx.2, hx0]
  · intro i hi
    rw [Multiset.mem_toFinset] at hi
    have hi0 : i ≠ 0 := (p.parts_pos hi).ne.symm
    rw [map_add, (summable_genFun_term' f hi0).map_tsum _ (WithPiTopology.continuous_coeff _ _)]
    suffices f i (Multiset.count i p.parts) =
        ∑' j, if Multiset.count i p.parts * i = i * (j + 1) then f i (j + 1) else 0 by
      simpa [toFinsuppAntidiag, hi, hi0, coeff_X_pow]
    rw [tsum_eq_single (Multiset.count i p.parts - 1) ?_]
    · rw [mul_comm]
      simp [Nat.sub_add_cancel (Multiset.one_le_count_iff_mem.mpr hi)]
    intro b hb
    suffices Multiset.count i p.parts * i ≠ i * (b + 1) by simp [this]
    rw [mul_comm i, (mul_left_inj' (Nat.ne_zero_of_lt (p.parts_pos hi))).ne]
    grind
/-
**Nat.Partition.hasProd_genFun** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partition`。
形式化陈述：hasProd_genFun (f : Nat -> Nat -> R) : HasProd (fun i => 1 + ∑' j, f (i + 
1) (j + 1) • X ^ ((i + 1) * (j + 1))) (genFun f)
参数：f : Nat -> Nat -> R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasProd.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : CommMonoid α] [ins
t_1 : TopologicalSpace α] (f : β → α) (a : α)   (L : SummationFilter β), HasProd
 f…
· 使用定理 `PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto`：tendsto_iff_coeff_
tendsto [Semiring R] {ι : Type*} (f : ι -> PowerSeries R) (u : Filter ι) (g : Po
werSeries R) : Tendsto f u (nhds g) ↔ fora…
· 使用定理 `tendsto_atTop_of_eventually_const`：tendsto_atTop_of_eventually_const {ι 
: Type*} [Preorder ι] {u : ι -> X} {i₀ : ι} (h : forall i >= i₀, u i = x) : Tend
sto u atTop (𝓝 x)
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `addRightEmbedding_apply`：∀ {G : Type u_1} [inst : Add G] [inst_1 : IsRig
htCancelAdd G] (g h : G), (addRightEmbedding g) h = h + g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.mem_of_subset`：mem_of_subset {s₁ s₂ : Finset α} {a : α} : s₁ subs
eteq s₂ -> a in s₁ -> a in s₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Nat.Partition.coeff_genFun`：coeff_genFun (f : Nat -> Nat -> R) (n : Nat)
 : (genFun f).coeff n = ∑ p : n.Partition, p.parts.toFinsupp.prod f
· 使用定理 `PowerSeries.coeff_prod`：coeff_prod [DecidableEq ι] (f : ι -> PowerSeries
 R) (d : Nat) (s : Finset ι) : coeff d (∏ j in s, f j) = ∑ l in finsuppAntidiag 
s d, ∏ i in …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_of_injOn`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} [ins
t : AddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (e 
: ι → κ),…
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Nat.Partition.toFinsuppAntidiag_injective`：toFinsuppAntidiag_injective (
n : Nat) : Function.Injective (toFinsuppAntidiag (n
· 使用定理 `Finset.finsuppAntidiag_mono`：finsuppAntidiag_mono {s t : Finset ι} (h : 
s subseteq t) (n : μ) : finsuppAntidiag s n subseteq finsuppAntidiag t n
· 使用定理 `Nat.Partition.toFinsuppAntidiag_mem_finsuppAntidiag`：toFinsuppAntidiag_m
em_finsuppAntidiag {n : Nat} (p : Partition n) : p.toFinsuppAntidiag in (Finset.
Icc 1 n).finsuppAntidiag n
· 使用定理 `_private.Mathlib.Combinatorics.Enumerative.Partition.GenFun.0.Nat.Partit
ion.aux_prod_coeff_eq_zero_of_notMem_range`：∀ {R : Type u_1} [inst : CommSemirin
g R] [inst_1 : TopologicalSpace R] [T2Space R] (f : ℕ → ℕ → R) {d : ℕ}   {s : Fi
nset ℕ},   0 ∉ s →     ∀…
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
（共 36 条，此处仅展示前 30 条）
-/
theorem hasProd_genFun (f : ℕ → ℕ → R) :
    HasProd (fun i ↦ 1 + ∑' j, f (i + 1) (j + 1) • X ^ ((i + 1) * (j + 1))) (genFun f) := by
  rw [HasProd, WithPiTopology.tendsto_iff_coeff_tendsto]
  refine fun d ↦ tendsto_atTop_of_eventually_const (fun s (hs : s ≥ range d) ↦ ?_)
  have : ∏ i ∈ s, ((1 : R⟦X⟧) + ∑' j, f (i + 1) (j + 1) • X ^ ((i + 1) * (j + 1)))
      = ∏ i ∈ s.map (addRightEmbedding 1), (1 + ∑' j, f i (j + 1) • X ^ (i * (j + 1))) := by simp
  rw [this]
  have hs : Icc 1 d ⊆ s.map (addRightEmbedding 1) := by
    intro i
    suffices 1 ≤ i → i ≤ d → ∃ a ∈ s, a + 1 = i by simpa
    intro h1 h2
    refine ⟨i - 1, mem_of_subset hs ?_, ?_⟩ <;> grind
  rw [coeff_genFun, coeff_prod]
  refine (sum_of_injOn toFinsuppAntidiag (toFinsuppAntidiag_injective d).injOn ?_ ?_ ?_).symm
  · intro p _
    exact mem_of_subset (finsuppAntidiag_mono hs _) p.toFinsuppAntidiag_mem_finsuppAntidiag
  · exact fun g hg hg' ↦ aux_prod_coeff_eq_zero_of_notMem_range f (by simp) hg (by simpa using hg')
  · exact fun p _ ↦ aux_prod_f_eq_prod_coeff f p hs (by simp)
/-
**Nat.Partition.multipliable_genFun** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partition`。
形式化陈述：multipliable_genFun (f : Nat -> Nat -> R) : Multipliable fun i => (1 : R⟦X
⟧) + ∑' j, f (i + 1) (j + 1) • X ^ ((i + 1) * (j + 1))
参数：f : Nat -> Nat -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.multipliable`：HasProd.multipliable (h : HasProd f a L) : Multipl
iable f L
· 使用定理 `Nat.Partition.hasProd_genFun`：hasProd_genFun (f : Nat -> Nat -> R) : Has
Prod (fun i => 1 + ∑' j, f (i + 1) (j + 1) • X ^ ((i + 1) * (j + 1))) (genFun f)
-/
theorem multipliable_genFun (f : ℕ → ℕ → R) :
    Multipliable fun i ↦ (1 : R⟦X⟧) + ∑' j, f (i + 1) (j + 1) • X ^ ((i + 1) * (j + 1)) :=
  (hasProd_genFun f).multipliable
/-
**Nat.Partition.genFun_eq_tprod** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partition`。
形式化陈述：genFun_eq_tprod (f : Nat -> Nat -> R) : genFun f = ∏' i, (1 + ∑' j, f (i +
 1) (j + 1) • X ^ ((i + 1) * (j + 1)))
参数：f : Nat -> Nat -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `PowerSeries.WithPiTopology.instT2Space`：instT2Space [T2Space R] : T2Spac
e (PowerSeries R)
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `Nat.Partition.hasProd_genFun`：hasProd_genFun (f : Nat -> Nat -> R) : Has
Prod (fun i => 1 + ∑' j, f (i + 1) (j + 1) • X ^ ((i + 1) * (j + 1))) (genFun f)
-/
theorem genFun_eq_tprod (f : ℕ → ℕ → R) :
    genFun f = ∏' i, (1 + ∑' j, f (i + 1) (j + 1) • X ^ ((i + 1) * (j + 1))) :=
  (hasProd_genFun f).tprod_eq.symm

end Nat.Partition

