/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Results on discretized exponentials

We state several auxiliary results pertaining to sequences of the form `⌊c^n⌋₊`.

* `tendsto_div_of_monotone_of_tendsto_div_floor_pow`: If a monotone sequence `u` is such that
  `u ⌊c^n⌋₊ / ⌊c^n⌋₊` converges to a limit `l` for all `c > 1`, then `u n / n` tends to `l`.
* `sum_div_nat_floor_pow_sq_le_div_sq`: The sum of `1/⌊c^i⌋₊^2` above a threshold `j` is comparable
  to `1/j^2`, up to a multiplicative constant.
-/

public section

open Filter Finset

open Topology

/-- If a monotone sequence `u` is such that `u n / n` tends to a limit `l` along subsequences with
exponential growth rate arbitrarily close to `1`, then `u n / n` tends to `l`. -/
/-
**tendsto_div_of_monotone_of_exists_subseq_tendsto_div** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：tendsto_div_of_monotone_of_exists_subseq_tendsto_div (u : Nat -> Real) (l 
: Real) (hmono : Monotone u) (hlim : forall a : Real, 1 < a -> exists c : Nat ->
 Nat, (forallᶠ n in atTop, (c (n + 1) : Real) <= a * c n) ∧ Tendsto c atTop atTo
p ∧ Tendsto (fun n => u (c n) / c n) atTop (𝓝 l)) : Tendsto (fun n => u n / n) a
tTop (𝓝 l)
参数：u : Nat -> Real；l : Real；hmono : Monotone u；hlim : forall a : Real, 1 < a -> 
exists c : Nat -> Nat, (forallᶠ n in atTop, (c (n + 1) : Real) <= a * c n) ∧ Ten
dsto c atTop atTop ∧ Tendsto (fun n => u (c n) / c n) atTop (𝓝 l)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `one_lt_two`：one_lt_two [AddLeftStrictMono α] : (1 : α) < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Filter.Tendsto.div_atTop`：Filter.Tendsto.div_atTop {a : 𝕜} (h : Tendsto 
f l (𝓝 a)) (hg : Tendsto g l atTop) : Tendsto (fun x => f x / g x) l (𝓝 0)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_natCast_atTop_iff`：tendsto_natCast_atTop_iff [Semiring R] [Parti
alOrder R] [IsStrictOrderedRing R] [Archimedean R] {f : α -> Nat} {l : Filter α}
 : Tendsto (fun…
· 使用定理 `le_of_tendsto_of_tendsto'`：le_of_tendsto_of_tendsto' {f g : β -> α} {b :
 Filter β} {a₁ a₂ : α} [hb : NeBot b] (hf : Tendsto f b (𝓝 a₁)) (hg : Tendsto g 
b (𝓝 a₂)) (h : …
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `div_le_div_of_nonneg_right`：div_le_div_of_nonneg_right (hab : a <= b) (h
c : 0 <= c) : a / c <= b / c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `lt_add_iff_pos_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 :
 LT α] [AddLeftStrictMono α] [AddLeftReflectLT α] (a : α) {b : α},   a < a + b ↔
 0 < b
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Ioi_mem_atTop`：Ioi_mem_atTop [Preorder α] [NoTopOrder α] (x : α) 
: Ioi x in (atTop : Filter α)
（共 206 条，此处仅展示前 30 条）

--- 原说明 ---
If a monotone sequence `u` is such that `u n / n` tends to a limit `l` along sub
sequences with
exponential growth rate arbitrarily close to `1`, then `u n / n` tends to `l`.
-/
theorem tendsto_div_of_monotone_of_exists_subseq_tendsto_div (u : ℕ → ℝ) (l : ℝ)
    (hmono : Monotone u)
    (hlim : ∀ a : ℝ, 1 < a → ∃ c : ℕ → ℕ, (∀ᶠ n in atTop, (c (n + 1) : ℝ) ≤ a * c n) ∧
      Tendsto c atTop atTop ∧ Tendsto (fun n => u (c n) / c n) atTop (𝓝 l)) :
    Tendsto (fun n => u n / n) atTop (𝓝 l) := by
  /- To check the result up to some `ε > 0`, we use a sequence `c` for which the ratio
    `c (N+1) / c N` is bounded by `1 + ε`. Sandwiching a given `n` between two consecutive values of
    `c`, say `c N` and `c (N+1)`, one can then bound `u n / n` from above by `u (c N) / c (N - 1)`
    and from below by `u (c (N - 1)) / c N` (using that `u` is monotone), which are both comparable
    to the limit `l` up to `1 + ε`.
    We give a version of this proof by clearing out denominators first, to avoid discussing the sign
    of different quantities. -/
  have lnonneg : 0 ≤ l := by
    rcases hlim 2 one_lt_two with ⟨c, _, ctop, clim⟩
    have : Tendsto (fun n => u 0 / c n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_iff.2 ctop)
    apply le_of_tendsto_of_tendsto' this clim fun n => ?_
    gcongr
    exact hmono zero_le
  have A : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, u n - n * l ≤ ε * (1 + ε + l) * n := by
    intro ε εpos
    rcases hlim (1 + ε) ((lt_add_iff_pos_right _).2 εpos) with ⟨c, cgrowth, ctop, clim⟩
    have L : ∀ᶠ n in atTop, u (c n) - c n * l ≤ ε * c n := by
      rw [← tendsto_sub_nhds_zero_iff, ← Asymptotics.isLittleO_one_iff ℝ,
        Asymptotics.isLittleO_iff] at clim
      filter_upwards [clim εpos, ctop (Ioi_mem_atTop 0)] with n hn cnpos'
      have cnpos : 0 < c n := cnpos'
      calc
        u (c n) - c n * l = (u (c n) / c n - l) * c n := by field
        _ ≤ ε * c n := by
          gcongr
          refine (le_abs_self _).trans ?_
          simpa using hn
    obtain ⟨a, ha⟩ :
      ∃ a : ℕ, ∀ b : ℕ, a ≤ b → (c (b + 1) : ℝ) ≤ (1 + ε) * c b ∧ u (c b) - c b * l ≤ ε * c b :=
      eventually_atTop.1 (cgrowth.and L)
    let M := ((Finset.range (a + 1)).image fun i => c i).max' (by simp)
    filter_upwards [Ici_mem_atTop M] with n hn
    have exN : ∃ N, n < c N := by
      rcases (tendsto_atTop.1 ctop (n + 1)).exists with ⟨N, hN⟩
      exact ⟨N, by lia⟩
    let N := Nat.find exN
    have ncN : n < c N := Nat.find_spec exN
    have aN : a + 1 ≤ N := by
      by_contra! h
      have cNM : c N ≤ M := by
        apply le_max'
        apply mem_image_of_mem
        exact mem_range.2 h
      exact lt_irrefl _ ((cNM.trans hn).trans_lt ncN)
    have Npos : 0 < N := lt_of_lt_of_le Nat.succ_pos' aN
    have cNn : c (N - 1) ≤ n := by
      have : N - 1 < N := Nat.pred_lt Npos.ne'
      simpa only [not_lt] using Nat.find_min exN this
    have IcN : (c N : ℝ) ≤ (1 + ε) * c (N - 1) := by
      have A : a ≤ N - 1 := (Nat.le_sub_one_iff_lt Npos).mpr aN
      have B : N - 1 + 1 = N := Nat.succ_pred_eq_of_pos Npos
      have := (ha _ A).1
      rwa [B] at this
    calc
      u n - n * l ≤ u (c N) - c (N - 1) * l := by gcongr; exact hmono ncN.le
      _ = u (c N) - c N * l + (c N - c (N - 1)) * l := by ring
      _ ≤ ε * c N + ε * c (N - 1) * l := by
        gcongr
        · exact (ha N (a.le_succ.trans aN)).2
        · linarith only [IcN]
      _ ≤ ε * ((1 + ε) * c (N - 1)) + ε * c (N - 1) * l := by gcongr
      _ = ε * (1 + ε + l) * c (N - 1) := by ring
      _ ≤ ε * (1 + ε + l) * n := by gcongr
  have B : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (n : ℝ) * l - u n ≤ ε * (1 + l) * n := by
    intro ε εpos
    rcases hlim (1 + ε) ((lt_add_iff_pos_right _).2 εpos) with ⟨c, cgrowth, ctop, clim⟩
    have L : ∀ᶠ n : ℕ in atTop, (c n : ℝ) * l - u (c n) ≤ ε * c n := by
      rw [← tendsto_sub_nhds_zero_iff, ← Asymptotics.isLittleO_one_iff ℝ,
        Asymptotics.isLittleO_iff] at clim
      filter_upwards [clim εpos, ctop (Ioi_mem_atTop 0)] with n hn cnpos'
      have cnpos : 0 < c n := cnpos'
      calc
        (c n : ℝ) * l - u (c n) = -(u (c n) / c n - l) * c n := by field
        _ ≤ ε * c n := by
          gcongr
          refine le_trans (neg_le_abs _) ?_
          simpa using hn
    obtain ⟨a, ha⟩ :
      ∃ a : ℕ,
        ∀ b : ℕ, a ≤ b → (c (b + 1) : ℝ) ≤ (1 + ε) * c b ∧ (c b : ℝ) * l - u (c b) ≤ ε * c b :=
      eventually_atTop.1 (cgrowth.and L)
    let M := ((Finset.range (a + 1)).image fun i => c i).max' (by simp)
    filter_upwards [Ici_mem_atTop M] with n hn
    have exN : ∃ N, n < c N := by
      rcases (tendsto_atTop.1 ctop (n + 1)).exists with ⟨N, hN⟩
      exact ⟨N, by lia⟩
    let N := Nat.find exN
    have ncN : n < c N := Nat.find_spec exN
    have aN : a + 1 ≤ N := by
      by_contra! h
      have cNM : c N ≤ M := by
        apply le_max'
        apply mem_image_of_mem
        exact mem_range.2 h
      exact lt_irrefl _ ((cNM.trans hn).trans_lt ncN)
    have Npos : 0 < N := lt_of_lt_of_le Nat.succ_pos' aN
    have aN' : a ≤ N - 1 := (Nat.le_sub_one_iff_lt Npos).mpr aN
    have cNn : c (N - 1) ≤ n := by
      have : N - 1 < N := Nat.pred_lt Npos.ne'
      simpa only [not_lt] using Nat.find_min exN this
    calc
      (n : ℝ) * l - u n ≤ c N * l - u (c (N - 1)) := by
        gcongr
        exact hmono cNn
      _ ≤ (1 + ε) * c (N - 1) * l - u (c (N - 1)) := by
        gcongr
        have B : N - 1 + 1 = N := Nat.succ_pred_eq_of_pos Npos
        simpa [B] using (ha _ aN').1
      _ = c (N - 1) * l - u (c (N - 1)) + ε * c (N - 1) * l := by ring
      _ ≤ ε * c (N - 1) + ε * c (N - 1) * l := add_le_add (ha _ aN').2 le_rfl
      _ = ε * (1 + l) * c (N - 1) := by ring
      _ ≤ ε * (1 + l) * n := by gcongr
  refine tendsto_order.2 ⟨fun d hd => ?_, fun d hd => ?_⟩
  · obtain ⟨ε, hε, εpos⟩ : ∃ ε : ℝ, d + ε * (1 + l) < l ∧ 0 < ε := by
      have L : Tendsto (fun ε => d + ε * (1 + l)) (𝓝[>] 0) (𝓝 (d + 0 * (1 + l))) := by
        apply Tendsto.mono_left _ nhdsWithin_le_nhds
        exact tendsto_const_nhds.add (tendsto_id.mul tendsto_const_nhds)
      simp only [zero_mul, add_zero] at L
      exact (((tendsto_order.1 L).2 l hd).and self_mem_nhdsWithin).exists
    filter_upwards [B ε εpos, Ioi_mem_atTop 0] with n hn npos
    simp_rw [div_eq_inv_mul]
    calc
      d < (n : ℝ)⁻¹ * n * (l - ε * (1 + l)) := by
        rw [inv_mul_cancel₀, one_mul]
        · linarith only [hε]
        · exact Nat.cast_ne_zero.2 (ne_of_gt npos)
      _ = (n : ℝ)⁻¹ * (n * l - ε * (1 + l) * n) := by ring
      _ ≤ (n : ℝ)⁻¹ * u n := by gcongr; linarith only [hn]
  · obtain ⟨ε, hε, εpos⟩ : ∃ ε : ℝ, l + ε * (1 + ε + l) < d ∧ 0 < ε := by
      have L : Tendsto (fun ε => l + ε * (1 + ε + l)) (𝓝[>] 0) (𝓝 (l + 0 * (1 + 0 + l))) := by
        apply Tendsto.mono_left _ nhdsWithin_le_nhds
        exact
          tendsto_const_nhds.add
            (tendsto_id.mul ((tendsto_const_nhds.add tendsto_id).add tendsto_const_nhds))
      simp only [zero_mul, add_zero] at L
      exact (((tendsto_order.1 L).2 d hd).and self_mem_nhdsWithin).exists
    filter_upwards [A ε εpos, Ioi_mem_atTop 0] with n hn (npos : 0 < n)
    calc
      u n / n ≤ (n * l + ε * (1 + ε + l) * n) / n := by gcongr; linarith only [hn]
      _ = (l + ε * (1 + ε + l)) := by field
      _ < d := hε

/-- If a monotone sequence `u` is such that `u ⌊c^n⌋₊ / ⌊c^n⌋₊` converges to a limit `l` for all
`c > 1`, then `u n / n` tends to `l`. It is even enough to have the assumption for a sequence of
`c`s converging to `1`. -/
/-
**tendsto_div_of_monotone_of_tendsto_div_floor_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_div_of_monotone_of_tendsto_div_floor_pow (u : Nat -> Real) (l : Re
al) (hmono : Monotone u) (c : Nat -> Real) (cone : forall k, 1 < c k) (clim : Te
ndsto c atTop (𝓝 1)) (hc : forall k, Tendsto (fun n : Nat => u ⌊c k ^ n⌋₊ / ⌊c k
 ^ n⌋₊) atTop (𝓝 l)) : Tendsto (fun n => u n / n) atTop (𝓝 l)
参数：u : Nat -> Real；l : Real；hmono : Monotone u；c : Nat -> Real；cone : forall k, 
1 < c k；clim : Tendsto c atTop (𝓝 1)；hc : forall k, Tendsto (fun n : Nat => u ⌊c
 k ^ n⌋₊ / ⌊c k ^ n⌋₊) atTop (𝓝 l)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_div_of_monotone_of_exists_subseq_tendsto_div`：tendsto_div_of_mon
otone_of_exists_subseq_tendsto_div (u : Nat -> Real) (l : Real) (hmono : Monoton
e u) (hlim : forall a : Real, 1 < a -> exi…
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tendsto_order`：tendsto_order [OrderTopology α] {f : β -> α} {a : α} {x :
 Filter β} : Tendsto f x (𝓝 a) ↔ (forall a' < a, forallᶠ b in x, a' < f b) ∧ for
all…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `one_le_pow₀`：one_le_pow₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 <= 
a) {n : Nat} : 1 <= a ^ n
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Filter.Tendsto.div`：Filter.Tendsto.div {l : Filter α} {a b : G₀} (hf : T
endsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) (hy : b != 0) : Tendsto (f / g) l (𝓝 
(a / b))
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `instIsTopologicalDivisionRingReal`：IsTopologicalDivisionRing ℝ
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Filter.Tendsto.mul`：Filter.Tendsto.mul {α : Type*} {f g : α -> M} {x : F
ilter α} {a b : M} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (
fun x =>…
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_nat_floor_div_atTop`：tendsto_nat_floor_div_atTop : Tendsto (fun 
x => (⌊x⌋₊ : R) / x) atTop (𝓝 1)
· 使用定理 `tendsto_pow_atTop_atTop_of_one_lt`：tendsto_pow_atTop_atTop_of_one_lt [Se
miring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α] [Archimedean
 α] {r : α} (h : 1 < r)…
（共 107 条，此处仅展示前 30 条）

--- 原说明 ---
If a monotone sequence `u` is such that `u ⌊c^n⌋₊ / ⌊c^n⌋₊` converges to a limit
 `l` for all
`c > 1`, then `u n / n` tends to `l`. It is even enough to have the assumption f
or a sequence of
`c`s converging to `1`.
-/
theorem tendsto_div_of_monotone_of_tendsto_div_floor_pow (u : ℕ → ℝ) (l : ℝ) (hmono : Monotone u)
    (c : ℕ → ℝ) (cone : ∀ k, 1 < c k) (clim : Tendsto c atTop (𝓝 1))
    (hc : ∀ k, Tendsto (fun n : ℕ => u ⌊c k ^ n⌋₊ / ⌊c k ^ n⌋₊) atTop (𝓝 l)) :
    Tendsto (fun n => u n / n) atTop (𝓝 l) := by
  apply tendsto_div_of_monotone_of_exists_subseq_tendsto_div u l hmono
  intro a ha
  obtain ⟨k, hk⟩ : ∃ k, c k < a := ((tendsto_order.1 clim).2 a ha).exists
  refine
    ⟨fun n => ⌊c k ^ n⌋₊, ?_,
      (tendsto_nat_floor_atTop (α := ℝ)).comp (tendsto_pow_atTop_atTop_of_one_lt (cone k)), hc k⟩
  have H : ∀ n : ℕ, (0 : ℝ) < ⌊c k ^ n⌋₊ := by
    intro n
    refine zero_lt_one.trans_le ?_
    simp only [Nat.one_le_cast, Nat.one_le_floor_iff, one_le_pow₀ (cone k).le]
  have A :
    Tendsto (fun n : ℕ => (⌊c k ^ (n + 1)⌋₊ : ℝ) / c k ^ (n + 1) * c k / (⌊c k ^ n⌋₊ / c k ^ n))
      atTop (𝓝 (1 * c k / 1)) := by
    refine Tendsto.div (Tendsto.mul ?_ tendsto_const_nhds) ?_ one_ne_zero
    · refine tendsto_nat_floor_div_atTop.comp ?_
      exact (tendsto_pow_atTop_atTop_of_one_lt (cone k)).comp (tendsto_add_atTop_nat 1)
    · refine tendsto_nat_floor_div_atTop.comp ?_
      exact tendsto_pow_atTop_atTop_of_one_lt (cone k)
  have B : Tendsto (fun n : ℕ => (⌊c k ^ (n + 1)⌋₊ : ℝ) / ⌊c k ^ n⌋₊) atTop (𝓝 (c k)) := by
    simp only [one_mul, div_one] at A
    convert! A using 1
    ext1 n
    field [(zero_lt_one.trans (cone k)).ne']
  filter_upwards [(tendsto_order.1 B).2 a hk] with n hn
  exact (div_le_iff₀ (H n)).1 hn.le

/-- The sum of `1/(c^i)^2` above a threshold `j` is comparable to `1/j^2`, up to a multiplicative
constant. -/
/-
**sum_div_pow_sq_le_div_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sum_div_pow_sq_le_div_sq (N : Nat) {j : Real} (hj : 0 < j) {c : Real} (hc 
: 1 < c) : (∑ i in range N with j < c ^ i, (1 : Real) / (c ^ i) ^ 2) <= c ^ 3 * 
(c - 1)⁻¹ / j ^ 2
参数：N : Nat；hj : 0 < j；hc : 1 < c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `sq_pos_of_pos`：sq_pos_of_pos [PosMulStrictMono M₀] (ha : 0 < a) : 0 < a 
^ 2
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用引理 `div_le_div_iff₀`：div_le_div_iff₀ (hb : 0 < b) (hd : 0 < d) : a / b <= c 
/ d ↔ a * d <= c * b
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
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
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `pow_lt_one₀`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preo
rder M₀] {a : M₀} [PosMulMono M₀],   0 ≤ a → a < 1 → ∀ {n : ℕ}, n ≠ 0 → a ^ n < 
1
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `inv_nonneg`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Partia
lOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 ≤ a⁻¹ ↔ 0 ≤ a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `inv_lt_one_of_one_lt₀`：inv_lt_one_of_one_lt₀ (ha : 1 < a) : a⁻¹ < 1
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
（共 156 条，此处仅展示前 30 条）

--- 原说明 ---
The sum of `1/(c^i)^2` above a threshold `j` is comparable to `1/j^2`, up to a m
ultiplicative
constant.
-/
theorem sum_div_pow_sq_le_div_sq (N : ℕ) {j : ℝ} (hj : 0 < j) {c : ℝ} (hc : 1 < c) :
    (∑ i ∈ range N with j < c ^ i, (1 : ℝ) / (c ^ i) ^ 2) ≤ c ^ 3 * (c - 1)⁻¹ / j ^ 2 := by
  have cpos : 0 < c := zero_lt_one.trans hc
  have A : (0 : ℝ) < c⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.2 cpos)
  have B : c ^ 2 * ((1 : ℝ) - c⁻¹ ^ 2)⁻¹ ≤ c ^ 3 * (c - 1)⁻¹ := by
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ _ (sub_pos.2 hc)]
    swap
    · exact sub_pos.2 (pow_lt_one₀ (inv_nonneg.2 cpos.le) (inv_lt_one_of_one_lt₀ hc) two_ne_zero)
    have : c ^ 3 = c ^ 2 * c := by ring
    simp only [mul_sub, this, mul_one, inv_pow, sub_le_sub_iff_left]
    rw [mul_assoc, mul_comm c, ← mul_assoc, mul_inv_cancel₀ (sq_pos_of_pos cpos).ne', one_mul]
    simpa using pow_right_mono₀ hc.le one_le_two
  have C : c⁻¹ ^ 2 < 1 := pow_lt_one₀ (inv_nonneg.2 cpos.le) (inv_lt_one_of_one_lt₀ hc) two_ne_zero
  calc
    (∑ i ∈ range N with j < c ^ i, (1 : ℝ) / (c ^ i) ^ 2) ≤
        ∑ i ∈ Ico ⌊Real.log j / Real.log c⌋₊ N, (1 : ℝ) / (c ^ i) ^ 2 := by
      gcongr
      intro i hi
      simp only [mem_filter, mem_range] at hi
      simp only [hi.1, mem_Ico, and_true]
      apply Nat.floor_le_of_le
      apply le_of_lt
      rw [div_lt_iff₀ (Real.log_pos hc), ← Real.log_pow]
      exact Real.log_lt_log hj hi.2
    _ = ∑ i ∈ Ico ⌊Real.log j / Real.log c⌋₊ N, (c⁻¹ ^ 2) ^ i := by
      simp [← pow_mul, mul_comm]
    _ ≤ (c⁻¹ ^ 2) ^ ⌊Real.log j / Real.log c⌋₊ / ((1 : ℝ) - c⁻¹ ^ 2) :=
      geom_sum_Ico_le_of_lt_one (sq_nonneg _) C
    _ ≤ (c⁻¹ ^ 2) ^ (Real.log j / Real.log c - 1) / ((1 : ℝ) - c⁻¹ ^ 2) := by
      gcongr
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge A C.le (Nat.sub_one_lt_floor _).le
    _ = c ^ 2 * ((1 : ℝ) - c⁻¹ ^ 2)⁻¹ / j ^ 2 := by
      have I : (c⁻¹ ^ 2) ^ (Real.log j / Real.log c) = (1 : ℝ) / j ^ 2 := by
        apply Real.log_injOn_pos (Real.rpow_pos_of_pos A _)
        · rw [Set.mem_Ioi]; positivity
        rw [Real.log_rpow A]
        simp only [one_div, Real.log_inv, Real.log_pow, mul_neg, neg_inj]
        field [(Real.log_pos hc).ne']
      rw [Real.rpow_sub A, I]
      simp
      ring
    _ ≤ c ^ 3 * (c - 1)⁻¹ / j ^ 2 := by gcongr
/-
**mul_pow_le_nat_floor_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_pow_le_nat_floor_pow {c : Real} (hc : 1 < c) (i : Nat) : (1 - c⁻¹) * c
 ^ i <= ⌊c ^ i⌋₊
参数：hc : 1 < c；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Nat.floor_one`：floor_one : ⌊(1 : R)⌋₊ = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b : R}, a = a' → a'⁻¹ = b → a⁻¹ = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_single`：∀ {R : Type u_2} [inst : Semifiel
d R] {a b : R}, a⁻¹ = b → (a + 0)⁻¹ = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_mul`：∀ {R : Type u_2} [inst : Semifield R
] {a₁ : R} {a₂ : ℕ} {a₃ b₁ b₃ c : R},   a₁⁻¹ = b₁ → a₃⁻¹ = b₃ → b₃ * (b₁ ^ a₂ * 
Nat.rawCast 1) = c → (a₁…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isNat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n 1 → Mathlib.Meta.NormNum
.IsNat a n
（共 64 条，此处仅展示前 30 条）
-/
theorem mul_pow_le_nat_floor_pow {c : ℝ} (hc : 1 < c) (i : ℕ) : (1 - c⁻¹) * c ^ i ≤ ⌊c ^ i⌋₊ := by
  have cpos : 0 < c := zero_lt_one.trans hc
  rcases eq_or_ne i 0 with (rfl | hi)
  · simp only [pow_zero, Nat.floor_one, Nat.cast_one, mul_one, sub_le_self_iff, inv_nonneg, cpos.le]
  calc
    (1 - c⁻¹) * c ^ i = c ^ i - c ^ i * c⁻¹ := by ring
    _ ≤ c ^ i - 1 := by
      gcongr
      simpa only [← div_eq_mul_inv, one_le_div cpos, pow_one] using le_self_pow₀ hc.le hi
    _ ≤ ⌊c ^ i⌋₊ := (Nat.sub_one_lt_floor _).le

/-- The sum of `1/⌊c^i⌋₊^2` above a threshold `j` is comparable to `1/j^2`, up to a multiplicative
constant. -/
/-
**sum_div_nat_floor_pow_sq_le_div_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sum_div_nat_floor_pow_sq_le_div_sq (N : Nat) {j : Real} (hj : 0 < j) {c : 
Real} (hc : 1 < c) : (∑ i in range N with j < ⌊c ^ i⌋₊, (1 : Real) / (⌊c ^ i⌋₊ :
 Real) ^ 2) <= c ^ 5 * (c - 1)⁻¹ ^ 3 / j ^ 2
参数：N : Nat；hj : 0 < j；hc : 1 < c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
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
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `inv_lt_one_of_one_lt₀`：inv_lt_one_of_one_lt₀ (ha : 1 < a) : a⁻¹ < 1
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Finset.sum_le_sum_of_subset_of_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [
inst : AddCommMonoid N] [inst_1 : Preorder N] {f : ι → N} {s t : Finset ι}   [Ad
dLeftMono N], s ⊆ t → (∀ i …
· 使用定理 `Finset.monotone_filter_right`：∀ {α : Type u_1} (s : Finset α) ⦃p q : α →
 Prop⦄ [inst : DecidablePred p] [inst_1 : DecidablePred q],   (∀ a ∈ s, p a → q 
a) → Finset.filter…
· 使用定理 `lt_imp_lt_of_le_of_le`：lt_imp_lt_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a < b -> c < d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Nat.floor_le`：floor_le (ha : 0 <= a) : (⌊a⌋₊ : R) <= a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_pos_of_nonneg`：div_nonneg_of_pos_o
f_nonneg [PosMulReflectLT α] (ha : 0 < a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `Even.pow_nonneg`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : LinearOr
der R] [IsOrderedRing R] [ExistsAddOfLE R] {n : ℕ},   Even n → ∀ (a : R), 0 ≤ a 
^ n
（共 135 条，此处仅展示前 30 条）

--- 原说明 ---
The sum of `1/⌊c^i⌋₊^2` above a threshold `j` is comparable to `1/j^2`, up to a 
multiplicative
constant.
-/
theorem sum_div_nat_floor_pow_sq_le_div_sq (N : ℕ) {j : ℝ} (hj : 0 < j) {c : ℝ} (hc : 1 < c) :
    (∑ i ∈ range N with j < ⌊c ^ i⌋₊, (1 : ℝ) / (⌊c ^ i⌋₊ : ℝ) ^ 2) ≤
      c ^ 5 * (c - 1)⁻¹ ^ 3 / j ^ 2 := by
  have cpos : 0 < c := zero_lt_one.trans hc
  have A : 0 < 1 - c⁻¹ := sub_pos.2 (inv_lt_one_of_one_lt₀ hc)
  calc
    (∑ i ∈ range N with j < ⌊c ^ i⌋₊, (1 : ℝ) / (⌊c ^ i⌋₊ : ℝ) ^ 2) ≤
        ∑ i ∈ range N with j < c ^ i, (1 : ℝ) / (⌊c ^ i⌋₊ : ℝ) ^ 2 := by
      gcongr with k hk; exact Nat.floor_le (by positivity)
    _ ≤ ∑ i ∈ range N with j < c ^ i, (1 - c⁻¹)⁻¹ ^ 2 * ((1 : ℝ) / (c ^ i) ^ 2) := by
      gcongr with i
      rw [mul_div_assoc', mul_one, div_le_div_iff₀]; rotate_left
      · apply sq_pos_of_pos
        refine zero_lt_one.trans_le ?_
        simp only [Nat.le_floor, one_le_pow₀, hc.le, Nat.one_le_cast, Nat.cast_one]
      · exact sq_pos_of_pos (pow_pos cpos _)
      rw [one_mul, ← mul_pow]
      gcongr
      rw [← div_eq_inv_mul, le_div_iff₀ A, mul_comm]
      exact mul_pow_le_nat_floor_pow hc i
    _ ≤ (1 - c⁻¹)⁻¹ ^ 2 * (c ^ 3 * (c - 1)⁻¹) / j ^ 2 := by
      rw [← mul_sum, ← mul_div_assoc']
      gcongr
      exact sum_div_pow_sq_le_div_sq N hj hc
    _ = c ^ 5 * (c - 1)⁻¹ ^ 3 / j ^ 2 := by
      congr 1
      field
