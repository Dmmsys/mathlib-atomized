/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The logarithm as a limit of powers

This file shows that the logarithm can be expressed as a limit of powers, namely that
`p⁻¹ * (x ^ p - 1)` tends to `log x` as `p` tends to zero for positive `x`.

## Main declarations

* `Real.tendstoLocallyUniformlyOn_rpow_sub_one_log`: `p⁻¹ * (x ^ p - 1)` tends uniformly to
  `log x` on compact subsets of `Ioi 0` as `p` tends to zero
* `tendsto_rpow_sub_one_log`: `p⁻¹ * (x ^ p - 1)`: the analogous statement for pointwise
  convergence.
-/

public section

open scoped Topology
open Real Filter

/-
**Real.norm_inv_mul_rpow_sub_one_sub_log_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Real.norm_inv_mul_rpow_sub_one_sub_log_le {p x : Real} (p_pos : 0 < p) (x_
pos : 0 < x) (hx : ‖p * log x‖ <= 1) : ‖p⁻¹ * (x ^ p - 1) - log x‖ <= p * ‖log x
‖ ^ 2
参数：p_pos : 0 < p；x_pos : 0 < x；hx : ‖p * log x‖ <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Real.exp_mul`：exp_mul (x y : Real) : exp (x * y) = exp x ^ y
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Real.norm_exp_sub_one_sub_id_le`：∀ {x : ℝ}, ‖x‖ ≤ 1 → ‖Real.exp x - 1 - 
x‖ ≤ ‖x‖ ^ 2
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
-/
lemma Real.norm_inv_mul_rpow_sub_one_sub_log_le {p x : ℝ} (p_pos : 0 < p) (x_pos : 0 < x)
    (hx : ‖p * log x‖ ≤ 1) : ‖p⁻¹ * (x ^ p - 1) - log x‖ ≤ p * ‖log x‖ ^ 2 := by
  have pinv_nonneg : 0 ≤ p⁻¹ := by grind [_root_.inv_nonneg]
  calc
    _ = ‖p⁻¹ * ((x ^ p - 1) - p * log x)‖ := by grind
    _ = p⁻¹ * ‖(rexp (p * log x) - 1) - p * log x‖ := by
          simp only [norm_mul, Real.norm_of_nonneg (r := p⁻¹) pinv_nonneg]
          congr
          rw [mul_comm, Real.exp_mul, Real.exp_log (by grind)]
    _ ≤ p⁻¹ * ‖p * log x‖ ^ 2 := by
          gcongr
          refine Real.norm_exp_sub_one_sub_id_le ?_
          simp only [hx]
    _ = p * ‖log x‖ ^ 2 := by
          simp only [norm_mul]
          grind [Real.norm_of_nonneg]

open Set in
/-
**Real.tendstoLocallyUniformlyOn_rpow_sub_one_log** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Real.tendstoLocallyUniformlyOn_rpow_sub_one_log : TendstoLocallyUniformlyO
n (fun (p : Real) (x : Real) => p⁻¹ * (x ^ p - 1)) log (𝓝[>] 0) (Ioi 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendstoLocallyUniformlyOn_iff_forall_isCompact`：tendstoLocallyUniformlyO
n_iff_forall_isCompact [LocallyCompactSpace α] (hs : IsOpen s) : TendstoLocallyU
niformlyOn F f p s ↔ forall K, K sub…
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `isOpen_Ioi`：isOpen_Ioi : IsOpen (Ioi a)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Filter.HasBasis.tendstoUniformlyOn_iff_of_uniformity`：tendstoUniformlyOn
_iff_of_uniformity {F : X -> α -> β} {f : α -> β} {l : Filter X} {s : Set α} {pβ
 : ιβ -> Prop} {sβ : ιβ -> Set (β × β)} (h…
· 使用定理 `Metric.uniformity_basis_dist_le`：uniformity_basis_dist_le : (𝓤 α).HasBas
is ((0 : Real) < ·) fun ε => { p : α × α | dist p.1 p.2 <= ε }
· 使用引理 `Real.sSup_nonneg`：sSup_nonneg (hs : forall x in s, 0 <= x) : 0 <= sSup s
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Right.add_pos_of_nonneg_of_pos`：∀ {α : Type u_1} [inst : AddZeroClass α]
 [inst_1 : Preorder α] [AddRightMono α] {a b : α}, 0 ≤ a → 0 < b → 0 < a + b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
· 使用引理 `nhdsGT_basis`：nhdsGT_basis [NoMaxOrder α] (a : α) : (𝓝[>] a).HasBasis (a
 < ·) (Ioo a)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `eventually_le_nhds`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 :
 LinearOrder α] [ClosedIciTopology α] {a b : α},   a < b → ∀ᶠ (x : α) in nhds a,
 x ≤ b
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
（共 56 条，此处仅展示前 30 条）
-/
lemma Real.tendstoLocallyUniformlyOn_rpow_sub_one_log :
    TendstoLocallyUniformlyOn (fun (p : ℝ) (x : ℝ) => p⁻¹ * (x ^ p - 1)) log (𝓝[>] 0) (Ioi 0) := by
  refine (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_Ioi).mpr ?_
  intro s hs hs'
  rw [Metric.uniformity_basis_dist_le.tendstoUniformlyOn_iff_of_uniformity]
  intro ε hε
  let pbound : ℝ := ε / (sSup ((fun x => ‖log x‖ ^ 2) '' s) + 1)
  have hxs : ∀ x ∈ s, x ≠ 0 := by grind
  have sSup_nonneg : 0 ≤ sSup ((fun x => ‖log x‖ ^ 2) '' s) := by
    refine Real.sSup_nonneg ?_
    grind [← sq_nonneg]
  have sSup_nonneg' : 0 ≤ sSup ((fun x => ‖log x‖) '' s) := by
    refine Real.sSup_nonneg ?_
    grind [← sq_nonneg]
  have pbound_pos : 0 < pbound := by positivity
  have h₁ : ∀ᶠ p : ℝ in 𝓝[>] 0, 0 < p ∧ p < pbound := nhdsGT_basis 0 |>.mem_of_mem pbound_pos
  have h₂ : ∀ᶠ p : ℝ in 𝓝[>] 0, p ≤ 1 / (sSup ((fun x => ‖log x‖) '' s) + 1) :=
    Eventually.filter_mono nhdsWithin_le_nhds <| eventually_le_nhds (by positivity)
  have hcont : ContinuousOn (fun x => ‖log x‖ ^ 2) s := by fun_prop
  have hcont' : ContinuousOn (fun x => ‖log x‖) s := by fun_prop
  filter_upwards [h₁, h₂] with p ⟨hp₁,hp₂⟩ hp₃
  intro x hx
  have hx' : ‖p * log x‖ ≤ 1 := calc
    _ = p * ‖log x‖ := by grind [norm_mul, Real.norm_of_nonneg]
    _ ≤ 1 / (sSup ((fun y => ‖log y‖) '' s) + 1) * ‖log x‖ := by gcongr
    _ ≤ 1 / (‖log x‖ + 1) * ‖log x‖ := by
        gcongr
        refine le_csSup ?_ (by grind)
        grind [IsCompact.bddAbove, ← IsCompact.image_of_continuousOn]
    _ = ‖log x‖ / (‖log x‖ + 1) := by grind
    _ ≤ 1 := by rw [div_le_one₀] <;> grind [norm_nonneg]
  have pinv_nonneg : 0 ≤ p⁻¹ := by grind [_root_.inv_nonneg]
  rw [dist_eq_norm']
  calc
    _ ≤ p * ‖log x‖ ^ 2 := Real.norm_inv_mul_rpow_sub_one_sub_log_le hp₁ (hs hx) hx'
    _ ≤ p * sSup ((fun x => ‖log x‖ ^ 2) '' s) := by
          gcongr
          refine le_csSup ?_ (by grind)
          grind [IsCompact.bddAbove, ← IsCompact.image_of_continuousOn]
    _ ≤ pbound * (sSup ((fun x => ‖log x‖ ^ 2) '' s) + 1) := by gcongr; grind
    _ = ε := by grind
/-
**tendsto_rpow_sub_one_log** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_rpow_sub_one_log {x : Real} (hx : 0 < x) : Tendsto (fun p => p⁻¹ *
 (x ^ p - 1)) (𝓝[>] 0) (𝓝 (log x))
参数：hx : 0 < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TendstoLocallyUniformlyOn.tendsto_at`：TendstoLocallyUniformlyOn.tendsto_
at (hf : TendstoLocallyUniformlyOn F f p s) {a : α} (ha : a in s) : Tendsto (fun
 i => F i a) p (𝓝 (f a))
· 使用引理 `Real.tendstoLocallyUniformlyOn_rpow_sub_one_log`：Real.tendstoLocallyUnif
ormlyOn_rpow_sub_one_log : TendstoLocallyUniformlyOn (fun (p : Real) (x : Real) 
=> p⁻¹ * (x ^ p - 1)) log (𝓝[>] 0) (I…
-/
lemma tendsto_rpow_sub_one_log {x : ℝ} (hx : 0 < x) :
    Tendsto (fun p => p⁻¹ * (x ^ p - 1)) (𝓝[>] 0) (𝓝 (log x)) :=
  TendstoLocallyUniformlyOn.tendsto_at
    tendstoLocallyUniformlyOn_rpow_sub_one_log (by grind)
