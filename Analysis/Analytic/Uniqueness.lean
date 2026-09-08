/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Analytic.ChangeOrigin

/-!
# Uniqueness principle for analytic functions

We show that two analytic functions which coincide around a point coincide on whole connected sets,
in `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`.
-/

public section


variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

open Set

open scoped Topology ENNReal NNReal

/-!
### Uniqueness of power series
If a function `f : E → F` has two representations as power series at a point `x : E`, corresponding
to formal multilinear series `p₁` and `p₂`, then these representations agree term-by-term. That is,
for any `n : ℕ` and `y : E`, `p₁ n (fun i ↦ y) = p₂ n (fun i ↦ y)`. In the one-dimensional case,
when `f : 𝕜 → E`, the continuous multilinear maps `p₁ n` and `p₂ n` are given by
`ContinuousMultilinearMap.mkPiRing`, and hence are determined completely by the value of
`p₁ n (fun i ↦ 1)`, so `p₁ = p₂`. Consequently, the radius of convergence for one series can be
transferred to the other.
-/

section Uniqueness

open ContinuousMultilinearMap

/-
**Asymptotics.IsBigO.continuousMultilinearMap_apply_eq_zero** 是 Mathlib 中的一个定理，位
于命名空间 ``。
形式化陈述：Asymptotics.IsBigO.continuousMultilinearMap_apply_eq_zero {n : Nat} {p : E
 [×n]->L[𝕜] F} (h : (fun y => p fun _ => y) =O[𝓝 0] fun y => ‖y‖ ^ (n + 1)) (y :
 E) : (p fun _ => y) = 0
参数：h : (fun y => p fun _ => y) =O[𝓝 0] fun y => ‖y‖ ^ (n + 1)；y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.exists_pos`：∀ {α : Type u_1} {E : Type u_3} {F' : Typ
e u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {f : α → E}   {g' : 
α → F'} {l : Filter…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `eventually_nhds_iff`：eventually_nhds_iff {p : X -> Prop} : (forallᶠ y in
 𝓝 x, p y) ↔ exists t : Set X, (forall y in t, p y) ∧ IsOpen t ∧ x in t
· 使用定理 `Asymptotics.isBigOWith_iff`：isBigOWith_iff : IsBigOWith c l f g ↔ forall
ᶠ x in l, ‖f x‖ <= c * ‖g x‖
· 使用定理 `Metric.isOpen_iff`：isOpen_iff : IsOpen s ↔ forall x in s, exists ε > 0, 
ball x ε subseteq s
· 使用定理 `norm_eq_zero`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a‖ = 
0 ↔ a = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMultilinearMap.fin0_apply_norm`：ContinuousMultilinearMap.fin0_
apply_norm (f : G [×0]->L[𝕜] G') {x : Fin 0 -> G} : ‖f x‖ = ‖f‖
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Metric.mem_ball_self`：mem_ball_self (h : 0 < ε) : x in ball x ε
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousMultilinearMap.map_zero`：map_zero [Nonempty ι] : f 0 = 0
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_of_forall_pos_le_add`：∀ {α : Type u} [inst : LinearOrder α] [DenselyO
rdered α] [inst_2 : AddMonoid α] [ExistsAddOfLE α] [AddLeftReflectLT α]   {a b :
 α}, (∀ (ε : …
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
（共 98 条，此处仅展示前 30 条）
-/
theorem Asymptotics.IsBigO.continuousMultilinearMap_apply_eq_zero {n : ℕ} {p : E [×n]→L[𝕜] F}
    (h : (fun y => p fun _ => y) =O[𝓝 0] fun y => ‖y‖ ^ (n + 1)) (y : E) : (p fun _ => y) = 0 := by
  obtain ⟨c, c_pos, hc⟩ := h.exists_pos
  obtain ⟨t, ht, t_open, z_mem⟩ := eventually_nhds_iff.mp (isBigOWith_iff.mp hc)
  obtain ⟨δ, δ_pos, δε⟩ := (Metric.isOpen_iff.mp t_open) 0 z_mem
  clear h hc z_mem
  rcases n with - | n
  · exact norm_eq_zero.mp (by
      simpa only [fin0_apply_norm, norm_eq_zero, norm_zero, zero_add, pow_one,
        mul_zero, norm_le_zero_iff] using! ht 0 (δε (Metric.mem_ball_self δ_pos)))
  · refine Or.elim (Classical.em (y = 0))
      (fun hy => by simpa only [hy] using! p.map_zero) fun hy => ?_
    replace hy := norm_pos_iff.mpr hy
    refine norm_eq_zero.mp (le_antisymm (le_of_forall_pos_le_add fun ε ε_pos => ?_) (norm_nonneg _))
    have h₀ := _root_.mul_pos c_pos (pow_pos hy (n.succ + 1))
    obtain ⟨k, k_pos, k_norm⟩ := NormedField.exists_norm_lt 𝕜
      (lt_min (mul_pos δ_pos (inv_pos.mpr hy)) (mul_pos ε_pos (inv_pos.mpr h₀)))
    have h₁ : ‖k • y‖ < δ := by
      rw [norm_smul]
      exact inv_mul_cancel_right₀ hy.ne.symm δ ▸
        mul_lt_mul_of_pos_right (lt_of_lt_of_le k_norm (min_le_left _ _)) hy
    have h₂ :=
      calc
        ‖p fun _ => k • y‖ ≤ c * ‖k • y‖ ^ (n.succ + 1) := by
          simpa only [norm_pow, _root_.norm_norm] using! ht (k • y) (δε (mem_ball_zero_iff.mpr h₁))
        _ = ‖k‖ ^ n.succ * (‖k‖ * (c * ‖y‖ ^ (n.succ + 1))) := by
          simp only [norm_smul, mul_pow]
          ring
    have h₃ : ‖k‖ * (c * ‖y‖ ^ (n.succ + 1)) < ε :=
      inv_mul_cancel_right₀ h₀.ne.symm ε ▸
        mul_lt_mul_of_pos_right (lt_of_lt_of_le k_norm (min_le_right _ _)) h₀
    calc
      ‖p fun _ => y‖ = ‖k⁻¹ ^ n.succ‖ * ‖p fun _ => k • y‖ := by
        simpa only [inv_smul_smul₀ (norm_pos_iff.mp k_pos), norm_smul, Finset.prod_const,
          Finset.card_fin] using!
          congr_arg norm (p.map_smul_univ (fun _ : Fin n.succ => k⁻¹) fun _ : Fin n.succ => k • y)
      _ ≤ ‖k⁻¹ ^ n.succ‖ * (‖k‖ ^ n.succ * (‖k‖ * (c * ‖y‖ ^ (n.succ + 1)))) := by gcongr
      _ = ‖(k⁻¹ * k) ^ n.succ‖ * (‖k‖ * (c * ‖y‖ ^ (n.succ + 1))) := by
        rw [← mul_assoc]
        simp [norm_mul, mul_pow]
      _ ≤ 0 + ε := by
        rw [inv_mul_cancel₀ (norm_pos_iff.mp k_pos)]
        simpa using! h₃.le

/-- If a formal multilinear series `p` represents the zero function at `x : E`, then the
terms `p n (fun i ↦ y)` appearing in the sum are zero for any `n : ℕ`, `y : E`. -/
/-
**HasFPowerSeriesAt.apply_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesAt.apply_eq_zero {p : FormalMultilinearSeries 𝕜 E F} {x : E
} (h : HasFPowerSeriesAt 0 p x) (n : Nat) : forall y : E, (p n fun _ => y) = 0
参数：h : HasFPowerSeriesAt 0 p x；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_range_succ_iff`：mem_range_succ_iff {a b : Nat} : a in range b
.succ ↔ a <= b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
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
· 使用定理 `HasFPowerSeriesAt.isBigO_sub_partialSum_pow`：HasFPowerSeriesAt.isBigO_su
b_partialSum_pow (hf : HasFPowerSeriesAt f p x) (n : Nat) : (fun y : E => f (x +
 y) - p.partialSum n y) =O[𝓝 0] f…
· 使用定理 `Asymptotics.IsBigO.continuousMultilinearMap_apply_eq_zero`：Asymptotics.I
sBigO.continuousMultilinearMap_apply_eq_zero {n : Nat} {p : E [×n]->L[𝕜] F} (h :
 (fun y => p fun _ => y) =O[𝓝 0] fun y => ‖y‖ ^…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a

--- 原说明 ---
If a formal multilinear series `p` represents the zero function at `x : E`, then
 the
terms `p n (fun i ↦ y)` appearing in the sum are zero for any `n : ℕ`, `y : E`.
-/
theorem HasFPowerSeriesAt.apply_eq_zero {p : FormalMultilinearSeries 𝕜 E F} {x : E}
    (h : HasFPowerSeriesAt 0 p x) (n : ℕ) : ∀ y : E, (p n fun _ => y) = 0 := by
  refine Nat.strong_induction_on n fun k hk => ?_
  have psum_eq : p.partialSum (k + 1) = fun y => p k fun _ => y := by
    funext z
    refine Finset.sum_eq_single _ (fun b hb hnb => ?_) fun hn => ?_
    · have := Finset.mem_range_succ_iff.mp hb
      simp only [hk b (this.lt_of_ne hnb)]
    · exact False.elim (hn (Finset.mem_range.mpr (lt_add_one k)))
  replace h := h.isBigO_sub_partialSum_pow k.succ
  simp only [psum_eq, zero_sub, Pi.zero_apply, Asymptotics.isBigO_neg_left] at h
  exact h.continuousMultilinearMap_apply_eq_zero

/-- A one-dimensional formal multilinear series representing the zero function is zero. -/
/-
**HasFPowerSeriesAt.eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesAt.eq_zero {p : FormalMultilinearSeries 𝕜 𝕜 E} {x : 𝕜} (h :
 HasFPowerSeriesAt 0 p x) : p = 0
参数：h : HasFPowerSeriesAt 0 p x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `FormalMultilinearSeries.ext`：∀ {𝕜 : Type u} {E : Type v} {F : Type w} [i
nst : Semiring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module 𝕜 E]   [ins
t_3 : Topological…
· 使用定理 `ContinuousMultilinearMap.ext_ring`：ext_ring [Finite ι] [TopologicalSpace
 R] ⦃f g : ContinuousMultilinearMap R (fun _ : ι => R) M₂⦄ (h : f (fun _ => 1) =
 g (fun _ => 1)) : f = …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousMultilinearMap.mkPiRing_apply_one_eq_self`：mkPiRing_apply_one_
eq_self (f : ContinuousMultilinearMap R (fun _ : ι => R) M) : ContinuousMultilin
earMap.mkPiRing R ι (f fun _ => 1) = f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousMultilinearMap.mkPiRing.congr_simp`：∀ (R : Type u) (ι : Type v
) {M : Type u_1} [inst : Fintype ι] [inst_1 : CommRing R] [inst_2 : AddCommMonoi
d M]   [inst_3 : _root_.Module R M…
· 使用定理 `HasFPowerSeriesAt.apply_eq_zero`：HasFPowerSeriesAt.apply_eq_zero {p : Fo
rmalMultilinearSeries 𝕜 E F} {x : E} (h : HasFPowerSeriesAt 0 p x) (n : Nat) : f
orall y : E, (p n fun…
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousMultilinearMap.instIsZeroApplyForall`：∀ {R : Type u} {ι : Type
 v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → 
AddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A one-dimensional formal multilinear series representing the zero function is ze
ro.
-/
theorem HasFPowerSeriesAt.eq_zero {p : FormalMultilinearSeries 𝕜 𝕜 E} {x : 𝕜}
    (h : HasFPowerSeriesAt 0 p x) : p = 0 := by
  ext n
  rw [← mkPiRing_apply_one_eq_self (p n)]
  simp [h.apply_eq_zero n 1]

/-- One-dimensional formal multilinear series representing the same function are equal. -/
/-
**HasFPowerSeriesAt.eq_formalMultilinearSeries** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesAt.eq_formalMultilinearSeries {p₁ p₂ : FormalMultilinearSer
ies 𝕜 𝕜 E} {f : 𝕜 -> E} {x : 𝕜} (h₁ : HasFPowerSeriesAt f p₁ x) (h₂ : HasFPowerS
eriesAt f p₂ x) : p₁ = p₂
参数：h₁ : HasFPowerSeriesAt f p₁ x；h₂ : HasFPowerSeriesAt f p₂ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `HasFPowerSeriesAt.eq_zero`：HasFPowerSeriesAt.eq_zero {p : FormalMultilin
earSeries 𝕜 𝕜 E} {x : 𝕜} (h : HasFPowerSeriesAt 0 p x) : p = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `HasFPowerSeriesAt.sub`：HasFPowerSeriesAt.sub (hf : HasFPowerSeriesAt f p
f x) (hg : HasFPowerSeriesAt g pg x) : HasFPowerSeriesAt (f - g) (pf - pg) x

--- 原说明 ---
One-dimensional formal multilinear series representing the same function are equ
al.
-/
theorem HasFPowerSeriesAt.eq_formalMultilinearSeries {p₁ p₂ : FormalMultilinearSeries 𝕜 𝕜 E}
    {f : 𝕜 → E} {x : 𝕜} (h₁ : HasFPowerSeriesAt f p₁ x) (h₂ : HasFPowerSeriesAt f p₂ x) : p₁ = p₂ :=
  sub_eq_zero.mp (HasFPowerSeriesAt.eq_zero (x := x) (by simpa only [sub_self] using h₁.sub h₂))
/-
**HasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually** 是 Mathlib 中的一个定理，
位于命名空间 ``。
形式化陈述：HasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually {p q : FormalMu
ltilinearSeries 𝕜 𝕜 E} {f g : 𝕜 -> E} {x : 𝕜} (hp : HasFPowerSeriesAt f p x) (hq
 : HasFPowerSeriesAt g q x) (heq : forallᶠ z in 𝓝 x, f z = g z) : p = q
参数：hp : HasFPowerSeriesAt f p x；hq : HasFPowerSeriesAt g q x；heq : forallᶠ z in 
𝓝 x, f z = g z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasFPowerSeriesAt.eq_formalMultilinearSeries`：HasFPowerSeriesAt.eq_forma
lMultilinearSeries {p₁ p₂ : FormalMultilinearSeries 𝕜 𝕜 E} {f : 𝕜 -> E} {x : 𝕜} 
(h₁ : HasFPowerSeriesAt f p₁ x) (h…
· 使用定理 `HasFPowerSeriesAt.congr`：HasFPowerSeriesAt.congr (hf : HasFPowerSeriesAt
 f p x) (hg : f =ᶠ[𝓝 x] g) : HasFPowerSeriesAt g p x
-/
theorem HasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually
    {p q : FormalMultilinearSeries 𝕜 𝕜 E} {f g : 𝕜 → E} {x : 𝕜} (hp : HasFPowerSeriesAt f p x)
    (hq : HasFPowerSeriesAt g q x) (heq : ∀ᶠ z in 𝓝 x, f z = g z) : p = q :=
  (hp.congr heq).eq_formalMultilinearSeries hq

/-- A one-dimensional formal multilinear series representing a locally zero function is zero. -/
/-
**HasFPowerSeriesAt.eq_zero_of_eventually** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesAt.eq_zero_of_eventually {p : FormalMultilinearSeries 𝕜 𝕜 E
} {f : 𝕜 -> E} {x : 𝕜} (hp : HasFPowerSeriesAt f p x) (hf : f =ᶠ[𝓝 x] 0) : p = 0
参数：hp : HasFPowerSeriesAt f p x；hf : f =ᶠ[𝓝 x] 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasFPowerSeriesAt.eq_zero`：HasFPowerSeriesAt.eq_zero {p : FormalMultilin
earSeries 𝕜 𝕜 E} {x : 𝕜} (h : HasFPowerSeriesAt 0 p x) : p = 0
· 使用定理 `HasFPowerSeriesAt.congr`：HasFPowerSeriesAt.congr (hf : HasFPowerSeriesAt
 f p x) (hg : f =ᶠ[𝓝 x] g) : HasFPowerSeriesAt g p x

--- 原说明 ---
A one-dimensional formal multilinear series representing a locally zero function
 is zero.
-/
theorem HasFPowerSeriesAt.eq_zero_of_eventually {p : FormalMultilinearSeries 𝕜 𝕜 E} {f : 𝕜 → E}
    {x : 𝕜} (hp : HasFPowerSeriesAt f p x) (hf : f =ᶠ[𝓝 x] 0) : p = 0 :=
  (hp.congr hf).eq_zero

/-- If a function `f : 𝕜 → E` has two power series representations at `x`, then the given radii in
which convergence is guaranteed may be interchanged. This can be useful when the formal multilinear
series in one representation has a particularly nice form, but the other has a larger radius. -/
/-
**HasFPowerSeriesOnBall.exchange_radius** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesOnBall.exchange_radius {p₁ p₂ : FormalMultilinearSeries 𝕜 𝕜
 E} {f : 𝕜 -> E} {r₁ r₂ : Real>=0∞} {x : 𝕜} (h₁ : HasFPowerSeriesOnBall f p₁ x r
₁) (h₂ : HasFPowerSeriesOnBall f p₂ x r₂) : HasFPowerSeriesOnBall f p₁ x r₂
参数：h₁ : HasFPowerSeriesOnBall f p₁ x r₁；h₂ : HasFPowerSeriesOnBall f p₂ x r₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasFPowerSeriesAt.eq_formalMultilinearSeries`：HasFPowerSeriesAt.eq_forma
lMultilinearSeries {p₁ p₂ : FormalMultilinearSeries 𝕜 𝕜 E} {f : 𝕜 -> E} {x : 𝕜} 
(h₁ : HasFPowerSeriesAt f p₁ x) (h…
· 使用定理 `HasFPowerSeriesOnBall.hasFPowerSeriesAt`：HasFPowerSeriesOnBall.hasFPower
SeriesAt (hf : HasFPowerSeriesOnBall f p x r) : HasFPowerSeriesAt f p x

--- 原说明 ---
If a function `f : 𝕜 → E` has two power series representations at `x`, then the 
given radii in
which convergence is guaranteed may be interchanged. This can be useful when the
 formal multilinear
series in one representation has a particularly nice form, but the other has a l
arger radius.
-/
theorem HasFPowerSeriesOnBall.exchange_radius {p₁ p₂ : FormalMultilinearSeries 𝕜 𝕜 E} {f : 𝕜 → E}
    {r₁ r₂ : ℝ≥0∞} {x : 𝕜} (h₁ : HasFPowerSeriesOnBall f p₁ x r₁)
    (h₂ : HasFPowerSeriesOnBall f p₂ x r₂) : HasFPowerSeriesOnBall f p₁ x r₂ :=
  h₂.hasFPowerSeriesAt.eq_formalMultilinearSeries h₁.hasFPowerSeriesAt ▸ h₂

/-- If a function `f : 𝕜 → E` has power series representation `p` on a ball of some radius and for
each positive radius it has some power series representation, then `p` converges to `f` on the whole
`𝕜`. -/
/-
**HasFPowerSeriesOnBall.r_eq_top_of_exists** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesOnBall.r_eq_top_of_exists {f : 𝕜 -> E} {r : Real>=0∞} {x : 
𝕜} {p : FormalMultilinearSeries 𝕜 𝕜 E} (h : HasFPowerSeriesOnBall f p x r) (h' :
 forall (r' : Real>=0) (_ : 0 < r'), exists p' : FormalMultilinearSeries 𝕜 𝕜 E, 
HasFPowerSeriesOnBall f p' x r') : HasFPowerSeriesOnBall f p x ∞
参数：h : HasFPowerSeriesOnBall f p x r；h' : forall (r' : Real>=0) (_ : 0 < r'), ex
ists p' : FormalMultilinearSeries 𝕜 𝕜 E, HasFPowerSeriesOnBall f p' x r'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ENNReal.le_of_forall_pos_nnreal_lt`：le_of_forall_pos_nnreal_lt {x y : Re
al>=0∞} (h : forall r : Real>=0, 0 < r -> ↑r < x -> ↑r <= y) : x <= y
· 使用定理 `HasFPowerSeriesOnBall.r_le`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_
3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 
: NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesOnBall.exchange_radius`：HasFPowerSeriesOnBall.exchange_ra
dius {p₁ p₂ : FormalMultilinearSeries 𝕜 𝕜 E} {f : 𝕜 -> E} {r₁ r₂ : Real>=0∞} {x 
: 𝕜} (h₁ : HasFPowerSeriesO…
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `IsStrictOrderedRing.toNoMaxOrder`：∀ {R : Type u} [inst : Semiring R] [in
st_1 : PartialOrder R] [IsStrictOrderedRing R], NoMaxOrder R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `LT.lt.ne_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → a ≠ ⊥
· 使用定理 `HasFPowerSeriesOnBall.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type 
u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_
2 : NormedSpace 𝕜 …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_eball_zero_iff`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {a : 
E} {r : ENNReal}, a ∈ Metric.eball 0 r ↔ ‖a‖ₑ < r
· 使用定理 `ENNReal.coe_lt_coe`：∀ {r q : NNReal}, ↑r < ↑q ↔ r < q

--- 原说明 ---
If a function `f : 𝕜 → E` has power series representation `p` on a ball of some 
radius and for
each positive radius it has some power series representation, then `p` converges
 to `f` on the whole
`𝕜`.
-/
theorem HasFPowerSeriesOnBall.r_eq_top_of_exists {f : 𝕜 → E} {r : ℝ≥0∞} {x : 𝕜}
    {p : FormalMultilinearSeries 𝕜 𝕜 E} (h : HasFPowerSeriesOnBall f p x r)
    (h' : ∀ (r' : ℝ≥0) (_ : 0 < r'), ∃ p' : FormalMultilinearSeries 𝕜 𝕜 E,
      HasFPowerSeriesOnBall f p' x r') :
    HasFPowerSeriesOnBall f p x ∞ :=
  { r_le := ENNReal.le_of_forall_pos_nnreal_lt fun r hr _ =>
      let ⟨_, hp'⟩ := h' r hr
      (h.exchange_radius hp').r_le
    r_pos := ENNReal.coe_lt_top
    hasSum := fun {y} _ =>
      let ⟨r', hr'⟩ := exists_gt ‖y‖₊
      let ⟨_, hp'⟩ := h' r' hr'.ne_bot.bot_lt
      (h.exchange_radius hp').hasSum <| mem_eball_zero_iff.mpr (ENNReal.coe_lt_coe.2 hr') }

end Uniqueness

namespace AnalyticOnNhd

/-- If an analytic function vanishes around a point, then it is uniformly zero along
a connected set. Superseded by `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero` which
does not assume completeness of the target space. -/
/-
**AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero_aux** 是 Mathlib 中
的一个定理，位于命名空间 `AnalyticOnNhd`。
形式化陈述：eqOn_zero_of_preconnected_of_eventuallyEq_zero_aux [CompleteSpace F] {f : 
E -> F} {U : Set E} (hf : AnalyticOnNhd 𝕜 f U) (hU : IsPreconnected U) {z₀ : E} 
(h₀ : z₀ in U) (hfz₀ : f =ᶠ[𝓝 z₀] 0) : EqOn f 0 U
参数：hf : AnalyticOnNhd 𝕜 f U；hU : IsPreconnected U；h₀ : z₀ in U；hfz₀ : f =ᶠ[𝓝 z₀]
 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EMetric.mem_closure_iff`：mem_closure_iff : x in closure s ↔ forall ε > 0
, exists y in s, edist x y < ε
· 使用定理 `ENNReal.half_pos`：∀ {a : ENNReal}, a ≠ 0 → 0 < a / 2
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `HasFPowerSeriesOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u
_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2
 : NormedSpace 𝕜 …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_eq_enorm_sub`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (
a b : E), edist a b = ‖a - b‖ₑ
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
· 使用定理 `HasFPowerSeriesOnBall.changeOrigin`：HasFPowerSeriesOnBall.changeOrigin (
hf : HasFPowerSeriesOnBall f p x r) (h : (‖y‖₊ : Real>=0∞) < r) : HasFPowerSerie
sOnBall f (p.changeOrigi…
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `ENNReal.half_le_self`：∀ {a : ENNReal}, a / 2 ≤ a
· 使用定理 `HasFPowerSeriesOnBall.mono`：HasFPowerSeriesOnBall.mono (hf : HasFPowerSe
riesOnBall f p x r) (r'_pos : 0 < r') (hr : r' <= r) : HasFPowerSeriesOnBall f p
 x r'
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `ENNReal.le_sub_of_add_le_left`：le_sub_of_add_le_left (ha : a != ∞) : a +
 b <= c -> b <= c - a
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
（共 50 条，此处仅展示前 30 条）

--- 原说明 ---
If an analytic function vanishes around a point, then it is uniformly zero along
a connected set. Superseded by `AnalyticOnNhd.eqOn_zero_of_preconnected_of_event
uallyEq_zero` which
does not assume completeness of the target space.
-/
theorem eqOn_zero_of_preconnected_of_eventuallyEq_zero_aux [CompleteSpace F] {f : E → F} {U : Set E}
    (hf : AnalyticOnNhd 𝕜 f U) (hU : IsPreconnected U)
    {z₀ : E} (h₀ : z₀ ∈ U) (hfz₀ : f =ᶠ[𝓝 z₀] 0) :
    EqOn f 0 U := by
  /- Let `u` be the set of points around which `f` vanishes. It is clearly open. We have to show
    that its limit points in `U` still belong to it, from which the inclusion `U ⊆ u` will follow
    by connectedness. -/
  let u := {x | f =ᶠ[𝓝 x] 0}
  suffices main : closure u ∩ U ⊆ u by
    have Uu : U ⊆ u :=
      hU.subset_of_closure_inter_subset isOpen_setOfPred_eventually_nhds ⟨z₀, h₀, hfz₀⟩ main
    intro z hz
    simpa using mem_of_mem_nhds (Uu hz)
  /- Take a limit point `x`, then a ball `B (x, r)` on which it has a power series expansion, and
    then `y ∈ B (x, r/2) ∩ u`. Then `f` has a power series expansion on `B (y, r/2)` as it is
    contained in `B (x, r)`. All the coefficients in this series expansion vanish, as `f` is zero
    on a neighborhood of `y`. Therefore, `f` is zero on `B (y, r/2)`. As this ball contains `x`,
    it follows that `f` vanishes on a neighborhood of `x`, proving the claim. -/
  rintro x ⟨xu, xU⟩
  rcases hf x xU with ⟨p, r, hp⟩
  obtain ⟨y, yu, hxy⟩ : ∃ y ∈ u, edist x y < r / 2 :=
    EMetric.mem_closure_iff.1 xu (r / 2) (ENNReal.half_pos hp.r_pos.ne')
  let q := p.changeOrigin (y - x)
  have has_series : HasFPowerSeriesOnBall f q y (r / 2) := by
    have A : (‖y - x‖₊ : ℝ≥0∞) < r / 2 := by rwa [edist_comm, edist_eq_enorm_sub] at hxy
    have := hp.changeOrigin (A.trans_le ENNReal.half_le_self)
    simp only [add_sub_cancel] at this
    apply this.mono (ENNReal.half_pos hp.r_pos.ne')
    apply ENNReal.le_sub_of_add_le_left ENNReal.coe_ne_top
    apply (add_le_add A.le (le_refl (r / 2))).trans (le_of_eq _)
    exact ENNReal.add_halves _
  have M : Metric.eball y (r / 2) ∈ 𝓝 x := Metric.isOpen_eball.mem_nhds hxy
  filter_upwards [M] with z hz
  have A : HasSum (fun n : ℕ => q n fun _ : Fin n => z - y) (f z) := has_series.hasSum_sub hz
  have B : HasSum (fun n : ℕ => q n fun _ : Fin n => z - y) 0 := by
    have : HasFPowerSeriesAt 0 q y := has_series.hasFPowerSeriesAt.congr yu
    convert! hasSum_zero (α := F) using 1
    ext n
    exact this.apply_eq_zero n _
  exact HasSum.unique A B

/-- The *identity principle* for analytic functions: If an analytic function vanishes in a whole
neighborhood of a point `z₀`, then it is uniformly zero along a connected set. For a one-dimensional
version assuming only that the function vanishes at some points arbitrarily close to `z₀`, see
`AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero`. -/
/-
**AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero** 是 Mathlib 中的一个定
理，位于命名空间 `AnalyticOnNhd`。
形式化陈述：eqOn_zero_of_preconnected_of_eventuallyEq_zero {f : E -> F} {U : Set E} (h
f : AnalyticOnNhd 𝕜 f U) (hU : IsPreconnected U) {z₀ : E} (h₀ : z₀ in U) (hfz₀ :
 f =ᶠ[𝓝 z₀] 0) : EqOn f 0 U
参数：hf : AnalyticOnNhd 𝕜 f U；hU : IsPreconnected U；h₀ : z₀ in U；hfz₀ : f =ᶠ[𝓝 z₀]
 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `AnalyticAt.comp`：AnalyticAt.comp {g : F -> G} {f : E -> F} {x : E} (hg :
 AnalyticAt 𝕜 g (f x)) (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (g ∘ f) x
· 使用定理 `ContinuousLinearMap.analyticAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {F : Type u_…
· 使用定理 `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero_aux`：eqOn_z
ero_of_preconnected_of_eventuallyEq_zero_aux [CompleteSpace F] {f : E -> F} {U :
 Set E} (hf : AnalyticOnNhd 𝕜 f U) (hU : IsPreconnecte…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `UniformSpace.Completion.coe_injective`：coe_injective [T0Space α] : Funct
ion.Injective ((↑) : α -> Completion α)
· 使用定理 `T3Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T3
Space X], T0Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `instT4SpaceOfT1SpaceOfNormalSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [T1Space X] [NormalSpace X], T4Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `CompletelyNormalSpace.toNormalSpace`：∀ {X : Type u_1} [inst : Topologica
lSpace X] [CompletelyNormalSpace X], NormalSpace X
· 使用定理 `UniformSpace.completelyNormalSpace_of_isCountablyGenerated_uniformity`：∀
 {α : Type u} [inst : UniformSpace α] [(uniformity α).IsCountablyGenerated], Com
pletelyNormalSpace α
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated

--- 原说明 ---
The *identity principle* for analytic functions: If an analytic function vanishe
s in a whole
neighborhood of a point `z₀`, then it is uniformly zero along a connected set. F
or a one-dimensional
version assuming only that the function vanishes at some points arbitrarily clos
e to `z₀`, see
`AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero`.
-/
theorem eqOn_zero_of_preconnected_of_eventuallyEq_zero {f : E → F} {U : Set E}
    (hf : AnalyticOnNhd 𝕜 f U) (hU : IsPreconnected U)
    {z₀ : E} (h₀ : z₀ ∈ U) (hfz₀ : f =ᶠ[𝓝 z₀] 0) :
    EqOn f 0 U := by
  let F' := UniformSpace.Completion F
  set e : F →L[𝕜] F' := UniformSpace.Completion.toComplL
  have : AnalyticOnNhd 𝕜 (e ∘ f) U := fun x hx => (e.analyticAt _).comp (hf x hx)
  have A : EqOn (e ∘ f) 0 U := by
    apply eqOn_zero_of_preconnected_of_eventuallyEq_zero_aux this hU h₀
    filter_upwards [hfz₀] with x hx
    simp only [hx, Function.comp_apply, Pi.zero_apply, map_zero]
  intro z hz
  have : e (f z) = e 0 := by simpa only using! A hz
  exact UniformSpace.Completion.coe_injective F this

/-- The *identity principle* for analytic functions: If two analytic functions coincide in a whole
neighborhood of a point `z₀`, then they coincide globally along a connected set.
For a one-dimensional version assuming only that the functions coincide at some points
arbitrarily close to `z₀`, see `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`. -/
/-
**AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 `
AnalyticOnNhd`。
形式化陈述：eqOn_of_preconnected_of_eventuallyEq {f g : E -> F} {U : Set E} (hf : Anal
yticOnNhd 𝕜 f U) (hg : AnalyticOnNhd 𝕜 g U) (hU : IsPreconnected U) {z₀ : E} (h₀
 : z₀ in U) (hfg : f =ᶠ[𝓝 z₀] g) : EqOn f g U
参数：hf : AnalyticOnNhd 𝕜 f U；hg : AnalyticOnNhd 𝕜 g U；hU : IsPreconnected U；h₀ : 
z₀ in U；hfg : f =ᶠ[𝓝 z₀] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`：eqOn_zero_
of_preconnected_of_eventuallyEq_zero {f : E -> F} {U : Set E} (hf : AnalyticOnNh
d 𝕜 f U) (hU : IsPreconnected U) {z₀ : E} (h₀ : z₀…
· 使用定理 `AnalyticOnNhd.sub`：AnalyticOnNhd.sub (hf : AnalyticOnNhd 𝕜 f s) (hg : An
alyticOnNhd 𝕜 g s) : AnalyticOnNhd 𝕜 (f - g) s

--- 原说明 ---
The *identity principle* for analytic functions: If two analytic functions coinc
ide in a whole
neighborhood of a point `z₀`, then they coincide globally along a connected set.
For a one-dimensional version assuming only that the functions coincide at some 
points
arbitrarily close to `z₀`, see `AnalyticOnNhd.eqOn_of_preconnected_of_frequently
_eq`.
-/
theorem eqOn_of_preconnected_of_eventuallyEq {f g : E → F} {U : Set E} (hf : AnalyticOnNhd 𝕜 f U)
    (hg : AnalyticOnNhd 𝕜 g U) (hU : IsPreconnected U) {z₀ : E} (h₀ : z₀ ∈ U) (hfg : f =ᶠ[𝓝 z₀] g) :
    EqOn f g U := by
  have hfg' : f - g =ᶠ[𝓝 z₀] 0 := hfg.mono fun z h => by simp [h]
  simpa [sub_eq_zero] using! fun z hz =>
    (hf.sub hg).eqOn_zero_of_preconnected_of_eventuallyEq_zero hU h₀ hfg' hz

/-- The *identity principle* for analytic functions: If two analytic functions on a normed space
coincide in a neighborhood of a point `z₀`, then they coincide everywhere.
For a one-dimensional version assuming only that the functions coincide at some points
arbitrarily close to `z₀`, see `AnalyticOnNhd.eq_of_frequently_eq`. -/
/-
**AnalyticOnNhd.eq_of_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 `AnalyticOnNhd`。
形式化陈述：eq_of_eventuallyEq {f g : E -> F} [PreconnectedSpace E] (hf : AnalyticOnNh
d 𝕜 f univ) (hg : AnalyticOnNhd 𝕜 g univ) {z₀ : E} (hfg : f =ᶠ[𝓝 z₀] g) : f = g
参数：hf : AnalyticOnNhd 𝕜 f univ；hg : AnalyticOnNhd 𝕜 g univ；hfg : f =ᶠ[𝓝 z₀] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`：eqOn_of_preconnected
_of_eventuallyEq {f g : E -> F} {U : Set E} (hf : AnalyticOnNhd 𝕜 f U) (hg : Ana
lyticOnNhd 𝕜 g U) (hU : IsPreconnected U…
· 使用定理 `PreconnectedSpace.isPreconnected_univ`：∀ {α : Type u} {inst : Topologica
lSpace α} [self : PreconnectedSpace α], IsPreconnected Set.univ
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
The *identity principle* for analytic functions: If two analytic functions on a 
normed space
coincide in a neighborhood of a point `z₀`, then they coincide everywhere.
For a one-dimensional version assuming only that the functions coincide at some 
points
arbitrarily close to `z₀`, see `AnalyticOnNhd.eq_of_frequently_eq`.
-/
theorem eq_of_eventuallyEq {f g : E → F} [PreconnectedSpace E] (hf : AnalyticOnNhd 𝕜 f univ)
    (hg : AnalyticOnNhd 𝕜 g univ) {z₀ : E} (hfg : f =ᶠ[𝓝 z₀] g) : f = g :=
  funext fun x =>
    eqOn_of_preconnected_of_eventuallyEq hf hg isPreconnected_univ (mem_univ z₀) hfg (mem_univ x)

end AnalyticOnNhd

