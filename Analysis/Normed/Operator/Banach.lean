/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Group.AddTorsor

/-!
# Banach open mapping theorem

This file contains the Banach open mapping theorem, i.e., the fact that a bijective
bounded linear map between Banach spaces has a bounded inverse.
-/

@[expose] public section

open Function Metric Set Filter Finset Topology NNReal

open LinearMap (range ker)

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜'] {σ : 𝕜 →+* 𝕜'}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜' F] (f : E →SL[σ] F)

namespace ContinuousLinearMap

/-- A (possibly nonlinear) right inverse to a continuous linear map, which doesn't have to be
linear itself but which satisfies a bound `‖inverse x‖ ≤ C * ‖x‖`. A surjective continuous linear
map doesn't always have a continuous linear right inverse, but it always has a nonlinear inverse
in this sense, by Banach's open mapping theorem. -/
/-
**ContinuousLinearMap.NonlinearRightInverse** 是 Mathlib 中的一个归纳类型，位于命名空间 `Continu
ousLinearMap`。
形式化陈述：{𝕜 : Type u_1} →   {𝕜' : Type u_2} →     [inst : NontriviallyNormedField 𝕜
] →       [inst_1 : NontriviallyNormedField 𝕜'] →         {σ : 𝕜 →+* 𝕜'} →      
     {E : Type u_3} →             [inst_2 : NormedAddCommGroup E] →             
  [inst_3 : NormedSpace 𝕜 E] →                 {F : Type u_4} →                 
  [inst_4 : NormedAddCommGroup F] → [inst_5 : NormedSpace 𝕜' F] → (E →SL[σ] F) →
 Type (max u_3 u_4)
参数：E →SL[σ] F；max u_3 u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A (possibly nonlinear) right inverse to a continuous linear map, which doesn't h
ave to be
linear itself but which satisfies a bound `‖inverse x‖ ≤ C * ‖x‖`. A surjective 
continuous linear
map doesn't always have a continuous linear right inverse, but it always has a n
onlinear inverse
in this sense, by Banach's open mapping theorem.
-/
structure NonlinearRightInverse where
  /-- The underlying function.

  Do NOT use directly. Use the coercion instead. -/
  toFun : F → E
  /-- The bound `C` so that `‖inverse x‖ ≤ C * ‖x‖` for all `x`. -/
  nnnorm : ℝ≥0
  bound' : ∀ y, ‖toFun y‖ ≤ nnnorm * ‖y‖
  right_inv' : ∀ y, f (toFun y) = y
/-
**ContinuousLinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeFun (NonlinearRightInverse f) fun _ => F → E :=
  ⟨fun fsymm => fsymm.toFun⟩

@[simp]
/-
**ContinuousLinearMap.NonlinearRightInverse.right_inv** 是 Mathlib 中的一个定理，位于命名空间 
`ContinuousLinearMap.NonlinearRightInverse`。
形式化陈述：∀ {𝕜 : Type u_1} {𝕜' : Type u_2} [inst : NontriviallyNormedField 𝕜] [inst_
1 : NontriviallyNormedField 𝕜'] {σ : 𝕜 →+* 𝕜'}   {E : Type u_3} [inst_2 : Normed
AddCommGroup E] [inst_3 : NormedSpace 𝕜 E] {F : Type u_4}   [inst_4 : NormedAddC
ommGroup F] [inst_5 : NormedSpace 𝕜' F] {f : E →SL[σ] F} (fsymm : f.NonlinearRig
htInverse)   (y : F), f (fsymm.toFun y) = y
参数：fsymm : f.NonlinearRightInverse；y : F；fsymm.toFun y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.NonlinearRightInverse.right_inv'`：∀ {𝕜 : Type u_1} {
𝕜' : Type u_2} [inst : NontriviallyNormedField 𝕜] [inst_1 : NontriviallyNormedFi
eld 𝕜'] {σ : 𝕜 →+* 𝕜'}   {E : Type u_3} [i…
-/
theorem NonlinearRightInverse.right_inv {f : E →SL[σ] F} (fsymm : NonlinearRightInverse f) (y : F) :
    f (fsymm y) = y :=
  fsymm.right_inv' y
/-
**ContinuousLinearMap.NonlinearRightInverse.bound** 是 Mathlib 中的一个定理，位于命名空间 `Con
tinuousLinearMap.NonlinearRightInverse`。
形式化陈述：∀ {𝕜 : Type u_1} {𝕜' : Type u_2} [inst : NontriviallyNormedField 𝕜] [inst_
1 : NontriviallyNormedField 𝕜'] {σ : 𝕜 →+* 𝕜'}   {E : Type u_3} [inst_2 : Normed
AddCommGroup E] [inst_3 : NormedSpace 𝕜 E] {F : Type u_4}   [inst_4 : NormedAddC
ommGroup F] [inst_5 : NormedSpace 𝕜' F] {f : E →SL[σ] F} (fsymm : f.NonlinearRig
htInverse)   (y : F), ‖fsymm.toFun y‖ ≤ ↑fsymm.nnnorm * ‖y‖
参数：fsymm : f.NonlinearRightInverse；y : F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.NonlinearRightInverse.bound'`：∀ {𝕜 : Type u_1} {𝕜' :
 Type u_2} [inst : NontriviallyNormedField 𝕜] [inst_1 : NontriviallyNormedField 
𝕜'] {σ : 𝕜 →+* 𝕜'}   {E : Type u_3} [i…
-/
theorem NonlinearRightInverse.bound {f : E →SL[σ] F} (fsymm : NonlinearRightInverse f) (y : F) :
    ‖fsymm y‖ ≤ fsymm.nnnorm * ‖y‖ :=
  fsymm.bound' y

end ContinuousLinearMap

variable {σ' : 𝕜' →+* 𝕜} [RingHomInvPair σ σ'] [RingHomIsometric σ] [RingHomIsometric σ']

/-- Given a continuous linear equivalence, the inverse is in particular an instance of
`ContinuousLinearMap.NonlinearRightInverse` (which turns out to be linear). -/
/-
**ContinuousLinearEquiv.toNonlinearRightInverse** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ContinuousLinearEquiv.toNonlinearRightInverse [RingHomInvPair σ' σ] (f : E
 ≃SL[σ] F) : ContinuousLinearMap.NonlinearRightInverse (f : E ->SL[σ] F) where t
oFun
参数：f : E ≃SL[σ] F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a continuous linear equivalence, the inverse is in particular an instance 
of
`ContinuousLinearMap.NonlinearRightInverse` (which turns out to be linear).
-/
noncomputable def ContinuousLinearEquiv.toNonlinearRightInverse
    [RingHomInvPair σ' σ] (f : E ≃SL[σ] F) :
    ContinuousLinearMap.NonlinearRightInverse (f : E →SL[σ] F) where
  toFun := f.invFun
  nnnorm := ‖(f.symm : F →SL[σ'] E)‖₊
  bound' _ := ContinuousLinearMap.le_opNorm (f.symm : F →SL[σ'] E) _
  right_inv' := f.apply_symm_apply
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [RingHomInvPair σ' σ] (f : E ≃SL[σ] F) :
    Inhabited (ContinuousLinearMap.NonlinearRightInverse (f : E →SL[σ] F)) :=
  ⟨f.toNonlinearRightInverse⟩

/-! ### Proof of the Banach open mapping theorem -/


variable [CompleteSpace F]

namespace ContinuousLinearMap

include σ' in
/-- First step of the proof of the Banach open mapping theorem (using completeness of `F`):
by Baire's theorem, there exists a ball in `E` whose image closure has nonempty interior.
Rescaling everything, it follows that any `y ∈ F` is arbitrarily well approached by
images of elements of norm at most `C * ‖y‖`.
For further use, we will only need such an element whose image
is within distance `‖y‖/2` of `y`, to apply an iterative process. -/
/-
**ContinuousLinearMap.exists_approx_preimage_norm_le** 是 Mathlib 中的一个定理，位于命名空间 `
ContinuousLinearMap`。
形式化陈述：exists_approx_preimage_norm_le (surj : Surjective f) : exists C >= 0, fora
ll y, exists x, dist (f x) y <= 1 / 2 * ‖y‖ ∧ ‖x‖ <= C * ‖y‖
参数：surj : Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `exists_nat_gt`：exists_nat_gt (x : R) : exists n : Nat, x < n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.mem_ball`：mem_ball : y in ball x ε ↔ dist y x < ε
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `nonempty_interior_of_iUnion_of_closed`：nonempty_interior_of_iUnion_of_cl
osed [Countable ι] {f : ι -> Set X} (hc : forall i, IsClosed (f i)) (hU : ⋃ i, f
 i = univ) : exists i, (int…
· 使用定理 `BaireSpace.of_completelyPseudoMetrizable`：∀ {X : Type u_1} [inst : Topol
ogicalSpace X] [TopologicalSpace.IsCompletelyPseudoMetrizableSpace X], BaireSpac
e X
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.toIsCompletelyPseudoMetriza
bleSpace`：∀ {X : Type u_1} [inst : TopologicalSpace X] [TopologicalSpace.IsCompl
etelyMetrizableSpace X],   TopologicalSpace.IsCompletelyPseudoMetrizab…
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
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
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
（共 169 条，此处仅展示前 30 条）

--- 原说明 ---
First step of the proof of the Banach open mapping theorem (using completeness o
f `F`):
by Baire's theorem, there exists a ball in `E` whose image closure has nonempty 
interior.
Rescaling everything, it follows that any `y ∈ F` is arbitrarily well approached
 by
images of elements of norm at most `C * ‖y‖`.
For further use, we will only need such an element whose image
is within distance `‖y‖/2` of `y`, to apply an iterative process.
-/
theorem exists_approx_preimage_norm_le (surj : Surjective f) :
    ∃ C ≥ 0, ∀ y, ∃ x, dist (f x) y ≤ 1 / 2 * ‖y‖ ∧ ‖x‖ ≤ C * ‖y‖ := by
  have A : ⋃ n : ℕ, closure (f '' ball 0 n) = Set.univ := by
    refine Subset.antisymm (subset_univ _) fun y _ => ?_
    rcases surj y with ⟨x, hx⟩
    rcases exists_nat_gt ‖x‖ with ⟨n, hn⟩
    refine mem_iUnion.2 ⟨n, subset_closure ?_⟩
    refine (mem_image _ _ _).2 ⟨x, ⟨?_, hx⟩⟩
    rwa [mem_ball, dist_eq_norm, sub_zero]
  have : ∃ (n : ℕ) (x : _), x ∈ interior (closure (f '' ball 0 n)) :=
    nonempty_interior_of_iUnion_of_closed (fun n => isClosed_closure) A
  simp only [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at this
  rcases this with ⟨n, a, ε, ⟨εpos, H⟩⟩
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  refine ⟨(ε / 2)⁻¹ * ‖c‖ * 2 * n, by positivity, fun y => ?_⟩
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · have hc' : 1 < ‖σ c‖ := by simp only [RingHomIsometric.norm_map, hc]
    rcases rescale_to_shell hc' (half_pos εpos) hy with ⟨d, hd, ydlt, -, dinv⟩
    let δ := ‖d‖ * ‖y‖ / 4
    have δpos : 0 < δ := by positivity
    have : a + d • y ∈ ball a ε := by
      simp [dist_eq_norm, lt_of_le_of_lt ydlt.le (half_lt_self εpos)]
    rcases Metric.mem_closure_iff.1 (H this) _ δpos with ⟨z₁, z₁im, h₁⟩
    rcases (mem_image _ _ _).1 z₁im with ⟨x₁, hx₁, xz₁⟩
    rw [← xz₁] at h₁
    rw [mem_ball, dist_eq_norm, sub_zero] at hx₁
    have : a ∈ ball a ε := by
      simp only [mem_ball, dist_self]
      exact εpos
    rcases Metric.mem_closure_iff.1 (H this) _ δpos with ⟨z₂, z₂im, h₂⟩
    rcases (mem_image _ _ _).1 z₂im with ⟨x₂, hx₂, xz₂⟩
    rw [← xz₂] at h₂
    rw [mem_ball, dist_eq_norm, sub_zero] at hx₂
    let x := x₁ - x₂
    have I : ‖f x - d • y‖ ≤ 2 * δ :=
      calc
        ‖f x - d • y‖ = ‖f x₁ - (a + d • y) - (f x₂ - a)‖ := by
          congr 1
          simp only [x, f.map_sub]
          abel
        _ ≤ ‖f x₁ - (a + d • y)‖ + ‖f x₂ - a‖ := norm_sub_le _ _
        _ ≤ 2 * δ := by grind [dist_eq_norm']
    have J : ‖f (σ' d⁻¹ • x) - y‖ ≤ 1 / 2 * ‖y‖ :=
      calc
        ‖f (σ' d⁻¹ • x) - y‖ = ‖d⁻¹ • f x - (d⁻¹ * d) • y‖ := by
          rwa [f.map_smulₛₗ _, inv_mul_cancel₀, one_smul, map_inv₀, map_inv₀,
            RingHomCompTriple.comp_apply, RingHom.id_apply]
        _ = ‖d⁻¹ • (f x - d • y)‖ := by rw [mul_smul, smul_sub]
        _ = ‖d‖⁻¹ * ‖f x - d • y‖ := by rw [norm_smul, norm_inv]
        _ ≤ ‖d‖⁻¹ * (2 * δ) := by gcongr
        _ = 1 / 2 * ‖y‖ := by simp [δ, field]; norm_num
    rw [← dist_eq_norm] at J
    have K : ‖σ' d⁻¹ • x‖ ≤ (ε / 2)⁻¹ * ‖c‖ * 2 * ↑n * ‖y‖ :=
      calc
        ‖σ' d⁻¹ • x‖ = ‖d‖⁻¹ * ‖x₁ - x₂‖ := by rw [norm_smul, RingHomIsometric.norm_map, norm_inv]
        _ ≤ (ε / 2)⁻¹ * ‖c‖ * ‖y‖ * (n + n) := by
          gcongr
          · simpa using dinv
          · exact le_trans (norm_sub_le _ _) (by gcongr)
        _ = (ε / 2)⁻¹ * ‖c‖ * 2 * ↑n * ‖y‖ := by ring
    exact ⟨σ' d⁻¹ • x, J, K⟩

variable [CompleteSpace E]

section
include σ'

/-- The Banach open mapping theorem: if a bounded linear map between Banach spaces is onto, then
any point has a preimage with controlled norm. -/
/-
**ContinuousLinearMap.exists_preimage_norm_le** 是 Mathlib 中的一个定理，位于命名空间 `Continu
ousLinearMap`。
形式化陈述：exists_preimage_norm_le (surj : Surjective f) : exists C > 0, forall y, ex
ists x, f x = y ∧ ‖x‖ <= C * ‖y‖
参数：surj : Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ContinuousLinearMap.exists_approx_preimage_norm_le`：exists_approx_preima
ge_norm_le (surj : Surjective f) : exists C >= 0, forall y, exists x, dist (f x)
 y <= 1 / 2 * ‖y‖ ∧ ‖x‖ <= C * ‖y‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
（共 144 条，此处仅展示前 30 条）

--- 原说明 ---
The Banach open mapping theorem: if a bounded linear map between Banach spaces i
s onto, then
any point has a preimage with controlled norm.
-/
theorem exists_preimage_norm_le (surj : Surjective f) :
    ∃ C > 0, ∀ y, ∃ x, f x = y ∧ ‖x‖ ≤ C * ‖y‖ := by
  obtain ⟨C, C0, hC⟩ := exists_approx_preimage_norm_le f surj
  /- Second step of the proof: starting from `y`, we want an exact preimage of `y`. Let `g y` be
    the approximate preimage of `y` given by the first step, and `h y = y - f(g y)` the part that
    has no preimage yet. We will iterate this process, taking the approximate preimage of `h y`,
    leaving only `h^2 y` without preimage yet, and so on. Let `u n` be the approximate preimage
    of `h^n y`. Then `u` is a converging series, and by design the sum of the series is a
    preimage of `y`. This uses completeness of `E`. -/
  choose g hg using hC
  let h y := y - f (g y)
  have hle : ∀ y, ‖h y‖ ≤ 1 / 2 * ‖y‖ := by
    intro y
    rw [← dist_eq_norm, dist_comm]
    exact (hg y).1
  refine ⟨2 * C + 1, by linarith, fun y => ?_⟩
  have hnle : ∀ n : ℕ, ‖h^[n] y‖ ≤ (1 / 2) ^ n * ‖y‖ := by
    intro n
    induction n with
    | zero => simp only [one_div, one_mul, iterate_zero_apply, pow_zero, le_rfl]
    | succ n IH =>
      rw [iterate_succ']
      apply le_trans (hle _) _
      rw [pow_succ', mul_assoc]
      gcongr
  let u n := g (h^[n] y)
  have ule : ∀ n, ‖u n‖ ≤ (1 / 2) ^ n * (C * ‖y‖) := fun n ↦ by
    apply le_trans (hg _).2
    calc
      C * ‖h^[n] y‖ ≤ C * ((1 / 2) ^ n * ‖y‖) := by gcongr; exact hnle n
      _ = (1 / 2) ^ n * (C * ‖y‖) := by ring
  have sNu : Summable fun n => ‖u n‖ := by
    refine .of_nonneg_of_le (fun n => norm_nonneg _) ule ?_
    exact Summable.mul_right _ (summable_geometric_of_lt_one (by simp) (by norm_num))
  have su : Summable u := sNu.of_norm
  let x := tsum u
  have x_ineq : ‖x‖ ≤ (2 * C + 1) * ‖y‖ :=
    calc
      ‖x‖ ≤ ∑' n, ‖u n‖ := norm_tsum_le_tsum_norm sNu
      _ ≤ ∑' n, (1 / 2) ^ n * (C * ‖y‖) :=
        sNu.tsum_le_tsum ule <| Summable.mul_right _ summable_geometric_two
      _ = (∑' n, (1 / 2) ^ n) * (C * ‖y‖) := tsum_mul_right
      _ = 2 * C * ‖y‖ := by rw [tsum_geometric_two, mul_assoc]
      _ ≤ 2 * C * ‖y‖ + ‖y‖ := le_add_of_nonneg_right (norm_nonneg y)
      _ = (2 * C + 1) * ‖y‖ := by ring
  have fsumeq : ∀ n : ℕ, f (∑ i ∈ Finset.range n, u i) = y - h^[n] y := by
    intro n
    induction n with
    | zero => simp [f.map_zero]
    | succ n IH => rw [sum_range_succ, f.map_add, IH, iterate_succ_apply', sub_add]
  have : Tendsto (fun n => ∑ i ∈ Finset.range n, u i) atTop (𝓝 x) := su.hasSum.tendsto_sum_nat
  have L₁ : Tendsto (fun n => f (∑ i ∈ Finset.range n, u i)) atTop (𝓝 (f x)) :=
    (f.continuous.tendsto _).comp this
  simp only [fsumeq] at L₁
  have L₂ : Tendsto (fun n => y - h^[n] y) atTop (𝓝 (y - 0)) := by
    refine tendsto_const_nhds.sub ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) hnle ?_
    rw [← zero_mul ‖y‖]
    refine (_root_.tendsto_pow_atTop_nhds_zero_of_lt_one ?_ ?_).mul tendsto_const_nhds <;> norm_num
  have feq : f x = y - 0 := tendsto_nhds_unique L₁ L₂
  rw [sub_zero] at feq
  exact ⟨x, feq, x_ineq⟩

/-- The Banach open mapping theorem: a surjective bounded linear map between Banach spaces is
open. -/
/-
**ContinuousLinearMap.isOpenMap** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：∀ {𝕜 : Type u_1} {𝕜' : Type u_2} [inst : NontriviallyNormedField 𝕜] [inst_
1 : NontriviallyNormedField 𝕜'] {σ : 𝕜 →+* 𝕜'}   {E : Type u_3} [inst_2 : Normed
AddCommGroup E] [inst_3 : NormedSpace 𝕜 E] {F : Type u_4}   [inst_4 : NormedAddC
ommGroup F] [inst_5 : NormedSpace 𝕜' F] (f : E →SL[σ] F) {σ' : 𝕜' →+* 𝕜} [RingHo
mInvPair σ σ']   [RingHomIsometric σ] [RingHomIsometric σ'] [CompleteSpace F] [C
ompleteSpace E], Function.Surjective ⇑f → IsOpenMap ⇑f
参数：f : E →SL[σ] F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.exists_preimage_norm_le`：exists_preimage_norm_le (su
rj : Surjective f) : exists C > 0, forall y, exists x, f x = y ∧ ‖x‖ <= C * ‖y‖
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.isOpen_iff`：isOpen_iff : IsOpen s ↔ forall x in s, exists ε > 0, 
ball x ε subseteq s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.map_add`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : S
emiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_2 :
 TopologicalSpace…
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_self_add_left`：∀ {E : Type u_2} [inst : SeminormedAddGroup E] (a b 
: E), dist (b + a) b = ‖a‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_lt_mul_of_pos_left`：mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc
 : b < c) (ha : 0 < a) : a * b < a * c
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `Metric.mem_ball`：mem_ball : y in ball x ε ↔ dist y x < ε
· 使用引理 `mul_div_cancel₀`：mul_div_cancel₀ (a : G₀) (hb : b != 0) : b * (a / b) = 
a
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a

--- 原说明 ---
The Banach open mapping theorem: a surjective bounded linear map between Banach 
spaces is
open.
-/
protected theorem isOpenMap (surj : Surjective f) : IsOpenMap f := by
  intro s hs
  rcases exists_preimage_norm_le f surj with ⟨C, Cpos, hC⟩
  refine isOpen_iff.2 fun y yfs => ?_
  rcases yfs with ⟨x, xs, fxy⟩
  rcases isOpen_iff.1 hs x xs with ⟨ε, εpos, hε⟩
  refine ⟨ε / C, div_pos εpos Cpos, fun z hz => ?_⟩
  rcases hC (z - y) with ⟨w, wim, wnorm⟩
  have : f (x + w) = z := by rw [f.map_add, wim, fxy, add_sub_cancel]
  rw [← this]
  have : x + w ∈ ball x ε :=
    calc
      dist (x + w) x = ‖w‖ := by
        simp
      _ ≤ C * ‖z - y‖ := wnorm
      _ < C * (ε / C) := by
        apply mul_lt_mul_of_pos_left _ Cpos
        rwa [mem_ball, dist_eq_norm] at hz
      _ = ε := mul_div_cancel₀ _ (ne_of_gt Cpos)
  exact Set.mem_image_of_mem _ (hε this)
/-
**ContinuousLinearMap.isQuotientMap** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearM
ap`。
形式化陈述：isQuotientMap (surj : Surjective f) : IsQuotientMap f
参数：surj : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.isQuotientMap`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → Continuo
us f → Functi…
· 使用定理 `ContinuousLinearMap.isOpenMap`：∀ {𝕜 : Type u_1} {𝕜' : Type u_2} [inst : 
NontriviallyNormedField 𝕜] [inst_1 : NontriviallyNormedField 𝕜'] {σ : 𝕜 →+* 𝕜'} 
  {E : Type u_3} [i…
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
-/
theorem isQuotientMap (surj : Surjective f) : IsQuotientMap f :=
  (f.isOpenMap surj).isQuotientMap f.continuous surj

end

/-
**ContinuousLinearMap._root_.AffineMap.isOpenMap** 是 Mathlib 中的一个定理，位于命名空间 `Cont
inuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AffineMap.isOpenMap {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [CompleteSpace F] {P Q : Type*} [MetricSpace P] [NormedAddTorsor E P] [MetricSpace Q]
    [NormedAddTorsor F Q] (f : P →ᵃ[𝕜] Q) (hf : Continuous f) (surj : Surjective f) :
    IsOpenMap f :=
  AffineMap.isOpenMap_linear_iff.mp <|
    ContinuousLinearMap.isOpenMap { f.linear with cont := AffineMap.continuous_linear_iff.mpr hf }
      (f.linear_surjective_iff.mpr surj)

/-! ### Applications of the Banach open mapping theorem -/

section
include σ'

/-
**ContinuousLinearMap.interior_preimage** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLin
earMap`。
形式化陈述：interior_preimage (hsurj : Surjective f) (s : Set F) : interior (f ⁻¹' s) 
= f ⁻¹' interior s
参数：hsurj : Surjective f；s : Set F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOpenMap.preimage_interior_eq_interior_preimage`：∀ {X : Type u_1} {Y : 
Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],
   IsOpenMap f → Continuous f → ∀ (s :…
· 使用定理 `ContinuousLinearMap.isOpenMap`：∀ {𝕜 : Type u_1} {𝕜' : Type u_2} [inst : 
NontriviallyNormedField 𝕜] [inst_1 : NontriviallyNormedField 𝕜'] {σ : 𝕜 →+* 𝕜'} 
  {E : Type u_3} [i…
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
-/
theorem interior_preimage (hsurj : Surjective f) (s : Set F) :
    interior (f ⁻¹' s) = f ⁻¹' interior s :=
  ((f.isOpenMap hsurj).preimage_interior_eq_interior_preimage f.continuous s).symm
/-
**ContinuousLinearMap.closure_preimage** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：closure_preimage (hsurj : Surjective f) (s : Set F) : closure (f ⁻¹' s) = 
f ⁻¹' closure s
参数：hsurj : Surjective f；s : Set F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOpenMap.preimage_closure_eq_closure_preimage`：∀ {X : Type u_1} {Y : Ty
pe u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],  
 IsOpenMap f → Continuous f → ∀ (s :…
· 使用定理 `ContinuousLinearMap.isOpenMap`：∀ {𝕜 : Type u_1} {𝕜' : Type u_2} [inst : 
NontriviallyNormedField 𝕜] [inst_1 : NontriviallyNormedField 𝕜'] {σ : 𝕜 →+* 𝕜'} 
  {E : Type u_3} [i…
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
-/
theorem closure_preimage (hsurj : Surjective f) (s : Set F) : closure (f ⁻¹' s) = f ⁻¹' closure s :=
  ((f.isOpenMap hsurj).preimage_closure_eq_closure_preimage f.continuous s).symm
/-
**ContinuousLinearMap.frontier_preimage** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLin
earMap`。
形式化陈述：frontier_preimage (hsurj : Surjective f) (s : Set F) : frontier (f ⁻¹' s) 
= f ⁻¹' frontier s
参数：hsurj : Surjective f；s : Set F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOpenMap.preimage_frontier_eq_frontier_preimage`：∀ {X : Type u_1} {Y : 
Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],
   IsOpenMap f → Continuous f → ∀ (s :…
· 使用定理 `ContinuousLinearMap.isOpenMap`：∀ {𝕜 : Type u_1} {𝕜' : Type u_2} [inst : 
NontriviallyNormedField 𝕜] [inst_1 : NontriviallyNormedField 𝕜'] {σ : 𝕜 →+* 𝕜'} 
  {E : Type u_3} [i…
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
-/
theorem frontier_preimage (hsurj : Surjective f) (s : Set F) :
    frontier (f ⁻¹' s) = f ⁻¹' frontier s :=
  ((f.isOpenMap hsurj).preimage_frontier_eq_frontier_preimage f.continuous s).symm
/-
**ContinuousLinearMap.exists_nonlinearRightInverse_of_surjective** 是 Mathlib 中的一
个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：exists_nonlinearRightInverse_of_surjective (f : E ->SL[σ] F) (hsurj : f.ra
nge = ⊤) : exists fsymm : NonlinearRightInverse f, 0 < fsymm.nnnorm
参数：f : E ->SL[σ] F；hsurj : f.range = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `GT.gt.lt`：∀ {α : Type u_2} [inst : LT α] {a b : α}, a > b → b < a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `ContinuousLinearMap.exists_preimage_norm_le`：exists_preimage_norm_le (su
rj : Surjective f) : exists C > 0, forall y, exists x, f x = y ∧ ‖x‖ <= C * ‖y‖
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
-/
theorem exists_nonlinearRightInverse_of_surjective (f : E →SL[σ] F) (hsurj : f.range = ⊤) :
    ∃ fsymm : NonlinearRightInverse f, 0 < fsymm.nnnorm := by
  choose C hC fsymm h using
    exists_preimage_norm_le _ (LinearMap.range_eq_top.1 hsurj)
  use {
      toFun := fsymm
      nnnorm := ⟨C, hC.lt.le⟩
      bound' := fun y => (h y).2
      right_inv' := fun y => (h y).1 }
  exact hC

end

/-- A surjective continuous linear map between Banach spaces admits a (possibly nonlinear)
controlled right inverse. In general, it is not possible to ensure that such a right inverse
is linear (take for instance the map from `E` to `E/F` where `F` is a closed subspace of `E`
without a closed complement. Then it doesn't have a continuous linear right inverse.) -/
noncomputable irreducible_def nonlinearRightInverseOfSurjective (f : E →SL[σ] F)
  (hsurj : f.range = ⊤) : NonlinearRightInverse f :=
  Classical.choose (exists_nonlinearRightInverse_of_surjective f hsurj)

/-
**ContinuousLinearMap.nonlinearRightInverseOfSurjective_nnnorm_pos** 是 Mathlib 中
的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：nonlinearRightInverseOfSurjective_nnnorm_pos (f : E ->SL[σ] F) (hsurj : f.
range = ⊤) : 0 < (nonlinearRightInverseOfSurjective f hsurj).nnnorm
参数：f : E ->SL[σ] F；hsurj : f.range = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `ContinuousLinearMap.exists_nonlinearRightInverse_of_surjective`：exists_n
onlinearRightInverse_of_surjective (f : E ->SL[σ] F) (hsurj : f.range = ⊤) : exi
sts fsymm : NonlinearRightInverse f, 0 < fsymm.nnnor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.nonlinearRightInverseOfSurjective_def`：∀ {𝕜 : Type u
_5} {𝕜' : Type u_6} [inst : NontriviallyNormedField 𝕜] [inst_1 : NontriviallyNor
medField 𝕜'] {σ : 𝕜 →+* 𝕜'}   {E : Type u_7} [i…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem nonlinearRightInverseOfSurjective_nnnorm_pos (f : E →SL[σ] F) (hsurj : f.range = ⊤) :
    0 < (nonlinearRightInverseOfSurjective f hsurj).nnnorm := by
  rw [nonlinearRightInverseOfSurjective]
  exact Classical.choose_spec (exists_nonlinearRightInverse_of_surjective f hsurj)

end ContinuousLinearMap

namespace LinearEquiv

variable [CompleteSpace E] [RingHomInvPair σ' σ]

/-- If a bounded linear map is a bijection, then its inverse is also a bounded linear map. -/
@[continuity]
/-
**LinearEquiv.continuous_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：continuous_symm (e : E ≃ₛₗ[σ] F) (h : Continuous e) : Continuous e.symm
参数：e : E ≃ₛₗ[σ] F；h : Continuous e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuous_def`：continuous_def {_ : TopologicalSpace X} {_ : Topological
Space Y} {f : X -> Y} : Continuous f ↔ forall s, IsOpen s -> IsOpen (f ⁻¹' s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.image_eq_preimage_symm`：∀ {R : Type u_1} {S : Type u_6} {M :
 Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 :
 AddCommMonoid M] [inst_…
· 使用定理 `LinearEquiv.coe_coe`：coe_coe : ⇑(e : M ->ₛₗ[σ] M₂) = e
· 使用定理 `ContinuousLinearMap.isOpenMap`：∀ {𝕜 : Type u_1} {𝕜' : Type u_2} [inst : 
NontriviallyNormedField 𝕜] [inst_1 : NontriviallyNormedField 𝕜'] {σ : 𝕜 →+* 𝕜'} 
  {E : Type u_3} [i…
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…

--- 原说明 ---
If a bounded linear map is a bijection, then its inverse is also a bounded linea
r map.
-/
theorem continuous_symm (e : E ≃ₛₗ[σ] F) (h : Continuous e) : Continuous e.symm := by
  rw [continuous_def]
  intro s hs
  rw [← e.image_eq_preimage_symm]
  rw [← e.coe_coe] at h ⊢
  exact ContinuousLinearMap.isOpenMap (σ := σ) ⟨_, h⟩ e.surjective s hs

/-- Associating to a linear equivalence between Banach spaces a continuous linear equivalence when
the direct map is continuous, thanks to the Banach open mapping theorem that ensures that the
inverse map is also continuous. -/
/-
**LinearEquiv.toContinuousLinearEquivOfContinuous** 是 Mathlib 中的一个定义，位于命名空间 `Lin
earEquiv`。
形式化陈述：toContinuousLinearEquivOfContinuous (e : E ≃ₛₗ[σ] F) (h : Continuous e) : 
E ≃SL[σ] F
参数：e : E ≃ₛₗ[σ] F；h : Continuous e。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.continuous_symm`：continuous_symm (e : E ≃ₛₗ[σ] F) (h : Conti
nuous e) : Continuous e.symm

--- 原说明 ---
Associating to a linear equivalence between Banach spaces a continuous linear eq
uivalence when
the direct map is continuous, thanks to the Banach open mapping theorem that ens
ures that the
inverse map is also continuous.
-/
def toContinuousLinearEquivOfContinuous (e : E ≃ₛₗ[σ] F) (h : Continuous e) : E ≃SL[σ] F :=
  { e with
    continuous_toFun := h
    continuous_invFun := e.continuous_symm h }

@[simp]
/-
**LinearEquiv.coeFn_toContinuousLinearEquivOfContinuous** 是 Mathlib 中的一个定理，位于命名空
间 `LinearEquiv`。
形式化陈述：coeFn_toContinuousLinearEquivOfContinuous (e : E ≃ₛₗ[σ] F) (h : Continuous
 e) : ⇑(e.toContinuousLinearEquivOfContinuous h) = e
参数：e : E ≃ₛₗ[σ] F；h : Continuous e。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeFn_toContinuousLinearEquivOfContinuous (e : E ≃ₛₗ[σ] F) (h : Continuous e) :
    ⇑(e.toContinuousLinearEquivOfContinuous h) = e :=
  rfl

@[simp]
/-
**LinearEquiv.coeFn_toContinuousLinearEquivOfContinuous_symm** 是 Mathlib 中的一个定理，
位于命名空间 `LinearEquiv`。
形式化陈述：coeFn_toContinuousLinearEquivOfContinuous_symm (e : E ≃ₛₗ[σ] F) (h : Conti
nuous e) : ⇑(e.toContinuousLinearEquivOfContinuous h).symm = e.symm
参数：e : E ≃ₛₗ[σ] F；h : Continuous e。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeFn_toContinuousLinearEquivOfContinuous_symm (e : E ≃ₛₗ[σ] F) (h : Continuous e) :
    ⇑(e.toContinuousLinearEquivOfContinuous h).symm = e.symm :=
  rfl

end LinearEquiv

namespace ContinuousLinearMap

variable [CompleteSpace E] [RingHomInvPair σ' σ] {f : E →SL[σ] F}

/-- An injective continuous linear map with a closed range defines a continuous linear equivalence
between its domain and its range. -/
/-
**ContinuousLinearMap.equivRange** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`
。
形式化陈述：equivRange (hinj : Injective f) (hclo : IsClosed (range f)) : E ≃SL[σ] f.r
ange
参数：hinj : Injective f；hclo : IsClosed (range f)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An injective continuous linear map with a closed range defines a continuous line
ar equivalence
between its domain and its range.
-/
noncomputable def equivRange (hinj : Injective f) (hclo : IsClosed (range f)) :
    E ≃SL[σ] f.range :=
  have : CompleteSpace f.range := hclo.completeSpace_coe
  LinearEquiv.toContinuousLinearEquivOfContinuous (LinearEquiv.ofInjective f.toLinearMap hinj) <|
    (f.continuous.codRestrict fun x ↦ f.mem_range_self x).congr fun _ ↦ rfl

@[simp]
/-
**ContinuousLinearMap.coe_linearMap_equivRange** 是 Mathlib 中的一个定理，位于命名空间 `Contin
uousLinearMap`。
形式化陈述：coe_linearMap_equivRange (hinj : Injective f) (hclo : IsClosed (range f)) 
: f.equivRange hinj hclo = f.rangeRestrict
参数：hinj : Injective f；hclo : IsClosed (range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
-/
theorem coe_linearMap_equivRange (hinj : Injective f) (hclo : IsClosed (range f)) :
    f.equivRange hinj hclo = f.rangeRestrict :=
  rfl

@[simp]
/-
**ContinuousLinearMap.coe_equivRange** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：coe_equivRange (hinj : Injective f) (hclo : IsClosed (range f)) : (f.equiv
Range hinj hclo : E -> f.range) = f.rangeRestrict
参数：hinj : Injective f；hclo : IsClosed (range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
-/
theorem coe_equivRange (hinj : Injective f) (hclo : IsClosed (range f)) :
    (f.equivRange hinj hclo : E → f.range) = f.rangeRestrict :=
  rfl

@[simp]
/-
**ContinuousLinearMap.equivRange_symm_toLinearEquiv** 是 Mathlib 中的一个引理，位于命名空间 `C
ontinuousLinearMap`。
形式化陈述：equivRange_symm_toLinearEquiv (hinj : Injective f) (hclo : IsClosed (range
 f)) : (f.equivRange hinj hclo).toLinearEquiv.symm = (LinearEquiv.ofInjective f.
toLinearMap hinj).symm
参数：hinj : Injective f；hclo : IsClosed (range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
-/
lemma equivRange_symm_toLinearEquiv (hinj : Injective f) (hclo : IsClosed (range f)) :
    (f.equivRange hinj hclo).toLinearEquiv.symm =
      (LinearEquiv.ofInjective f.toLinearMap hinj).symm := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**ContinuousLinearMap.equivRange_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Continuou
sLinearMap`。
形式化陈述：equivRange_symm_apply (hinj : Injective f) (hclo : IsClosed (range f)) (x 
: E) : (f.equivRange hinj hclo).symm ⟨f x, by simp⟩ = x
参数：hinj : Injective f；hclo : IsClosed (range f)；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equivRange_symm_apply (hinj : Injective f) (hclo : IsClosed (range f))
    (x : E) : (f.equivRange hinj hclo).symm ⟨f x, by simp⟩ = x := by
  simp [ContinuousLinearEquiv.symm_apply_eq, Subtype.ext_iff]

section

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [CompleteSpace E] [CompleteSpace F]

-- TODO: once mathlib has Fredholm operators, generalise the next four lemmas accordingly

/-- If `f : E →L[𝕜] F` is injective with closed range (and `E` and `F` are Banach spaces),
`f` is anti-Lipschitz. -/
/-
**ContinuousLinearMap.antilipschitz_of_injective_of_isClosed_range** 是 Mathlib 中
的一个引理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：antilipschitz_of_injective_of_isClosed_range (f : E ->L[𝕜] F) (hf : Inject
ive f) (hf' : IsClosed (Set.range f)) : exists K, AntilipschitzWith K f
参数：f : E ->L[𝕜] F；hf : Injective f；hf' : IsClosed (Set.range f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `AntilipschitzWith.comp`：comp {Kg : Real>=0} {g : β -> γ} (hg : Antilipsc
hitzWith Kg g) {Kf : Real>=0} {f : α -> β} (hf : AntilipschitzWith Kf f) : Antil
ipschitzWith…
· 使用定理 `AntilipschitzWith.subtype_coe`：subtype_coe (s : Set α) : AntilipschitzWi
th 1 ((↑) : s -> α)
· 使用定理 `ContinuousLinearEquiv.antilipschitz`：∀ {𝕜 : Type u_1} {𝕜₂ : Type u_3} {E
 : Type u_5} {F : Type u_6} [inst : NormedAddCommGroup E]   [inst_1 : NormedAddC
ommGroup F] [inst_2 : Non…

--- 原说明 ---
If `f : E →L[𝕜] F` is injective with closed range (and `E` and `F` are Banach sp
aces),
`f` is anti-Lipschitz.
-/
lemma antilipschitz_of_injective_of_isClosed_range (f : E →L[𝕜] F)
    (hf : Injective f) (hf' : IsClosed (Set.range f)) : ∃ K, AntilipschitzWith K f :=
  ⟨_, .comp (.subtype_coe (Set.range f)) (f.equivRange hf hf').antilipschitz⟩

/-- A choice of anti-Lipschitz constant for `f : E →L[𝕜] F` injective with closed range
(assuming `E` and `F` are Banach spaces). -/
/-
**ContinuousLinearMap.antilipschitzConstant_of_injective_of_isClosed_range** 是 M
athlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：antilipschitzConstant_of_injective_of_isClosed_range (f : E ->L[𝕜] F) (hf 
: Injective f) (hf' : IsClosed (Set.range f)) : Real>=0
参数：f : E ->L[𝕜] F；hf : Injective f；hf' : IsClosed (Set.range f)。
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousLinearMap.antilipschitz_of_injective_of_isClosed_range`：antili
pschitz_of_injective_of_isClosed_range (f : E ->L[𝕜] F) (hf : Injective f) (hf' 
: IsClosed (Set.range f)) : exists K, AntilipschitzWit…

--- 原说明 ---
A choice of anti-Lipschitz constant for `f : E →L[𝕜] F` injective with closed ra
nge
(assuming `E` and `F` are Banach spaces).
-/
noncomputable def antilipschitzConstant_of_injective_of_isClosed_range (f : E →L[𝕜] F)
    (hf : Injective f) (hf' : IsClosed (Set.range f)) : ℝ≥0 :=
  Classical.choose (f.antilipschitz_of_injective_of_isClosed_range hf hf')
/-
**ContinuousLinearMap.antilipschitz_antiLipschitzConstant_of_injective_of_isClos
ed_range** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：antilipschitz_antiLipschitzConstant_of_injective_of_isClosed_range (f : E 
->L[𝕜] F) (hf : Injective f) (hf' : IsClosed (Set.range f)) : AntilipschitzWith 
(f.antilipschitzConstant_of_injective_of_isClosed_range hf hf') f
参数：f : E ->L[𝕜] F；hf : Injective f；hf' : IsClosed (Set.range f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用引理 `ContinuousLinearMap.antilipschitz_of_injective_of_isClosed_range`：antili
pschitz_of_injective_of_isClosed_range (f : E ->L[𝕜] F) (hf : Injective f) (hf' 
: IsClosed (Set.range f)) : exists K, AntilipschitzWit…
-/
lemma antilipschitz_antiLipschitzConstant_of_injective_of_isClosed_range (f : E →L[𝕜] F)
    (hf : Injective f) (hf' : IsClosed (Set.range f)) :
    AntilipschitzWith (f.antilipschitzConstant_of_injective_of_isClosed_range hf hf') f :=
  Classical.choose_spec (f.antilipschitz_of_injective_of_isClosed_range hf hf')

/-- An injective bounded linear operator between Banach spaces has closed range
iff it is anti-Lipschitz. -/
/-
**ContinuousLinearMap.isClosed_range_iff_antilipschitz_of_injective** 是 Mathlib 
中的一个引理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：isClosed_range_iff_antilipschitz_of_injective (f : E ->L[𝕜] F) (hf : Injec
tive f) : IsClosed (Set.range f) ↔ exists K, AntilipschitzWith K f
参数：f : E ->L[𝕜] F；hf : Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousLinearMap.antilipschitz_of_injective_of_isClosed_range`：antili
pschitz_of_injective_of_isClosed_range (f : E ->L[𝕜] F) (hf : Injective f) (hf' 
: IsClosed (Set.range f)) : exists K, AntilipschitzWit…
· 使用定理 `AntilipschitzWith.isClosed_range`：isClosed_range {α β : Type*} [PseudoEM
etricSpace α] [EMetricSpace β] [CompleteSpace α] {f : α -> β} {K : Real>=0} (hf 
: AntilipschitzWith K …
· 使用定理 `ContinuousLinearMap.uniformContinuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2}
 [inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {E₁ : Type u_9}  
 {E₂ : Type u_10} [inst_2 :…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
An injective bounded linear operator between Banach spaces has closed range
iff it is anti-Lipschitz.
-/
lemma isClosed_range_iff_antilipschitz_of_injective (f : E →L[𝕜] F)
    (hf : Injective f) : IsClosed (Set.range f) ↔ ∃ K, AntilipschitzWith K f := by
  refine ⟨fun h ↦ f.antilipschitz_of_injective_of_isClosed_range hf h, fun h ↦ ?_⟩
  choose K hf' using h
  exact hf'.isClosed_range f.uniformContinuous

/-- A choice of continuous left inverse of an injective continuous linear map with closed range:
this is `LinearMap.leftInverse` as a continuous linear map;
by injectivity, the junk value of `leftInverse` never matters, and continuity of the inverse
follows form the closed range condition. -/
/-
**ContinuousLinearMap.leftInverse_of_injective_of_isClosed_range** 是 Mathlib 中的一
个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：leftInverse_of_injective_of_isClosed_range (f : E ->L[𝕜] F) (hf : Injectiv
e f) (hf' : IsClosed (range f)) : f.range ->L[𝕜] E
参数：f : E ->L[𝕜] F；hf : Injective f；hf' : IsClosed (range f)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A choice of continuous left inverse of an injective continuous linear map with c
losed range:
this is `LinearMap.leftInverse` as a continuous linear map;
by injectivity, the junk value of `leftInverse` never matters, and continuity of
 the inverse
follows form the closed range condition.
-/
noncomputable def leftInverse_of_injective_of_isClosed_range
    (f : E →L[𝕜] F) (hf : Injective f) (hf' : IsClosed (range f)) : f.range →L[𝕜] E :=
  letI K := f.antilipschitzConstant_of_injective_of_isClosed_range hf hf'
  letI hfK := f.antilipschitz_antiLipschitzConstant_of_injective_of_isClosed_range hf hf'
  LinearMap.mkContinuous f.rangeRestrict.leftInverse K (by
    rintro ⟨y, x, rfl⟩
    have aux := hfK.le_mul_dist x 0
    simp only [dist_zero_right, map_zero] at aux
    convert! aux
    exact f.rangeRestrict.leftInverse_apply_of_inj
      (by rw [ker_codRestrict]; exact LinearMap.ker_eq_bot.mpr hf) x)

end

end ContinuousLinearMap

namespace ContinuousLinearEquiv

variable [CompleteSpace E] [RingHomInvPair σ' σ]

/-- Convert a bijective continuous linear map `f : E →SL[σ] F` from a Banach space to a normed space
to a continuous linear equivalence. -/
/-
**ContinuousLinearEquiv.ofBijective** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearE
quiv`。
形式化陈述：ofBijective (f : E ->SL[σ] F) (hinj : f.ker = ⊥) (hsurj : f.range = ⊤) : E
 ≃SL[σ] F
参数：f : E ->SL[σ] F；hinj : f.ker = ⊥；hsurj : f.range = ⊤。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert a bijective continuous linear map `f : E →SL[σ] F` from a Banach space t
o a normed space
to a continuous linear equivalence.
-/
noncomputable def ofBijective (f : E →SL[σ] F) (hinj : f.ker = ⊥) (hsurj : f.range = ⊤) :
    E ≃SL[σ] F :=
  (LinearEquiv.ofBijective f
        ⟨LinearMap.ker_eq_bot.mp hinj,
          LinearMap.range_eq_top.mp hsurj⟩).toContinuousLinearEquivOfContinuous
    -- Porting note: `by exact` was not previously needed. Why is it needed now?
    (by exact f.continuous)

@[simp]
/-
**ContinuousLinearEquiv.coeFn_ofBijective** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousL
inearEquiv`。
形式化陈述：coeFn_ofBijective (f : E ->SL[σ] F) (hinj : f.ker = ⊥) (hsurj : f.range = 
⊤) : ⇑(ofBijective f hinj hsurj) = f
参数：f : E ->SL[σ] F；hinj : f.ker = ⊥；hsurj : f.range = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
-/
theorem coeFn_ofBijective (f : E →SL[σ] F) (hinj : f.ker = ⊥) (hsurj : f.range = ⊤) :
    ⇑(ofBijective f hinj hsurj) = f :=
  rfl
/-
**ContinuousLinearEquiv.coe_ofBijective** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLin
earEquiv`。
形式化陈述：coe_ofBijective (f : E ->SL[σ] F) (hinj : f.ker = ⊥) (hsurj : f.range = ⊤)
 : ↑(ofBijective f hinj hsurj) = f
参数：f : E ->SL[σ] F；hinj : f.ker = ⊥；hsurj : f.range = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
-/
theorem coe_ofBijective (f : E →SL[σ] F) (hinj : f.ker = ⊥) (hsurj : f.range = ⊤) :
    ↑(ofBijective f hinj hsurj) = f := by
  ext
  rfl

@[simp]
/-
**ContinuousLinearEquiv.ofBijective_symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `
ContinuousLinearEquiv`。
形式化陈述：ofBijective_symm_apply_apply (f : E ->SL[σ] F) (hinj : f.ker = ⊥) (hsurj :
 f.range = ⊤) (x : E) : (ofBijective f hinj hsurj).symm (f x) = x
参数：f : E ->SL[σ] F；hinj : f.ker = ⊥；hsurj : f.range = ⊤；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `ContinuousLinearEquiv.symm_apply_apply`：symm_apply_apply (e : M₁ ≃SL[σ₁₂
] M₂) (b : M₁) : e.symm (e b) = b
-/
theorem ofBijective_symm_apply_apply (f : E →SL[σ] F) (hinj : f.ker = ⊥) (hsurj : f.range = ⊤)
    (x : E) : (ofBijective f hinj hsurj).symm (f x) = x :=
  (ofBijective f hinj hsurj).symm_apply_apply x

@[simp]
/-
**ContinuousLinearEquiv.ofBijective_apply_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `
ContinuousLinearEquiv`。
形式化陈述：ofBijective_apply_symm_apply (f : E ->SL[σ] F) (hinj : f.ker = ⊥) (hsurj :
 f.range = ⊤) (y : F) : f ((ofBijective f hinj hsurj).symm y) = y
参数：f : E ->SL[σ] F；hinj : f.ker = ⊥；hsurj : f.range = ⊤；y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `ContinuousLinearEquiv.apply_symm_apply`：apply_symm_apply (e : M₁ ≃SL[σ₁₂
] M₂) (c : M₂) : e (e.symm c) = c
-/
theorem ofBijective_apply_symm_apply (f : E →SL[σ] F) (hinj : f.ker = ⊥)
    (hsurj : f.range = ⊤) (y : F) : f ((ofBijective f hinj hsurj).symm y) = y :=
  (ofBijective f hinj hsurj).apply_symm_apply y
/-
**ContinuousLinearEquiv._root_.ContinuousLinearMap.isUnit_iff_bijective** 是 Math
lib 中的一个引理，位于命名空间 `ContinuousLinearEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ContinuousLinearMap.isUnit_iff_bijective {f : E →L[𝕜] E} :
    IsUnit f ↔ Bijective f := by
  constructor
  · rintro ⟨f, rfl⟩
    exact ofUnit f |>.bijective
  · refine fun h ↦ ⟨toUnit <| .ofBijective f ?_ ?_, rfl⟩ <;>
    simp only [LinearMap.range_eq_top, LinearMap.ker_eq_bot, f.coe_coe, h.1, h.2]

end ContinuousLinearEquiv

namespace ContinuousLinearMap

variable [CompleteSpace E]

/--
A continuous linear endomorphism is a unit iff it's a unit viewed simply as a linear map, provided
the space is complete.
-/
/-
**ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `C
ontinuousLinearMap`。
形式化陈述：isUnit_iff_isUnit_toLinearMap {f : E ->L[𝕜] E} : IsUnit f ↔ IsUnit (f : E 
->ₗ[𝕜] E)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousLinearMap.isUnit_iff_bijective`：∀ {𝕜 : Type u_1} [inst : Nontr
iviallyNormedField 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 :
 NormedSpace 𝕜 E] [CompleteSpa…
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Module.End.isUnit_iff`：∀ {R : Type u_1} {M : Type u_5} [inst : Semiring 
R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (f : Module.End R M
), IsUnit f…

--- 原说明 ---
A continuous linear endomorphism is a unit iff it's a unit viewed simply as a li
near map, provided
the space is complete.
-/
theorem isUnit_iff_isUnit_toLinearMap {f : E →L[𝕜] E} :
    IsUnit f ↔ IsUnit (f : E →ₗ[𝕜] E) :=
  f.isUnit_iff_bijective.trans (Module.End.isUnit_iff _).symm

/--
The spectrum of a continuous linear map `f` over a Banach space is exactly the spectrum of `f`
viewed as a mere linear map.
-/
/-
**ContinuousLinearMap.spectrum_eq** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：spectrum_eq {f : E ->L[𝕜] E} : spectrum 𝕜 f = spectrum 𝕜 (f : Module.End 𝕜
 E)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
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
· 使用定理 `spectrum.mem_iff`：mem_iff {r : R} {a : A} : r in σ a ↔ ¬IsUnit (↑ₐ r - a
)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap`：isUnit_iff_isUnit_toL
inearMap {f : E ->L[𝕜] E} : IsUnit f ↔ IsUnit (f : E ->ₗ[𝕜] E)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The spectrum of a continuous linear map `f` over a Banach space is exactly the s
pectrum of `f`
viewed as a mere linear map.
-/
theorem spectrum_eq {f : E →L[𝕜] E} :
    spectrum 𝕜 f = spectrum 𝕜 (f : Module.End 𝕜 E) := by
  ext μ
  rw [spectrum.mem_iff, spectrum.mem_iff, ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap]
  rfl

/-- Intermediate definition used to show
`ContinuousLinearMap.closed_complemented_range_of_isCompl_of_ker_eq_bot`.

This is `f.coprod G.subtypeL` as a `ContinuousLinearEquiv`. -/
/-
**ContinuousLinearMap.coprodSubtypeLEquivOfIsCompl** 是 Mathlib 中的一个定义，位于命名空间 `Co
ntinuousLinearMap`。
形式化陈述：coprodSubtypeLEquivOfIsCompl {F : Type*} [NormedAddCommGroup F] [NormedSpa
ce 𝕜 F] [CompleteSpace F] (f : E ->L[𝕜] F) {G : Submodule 𝕜 F} (h : IsCompl f.ra
nge G) [CompleteSpace G] (hker : f.ker = ⊥) : (E × G) ≃L[𝕜] F
参数：f : E ->L[𝕜] F；h : IsCompl f.range G；hker : f.ker = ⊥。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Intermediate definition used to show
`ContinuousLinearMap.closed_complemented_range_of_isCompl_of_ker_eq_bot`.

This is `f.coprod G.subtypeL` as a `ContinuousLinearEquiv`.
-/
noncomputable def coprodSubtypeLEquivOfIsCompl {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [CompleteSpace F] (f : E →L[𝕜] F) {G : Submodule 𝕜 F}
    (h : IsCompl f.range G) [CompleteSpace G] (hker : f.ker = ⊥) : (E × G) ≃L[𝕜] F :=
  ContinuousLinearEquiv.ofBijective (f.coprod G.subtypeL)
    (by
      rw [ker_coprod_of_disjoint_range]
      · simp [hker]
      · simp [h.disjoint])
    (by simp [LinearMap.range_coprod, h.sup_eq_top])
/-
**ContinuousLinearMap.range_eq_map_coprodSubtypeLEquivOfIsCompl** 是 Mathlib 中的一个
定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：range_eq_map_coprodSubtypeLEquivOfIsCompl {F : Type*} [NormedAddCommGroup 
F] [NormedSpace 𝕜 F] [CompleteSpace F] (f : E ->L[𝕜] F) {G : Submodule 𝕜 F} (h :
 IsCompl f.range G) [CompleteSpace G] (hker : f.ker = ⊥) : f.range = ((⊤ : Submo
dule 𝕜 E).prod (⊥ : Submodule 𝕜 G)).map (f.coprodSubtypeLEquivOfIsCompl h hker :
 E × G ->ₗ[𝕜] F)
参数：f : E ->L[𝕜] F；h : IsCompl f.range G；hker : f.ker = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.coprodSubtypeLEquivOfIsCompl.eq_1`：∀ {𝕜 : Type u_1} 
[inst : NontriviallyNormedField 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E
]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : Co…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap`：∀ {R₁ : Type u_
1} {R₂ : Type u_2} [inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂}
 {σ₂₁ : R₂ →+* R₁}   [inst_2 : RingHomInvPair…
· 使用定理 `ContinuousLinearEquiv.coe_ofBijective`：coe_ofBijective (f : E ->SL[σ] F)
 (hinj : f.ker = ⊥) (hsurj : f.range = ⊤) : ↑(ofBijective f hinj hsurj) = f
· 使用定理 `ContinuousLinearMap.coe_coprod`：∀ {R : Type u_1} {M : Type u_3} {M₁ : Ty
pe u_5} {M₂ : Type u_6} [inst : Semiring R] [inst_1 : TopologicalSpace M]   [ins
t_2 : TopologicalSpa…
· 使用定理 `LinearMap.coprod_map_prod`：coprod_map_prod (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ
[R] M₃) (S : Submodule R M) (S' : Submodule R M₂) : (Submodule.prod S S').map (L
inearMap.coprod…
· 使用定理 `Submodule.map_bot`：map_bot (f : M ->ₛₗ[σ₁₂] M₂) : map f ⊥ = ⊥
· 使用定理 `sup_bot_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), a ⊔ ⊥ = a
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
-/
theorem range_eq_map_coprodSubtypeLEquivOfIsCompl {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [CompleteSpace F] (f : E →L[𝕜] F) {G : Submodule 𝕜 F}
    (h : IsCompl f.range G) [CompleteSpace G] (hker : f.ker = ⊥) :
    f.range =
      ((⊤ : Submodule 𝕜 E).prod (⊥ : Submodule 𝕜 G)).map
        (f.coprodSubtypeLEquivOfIsCompl h hker : E × G →ₗ[𝕜] F) := by
  rw [coprodSubtypeLEquivOfIsCompl, ← ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap,
    ContinuousLinearEquiv.coe_ofBijective, coe_coprod, LinearMap.coprod_map_prod, Submodule.map_bot,
    sup_bot_eq, Submodule.map_top]

/- TODO: remove the assumption `f.ker = ⊥` in the next lemma, by using the map induced by `f` on
`E / f.ker`, once we have quotient normed spaces. -/
/-
**ContinuousLinearMap.closed_complemented_range_of_isCompl_of_ker_eq_bot** 是 Mat
hlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：closed_complemented_range_of_isCompl_of_ker_eq_bot {F : Type*} [NormedAddC
ommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F] (f : E ->L[𝕜] F) (G : Submodule 
𝕜 F) (h : IsCompl f.range G) (hG : IsClosed (G : Set F)) (hker : f.ker = ⊥) : Is
Closed (f.range : Set F)
参数：f : E ->L[𝕜] F；G : Submodule 𝕜 F；h : IsCompl f.range G；hG : IsClosed (G : Set
 F)；hker : f.ker = ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.range_eq_map_coprodSubtypeLEquivOfIsCompl`：range_eq_
map_coprodSubtypeLEquivOfIsCompl {F : Type*} [NormedAddCommGroup F] [NormedSpace
 𝕜 F] [CompleteSpace F] (f : E ->L[𝕜] F) {G : Submo…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Homeomorph.isClosed_image`：isClosed_image (h : X ≃ₜ Y) {s : Set X} : IsC
losed (h '' s) ↔ IsClosed s
· 使用定理 `IsClosed.prod`：IsClosed.prod {s₁ : Set X} {s₂ : Set Y} (h₁ : IsClosed s₁
) (h₂ : IsClosed s₂) : IsClosed (s₁ ×ˢ s₂)
· 使用定理 `isClosed_univ`：isClosed_univ : IsClosed (univ : Set X)
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α

--- 原说明 ---
TODO: remove the assumption `f.ker = ⊥` in the next lemma, by using the map indu
ced by `f` on
`E / f.ker`, once we have quotient normed spaces.
-/
theorem closed_complemented_range_of_isCompl_of_ker_eq_bot {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [CompleteSpace F] (f : E →L[𝕜] F) (G : Submodule 𝕜 F)
    (h : IsCompl f.range G) (hG : IsClosed (G : Set F)) (hker : f.ker = ⊥) :
    IsClosed (f.range : Set F) := by
  have : CompleteSpace G := hG.completeSpace_coe
  let g := coprodSubtypeLEquivOfIsCompl f h hker
  rw [range_eq_map_coprodSubtypeLEquivOfIsCompl f h hker]
  apply g.toHomeomorph.isClosed_image.2
  exact isClosed_univ.prod isClosed_singleton

end ContinuousLinearMap

section ClosedGraphThm

variable [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F] (g : E →ₗ[𝕜] F)

/-- The **closed graph theorem** : a linear map between two Banach spaces whose graph is closed
is continuous. -/
/-
**LinearMap.continuous_of_isClosed_graph** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.continuous_of_isClosed_graph (hg : IsClosed (g.graph : Set <| E 
× F)) : Continuous g
参数：hg : IsClosed (g.graph : Set <| E × F)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `completeSpace_coe_iff_isComplete`：completeSpace_coe_iff_isComplete {s : 
Set α} : CompleteSpace s ↔ IsComplete s
· 使用定理 `IsClosed.isComplete`：IsClosed.isComplete [CompleteSpace α] {s : Set α} (
h : IsClosed s) : IsComplete s
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.graph_eq_range_prod`：graph_eq_range_prod : f.graph = range (Li
nearMap.id.prod f)
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ContinuousLinearEquiv.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [ins
t : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [i
nst_2 : RingHomInvPair…

--- 原说明 ---
The **closed graph theorem** : a linear map between two Banach spaces whose grap
h is closed
is continuous.
-/
theorem LinearMap.continuous_of_isClosed_graph (hg : IsClosed (g.graph : Set <| E × F)) :
    Continuous g := by
  let : CompleteSpace g.graph := completeSpace_coe_iff_isComplete.mpr hg.isComplete
  let φ₀ : E →ₗ[𝕜] E × F := LinearMap.id.prod g
  have : Function.LeftInverse Prod.fst φ₀ := fun x => rfl
  let φ : E ≃ₗ[𝕜] g.graph :=
    (LinearEquiv.ofLeftInverse this).trans (LinearEquiv.ofEq _ _ g.graph_eq_range_prod.symm)
  let ψ : g.graph ≃L[𝕜] E :=
    φ.symm.toContinuousLinearEquivOfContinuous continuous_subtype_val.fst
  exact (continuous_subtype_val.comp ψ.symm.continuous).snd

/-- A useful form of the **closed graph theorem** : let `f` be a linear map between two Banach
spaces. To show that `f` is continuous, it suffices to show that for any convergent sequence
`uₙ ⟶ x`, if `f(uₙ) ⟶ y` then `y = f(x)`. -/
/-
**LinearMap.continuous_of_seq_closed_graph** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.continuous_of_seq_closed_graph (hg : forall (u : Nat -> E) (x y)
, Tendsto u atTop (𝓝 x) -> Tendsto (g ∘ u) atTop (𝓝 y) -> y = g x) : Continuous 
g
参数：hg : forall (u : Nat -> E) (x y), Tendsto u atTop (𝓝 x) -> Tendsto (g ∘ u) at
Top (𝓝 y) -> y = g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.continuous_of_isClosed_graph`：LinearMap.continuous_of_isClosed
_graph (hg : IsClosed (g.graph : Set <| E × F)) : Continuous g
· 使用定理 `IsSeqClosed.isClosed`：∀ {X : Type u_1} [inst : TopologicalSpace X] [Sequ
entialSpace X] {s : Set X}, IsSeqClosed s → IsClosed s
· 使用定理 `FrechetUrysohnSpace.to_sequentialSpace`：∀ {X : Type u_1} [inst : Topolog
icalSpace X] [FrechetUrysohnSpace X], SequentialSpace X
· 使用定理 `FirstCountableTopology.frechetUrysohnSpace`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] [FirstCountableTopology X], FrechetUrysohnSpace X
· 使用定理 `TopologicalSpace.instFirstCountableTopologyProd`：∀ {α : Type u} [t : Top
ologicalSpace α] {β : Type u_1} [inst : TopologicalSpace β] [FirstCountableTopol
ogy α]   [FirstCountableTopology β], …
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)

--- 原说明 ---
A useful form of the **closed graph theorem** : let `f` be a linear map between 
two Banach
spaces. To show that `f` is continuous, it suffices to show that for any converg
ent sequence
`uₙ ⟶ x`, if `f(uₙ) ⟶ y` then `y = f(x)`.
-/
theorem LinearMap.continuous_of_seq_closed_graph
    (hg : ∀ (u : ℕ → E) (x y), Tendsto u atTop (𝓝 x) → Tendsto (g ∘ u) atTop (𝓝 y) → y = g x) :
    Continuous g := by
  refine g.continuous_of_isClosed_graph (IsSeqClosed.isClosed ?_)
  rintro φ ⟨x, y⟩ hφg hφ
  refine hg (Prod.fst ∘ φ) x y ((continuous_fst.tendsto _).comp hφ) ?_
  have : g ∘ Prod.fst ∘ φ = Prod.snd ∘ φ := by
    ext n
    exact (hφg n).symm
  rw [this]
  exact (continuous_snd.tendsto _).comp hφ

variable {g}

namespace ContinuousLinearMap

/-- Upgrade a `LinearMap` to a `ContinuousLinearMap` using the **closed graph theorem**. -/
/-
**ContinuousLinearMap.ofIsClosedGraph** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：ofIsClosedGraph (hg : IsClosed (g.graph : Set <| E × F)) : E ->L[𝕜] F wher
e toLinearMap
参数：hg : IsClosed (g.graph : Set <| E × F)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.continuous_of_isClosed_graph`：LinearMap.continuous_of_isClosed
_graph (hg : IsClosed (g.graph : Set <| E × F)) : Continuous g

--- 原说明 ---
Upgrade a `LinearMap` to a `ContinuousLinearMap` using the **closed graph theore
m**.
-/
def ofIsClosedGraph (hg : IsClosed (g.graph : Set <| E × F)) : E →L[𝕜] F where
  toLinearMap := g
  cont := g.continuous_of_isClosed_graph hg

@[simp]
/-
**ContinuousLinearMap.coeFn_ofIsClosedGraph** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sLinearMap`。
形式化陈述：coeFn_ofIsClosedGraph (hg : IsClosed (g.graph : Set <| E × F)) : ⇑(Continu
ousLinearMap.ofIsClosedGraph hg) = g
参数：hg : IsClosed (g.graph : Set <| E × F)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeFn_ofIsClosedGraph (hg : IsClosed (g.graph : Set <| E × F)) :
    ⇑(ContinuousLinearMap.ofIsClosedGraph hg) = g :=
  rfl
/-
**ContinuousLinearMap.coe_ofIsClosedGraph** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousL
inearMap`。
形式化陈述：coe_ofIsClosedGraph (hg : IsClosed (g.graph : Set <| E × F)) : ↑(Continuou
sLinearMap.ofIsClosedGraph hg) = g
参数：hg : IsClosed (g.graph : Set <| E × F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
theorem coe_ofIsClosedGraph (hg : IsClosed (g.graph : Set <| E × F)) :
    ↑(ContinuousLinearMap.ofIsClosedGraph hg) = g := by
  ext
  rfl

/-- Upgrade a `LinearMap` to a `ContinuousLinearMap` using a variation on the
**closed graph theorem**. -/
/-
**ContinuousLinearMap.ofSeqClosedGraph** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：ofSeqClosedGraph (hg : forall (u : Nat -> E) (x y), Tendsto u atTop (𝓝 x) 
-> Tendsto (g ∘ u) atTop (𝓝 y) -> y = g x) : E ->L[𝕜] F where toLinearMap
参数：hg : forall (u : Nat -> E) (x y), Tendsto u atTop (𝓝 x) -> Tendsto (g ∘ u) at
Top (𝓝 y) -> y = g x。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.continuous_of_seq_closed_graph`：LinearMap.continuous_of_seq_cl
osed_graph (hg : forall (u : Nat -> E) (x y), Tendsto u atTop (𝓝 x) -> Tendsto (
g ∘ u) atTop (𝓝 y) -> y = g x)…

--- 原说明 ---
Upgrade a `LinearMap` to a `ContinuousLinearMap` using a variation on the
**closed graph theorem**.
-/
def ofSeqClosedGraph
    (hg : ∀ (u : ℕ → E) (x y), Tendsto u atTop (𝓝 x) → Tendsto (g ∘ u) atTop (𝓝 y) → y = g x) :
    E →L[𝕜] F where
  toLinearMap := g
  cont := g.continuous_of_seq_closed_graph hg

@[simp]
/-
**ContinuousLinearMap.coeFn_ofSeqClosedGraph** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usLinearMap`。
形式化陈述：coeFn_ofSeqClosedGraph (hg : forall (u : Nat -> E) (x y), Tendsto u atTop 
(𝓝 x) -> Tendsto (g ∘ u) atTop (𝓝 y) -> y = g x) : ⇑(ContinuousLinearMap.ofSeqCl
osedGraph hg) = g
参数：hg : forall (u : Nat -> E) (x y), Tendsto u atTop (𝓝 x) -> Tendsto (g ∘ u) at
Top (𝓝 y) -> y = g x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeFn_ofSeqClosedGraph
    (hg : ∀ (u : ℕ → E) (x y), Tendsto u atTop (𝓝 x) → Tendsto (g ∘ u) atTop (𝓝 y) → y = g x) :
    ⇑(ContinuousLinearMap.ofSeqClosedGraph hg) = g :=
  rfl
/-
**ContinuousLinearMap.coe_ofSeqClosedGraph** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
LinearMap`。
形式化陈述：coe_ofSeqClosedGraph (hg : forall (u : Nat -> E) (x y), Tendsto u atTop (𝓝
 x) -> Tendsto (g ∘ u) atTop (𝓝 y) -> y = g x) : ↑(ContinuousLinearMap.ofSeqClos
edGraph hg) = g
参数：hg : forall (u : Nat -> E) (x y), Tendsto u atTop (𝓝 x) -> Tendsto (g ∘ u) at
Top (𝓝 y) -> y = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
theorem coe_ofSeqClosedGraph
    (hg : ∀ (u : ℕ → E) (x y), Tendsto u atTop (𝓝 x) → Tendsto (g ∘ u) atTop (𝓝 y) → y = g x) :
    ↑(ContinuousLinearMap.ofSeqClosedGraph hg) = g := by
  ext
  rfl

end ContinuousLinearMap

end ClosedGraphThm

section BijectivityCriteria

namespace ContinuousLinearMap

variable {σ : 𝕜 →+* 𝕜'} {σ' : 𝕜' →+* 𝕜} [RingHomInvPair σ σ']
variable {F : Type u_4} [NormedAddCommGroup F] [NormedSpace 𝕜' F]
variable [CompleteSpace E]

/-
**ContinuousLinearMap.closed_range_of_antilipschitz** 是 Mathlib 中的一个引理，位于命名空间 `C
ontinuousLinearMap`。
形式化陈述：closed_range_of_antilipschitz {f : E ->SL[σ] F} {c : Real>=0} (hf : Antili
pschitzWith c f) : f.range.topologicalClosure = f.range
参数：hf : AntilipschitzWith c f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `AntilipschitzWith.isClosed_range`：isClosed_range {α β : Type*} [PseudoEM
etricSpace α] [EMetricSpace β] [CompleteSpace α] {f : α -> β} {K : Real>=0} (hf 
: AntilipschitzWith K …
· 使用定理 `ContinuousLinearMap.uniformContinuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2}
 [inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {E₁ : Type u_9}  
 {E₂ : Type u_10} [inst_2 :…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
-/
lemma closed_range_of_antilipschitz {f : E →SL[σ] F} {c : ℝ≥0} (hf : AntilipschitzWith c f) :
    f.range.topologicalClosure = f.range :=
  SetLike.ext'_iff.mpr <| (hf.isClosed_range f.uniformContinuous).closure_eq

variable [CompleteSpace F]
/-
**ContinuousLinearMap._root_.AntilipschitzWith.completeSpace_range_clm** 是 Mathl
ib 中的一个引理，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.AntilipschitzWith.completeSpace_range_clm {f : E →SL[σ] F} {c : ℝ≥0}
    (hf : AntilipschitzWith c f) : CompleteSpace f.range :=
  IsClosed.completeSpace_coe (hs := hf.isClosed_range f.uniformContinuous)

variable [RingHomInvPair σ' σ] [RingHomIsometric σ] [RingHomIsometric σ']

open Function
/-
**ContinuousLinearMap.bijective_iff_dense_range_and_antilipschitz** 是 Mathlib 中的
一个引理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：bijective_iff_dense_range_and_antilipschitz (f : E ->SL[σ] F) : Bijective 
f ↔ f.range.topologicalClosure = ⊤ ∧ exists c, AntilipschitzWith c f
参数：f : E ->SL[σ] F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `Dense.closure_eq`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X}
, Dense s → closure s = Set.univ
· 使用定理 `Function.Surjective.denseRange`：Function.Surjective.denseRange (hf : Fun
ction.Surjective f) : DenseRange f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ContinuousLinearEquiv.antilipschitz`：∀ {𝕜 : Type u_1} {𝕜₂ : Type u_3} {E
 : Type u_5} {F : Type u_6} [inst : NormedAddCommGroup E]   [inst_1 : NormedAddC
ommGroup F] [inst_2 : Non…
· 使用定理 `AntilipschitzWith.injective`：∀ {α : Type u_4} {β : Type u_5} [inst : EMe
tricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   Antilip
schitzWith K f → …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.coe_coe`：coe_coe (f : M₁ ->SL[σ₁₂] M₂) : ⇑(f : M₁ ->
ₛₗ[σ₁₂] M₂) = f
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用引理 `ContinuousLinearMap.closed_range_of_antilipschitz`：closed_range_of_antil
ipschitz {f : E ->SL[σ] F} {c : Real>=0} (hf : AntilipschitzWith c f) : f.range.
topologicalClosure = f.range
-/
lemma bijective_iff_dense_range_and_antilipschitz (f : E →SL[σ] F) :
    Bijective f ↔ f.range.topologicalClosure = ⊤ ∧ ∃ c, AntilipschitzWith c f := by
  refine ⟨fun h ↦ ⟨?eq_top, ?anti⟩, fun ⟨hd, c, hf⟩ ↦ ⟨hf.injective, ?surj⟩⟩
  case eq_top => simpa [SetLike.ext'_iff] using! h.2.denseRange.closure_eq
  case anti =>
    refine ⟨_, ContinuousLinearEquiv.ofBijective f ?_ ?_ |>.antilipschitz⟩ <;>
    simp only [LinearMap.range_eq_top, LinearMap.ker_eq_bot, f.coe_coe, h.1, h.2]
  case surj => rwa [← f.coe_coe, ← LinearMap.range_eq_top, ← closed_range_of_antilipschitz hf]

end ContinuousLinearMap

end BijectivityCriteria

