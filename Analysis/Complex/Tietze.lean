/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Topology.TietzeExtension
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
public import Mathlib.Analysis.Normed.Module.RCLike.Basic
/-!
# Finite-dimensional topological vector spaces over `ℝ` satisfy the Tietze extension property

There are two main results here:

- `RCLike.instTietzeExtensionTVS`: finite-dimensional topological vector spaces over `ℝ` (or `ℂ`)
  have the Tietze extension property.
- `BoundedContinuousFunction.exists_norm_eq_domRestrict_eq`: when mapping into a finite-dimensional
  normed vector space over `ℝ` (or `ℂ`), the extension can be chosen to preserve the norm of the
  bounded continuous function it extends.

-/

public section

universe u u₁ v w

-- this is not an instance because Lean cannot determine `𝕜`.
/-
**TietzeExtension.of_tvs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TietzeExtension.of_tvs (𝕜 : Type v) [NontriviallyNormedField 𝕜] {E : Type 
w} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] 
[ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] [Tiet
zeExtension.{u, v} 𝕜] : TietzeExtension.{u, w} E
参数：𝕜 : Type v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TietzeExtension.of_homeo`：TietzeExtension.of_homeo {Y : Type v} {Z : Typ
e w} [TopologicalSpace Y] [TopologicalSpace Z] [TietzeExtension.{u, w} Z] (e : Y
 ≃ₜ Z) : Tietz…
· 使用定理 `Pi.topologicalAddGroup`：∀ {β : Type v} {C : β → Type u_1} [inst : (b : β
) → TopologicalSpace (C b)] [inst_1 : (b : β) → AddGroup (C b)]   [∀ (b : β), Is
TopologicalA…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem TietzeExtension.of_tvs (𝕜 : Type v) [NontriviallyNormedField 𝕜] {E : Type w}
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜]
    [TietzeExtension.{u, v} 𝕜] : TietzeExtension.{u, w} E :=
  Module.Basis.ofVectorSpace 𝕜 E |>.equivFun.toContinuousLinearEquiv.toHomeomorph |> .of_homeo
/-
**Complex.instTietzeExtension** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Complex.instTietzeExtension : TietzeExtension Complex
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `TietzeExtension.of_tvs`：TietzeExtension.of_tvs (𝕜 : Type v) [Nontriviall
yNormedField 𝕜] {E : Type w} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] 
[IsTopologic…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Complex.instT2Space`：T2Space ℂ
-/
instance Complex.instTietzeExtension : TietzeExtension ℂ :=
  TietzeExtension.of_tvs ℝ
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) RCLike.instTietzeExtension {𝕜 : Type*} [RCLike 𝕜] :
    TietzeExtension 𝕜 := TietzeExtension.of_tvs ℝ
/-
**RCLike.instTietzeExtensionTVS** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：RCLike.instTietzeExtensionTVS {𝕜 : Type v} [RCLike 𝕜] {E : Type w} [AddCom
mGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [Continuou
sSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E] : TietzeExtension.{u, w} E
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `TietzeExtension.of_tvs`：TietzeExtension.of_tvs (𝕜 : Type v) [Nontriviall
yNormedField 𝕜] {E : Type w} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] 
[IsTopologic…
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `RCLike.instTietzeExtension`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜], TietzeEx
tension 𝕜
-/
instance RCLike.instTietzeExtensionTVS {𝕜 : Type v} [RCLike 𝕜] {E : Type w}
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E] :
    TietzeExtension.{u, w} E :=
  TietzeExtension.of_tvs 𝕜
/-
**Set.instTietzeExtensionUnitBall** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Set.instTietzeExtensionUnitBall {𝕜 : Type v} [RCLike 𝕜] {E : Type w} [Norm
edAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] : TietzeExtension.{u
, w} (Metric.ball (0 : E) 1)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `TietzeExtension.of_homeo`：TietzeExtension.of_homeo {Y : Type v} {Z : Typ
e w} [TopologicalSpace Y] [TopologicalSpace Z] [TietzeExtension.{u, w} Z] (e : Y
 ≃ₜ Z) : Tietz…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
instance Set.instTietzeExtensionUnitBall {𝕜 : Type v} [RCLike 𝕜] {E : Type w}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] :
    TietzeExtension.{u, w} (Metric.ball (0 : E) 1) :=
  have : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  .of_homeo Homeomorph.unitBall.symm
/-
**Set.instTietzeExtensionUnitClosedBall** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Set.instTietzeExtensionUnitClosedBall {𝕜 : Type v} [RCLike 𝕜] {E : Type w}
 [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] : TietzeExtens
ion.{u, w} (Metric.closedBall (0 : E) 1)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `continuous_piecewise`：continuous_piecewise [forall a, Decidable (a in s)
] (hs : forall a in frontier s, f a = g a) (hf : ContinuousOn f (closure s)) (hg
 : Continu…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `frontier_closedBall`：frontier_closedBall (x : E) {r : Real} (hr : r != 0
) : frontier (closedBall x r) = sphere x r
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `continuousOn_id`：continuousOn_id {s : Set α} : ContinuousOn id s
· 使用定理 `ContinuousOn.smul`：ContinuousOn.smul (hf : ContinuousOn f s) (hg : Conti
nuousOn g s) : ContinuousOn (f • g) s
· 使用定理 `ContinuousOn.inv₀`：ContinuousOn.inv₀ (hf : ContinuousOn f s) (h0 : foral
l x in s, f x != 0) : ContinuousOn f⁻¹ s
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `instIsTopologicalDivisionRingReal`：IsTopologicalDivisionRing ℝ
· 使用定理 `ContinuousOn.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAdd
Group E] [inst_1 : TopologicalSpace α] {f : α → E} {s : Set α},   ContinuousOn f
 s → Co…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `closure_compl`：closure_compl : closure sᶜ = (interior s)ᶜ
· 使用定理 `interior_closedBall`：interior_closedBall (x : E) {r : Real} (hr : r != 0
) : interior (closedBall x r) = ball x r
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
（共 54 条，此处仅展示前 30 条）
-/
instance Set.instTietzeExtensionUnitClosedBall {𝕜 : Type v} [RCLike 𝕜] {E : Type w}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] :
    TietzeExtension.{u, w} (Metric.closedBall (0 : E) 1) := by
  have : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  have : IsScalarTower ℝ 𝕜 E := Real.isScalarTower
  -- I didn't find this retract in Mathlib.
  let g : E → E := fun x ↦ ‖x‖⁻¹ • x
  classical
  suffices this : Continuous (piecewise (Metric.closedBall 0 1) id g) by
    refine .of_retract ⟨Subtype.val, by fun_prop⟩ ⟨_, this.codRestrict fun x ↦ ?_⟩ ?_
    · by_cases hx : x ∈ Metric.closedBall 0 1
      · simpa [piecewise_eq_of_mem (hi := hx)] using hx
      · simp only [g, piecewise_eq_of_notMem (hi := hx), RCLike.real_smul_eq_coe_smul (K := 𝕜)]
        by_cases hx' : x = 0 <;> simp [hx']
    · ext x
      simp
  refine continuous_piecewise (fun x hx ↦ ?_) continuousOn_id ?_
  · replace hx : ‖x‖ = 1 := by simpa [frontier_closedBall (0 : E) one_ne_zero] using hx
    simp [g, hx]
  · refine continuousOn_id.norm.inv₀ ?_ |>.smul continuousOn_id
    simp only [closure_compl, interior_closedBall (0 : E) one_ne_zero, mem_compl_iff,
      Metric.mem_ball, dist_zero_right, not_lt, id_eq, ne_eq, norm_eq_zero]
    exact fun x hx ↦ norm_pos_iff.mp <| one_pos.trans_le hx
/-
**Metric.instTietzeExtensionBall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Metric.instTietzeExtensionBall {𝕜 : Type v} [RCLike 𝕜] {E : Type w} [Norme
dAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] {r : Real} (hr : 0 < 
r) : TietzeExtension.{u, w} (Metric.ball (0 : E) r)
参数：hr : 0 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TietzeExtension.of_homeo`：TietzeExtension.of_homeo {Y : Type v} {Z : Typ
e w} [TopologicalSpace Y] [TopologicalSpace Z] [TietzeExtension.{u, w} Z] (e : Y
 ≃ₜ Z) : Tietz…
-/
theorem Metric.instTietzeExtensionBall {𝕜 : Type v} [RCLike 𝕜] {E : Type w}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] {r : ℝ} (hr : 0 < r) :
    TietzeExtension.{u, w} (Metric.ball (0 : E) r) :=
  have : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  .of_homeo <| show (Metric.ball (0 : E) r) ≃ₜ (Metric.ball (0 : E) 1) from
    OpenPartialHomeomorph.unitBallBall (0 : E) r hr |>.toHomeomorphSourceTarget.symm
/-
**Metric.instTietzeExtensionClosedBall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Metric.instTietzeExtensionClosedBall (𝕜 : Type v) [RCLike 𝕜] {E : Type w} 
[NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] (y : E) {r : Re
al} (hr : 0 < r) : TietzeExtension.{u, w} (Metric.closedBall y r)
参数：𝕜 : Type v；y : E；hr : 0 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TietzeExtension.of_homeo`：TietzeExtension.of_homeo {Y : Type v} {Z : Typ
e w} [TopologicalSpace Y] [TopologicalSpace Z] [TietzeExtension.{u, w} Z] (e : Y
 ≃ₜ Z) : Tietz…
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `algebraMap.coe_zero`：coe_zero : (↑(0 : R) : A) = 0
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `DilationEquiv.smulTorsor_apply`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : 
NormedDivisionRing 𝕜] [inst_1 : SeminormedAddCommGroup E]   [inst_2 : _root_.Mod
ule 𝕜 E] [inst_3 : N…
· 使用定理 `dist_add_self_left`：∀ {E : Type u_2} [inst : SeminormedAddCommGroup E] (
a b : E), dist (b + a) a = ‖b‖
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `RCLike.norm_ofReal`：norm_ofReal (r : Real) : ‖(r : K)‖ = |r|
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `mul_le_iff_le_one_right`：mul_le_iff_le_one_right [PosMulMono α] [PosMulR
eflectLE α] (a0 : 0 < a) : a * b <= a ↔ b <= 1
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
-/
theorem Metric.instTietzeExtensionClosedBall (𝕜 : Type v) [RCLike 𝕜] {E : Type w}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] (y : E) {r : ℝ} (hr : 0 < r) :
    TietzeExtension.{u, w} (Metric.closedBall y r) :=
  .of_homeo (Z := Metric.closedBall (0 : E) 1) <| by
    symm
    apply (DilationEquiv.smulTorsor y (k := (r : 𝕜)) <| by exact_mod_cast hr.ne').toHomeomorph.sets
    ext x
    simp only [mem_closedBall, dist_zero_right, DilationEquiv.coe_toHomeomorph, Set.mem_preimage,
      DilationEquiv.smulTorsor_apply, vadd_eq_add, dist_add_self_left, norm_smul,
      RCLike.norm_ofReal, abs_of_nonneg hr.le]
    exact (mul_le_iff_le_one_right hr).symm
/-
**unitInterval.instTietzeExtension** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：unitInterval.instTietzeExtension : TietzeExtension unitInterval
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `unitInterval.eq_closedBall`：eq_closedBall : I = Metric.closedBall 2⁻¹ 2⁻
¹
· 使用定理 `Metric.instTietzeExtensionClosedBall`：Metric.instTietzeExtensionClosedBa
ll (𝕜 : Type v) [RCLike 𝕜] {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
 [FiniteDimensional 𝕜 E] (…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_lt_true`：isNNRat_lt_true [Semiring α] [Line
arOrder α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Nat} -> {da db : Nat}
 -> IsNNRat a na da -> IsN…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
-/
instance unitInterval.instTietzeExtension : TietzeExtension unitInterval := by
  rw [unitInterval.eq_closedBall]
  exact Metric.instTietzeExtensionClosedBall ℝ _ (by norm_num)

variable {X : Type u} [TopologicalSpace X] [NormalSpace X] {s : Set X} (hs : IsClosed s)
variable (𝕜 : Type v) [RCLike 𝕜]
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

namespace BoundedContinuousFunction

include 𝕜 hs in
/-- **Tietze extension theorem** for real-valued bounded continuous maps, a version with a closed
embedding and bundled composition. If `e : C(X, Y)` is a closed embedding of a topological space
into a normal topological space and `f : X →ᵇ ℝ` is a bounded continuous function, then there exists
a bounded continuous function `g : Y →ᵇ ℝ` of the same norm such that `g ∘ e = f`. -/
/-
**BoundedContinuousFunction.exists_norm_eq_domRestrict_eq** 是 Mathlib 中的一个定理，位于命
名空间 `BoundedContinuousFunction`。
形式化陈述：exists_norm_eq_domRestrict_eq (f : s ->ᵇ E) : exists g : X ->ᵇ E, ‖g‖ = ‖f
‖ ∧ g.domRestrict s = f
参数：f : s ->ᵇ E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Metric.instTietzeExtensionClosedBall`：Metric.instTietzeExtensionClosedBa
ll (𝕜 : Type v) [RCLike 𝕜] {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
 [FiniteDimensional 𝕜 E] (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `BoundedContinuousFunction.norm_coe_le_norm`：norm_coe_le_norm (x : α) : ‖
f x‖ <= ‖f‖
· 使用定理 `BoundedContinuousMapClass.toContinuousMapClass`：∀ {F : Type u_2} {α : ou
tParam (Type u_3)} {β : outParam (Type u_4)} {inst : TopologicalSpace α}   {inst
_1 : PseudoMetricSpace β} {inst_2 : …
· 使用定理 `ContinuousMap.exists_forall_mem_restrict_eq`：ContinuousMap.exists_forall
_mem_restrict_eq (hs : IsClosed s) {Y : Type v} [TopologicalSpace Y] (f : C(s, Y
)) {t : Set Y} (hf : forall x, f …
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `BoundedContinuousFunction.norm_le`：norm_le (C0 : (0 : Real) <= C) : ‖f‖ 
<= C ↔ forall x : α, ‖f x‖ <= C
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `BoundedContinuousFunction.ext`：ext (h : forall x, f x = g x) : f = g

--- 原说明 ---
**Tietze extension theorem** for real-valued bounded continuous maps, a version 
with a closed
embedding and bundled composition. If `e : C(X, Y)` is a closed embedding of a t
opological space
into a normal topological space and `f : X →ᵇ ℝ` is a bounded continuous functio
n, then there exists
a bounded continuous function `g : Y →ᵇ ℝ` of the same norm such that `g ∘ e = f
`.
-/
theorem exists_norm_eq_domRestrict_eq (f : s →ᵇ E) :
    ∃ g : X →ᵇ E, ‖g‖ = ‖f‖ ∧ g.domRestrict s = f := by
  by_cases hf : ‖f‖ = 0; · exact ⟨0, by aesop⟩
  have := Metric.instTietzeExtensionClosedBall.{u, v} 𝕜 (0 : E) (by simp_all : 0 < ‖f‖)
  have hf' x : f x ∈ Metric.closedBall 0 ‖f‖ := by simpa using! f.norm_coe_le_norm x
  obtain ⟨g, hg_mem, hg⟩ := (f : C(s, E)).exists_forall_mem_restrict_eq hs hf'
  simp only [Metric.mem_closedBall, dist_zero_right] at hg_mem
  let g' : X →ᵇ E := .ofNormedAddCommGroup g (map_continuous g) ‖f‖ hg_mem
  refine ⟨g', ?_, by ext x; congrm($(hg) x)⟩
  apply le_antisymm ((g'.norm_le <| by positivity).mpr hg_mem)
  refine (f.norm_le <| by positivity).mpr fun x ↦ ?_
  have hx : f x = g' x := by simpa using! congr($(hg) x).symm
  rw [hx]
  exact g'.norm_le (norm_nonneg g') |>.mp le_rfl x

@[deprecated (since := "2026-07-19")]
alias exists_norm_eq_restrict_eq := exists_norm_eq_domRestrict_eq

end BoundedContinuousFunction

