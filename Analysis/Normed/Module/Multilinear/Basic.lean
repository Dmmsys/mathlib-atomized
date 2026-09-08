/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Sophie Morel, Yury Kudryashov
-/
module

public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
public import Mathlib.Topology.Algebra.Module.Multilinear.Topology
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Operator norm on the space of continuous multilinear maps

When `f` is a continuous multilinear map in finitely many variables, we define its norm `‖f‖` as the
smallest number such that `‖f m‖ ≤ ‖f‖ * ∏ i, ‖m i‖` for all `m`.

We show that it is indeed a norm, and prove its basic properties.

## Main results

Let `f` be a multilinear map in finitely many variables.
* `exists_bound_of_continuous` asserts that, if `f` is continuous, then there exists `C > 0`
  with `‖f m‖ ≤ C * ∏ i, ‖m i‖` for all `m`.
* `continuous_of_bound`, conversely, asserts that this bound implies continuity.
* `mkContinuous` constructs the associated continuous multilinear map.

Let `f` be a continuous multilinear map in finitely many variables.
* `‖f‖` is its norm, i.e., the smallest number such that `‖f m‖ ≤ ‖f‖ * ∏ i, ‖m i‖` for
  all `m`.
* `le_opNorm f m` asserts the fundamental inequality `‖f m‖ ≤ ‖f‖ * ∏ i, ‖m i‖`.
* `norm_image_sub_le f m₁ m₂` gives a control of the difference `f m₁ - f m₂` in terms of
  `‖f‖` and `‖m₁ - m₂‖`.

## Implementation notes

We mostly follow the API (and the proofs) of `OperatorNorm.lean`, with the additional complexity
that we should deal with multilinear maps in several variables.

From the mathematical point of view, all the results follow from the results on operator norm in
one variable, by applying them to one variable after the other through currying. However, this
is only well defined when there is an order on the variables (for instance on `Fin n`) although
the final result is independent of the order. While everything could be done following this
approach, it turns out that direct proofs are easier and more efficient.
-/

@[expose] public section

suppress_compilation

noncomputable section

open scoped NNReal Topology Uniformity
open Finset Metric Function Filter

/-!
### Type variables

We use the following type variables in this file:

* `𝕜` : a `NontriviallyNormedField`;
* `ι`, `ι'` : finite index types with decidable equality;
* `E`, `E₁` : families of normed vector spaces over `𝕜` indexed by `i : ι`;
* `E'` : a family of normed vector spaces over `𝕜` indexed by `i' : ι'`;
* `Ei` : a family of normed vector spaces over `𝕜` indexed by `i : Fin (Nat.succ n)`;
* `G`, `G'` : normed vector spaces over `𝕜`.
-/

universe u v v' wE wE₁ wE' wG wG'

section continuous_eval

variable {𝕜 ι : Type*} {E : ι → Type*} {F : Type*}
    [NormedField 𝕜] [Finite ι] [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    [TopologicalSpace F] [AddCommGroup F] [IsTopologicalAddGroup F] [Module 𝕜 F]

/-
**ContinuousMultilinearMap.instContinuousEval** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ContinuousMultilinearMap.instContinuousEval : ContinuousEval (ContinuousMu
ltilinearMap 𝕜 E F) (Π i, E i) F where continuous_eval
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `isUniformAddGroup_of_addCommGroup`：∀ {G : Type u_1} [inst : AddCommGroup
 G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGroup G],   IsUnifor
mAddGroup G
· 使用定理 `ContinuousOn.comp_continuous`：ContinuousOn.comp_continuous {g : β -> γ} 
{f : α -> β} {s : Set β} (hg : ContinuousOn g s) (hf : Continuous f) (hs : foral
l x, f x in s) : C…
· 使用定理 `IsUniformAddGroup.to_topologicalAddGroup`：∀ {α : Type u_1} [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsTopologicalAddGroup α
· 使用定理 `UniformOnFun.continuousOn_eval₂`：∀ {α : Type u_1} {β : Type u_2} [inst :
 UniformSpace β] {𝔖 : Set (Set α)} [inst_1 : TopologicalSpace α],   (∀ (x : α), 
∃ V ∈ 𝔖, V ∈ nhds x) …
· 使用定理 `NormedSpace.isVonNBounded_of_isBounded`：isVonNBounded_of_isBounded {s : 
Set E} (h : Bornology.IsBounded s) : Bornology.IsVonNBounded 𝕜 s
· 使用定理 `Metric.isBounded_ball`：isBounded_ball : IsBounded (ball x r)
· 使用定理 `Metric.ball_mem_nhds`：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ba
ll x ε in 𝓝 x
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Continuous.prodMap`：Continuous.prodMap {f : Z -> X} {g : W -> Y} (hf : C
ontinuous f) (hg : Continuous g) : Continuous (Prod.map f g)
· 使用定理 `Topology.IsEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Continuous…
· 使用引理 `ContinuousMultilinearMap.isEmbedding_toUniformOnFun`：isEmbedding_toUnifo
rmOnFun : IsEmbedding (toUniformOnFun : ContinuousMultilinearMap 𝕜 E F -> ((Π i,
 E i) ->ᵤ[{s | IsVonNBounded 𝕜 s}] F))
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `ContinuousMultilinearMap.cont`：∀ {R : Type u} {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoid (M₁
 i)] [inst_2 : AddC…
-/
instance ContinuousMultilinearMap.instContinuousEval :
    ContinuousEval (ContinuousMultilinearMap 𝕜 E F) (Π i, E i) F where
  continuous_eval := by
    cases nonempty_fintype ι
    let _ := IsTopologicalAddGroup.rightUniformSpace F
    have := isUniformAddGroup_of_addCommGroup (G := F)
    refine (UniformOnFun.continuousOn_eval₂ fun m ↦ ?_).comp_continuous
      (isEmbedding_toUniformOnFun.continuous.prodMap continuous_id) fun (f, x) ↦ f.cont.continuousAt
    exact ⟨ball m 1, NormedSpace.isVonNBounded_of_isBounded _ isBounded_ball,
      ball_mem_nhds _ one_pos⟩

namespace ContinuousLinearMap

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [Module 𝕜 G] [ContinuousConstSMul 𝕜 F]

/-
**ContinuousLinearMap.continuous_uncurry_of_multilinear** 是 Mathlib 中的一个引理，位于命名空
间 `ContinuousLinearMap`。
形式化陈述：continuous_uncurry_of_multilinear (f : G ->L[𝕜] ContinuousMultilinearMap 𝕜
 E F) : Continuous (fun (p : G × (Π i, E i)) => f p.1 p.2)
参数：f : G ->L[𝕜] ContinuousMultilinearMap 𝕜 E F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `Continuous.eval`：∀ {F : Type u_1} {X : Type u_2} {Y : Type u_3} {Z : Typ
e u_4} [inst : FunLike F X Y] [inst_1 : TopologicalSpace F]   [inst_2 : Topologi
calSp…
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
-/
lemma continuous_uncurry_of_multilinear (f : G →L[𝕜] ContinuousMultilinearMap 𝕜 E F) :
    Continuous (fun (p : G × (Π i, E i)) ↦ f p.1 p.2) := by
  fun_prop
/-
**ContinuousLinearMap.continuousOn_uncurry_of_multilinear** 是 Mathlib 中的一个引理，位于命
名空间 `ContinuousLinearMap`。
形式化陈述：continuousOn_uncurry_of_multilinear (f : G ->L[𝕜] ContinuousMultilinearMap
 𝕜 E F) {s} : ContinuousOn (fun (p : G × (Π i, E i)) => f p.1 p.2) s
参数：f : G ->L[𝕜] ContinuousMultilinearMap 𝕜 E F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用引理 `ContinuousLinearMap.continuous_uncurry_of_multilinear`：continuous_uncurr
y_of_multilinear (f : G ->L[𝕜] ContinuousMultilinearMap 𝕜 E F) : Continuous (fun
 (p : G × (Π i, E i)) => f p.1 p.2)
-/
lemma continuousOn_uncurry_of_multilinear (f : G →L[𝕜] ContinuousMultilinearMap 𝕜 E F) {s} :
    ContinuousOn (fun (p : G × (Π i, E i)) ↦ f p.1 p.2) s :=
  f.continuous_uncurry_of_multilinear.continuousOn
/-
**ContinuousLinearMap.continuousAt_uncurry_of_multilinear** 是 Mathlib 中的一个引理，位于命
名空间 `ContinuousLinearMap`。
形式化陈述：continuousAt_uncurry_of_multilinear (f : G ->L[𝕜] ContinuousMultilinearMap
 𝕜 E F) {x} : ContinuousAt (fun (p : G × (Π i, E i)) => f p.1 p.2) x
参数：f : G ->L[𝕜] ContinuousMultilinearMap 𝕜 E F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用引理 `ContinuousLinearMap.continuous_uncurry_of_multilinear`：continuous_uncurr
y_of_multilinear (f : G ->L[𝕜] ContinuousMultilinearMap 𝕜 E F) : Continuous (fun
 (p : G × (Π i, E i)) => f p.1 p.2)
-/
lemma continuousAt_uncurry_of_multilinear (f : G →L[𝕜] ContinuousMultilinearMap 𝕜 E F) {x} :
    ContinuousAt (fun (p : G × (Π i, E i)) ↦ f p.1 p.2) x :=
  f.continuous_uncurry_of_multilinear.continuousAt
/-
**ContinuousLinearMap.continuousWithinAt_uncurry_of_multilinear** 是 Mathlib 中的一个
引理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：continuousWithinAt_uncurry_of_multilinear (f : G ->L[𝕜] ContinuousMultilin
earMap 𝕜 E F) {s x} : ContinuousWithinAt (fun (p : G × (Π i, E i)) => f p.1 p.2)
 s x
参数：f : G ->L[𝕜] ContinuousMultilinearMap 𝕜 E F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `Continuous.continuousWithinAt`：Continuous.continuousWithinAt (h : Contin
uous f) : ContinuousWithinAt f s x
· 使用引理 `ContinuousLinearMap.continuous_uncurry_of_multilinear`：continuous_uncurr
y_of_multilinear (f : G ->L[𝕜] ContinuousMultilinearMap 𝕜 E F) : Continuous (fun
 (p : G × (Π i, E i)) => f p.1 p.2)
-/
lemma continuousWithinAt_uncurry_of_multilinear (f : G →L[𝕜] ContinuousMultilinearMap 𝕜 E F) {s x} :
    ContinuousWithinAt (fun (p : G × (Π i, E i)) ↦ f p.1 p.2) s x :=
  f.continuous_uncurry_of_multilinear.continuousWithinAt

end ContinuousLinearMap

end continuous_eval

section Seminorm

variable {𝕜 : Type u} {ι : Type v} {ι' : Type v'} {E : ι → Type wE} {E₁ : ι → Type wE₁}
  {E' : ι' → Type wE'} {G : Type wG} {G' : Type wG'}
  [Fintype ι'] [NontriviallyNormedField 𝕜] [∀ i, SeminormedAddCommGroup (E i)]
  [∀ i, NormedSpace 𝕜 (E i)] [∀ i, SeminormedAddCommGroup (E₁ i)] [∀ i, NormedSpace 𝕜 (E₁ i)]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G] [SeminormedAddCommGroup G'] [NormedSpace 𝕜 G']

/-!
### Continuity properties of multilinear maps

We relate continuity of multilinear maps to the inequality `‖f m‖ ≤ C * ∏ i, ‖m i‖`, in
both directions. Along the way, we prove useful bounds on the difference `‖f m₁ - f m₂‖`.
-/

namespace MultilinearMap

/-- If `f` is a continuous multilinear map on `E`
and `m` is an element of `∀ i, E i` such that one of the `m i` has norm `0`,
then `f m` has norm `0`.

Note that we cannot drop the continuity assumption because `f (m : Unit → E) = f (m ())`,
where the domain has zero norm and the codomain has a nonzero norm
does not satisfy this condition. -/
/-
**MultilinearMap.norm_map_coord_zero** 是 Mathlib 中的一个引理，位于命名空间 `MultilinearMap`。
形式化陈述：norm_map_coord_zero (f : MultilinearMap 𝕜 E G) (hf : Continuous f) {m : fo
rall i, E i} {i : ι} (hi : ‖m i‖ = 0) : ‖f m‖ = 0
参数：f : MultilinearMap 𝕜 E G；hf : Continuous f；hi : ‖m i‖ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inseparable_zero_iff_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E
] {a : E}, Inseparable a 0 ↔ ‖a‖ = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inseparable_pi`：inseparable_pi {f g : forall i, A i} : (f ~ᵢ g) ↔ forall
 i, f i ~ᵢ g i
· 使用引理 `Function.forall_update_iff`：forall_update_iff (f : forall a, β a) {a : α
} {b : β a} (p : forall a, β a -> Prop) : (forall x, p x (update f a b x)) ↔ p a
 b ∧ forall x, x…
· 使用定理 `Inseparable.symm`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X}
, Inseparable x y → Inseparable y x
· 使用定理 `MultilinearMap.map_update_zero`：map_update_zero [DecidableEq ι] (m : for
all i, M₁ i) (i : ι) : f (update m i 0) = 0
· 使用定理 `Inseparable.map`：map (h : x ~ᵢ y) (hf : Continuous f) : f x ~ᵢ f y

--- 原说明 ---
If `f` is a continuous multilinear map on `E`
and `m` is an element of `∀ i, E i` such that one of the `m i` has norm `0`,
then `f m` has norm `0`.

Note that we cannot drop the continuity assumption because `f (m : Unit → E) = f
 (m ())`,
where the domain has zero norm and the codomain has a nonzero norm
does not satisfy this condition.
-/
lemma norm_map_coord_zero (f : MultilinearMap 𝕜 E G) (hf : Continuous f)
    {m : ∀ i, E i} {i : ι} (hi : ‖m i‖ = 0) : ‖f m‖ = 0 := by
  classical
  rw [← inseparable_zero_iff_norm] at hi ⊢
  have : Inseparable (update m i 0) m := inseparable_pi.2 <|
    (forall_update_iff m fun i a ↦ Inseparable a (m i)).2 ⟨hi.symm, fun _ _ ↦ rfl⟩
  simpa only [map_update_zero] using this.symm.map hf

variable [Fintype ι]

/-- If a multilinear map in finitely many variables on seminormed spaces
sends vectors with a component of norm zero to vectors of norm zero
and satisfies the inequality `‖f m‖ ≤ C * ∏ i, ‖m i‖` on a shell `ε i / ‖c i‖ < ‖m i‖ < ε i`
for some positive numbers `ε i` and elements `c i : 𝕜`, `1 < ‖c i‖`,
then it satisfies this inequality for all `m`.

The first assumption is automatically satisfied on normed spaces, see `bound_of_shell` below.
For seminormed spaces, it follows from continuity of `f`, see next lemma,
see `bound_of_shell_of_continuous` below. -/
/-
**MultilinearMap.bound_of_shell_of_norm_map_coord_zero** 是 Mathlib 中的一个定理，位于命名空间
 `MultilinearMap`。
形式化陈述：bound_of_shell_of_norm_map_coord_zero (f : MultilinearMap 𝕜 E G) (hf₀ : fo
rall {m i}, ‖m i‖ = 0 -> ‖f m‖ = 0) {ε : ι -> Real} {C : Real} (hε : forall i, 0
 < ε i) {c : ι -> 𝕜} (hc : forall i, 1 < ‖c i‖) (hf : forall m : forall i, E i, 
(forall i, ε i / ‖c i‖ <= ‖m i‖) -> (forall i, ‖m i‖ < ε i) -> ‖f m‖ <= C * ∏ i,
 ‖m i‖) (m : forall i, E i) : ‖f m‖ <= C * ∏ i, ‖m i‖
参数：f : MultilinearMap 𝕜 E G；hf₀ : forall {m i}, ‖m i‖ = 0 -> ‖f m‖ = 0；hε : fora
ll i, 0 < ε i；hc : forall i, 1 < ‖c i‖；hf : forall m : forall i, E i, (forall i,
 ε i / ‖c i‖ <= ‖m i‖) -> (forall i, ‖m i‖ < ε i) -> ‖f m‖ <= C * ∏ i, ‖m i‖；m :
 forall i, E i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.prod_eq_zero`：prod_eq_zero (hi : i in s) (h : f i = 0) : ∏ j in s
, f j = 0
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `Finset.prod_pos`：prod_pos (h0 : forall i in s, 0 < f i) : 0 < ∏ i in s, 
f i
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MultilinearMap.map_smul_univ`：map_smul_univ [Fintype ι] (c : ι -> R) (m 
: forall i, M₁ i) : (f fun i => c i • m i) = (∏ i, c i) • f m
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_prod`：norm_prod (s : Finset β) (f : β -> α) : ‖∏ b in s, f b‖ = ∏ b
 in s, ‖f b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `rescale_to_shell_semi_normed`：rescale_to_shell_semi_normed {c : 𝕜} (hc :
 1 < ‖c‖) {ε : Real} (εpos : 0 < ε) {x : E} (hx : ‖x‖ != 0) : exists d : 𝕜, d !=
 0 ∧ ‖d • x‖ < ε ∧…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
If a multilinear map in finitely many variables on seminormed spaces
sends vectors with a component of norm zero to vectors of norm zero
and satisfies the inequality `‖f m‖ ≤ C * ∏ i, ‖m i‖` on a shell `ε i / ‖c i‖ < 
‖m i‖ < ε i`
for some positive numbers `ε i` and elements `c i : 𝕜`, `1 < ‖c i‖`,
then it satisfies this inequality for all `m`.

The first assumption is automatically satisfied on normed spaces, see `bound_of_
shell` below.
For seminormed spaces, it follows from continuity of `f`, see next lemma,
see `bound_of_shell_of_continuous` below.
-/
theorem bound_of_shell_of_norm_map_coord_zero (f : MultilinearMap 𝕜 E G)
    (hf₀ : ∀ {m i}, ‖m i‖ = 0 → ‖f m‖ = 0)
    {ε : ι → ℝ} {C : ℝ} (hε : ∀ i, 0 < ε i) {c : ι → 𝕜} (hc : ∀ i, 1 < ‖c i‖)
    (hf : ∀ m : ∀ i, E i, (∀ i, ε i / ‖c i‖ ≤ ‖m i‖) → (∀ i, ‖m i‖ < ε i) → ‖f m‖ ≤ C * ∏ i, ‖m i‖)
    (m : ∀ i, E i) : ‖f m‖ ≤ C * ∏ i, ‖m i‖ := by
  by_cases! hm : ∃ i, ‖m i‖ = 0
  · rcases hm with ⟨i, hi⟩
    rw [hf₀ hi, prod_eq_zero (mem_univ i) hi, mul_zero]
  choose δ hδ0 hδm_lt hle_δm _ using fun i => rescale_to_shell_semi_normed (hc i) (hε i) (hm i)
  have hδ0 : 0 < ∏ i, ‖δ i‖ := prod_pos fun i _ => norm_pos_iff.2 (hδ0 i)
  simpa [map_smul_univ, norm_smul, prod_mul_distrib, mul_left_comm C, hδ0] using
    hf (fun i => δ i • m i) hle_δm hδm_lt

/-- If a continuous multilinear map in finitely many variables on normed spaces satisfies
the inequality `‖f m‖ ≤ C * ∏ i, ‖m i‖` on a shell `ε i / ‖c i‖ < ‖m i‖ < ε i` for some positive
numbers `ε i` and elements `c i : 𝕜`, `1 < ‖c i‖`, then it satisfies this inequality for all `m`. -/
/-
**MultilinearMap.bound_of_shell_of_continuous** 是 Mathlib 中的一个定理，位于命名空间 `Multili
nearMap`。
形式化陈述：bound_of_shell_of_continuous (f : MultilinearMap 𝕜 E G) (hfc : Continuous 
f) {ε : ι -> Real} {C : Real} (hε : forall i, 0 < ε i) {c : ι -> 𝕜} (hc : forall
 i, 1 < ‖c i‖) (hf : forall m : forall i, E i, (forall i, ε i / ‖c i‖ <= ‖m i‖) 
-> (forall i, ‖m i‖ < ε i) -> ‖f m‖ <= C * ∏ i, ‖m i‖) (m : forall i, E i) : ‖f 
m‖ <= C * ∏ i, ‖m i‖
参数：f : MultilinearMap 𝕜 E G；hfc : Continuous f；hε : forall i, 0 < ε i；hc : foral
l i, 1 < ‖c i‖；hf : forall m : forall i, E i, (forall i, ε i / ‖c i‖ <= ‖m i‖) -
> (forall i, ‖m i‖ < ε i) -> ‖f m‖ <= C * ∏ i, ‖m i‖；m : forall i, E i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.bound_of_shell_of_norm_map_coord_zero`：bound_of_shell_of_
norm_map_coord_zero (f : MultilinearMap 𝕜 E G) (hf₀ : forall {m i}, ‖m i‖ = 0 ->
 ‖f m‖ = 0) {ε : ι -> Real} {C : Real} (hε…
· 使用引理 `MultilinearMap.norm_map_coord_zero`：norm_map_coord_zero (f : Multilinear
Map 𝕜 E G) (hf : Continuous f) {m : forall i, E i} {i : ι} (hi : ‖m i‖ = 0) : ‖f
 m‖ = 0

--- 原说明 ---
If a continuous multilinear map in finitely many variables on normed spaces sati
sfies
the inequality `‖f m‖ ≤ C * ∏ i, ‖m i‖` on a shell `ε i / ‖c i‖ < ‖m i‖ < ε i` f
or some positive
numbers `ε i` and elements `c i : 𝕜`, `1 < ‖c i‖`, then it satisfies this inequa
lity for all `m`.
-/
theorem bound_of_shell_of_continuous (f : MultilinearMap 𝕜 E G) (hfc : Continuous f)
    {ε : ι → ℝ} {C : ℝ} (hε : ∀ i, 0 < ε i) {c : ι → 𝕜} (hc : ∀ i, 1 < ‖c i‖)
    (hf : ∀ m : ∀ i, E i, (∀ i, ε i / ‖c i‖ ≤ ‖m i‖) → (∀ i, ‖m i‖ < ε i) → ‖f m‖ ≤ C * ∏ i, ‖m i‖)
    (m : ∀ i, E i) : ‖f m‖ ≤ C * ∏ i, ‖m i‖ :=
  bound_of_shell_of_norm_map_coord_zero f (norm_map_coord_zero f hfc) hε hc hf m

/-- If a multilinear map in finitely many variables on normed spaces is continuous, then it
satisfies the inequality `‖f m‖ ≤ C * ∏ i, ‖m i‖`, for some `C` which can be chosen to be
positive. -/
/-
**MultilinearMap.exists_bound_of_continuous** 是 Mathlib 中的一个定理，位于命名空间 `Multiline
arMap`。
形式化陈述：exists_bound_of_continuous (f : MultilinearMap 𝕜 E G) (hf : Continuous f) 
: exists C : Real, 0 < C ∧ forall m, ‖f m‖ <= C * ∏ i, ‖m i‖
参数：f : MultilinearMap 𝕜 E G；hf : Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `add_pos_of_nonneg_of_pos`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst
_1 : Preorder α] [AddLeftStrictMono α] {a b : α},   0 ≤ a → 0 < b → 0 < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NormedAddCommGroup.tendsto_nhds_nhds`：∀ {E : Type u_5} {F : Type u_6} [i
nst : SeminormedAddCommGroup E] [inst_1 : SeminormedAddCommGroup F] {f : E → F} 
  {x : E} {y : F}, Filter.…
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `NormedField.exists_one_lt_norm`：exists_one_lt_norm : exists x : α, 1 < ‖
x‖
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
（共 53 条，此处仅展示前 30 条）

--- 原说明 ---
If a multilinear map in finitely many variables on normed spaces is continuous, 
then it
satisfies the inequality `‖f m‖ ≤ C * ∏ i, ‖m i‖`, for some `C` which can be cho
sen to be
positive.
-/
theorem exists_bound_of_continuous (f : MultilinearMap 𝕜 E G) (hf : Continuous f) :
    ∃ C : ℝ, 0 < C ∧ ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖ := by
  cases isEmpty_or_nonempty ι
  · refine ⟨‖f 0‖ + 1, add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one, fun m => ?_⟩
    obtain rfl : m = 0 := funext (IsEmpty.elim ‹_›)
    simp [univ_eq_empty, zero_le_one]
  obtain ⟨ε : ℝ, ε0 : 0 < ε, hε : ∀ m : ∀ i, E i, ‖m - 0‖ < ε → ‖f m - f 0‖ < 1⟩ :=
    NormedAddCommGroup.tendsto_nhds_nhds.1 (hf.tendsto 0) 1 zero_lt_one
  simp only [sub_zero, f.map_zero] at hε
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  have : 0 < (‖c‖ / ε) ^ Fintype.card ι := pow_pos (div_pos (zero_lt_one.trans hc) ε0) _
  refine ⟨_, this, ?_⟩
  refine f.bound_of_shell_of_continuous hf (fun _ => ε0) (fun _ => hc) fun m hcm hm => ?_
  refine (hε m ((pi_norm_lt_iff ε0).2 hm)).le.trans ?_
  rw [← div_le_iff₀' this, one_div, ← inv_pow, inv_div, Fintype.card, ← prod_const]
  gcongr
  apply hcm

/-- If a multilinear map `f` satisfies a boundedness property around `0`,
one can deduce a bound on `f m₁ - f m₂` using the multilinearity.
Here, we give a precise but hard to use version.
See `norm_image_sub_le_of_bound` for a less precise but more usable version.
The bound reads
`‖f m - f m'‖ ≤
  C * ‖m 1 - m' 1‖ * max ‖m 2‖ ‖m' 2‖ * max ‖m 3‖ ‖m' 3‖ * ... * max ‖m n‖ ‖m' n‖ + ...`,
where the other terms in the sum are the same products where `1` is replaced by any `i`. -/
/-
**MultilinearMap.norm_image_sub_le_of_bound'** 是 Mathlib 中的一个定理，位于命名空间 `Multilin
earMap`。
形式化陈述：norm_image_sub_le_of_bound' [DecidableEq ι] (f : MultilinearMap 𝕜 E G) {C 
: Real} (hC : 0 <= C) (H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖) (m₁ m₂ : forall i,
 E i) : ‖f m₁ - f m₂‖ <= C * ∑ i, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ 
j‖ ‖m₂ j‖
参数：f : MultilinearMap 𝕜 E G；hC : 0 <= C；H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖；m₁
 m₂ : forall i, E i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.piecewise_empty`：piecewise_empty [forall i : ι, Decidable (i in (
∅ : Finset ι))] : piecewise ∅ f g = g
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `Finset.piecewise_insert`：piecewise_insert [DecidableEq ι] (j : ι) [foral
l i, Decidable (i in insert j s)] : (insert j s).piecewise f g = update (s.piece
wise f g) j (…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : ι} (hi : i ∉ 
s) : s.piecewise f g i = g i
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MultilinearMap.map_update_sub`：map_update_sub [DecidableEq ι] (m : foral
l i, M₁ i) (i : ι) (x y : M₁ i) : f (update m i (x - y)) = f (update m i x) - f 
(update m i y)
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用引理 `Finset.prod_le_prod`：prod_le_prod (h0 : forall i in s, 0 <= f i) (h1 : f
orall i in s, f i <= g i) : ∏ i in s, f i <= ∏ i in s, g i
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用引理 `Finset.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : ι} (hi : i in s) : 
s.piecewise f g i = f i
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `dist_triangle`：dist_triangle (x y z : α) : dist x z <= dist x y + dist y
 z
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
If a multilinear map `f` satisfies a boundedness property around `0`,
one can deduce a bound on `f m₁ - f m₂` using the multilinearity.
Here, we give a precise but hard to use version.
See `norm_image_sub_le_of_bound` for a less precise but more usable version.
The bound reads
`‖f m - f m'‖ ≤
  C * ‖m 1 - m' 1‖ * max ‖m 2‖ ‖m' 2‖ * max ‖m 3‖ ‖m' 3‖ * ... * max ‖m n‖ ‖m' n
‖ + ...`,
where the other terms in the sum are the same products where `1` is replaced by 
any `i`.
-/
theorem norm_image_sub_le_of_bound' [DecidableEq ι] (f : MultilinearMap 𝕜 E G) {C : ℝ} (hC : 0 ≤ C)
    (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) (m₁ m₂ : ∀ i, E i) :
    ‖f m₁ - f m₂‖ ≤ C * ∑ i, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ := by
  have A :
    ∀ s : Finset ι,
      ‖f m₁ - f (s.piecewise m₂ m₁)‖ ≤
        C * ∑ i ∈ s, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ := fun s ↦ by
    induction s using Finset.induction with
    | empty => simp
    | insert i s his Hrec =>
      have I :
        ‖f (s.piecewise m₂ m₁) - f ((insert i s).piecewise m₂ m₁)‖ ≤
          C * ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ := by
        have A : (insert i s).piecewise m₂ m₁ = Function.update (s.piecewise m₂ m₁) i (m₂ i) :=
          s.piecewise_insert _ _ _
        have B : s.piecewise m₂ m₁ = Function.update (s.piecewise m₂ m₁) i (m₁ i) := by
          simp [his]
        rw [B, A, ← f.map_update_sub]
        apply le_trans (H _)
        gcongr with j
        by_cases h : j = i
        · rw [h]
          simp
        · by_cases h' : j ∈ s <;> simp [h', h]
      calc
        ‖f m₁ - f ((insert i s).piecewise m₂ m₁)‖ ≤
            ‖f m₁ - f (s.piecewise m₂ m₁)‖ +
              ‖f (s.piecewise m₂ m₁) - f ((insert i s).piecewise m₂ m₁)‖ := by
          rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]
          exact dist_triangle _ _ _
        _ ≤ (C * ∑ i ∈ s, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖) +
              C * ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ :=
          (add_le_add Hrec I)
        _ = C * ∑ i ∈ insert i s, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ := by
          simp [his, add_comm, left_distrib]
  convert! A univ
  simp

/-- If `f` satisfies a boundedness property around `0`, one can deduce a bound on `f m₁ - f m₂`
using the multilinearity. Here, we give a usable but not very precise version. See
`norm_image_sub_le_of_bound'` for a more precise but less usable version. The bound is
`‖f m - f m'‖ ≤ C * card ι * ‖m - m'‖ * (max ‖m‖ ‖m'‖) ^ (card ι - 1)`. -/
/-
**MultilinearMap.norm_image_sub_le_of_bound** 是 Mathlib 中的一个定理，位于命名空间 `Multiline
arMap`。
形式化陈述：norm_image_sub_le_of_bound (f : MultilinearMap 𝕜 E G) {C : Real} (hC : 0 <
= C) (H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖) (m₁ m₂ : forall i, E i) : ‖f m₁ - f
 m₂‖ <= C * Fintype.card ι * max ‖m₁‖ ‖m₂‖ ^ (Fintype.card ι - 1) * ‖m₁ - m₂‖
参数：f : MultilinearMap 𝕜 E G；hC : 0 <= C；H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖；m₁
 m₂ : forall i, E i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.prod_le_prod`：prod_le_prod (h0 : forall i in s, 0 <= f i) (h1 : f
orall i in s, f i <= g i) : ∏ i in s, f i <= ∏ i in s, g i
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用引理 `Mathlib.Meta.Positivity.ite_nonneg`：ite_nonneg [LE α] (ha : 0 <= a) (hb 
: 0 <= b) : 0 <= ite p a b
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `le_max_of_le_left`：le_max_of_le_left : a <= b -> a <= max b c
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `norm_le_pi_norm`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : Fintype ι] 
[inst_1 : (i : ι) → SeminormedAddGroup (G i)] (f : (i : ι) → G i)   (i : ι), ‖f 
i‖ ≤ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.prod_update_of_mem`：prod_update_of_mem [DecidableEq ι] {s : Finse
t ι} {i : ι} (h : i in s) (f : ι -> M) (b : M) : ∏ x in s, Function.update f i b
 x = b * ∏ x in…
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Finset.card_univ_sdiff`：Finset.card_univ_sdiff [DecidableEq α] [Fintype 
α] (s : Finset α) : #(univ \ s) = Fintype.card α - #s
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `MultilinearMap.norm_image_sub_le_of_bound'`：norm_image_sub_le_of_bound' 
[DecidableEq ι] (f : MultilinearMap 𝕜 E G) {C : Real} (hC : 0 <= C) (H : forall 
m, ‖f m‖ <= C * ∏ i, ‖m i‖) (m₁ …
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α
（共 51 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` satisfies a boundedness property around `0`, one can deduce a bound on `f
 m₁ - f m₂`
using the multilinearity. Here, we give a usable but not very precise version. S
ee
`norm_image_sub_le_of_bound'` for a more precise but less usable version. The bo
und is
`‖f m - f m'‖ ≤ C * card ι * ‖m - m'‖ * (max ‖m‖ ‖m'‖) ^ (card ι - 1)`.
-/
theorem norm_image_sub_le_of_bound (f : MultilinearMap 𝕜 E G)
    {C : ℝ} (hC : 0 ≤ C) (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) (m₁ m₂ : ∀ i, E i) :
    ‖f m₁ - f m₂‖ ≤ C * Fintype.card ι * max ‖m₁‖ ‖m₂‖ ^ (Fintype.card ι - 1) * ‖m₁ - m₂‖ := by
  classical
  have A :
    ∀ i : ι,
      ∏ j, (if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖) ≤
        ‖m₁ - m₂‖ * max ‖m₁‖ ‖m₂‖ ^ (Fintype.card ι - 1) := by
    intro i
    calc
      ∏ j, (if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖) ≤
          ∏ j : ι, Function.update (fun _ => max ‖m₁‖ ‖m₂‖) i ‖m₁ - m₂‖ j := by
        gcongr with j
        rcases eq_or_ne j i with rfl | h
        · simp only [ite_true, Function.update_self]
          exact norm_le_pi_norm (m₁ - m₂) _
        · simp [h, -le_sup_iff, -sup_le_iff, sup_le_sup, norm_le_pi_norm]
      _ = ‖m₁ - m₂‖ * max ‖m₁‖ ‖m₂‖ ^ (Fintype.card ι - 1) := by
        rw [prod_update_of_mem (Finset.mem_univ _)]
        simp [card_univ_sdiff]
  calc
    ‖f m₁ - f m₂‖ ≤ C * ∑ i, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ :=
      f.norm_image_sub_le_of_bound' hC H m₁ m₂
    _ ≤ C * ∑ _i, ‖m₁ - m₂‖ * max ‖m₁‖ ‖m₂‖ ^ (Fintype.card ι - 1) := by gcongr; apply A
    _ = C * Fintype.card ι * max ‖m₁‖ ‖m₂‖ ^ (Fintype.card ι - 1) * ‖m₁ - m₂‖ := by
      rw [sum_const, card_univ, nsmul_eq_mul]
      ring

/-- If a multilinear map satisfies an inequality `‖f m‖ ≤ C * ∏ i, ‖m i‖`, then it is
continuous. -/
/-
**MultilinearMap.continuous_of_bound** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：continuous_of_bound (f : MultilinearMap 𝕜 E G) (C : Real) (H : forall m, ‖
f m‖ <= C * ∏ i, ‖m i‖) : Continuous f
参数：f : MultilinearMap 𝕜 E G；C : Real；H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用引理 `Finset.prod_nonneg`：prod_nonneg (h0 : forall i in s, 0 <= f i) : 0 <= ∏ 
i in s, f i
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `continuousAt_of_locally_lipschitz`：continuousAt_of_locally_lipschitz {f 
: α -> β} {x : α} {r : Real} (hr : 0 < r) (K : Real) (h : forall y, dist y x < r
 -> dist (f y) (f x) <=…
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `norm_le_of_mem_closedBall`：∀ {E : Type u_5} [inst : SeminormedAddGroup E
] {a b : E} {r : ℝ}, b ∈ Metric.closedBall a r → ‖b‖ ≤ ‖a‖ + r
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `MultilinearMap.norm_image_sub_le_of_bound`：norm_image_sub_le_of_bound (f
 : MultilinearMap 𝕜 E G) {C : Real} (hC : 0 <= C) (H : forall m, ‖f m‖ <= C * ∏ 
i, ‖m i‖) (m₁ m₂ : forall i, E …
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
If a multilinear map satisfies an inequality `‖f m‖ ≤ C * ∏ i, ‖m i‖`, then it i
s
continuous.
-/
theorem continuous_of_bound (f : MultilinearMap 𝕜 E G) (C : ℝ) (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) :
    Continuous f := by
  let D := max C 1
  have D_pos : 0 ≤ D := le_trans zero_le_one (le_max_right _ _)
  replace H (m) : ‖f m‖ ≤ D * ∏ i, ‖m i‖ :=
    (H m).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) <| by positivity)
  refine continuous_iff_continuousAt.2 fun m => ?_
  refine
    continuousAt_of_locally_lipschitz zero_lt_one
      (D * Fintype.card ι * (‖m‖ + 1) ^ (Fintype.card ι - 1)) fun m' h' => ?_
  rw [dist_eq_norm, dist_eq_norm]
  have : max ‖m'‖ ‖m‖ ≤ ‖m‖ + 1 := by
    simp [zero_le_one, norm_le_of_mem_closedBall (le_of_lt h')]
  calc
    ‖f m' - f m‖ ≤ D * Fintype.card ι * max ‖m'‖ ‖m‖ ^ (Fintype.card ι - 1) * ‖m' - m‖ :=
      f.norm_image_sub_le_of_bound D_pos H m' m
    _ ≤ D * Fintype.card ι * (‖m‖ + 1) ^ (Fintype.card ι - 1) * ‖m' - m‖ := by gcongr

/-- Constructing a continuous multilinear map from a multilinear map satisfying a boundedness
condition. -/
/-
**MultilinearMap.mkContinuous** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：mkContinuous (f : MultilinearMap 𝕜 E G) (C : Real) (H : forall m, ‖f m‖ <=
 C * ∏ i, ‖m i‖) : ContinuousMultilinearMap 𝕜 E G
参数：f : MultilinearMap 𝕜 E G；C : Real；H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.continuous_of_bound`：continuous_of_bound (f : Multilinear
Map 𝕜 E G) (C : Real) (H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖) : Continuous f

--- 原说明 ---
Constructing a continuous multilinear map from a multilinear map satisfying a bo
undedness
condition.
-/
def mkContinuous (f : MultilinearMap 𝕜 E G) (C : ℝ) (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) :
    ContinuousMultilinearMap 𝕜 E G :=
  { f with cont := f.continuous_of_bound C H }

@[simp]
/-
**MultilinearMap.coe_mkContinuous** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：coe_mkContinuous (f : MultilinearMap 𝕜 E G) (C : Real) (H : forall m, ‖f m
‖ <= C * ∏ i, ‖m i‖) : ⇑(f.mkContinuous C H) = f
参数：f : MultilinearMap 𝕜 E G；C : Real；H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mkContinuous (f : MultilinearMap 𝕜 E G) (C : ℝ) (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) :
    ⇑(f.mkContinuous C H) = f :=
  rfl

/-- Given a multilinear map in `n` variables, if one restricts it to `k` variables putting `z` on
the other coordinates, then the resulting restricted function satisfies an inequality
`‖f.restr v‖ ≤ C * ‖z‖^(n-k) * Π ‖v i‖` if the original function satisfies `‖f v‖ ≤ C * Π ‖v i‖`. -/
/-
**MultilinearMap.restr_norm_le** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：restr_norm_le {k n : Nat} (f : MultilinearMap 𝕜 (fun _ : Fin n => G) G') (
s : Finset (Fin n)) (hk : #s = k) (z : G) {C : Real} (H : forall m, ‖f m‖ <= C *
 ∏ i, ‖m i‖) (v : Fin k -> G) : ‖f.restr s hk z v‖ <= C * ‖z‖ ^ (n - k) * ∏ i, ‖
v i‖
参数：f : MultilinearMap 𝕜 (fun _ : Fin n => G) G'；s : Finset (Fin n)；hk : #s = k；z
 : G；H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖；v : Fin k -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Bijective.prod_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type 
u_3} [inst : Fintype ι] [inst_1 : Fintype κ] [inst_2 : CommMonoid M]   {e : ι → 
κ}, Function.Bijec…
· 使用定理 `OrderIso.bijective`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_
1 : LE β] (e : α ≃o β), Function.Bijective ⇑e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `apply_dite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst
 : Decidable P] (x : P → α) (y : ¬P → α),   f (dite P x y) = if h : P then f (x 
…
· 使用定理 `Fintype.prod_dite`：∀ {α : Type u_1} {β : Type u_2} [inst : Fintype α] {p
 : α → Prop} [inst_1 : DecidablePred p] [inst_2 : CommMonoid β]   (f : (a : α) →
 p a → …
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Fintype.card_of_subtype`：card_of_subtype {p : α -> Prop} (s : Finset α) 
(H : forall x : α, x in s ↔ p x) [Fintype { x // p x }] : card { x // p x } = #s
· 使用定理 `Finset.mem_compl`：mem_compl : a in sᶜ ↔ a ∉ s
· 使用定理 `Finset.card_compl`：Finset.card_compl [DecidableEq α] [Fintype α] (s : Fi
nset α) : #sᶜ = Fintype.card α - #s
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Fintype.instFastSubsingleton`：∀ (α : Type u_4), Meta.FastSubsingleton (F
intype α)

--- 原说明 ---
Given a multilinear map in `n` variables, if one restricts it to `k` variables p
utting `z` on
the other coordinates, then the resulting restricted function satisfies an inequ
ality
`‖f.restr v‖ ≤ C * ‖z‖^(n-k) * Π ‖v i‖` if the original function satisfies `‖f v
‖ ≤ C * Π ‖v i‖`.
-/
theorem restr_norm_le {k n : ℕ} (f : MultilinearMap 𝕜 (fun _ : Fin n => G) G')
    (s : Finset (Fin n)) (hk : #s = k) (z : G) {C : ℝ} (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖)
    (v : Fin k → G) : ‖f.restr s hk z v‖ ≤ C * ‖z‖ ^ (n - k) * ∏ i, ‖v i‖ := by
  rw [mul_right_comm, mul_assoc]
  convert! H _ using 2
  simp only [apply_dite norm, Fintype.prod_dite, prod_const ‖z‖, Finset.card_univ,
    Fintype.card_of_subtype sᶜ fun _ => mem_compl, card_compl, Fintype.card_fin, hk, ←
    (s.orderIsoOfFin hk).symm.bijective.prod_comp fun x => ‖v x‖]
  convert! rfl

end MultilinearMap

/-!
### Continuous multilinear maps

We define the norm `‖f‖` of a continuous multilinear map `f` in finitely many variables as the
smallest number such that `‖f m‖ ≤ ‖f‖ * ∏ i, ‖m i‖` for all `m`. We show that this
defines a normed space structure on `ContinuousMultilinearMap 𝕜 E G`.
-/

namespace ContinuousMultilinearMap

variable [Fintype ι]

/-
**ContinuousMultilinearMap.bound** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMultilinea
rMap`。
形式化陈述：bound (f : ContinuousMultilinearMap 𝕜 E G) : exists C : Real, 0 < C ∧ fora
ll m, ‖f m‖ <= C * ∏ i, ‖m i‖
参数：f : ContinuousMultilinearMap 𝕜 E G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.exists_bound_of_continuous`：exists_bound_of_continuous (f
 : MultilinearMap 𝕜 E G) (hf : Continuous f) : exists C : Real, 0 < C ∧ forall m
, ‖f m‖ <= C * ∏ i, ‖m i‖
· 使用定理 `ContinuousMultilinearMap.cont`：∀ {R : Type u} {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoid (M₁
 i)] [inst_2 : AddC…
-/
theorem bound (f : ContinuousMultilinearMap 𝕜 E G) :
    ∃ C : ℝ, 0 < C ∧ ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖ :=
  f.toMultilinearMap.exists_bound_of_continuous f.2

open Real

/-- The operator norm of a continuous multilinear map is the inf of all its bounds. -/
/-
**ContinuousMultilinearMap.opNorm** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMultiline
arMap`。
形式化陈述：opNorm (f : ContinuousMultilinearMap 𝕜 E G) : Real
参数：f : ContinuousMultilinearMap 𝕜 E G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The operator norm of a continuous multilinear map is the inf of all its bounds.
-/
def opNorm (f : ContinuousMultilinearMap 𝕜 E G) : ℝ :=
  sInf { c | 0 ≤ (c : ℝ) ∧ ∀ m, ‖f m‖ ≤ c * ∏ i, ‖m i‖ }
/-
**ContinuousMultilinearMap.hasOpNorm** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMultil
inearMap`。
形式化陈述：hasOpNorm : Norm (ContinuousMultilinearMap 𝕜 E G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasOpNorm : Norm (ContinuousMultilinearMap 𝕜 E G) :=
  ⟨opNorm⟩

/-- An alias of `ContinuousMultilinearMap.hasOpNorm` with non-dependent types to help typeclass
search. -/
/-
**ContinuousMultilinearMap.hasOpNorm'** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMulti
linearMap`。
形式化陈述：hasOpNorm' : Norm (ContinuousMultilinearMap 𝕜 (fun _ : ι => G) G')
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An alias of `ContinuousMultilinearMap.hasOpNorm` with non-dependent types to hel
p typeclass
search.
-/
instance hasOpNorm' : Norm (ContinuousMultilinearMap 𝕜 (fun _ : ι => G) G') :=
  ContinuousMultilinearMap.hasOpNorm
/-
**ContinuousMultilinearMap.norm_def** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMultili
nearMap`。
形式化陈述：norm_def (f : ContinuousMultilinearMap 𝕜 E G) : ‖f‖ = sInf { c | 0 <= (c :
 Real) ∧ forall m, ‖f m‖ <= c * ∏ i, ‖m i‖ }
参数：f : ContinuousMultilinearMap 𝕜 E G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem norm_def (f : ContinuousMultilinearMap 𝕜 E G) :
    ‖f‖ = sInf { c | 0 ≤ (c : ℝ) ∧ ∀ m, ‖f m‖ ≤ c * ∏ i, ‖m i‖ } :=
  rfl

-- So that invocations of `le_csInf` make sense: we show that the set of
-- bounds is nonempty and bounded below.
/-
**ContinuousMultilinearMap.bounds_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
MultilinearMap`。
形式化陈述：bounds_nonempty {f : ContinuousMultilinearMap 𝕜 E G} : exists c, c in { c 
| 0 <= c ∧ forall m, ‖f m‖ <= c * ∏ i, ‖m i‖ }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.bound`：bound (f : ContinuousMultilinearMap 𝕜 E 
G) : exists C : Real, 0 < C ∧ forall m, ‖f m‖ <= C * ∏ i, ‖m i‖
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem bounds_nonempty {f : ContinuousMultilinearMap 𝕜 E G} :
    ∃ c, c ∈ { c | 0 ≤ c ∧ ∀ m, ‖f m‖ ≤ c * ∏ i, ‖m i‖ } :=
  let ⟨M, hMp, hMb⟩ := f.bound
  ⟨M, le_of_lt hMp, hMb⟩
/-
**ContinuousMultilinearMap.bounds_bddBelow** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
MultilinearMap`。
形式化陈述：bounds_bddBelow {f : ContinuousMultilinearMap 𝕜 E G} : BddBelow { c | 0 <=
 c ∧ forall m, ‖f m‖ <= c * ∏ i, ‖m i‖ }
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bounds_bddBelow {f : ContinuousMultilinearMap 𝕜 E G} :
    BddBelow { c | 0 ≤ c ∧ ∀ m, ‖f m‖ ≤ c * ∏ i, ‖m i‖ } :=
  ⟨0, fun _ ⟨hn, _⟩ => hn⟩
/-
**ContinuousMultilinearMap.isLeast_opNorm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousM
ultilinearMap`。
形式化陈述：isLeast_opNorm (f : ContinuousMultilinearMap 𝕜 E G) : IsLeast {c : Real | 
0 <= c ∧ forall m, ‖f m‖ <= c * ∏ i, ‖m i‖} ‖f‖
参数：f : ContinuousMultilinearMap 𝕜 E G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.isLeast_csInf`：IsClosed.isLeast_csInf {s : Set α} (hc : IsClose
d s) (hs : s.Nonempty) (B : BddBelow s) : IsLeast s (sInf s)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ofPred_forall`：ofPred_forall (p : ι -> β -> Prop) : { x | forall i, 
p i x } = ⋂ i, { x | p i x }
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用定理 `isClosed_Ici`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Preor
der α] [ClosedIciTopology α] {a : α}, IsClosed (Set.Ici a)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `isClosed_iInter`：isClosed_iInter {f : ι -> Set X} (h : forall i, IsClose
d (f i)) : IsClosed (⋂ i, f i)
· 使用定理 `isClosed_le`：isClosed_le [TopologicalSpace β] {f g : β -> α} (hf : Conti
nuous f) (hg : Continuous g) : IsClosed { b | f b <= g b }
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `continuous_mul_const`：continuous_mul_const (m : M) : Continuous (· * m)
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `ContinuousMultilinearMap.bounds_nonempty`：bounds_nonempty {f : Continuou
sMultilinearMap 𝕜 E G} : exists c, c in { c | 0 <= c ∧ forall m, ‖f m‖ <= c * ∏ 
i, ‖m i‖ }
· 使用定理 `ContinuousMultilinearMap.bounds_bddBelow`：bounds_bddBelow {f : Continuou
sMultilinearMap 𝕜 E G} : BddBelow { c | 0 <= c ∧ forall m, ‖f m‖ <= c * ∏ i, ‖m 
i‖ }
-/
theorem isLeast_opNorm (f : ContinuousMultilinearMap 𝕜 E G) :
    IsLeast {c : ℝ | 0 ≤ c ∧ ∀ m, ‖f m‖ ≤ c * ∏ i, ‖m i‖} ‖f‖ := by
  refine IsClosed.isLeast_csInf ?_ bounds_nonempty bounds_bddBelow
  simp only [Set.ofPred_and, Set.ofPred_forall]
  exact isClosed_Ici.inter (isClosed_iInter fun m ↦ isClosed_le continuous_const (by fun_prop))
/-
**ContinuousMultilinearMap.opNorm_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMu
ltilinearMap`。
形式化陈述：opNorm_nonneg (f : ContinuousMultilinearMap 𝕜 E G) : 0 <= ‖f‖
参数：f : ContinuousMultilinearMap 𝕜 E G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.sInf_nonneg`：sInf_nonneg (hs : forall x in s, 0 <= x) : 0 <= sInf s
-/
theorem opNorm_nonneg (f : ContinuousMultilinearMap 𝕜 E G) : 0 ≤ ‖f‖ :=
  Real.sInf_nonneg fun _ ⟨hx, _⟩ => hx

/-- The fundamental property of the operator norm of a continuous multilinear map:
`‖f m‖` is bounded by `‖f‖` times the product of the `‖m i‖`. -/
/-
**ContinuousMultilinearMap.le_opNorm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMultil
inearMap`。
形式化陈述：le_opNorm (f : ContinuousMultilinearMap 𝕜 E G) (m : forall i, E i) : ‖f m‖
 <= ‖f‖ * ∏ i, ‖m i‖
参数：f : ContinuousMultilinearMap 𝕜 E G；m : forall i, E i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ContinuousMultilinearMap.isLeast_opNorm`：isLeast_opNorm (f : ContinuousM
ultilinearMap 𝕜 E G) : IsLeast {c : Real | 0 <= c ∧ forall m, ‖f m‖ <= c * ∏ i, 
‖m i‖} ‖f‖

--- 原说明 ---
The fundamental property of the operator norm of a continuous multilinear map:
`‖f m‖` is bounded by `‖f‖` times the product of the `‖m i‖`.
-/
theorem le_opNorm (f : ContinuousMultilinearMap 𝕜 E G) (m : ∀ i, E i) :
    ‖f m‖ ≤ ‖f‖ * ∏ i, ‖m i‖ :=
  f.isLeast_opNorm.1.2 m
/-
**ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le** 是 Mathlib 中的一个定理，位于命
名空间 `ContinuousMultilinearMap`。
形式化陈述：le_mul_prod_of_opNorm_le_of_le {f : ContinuousMultilinearMap 𝕜 E G} {m : f
orall i, E i} {C : Real} {b : ι -> Real} (hC : ‖f‖ <= C) (hm : forall i, ‖m i‖ <
= b i) : ‖f m‖ <= C * ∏ i, b i
参数：hC : ‖f‖ <= C；hm : forall i, ‖m i‖ <= b i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `ContinuousMultilinearMap.le_opNorm`：le_opNorm (f : ContinuousMultilinear
Map 𝕜 E G) (m : forall i, E i) : ‖f m‖ <= ‖f‖ * ∏ i, ‖m i‖
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用引理 `Finset.prod_le_prod`：prod_le_prod (h0 : forall i in s, 0 <= f i) (h1 : f
orall i in s, f i <= g i) : ∏ i in s, f i <= ∏ i in s, g i
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `Finset.prod_nonneg`：prod_nonneg (h0 : forall i in s, 0 <= f i) : 0 <= ∏ 
i in s, f i
· 使用定理 `ContinuousMultilinearMap.opNorm_nonneg`：opNorm_nonneg (f : ContinuousMul
tilinearMap 𝕜 E G) : 0 <= ‖f‖
-/
theorem le_mul_prod_of_opNorm_le_of_le {f : ContinuousMultilinearMap 𝕜 E G}
    {m : ∀ i, E i} {C : ℝ} {b : ι → ℝ} (hC : ‖f‖ ≤ C) (hm : ∀ i, ‖m i‖ ≤ b i) :
    ‖f m‖ ≤ C * ∏ i, b i :=
  (f.le_opNorm m).trans <| by gcongr; exacts [f.opNorm_nonneg.trans hC, hm _]
/-
**ContinuousMultilinearMap.le_opNorm_mul_prod_of_le** 是 Mathlib 中的一个定理，位于命名空间 `C
ontinuousMultilinearMap`。
形式化陈述：le_opNorm_mul_prod_of_le (f : ContinuousMultilinearMap 𝕜 E G) {m : forall 
i, E i} {b : ι -> Real} (hm : forall i, ‖m i‖ <= b i) : ‖f m‖ <= ‖f‖ * ∏ i, b i
参数：f : ContinuousMultilinearMap 𝕜 E G；hm : forall i, ‖m i‖ <= b i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le`：le_mul_prod_of_
opNorm_le_of_le {f : ContinuousMultilinearMap 𝕜 E G} {m : forall i, E i} {C : Re
al} {b : ι -> Real} (hC : ‖f‖ <= C) (hm : for…
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem le_opNorm_mul_prod_of_le (f : ContinuousMultilinearMap 𝕜 E G)
    {m : ∀ i, E i} {b : ι → ℝ} (hm : ∀ i, ‖m i‖ ≤ b i) : ‖f m‖ ≤ ‖f‖ * ∏ i, b i :=
  le_mul_prod_of_opNorm_le_of_le le_rfl hm
/-
**ContinuousMultilinearMap.le_opNorm_mul_pow_card_of_le** 是 Mathlib 中的一个定理，位于命名空
间 `ContinuousMultilinearMap`。
形式化陈述：le_opNorm_mul_pow_card_of_le (f : ContinuousMultilinearMap 𝕜 E G) {m b} (h
m : ‖m‖ <= b) : ‖f m‖ <= ‖f‖ * b ^ Fintype.card ι
参数：f : ContinuousMultilinearMap 𝕜 E G；hm : ‖m‖ <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `ContinuousMultilinearMap.le_opNorm_mul_prod_of_le`：le_opNorm_mul_prod_of
_le (f : ContinuousMultilinearMap 𝕜 E G) {m : forall i, E i} {b : ι -> Real} (hm
 : forall i, ‖m i‖ <= b i) : ‖f m‖ <= ‖…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_le_pi_norm`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : Fintype ι] 
[inst_1 : (i : ι) → SeminormedAddGroup (G i)] (f : (i : ι) → G i)   (i : ι), ‖f 
i‖ ≤ …
-/
theorem le_opNorm_mul_pow_card_of_le (f : ContinuousMultilinearMap 𝕜 E G) {m b} (hm : ‖m‖ ≤ b) :
    ‖f m‖ ≤ ‖f‖ * b ^ Fintype.card ι := by
  simpa only [prod_const] using! f.le_opNorm_mul_prod_of_le fun i => (norm_le_pi_norm m i).trans hm
/-
**ContinuousMultilinearMap.le_opNorm_mul_pow_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Co
ntinuousMultilinearMap`。
形式化陈述：le_opNorm_mul_pow_of_le {n : Nat} {Ei : Fin n -> Type*} [forall i, Seminor
medAddCommGroup (Ei i)] [forall i, NormedSpace 𝕜 (Ei i)] (f : ContinuousMultilin
earMap 𝕜 Ei G) {m : forall i, Ei i} {b : Real} (hm : ‖m‖ <= b) : ‖f m‖ <= ‖f‖ * 
b ^ n
参数：Ei i；Ei i；f : ContinuousMultilinearMap 𝕜 Ei G；hm : ‖m‖ <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `ContinuousMultilinearMap.le_opNorm_mul_pow_card_of_le`：le_opNorm_mul_pow
_card_of_le (f : ContinuousMultilinearMap 𝕜 E G) {m b} (hm : ‖m‖ <= b) : ‖f m‖ <
= ‖f‖ * b ^ Fintype.card ι
-/
theorem le_opNorm_mul_pow_of_le {n : ℕ} {Ei : Fin n → Type*} [∀ i, SeminormedAddCommGroup (Ei i)]
    [∀ i, NormedSpace 𝕜 (Ei i)] (f : ContinuousMultilinearMap 𝕜 Ei G) {m : ∀ i, Ei i} {b : ℝ}
    (hm : ‖m‖ ≤ b) : ‖f m‖ ≤ ‖f‖ * b ^ n := by
  simpa only [Fintype.card_fin] using f.le_opNorm_mul_pow_card_of_le hm
/-
**ContinuousMultilinearMap.le_of_opNorm_le** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
MultilinearMap`。
形式化陈述：le_of_opNorm_le {f : ContinuousMultilinearMap 𝕜 E G} {C : Real} (h : ‖f‖ <
= C) (m : forall i, E i) : ‖f m‖ <= C * ∏ i, ‖m i‖
参数：h : ‖f‖ <= C；m : forall i, E i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le`：le_mul_prod_of_
opNorm_le_of_le {f : ContinuousMultilinearMap 𝕜 E G} {m : forall i, E i} {C : Re
al} {b : ι -> Real} (hC : ‖f‖ <= C) (hm : for…
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem le_of_opNorm_le {f : ContinuousMultilinearMap 𝕜 E G} {C : ℝ} (h : ‖f‖ ≤ C) (m : ∀ i, E i) :
    ‖f m‖ ≤ C * ∏ i, ‖m i‖ :=
  le_mul_prod_of_opNorm_le_of_le h fun _ ↦ le_rfl
/-
**ContinuousMultilinearMap.ratio_le_opNorm** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
MultilinearMap`。
形式化陈述：ratio_le_opNorm (f : ContinuousMultilinearMap 𝕜 E G) (m : forall i, E i) :
 (‖f m‖ / ∏ i, ‖m i‖) <= ‖f‖
参数：f : ContinuousMultilinearMap 𝕜 E G；m : forall i, E i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `div_le_of_le_mul₀`：div_le_of_le_mul₀ (hb : 0 <= b) (hc : 0 <= c) (h : a 
<= c * b) : a / b <= c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用引理 `Finset.prod_nonneg`：prod_nonneg (h0 : forall i in s, 0 <= f i) : 0 <= ∏ 
i in s, f i
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `ContinuousMultilinearMap.opNorm_nonneg`：opNorm_nonneg (f : ContinuousMul
tilinearMap 𝕜 E G) : 0 <= ‖f‖
· 使用定理 `ContinuousMultilinearMap.le_opNorm`：le_opNorm (f : ContinuousMultilinear
Map 𝕜 E G) (m : forall i, E i) : ‖f m‖ <= ‖f‖ * ∏ i, ‖m i‖
-/
theorem ratio_le_opNorm (f : ContinuousMultilinearMap 𝕜 E G) (m : ∀ i, E i) :
    (‖f m‖ / ∏ i, ‖m i‖) ≤ ‖f‖ :=
  div_le_of_le_mul₀ (by positivity) (opNorm_nonneg _) (f.le_opNorm m)

/-- The image of the unit ball under a continuous multilinear map is bounded. -/
/-
**ContinuousMultilinearMap.unit_le_opNorm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousM
ultilinearMap`。
形式化陈述：unit_le_opNorm (f : ContinuousMultilinearMap 𝕜 E G) {m : forall i, E i} (h
 : ‖m‖ <= 1) : ‖f m‖ <= ‖f‖
参数：f : ContinuousMultilinearMap 𝕜 E G；h : ‖m‖ <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `ContinuousMultilinearMap.le_opNorm_mul_pow_card_of_le`：le_opNorm_mul_pow
_card_of_le (f : ContinuousMultilinearMap 𝕜 E G) {m b} (hm : ‖m‖ <= b) : ‖f m‖ <
= ‖f‖ * b ^ Fintype.card ι
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
The image of the unit ball under a continuous multilinear map is bounded.
-/
theorem unit_le_opNorm (f : ContinuousMultilinearMap 𝕜 E G) {m : ∀ i, E i} (h : ‖m‖ ≤ 1) :
    ‖f m‖ ≤ ‖f‖ :=
  (le_opNorm_mul_pow_card_of_le f h).trans <| by simp

/-- If one controls the norm of every `f x`, then one controls the norm of `f`. -/
/-
**ContinuousMultilinearMap.opNorm_le_bound** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
MultilinearMap`。
形式化陈述：opNorm_le_bound {f : ContinuousMultilinearMap 𝕜 E G} {M : Real} (hMp : 0 <
= M) (hM : forall m, ‖f m‖ <= M * ∏ i, ‖m i‖) : ‖f‖ <= M
参数：hMp : 0 <= M；hM : forall m, ‖f m‖ <= M * ∏ i, ‖m i‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csInf_le`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, BddBelow s → a ∈ s → sInf s ≤ a
· 使用定理 `ContinuousMultilinearMap.bounds_bddBelow`：bounds_bddBelow {f : Continuou
sMultilinearMap 𝕜 E G} : BddBelow { c | 0 <= c ∧ forall m, ‖f m‖ <= c * ∏ i, ‖m 
i‖ }

--- 原说明 ---
If one controls the norm of every `f x`, then one controls the norm of `f`.
-/
theorem opNorm_le_bound {f : ContinuousMultilinearMap 𝕜 E G}
    {M : ℝ} (hMp : 0 ≤ M) (hM : ∀ m, ‖f m‖ ≤ M * ∏ i, ‖m i‖) : ‖f‖ ≤ M :=
  csInf_le bounds_bddBelow ⟨hMp, hM⟩
/-
**ContinuousMultilinearMap.opNorm_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMu
ltilinearMap`。
形式化陈述：opNorm_le_iff {f : ContinuousMultilinearMap 𝕜 E G} {C : Real} (hC : 0 <= C
) : ‖f‖ <= C ↔ forall m, ‖f m‖ <= C * ∏ i, ‖m i‖
参数：hC : 0 <= C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.le_of_opNorm_le`：le_of_opNorm_le {f : Continuou
sMultilinearMap 𝕜 E G} {C : Real} (h : ‖f‖ <= C) (m : forall i, E i) : ‖f m‖ <= 
C * ∏ i, ‖m i‖
· 使用定理 `ContinuousMultilinearMap.opNorm_le_bound`：opNorm_le_bound {f : Continuou
sMultilinearMap 𝕜 E G} {M : Real} (hMp : 0 <= M) (hM : forall m, ‖f m‖ <= M * ∏ 
i, ‖m i‖) : ‖f‖ <= M
-/
theorem opNorm_le_iff {f : ContinuousMultilinearMap 𝕜 E G} {C : ℝ} (hC : 0 ≤ C) :
    ‖f‖ ≤ C ↔ ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖ :=
  ⟨fun h _ ↦ le_of_opNorm_le h _, opNorm_le_bound hC⟩

/-- The operator norm satisfies the triangle inequality. -/
/-
**ContinuousMultilinearMap.opNorm_add_le** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMu
ltilinearMap`。
形式化陈述：opNorm_add_le (f g : ContinuousMultilinearMap 𝕜 E G) : ‖f + g‖ <= ‖f‖ + ‖g
‖
参数：f g : ContinuousMultilinearMap 𝕜 E G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.opNorm_le_bound`：opNorm_le_bound {f : Continuou
sMultilinearMap 𝕜 E G} {M : Real} (hMp : 0 <= M) (hM : forall m, ‖f m‖ <= M * ∏ 
i, ‖m i‖) : ‖f‖ <= M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ContinuousMultilinearMap.opNorm_nonneg`：opNorm_nonneg (f : ContinuousMul
tilinearMap 𝕜 E G) : 0 <= ‖f‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `norm_add_le_of_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {a₁ a₂
 : E} {r₁ r₂ : ℝ}, ‖a₁‖ ≤ r₁ → ‖a₂‖ ≤ r₂ → ‖a₁ + a₂‖ ≤ r₁ + r₂
· 使用定理 `ContinuousMultilinearMap.le_opNorm`：le_opNorm (f : ContinuousMultilinear
Map 𝕜 E G) (m : forall i, E i) : ‖f m‖ <= ‖f‖ * ∏ i, ‖m i‖

--- 原说明 ---
The operator norm satisfies the triangle inequality.
-/
theorem opNorm_add_le (f g : ContinuousMultilinearMap 𝕜 E G) : ‖f + g‖ ≤ ‖f‖ + ‖g‖ :=
  opNorm_le_bound (add_nonneg (opNorm_nonneg f) (opNorm_nonneg g)) fun x => by
    rw [add_mul]
    exact norm_add_le_of_le (le_opNorm _ _) (le_opNorm _ _)
/-
**ContinuousMultilinearMap.opNorm_zero** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMult
ilinearMap`。
形式化陈述：opNorm_zero : ‖(0 : ContinuousMultilinearMap 𝕜 E G)‖ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `ContinuousMultilinearMap.opNorm_nonneg`：opNorm_nonneg (f : ContinuousMul
tilinearMap 𝕜 E G) : 0 <= ‖f‖
· 使用定理 `ContinuousMultilinearMap.opNorm_le_bound`：opNorm_le_bound {f : Continuou
sMultilinearMap 𝕜 E G} {M : Real} (hMp : 0 <= M) (hM : forall m, ‖f m‖ <= M * ∏ 
i, ‖m i‖) : ‖f‖ <= M
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousMultilinearMap.instIsZeroApplyForall`：∀ {R : Type u} {ι : Type
 v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → 
AddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem opNorm_zero : ‖(0 : ContinuousMultilinearMap 𝕜 E G)‖ = 0 :=
  (opNorm_nonneg _).antisymm' <| opNorm_le_bound le_rfl fun m => by simp
/-
**ContinuousMultilinearMap.opNorm_neg** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMulti
linearMap`。
形式化陈述：opNorm_neg (f : ContinuousMultilinearMap 𝕜 E G) : ‖-f‖ = ‖f‖
参数：f : ContinuousMultilinearMap 𝕜 E G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `ContinuousMultilinearMap.instIsNegApplyForall`：∀ {R : Type u} {ι : Type 
v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Ring R] [inst_1 : (i : ι) → AddComm
Group (M₁ i)]   [inst_2 : AddCommGr…
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem opNorm_neg (f : ContinuousMultilinearMap 𝕜 E G) : ‖-f‖ = ‖f‖ := by simp [norm_def]

section

variable {𝕜' : Type*} [SeminormedRing 𝕜'] [Module 𝕜' G] [IsBoundedSMul 𝕜' G] [SMulCommClass 𝕜 𝕜' G]

/-
**ContinuousMultilinearMap.opNorm_smul_le** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousM
ultilinearMap`。
形式化陈述：opNorm_smul_le (c : 𝕜') (f : ContinuousMultilinearMap 𝕜 E G) : ‖c • f‖ <= 
‖c‖ * ‖f‖
参数：c : 𝕜'；f : ContinuousMultilinearMap 𝕜 E G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.opNorm_le_bound`：opNorm_le_bound {f : Continuou
sMultilinearMap 𝕜 E G} {M : Real} (hMp : 0 <= M) (hM : forall m, ‖f m‖ <= M * ∏ 
i, ‖m i‖) : ‖f‖ <= M
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `ContinuousMultilinearMap.opNorm_nonneg`：opNorm_nonneg (f : ContinuousMul
tilinearMap 𝕜 E G) : 0 <= ‖f‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousMultilinearMap.instIsSMulApplyForall`：∀ {ι : Type v} {M₁ : ι →
 Type w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCo
mmMonoid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `norm_smul_le`：norm_smul_le (r : α) (x : β) : ‖r • x‖ <= ‖r‖ * ‖x‖
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `ContinuousMultilinearMap.le_opNorm`：le_opNorm (f : ContinuousMultilinear
Map 𝕜 E G) (m : forall i, E i) : ‖f m‖ <= ‖f‖ * ∏ i, ‖m i‖
-/
theorem opNorm_smul_le (c : 𝕜') (f : ContinuousMultilinearMap 𝕜 E G) : ‖c • f‖ ≤ ‖c‖ * ‖f‖ :=
  (c • f).opNorm_le_bound (mul_nonneg (norm_nonneg _) (opNorm_nonneg _)) fun m ↦ by
    grw [smul_apply, norm_smul_le, mul_assoc, le_opNorm]

variable (𝕜 E G) in
/-- Operator seminorm on the space of continuous multilinear maps, as `Seminorm`.

We use this seminorm
to define a `SeminormedAddCommGroup` structure on `ContinuousMultilinearMap 𝕜 E G`,
but we have to override the projection `UniformSpace`
so that it is definitionally equal to the one coming from the topologies on `E` and `G`. -/
/-
**ContinuousMultilinearMap.seminorm** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMultili
nearMap`。
形式化陈述：(𝕜 : Type u) →   {ι : Type v} →     (E : ι → Type wE) →       (G : Type wG
) →         [inst : NontriviallyNormedField 𝕜] →           [inst_1 : (i : ι) → S
eminormedAddCommGroup (E i)] →             [inst_2 : (i : ι) → NormedSpace 𝕜 (E 
i)] →               [inst_3 : SeminormedAddCommGroup G] →                 [inst_
4 : NormedSpace 𝕜 G] → [Fintype ι] → Seminorm 𝕜 (ContinuousMultilinearMap 𝕜 E G)
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousMultilinearMap.opNorm_zero`：opNorm_zero : ‖(0 : ContinuousMult
ilinearMap 𝕜 E G)‖ = 0
· 使用定理 `ContinuousMultilinearMap.opNorm_add_le`：opNorm_add_le (f g : ContinuousM
ultilinearMap 𝕜 E G) : ‖f + g‖ <= ‖f‖ + ‖g‖

--- 原说明 ---
Operator seminorm on the space of continuous multilinear maps, as `Seminorm`.

We use this seminorm
to define a `SeminormedAddCommGroup` structure on `ContinuousMultilinearMap 𝕜 E 
G`,
but we have to override the projection `UniformSpace`
so that it is definitionally equal to the one coming from the topologies on `E` 
and `G`.
-/
protected def seminorm : Seminorm 𝕜 (ContinuousMultilinearMap 𝕜 E G) :=
  .ofSMulLE norm opNorm_zero opNorm_add_le fun c f ↦ f.opNorm_smul_le c
/-
**ContinuousMultilinearMap.uniformity_eq_seminorm** 是 Mathlib 中的一个引理，位于命名空间 `Con
tinuousMultilinearMap`。
形式化陈述：uniformity_eq_seminorm : 𝓤 (ContinuousMultilinearMap 𝕜 E G) = ⨅ r > 0, 𝓟 {
f | ‖-f.1 + f.2‖ < r}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousMultilinearMap.opNorm_neg`：opNorm_neg (f : ContinuousMultiline
arMap 𝕜 E G) : ‖-f‖ = ‖f‖
· 使用定理 `neg_add`：neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R} (_ : -a₁ = b₁) (_ : 
-a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Seminorm.uniformity_eq_of_hasBasis`：uniformity_eq_of_hasBasis {ι} [Unifo
rmSpace E] [IsUniformAddGroup E] [ContinuousConstSMul 𝕜 E] {p' : ι -> Prop} {s :
 ι -> Set E} (p : Semino…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousMultilinearMap.hasBasis_nhds_zero_of_basis`：hasBasis_nhds_zero
_of_basis {ι : Type*} {p : ι -> Prop} {b : ι -> Set F} (h : (𝓝 (0 : F)).HasBasis
 p b) : (𝓝 (0 : ContinuousMultilinearMap 𝕜…
· 使用定理 `Metric.nhds_basis_closedBall`：nhds_basis_closedBall : (𝓝 x).HasBasis (fu
n ε : Real => 0 < ε) (closedBall x)
· 使用定理 `NormedField.exists_lt_norm`：exists_lt_norm (r : Real) : exists x : α, r 
< ‖x‖
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `ContinuousMultilinearMap.hasBasis_nhds_zero`：hasBasis_nhds_zero : (𝓝 (0 
: ContinuousMultilinearMap 𝕜 E F)).HasBasis (fun SV : Set (Π i, E i) × Set F => 
IsVonNBounded 𝕜 SV.1 ∧ SV.2 in 𝓝 …
· 使用定理 `ContinuousMultilinearMap.opNorm_le_bound`：opNorm_le_bound {f : Continuou
sMultilinearMap 𝕜 E G} {M : Real} (hMp : 0 <= M) (hM : forall m, ‖f m‖ <= M * ∏ 
i, ‖m i‖) : ‖f‖ <= M
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
（共 62 条，此处仅展示前 30 条）
-/
lemma uniformity_eq_seminorm :
    𝓤 (ContinuousMultilinearMap 𝕜 E G) = ⨅ r > 0, 𝓟 {f | ‖-f.1 + f.2‖ < r} := by
  have A (f : ContinuousMultilinearMap 𝕜 E G × ContinuousMultilinearMap 𝕜 E G) :
      ‖-f.1 + f.2‖ = ‖f.1 - f.2‖ := by rw [← opNorm_neg, neg_add, neg_neg, sub_eq_add_neg]
  simp only [A]
  refine (ContinuousMultilinearMap.seminorm 𝕜 E G).uniformity_eq_of_hasBasis
    (ContinuousMultilinearMap.hasBasis_nhds_zero_of_basis Metric.nhds_basis_closedBall)
    ?_ fun (s, r) ⟨hs, hr⟩ ↦ ?_
  · rcases NormedField.exists_lt_norm 𝕜 1 with ⟨c, hc⟩
    have hc₀ : 0 < ‖c‖ := one_pos.trans hc
    simp only [hasBasis_nhds_zero.mem_iff, Prod.exists]
    use 1, closedBall 0 ‖c‖, closedBall 0 1
    suffices ∀ f : ContinuousMultilinearMap 𝕜 E G, (∀ x, ‖x‖ ≤ ‖c‖ → ‖f x‖ ≤ 1) → ‖f‖ ≤ 1 by
      simpa [NormedSpace.isVonNBounded_closedBall, closedBall_mem_nhds, Set.subset_def, Set.MapsTo]
    intro f hf
    refine opNorm_le_bound (by positivity) <|
      f.1.bound_of_shell_of_continuous f.2 (fun _ ↦ hc₀) (fun _ ↦ hc) fun x hcx hx ↦ ?_
    calc
      ‖f x‖ ≤ 1 := hf _ <| (pi_norm_le_iff_of_nonneg (norm_nonneg c)).2 fun i ↦ (hx i).le
      _ = ∏ i : ι, 1 := by simp
      _ ≤ ∏ i, ‖x i‖ := by gcongr with i; simpa only [div_self hc₀.ne'] using hcx i
      _ = 1 * ∏ i, ‖x i‖ := (one_mul _).symm
  · rcases (NormedSpace.isVonNBounded_iff' _).1 hs with ⟨ε, hε⟩
    rcases exists_pos_mul_lt hr (ε ^ Fintype.card ι) with ⟨δ, hδ₀, hδ⟩
    refine ⟨δ, hδ₀, fun f hf x hx ↦ ?_⟩
    simp only [Seminorm.mem_ball_zero, mem_closedBall_zero_iff] at hf ⊢
    replace hf : ‖f‖ ≤ δ := hf.le
    replace hx : ‖x‖ ≤ ε := hε x hx
    calc
      ‖f x‖ ≤ ‖f‖ * ε ^ Fintype.card ι := le_opNorm_mul_pow_card_of_le f hx
      _ ≤ δ * ε ^ Fintype.card ι := by have := (norm_nonneg x).trans hx; gcongr
      _ ≤ r := (mul_comm _ _).trans_le hδ.le
/-
**ContinuousMultilinearMap.instPseudoMetricSpace** 是 Mathlib 中的一个实例，位于命名空间 `Cont
inuousMultilinearMap`。
形式化陈述：instPseudoMetricSpace : PseudoMetricSpace (ContinuousMultilinearMap 𝕜 E G)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `ContinuousMultilinearMap.uniformity_eq_seminorm`：uniformity_eq_seminorm 
: 𝓤 (ContinuousMultilinearMap 𝕜 E G) = ⨅ r > 0, 𝓟 {f | ‖-f.1 + f.2‖ < r}
-/
instance instPseudoMetricSpace : PseudoMetricSpace (ContinuousMultilinearMap 𝕜 E G) :=
  .replaceUniformity
    (ContinuousMultilinearMap.seminorm 𝕜 E G).toSeminormedAddCommGroup.toPseudoMetricSpace
    uniformity_eq_seminorm

/-- Continuous multilinear maps themselves form a seminormed space with respect to
the operator norm. -/
/-
**ContinuousMultilinearMap.seminormedAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `Con
tinuousMultilinearMap`。
形式化陈述：seminormedAddCommGroup : SeminormedAddCommGroup (ContinuousMultilinearMap 
𝕜 E G)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E

--- 原说明 ---
Continuous multilinear maps themselves form a seminormed space with respect to
the operator norm.
-/
instance seminormedAddCommGroup :
    SeminormedAddCommGroup (ContinuousMultilinearMap 𝕜 E G) := ⟨fun _ _ ↦ rfl⟩

/-- An alias of `ContinuousMultilinearMap.seminormedAddCommGroup` with non-dependent types to help
typeclass search. -/
/-
**ContinuousMultilinearMap.seminormedAddCommGroup'** 是 Mathlib 中的一个实例，位于命名空间 `Co
ntinuousMultilinearMap`。
形式化陈述：seminormedAddCommGroup' : SeminormedAddCommGroup (ContinuousMultilinearMap
 𝕜 (fun _ : ι => G) G')
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An alias of `ContinuousMultilinearMap.seminormedAddCommGroup` with non-dependent
 types to help
typeclass search.
-/
instance seminormedAddCommGroup' :
    SeminormedAddCommGroup (ContinuousMultilinearMap 𝕜 (fun _ : ι => G) G') :=
  ContinuousMultilinearMap.seminormedAddCommGroup
/-
**ContinuousMultilinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMultilinearMap`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsBoundedSMul 𝕜' (ContinuousMultilinearMap 𝕜 E G) := .of_norm_smul_le opNorm_smul_le

section NormedField
variable {𝕜' : Type*} [NormedField 𝕜'] [NormedSpace 𝕜' G] [SMulCommClass 𝕜 𝕜' G]

/-
**ContinuousMultilinearMap.normedSpace** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMult
ilinearMap`。
形式化陈述：normedSpace : NormedSpace 𝕜' (ContinuousMultilinearMap 𝕜 E G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance normedSpace : NormedSpace 𝕜' (ContinuousMultilinearMap 𝕜 E G) :=
  ⟨fun c f => f.opNorm_smul_le c⟩

/-- An alias of `ContinuousMultilinearMap.normedSpace` with non-dependent types to help typeclass
search. -/
/-
**ContinuousMultilinearMap.normedSpace'** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMul
tilinearMap`。
形式化陈述：normedSpace' : NormedSpace 𝕜' (ContinuousMultilinearMap 𝕜 (fun _ : ι => G'
) G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An alias of `ContinuousMultilinearMap.normedSpace` with non-dependent types to h
elp typeclass
search.
-/
instance normedSpace' : NormedSpace 𝕜' (ContinuousMultilinearMap 𝕜 (fun _ : ι => G') G) :=
  ContinuousMultilinearMap.normedSpace

end NormedField

/-- The fundamental property of the operator norm of a continuous multilinear map:
`‖f m‖` is bounded by `‖f‖` times the product of the `‖m i‖`, `nnnorm` version. -/
/-
**ContinuousMultilinearMap.le_opNNNorm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMult
ilinearMap`。
形式化陈述：le_opNNNorm (f : ContinuousMultilinearMap 𝕜 E G) (m : forall i, E i) : ‖f 
m‖₊ <= ‖f‖₊ * ∏ i, ‖m i‖₊
参数：f : ContinuousMultilinearMap 𝕜 E G；m : forall i, E i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.coe_prod`：coe_prod (s : Finset ι) (f : ι -> Real>=0) : ↑(∏ a in s
, f a) = ∏ a in s, (f a : Real)
· 使用定理 `ContinuousMultilinearMap.le_opNorm`：le_opNorm (f : ContinuousMultilinear
Map 𝕜 E G) (m : forall i, E i) : ‖f m‖ <= ‖f‖ * ∏ i, ‖m i‖

--- 原说明 ---
The fundamental property of the operator norm of a continuous multilinear map:
`‖f m‖` is bounded by `‖f‖` times the product of the `‖m i‖`, `nnnorm` version.
-/
theorem le_opNNNorm (f : ContinuousMultilinearMap 𝕜 E G) (m : ∀ i, E i) :
    ‖f m‖₊ ≤ ‖f‖₊ * ∏ i, ‖m i‖₊ :=
  NNReal.coe_le_coe.1 <| by
    push_cast
    exact f.le_opNorm m
/-
**ContinuousMultilinearMap.le_of_opNNNorm_le** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usMultilinearMap`。
形式化陈述：le_of_opNNNorm_le (f : ContinuousMultilinearMap 𝕜 E G) {C : Real>=0} (h : 
‖f‖₊ <= C) (m : forall i, E i) : ‖f m‖₊ <= C * ∏ i, ‖m i‖₊
参数：f : ContinuousMultilinearMap 𝕜 E G；h : ‖f‖₊ <= C；m : forall i, E i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `ContinuousMultilinearMap.le_opNNNorm`：le_opNNNorm (f : ContinuousMultili
nearMap 𝕜 E G) (m : forall i, E i) : ‖f m‖₊ <= ‖f‖₊ * ∏ i, ‖m i‖₊
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem le_of_opNNNorm_le (f : ContinuousMultilinearMap 𝕜 E G)
    {C : ℝ≥0} (h : ‖f‖₊ ≤ C) (m : ∀ i, E i) : ‖f m‖₊ ≤ C * ∏ i, ‖m i‖₊ :=
  (f.le_opNNNorm m).trans <| mul_le_mul' h le_rfl
/-
**ContinuousMultilinearMap.opNNNorm_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
MultilinearMap`。
形式化陈述：opNNNorm_le_iff {f : ContinuousMultilinearMap 𝕜 E G} {C : Real>=0} : ‖f‖₊ 
<= C ↔ forall m, ‖f m‖₊ <= C * ∏ i, ‖m i‖₊
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ContinuousMultilinearMap.opNorm_le_iff`：opNorm_le_iff {f : ContinuousMul
tilinearMap 𝕜 E G} {C : Real} (hC : 0 <= C) : ‖f‖ <= C ↔ forall m, ‖f m‖ <= C * 
∏ i, ‖m i‖
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `NNReal.coe_prod`：coe_prod (s : Finset ι) (f : ι -> Real>=0) : ↑(∏ a in s
, f a) = ∏ a in s, (f a : Real)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem opNNNorm_le_iff {f : ContinuousMultilinearMap 𝕜 E G} {C : ℝ≥0} :
    ‖f‖₊ ≤ C ↔ ∀ m, ‖f m‖₊ ≤ C * ∏ i, ‖m i‖₊ := by
  simp only [← NNReal.coe_le_coe]; simp [opNorm_le_iff C.coe_nonneg, NNReal.coe_prod]
/-
**ContinuousMultilinearMap.isLeast_opNNNorm** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sMultilinearMap`。
形式化陈述：isLeast_opNNNorm (f : ContinuousMultilinearMap 𝕜 E G) : IsLeast {C : Real>
=0 | forall m, ‖f m‖₊ <= C * ∏ i, ‖m i‖₊} ‖f‖₊
参数：f : ContinuousMultilinearMap 𝕜 E G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `isLeast_Ici`：isLeast_Ici : IsLeast (Ici a) a
-/
theorem isLeast_opNNNorm (f : ContinuousMultilinearMap 𝕜 E G) :
    IsLeast {C : ℝ≥0 | ∀ m, ‖f m‖₊ ≤ C * ∏ i, ‖m i‖₊} ‖f‖₊ := by
  simpa only [← opNNNorm_le_iff] using! isLeast_Ici
/-
**ContinuousMultilinearMap.opNNNorm_prod** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMu
ltilinearMap`。
形式化陈述：opNNNorm_prod (f : ContinuousMultilinearMap 𝕜 E G) (g : ContinuousMultilin
earMap 𝕜 E G') : ‖f.prod g‖₊ = max ‖f‖₊ ‖g‖₊
参数：f : ContinuousMultilinearMap 𝕜 E G；g : ContinuousMultilinearMap 𝕜 E G'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem opNNNorm_prod (f : ContinuousMultilinearMap 𝕜 E G) (g : ContinuousMultilinearMap 𝕜 E G') :
    ‖f.prod g‖₊ = max ‖f‖₊ ‖g‖₊ :=
  eq_of_forall_ge_iff fun _ ↦ by
    simp only [opNNNorm_le_iff, prod_apply, Prod.nnnorm_def, max_le_iff, forall_and]
/-
**ContinuousMultilinearMap.opNorm_prod** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMult
ilinearMap`。
形式化陈述：opNorm_prod (f : ContinuousMultilinearMap 𝕜 E G) (g : ContinuousMultilinea
rMap 𝕜 E G') : ‖f.prod g‖ = max ‖f‖ ‖g‖
参数：f : ContinuousMultilinearMap 𝕜 E G；g : ContinuousMultilinearMap 𝕜 E G'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `ContinuousMultilinearMap.opNNNorm_prod`：opNNNorm_prod (f : ContinuousMul
tilinearMap 𝕜 E G) (g : ContinuousMultilinearMap 𝕜 E G') : ‖f.prod g‖₊ = max ‖f‖
₊ ‖g‖₊
-/
theorem opNorm_prod (f : ContinuousMultilinearMap 𝕜 E G) (g : ContinuousMultilinearMap 𝕜 E G') :
    ‖f.prod g‖ = max ‖f‖ ‖g‖ :=
  congr_arg NNReal.toReal (opNNNorm_prod f g)
/-
**ContinuousMultilinearMap.opNNNorm_pi** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMult
ilinearMap`。
形式化陈述：opNNNorm_pi [forall i', SeminormedAddCommGroup (E' i')] [forall i', Normed
Space 𝕜 (E' i')] (f : forall i', ContinuousMultilinearMap 𝕜 E (E' i')) : ‖pi f‖₊
 = ‖f‖₊
参数：E' i'；E' i'；f : forall i', ContinuousMultilinearMap 𝕜 E (E' i')。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
-/
theorem opNNNorm_pi
    [∀ i', SeminormedAddCommGroup (E' i')] [∀ i', NormedSpace 𝕜 (E' i')]
    (f : ∀ i', ContinuousMultilinearMap 𝕜 E (E' i')) : ‖pi f‖₊ = ‖f‖₊ :=
  eq_of_forall_ge_iff fun _ ↦ by simpa [opNNNorm_le_iff, pi_nnnorm_le_iff] using forall_comm
/-
**ContinuousMultilinearMap.opNorm_pi** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMultil
inearMap`。
形式化陈述：opNorm_pi {ι' : Type v'} [Fintype ι'] {E' : ι' -> Type wE'} [forall i', Se
minormedAddCommGroup (E' i')] [forall i', NormedSpace 𝕜 (E' i')] (f : forall i',
 ContinuousMultilinearMap 𝕜 E (E' i')) : ‖pi f‖ = ‖f‖
参数：E' i'；E' i'；f : forall i', ContinuousMultilinearMap 𝕜 E (E' i')。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `ContinuousMultilinearMap.opNNNorm_pi`：opNNNorm_pi [forall i', Seminormed
AddCommGroup (E' i')] [forall i', NormedSpace 𝕜 (E' i')] (f : forall i', Continu
ousMultilinearMap 𝕜 E (E' …
-/
theorem opNorm_pi {ι' : Type v'} [Fintype ι'] {E' : ι' → Type wE'}
    [∀ i', SeminormedAddCommGroup (E' i')] [∀ i', NormedSpace 𝕜 (E' i')]
    (f : ∀ i', ContinuousMultilinearMap 𝕜 E (E' i')) :
    ‖pi f‖ = ‖f‖ :=
  congr_arg NNReal.toReal (opNNNorm_pi f)

section

@[simp]
/-
**ContinuousMultilinearMap.norm_ofSubsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Contin
uousMultilinearMap`。
形式化陈述：norm_ofSubsingleton [Subsingleton ι] (i : ι) (f : G ->L[𝕜] G') : ‖ofSubsin
gleton 𝕜 G G' i f‖ = ‖f‖
参数：i : ι；f : G ->L[𝕜] G'。
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
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ContinuousMultilinearMap.ofSubsingleton_apply_apply`：∀ (R : Type u) {ι :
 Type v} (M₂ : Type w₂) (M₃ : Type w₃) [inst : Semiring R] [inst_1 : AddCommMono
id M₂]   [inst_2 : AddCommMonoid M₃] [ins…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Equiv.funUnique_symm_apply`：∀ (α : Sort u) (β : Sort u_1) [inst : Unique
 α], ⇑(Equiv.funUnique α β).symm = uniqueElim
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_ofSubsingleton [Subsingleton ι] (i : ι) (f : G →L[𝕜] G') :
    ‖ofSubsingleton 𝕜 G G' i f‖ = ‖f‖ := by
  let : Unique ι := uniqueOfSubsingleton i
  simp [norm_def, ContinuousLinearMap.norm_def, (Equiv.funUnique _ _).symm.surjective.forall]

@[simp]
/-
**ContinuousMultilinearMap.nnnorm_ofSubsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Cont
inuousMultilinearMap`。
形式化陈述：nnnorm_ofSubsingleton [Subsingleton ι] (i : ι) (f : G ->L[𝕜] G') : ‖ofSubs
ingleton 𝕜 G G' i f‖₊ = ‖f‖₊
参数：i : ι；f : G ->L[𝕜] G'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `ContinuousMultilinearMap.norm_ofSubsingleton`：norm_ofSubsingleton [Subsi
ngleton ι] (i : ι) (f : G ->L[𝕜] G') : ‖ofSubsingleton 𝕜 G G' i f‖ = ‖f‖
-/
theorem nnnorm_ofSubsingleton [Subsingleton ι] (i : ι) (f : G →L[𝕜] G') :
    ‖ofSubsingleton 𝕜 G G' i f‖₊ = ‖f‖₊ :=
  NNReal.eq <| norm_ofSubsingleton i f

variable (𝕜 G)

/-- Linear isometry between continuous linear maps from `G` to `G'`
and continuous `1`-multilinear maps from `G` to `G'`. -/
@[simps apply symm_apply]
/-
**ContinuousMultilinearMap.ofSubsingleton** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousM
ultilinearMap`。
形式化陈述：ofSubsingleton [Subsingleton ι] (i : ι) : (M₂ ->L[R] M₃) ≃ ContinuousMulti
linearMap R (fun _ : ι => M₂) M₃ where toFun f
参数：i : ι。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Linear isometry between continuous linear maps from `G` to `G'`
and continuous `1`-multilinear maps from `G` to `G'`.
-/
def ofSubsingletonₗᵢ [Subsingleton ι] (i : ι) :
    (G →L[𝕜] G') ≃ₗᵢ[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ G) G' :=
  { ofSubsingleton 𝕜 G G' i with
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl
    norm_map' := norm_ofSubsingleton i }
/-
**ContinuousMultilinearMap.norm_ofSubsingleton_id_le** 是 Mathlib 中的一个定理，位于命名空间 `
ContinuousMultilinearMap`。
形式化陈述：norm_ofSubsingleton_id_le [Subsingleton ι] (i : ι) : ‖ofSubsingleton 𝕜 G G
 i (.id _ _)‖ <= 1
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMultilinearMap.norm_ofSubsingleton`：norm_ofSubsingleton [Subsi
ngleton ι] (i : ι) (f : G ->L[𝕜] G') : ‖ofSubsingleton 𝕜 G G' i f‖ = ‖f‖
· 使用定理 `ContinuousLinearMap.norm_id_le`：norm_id_le : ‖ContinuousLinearMap.id 𝕜 E
‖ <= 1
-/
theorem norm_ofSubsingleton_id_le [Subsingleton ι] (i : ι) :
    ‖ofSubsingleton 𝕜 G G i (.id _ _)‖ ≤ 1 := by
  rw [norm_ofSubsingleton]
  apply ContinuousLinearMap.norm_id_le
/-
**ContinuousMultilinearMap.nnnorm_ofSubsingleton_id_le** 是 Mathlib 中的一个定理，位于命名空间
 `ContinuousMultilinearMap`。
形式化陈述：nnnorm_ofSubsingleton_id_le [Subsingleton ι] (i : ι) : ‖ofSubsingleton 𝕜 G
 G i (.id _ _)‖₊ <= 1
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.norm_ofSubsingleton_id_le`：norm_ofSubsingleton_
id_le [Subsingleton ι] (i : ι) : ‖ofSubsingleton 𝕜 G G i (.id _ _)‖ <= 1
-/
theorem nnnorm_ofSubsingleton_id_le [Subsingleton ι] (i : ι) :
    ‖ofSubsingleton 𝕜 G G i (.id _ _)‖₊ ≤ 1 :=
  norm_ofSubsingleton_id_le _ _ _

variable {G} (E)

@[simp]
/-
**ContinuousMultilinearMap.norm_constOfIsEmpty** 是 Mathlib 中的一个定理，位于命名空间 `Contin
uousMultilinearMap`。
形式化陈述：norm_constOfIsEmpty [IsEmpty ι] (x : G) : ‖constOfIsEmpty 𝕜 E x‖ = ‖x‖
参数：x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `ContinuousMultilinearMap.opNorm_le_bound`：opNorm_le_bound {f : Continuou
sMultilinearMap 𝕜 E G} {M : Real} (hMp : 0 <= M) (hM : forall m, ‖f m‖ <= M * ∏ 
i, ‖m i‖) : ‖f‖ <= M
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.prod_empty`：prod_empty [IsEmpty ι] (f : ι -> M) : ∏ x : ι, f x =
 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `ContinuousMultilinearMap.constOfIsEmpty_apply`：∀ (R : Type u) {ι : Type 
v} (M₁ : ι → Type w₁) {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → A
ddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `ContinuousMultilinearMap.le_opNorm`：le_opNorm (f : ContinuousMultilinear
Map 𝕜 E G) (m : forall i, E i) : ‖f m‖ <= ‖f‖ * ∏ i, ‖m i‖
-/
theorem norm_constOfIsEmpty [IsEmpty ι] (x : G) : ‖constOfIsEmpty 𝕜 E x‖ = ‖x‖ := by
  apply le_antisymm
  · refine opNorm_le_bound (norm_nonneg _) fun x => ?_
    rw [Fintype.prod_empty, mul_one, constOfIsEmpty_apply]
  · simpa using (constOfIsEmpty 𝕜 E x).le_opNorm 0

@[simp]
/-
**ContinuousMultilinearMap.nnnorm_constOfIsEmpty** 是 Mathlib 中的一个定理，位于命名空间 `Cont
inuousMultilinearMap`。
形式化陈述：nnnorm_constOfIsEmpty [IsEmpty ι] (x : G) : ‖constOfIsEmpty 𝕜 E x‖₊ = ‖x‖₊
参数：x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `ContinuousMultilinearMap.norm_constOfIsEmpty`：norm_constOfIsEmpty [IsEmp
ty ι] (x : G) : ‖constOfIsEmpty 𝕜 E x‖ = ‖x‖
-/
theorem nnnorm_constOfIsEmpty [IsEmpty ι] (x : G) : ‖constOfIsEmpty 𝕜 E x‖₊ = ‖x‖₊ :=
  NNReal.eq <| norm_constOfIsEmpty _ _ _

end

section

variable (𝕜 E E' G G')

/-- `ContinuousMultilinearMap.prod` as a `LinearIsometryEquiv`. -/
@[simps]
/-
**ContinuousMultilinearMap.prodL** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMultilinea
rMap`。
形式化陈述：prodL : ContinuousMultilinearMap 𝕜 E G × ContinuousMultilinearMap 𝕜 E G' ≃
ₗᵢ[𝕜] ContinuousMultilinearMap 𝕜 E (G × G') where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousMultilinearMap.prod` as a `LinearIsometryEquiv`.
-/
def prodL :
    ContinuousMultilinearMap 𝕜 E G × ContinuousMultilinearMap 𝕜 E G' ≃ₗᵢ[𝕜]
      ContinuousMultilinearMap 𝕜 E (G × G') where
  __ := prodEquiv
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' f := opNorm_prod f.1 f.2

/-- `ContinuousMultilinearMap.pi` as a `LinearIsometryEquiv`. -/
@[simps! apply symm_apply]
/-
**ContinuousMultilinearMap.pi** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMultilinearMa
p`。
形式化陈述：pi {ι' : Type*} {M' : ι' -> Type*} [forall i, AddCommMonoid (M' i)] [foral
l i, TopologicalSpace (M' i)] [forall i, Module R (M' i)] (f : forall i, Continu
ousMultilinearMap R M₁ (M' i)) : ContinuousMultilinearMap R M₁ (forall i, M' i) 
where cont
参数：M' i；M' i；M' i；f : forall i, ContinuousMultilinearMap R M₁ (M' i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousMultilinearMap.pi` as a `LinearIsometryEquiv`.
-/
def piₗᵢ {ι' : Type v'} [Fintype ι'] {E' : ι' → Type wE'} [∀ i', NormedAddCommGroup (E' i')]
    [∀ i', NormedSpace 𝕜 (E' i')] :
    (Π i', ContinuousMultilinearMap 𝕜 E (E' i'))
      ≃ₗᵢ[𝕜] (ContinuousMultilinearMap 𝕜 E (Π i, E' i)) where
  toLinearEquiv := piLinearEquiv
  norm_map' := opNorm_pi

end

end

section RestrictScalars

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜' 𝕜]
variable [NormedSpace 𝕜' G] [IsScalarTower 𝕜' 𝕜 G]
variable [∀ i, NormedSpace 𝕜' (E i)] [∀ i, IsScalarTower 𝕜' 𝕜 (E i)]

@[simp]
/-
**ContinuousMultilinearMap.norm_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `Conti
nuousMultilinearMap`。
形式化陈述：norm_restrictScalars (f : ContinuousMultilinearMap 𝕜 E G) : ‖f.restrictSca
lars 𝕜'‖ = ‖f‖
参数：f : ContinuousMultilinearMap 𝕜 E G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem norm_restrictScalars (f : ContinuousMultilinearMap 𝕜 E G) :
    ‖f.restrictScalars 𝕜'‖ = ‖f‖ :=
  rfl

variable (𝕜')

/-- `ContinuousMultilinearMap.restrictScalars` as a `LinearIsometry`. -/
/-
**ContinuousMultilinearMap.restrictScalars** 是 Mathlib 中的一个定义，位于命名空间 `Continuous
MultilinearMap`。
形式化陈述：restrictScalars (f : ContinuousMultilinearMap A M₁ M₂) : ContinuousMultili
nearMap R M₁ M₂ where toMultilinearMap
参数：f : ContinuousMultilinearMap A M₁ M₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.cont`：∀ {R : Type u} {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoid (M₁
 i)] [inst_2 : AddC…

--- 原说明 ---
`ContinuousMultilinearMap.restrictScalars` as a `LinearIsometry`.
-/
def restrictScalarsₗᵢ : ContinuousMultilinearMap 𝕜 E G →ₗᵢ[𝕜'] ContinuousMultilinearMap 𝕜' E G where
  toFun := restrictScalars 𝕜'
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

end RestrictScalars

/-- The difference `f m₁ - f m₂` is controlled in terms of `‖f‖` and `‖m₁ - m₂‖`, precise version.
For a less precise but more usable version, see `norm_image_sub_le`. The bound reads
`‖f m - f m'‖ ≤
  ‖f‖ * ‖m 1 - m' 1‖ * max ‖m 2‖ ‖m' 2‖ * max ‖m 3‖ ‖m' 3‖ * ... * max ‖m n‖ ‖m' n‖ + ...`,
where the other terms in the sum are the same products where `1` is replaced by any `i`. -/
/-
**ContinuousMultilinearMap.norm_image_sub_le'** 是 Mathlib 中的一个定理，位于命名空间 `Continu
ousMultilinearMap`。
形式化陈述：norm_image_sub_le' [DecidableEq ι] (f : ContinuousMultilinearMap 𝕜 E G) (m
₁ m₂ : forall i, E i) : ‖f m₁ - f m₂‖ <= ‖f‖ * ∑ i, ∏ j, if j = i then ‖m₁ i - m
₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖
参数：f : ContinuousMultilinearMap 𝕜 E G；m₁ m₂ : forall i, E i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.norm_image_sub_le_of_bound'`：norm_image_sub_le_of_bound' 
[DecidableEq ι] (f : MultilinearMap 𝕜 E G) {C : Real} (hC : 0 <= C) (H : forall 
m, ‖f m‖ <= C * ∏ i, ‖m i‖) (m₁ …
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `ContinuousMultilinearMap.le_opNorm`：le_opNorm (f : ContinuousMultilinear
Map 𝕜 E G) (m : forall i, E i) : ‖f m‖ <= ‖f‖ * ∏ i, ‖m i‖

--- 原说明 ---
The difference `f m₁ - f m₂` is controlled in terms of `‖f‖` and `‖m₁ - m₂‖`, pr
ecise version.
For a less precise but more usable version, see `norm_image_sub_le`. The bound r
eads
`‖f m - f m'‖ ≤
  ‖f‖ * ‖m 1 - m' 1‖ * max ‖m 2‖ ‖m' 2‖ * max ‖m 3‖ ‖m' 3‖ * ... * max ‖m n‖ ‖m'
 n‖ + ...`,
where the other terms in the sum are the same products where `1` is replaced by 
any `i`.
-/
theorem norm_image_sub_le' [DecidableEq ι] (f : ContinuousMultilinearMap 𝕜 E G) (m₁ m₂ : ∀ i, E i) :
    ‖f m₁ - f m₂‖ ≤ ‖f‖ * ∑ i, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ :=
  f.toMultilinearMap.norm_image_sub_le_of_bound' (norm_nonneg _) f.le_opNorm _ _

/-- The difference `f m₁ - f m₂` is controlled in terms of `‖f‖` and `‖m₁ - m₂‖`, less precise
version. For a more precise but less usable version, see `norm_image_sub_le'`.
The bound is `‖f m - f m'‖ ≤ ‖f‖ * card ι * ‖m - m'‖ * (max ‖m‖ ‖m'‖) ^ (card ι - 1)`. -/
/-
**ContinuousMultilinearMap.norm_image_sub_le** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usMultilinearMap`。
形式化陈述：norm_image_sub_le (f : ContinuousMultilinearMap 𝕜 E G) (m₁ m₂ : forall i, 
E i) : ‖f m₁ - f m₂‖ <= ‖f‖ * Fintype.card ι * max ‖m₁‖ ‖m₂‖ ^ (Fintype.card ι -
 1) * ‖m₁ - m₂‖
参数：f : ContinuousMultilinearMap 𝕜 E G；m₁ m₂ : forall i, E i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.norm_image_sub_le_of_bound`：norm_image_sub_le_of_bound (f
 : MultilinearMap 𝕜 E G) {C : Real} (hC : 0 <= C) (H : forall m, ‖f m‖ <= C * ∏ 
i, ‖m i‖) (m₁ m₂ : forall i, E …
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `ContinuousMultilinearMap.le_opNorm`：le_opNorm (f : ContinuousMultilinear
Map 𝕜 E G) (m : forall i, E i) : ‖f m‖ <= ‖f‖ * ∏ i, ‖m i‖

--- 原说明 ---
The difference `f m₁ - f m₂` is controlled in terms of `‖f‖` and `‖m₁ - m₂‖`, le
ss precise
version. For a more precise but less usable version, see `norm_image_sub_le'`.
The bound is `‖f m - f m'‖ ≤ ‖f‖ * card ι * ‖m - m'‖ * (max ‖m‖ ‖m'‖) ^ (card ι 
- 1)`.
-/
theorem norm_image_sub_le (f : ContinuousMultilinearMap 𝕜 E G) (m₁ m₂ : ∀ i, E i) :
    ‖f m₁ - f m₂‖ ≤ ‖f‖ * Fintype.card ι * max ‖m₁‖ ‖m₂‖ ^ (Fintype.card ι - 1) * ‖m₁ - m₂‖ :=
  f.toMultilinearMap.norm_image_sub_le_of_bound (norm_nonneg _) f.le_opNorm _ _

end ContinuousMultilinearMap

variable [Fintype ι]

/-- If a continuous multilinear map is constructed from a multilinear map via the constructor
`mkContinuous`, then its norm is bounded by the bound given to the constructor if it is
nonnegative. -/
/-
**MultilinearMap.mkContinuous_norm_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MultilinearMap.mkContinuous_norm_le (f : MultilinearMap 𝕜 E G) {C : Real} 
(hC : 0 <= C) (H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖) : ‖f.mkContinuous C H‖ <= 
C
参数：f : MultilinearMap 𝕜 E G；hC : 0 <= C；H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.opNorm_le_bound`：opNorm_le_bound {f : Continuou
sMultilinearMap 𝕜 E G} {M : Real} (hMp : 0 <= M) (hM : forall m, ‖f m‖ <= M * ∏ 
i, ‖m i‖) : ‖f‖ <= M

--- 原说明 ---
If a continuous multilinear map is constructed from a multilinear map via the co
nstructor
`mkContinuous`, then its norm is bounded by the bound given to the constructor i
f it is
nonnegative.
-/
theorem MultilinearMap.mkContinuous_norm_le (f : MultilinearMap 𝕜 E G) {C : ℝ} (hC : 0 ≤ C)
    (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) : ‖f.mkContinuous C H‖ ≤ C :=
  ContinuousMultilinearMap.opNorm_le_bound hC fun m => H m

/-- If a continuous multilinear map is constructed from a multilinear map via the constructor
`mkContinuous`, then its norm is bounded by the bound given to the constructor if it is
nonnegative. -/
/-
**MultilinearMap.mkContinuous_norm_le'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MultilinearMap.mkContinuous_norm_le' (f : MultilinearMap 𝕜 E G) {C : Real}
 (H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖) : ‖f.mkContinuous C H‖ <= max C 0
参数：f : MultilinearMap 𝕜 E G；H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.opNorm_le_bound`：opNorm_le_bound {f : Continuou
sMultilinearMap 𝕜 E G} {M : Real} (hMp : 0 <= M) (hM : forall m, ‖f m‖ <= M * ∏ 
i, ‖m i‖) : ‖f‖ <= M
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用引理 `Finset.prod_nonneg`：prod_nonneg (h0 : forall i in s, 0 <= f i) : 0 <= ∏ 
i in s, f i
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖

--- 原说明 ---
If a continuous multilinear map is constructed from a multilinear map via the co
nstructor
`mkContinuous`, then its norm is bounded by the bound given to the constructor i
f it is
nonnegative.
-/
theorem MultilinearMap.mkContinuous_norm_le' (f : MultilinearMap 𝕜 E G) {C : ℝ}
    (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) : ‖f.mkContinuous C H‖ ≤ max C 0 :=
  ContinuousMultilinearMap.opNorm_le_bound (le_max_right _ _) fun m ↦ (H m).trans <|
    mul_le_mul_of_nonneg_right (le_max_left _ _) <| by positivity

namespace ContinuousMultilinearMap

/-- Given a continuous multilinear map `f` on `n` variables (parameterized by `Fin n`) and a subset
`s` of `k` of these variables, one gets a new continuous multilinear map on `Fin k` by varying
these variables, and fixing the other ones equal to a given value `z`. It is denoted by
`f.restr s hk z`, where `hk` is a proof that the cardinality of `s` is `k`. The implicit
identification between `Fin k` and `s` that we use is the canonical (increasing) bijection. -/
/-
**ContinuousMultilinearMap.restr** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMultilinea
rMap`。
形式化陈述：restr {k n : Nat} (f : (G [×n]->L[𝕜] G' :)) (s : Finset (Fin n)) (hk : #s 
= k) (z : G) : G [×k]->L[𝕜] G'
参数：f : (G [×n]->L[𝕜] G' :)；s : Finset (Fin n)；hk : #s = k；z : G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a continuous multilinear map `f` on `n` variables (parameterized by `Fin n
`) and a subset
`s` of `k` of these variables, one gets a new continuous multilinear map on `Fin
 k` by varying
these variables, and fixing the other ones equal to a given value `z`. It is den
oted by
`f.restr s hk z`, where `hk` is a proof that the cardinality of `s` is `k`. The 
implicit
identification between `Fin k` and `s` that we use is the canonical (increasing)
 bijection.
-/
def restr {k n : ℕ} (f : (G [×n]→L[𝕜] G' :)) (s : Finset (Fin n)) (hk : #s = k) (z : G) :
    G [×k]→L[𝕜] G' :=
  (f.toMultilinearMap.restr s hk z).mkContinuous (‖f‖ * ‖z‖ ^ (n - k)) fun _ =>
    MultilinearMap.restr_norm_le _ _ _ _ f.le_opNorm _
/-
**ContinuousMultilinearMap.norm_restr** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMulti
linearMap`。
形式化陈述：norm_restr {k n : Nat} (f : G [×n]->L[𝕜] G') (s : Finset (Fin n)) (hk : #s
 = k) (z : G) : ‖f.restr s hk z‖ <= ‖f‖ * ‖z‖ ^ (n - k)
参数：f : G [×n]->L[𝕜] G'；s : Finset (Fin n)；hk : #s = k；z : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.mkContinuous_norm_le`：MultilinearMap.mkContinuous_norm_le
 (f : MultilinearMap 𝕜 E G) {C : Real} (hC : 0 <= C) (H : forall m, ‖f m‖ <= C *
 ∏ i, ‖m i‖) : ‖f.mkConti…
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
-/
theorem norm_restr {k n : ℕ} (f : G [×n]→L[𝕜] G') (s : Finset (Fin n)) (hk : #s = k) (z : G) :
    ‖f.restr s hk z‖ ≤ ‖f‖ * ‖z‖ ^ (n - k) := by
  apply MultilinearMap.mkContinuous_norm_le
  exact mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)

section

variable {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]

@[simp]
/-
**ContinuousMultilinearMap.norm_mkPiAlgebra_le** 是 Mathlib 中的一个定理，位于命名空间 `Contin
uousMultilinearMap`。
形式化陈述：norm_mkPiAlgebra_le [Nonempty ι] : ‖ContinuousMultilinearMap.mkPiAlgebra 𝕜
 ι A‖ <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.opNorm_le_bound`：opNorm_le_bound {f : Continuou
sMultilinearMap 𝕜 E G} {M : Real} (hMp : 0 <= M) (hM : forall m, ‖f m‖ <= M * ∏ 
i, ‖m i‖) : ‖f‖ <= M
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Finset.norm_prod_le'`：Finset.norm_prod_le' {α : Type*} [NormedCommRing α
] (s : Finset ι) (hs : s.Nonempty) (f : ι -> α) : ‖∏ i in s, f i‖ <= ∏ i in s, ‖
f i‖
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty
-/
theorem norm_mkPiAlgebra_le [Nonempty ι] : ‖ContinuousMultilinearMap.mkPiAlgebra 𝕜 ι A‖ ≤ 1 := by
  refine opNorm_le_bound zero_le_one fun m => ?_
  simp only [ContinuousMultilinearMap.mkPiAlgebra_apply, one_mul]
  exact norm_prod_le' _ univ_nonempty _
/-
**ContinuousMultilinearMap.norm_mkPiAlgebra_of_empty** 是 Mathlib 中的一个定理，位于命名空间 `
ContinuousMultilinearMap`。
形式化陈述：norm_mkPiAlgebra_of_empty [IsEmpty ι] : ‖ContinuousMultilinearMap.mkPiAlge
bra 𝕜 ι A‖ = ‖(1 : A)‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `ContinuousMultilinearMap.opNorm_le_bound`：opNorm_le_bound {f : Continuou
sMultilinearMap 𝕜 E G} {M : Real} (hMp : 0 <= M) (hM : forall m, ‖f m‖ <= M * ∏ 
i, ‖m i‖) : ‖f‖ <= M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContinuousMultilinearMap.ratio_le_opNorm`：ratio_le_opNorm (f : Continuou
sMultilinearMap 𝕜 E G) (m : forall i, E i) : (‖f m‖ / ∏ i, ‖m i‖) <= ‖f‖
-/
theorem norm_mkPiAlgebra_of_empty [IsEmpty ι] :
    ‖ContinuousMultilinearMap.mkPiAlgebra 𝕜 ι A‖ = ‖(1 : A)‖ := by
  apply le_antisymm
  · apply opNorm_le_bound <;> simp
  · convert! ratio_le_opNorm (ContinuousMultilinearMap.mkPiAlgebra 𝕜 ι A) fun _ => 1
    simp

@[simp]
/-
**ContinuousMultilinearMap.norm_mkPiAlgebra** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sMultilinearMap`。
形式化陈述：norm_mkPiAlgebra [NormOneClass A] : ‖ContinuousMultilinearMap.mkPiAlgebra 
𝕜 ι A‖ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMultilinearMap.norm_mkPiAlgebra_of_empty`：norm_mkPiAlgebra_of_
empty [IsEmpty ι] : ‖ContinuousMultilinearMap.mkPiAlgebra 𝕜 ι A‖ = ‖(1 : A)‖
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `ContinuousMultilinearMap.norm_mkPiAlgebra_le`：norm_mkPiAlgebra_le [Nonem
pty ι] : ‖ContinuousMultilinearMap.mkPiAlgebra 𝕜 ι A‖ <= 1
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ContinuousMultilinearMap.ratio_le_opNorm`：ratio_le_opNorm (f : Continuou
sMultilinearMap 𝕜 E G) (m : forall i, E i) : (‖f m‖ / ∏ i, ‖m i‖) <= ‖f‖
-/
theorem norm_mkPiAlgebra [NormOneClass A] : ‖ContinuousMultilinearMap.mkPiAlgebra 𝕜 ι A‖ = 1 := by
  cases isEmpty_or_nonempty ι
  · simp [norm_mkPiAlgebra_of_empty]
  · refine le_antisymm norm_mkPiAlgebra_le ?_
    convert! ratio_le_opNorm (ContinuousMultilinearMap.mkPiAlgebra 𝕜 ι A) fun _ => 1
    simp

end

section

variable {n : ℕ} {A : Type*} [SeminormedRing A] [NormedAlgebra 𝕜 A]

/-
**ContinuousMultilinearMap.norm_mkPiAlgebraFin_succ_le** 是 Mathlib 中的一个定理，位于命名空间
 `ContinuousMultilinearMap`。
形式化陈述：norm_mkPiAlgebraFin_succ_le : ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n
.succ A‖ <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.opNorm_le_bound`：opNorm_le_bound {f : Continuou
sMultilinearMap 𝕜 E G} {M : Real} (hMp : 0 <= M) (hM : forall m, ‖f m‖ <= M * ∏ 
i, ‖m i‖) : ‖f‖ <= M
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.ofFn_eq_map`：ofFn_eq_map {n} {f : Fin n -> α} : ofFn f = (finRange 
n).map f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fin.prod_univ_def`：prod_univ_def (f : Fin n -> M) : ∏ i, f i = ((List.fi
nRange n).map f).prod
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `List.norm_prod_le'`：List.norm_prod_le' : forall {l : List α}, l != [] ->
 ‖l.prod‖ <= (l.map norm).prod | [], h => (h rfl).elim | [a], _ => by simp | a::
b::l, _ …
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `List.map_eq_nil_iff`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : Li
st α}, List.map f l = [] ↔ l = []
· 使用定理 `List.finRange_eq_nil_iff`：∀ {n : ℕ}, List.finRange n = [] ↔ n = 0
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
-/
theorem norm_mkPiAlgebraFin_succ_le : ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n.succ A‖ ≤ 1 := by
  refine opNorm_le_bound zero_le_one fun m => ?_
  simp only [ContinuousMultilinearMap.mkPiAlgebraFin_apply, one_mul, List.ofFn_eq_map,
    Fin.prod_univ_def]
  refine (List.norm_prod_le' ?_).trans_eq ?_
  · rw [Ne, List.map_eq_nil_iff, List.finRange_eq_nil_iff]
    exact Nat.succ_ne_zero _
  rw [List.map_map, Function.comp_def]
/-
**ContinuousMultilinearMap.norm_mkPiAlgebraFin_le_of_pos** 是 Mathlib 中的一个定理，位于命名
空间 `ContinuousMultilinearMap`。
形式化陈述：norm_mkPiAlgebraFin_le_of_pos (hn : 0 < n) : ‖ContinuousMultilinearMap.mkP
iAlgebraFin 𝕜 n A‖ <= 1
参数：hn : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Nat.exists_eq_succ_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k.succ
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `ContinuousMultilinearMap.norm_mkPiAlgebraFin_succ_le`：norm_mkPiAlgebraFi
n_succ_le : ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n.succ A‖ <= 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem norm_mkPiAlgebraFin_le_of_pos (hn : 0 < n) :
    ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n A‖ ≤ 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact norm_mkPiAlgebraFin_succ_le
/-
**ContinuousMultilinearMap.norm_mkPiAlgebraFin_zero** 是 Mathlib 中的一个定理，位于命名空间 `C
ontinuousMultilinearMap`。
形式化陈述：norm_mkPiAlgebraFin_zero : ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 0 A‖
 = ‖(1 : A)‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `ContinuousMultilinearMap.opNorm_le_bound`：opNorm_le_bound {f : Continuou
sMultilinearMap 𝕜 E G} {M : Real} (hMp : 0 <= M) (hM : forall m, ‖f m‖ <= M * ∏ 
i, ‖m i‖) : ‖f‖ <= M
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.ofFn_zero`：∀ {α : Type u_1} {f : Fin 0 → α}, List.ofFn f = []
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContinuousMultilinearMap.ratio_le_opNorm`：ratio_le_opNorm (f : Continuou
sMultilinearMap 𝕜 E G) (m : forall i, E i) : (‖f m‖ / ∏ i, ‖m i‖) <= ‖f‖
-/
theorem norm_mkPiAlgebraFin_zero : ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 0 A‖ = ‖(1 : A)‖ := by
  refine le_antisymm ?_ ?_
  · refine opNorm_le_bound (norm_nonneg (1 : A)) ?_
    simp
  · convert! ratio_le_opNorm (ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 0 A) fun _ => (1 : A)
    simp
/-
**ContinuousMultilinearMap.norm_mkPiAlgebraFin_le** 是 Mathlib 中的一个定理，位于命名空间 `Con
tinuousMultilinearMap`。
形式化陈述：norm_mkPiAlgebraFin_le : ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n A‖ <
= max 1 ‖(1 : A)‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `ContinuousMultilinearMap.norm_mkPiAlgebraFin_zero`：norm_mkPiAlgebraFin_z
ero : ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 0 A‖ = ‖(1 : A)‖
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousMultilinearMap.norm_mkPiAlgebraFin_le_of_pos`：norm_mkPiAlgebra
Fin_le_of_pos (hn : 0 < n) : ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n A‖ <= 
1
· 使用定理 `Nat.zero_lt_succ`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
-/
theorem norm_mkPiAlgebraFin_le :
    ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n A‖ ≤ max 1 ‖(1 : A)‖ := by
  cases n
  · exact norm_mkPiAlgebraFin_zero.le.trans (le_max_right _ _)
  · exact (norm_mkPiAlgebraFin_le_of_pos (Nat.zero_lt_succ _)).trans (le_max_left _ _)

@[simp]
/-
**ContinuousMultilinearMap.norm_mkPiAlgebraFin** 是 Mathlib 中的一个定理，位于命名空间 `Contin
uousMultilinearMap`。
形式化陈述：norm_mkPiAlgebraFin [NormOneClass A] : ‖ContinuousMultilinearMap.mkPiAlgeb
raFin 𝕜 n A‖ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMultilinearMap.norm_mkPiAlgebraFin_zero`：norm_mkPiAlgebraFin_z
ero : ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 0 A‖ = ‖(1 : A)‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `ContinuousMultilinearMap.norm_mkPiAlgebraFin_succ_le`：norm_mkPiAlgebraFi
n_succ_le : ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n.succ A‖ <= 1
· 使用定理 `le_of_eq_of_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ 
c → a ≤ c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.ofFn_succ`：∀ {α : Type u_1} {n : ℕ} {f : Fin (n + 1) → α}, List.ofF
n f = f 0 :: List.ofFn fun i => f i.succ
· 使用定理 `List.ofFn_const`：∀ {α : Type u} (n : ℕ) (c : α), (List.ofFn fun x => c) 
= List.replicate n c
· 使用定理 `List.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n a).
prod = a ^ n
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ContinuousMultilinearMap.ratio_le_opNorm`：ratio_le_opNorm (f : Continuou
sMultilinearMap 𝕜 E G) (m : forall i, E i) : (‖f m‖ / ∏ i, ‖m i‖) <= ‖f‖
-/
theorem norm_mkPiAlgebraFin [NormOneClass A] :
    ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n A‖ = 1 := by
  cases n
  · rw [norm_mkPiAlgebraFin_zero]
    simp
  · refine le_antisymm norm_mkPiAlgebraFin_succ_le ?_
    refine le_of_eq_of_le ?_ <|
      ratio_le_opNorm (ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 (Nat.succ _) A) fun _ => 1
    simp

end

@[simp]
/-
**ContinuousMultilinearMap.nnnorm_smulRight** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sMultilinearMap`。
形式化陈述：nnnorm_smulRight (f : ContinuousMultilinearMap 𝕜 E 𝕜) (z : G) : ‖f.smulRig
ht z‖₊ = ‖f‖₊ * ‖z‖₊
参数：f : ContinuousMultilinearMap 𝕜 E 𝕜；z : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ContinuousMultilinearMap.opNNNorm_le_iff`：opNNNorm_le_iff {f : Continuou
sMultilinearMap 𝕜 E G} {C : Real>=0} : ‖f‖₊ <= C ↔ forall m, ‖f m‖₊ <= C * ∏ i, 
‖m i‖₊
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `nnnorm_smul_le`：nnnorm_smul_le (r : α) (x : β) : ‖r • x‖₊ <= ‖r‖₊ * ‖x‖₊
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `ContinuousMultilinearMap.le_opNNNorm`：le_opNNNorm (f : ContinuousMultili
nearMap 𝕜 E G) (m : forall i, E i) : ‖f m‖₊ <= ‖f‖₊ * ∏ i, ‖m i‖₊
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_div_iff₀`：le_div_iff₀ (hc : 0 < c) : a <= b / c ↔ a * c <= b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `div_mul_eq_mul_div`：div_mul_eq_mul_div : a / b * c = a * c / b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `ContinuousMultilinearMap.smulRight_apply`：∀ {R : Type u} {ι : Type v} {M
₁ : ι → Type w₁} {M₂ : Type w₂} [inst : CommSemiring R]   [inst_1 : (i : ι) → Ad
dCommMonoid (M₁ i)] [inst_2 : …
· 使用定理 `nnnorm_smul`：nnnorm_smul (r : α) (x : β) : ‖r • x‖₊ = ‖r‖₊ * ‖x‖₊
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
-/
theorem nnnorm_smulRight (f : ContinuousMultilinearMap 𝕜 E 𝕜) (z : G) :
    ‖f.smulRight z‖₊ = ‖f‖₊ * ‖z‖₊ := by
  refine le_antisymm ?_ ?_
  · refine opNNNorm_le_iff.2 fun m => (nnnorm_smul_le _ _).trans ?_
    rw [mul_right_comm]
    gcongr
    exact le_opNNNorm _ _
  · obtain hz | hz := eq_zero_or_pos ‖z‖₊
    · simp [hz]
    rw [← le_div_iff₀ hz, opNNNorm_le_iff]
    intro m
    rw [div_mul_eq_mul_div, le_div_iff₀ hz]
    refine le_trans ?_ ((f.smulRight z).le_opNNNorm m)
    rw [smulRight_apply, nnnorm_smul]

@[simp]
/-
**ContinuousMultilinearMap.norm_smulRight** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousM
ultilinearMap`。
形式化陈述：norm_smulRight (f : ContinuousMultilinearMap 𝕜 E 𝕜) (z : G) : ‖f.smulRight
 z‖ = ‖f‖ * ‖z‖
参数：f : ContinuousMultilinearMap 𝕜 E 𝕜；z : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContinuousMultilinearMap.nnnorm_smulRight`：nnnorm_smulRight (f : Continu
ousMultilinearMap 𝕜 E 𝕜) (z : G) : ‖f.smulRight z‖₊ = ‖f‖₊ * ‖z‖₊
-/
theorem norm_smulRight (f : ContinuousMultilinearMap 𝕜 E 𝕜) (z : G) :
    ‖f.smulRight z‖ = ‖f‖ * ‖z‖ :=
  congr_arg NNReal.toReal (nnnorm_smulRight f z)

@[simp]
/-
**ContinuousMultilinearMap.norm_mkPiRing** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMu
ltilinearMap`。
形式化陈述：norm_mkPiRing (z : G) : ‖ContinuousMultilinearMap.mkPiRing 𝕜 ι z‖ = ‖z‖
参数：z : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMultilinearMap.mkPiRing.eq_1`：∀ (R : Type u) (ι : Type v) {M :
 Type u_1} [inst : Fintype ι] [inst_1 : CommRing R] [inst_2 : AddCommMonoid M]  
 [inst_3 : _root_.Module R M…
· 使用定理 `ContinuousMultilinearMap.norm_smulRight`：norm_smulRight (f : ContinuousM
ultilinearMap 𝕜 E 𝕜) (z : G) : ‖f.smulRight z‖ = ‖f‖ * ‖z‖
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `ContinuousMultilinearMap.norm_mkPiAlgebra`：norm_mkPiAlgebra [NormOneClas
s A] : ‖ContinuousMultilinearMap.mkPiAlgebra 𝕜 ι A‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem norm_mkPiRing (z : G) : ‖ContinuousMultilinearMap.mkPiRing 𝕜 ι z‖ = ‖z‖ := by
  rw [ContinuousMultilinearMap.mkPiRing, norm_smulRight, norm_mkPiAlgebra, one_mul]

variable (𝕜 E G) in
/-- Continuous bilinear map realizing `(f, z) ↦ f.smulRight z`. -/
/-
**ContinuousMultilinearMap.smulRightL** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMulti
linearMap`。
形式化陈述：smulRightL : ContinuousMultilinearMap 𝕜 E 𝕜 ->L[𝕜] G ->L[𝕜] ContinuousMult
ilinearMap 𝕜 E G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Continuous bilinear map realizing `(f, z) ↦ f.smulRight z`.
-/
def smulRightL : ContinuousMultilinearMap 𝕜 E 𝕜 →L[𝕜] G →L[𝕜] ContinuousMultilinearMap 𝕜 E G :=
  LinearMap.mkContinuous₂
    { toFun := fun f ↦
        { toFun := fun z ↦ f.smulRight z
          map_add' := fun x y ↦ by ext; simp
          map_smul' := fun c x ↦ by ext; simp [smul_smul, mul_comm] }
      map_add' := fun f g ↦ by ext; simp [add_smul]
      map_smul' := fun c f ↦ by ext; simp [smul_smul] }
    1 (fun f z ↦ by simp [norm_smulRight])
/-
**ContinuousMultilinearMap.smulRightL_apply** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sMultilinearMap`。
形式化陈述：∀ {𝕜 : Type u} {ι : Type v} {E : ι → Type wE} {G : Type wG} [inst : Nontri
viallyNormedField 𝕜]   [inst_1 : (i : ι) → SeminormedAddCommGroup (E i)] [inst_2
 : (i : ι) → NormedSpace 𝕜 (E i)]   [inst_3 : SeminormedAddCommGroup G] [inst_4 
: NormedSpace 𝕜 G] [inst_5 : Fintype ι]   (f : ContinuousMultilinearMap 𝕜 E 𝕜) (
z : G), ((ContinuousMultilinearMap.smulRightL 𝕜 E G) f) z = f.smulRight z
参数：i : ι；E i；i : ι；E i；f : ContinuousMultilinearMap 𝕜 E 𝕜；z : G；(ContinuousMulti
linearMap.smulRightL 𝕜 E G) f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
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
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `ContinuousMultilinearMap.instSMulCommClass`：∀ {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCommMo
noid M₂]   [inst_2 : (i : ι) → T…
-/
@[simp] lemma smulRightL_apply (f : ContinuousMultilinearMap 𝕜 E 𝕜) (z : G) :
    smulRightL 𝕜 E G f z = f.smulRight z := rfl
/-
**ContinuousMultilinearMap.norm_smulRightL_le** 是 Mathlib 中的一个引理，位于命名空间 `Continu
ousMultilinearMap`。
形式化陈述：norm_smulRightL_le : ‖smulRightL 𝕜 E G‖ <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.mkContinuous₂_norm_le`：mkContinuous₂_norm_le (f : E ->ₛₗ[σ₁₃] 
F ->ₛₗ[σ₂₃] G) {C : Real} (h0 : 0 <= C) (hC : forall x y, ‖f x y‖ <= C * ‖x‖ * ‖
y‖) : ‖f.mkContinuous…
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
-/
lemma norm_smulRightL_le : ‖smulRightL 𝕜 E G‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

variable (𝕜 ι G)

/-- Continuous multilinear maps on `𝕜^n` with values in `G` are in bijection with `G`, as such a
continuous multilinear map is completely determined by its value on the constant vector made of
ones. We register this bijection as a linear isometry in
`ContinuousMultilinearMap.piFieldEquiv`. -/
/-
**ContinuousMultilinearMap.piFieldEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMul
tilinearMap`。
形式化陈述：(𝕜 : Type u) →   (ι : Type v) →     (G : Type wG) →       [inst : Nontrivi
allyNormedField 𝕜] →         [inst_1 : SeminormedAddCommGroup G] →           [in
st_2 : NormedSpace 𝕜 G] → [inst_3 : Fintype ι] → G ≃ₗᵢ[𝕜] ContinuousMultilinearM
ap 𝕜 (fun x => 𝕜) G
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.norm_mkPiRing`：norm_mkPiRing (z : G) : ‖Continu
ousMultilinearMap.mkPiRing 𝕜 ι z‖ = ‖z‖

--- 原说明 ---
Continuous multilinear maps on `𝕜^n` with values in `G` are in bijection with `G
`, as such a
continuous multilinear map is completely determined by its value on the constant
 vector made of
ones. We register this bijection as a linear isometry in
`ContinuousMultilinearMap.piFieldEquiv`.
-/
protected def piFieldEquiv : G ≃ₗᵢ[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι => 𝕜) G where
  toFun z := ContinuousMultilinearMap.mkPiRing 𝕜 ι z
  invFun f := f fun _ => 1
  map_add' z z' := by
    ext
    simp [smul_add]
  map_smul' c z := by
    ext
    simp [smul_smul, mul_comm]
  left_inv z := by simp
  right_inv f := f.mkPiRing_apply_one_eq_self
  norm_map' := norm_mkPiRing

end ContinuousMultilinearMap

open ContinuousMultilinearMap

namespace MultilinearMap

/-- Given a map `f : G →ₗ[𝕜] MultilinearMap 𝕜 E G'` and an estimate
`H : ∀ x m, ‖f x m‖ ≤ C * ‖x‖ * ∏ i, ‖m i‖`, construct a continuous linear
map from `G` to `ContinuousMultilinearMap 𝕜 E G'`.

In order to lift, e.g., a map `f : (MultilinearMap 𝕜 E G) →ₗ[𝕜] MultilinearMap 𝕜 E' G'`
to a map `(ContinuousMultilinearMap 𝕜 E G) →L[𝕜] ContinuousMultilinearMap 𝕜 E' G'`,
one can apply this construction to `f.comp ContinuousMultilinearMap.toMultilinearMapLinear`
which is a linear map from `ContinuousMultilinearMap 𝕜 E G` to `MultilinearMap 𝕜 E' G'`. -/
/-
**MultilinearMap.mkContinuousLinear** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearMap`。
形式化陈述：mkContinuousLinear (f : G ->ₗ[𝕜] MultilinearMap 𝕜 E G') (C : Real) (H : fo
rall x m, ‖f x m‖ <= C * ‖x‖ * ∏ i, ‖m i‖) : G ->L[𝕜] ContinuousMultilinearMap 𝕜
 E G'
参数：f : G ->ₗ[𝕜] MultilinearMap 𝕜 E G'；C : Real；H : forall x m, ‖f x m‖ <= C * ‖x
‖ * ∏ i, ‖m i‖。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a map `f : G →ₗ[𝕜] MultilinearMap 𝕜 E G'` and an estimate
`H : ∀ x m, ‖f x m‖ ≤ C * ‖x‖ * ∏ i, ‖m i‖`, construct a continuous linear
map from `G` to `ContinuousMultilinearMap 𝕜 E G'`.

In order to lift, e.g., a map `f : (MultilinearMap 𝕜 E G) →ₗ[𝕜] MultilinearMap 𝕜
 E' G'`
to a map `(ContinuousMultilinearMap 𝕜 E G) →L[𝕜] ContinuousMultilinearMap 𝕜 E' G
'`,
one can apply this construction to `f.comp ContinuousMultilinearMap.toMultilinea
rMapLinear`
which is a linear map from `ContinuousMultilinearMap 𝕜 E G` to `MultilinearMap 𝕜
 E' G'`.
-/
def mkContinuousLinear (f : G →ₗ[𝕜] MultilinearMap 𝕜 E G') (C : ℝ)
    (H : ∀ x m, ‖f x m‖ ≤ C * ‖x‖ * ∏ i, ‖m i‖) : G →L[𝕜] ContinuousMultilinearMap 𝕜 E G' :=
  LinearMap.mkContinuous
    { toFun := fun x => (f x).mkContinuous (C * ‖x‖) <| H x
      map_add' := fun x y => by
        ext1
        simp
      map_smul' := fun c x => by
        ext1
        simp }
    (max C 0) fun x => by
      simpa using ((f x).mkContinuous_norm_le' _).trans_eq <| by
        rw [max_mul_of_nonneg _ _ (norm_nonneg x), zero_mul]
/-
**MultilinearMap.mkContinuousLinear_norm_le'** 是 Mathlib 中的一个定理，位于命名空间 `Multilin
earMap`。
形式化陈述：mkContinuousLinear_norm_le' (f : G ->ₗ[𝕜] MultilinearMap 𝕜 E G') (C : Real
) (H : forall x m, ‖f x m‖ <= C * ‖x‖ * ∏ i, ‖m i‖) : ‖mkContinuousLinear f C H‖
 <= max C 0
参数：f : G ->ₗ[𝕜] MultilinearMap 𝕜 E G'；C : Real；H : forall x m, ‖f x m‖ <= C * ‖x
‖ * ∏ i, ‖m i‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `LinearMap.mkContinuous_norm_le`：mkContinuous_norm_le (f : E ->ₛₗ[σ₁₂] F)
 {C : Real} (hC : 0 <= C) (h : forall x, ‖f x‖ <= C * ‖x‖) : ‖f.mkContinuous C h
‖ <= C
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
-/
theorem mkContinuousLinear_norm_le' (f : G →ₗ[𝕜] MultilinearMap 𝕜 E G') (C : ℝ)
    (H : ∀ x m, ‖f x m‖ ≤ C * ‖x‖ * ∏ i, ‖m i‖) : ‖mkContinuousLinear f C H‖ ≤ max C 0 := by
  dsimp only [mkContinuousLinear]
  exact LinearMap.mkContinuous_norm_le _ (le_max_right _ _) _
/-
**MultilinearMap.mkContinuousLinear_norm_le** 是 Mathlib 中的一个定理，位于命名空间 `Multiline
arMap`。
形式化陈述：mkContinuousLinear_norm_le (f : G ->ₗ[𝕜] MultilinearMap 𝕜 E G') {C : Real}
 (hC : 0 <= C) (H : forall x m, ‖f x m‖ <= C * ‖x‖ * ∏ i, ‖m i‖) : ‖mkContinuous
Linear f C H‖ <= C
参数：f : G ->ₗ[𝕜] MultilinearMap 𝕜 E G'；hC : 0 <= C；H : forall x m, ‖f x m‖ <= C *
 ‖x‖ * ∏ i, ‖m i‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MultilinearMap.mkContinuousLinear_norm_le'`：mkContinuousLinear_norm_le' 
(f : G ->ₗ[𝕜] MultilinearMap 𝕜 E G') (C : Real) (H : forall x m, ‖f x m‖ <= C * 
‖x‖ * ∏ i, ‖m i‖) : ‖mkContinuou…
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
-/
theorem mkContinuousLinear_norm_le (f : G →ₗ[𝕜] MultilinearMap 𝕜 E G') {C : ℝ} (hC : 0 ≤ C)
    (H : ∀ x m, ‖f x m‖ ≤ C * ‖x‖ * ∏ i, ‖m i‖) : ‖mkContinuousLinear f C H‖ ≤ C :=
  (mkContinuousLinear_norm_le' f C H).trans_eq (max_eq_left hC)

variable [∀ i, SeminormedAddCommGroup (E' i)] [∀ i, NormedSpace 𝕜 (E' i)]

/-- Given a map `f : MultilinearMap 𝕜 E (MultilinearMap 𝕜 E' G)` and an estimate
`H : ∀ m m', ‖f m m'‖ ≤ C * ∏ i, ‖m i‖ * ∏ i, ‖m' i‖`, upgrade all `MultilinearMap`s in the type to
`ContinuousMultilinearMap`s. -/
/-
**MultilinearMap.mkContinuousMultilinear** 是 Mathlib 中的一个定义，位于命名空间 `MultilinearM
ap`。
形式化陈述：mkContinuousMultilinear (f : MultilinearMap 𝕜 E (MultilinearMap 𝕜 E' G)) (
C : Real) (H : forall m₁ m₂, ‖f m₁ m₂‖ <= (C * ∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖) : Con
tinuousMultilinearMap 𝕜 E (ContinuousMultilinearMap 𝕜 E' G)
参数：f : MultilinearMap 𝕜 E (MultilinearMap 𝕜 E' G)；C : Real；H : forall m₁ m₂, ‖f 
m₁ m₂‖ <= (C * ∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a map `f : MultilinearMap 𝕜 E (MultilinearMap 𝕜 E' G)` and an estimate
`H : ∀ m m', ‖f m m'‖ ≤ C * ∏ i, ‖m i‖ * ∏ i, ‖m' i‖`, upgrade all `MultilinearM
ap`s in the type to
`ContinuousMultilinearMap`s.
-/
def mkContinuousMultilinear (f : MultilinearMap 𝕜 E (MultilinearMap 𝕜 E' G)) (C : ℝ)
    (H : ∀ m₁ m₂, ‖f m₁ m₂‖ ≤ (C * ∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖) :
    ContinuousMultilinearMap 𝕜 E (ContinuousMultilinearMap 𝕜 E' G) :=
  mkContinuous
    { toFun := fun m => mkContinuous (f m) (C * ∏ i, ‖m i‖) <| H m
      map_update_add' := fun m i x y => by
        ext1
        simp
      map_update_smul' := fun m i c x => by
        ext1
        simp }
    (max C 0) fun m => by
      simp only [coe_mk]
      refine ((f m).mkContinuous_norm_le' _).trans_eq ?_
      rw [max_mul_of_nonneg, zero_mul]
      positivity

@[simp]
/-
**MultilinearMap.mkContinuousMultilinear_apply** 是 Mathlib 中的一个定理，位于命名空间 `Multil
inearMap`。
形式化陈述：mkContinuousMultilinear_apply (f : MultilinearMap 𝕜 E (MultilinearMap 𝕜 E'
 G)) {C : Real} (H : forall m₁ m₂, ‖f m₁ m₂‖ <= (C * ∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖)
 (m : forall i, E i) : ⇑(mkContinuousMultilinear f C H m) = f m
参数：f : MultilinearMap 𝕜 E (MultilinearMap 𝕜 E' G)；H : forall m₁ m₂, ‖f m₁ m₂‖ <=
 (C * ∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖；m : forall i, E i。
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
-/
theorem mkContinuousMultilinear_apply (f : MultilinearMap 𝕜 E (MultilinearMap 𝕜 E' G)) {C : ℝ}
    (H : ∀ m₁ m₂, ‖f m₁ m₂‖ ≤ (C * ∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖) (m : ∀ i, E i) :
    ⇑(mkContinuousMultilinear f C H m) = f m :=
  rfl
/-
**MultilinearMap.mkContinuousMultilinear_norm_le'** 是 Mathlib 中的一个定理，位于命名空间 `Mul
tilinearMap`。
形式化陈述：mkContinuousMultilinear_norm_le' (f : MultilinearMap 𝕜 E (MultilinearMap 𝕜
 E' G)) (C : Real) (H : forall m₁ m₂, ‖f m₁ m₂‖ <= (C * ∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ 
i‖) : ‖mkContinuousMultilinear f C H‖ <= max C 0
参数：f : MultilinearMap 𝕜 E (MultilinearMap 𝕜 E' G)；C : Real；H : forall m₁ m₂, ‖f 
m₁ m₂‖ <= (C * ∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖。
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
· 使用定理 `MultilinearMap.mkContinuous_norm_le`：MultilinearMap.mkContinuous_norm_le
 (f : MultilinearMap 𝕜 E G) {C : Real} (hC : 0 <= C) (H : forall m, ‖f m‖ <= C *
 ∏ i, ‖m i‖) : ‖f.mkConti…
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
-/
theorem mkContinuousMultilinear_norm_le' (f : MultilinearMap 𝕜 E (MultilinearMap 𝕜 E' G)) (C : ℝ)
    (H : ∀ m₁ m₂, ‖f m₁ m₂‖ ≤ (C * ∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖) :
    ‖mkContinuousMultilinear f C H‖ ≤ max C 0 := by
  dsimp only [mkContinuousMultilinear]
  exact mkContinuous_norm_le _ (le_max_right _ _) _
/-
**MultilinearMap.mkContinuousMultilinear_norm_le** 是 Mathlib 中的一个定理，位于命名空间 `Mult
ilinearMap`。
形式化陈述：mkContinuousMultilinear_norm_le (f : MultilinearMap 𝕜 E (MultilinearMap 𝕜 
E' G)) {C : Real} (hC : 0 <= C) (H : forall m₁ m₂, ‖f m₁ m₂‖ <= (C * ∏ i, ‖m₁ i‖
) * ∏ i, ‖m₂ i‖) : ‖mkContinuousMultilinear f C H‖ <= C
参数：f : MultilinearMap 𝕜 E (MultilinearMap 𝕜 E' G)；hC : 0 <= C；H : forall m₁ m₂, 
‖f m₁ m₂‖ <= (C * ∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
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
· 使用定理 `MultilinearMap.mkContinuousMultilinear_norm_le'`：mkContinuousMultilinear
_norm_le' (f : MultilinearMap 𝕜 E (MultilinearMap 𝕜 E' G)) (C : Real) (H : foral
l m₁ m₂, ‖f m₁ m₂‖ <= (C * ∏ i, ‖m₁ i…
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
-/
theorem mkContinuousMultilinear_norm_le (f : MultilinearMap 𝕜 E (MultilinearMap 𝕜 E' G)) {C : ℝ}
    (hC : 0 ≤ C) (H : ∀ m₁ m₂, ‖f m₁ m₂‖ ≤ (C * ∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖) :
    ‖mkContinuousMultilinear f C H‖ ≤ C :=
  (mkContinuousMultilinear_norm_le' f C H).trans_eq (max_eq_left hC)

end MultilinearMap

namespace ContinuousLinearMap

/-
**ContinuousLinearMap.norm_compContinuousMultilinearMap_le** 是 Mathlib 中的一个定理，位于
命名空间 `ContinuousLinearMap`。
形式化陈述：norm_compContinuousMultilinearMap_le (g : G ->L[𝕜] G') (f : ContinuousMult
ilinearMap 𝕜 E G) : ‖g.compContinuousMultilinearMap f‖ <= ‖g‖ * ‖f‖
参数：g : G ->L[𝕜] G'；f : ContinuousMultilinearMap 𝕜 E G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.opNorm_le_bound`：opNorm_le_bound {f : Continuou
sMultilinearMap 𝕜 E G} {M : Real} (hMp : 0 <= M) (hM : forall m, ‖f m‖ <= M * ∏ 
i, ‖m i‖) : ‖f‖ <= M
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `ContinuousLinearMap.le_opNorm_of_le`：le_opNorm_of_le {c : Real} {x} (h :
 ‖x‖ <= c) : ‖f x‖ <= ‖f‖ * c
· 使用定理 `ContinuousMultilinearMap.le_opNorm`：le_opNorm (f : ContinuousMultilinear
Map 𝕜 E G) (m : forall i, E i) : ‖f m‖ <= ‖f‖ * ∏ i, ‖m i‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem norm_compContinuousMultilinearMap_le (g : G →L[𝕜] G') (f : ContinuousMultilinearMap 𝕜 E G) :
    ‖g.compContinuousMultilinearMap f‖ ≤ ‖g‖ * ‖f‖ :=
  ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m ↦
    calc
      ‖g (f m)‖ ≤ ‖g‖ * (‖f‖ * ∏ i, ‖m i‖) := g.le_opNorm_of_le <| f.le_opNorm _
      _ = _ := (mul_assoc _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
/-- Flip arguments in `f : G →L[𝕜] ContinuousMultilinearMap 𝕜 E G'` to get
`ContinuousMultilinearMap 𝕜 E (G →L[𝕜] G')` -/
@[simps! apply_apply]
/-
**ContinuousLinearMap.flipMultilinear** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：flipMultilinear (f : G ->L[𝕜] ContinuousMultilinearMap 𝕜 E G') : Continuou
sMultilinearMap 𝕜 E (G ->L[𝕜] G')
参数：f : G ->L[𝕜] ContinuousMultilinearMap 𝕜 E G'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E

--- 原说明 ---
Flip arguments in `f : G →L[𝕜] ContinuousMultilinearMap 𝕜 E G'` to get
`ContinuousMultilinearMap 𝕜 E (G →L[𝕜] G')`
-/
def flipMultilinear (f : G →L[𝕜] ContinuousMultilinearMap 𝕜 E G') :
    ContinuousMultilinearMap 𝕜 E (G →L[𝕜] G') :=
  MultilinearMap.mkContinuous
    { toFun := fun m =>
        LinearMap.mkContinuous
          { toFun := (f · m)
            map_add' := by simp
            map_smul' := by simp }
          (‖f‖ * ∏ i, ‖m i‖) fun x => by
          rw [mul_right_comm]
          exact (f x).le_of_opNorm_le (f.le_opNorm x) _
      map_update_add' := fun m i x y => by
        ext1
        simp only [add_apply, ContinuousMultilinearMap.map_update_add, LinearMap.coe_mk,
          LinearMap.mkContinuous_apply, AddHom.coe_mk]
      map_update_smul' := fun m i c x => by
        ext1
        simp only [FunLike.coe_smul, ContinuousMultilinearMap.map_update_smul, LinearMap.coe_mk,
          LinearMap.mkContinuous_apply, Pi.smul_apply, AddHom.coe_mk] }
    ‖f‖ fun m => by
      dsimp only [MultilinearMap.coe_mk]
      exact LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- Flip arguments in `f : ContinuousMultilinearMap 𝕜 E (G →L[𝕜] G')` to get
`G →L[𝕜] ContinuousMultilinearMap 𝕜 E G'` -/
@[simps! apply_apply]
/-
**ContinuousLinearMap._root_.ContinuousMultilinearMap.flipLinear** 是 Mathlib 中的一
个定义，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Flip arguments in `f : ContinuousMultilinearMap 𝕜 E (G →L[𝕜] G')` to get
`G →L[𝕜] ContinuousMultilinearMap 𝕜 E G'`
-/
def _root_.ContinuousMultilinearMap.flipLinear (f : ContinuousMultilinearMap 𝕜 E (G →L[𝕜] G')) :
    G →L[𝕜] ContinuousMultilinearMap 𝕜 E G' :=
  MultilinearMap.mkContinuousLinear
    { toFun x :=
        { toFun m := f m x
          map_update_add' := by simp
          map_update_smul' := by simp }
      map_add' x y := by ext1; simp
      map_smul' c x := by ext1; simp } ‖f‖ <| fun x m ↦ by
    rw [LinearMap.coe_mk, AddHom.coe_mk, MultilinearMap.coe_mk, mul_right_comm]
    apply ((f m).le_opNorm x).trans
    gcongr
    apply f.le_opNorm
/-
**ContinuousLinearMap.flipLinear_flipMultilinear** 是 Mathlib 中的一个定理，位于命名空间 `Cont
inuousLinearMap`。
形式化陈述：∀ {𝕜 : Type u} {ι : Type v} {E : ι → Type wE} {G : Type wG} {G' : Type wG'
} [inst : NontriviallyNormedField 𝕜]   [inst_1 : (i : ι) → SeminormedAddCommGrou
p (E i)] [inst_2 : (i : ι) → NormedSpace 𝕜 (E i)]   [inst_3 : SeminormedAddCommG
roup G] [inst_4 : NormedSpace 𝕜 G] [inst_5 : SeminormedAddCommGroup G']   [inst_
6 : NormedSpace 𝕜 G'] [inst_7 : Fintype ι] (f : G →L[𝕜] ContinuousMultilinearMap
 𝕜 E G'),   f.flipMultilinear.flipLinear = f
参数：i : ι；E i；i : ι；E i；f : G →L[𝕜] ContinuousMultilinearMap 𝕜 E G'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
@[simp] lemma flipLinear_flipMultilinear (f : G →L[𝕜] ContinuousMultilinearMap 𝕜 E G') :
    f.flipMultilinear.flipLinear = f := rfl
/-
**ContinuousLinearMap._root_.ContinuousMultilinearMap.flipMultilinear_flipLinear
** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.ContinuousMultilinearMap.flipMultilinear_flipLinear
    (f : ContinuousMultilinearMap 𝕜 E (G →L[𝕜] G')) :
    f.flipLinear.flipMultilinear = f := rfl

variable (𝕜 E G G') in
/-- Flipping arguments gives a linear equivalence between `G →L[𝕜] ContinuousMultilinearMap 𝕜 E G'`
and `ContinuousMultilinearMap 𝕜 E (G →L[𝕜] G')` -/
/-
**ContinuousLinearMap.flipMultilinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Continuous
LinearMap`。
形式化陈述：flipMultilinearEquiv : (G ->L[𝕜] ContinuousMultilinearMap 𝕜 E G') ≃L[𝕜] Co
ntinuousMultilinearMap 𝕜 E (G ->L[𝕜] G')
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E

--- 原说明 ---
Flipping arguments gives a linear equivalence between `G →L[𝕜] ContinuousMultili
nearMap 𝕜 E G'`
and `ContinuousMultilinearMap 𝕜 E (G →L[𝕜] G')`
-/
def flipMultilinearEquivₗ : (G →L[𝕜] ContinuousMultilinearMap 𝕜 E G') ≃ₗ[𝕜]
    (ContinuousMultilinearMap 𝕜 E (G →L[𝕜] G')) where
  toFun f := f.flipMultilinear
  invFun f := f.flipLinear
  map_add' f g := by ext; simp
  map_smul' c f := by ext; simp
  left_inv f := rfl
  right_inv f := rfl

variable (𝕜 E G G') in
/-- Flipping arguments gives a continuous linear equivalence between
`G →L[𝕜] ContinuousMultilinearMap 𝕜 E G'` and `ContinuousMultilinearMap 𝕜 E (G →L[𝕜] G')` -/
/-
**ContinuousLinearMap.flipMultilinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Continuous
LinearMap`。
形式化陈述：flipMultilinearEquiv : (G ->L[𝕜] ContinuousMultilinearMap 𝕜 E G') ≃L[𝕜] Co
ntinuousMultilinearMap 𝕜 E (G ->L[𝕜] G')
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E

--- 原说明 ---
Flipping arguments gives a continuous linear equivalence between
`G →L[𝕜] ContinuousMultilinearMap 𝕜 E G'` and `ContinuousMultilinearMap 𝕜 E (G →
L[𝕜] G')`
-/
def flipMultilinearEquiv : (G →L[𝕜] ContinuousMultilinearMap 𝕜 E G') ≃L[𝕜]
    ContinuousMultilinearMap 𝕜 E (G →L[𝕜] G') := by
  refine (flipMultilinearEquivₗ 𝕜 E G G').toContinuousLinearEquivOfBounds 1 1 ?_ ?_
  · intro f
    suffices ‖f.flipMultilinear‖ ≤ ‖f‖ by simpa
    apply MultilinearMap.mkContinuous_norm_le
    positivity
  · intro f
    suffices ‖f.flipLinear‖ ≤ ‖f‖ by simpa
    apply MultilinearMap.mkContinuousLinear_norm_le
    positivity
/-
**ContinuousLinearMap.coe_flipMultilinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Contin
uousLinearMap`。
形式化陈述：∀ {𝕜 : Type u} {ι : Type v} {E : ι → Type wE} {G : Type wG} {G' : Type wG'
} [inst : NontriviallyNormedField 𝕜]   [inst_1 : (i : ι) → SeminormedAddCommGrou
p (E i)] [inst_2 : (i : ι) → NormedSpace 𝕜 (E i)]   [inst_3 : SeminormedAddCommG
roup G] [inst_4 : NormedSpace 𝕜 G] [inst_5 : SeminormedAddCommGroup G']   [inst_
6 : NormedSpace 𝕜 G'] [inst_7 : Fintype ι],   ⇑(ContinuousLinearMap.flipMultilin
earEquiv 𝕜 E G G') = ContinuousLinearMap.flipMultilinear
参数：i : ι；E i；i : ι；E i；ContinuousLinearMap.flipMultilinearEquiv 𝕜 E G G'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousMultilinearMap.instSMulCommClass`：∀ {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCommMo
noid M₂]   [inst_2 : (i : ι) → T…
-/
@[simp] lemma coe_flipMultilinearEquiv :
    (flipMultilinearEquiv 𝕜 E G G' : (G →L[𝕜] ContinuousMultilinearMap 𝕜 E G') →
      (ContinuousMultilinearMap 𝕜 E (G →L[𝕜] G'))) = flipMultilinear := rfl
/-
**ContinuousLinearMap.coe_symm_flipMultilinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `C
ontinuousLinearMap`。
形式化陈述：∀ {𝕜 : Type u} {ι : Type v} {E : ι → Type wE} {G : Type wG} {G' : Type wG'
} [inst : NontriviallyNormedField 𝕜]   [inst_1 : (i : ι) → SeminormedAddCommGrou
p (E i)] [inst_2 : (i : ι) → NormedSpace 𝕜 (E i)]   [inst_3 : SeminormedAddCommG
roup G] [inst_4 : NormedSpace 𝕜 G] [inst_5 : SeminormedAddCommGroup G']   [inst_
6 : NormedSpace 𝕜 G'] [inst_7 : Fintype ι],   ⇑(ContinuousLinearMap.flipMultilin
earEquiv 𝕜 E G G').symm = ContinuousMultilinearMap.flipLinear
参数：i : ι；E i；i : ι；E i；ContinuousLinearMap.flipMultilinearEquiv 𝕜 E G G'。
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
· 使用定理 `ContinuousMultilinearMap.instSMulCommClass`：∀ {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCommMo
noid M₂]   [inst_2 : (i : ι) → T…
-/
@[simp] lemma coe_symm_flipMultilinearEquiv :
    ((flipMultilinearEquiv 𝕜 E G G').symm : (ContinuousMultilinearMap 𝕜 E (G →L[𝕜] G')) →
    (G →L[𝕜] ContinuousMultilinearMap 𝕜 E G')) = flipLinear := rfl

end ContinuousLinearMap

/-
**LinearIsometry.norm_compContinuousMultilinearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIsometry.norm_compContinuousMultilinearMap (g : G ->ₗᵢ[𝕜] G') (f : C
ontinuousMultilinearMap 𝕜 E G) : ‖g.toContinuousLinearMap.compContinuousMultilin
earMap f‖ = ‖f‖
参数：g : G ->ₗᵢ[𝕜] G'；f : ContinuousMultilinearMap 𝕜 E G。
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
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ContinuousLinearMap.compContinuousMultilinearMap_coe`：∀ {R : Type u} {ι 
: Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} {M₃ : Type w₃} [inst : Semiring R]  
 [inst_1 : (i : ι) → AddCommMonoid (M₁ i)]…
· 使用定理 `LinearIsometry.norm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5}
 {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [
inst_2 : Semi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem LinearIsometry.norm_compContinuousMultilinearMap (g : G →ₗᵢ[𝕜] G')
    (f : ContinuousMultilinearMap 𝕜 E G) :
    ‖g.toContinuousLinearMap.compContinuousMultilinearMap f‖ = ‖f‖ := by
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map,
    ContinuousMultilinearMap.norm_def, Function.comp_apply]

namespace ContinuousMultilinearMap

/-
**ContinuousMultilinearMap.norm_compContinuousLinearMap_le** 是 Mathlib 中的一个定理，位于
命名空间 `ContinuousMultilinearMap`。
形式化陈述：norm_compContinuousLinearMap_le (g : ContinuousMultilinearMap 𝕜 E₁ G) (f :
 forall i, E i ->L[𝕜] E₁ i) : ‖g.compContinuousLinearMap f‖ <= ‖g‖ * ∏ i, ‖f i‖
参数：g : ContinuousMultilinearMap 𝕜 E₁ G；f : forall i, E i ->L[𝕜] E₁ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.opNorm_le_bound`：opNorm_le_bound {f : Continuou
sMultilinearMap 𝕜 E G} {M : Real} (hMp : 0 <= M) (hM : forall m, ‖f m‖ <= M * ∏ 
i, ‖m i‖) : ‖f‖ <= M
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `Finset.prod_nonneg`：prod_nonneg (h0 : forall i in s, 0 <= f i) : 0 <= ∏ 
i in s, f i
· 使用定理 `ContinuousMultilinearMap.le_opNorm`：le_opNorm (f : ContinuousMultilinear
Map 𝕜 E G) (m : forall i, E i) : ‖f m‖ <= ‖f‖ * ∏ i, ‖m i‖
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用引理 `Finset.prod_le_prod`：prod_le_prod (h0 : forall i in s, 0 <= f i) (h1 : f
orall i in s, f i <= g i) : ∏ i in s, f i <= ∏ i in s, g i
· 使用定理 `ContinuousLinearMap.le_opNorm`：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem norm_compContinuousLinearMap_le (g : ContinuousMultilinearMap 𝕜 E₁ G)
    (f : ∀ i, E i →L[𝕜] E₁ i) : ‖g.compContinuousLinearMap f‖ ≤ ‖g‖ * ∏ i, ‖f i‖ :=
  opNorm_le_bound (by positivity) fun m =>
    calc
      ‖g fun i => f i (m i)‖ ≤ ‖g‖ * ∏ i, ‖f i (m i)‖ := g.le_opNorm _
      _ ≤ ‖g‖ * ∏ i, ‖f i‖ * ‖m i‖ := by gcongr with i; exact (f i).le_opNorm (m i)
      _ = (‖g‖ * ∏ i, ‖f i‖) * ∏ i, ‖m i‖ := by rw [prod_mul_distrib, mul_assoc]
/-
**ContinuousMultilinearMap.norm_compContinuous_linearIsometry_le** 是 Mathlib 中的一
个定理，位于命名空间 `ContinuousMultilinearMap`。
形式化陈述：norm_compContinuous_linearIsometry_le (g : ContinuousMultilinearMap 𝕜 E₁ G
) (f : forall i, E i ->ₗᵢ[𝕜] E₁ i) : ‖g.compContinuousLinearMap fun i => (f i).t
oContinuousLinearMap‖ <= ‖g‖
参数：g : ContinuousMultilinearMap 𝕜 E₁ G；f : forall i, E i ->ₗᵢ[𝕜] E₁ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.opNorm_le_bound`：opNorm_le_bound {f : Continuou
sMultilinearMap 𝕜 E G} {M : Real} (hMp : 0 <= M) (hM : forall m, ‖f m‖ <= M * ∏ 
i, ‖m i‖) : ‖f‖ <= M
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `ContinuousMultilinearMap.le_opNorm`：le_opNorm (f : ContinuousMultilinear
Map 𝕜 E G) (m : forall i, E i) : ‖f m‖ <= ‖f‖ * ∏ i, ‖m i‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearIsometry.norm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5}
 {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [
inst_2 : Semi…
-/
theorem norm_compContinuous_linearIsometry_le (g : ContinuousMultilinearMap 𝕜 E₁ G)
    (f : ∀ i, E i →ₗᵢ[𝕜] E₁ i) :
    ‖g.compContinuousLinearMap fun i => (f i).toContinuousLinearMap‖ ≤ ‖g‖ := by
  refine opNorm_le_bound (norm_nonneg _) fun m => ?_
  apply (g.le_opNorm _).trans _
  simp only [ContinuousLinearMap.coe_coe, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometry.norm_map, le_rfl]
/-
**ContinuousMultilinearMap.norm_compContinuous_linearIsometryEquiv** 是 Mathlib 中
的一个定理，位于命名空间 `ContinuousMultilinearMap`。
形式化陈述：norm_compContinuous_linearIsometryEquiv (g : ContinuousMultilinearMap 𝕜 E₁
 G) (f : forall i, E i ≃ₗᵢ[𝕜] E₁ i) : ‖g.compContinuousLinearMap fun i => (f i :
 E i ->L[𝕜] E₁ i)‖ = ‖g‖
参数：g : ContinuousMultilinearMap 𝕜 E₁ G；f : forall i, E i ≃ₗᵢ[𝕜] E₁ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `ContinuousMultilinearMap.norm_compContinuous_linearIsometry_le`：norm_com
pContinuous_linearIsometry_le (g : ContinuousMultilinearMap 𝕜 E₁ G) (f : forall 
i, E i ->ₗᵢ[𝕜] E₁ i) : ‖g.compContinuousLinearMap fu…
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearIsometryEquiv.apply_symm_apply`：apply_symm_apply (x : E₂) : e (e.s
ymm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_compContinuous_linearIsometryEquiv (g : ContinuousMultilinearMap 𝕜 E₁ G)
    (f : ∀ i, E i ≃ₗᵢ[𝕜] E₁ i) :
    ‖g.compContinuousLinearMap fun i => (f i : E i →L[𝕜] E₁ i)‖ = ‖g‖ := by
  apply le_antisymm (g.norm_compContinuous_linearIsometry_le fun i => (f i).toLinearIsometry)
  have : g = (g.compContinuousLinearMap fun i => (f i : E i →L[𝕜] E₁ i)).compContinuousLinearMap
      fun i => ((f i).symm : E₁ i →L[𝕜] E i) := by
    ext1 m
    simp
  conv_lhs => rw [this]
  apply (g.compContinuousLinearMap fun i =>
    (f i : E i →L[𝕜] E₁ i)).norm_compContinuous_linearIsometry_le
      fun i => (f i).symm.toLinearIsometry


variable (G) in
/-
**ContinuousMultilinearMap.norm_compContinuousLinearMapL_le** 是 Mathlib 中的一个定理，位
于命名空间 `ContinuousMultilinearMap`。
形式化陈述：norm_compContinuousLinearMapL_le (f : forall i, E i ->L[𝕜] E₁ i) : ‖compCo
ntinuousLinearMapL (F
参数：f : forall i, E i ->L[𝕜] E₁ i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用引理 `Finset.prod_nonneg`：prod_nonneg (h0 : forall i in s, 0 <= f i) : 0 <= ∏ 
i in s, f i
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `ContinuousMultilinearMap.norm_compContinuousLinearMap_le`：norm_compConti
nuousLinearMap_le (g : ContinuousMultilinearMap 𝕜 E₁ G) (f : forall i, E i ->L[𝕜
] E₁ i) : ‖g.compContinuousLinearMap f‖ <= ‖g‖…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem norm_compContinuousLinearMapL_le (f : ∀ i, E i →L[𝕜] E₁ i) :
    ‖compContinuousLinearMapL (F := G) f‖ ≤ ∏ i, ‖f i‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun g ↦
    norm_compContinuousLinearMap_le _ _ |>.trans_eq <| mul_comm _ _

/-- `ContinuousMultilinearMap.compContinuousLinearMap` as a bundled continuous linear map.
This implementation fixes `g : ContinuousMultilinearMap 𝕜 E₁ G`.

Actually, the map is linear in `g`,
see `ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear`.

For a version fixing `f` and varying `g`, see `compContinuousLinearMapL`. -/
/-
**ContinuousMultilinearMap.compContinuousLinearMapLRight** 是 Mathlib 中的一个定义，位于命名
空间 `ContinuousMultilinearMap`。
形式化陈述：compContinuousLinearMapLRight (g : ContinuousMultilinearMap 𝕜 E₁ G) : Cont
inuousMultilinearMap 𝕜 (fun i => E i ->L[𝕜] E₁ i) (ContinuousMultilinearMap 𝕜 E 
G)
参数：g : ContinuousMultilinearMap 𝕜 E₁ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousMultilinearMap.compContinuousLinearMap` as a bundled continuous linea
r map.
This implementation fixes `g : ContinuousMultilinearMap 𝕜 E₁ G`.

Actually, the map is linear in `g`,
see `ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear`.

For a version fixing `f` and varying `g`, see `compContinuousLinearMapL`.
-/
def compContinuousLinearMapLRight (g : ContinuousMultilinearMap 𝕜 E₁ G) :
    ContinuousMultilinearMap 𝕜 (fun i ↦ E i →L[𝕜] E₁ i) (ContinuousMultilinearMap 𝕜 E G) :=
  MultilinearMap.mkContinuous
    { toFun := fun f => g.compContinuousLinearMap f
      map_update_add' := by
        intro h f i f₁ f₂
        ext x
        simp only [compContinuousLinearMap_apply, add_apply]
        convert! g.map_update_add (fun j ↦ f j (x j)) i (f₁ (x i)) (f₂ (x i)) <;>
          exact apply_update (fun (i : ι) (f : E i →L[𝕜] E₁ i) ↦ f (x i)) f i _ _
      map_update_smul' := by
        intro h f i a f₀
        ext x
        simp only [compContinuousLinearMap_apply, smul_apply]
        convert! g.map_update_smul (fun j ↦ f j (x j)) i a (f₀ (x i)) <;>
          exact apply_update (fun (i : ι) (f : E i →L[𝕜] E₁ i) ↦ f (x i)) f i _ _ }
    (‖g‖) (fun f ↦ by simp [norm_compContinuousLinearMap_le])

@[simp]
/-
**ContinuousMultilinearMap.compContinuousLinearMapLRight_apply** 是 Mathlib 中的一个定
理，位于命名空间 `ContinuousMultilinearMap`。
形式化陈述：compContinuousLinearMapLRight_apply (g : ContinuousMultilinearMap 𝕜 E₁ G) 
(f : forall i, E i ->L[𝕜] E₁ i) : compContinuousLinearMapLRight g f = g.compCont
inuousLinearMap f
参数：g : ContinuousMultilinearMap 𝕜 E₁ G；f : forall i, E i ->L[𝕜] E₁ i。
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
-/
theorem compContinuousLinearMapLRight_apply (g : ContinuousMultilinearMap 𝕜 E₁ G)
    (f : ∀ i, E i →L[𝕜] E₁ i) : compContinuousLinearMapLRight g f = g.compContinuousLinearMap f :=
  rfl

variable (E) in
/-
**ContinuousMultilinearMap.norm_compContinuousLinearMapLRight_le** 是 Mathlib 中的一
个定理，位于命名空间 `ContinuousMultilinearMap`。
形式化陈述：norm_compContinuousLinearMapLRight_le (g : ContinuousMultilinearMap 𝕜 E₁ G
) : ‖compContinuousLinearMapLRight (E
参数：g : ContinuousMultilinearMap 𝕜 E₁ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.mkContinuous_norm_le`：MultilinearMap.mkContinuous_norm_le
 (f : MultilinearMap 𝕜 E G) {C : Real} (hC : 0 <= C) (H : forall m, ‖f m‖ <= C *
 ∏ i, ‖m i‖) : ‖f.mkConti…
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem norm_compContinuousLinearMapLRight_le (g : ContinuousMultilinearMap 𝕜 E₁ G) :
    ‖compContinuousLinearMapLRight (E := E) g‖ ≤ ‖g‖ :=
  MultilinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

variable (𝕜 E E₁ G)

open Function in
/-- If `f` is a collection of continuous linear maps, then the construction
`ContinuousMultilinearMap.compContinuousLinearMap`
sending a continuous multilinear map `g` to `g (f₁ ·, ..., fₙ ·)`
is continuous-linear in `g` and multilinear in `f₁, ..., fₙ`. -/
/-
**ContinuousMultilinearMap.compContinuousLinearMapMultilinear** 是 Mathlib 中的一个定义
，位于命名空间 `ContinuousMultilinearMap`。
形式化陈述：compContinuousLinearMapMultilinear : MultilinearMap 𝕜 (fun i => E i ->L[𝕜]
 E₁ i) ((ContinuousMultilinearMap 𝕜 E₁ G) ->L[𝕜] ContinuousMultilinearMap 𝕜 E G)
 where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E

--- 原说明 ---
If `f` is a collection of continuous linear maps, then the construction
`ContinuousMultilinearMap.compContinuousLinearMap`
sending a continuous multilinear map `g` to `g (f₁ ·, ..., fₙ ·)`
is continuous-linear in `g` and multilinear in `f₁, ..., fₙ`.
-/
noncomputable def compContinuousLinearMapMultilinear :
    MultilinearMap 𝕜 (fun i ↦ E i →L[𝕜] E₁ i)
      ((ContinuousMultilinearMap 𝕜 E₁ G) →L[𝕜] ContinuousMultilinearMap 𝕜 E G) where
  toFun := compContinuousLinearMapL
  map_update_add' f i f₁ f₂ := by
    ext g x
    change (g fun j ↦ update f i (f₁ + f₂) j <| x j) =
        (g fun j ↦ update f i f₁ j <| x j) + g fun j ↦ update f i f₂ j (x j)
    convert! g.map_update_add (fun j ↦ f j (x j)) i (f₁ (x i)) (f₂ (x i)) <;>
      exact apply_update (fun (i : ι) (f : E i →L[𝕜] E₁ i) ↦ f (x i)) f i _ _
  map_update_smul' f i a f₀ := by
    ext g x
    change (g fun j ↦ update f i (a • f₀) j <| x j) = a • g fun j ↦ update f i f₀ j (x j)
    convert! g.map_update_smul (fun j ↦ f j (x j)) i a (f₀ (x i)) <;>
      exact apply_update (fun (i : ι) (f : E i →L[𝕜] E₁ i) ↦ f (x i)) f i _ _

/-- If `f` is a collection of continuous linear maps, then the construction
`ContinuousMultilinearMap.compContinuousLinearMap`
sending a continuous multilinear map `g` to `g (f₁ ·, ..., fₙ ·)` is continuous-linear in `g` and
continuous-multilinear in `f₁, ..., fₙ`. -/
@[simps! apply_apply]
/-
**ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear** 是 Math
lib 中的一个定义，位于命名空间 `ContinuousMultilinearMap`。
形式化陈述：compContinuousLinearMapContinuousMultilinear : ContinuousMultilinearMap 𝕜 
(fun i => E i ->L[𝕜] E₁ i) ((ContinuousMultilinearMap 𝕜 E₁ G) ->L[𝕜] ContinuousM
ultilinearMap 𝕜 E G)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E

--- 原说明 ---
If `f` is a collection of continuous linear maps, then the construction
`ContinuousMultilinearMap.compContinuousLinearMap`
sending a continuous multilinear map `g` to `g (f₁ ·, ..., fₙ ·)` is continuous-
linear in `g` and
continuous-multilinear in `f₁, ..., fₙ`.
-/
noncomputable def compContinuousLinearMapContinuousMultilinear :
    ContinuousMultilinearMap 𝕜 (fun i ↦ E i →L[𝕜] E₁ i)
      ((ContinuousMultilinearMap 𝕜 E₁ G) →L[𝕜] ContinuousMultilinearMap 𝕜 E G) :=
  MultilinearMap.mkContinuous (𝕜 := 𝕜) (E := fun i ↦ E i →L[𝕜] E₁ i)
    (G := (ContinuousMultilinearMap 𝕜 E₁ G) →L[𝕜] ContinuousMultilinearMap 𝕜 E G)
    (compContinuousLinearMapMultilinear 𝕜 E E₁ G) 1 fun f ↦ by
      rw [one_mul]
      apply norm_compContinuousLinearMapL_le

variable {𝕜 E E₁ G}

/-- Fréchet derivative of `compContinuousLinearMap f g` with respect to `g`.
The derivative with respect to `f` is given by `compContinuousLinearMapL`. -/
/-
**ContinuousMultilinearMap.fderivCompContinuousLinearMap** 是 Mathlib 中的一个定义，位于命名
空间 `ContinuousMultilinearMap`。
形式化陈述：fderivCompContinuousLinearMap [DecidableEq ι] (f : ContinuousMultilinearMa
p 𝕜 E₁ G) (g : forall i, E i ->L[𝕜] E₁ i) : (forall i, E i ->L[𝕜] E₁ i) ->L[𝕜] C
ontinuousMultilinearMap 𝕜 E G
参数：f : ContinuousMultilinearMap 𝕜 E₁ G；g : forall i, E i ->L[𝕜] E₁ i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Fréchet derivative of `compContinuousLinearMap f g` with respect to `g`.
The derivative with respect to `f` is given by `compContinuousLinearMapL`.
-/
noncomputable def fderivCompContinuousLinearMap [DecidableEq ι]
    (f : ContinuousMultilinearMap 𝕜 E₁ G) (g : ∀ i, E i →L[𝕜] E₁ i) :
    (∀ i, E i →L[𝕜] E₁ i) →L[𝕜] ContinuousMultilinearMap 𝕜 E G :=
  ContinuousLinearMap.apply _ _ f
    |>.compContinuousMultilinearMap (compContinuousLinearMapContinuousMultilinear 𝕜 _ _ _)
    |>.linearDeriv g

@[simp]
/-
**ContinuousMultilinearMap.fderivCompContinuousLinearMap_apply** 是 Mathlib 中的一个引
理，位于命名空间 `ContinuousMultilinearMap`。
形式化陈述：fderivCompContinuousLinearMap_apply [DecidableEq ι] (f : ContinuousMultili
nearMap 𝕜 E₁ G) (g : forall i, E i ->L[𝕜] E₁ i) (dg : forall i, E i ->L[𝕜] E₁ i)
 (v : forall i, E i) : f.fderivCompContinuousLinearMap g dg v = ∑ i, f fun j => 
(update g i (dg i) j) (v j)
参数：f : ContinuousMultilinearMap 𝕜 E₁ G；g : forall i, E i ->L[𝕜] E₁ i；dg : forall
 i, E i ->L[𝕜] E₁ i；v : forall i, E i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ContinuousMultilinearMap.linearDeriv_apply`：linearDeriv_apply : f.linear
Deriv x y = ∑ i, f (Function.update x i (y i))
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ContinuousLinearMap.compContinuousMultilinearMap_coe`：∀ {R : Type u} {ι 
: Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} {M₃ : Type w₃} [inst : Semiring R]  
 [inst_1 : (i : ι) → AddCommMonoid (M₁ i)]…
· 使用定理 `ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear_ap
ply_apply`：∀ (𝕜 : Type u) {ι : Type v} (E : ι → Type wE) (E₁ : ι → Type wE₁) (G 
: Type wG) [inst : NontriviallyNormedField 𝕜]   [inst_1 : (i : ι) → Sem…
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousMultilinearMap.instIsZeroApplyForall`：∀ {R : Type u} {ι : Type
 v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → 
AddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `ContinuousMultilinearMap.instIsAddApplyForall`：∀ {R : Type u} {ι : Type 
v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → A
ddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fderivCompContinuousLinearMap_apply [DecidableEq ι]
    (f : ContinuousMultilinearMap 𝕜 E₁ G) (g : ∀ i, E i →L[𝕜] E₁ i)
    (dg : ∀ i, E i →L[𝕜] E₁ i) (v : ∀ i, E i) :
    f.fderivCompContinuousLinearMap g dg v = ∑ i, f fun j ↦ (update g i (dg i) j) (v j) := by
  simp [fderivCompContinuousLinearMap]

/-- One of the components of the iterated derivative of a continuous multilinear map. Given a
bijection `e` between a type `α` (typically `Fin k`) and a subset `s` of `ι`, this component is a
continuous multilinear map of `k` vectors `v₁, ..., vₖ`, mapping them
to `f (x₁, (v_{e.symm 2})₂, x₃, ...)`, where at indices `i` in `s` one uses the `i`-th coordinate of
the vector `v_{e.symm i}` and otherwise one uses the `i`-th coordinate of a reference vector `x`.
This is continuous multilinear in the components of `x` outside of `s`, and in the `v_j`. -/
/-
**ContinuousMultilinearMap.iteratedFDerivComponent** 是 Mathlib 中的一个定义，位于命名空间 `Co
ntinuousMultilinearMap`。
形式化陈述：iteratedFDerivComponent {α : Type*} [Fintype α] (f : ContinuousMultilinear
Map 𝕜 E₁ G) {s : Set ι} (e : α ≃ s) [DecidablePred (· in s)] : ContinuousMultili
nearMap 𝕜 (fun (i : {a : ι // a ∉ s}) => E₁ i) (ContinuousMultilinearMap 𝕜 (fun 
(_ : α) => (forall i, E₁ i)) G)
参数：f : ContinuousMultilinearMap 𝕜 E₁ G；e : α ≃ s；· in s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
One of the components of the iterated derivative of a continuous multilinear map
. Given a
bijection `e` between a type `α` (typically `Fin k`) and a subset `s` of `ι`, th
is component is a
continuous multilinear map of `k` vectors `v₁, ..., vₖ`, mapping them
to `f (x₁, (v_{e.symm 2})₂, x₃, ...)`, where at indices `i` in `s` one uses the 
`i`-th coordinate of
the vector `v_{e.symm i}` and otherwise one uses the `i`-th coordinate of a refe
rence vector `x`.
This is continuous multilinear in the components of `x` outside of `s`, and in t
he `v_j`.
-/
noncomputable def iteratedFDerivComponent {α : Type*} [Fintype α]
    (f : ContinuousMultilinearMap 𝕜 E₁ G) {s : Set ι} (e : α ≃ s) [DecidablePred (· ∈ s)] :
    ContinuousMultilinearMap 𝕜 (fun (i : {a : ι // a ∉ s}) ↦ E₁ i)
      (ContinuousMultilinearMap 𝕜 (fun (_ : α) ↦ (∀ i, E₁ i)) G) :=
  (f.toMultilinearMap.iteratedFDerivComponent e).mkContinuousMultilinear ‖f‖ <| by
    intro x m
    simp only [MultilinearMap.iteratedFDerivComponent, MultilinearMap.domDomRestrictₗ,
      MultilinearMap.coe_mk, MultilinearMap.domDomRestrict_apply, coe_coe]
    apply (f.le_opNorm _).trans _
    classical
    rw [← prod_compl_mul_prod s.toFinset, mul_assoc]
    gcongr
    · apply le_of_eq
      have : ∀ x, x ∈ s.toFinsetᶜ ↔ (fun x ↦ x ∉ s) x := by simp
      rw [prod_subtype _ this]
      congr with i
      simp [i.2]
    · rw [prod_subtype _ (fun _ ↦ s.mem_toFinset), ← Equiv.prod_comp e.symm]
      gcongr with i
      simpa only [i.2, ↓reduceDIte, Subtype.coe_eta] using norm_le_pi_norm (m (e.symm i)) ↑i
/-
**ContinuousMultilinearMap.iteratedFDerivComponent_apply** 是 Mathlib 中的一个定理，位于命名
空间 `ContinuousMultilinearMap`。
形式化陈述：∀ {𝕜 : Type u} {ι : Type v} {E₁ : ι → Type wE₁} {G : Type wG} [inst : Nont
riviallyNormedField 𝕜]   [inst_1 : (i : ι) → SeminormedAddCommGroup (E₁ i)] [ins
t_2 : (i : ι) → NormedSpace 𝕜 (E₁ i)]   [inst_3 : SeminormedAddCommGroup G] [ins
t_4 : NormedSpace 𝕜 G] [inst_5 : Fintype ι] {α : Type u_1}   [inst_6 : Fintype α
] (f : ContinuousMultilinearMap 𝕜 E₁ G) {s : Set ι} (e : α ≃ ↑s)   [inst_7 : Dec
idablePred fun x => x ∈ s] (v : (i : { a // a ∉ s }) → E₁ ↑i) (w : α → (i : ι) →
 E₁ i),   ((f.iteratedFDerivComponent e) v) w = f fun j => if h : j ∈ s then w (
e.symm ⟨j, h⟩) j else v ⟨j, h⟩
参数：i : ι；E₁ i；i : ι；E₁ i；f : ContinuousMultilinearMap 𝕜 E₁ G；e : α ≃ ↑s；v : (i :
 { a // a ∉ s }) → E₁ ↑i；w : α → (i : ι) → E₁ i；(f.iteratedFDerivComponent e) v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
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
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `MultilinearMap.mk.congr_simp`：∀ {R : Type uR} {ι : Type uι} {M₁ : ι → Ty
pe v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoid (M
₁ i)] [inst_2 : Ad…
· 使用定理 `MultilinearMap.mkContinuousMultilinear.congr_simp`：∀ {𝕜 : Type u} {ι : T
ype v} {ι' : Type v'} {E : ι → Type wE} {E' : ι' → Type wE'} {G : Type wG} [inst
 : Fintype ι']   [inst_1 : Nontrivially…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma iteratedFDerivComponent_apply {α : Type*} [Fintype α]
    (f : ContinuousMultilinearMap 𝕜 E₁ G) {s : Set ι} (e : α ≃ s) [DecidablePred (· ∈ s)]
    (v : ∀ i : {a : ι // a ∉ s}, E₁ i) (w : α → (∀ i, E₁ i)) :
    f.iteratedFDerivComponent e v w =
      f (fun j ↦ if h : j ∈ s then w (e.symm ⟨j, h⟩) j else v ⟨j, h⟩) := by
  simp [iteratedFDerivComponent, MultilinearMap.iteratedFDerivComponent,
    MultilinearMap.domDomRestrictₗ]
/-
**ContinuousMultilinearMap.norm_iteratedFDerivComponent_le** 是 Mathlib 中的一个引理，位于
命名空间 `ContinuousMultilinearMap`。
形式化陈述：norm_iteratedFDerivComponent_le {α : Type*} [Fintype α] (f : ContinuousMul
tilinearMap 𝕜 E₁ G) {s : Set ι} (e : α ≃ s) [DecidablePred (· in s)] (x : (i : ι
) -> E₁ i) : ‖f.iteratedFDerivComponent e (x ·)‖ <= ‖f‖ * ‖x‖ ^ (Fintype.card ι 
- Fintype.card α)
参数：f : ContinuousMultilinearMap 𝕜 E₁ G；e : α ≃ s；· in s；x : (i : ι) -> E₁ i。
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
· 使用定理 `ContinuousMultilinearMap.le_opNorm`：le_opNorm (f : ContinuousMultilinear
Map 𝕜 E G) (m : forall i, E i) : ‖f m‖ <= ‖f‖ * ∏ i, ‖m i‖
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `MultilinearMap.mkContinuousMultilinear_norm_le`：mkContinuousMultilinear_
norm_le (f : MultilinearMap 𝕜 E (MultilinearMap 𝕜 E' G)) {C : Real} (hC : 0 <= C
) (H : forall m₁ m₂, ‖f m₁ m₂‖ <= (C…
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `Finset.prod_le_prod`：prod_le_prod (h0 : forall i in s, 0 <= f i) (h1 : f
orall i in s, f i <= g i) : ∏ i in s, f i <= ∏ i in s, g i
· 使用定理 `norm_le_pi_norm`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : Fintype ι] 
[inst_1 : (i : ι) → SeminormedAddGroup (G i)] (f : (i : ι) → G i)   (i : ι), ‖f 
i‖ ≤ …
· 使用引理 `Finset.prod_nonneg`：prod_nonneg (h0 : forall i in s, 0 <= f i) : 0 <= ∏ 
i in s, f i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fintype.card_subtype_compl`：Fintype.card_subtype_compl [Fintype α] (p : 
α -> Prop) [Fintype { x // p x }] [Fintype { x // ¬p x }] : Fintype.card { x // 
¬p x } = Fintype…
· 使用定理 `Fintype.card_ofFinset`：card_ofFinset {p : Set α} (s : Finset α) (H : for
all x, x in s ↔ x in p) : @Fintype.card p (ofFinset s H) = #s
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma norm_iteratedFDerivComponent_le {α : Type*} [Fintype α]
    (f : ContinuousMultilinearMap 𝕜 E₁ G) {s : Set ι} (e : α ≃ s) [DecidablePred (· ∈ s)]
    (x : (i : ι) → E₁ i) :
    ‖f.iteratedFDerivComponent e (x ·)‖ ≤ ‖f‖ * ‖x‖ ^ (Fintype.card ι - Fintype.card α) := calc
  ‖f.iteratedFDerivComponent e (fun i ↦ x i)‖
    ≤ ‖f.iteratedFDerivComponent e‖ * ∏ i : {a : ι // a ∉ s}, ‖x i‖ :=
      ContinuousMultilinearMap.le_opNorm _ _
  _ ≤ ‖f‖ * ∏ _i : {a : ι // a ∉ s}, ‖x‖ := by
      gcongr
      · exact MultilinearMap.mkContinuousMultilinear_norm_le _ (norm_nonneg _) _
      · exact norm_le_pi_norm _ _
  _ = ‖f‖ * ‖x‖ ^ (Fintype.card {a : ι // a ∉ s}) := by rw [prod_const, card_univ]
  _ = ‖f‖ * ‖x‖ ^ (Fintype.card ι - Fintype.card α) := by simp [Fintype.card_congr e]

open scoped Classical in
/-- The `k`-th iterated derivative of a continuous multilinear map `f` at the point `x`. It is a
continuous multilinear map of `k` vectors `v₁, ..., vₖ` (with the same type as `x`), mapping them
to `∑ f (x₁, (v_{i₁})₂, x₃, ...)`, where at each index `j` one uses either `xⱼ` or one
of the `(vᵢ)ⱼ`, and each `vᵢ` has to be used exactly once.
The sum is parameterized by the embeddings of `Fin k` in the index type `ι` (or, equivalently,
by the subsets `s` of `ι` of cardinality `k` and then the bijections between `Fin k` and `s`).

The fact that this is indeed the iterated Fréchet derivative is proved in
`ContinuousMultilinearMap.iteratedFDeriv_eq`.
-/
/-
**ContinuousMultilinearMap.iteratedFDeriv** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousM
ultilinearMap`。
形式化陈述：{𝕜 : Type u} →   {ι : Type v} →     {E₁ : ι → Type wE₁} →       {G : Type 
wG} →         [inst : NontriviallyNormedField 𝕜] →           [inst_1 : (i : ι) →
 SeminormedAddCommGroup (E₁ i)] →             [inst_2 : (i : ι) → NormedSpace 𝕜 
(E₁ i)] →               [inst_3 : SeminormedAddCommGroup G] →                 [i
nst_4 : NormedSpace 𝕜 G] →                   [Fintype ι] →                     C
ontinuousMultilinearMap 𝕜 E₁ G → (k : ℕ) → ((i : ι) → E₁ i) → ((i : ι) → E₁ i) [
×k]→L[𝕜] G
参数：i : ι；E₁ i；i : ι；E₁ i；k : ℕ；(i : ι) → E₁ i；(i : ι) → E₁ i。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E

--- 原说明 ---
The `k`-th iterated derivative of a continuous multilinear map `f` at the point 
`x`. It is a
continuous multilinear map of `k` vectors `v₁, ..., vₖ` (with the same type as `
x`), mapping them
to `∑ f (x₁, (v_{i₁})₂, x₃, ...)`, where at each index `j` one uses either `xⱼ` 
or one
of the `(vᵢ)ⱼ`, and each `vᵢ` has to be used exactly once.
The sum is parameterized by the embeddings of `Fin k` in the index type `ι` (or,
 equivalently,
by the subsets `s` of `ι` of cardinality `k` and then the bijections between `Fi
n k` and `s`).

The fact that this is indeed the iterated Fréchet derivative is proved in
`ContinuousMultilinearMap.iteratedFDeriv_eq`.
-/
protected def iteratedFDeriv (f : ContinuousMultilinearMap 𝕜 E₁ G) (k : ℕ) (x : (i : ι) → E₁ i) :
    ContinuousMultilinearMap 𝕜 (fun (_ : Fin k) ↦ (∀ i, E₁ i)) G :=
  ∑ e : Fin k ↪ ι, iteratedFDerivComponent f e.toEquivRange (Pi.compRightL 𝕜 _ Subtype.val x)

/-- Controlling the norm of `f.iteratedFDeriv` when `f` is continuous multilinear. For the same
bound on the iterated derivative of `f` in the calculus sense,
see `ContinuousMultilinearMap.norm_iteratedFDeriv_le`. -/
/-
**ContinuousMultilinearMap.norm_iteratedFDeriv_le'** 是 Mathlib 中的一个引理，位于命名空间 `Co
ntinuousMultilinearMap`。
形式化陈述：norm_iteratedFDeriv_le' (f : ContinuousMultilinearMap 𝕜 E₁ G) (k : Nat) (x
 : (i : ι) -> E₁ i) : ‖f.iteratedFDeriv k x‖ <= Nat.descFactorial (Fintype.card 
ι) k * ‖f‖ * ‖x‖ ^ (Fintype.card ι - k)
参数：f : ContinuousMultilinearMap 𝕜 E₁ G；k : Nat；x : (i : ι) -> E₁ i。
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
· 使用定理 `norm_sum_le`：norm_sum_le {E} [SeminormedAddCommGroup E] (s : Finset ι) (
f : ι -> E) : ‖∑ i in s, f i‖ <= ∑ i in s, ‖f i‖
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用引理 `ContinuousMultilinearMap.norm_iteratedFDerivComponent_le`：norm_iteratedF
DerivComponent_le {α : Type*} [Fintype α] (f : ContinuousMultilinearMap 𝕜 E₁ G) 
{s : Set ι} (e : α ≃ s) [DecidablePred (· in s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fintype.card_embedding_eq`：card_embedding_eq {α β : Type*} [Fintype α] [
Fintype β] [emb : Fintype (α ↪ β)] : ‖α ↪ β‖ = ‖β‖.descFactorial ‖α‖
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Controlling the norm of `f.iteratedFDeriv` when `f` is continuous multilinear. F
or the same
bound on the iterated derivative of `f` in the calculus sense,
see `ContinuousMultilinearMap.norm_iteratedFDeriv_le`.
-/
lemma norm_iteratedFDeriv_le' (f : ContinuousMultilinearMap 𝕜 E₁ G) (k : ℕ) (x : (i : ι) → E₁ i) :
    ‖f.iteratedFDeriv k x‖
      ≤ Nat.descFactorial (Fintype.card ι) k * ‖f‖ * ‖x‖ ^ (Fintype.card ι - k) := by
  classical
  calc ‖f.iteratedFDeriv k x‖
  _ ≤ ∑ e : Fin k ↪ ι, ‖iteratedFDerivComponent f e.toEquivRange (fun i ↦ x i)‖ := norm_sum_le _ _
  _ ≤ ∑ _ : Fin k ↪ ι, ‖f‖ * ‖x‖ ^ (Fintype.card ι - k) := by
    gcongr with e _
    simpa using norm_iteratedFDerivComponent_le f e.toEquivRange x
  _ = Nat.descFactorial (Fintype.card ι) k * ‖f‖ * ‖x‖ ^ (Fintype.card ι - k) := by
    simp [card_univ, mul_assoc]

end ContinuousMultilinearMap

end Seminorm

section Norm

namespace ContinuousMultilinearMap

/-! Results that are only true if the target space is a `NormedAddCommGroup` (and not just a
`SeminormedAddCommGroup`). -/

variable {𝕜 : Type u} {ι : Type v} {E : ι → Type wE} {G : Type wG} {G' : Type wG'} [Fintype ι]
  [NontriviallyNormedField 𝕜] [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [SeminormedAddCommGroup G'] [NormedSpace 𝕜 G']

/-- A continuous linear map is zero iff its norm vanishes. -/
/-
**ContinuousMultilinearMap.opNorm_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
MultilinearMap`。
形式化陈述：opNorm_zero_iff {f : ContinuousMultilinearMap 𝕜 E G} : ‖f‖ = 0 ↔ f = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.ge_iff_eq'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (a ≤ b ↔ a = b)
· 使用定理 `ContinuousMultilinearMap.opNorm_nonneg`：opNorm_nonneg (f : ContinuousMul
tilinearMap 𝕜 E G) : 0 <= ‖f‖
· 使用定理 `ContinuousMultilinearMap.opNorm_le_iff`：opNorm_le_iff {f : ContinuousMul
tilinearMap 𝕜 E G} {C : Real} (hC : 0 <= C) : ‖f‖ <= C ↔ forall m, ‖f m‖ <= C * 
∏ i, ‖m i‖
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousMultilinearMap.instIsZeroApplyForall`：∀ {R : Type u} {ι : Type
 v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → 
AddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A continuous linear map is zero iff its norm vanishes.
-/
theorem opNorm_zero_iff {f : ContinuousMultilinearMap 𝕜 E G} : ‖f‖ = 0 ↔ f = 0 := by
  simp [← (opNorm_nonneg f).ge_iff_eq', opNorm_le_iff le_rfl, ContinuousMultilinearMap.ext_iff]

/-- Continuous multilinear maps themselves form a normed group with respect to
the operator norm. -/
/-
**ContinuousMultilinearMap.normedAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `Continu
ousMultilinearMap`。
形式化陈述：normedAddCommGroup : NormedAddCommGroup (ContinuousMultilinearMap 𝕜 E G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Continuous multilinear maps themselves form a normed group with respect to
the operator norm.
-/
instance normedAddCommGroup : NormedAddCommGroup (ContinuousMultilinearMap 𝕜 E G) :=
  NormedAddCommGroup.ofSeparation fun _ ↦ opNorm_zero_iff.mp

/-- An alias of `ContinuousMultilinearMap.normedAddCommGroup` with non-dependent types to help
typeclass search. -/
/-
**ContinuousMultilinearMap.normedAddCommGroup'** 是 Mathlib 中的一个实例，位于命名空间 `Contin
uousMultilinearMap`。
形式化陈述：normedAddCommGroup' : NormedAddCommGroup (ContinuousMultilinearMap 𝕜 (fun 
_ : ι => G') G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An alias of `ContinuousMultilinearMap.normedAddCommGroup` with non-dependent typ
es to help
typeclass search.
-/
instance normedAddCommGroup' :
    NormedAddCommGroup (ContinuousMultilinearMap 𝕜 (fun _ : ι => G') G) :=
  ContinuousMultilinearMap.normedAddCommGroup

variable (𝕜 G)
/-
**ContinuousMultilinearMap.norm_ofSubsingleton_id** 是 Mathlib 中的一个定理，位于命名空间 `Con
tinuousMultilinearMap`。
形式化陈述：norm_ofSubsingleton_id [Subsingleton ι] [Nontrivial G] (i : ι) : ‖ofSubsin
gleton 𝕜 G G i (.id _ _)‖ = 1
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMultilinearMap.norm_ofSubsingleton`：norm_ofSubsingleton [Subsi
ngleton ι] (i : ι) (f : G ->L[𝕜] G') : ‖ofSubsingleton 𝕜 G G' i f‖ = ‖f‖
· 使用定理 `ContinuousLinearMap.norm_id`：norm_id [NontrivialTopology E] : ‖Continuou
sLinearMap.id 𝕜 E‖ = 1
· 使用定理 `EMetric.instNontrivialTopologyOfNontrivial`：∀ {α : Type u_2} [inst : EMe
tricSpace α] [Nontrivial α], NontrivialTopology α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_ofSubsingleton_id [Subsingleton ι] [Nontrivial G] (i : ι) :
    ‖ofSubsingleton 𝕜 G G i (.id _ _)‖ = 1 := by
  simp [ContinuousLinearMap.norm_id]
/-
**ContinuousMultilinearMap.nnnorm_ofSubsingleton_id** 是 Mathlib 中的一个定理，位于命名空间 `C
ontinuousMultilinearMap`。
形式化陈述：nnnorm_ofSubsingleton_id [Subsingleton ι] [Nontrivial G] (i : ι) : ‖ofSubs
ingleton 𝕜 G G i (.id _ _)‖₊ = 1
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `ContinuousMultilinearMap.norm_ofSubsingleton_id`：norm_ofSubsingleton_id 
[Subsingleton ι] [Nontrivial G] (i : ι) : ‖ofSubsingleton 𝕜 G G i (.id _ _)‖ = 1
-/
theorem nnnorm_ofSubsingleton_id [Subsingleton ι] [Nontrivial G] (i : ι) :
    ‖ofSubsingleton 𝕜 G G i (.id _ _)‖₊ = 1 :=
  NNReal.eq <| norm_ofSubsingleton_id ..

end ContinuousMultilinearMap

end Norm

section Norm

/-! Results that are only true if the source is a `NormedAddCommGroup` (and not just a
`SeminormedAddCommGroup`). -/

variable {𝕜 : Type u} {ι : Type v} {E : ι → Type wE} {G : Type wG} [Fintype ι]
  [NontriviallyNormedField 𝕜] [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

namespace MultilinearMap

/-- If a multilinear map in finitely many variables on normed spaces satisfies the inequality
`‖f m‖ ≤ C * ∏ i, ‖m i‖` on a shell `ε i / ‖c i‖ < ‖m i‖ < ε i` for some positive numbers `ε i`
and elements `c i : 𝕜`, `1 < ‖c i‖`, then it satisfies this inequality for all `m`. -/
/-
**MultilinearMap.bound_of_shell** 是 Mathlib 中的一个定理，位于命名空间 `MultilinearMap`。
形式化陈述：bound_of_shell (f : MultilinearMap 𝕜 E G) {ε : ι -> Real} {C : Real} {c : 
ι -> 𝕜} (hε : forall i, 0 < ε i) (hc : forall i, 1 < ‖c i‖) (hf : forall m : for
all i, E i, (forall i, ε i / ‖c i‖ <= ‖m i‖) -> (forall i, ‖m i‖ < ε i) -> ‖f m‖
 <= C * ∏ i, ‖m i‖) (m : forall i, E i) : ‖f m‖ <= C * ∏ i, ‖m i‖
参数：f : MultilinearMap 𝕜 E G；hε : forall i, 0 < ε i；hc : forall i, 1 < ‖c i‖；hf :
 forall m : forall i, E i, (forall i, ε i / ‖c i‖ <= ‖m i‖) -> (forall i, ‖m i‖ 
< ε i) -> ‖f m‖ <= C * ∏ i, ‖m i‖；m : forall i, E i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.bound_of_shell_of_norm_map_coord_zero`：bound_of_shell_of_
norm_map_coord_zero (f : MultilinearMap 𝕜 E G) (hf₀ : forall {m i}, ‖m i‖ = 0 ->
 ‖f m‖ = 0) {ε : ι -> Real} {C : Real} (hε…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MultilinearMap.map_coord_zero`：map_coord_zero {m : forall i, M₁ i} (i : 
ι) (h : m i = 0) : f m = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `norm_eq_zero`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a‖ = 
0 ↔ a = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0

--- 原说明 ---
If a multilinear map in finitely many variables on normed spaces satisfies the i
nequality
`‖f m‖ ≤ C * ∏ i, ‖m i‖` on a shell `ε i / ‖c i‖ < ‖m i‖ < ε i` for some positiv
e numbers `ε i`
and elements `c i : 𝕜`, `1 < ‖c i‖`, then it satisfies this inequality for all `
m`.
-/
theorem bound_of_shell (f : MultilinearMap 𝕜 E G) {ε : ι → ℝ} {C : ℝ} {c : ι → 𝕜}
    (hε : ∀ i, 0 < ε i) (hc : ∀ i, 1 < ‖c i‖)
    (hf : ∀ m : ∀ i, E i, (∀ i, ε i / ‖c i‖ ≤ ‖m i‖) → (∀ i, ‖m i‖ < ε i) → ‖f m‖ ≤ C * ∏ i, ‖m i‖)
    (m : ∀ i, E i) : ‖f m‖ ≤ C * ∏ i, ‖m i‖ :=
  bound_of_shell_of_norm_map_coord_zero f
    (fun h ↦ by rw [map_coord_zero f _ (norm_eq_zero.1 h), norm_zero]) hε hc hf m

end MultilinearMap

end Norm

