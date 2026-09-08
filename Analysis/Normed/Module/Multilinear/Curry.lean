/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.LinearAlgebra.Multilinear.Curry
public import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Currying and uncurrying continuous multilinear maps

We associate to a continuous multilinear map in `n+1` variables (i.e., based on `Fin n.succ`) two
curried functions, named `f.curryLeft` (which is a continuous linear map on `E 0` taking values
in continuous multilinear maps in `n` variables) and `f.curryRight` (which is a continuous
multilinear map in `n` variables taking values in continuous linear maps on `E (last n)`).
The inverse operations are called `uncurryLeft` and `uncurryRight`.

We also register continuous linear equiv versions of these correspondences, in
`continuousMultilinearCurryLeftEquiv` and `continuousMultilinearCurryRightEquiv`.

## Main results

* `ContinuousMultilinearMap.curryLeft`, `ContinuousLinearMap.uncurryLeft` and
  `continuousMultilinearCurryLeftEquiv`
* `ContinuousMultilinearMap.curryRight`, `ContinuousMultilinearMap.uncurryRight` and
  `continuousMultilinearCurryRightEquiv`.
* `ContinuousMultilinearMap.curryMid`, `ContinuousLinearMap.uncurryMid` and
  `ContinuousMultilinearMap.curryMidEquiv`
-/

@[expose] public section

suppress_compilation

noncomputable section

open NNReal Finset Metric ContinuousMultilinearMap Fin Function

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


universe u v v' wE wE₁ wE' wEi wG wG'

variable {𝕜 : Type u} {ι : Type v} {ι' : Type v'} {n : ℕ} {E : ι → Type wE}
  {Ei : Fin n.succ → Type wEi} {G : Type wG} {G' : Type wG'} [Fintype ι]
  [Fintype ι'] [NontriviallyNormedField 𝕜] [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace 𝕜 (E i)] [∀ i, NormedAddCommGroup (Ei i)] [∀ i, NormedSpace 𝕜 (Ei i)]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup G'] [NormedSpace 𝕜 G']

/-
**ContinuousLinearMap.norm_map_removeNth_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.norm_map_removeNth_le {i : Fin (n + 1)} (f : Ei i ->L[
𝕜] ContinuousMultilinearMap 𝕜 (fun j => Ei (i.succAbove j)) G) (m : forall i, Ei
 i) : ‖f (m i) (i.removeNth m)‖ <= ‖f‖ * ∏ j, ‖m j‖
参数：n + 1；f : Ei i ->L[𝕜] ContinuousMultilinearMap 𝕜 (fun j => Ei (i.succAbove j)
) G；m : forall i, Ei i。
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.prod_univ_succAbove`：prod_univ_succAbove (f : Fin (n + 1) -> M) (x :
 Fin (n + 1)) : ∏ i, f i = f x * ∏ i : Fin n, f (x.succAbove i)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `ContinuousMultilinearMap.le_of_opNorm_le`：le_of_opNorm_le {f : Continuou
sMultilinearMap 𝕜 E G} {C : Real} (h : ‖f‖ <= C) (m : forall i, E i) : ‖f m‖ <= 
C * ∏ i, ‖m i‖
· 使用定理 `ContinuousLinearMap.le_opNorm`：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖
-/
theorem ContinuousLinearMap.norm_map_removeNth_le {i : Fin (n + 1)}
    (f : Ei i →L[𝕜] ContinuousMultilinearMap 𝕜 (fun j ↦ Ei (i.succAbove j)) G) (m : ∀ i, Ei i) :
    ‖f (m i) (i.removeNth m)‖ ≤ ‖f‖ * ∏ j, ‖m j‖ := by
  rw [i.prod_univ_succAbove, ← mul_assoc]
  exact (f (m i)).le_of_opNorm_le (f.le_opNorm _) _
/-
**ContinuousLinearMap.norm_map_tail_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.norm_map_tail_le (f : Ei 0 ->L[𝕜] ContinuousMultilinea
rMap 𝕜 (fun i : Fin n => Ei i.succ) G) (m : forall i, Ei i) : ‖f (m 0) (tail m)‖
 <= ‖f‖ * ∏ i, ‖m i‖
参数：f : Ei 0 ->L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G；m :
 forall i, Ei i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
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
· 使用定理 `ContinuousLinearMap.norm_map_removeNth_le`：ContinuousLinearMap.norm_map_
removeNth_le {i : Fin (n + 1)} (f : Ei i ->L[𝕜] ContinuousMultilinearMap 𝕜 (fun 
j => Ei (i.succAbove j)) G) (m …
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
-/
theorem ContinuousLinearMap.norm_map_tail_le
    (f : Ei 0 →L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G) (m : ∀ i, Ei i) :
    ‖f (m 0) (tail m)‖ ≤ ‖f‖ * ∏ i, ‖m i‖ :=
  ContinuousLinearMap.norm_map_removeNth_le (i := 0) f m
/-
**ContinuousMultilinearMap.norm_map_init_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMultilinearMap.norm_map_init_le (f : ContinuousMultilinearMap 𝕜 
(fun i : Fin n => Ei <| castSucc i) (Ei (last n) ->L[𝕜] G)) (m : forall i, Ei i)
 : ‖f (init m) (m (last n))‖ <= ‖f‖ * ∏ i, ‖m i‖
参数：f : ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last 
n) ->L[𝕜] G)；m : forall i, Ei i。
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.prod_univ_castSucc`：prod_univ_castSucc (f : Fin (n + 1) -> M) : ∏ i,
 f i = (∏ i : Fin n, f (Fin.castSucc i)) * f (last n)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `ContinuousLinearMap.le_of_opNorm_le`：le_of_opNorm_le {c : Real} (h : ‖f‖
 <= c) (x : E) : ‖f x‖ <= c * ‖x‖
· 使用定理 `ContinuousMultilinearMap.le_opNorm`：le_opNorm (f : ContinuousMultilinear
Map 𝕜 E G) (m : forall i, E i) : ‖f m‖ <= ‖f‖ * ∏ i, ‖m i‖
-/
theorem ContinuousMultilinearMap.norm_map_init_le
    (f : ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) →L[𝕜] G))
    (m : ∀ i, Ei i) : ‖f (init m) (m (last n))‖ ≤ ‖f‖ * ∏ i, ‖m i‖ := by
  rw [prod_univ_castSucc, ← mul_assoc]
  exact (f (init m)).le_of_opNorm_le (f.le_opNorm _) _
/-
**ContinuousMultilinearMap.norm_map_insertNth_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMultilinearMap.norm_map_insertNth_le (f : ContinuousMultilinearM
ap 𝕜 Ei G) {i : Fin (n + 1)} (x : Ei i) (m : forall j, Ei (i.succAbove j)) : ‖f 
(i.insertNth x m)‖ <= ‖f‖ * ‖x‖ * ∏ i, ‖m i‖
参数：f : ContinuousMultilinearMap 𝕜 Ei G；n + 1；x : Ei i；m : forall j, Ei (i.succAb
ove j)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fin.prod_univ_succAbove`：prod_univ_succAbove (f : Fin (n + 1) -> M) (x :
 Fin (n + 1)) : ∏ i, f i = f x * ∏ i : Fin n, f (x.succAbove i)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fin.insertNth_apply_same`：insertNth_apply_same (i : Fin (n + 1)) (x : α 
i) (p : forall j, α (i.succAbove j)) : insertNth i x p i = x
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Fin.insertNth_apply_succAbove`：insertNth_apply_succAbove (i : Fin (n + 1
)) (x : α i) (p : forall j, α (i.succAbove j)) (j : Fin n) : insertNth i x p (i.
succAbove j) = p j
· 使用定理 `ContinuousMultilinearMap.le_opNorm`：le_opNorm (f : ContinuousMultilinear
Map 𝕜 E G) (m : forall i, E i) : ‖f m‖ <= ‖f‖ * ∏ i, ‖m i‖
-/
theorem ContinuousMultilinearMap.norm_map_insertNth_le (f : ContinuousMultilinearMap 𝕜 Ei G)
    {i : Fin (n + 1)} (x : Ei i) (m : ∀ j, Ei (i.succAbove j)) :
    ‖f (i.insertNth x m)‖ ≤ ‖f‖ * ‖x‖ * ∏ i, ‖m i‖ := by
  simpa [i.prod_univ_succAbove, mul_assoc] using f.le_opNorm (i.insertNth x m)
/-
**ContinuousMultilinearMap.norm_map_cons_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMultilinearMap.norm_map_cons_le (f : ContinuousMultilinearMap 𝕜 
Ei G) (x : Ei 0) (m : forall i : Fin n, Ei i.succ) : ‖f (cons x m)‖ <= ‖f‖ * ‖x‖
 * ∏ i, ‖m i‖
参数：f : ContinuousMultilinearMap 𝕜 Ei G；x : Ei 0；m : forall i : Fin n, Ei i.succ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fin.prod_univ_succ`：prod_univ_succ (f : Fin (n + 1) -> M) : ∏ i, f i = f
 0 * ∏ i : Fin n, f i.succ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i
· 使用定理 `ContinuousMultilinearMap.le_opNorm`：le_opNorm (f : ContinuousMultilinear
Map 𝕜 E G) (m : forall i, E i) : ‖f m‖ <= ‖f‖ * ∏ i, ‖m i‖
-/
theorem ContinuousMultilinearMap.norm_map_cons_le (f : ContinuousMultilinearMap 𝕜 Ei G) (x : Ei 0)
    (m : ∀ i : Fin n, Ei i.succ) : ‖f (cons x m)‖ ≤ ‖f‖ * ‖x‖ * ∏ i, ‖m i‖ := by
  simpa [prod_univ_succ, mul_assoc] using f.le_opNorm (cons x m)
/-
**ContinuousMultilinearMap.norm_map_snoc_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMultilinearMap.norm_map_snoc_le (f : ContinuousMultilinearMap 𝕜 
Ei G) (m : forall i : Fin n, Ei <| castSucc i) (x : Ei (last n)) : ‖f (snoc m x)
‖ <= (‖f‖ * ∏ i, ‖m i‖) * ‖x‖
参数：f : ContinuousMultilinearMap 𝕜 Ei G；m : forall i : Fin n, Ei <| castSucc i；x 
: Ei (last n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fin.prod_univ_castSucc`：prod_univ_castSucc (f : Fin (n + 1) -> M) : ∏ i,
 f i = (∏ i : Fin n, f (Fin.castSucc i)) * f (last n)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Fin.snoc_castSucc`：snoc_castSucc : snoc p x i.castSucc = p i
· 使用定理 `Fin.snoc_last`：snoc_last : snoc p x (last n) = x
· 使用定理 `ContinuousMultilinearMap.le_opNorm`：le_opNorm (f : ContinuousMultilinear
Map 𝕜 E G) (m : forall i, E i) : ‖f m‖ <= ‖f‖ * ∏ i, ‖m i‖
-/
theorem ContinuousMultilinearMap.norm_map_snoc_le (f : ContinuousMultilinearMap 𝕜 Ei G)
    (m : ∀ i : Fin n, Ei <| castSucc i) (x : Ei (last n)) :
    ‖f (snoc m x)‖ ≤ (‖f‖ * ∏ i, ‖m i‖) * ‖x‖ := by
  simpa [prod_univ_castSucc, mul_assoc] using f.le_opNorm (snoc m x)

/-! #### Left currying -/


/-- Given a continuous linear map `f` from `E 0` to continuous multilinear maps on `n` variables,
construct the corresponding continuous multilinear map on `n+1` variables obtained by concatenating
the variables, given by `m ↦ f (m 0) (tail m)` -/
/-
**ContinuousLinearMap.uncurryLeft** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.uncurryLeft (f : Ei 0 ->L[𝕜] ContinuousMultilinearMap 
𝕜 (fun i : Fin n => Ei i.succ) G) : ContinuousMultilinearMap 𝕜 Ei G
参数：f : Ei 0 ->L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)

--- 原说明 ---
Given a continuous linear map `f` from `E 0` to continuous multilinear maps on `
n` variables,
construct the corresponding continuous multilinear map on `n+1` variables obtain
ed by concatenating
the variables, given by `m ↦ f (m 0) (tail m)`
-/
def ContinuousLinearMap.uncurryLeft
    (f : Ei 0 →L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G) :
    ContinuousMultilinearMap 𝕜 Ei G :=
  (ContinuousMultilinearMap.toMultilinearMapLinear ∘ₗ f.toLinearMap).uncurryLeft.mkContinuous
    ‖f‖ fun m => by exact ContinuousLinearMap.norm_map_tail_le f m

@[simp]
/-
**ContinuousLinearMap.uncurryLeft_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.uncurryLeft_apply (f : Ei 0 ->L[𝕜] ContinuousMultiline
arMap 𝕜 (fun i : Fin n => Ei i.succ) G) (m : forall i, Ei i) : f.uncurryLeft m =
 f (m 0) (tail m)
参数：f : Ei 0 ->L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G；m :
 forall i, Ei i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
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
theorem ContinuousLinearMap.uncurryLeft_apply
    (f : Ei 0 →L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G) (m : ∀ i, Ei i) :
    f.uncurryLeft m = f (m 0) (tail m) :=
  rfl

/-- Given a continuous multilinear map `f` in `n+1` variables, split the first variable to obtain
a continuous linear map into continuous multilinear maps in `n` variables, given by
`x ↦ (m ↦ f (cons x m))`. -/
/-
**ContinuousMultilinearMap.curryLeft** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ContinuousMultilinearMap.curryLeft (f : ContinuousMultilinearMap 𝕜 Ei G) :
 Ei 0 ->L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G
参数：f : ContinuousMultilinearMap 𝕜 Ei G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ContinuousMultilinearMap.norm_map_cons_le`：ContinuousMultilinearMap.norm
_map_cons_le (f : ContinuousMultilinearMap 𝕜 Ei G) (x : Ei 0) (m : forall i : Fi
n n, Ei i.succ) : ‖f (cons x m)…

--- 原说明 ---
Given a continuous multilinear map `f` in `n+1` variables, split the first varia
ble to obtain
a continuous linear map into continuous multilinear maps in `n` variables, given
 by
`x ↦ (m ↦ f (cons x m))`.
-/
def ContinuousMultilinearMap.curryLeft (f : ContinuousMultilinearMap 𝕜 Ei G) :
    Ei 0 →L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G :=
  MultilinearMap.mkContinuousLinear f.toMultilinearMap.curryLeft ‖f‖ f.norm_map_cons_le

@[simp]
/-
**ContinuousMultilinearMap.curryLeft_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMultilinearMap.curryLeft_apply (f : ContinuousMultilinearMap 𝕜 E
i G) (x : Ei 0) (m : forall i : Fin n, Ei i.succ) : f.curryLeft x m = f (cons x 
m)
参数：f : ContinuousMultilinearMap 𝕜 Ei G；x : Ei 0；m : forall i : Fin n, Ei i.succ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
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
theorem ContinuousMultilinearMap.curryLeft_apply (f : ContinuousMultilinearMap 𝕜 Ei G) (x : Ei 0)
    (m : ∀ i : Fin n, Ei i.succ) : f.curryLeft x m = f (cons x m) :=
  rfl

@[simp]
/-
**ContinuousLinearMap.curry_uncurryLeft** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.curry_uncurryLeft (f : Ei 0 ->L[𝕜] ContinuousMultiline
arMap 𝕜 (fun i : Fin n => Ei i.succ) G) : f.uncurryLeft.curryLeft = f
参数：f : Ei 0 ->L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
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
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMultilinearMap.curryLeft_apply`：ContinuousMultilinearMap.curry
Left_apply (f : ContinuousMultilinearMap 𝕜 Ei G) (x : Ei 0) (m : forall i : Fin 
n, Ei i.succ) : f.curryLeft x …
· 使用定理 `ContinuousLinearMap.uncurryLeft_apply`：ContinuousLinearMap.uncurryLeft_a
pply (f : Ei 0 ->L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G)
 (m : forall i, Ei i) : f.u…
· 使用定理 `Fin.tail_cons`：tail_cons : tail (cons x p) = p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
-/
theorem ContinuousLinearMap.curry_uncurryLeft
    (f : Ei 0 →L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G) :
    f.uncurryLeft.curryLeft = f := by
  ext m x
  rw [ContinuousMultilinearMap.curryLeft_apply, ContinuousLinearMap.uncurryLeft_apply, tail_cons,
    cons_zero]

@[simp]
/-
**ContinuousMultilinearMap.uncurry_curryLeft** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMultilinearMap.uncurry_curryLeft (f : ContinuousMultilinearMap 𝕜
 Ei G) : f.curryLeft.uncurryLeft = f
参数：f : ContinuousMultilinearMap 𝕜 Ei G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.toMultilinearMap_injective`：∀ {R : Type u} {ι :
 Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : 
ι) → AddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `MultilinearMap.uncurry_curryLeft`：MultilinearMap.uncurry_curryLeft (f : 
MultilinearMap R M M₂) : f.curryLeft.uncurryLeft = f
-/
theorem ContinuousMultilinearMap.uncurry_curryLeft (f : ContinuousMultilinearMap 𝕜 Ei G) :
    f.curryLeft.uncurryLeft = f :=
  ContinuousMultilinearMap.toMultilinearMap_injective <| f.toMultilinearMap.uncurry_curryLeft

variable (𝕜 Ei G)

set_option backward.isDefEq.respectTransparency false in
/-- The space of continuous multilinear maps on `Π(i : Fin (n+1)), E i` is canonically isomorphic to
the space of continuous linear maps from `E 0` to the space of continuous multilinear maps on
`Π(i : Fin n), E i.succ`, by separating the first variable. We register this isomorphism in
`continuousMultilinearCurryLeftEquiv 𝕜 E E₂`. The algebraic version (without topology) is given
in `multilinearCurryLeftEquiv 𝕜 E E₂`.

The direct and inverse maps are given by `f.curryLeft` and `f.uncurryLeft`. Use these
unless you need the full framework of linear isometric equivs. -/
/-
**continuousMultilinearCurryLeftEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：continuousMultilinearCurryLeftEquiv : ContinuousMultilinearMap 𝕜 Ei G ≃ₗᵢ[
𝕜] Ei 0 ->L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ContinuousMultilinearMap.uncurry_curryLeft`：ContinuousMultilinearMap.unc
urry_curryLeft (f : ContinuousMultilinearMap 𝕜 Ei G) : f.curryLeft.uncurryLeft =
 f
· 使用定理 `ContinuousLinearMap.curry_uncurryLeft`：ContinuousLinearMap.curry_uncurry
Left (f : Ei 0 ->L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G)
 : f.uncurryLeft.curryLeft …

--- 原说明 ---
The space of continuous multilinear maps on `Π(i : Fin (n+1)), E i` is canonical
ly isomorphic to
the space of continuous linear maps from `E 0` to the space of continuous multil
inear maps on
`Π(i : Fin n), E i.succ`, by separating the first variable. We register this iso
morphism in
`continuousMultilinearCurryLeftEquiv 𝕜 E E₂`. The algebraic version (without top
ology) is given
in `multilinearCurryLeftEquiv 𝕜 E E₂`.

The direct and inverse maps are given by `f.curryLeft` and `f.uncurryLeft`. Use 
these
unless you need the full framework of linear isometric equivs.
-/
def continuousMultilinearCurryLeftEquiv :
    ContinuousMultilinearMap 𝕜 Ei G ≃ₗᵢ[𝕜]
      Ei 0 →L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G :=
  LinearIsometryEquiv.ofBounds
    { toFun := ContinuousMultilinearMap.curryLeft
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := ContinuousLinearMap.uncurryLeft
      left_inv := ContinuousMultilinearMap.uncurry_curryLeft
      right_inv := ContinuousLinearMap.curry_uncurryLeft }
    (fun f => by dsimp; exact MultilinearMap.mkContinuousLinear_norm_le _ (norm_nonneg f) _)
    (fun f => by
      simp only [LinearEquiv.coe_symm_mk]
      exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg f) _)

variable {𝕜 Ei G}

@[simp]
/-
**continuousMultilinearCurryLeftEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousMultilinearCurryLeftEquiv_apply (f : ContinuousMultilinearMap 𝕜 
Ei G) (x : Ei 0) (v : Π i : Fin n, Ei i.succ) : continuousMultilinearCurryLeftEq
uiv 𝕜 Ei G f x v = f (cons x v)
参数：f : ContinuousMultilinearMap 𝕜 Ei G；x : Ei 0；v : Π i : Fin n, Ei i.succ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
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
theorem continuousMultilinearCurryLeftEquiv_apply
    (f : ContinuousMultilinearMap 𝕜 Ei G) (x : Ei 0) (v : Π i : Fin n, Ei i.succ) :
    continuousMultilinearCurryLeftEquiv 𝕜 Ei G f x v = f (cons x v) :=
  rfl

@[simp]
/-
**continuousMultilinearCurryLeftEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousMultilinearCurryLeftEquiv_symm_apply (f : Ei 0 ->L[𝕜] Continuous
MultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G) (v : Π i, Ei i) : (continuousMu
ltilinearCurryLeftEquiv 𝕜 Ei G).symm f v = f (v 0) (tail v)
参数：f : Ei 0 ->L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G；v :
 Π i, Ei i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
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
theorem continuousMultilinearCurryLeftEquiv_symm_apply
    (f : Ei 0 →L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G) (v : Π i, Ei i) :
    (continuousMultilinearCurryLeftEquiv 𝕜 Ei G).symm f v = f (v 0) (tail v) :=
  rfl

@[simp]
/-
**ContinuousMultilinearMap.curryLeft_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMultilinearMap.curryLeft_norm (f : ContinuousMultilinearMap 𝕜 Ei
 G) : ‖f.curryLeft‖ = ‖f‖
参数：f : ContinuousMultilinearMap 𝕜 Ei G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.norm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type
 u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* 
R₂} {σ₂₁ : R₂ →+* …
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
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
theorem ContinuousMultilinearMap.curryLeft_norm (f : ContinuousMultilinearMap 𝕜 Ei G) :
    ‖f.curryLeft‖ = ‖f‖ :=
  (continuousMultilinearCurryLeftEquiv 𝕜 Ei G).norm_map f

@[simp]
/-
**ContinuousLinearMap.uncurryLeft_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.uncurryLeft_norm (f : Ei 0 ->L[𝕜] ContinuousMultilinea
rMap 𝕜 (fun i : Fin n => Ei i.succ) G) : ‖f.uncurryLeft‖ = ‖f‖
参数：f : Ei 0 ->L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
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
· 使用定理 `LinearIsometryEquiv.norm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type
 u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* 
R₂} {σ₂₁ : R₂ →+* …
· 使用定理 `ContinuousMultilinearMap.instSMulCommClass`：∀ {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCommMo
noid M₂]   [inst_2 : (i : ι) → T…
-/
theorem ContinuousLinearMap.uncurryLeft_norm
    (f : Ei 0 →L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G) :
    ‖f.uncurryLeft‖ = ‖f‖ :=
  (continuousMultilinearCurryLeftEquiv 𝕜 Ei G).symm.norm_map f

/-! #### Right currying -/


/-- Given a continuous linear map `f` from continuous multilinear maps on `n` variables to
continuous linear maps on `E 0`, construct the corresponding continuous multilinear map on `n+1`
variables obtained by concatenating the variables, given by `m ↦ f (init m) (m (last n))`. -/
/-
**ContinuousMultilinearMap.uncurryRight** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ContinuousMultilinearMap.uncurryRight (f : ContinuousMultilinearMap 𝕜 (fun
 i : Fin n => Ei <| castSucc i) (Ei (last n) ->L[𝕜] G)) : ContinuousMultilinearM
ap 𝕜 Ei G
参数：f : ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last 
n) ->L[𝕜] G)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.norm_map_init_le`：ContinuousMultilinearMap.norm
_map_init_le (f : ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i)
 (Ei (last n) ->L[𝕜] G)) (m : f…

--- 原说明 ---
Given a continuous linear map `f` from continuous multilinear maps on `n` variab
les to
continuous linear maps on `E 0`, construct the corresponding continuous multilin
ear map on `n+1`
variables obtained by concatenating the variables, given by `m ↦ f (init m) (m (
last n))`.
-/
def ContinuousMultilinearMap.uncurryRight
    (f : ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) →L[𝕜] G)) :
    ContinuousMultilinearMap 𝕜 Ei G :=
  let f' : MultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) →ₗ[𝕜] G) :=
    (ContinuousLinearMap.coeLM 𝕜).compMultilinearMap f.toMultilinearMap
  f'.uncurryRight.mkContinuous ‖f‖ fun m => f.norm_map_init_le m

@[simp]
/-
**ContinuousMultilinearMap.uncurryRight_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMultilinearMap.uncurryRight_apply (f : ContinuousMultilinearMap 
𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) ->L[𝕜] G)) (m : forall i, Ei 
i) : f.uncurryRight m = f (init m) (m (last n))
参数：f : ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last 
n) ->L[𝕜] G)；m : forall i, Ei i。
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
theorem ContinuousMultilinearMap.uncurryRight_apply
    (f : ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) →L[𝕜] G))
    (m : ∀ i, Ei i) : f.uncurryRight m = f (init m) (m (last n)) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Given a continuous multilinear map `f` in `n+1` variables, split the last variable to obtain
a continuous multilinear map in `n` variables into continuous linear maps, given by
`m ↦ (x ↦ f (snoc m x))`. -/
/-
**ContinuousMultilinearMap.curryRight** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ContinuousMultilinearMap.curryRight (f : ContinuousMultilinearMap 𝕜 Ei G) 
: ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) ->
L[𝕜] G)
参数：f : ContinuousMultilinearMap 𝕜 Ei G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.norm_map_snoc_le`：ContinuousMultilinearMap.norm
_map_snoc_le (f : ContinuousMultilinearMap 𝕜 Ei G) (m : forall i : Fin n, Ei <| 
castSucc i) (x : Ei (last n)) :…

--- 原说明 ---
Given a continuous multilinear map `f` in `n+1` variables, split the last variab
le to obtain
a continuous multilinear map in `n` variables into continuous linear maps, given
 by
`m ↦ (x ↦ f (snoc m x))`.
-/
def ContinuousMultilinearMap.curryRight (f : ContinuousMultilinearMap 𝕜 Ei G) :
    ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) →L[𝕜] G) :=
  let f' : MultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) →L[𝕜] G) :=
    { toFun := fun m =>
        (f.toMultilinearMap.curryRight m).mkContinuous (‖f‖ * ∏ i, ‖m i‖) fun x =>
          f.norm_map_snoc_le m x
      map_update_add' := fun m i x y => by
        ext
        simp
      map_update_smul' := fun m i c x => by
        ext
        simp }
  f'.mkContinuous ‖f‖ fun m => by
    simp only [f', MultilinearMap.coe_mk]
    exact LinearMap.mkContinuous_norm_le _ (by positivity) _

@[simp]
/-
**ContinuousMultilinearMap.curryRight_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMultilinearMap.curryRight_apply (f : ContinuousMultilinearMap 𝕜 
Ei G) (m : forall i : Fin n, Ei <| castSucc i) (x : Ei (last n)) : f.curryRight 
m x = f (snoc m x)
参数：f : ContinuousMultilinearMap 𝕜 Ei G；m : forall i : Fin n, Ei <| castSucc i；x 
: Ei (last n)。
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
theorem ContinuousMultilinearMap.curryRight_apply (f : ContinuousMultilinearMap 𝕜 Ei G)
    (m : ∀ i : Fin n, Ei <| castSucc i) (x : Ei (last n)) : f.curryRight m x = f (snoc m x) :=
  rfl

@[simp]
/-
**ContinuousMultilinearMap.curry_uncurryRight** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMultilinearMap.curry_uncurryRight (f : ContinuousMultilinearMap 
𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) ->L[𝕜] G)) : f.uncurryRight.c
urryRight = f
参数：f : ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last 
n) ->L[𝕜] G)。
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
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMultilinearMap.curryRight_apply`：ContinuousMultilinearMap.curr
yRight_apply (f : ContinuousMultilinearMap 𝕜 Ei G) (m : forall i : Fin n, Ei <| 
castSucc i) (x : Ei (last n)) :…
· 使用定理 `ContinuousMultilinearMap.uncurryRight_apply`：ContinuousMultilinearMap.un
curryRight_apply (f : ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSuc
c i) (Ei (last n) ->L[𝕜] G)) (m :…
· 使用定理 `Fin.snoc_last`：snoc_last : snoc p x (last n) = x
· 使用定理 `Fin.init_snoc`：init_snoc : init (snoc p x) = p
-/
theorem ContinuousMultilinearMap.curry_uncurryRight
    (f : ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) →L[𝕜] G)) :
    f.uncurryRight.curryRight = f := by
  ext m x
  rw [ContinuousMultilinearMap.curryRight_apply, ContinuousMultilinearMap.uncurryRight_apply,
    snoc_last, init_snoc]

@[simp]
/-
**ContinuousMultilinearMap.uncurry_curryRight** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMultilinearMap.uncurry_curryRight (f : ContinuousMultilinearMap 
𝕜 Ei G) : f.curryRight.uncurryRight = f
参数：f : ContinuousMultilinearMap 𝕜 Ei G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
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
· 使用定理 `ContinuousMultilinearMap.uncurryRight_apply`：ContinuousMultilinearMap.un
curryRight_apply (f : ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSuc
c i) (Ei (last n) ->L[𝕜] G)) (m :…
· 使用定理 `ContinuousMultilinearMap.curryRight_apply`：ContinuousMultilinearMap.curr
yRight_apply (f : ContinuousMultilinearMap 𝕜 Ei G) (m : forall i : Fin n, Ei <| 
castSucc i) (x : Ei (last n)) :…
· 使用定理 `Fin.snoc_init_self`：snoc_init_self : snoc (init q) (q (last n)) = q
-/
theorem ContinuousMultilinearMap.uncurry_curryRight (f : ContinuousMultilinearMap 𝕜 Ei G) :
    f.curryRight.uncurryRight = f := by
  ext m
  rw [uncurryRight_apply, curryRight_apply, snoc_init_self]

variable (𝕜 Ei G)

set_option backward.isDefEq.respectTransparency false in
/--
The space of continuous multilinear maps on `Π(i : Fin (n+1)), Ei i` is canonically isomorphic to
the space of continuous multilinear maps on `Π(i : Fin n), Ei <| castSucc i` with values in the
space of continuous linear maps on `Ei (last n)`, by separating the last variable. We register this
isomorphism as a continuous linear equiv in `continuousMultilinearCurryRightEquiv 𝕜 Ei G`.
The algebraic version (without topology) is given in `multilinearCurryRightEquiv 𝕜 Ei G`.

The direct and inverse maps are given by `f.curryRight` and `f.uncurryRight`. Use these
unless you need the full framework of linear isometric equivs.
-/
/-
**continuousMultilinearCurryRightEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：continuousMultilinearCurryRightEquiv : ContinuousMultilinearMap 𝕜 Ei G ≃ₗᵢ
[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) 
->L[𝕜] G)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.uncurry_curryRight`：ContinuousMultilinearMap.un
curry_curryRight (f : ContinuousMultilinearMap 𝕜 Ei G) : f.curryRight.uncurryRig
ht = f
· 使用定理 `ContinuousMultilinearMap.curry_uncurryRight`：ContinuousMultilinearMap.cu
rry_uncurryRight (f : ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSuc
c i) (Ei (last n) ->L[𝕜] G)) : f.…

--- 原说明 ---
The space of continuous multilinear maps on `Π(i : Fin (n+1)), Ei i` is canonica
lly isomorphic to
the space of continuous multilinear maps on `Π(i : Fin n), Ei <| castSucc i` wit
h values in the
space of continuous linear maps on `Ei (last n)`, by separating the last variabl
e. We register this
isomorphism as a continuous linear equiv in `continuousMultilinearCurryRightEqui
v 𝕜 Ei G`.
The algebraic version (without topology) is given in `multilinearCurryRightEquiv
 𝕜 Ei G`.

The direct and inverse maps are given by `f.curryRight` and `f.uncurryRight`. Us
e these
unless you need the full framework of linear isometric equivs.
-/
def continuousMultilinearCurryRightEquiv :
    ContinuousMultilinearMap 𝕜 Ei G ≃ₗᵢ[𝕜]
      ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) →L[𝕜] G) :=
  LinearIsometryEquiv.ofBounds
    { toFun := ContinuousMultilinearMap.curryRight
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := ContinuousMultilinearMap.uncurryRight
      left_inv := ContinuousMultilinearMap.uncurry_curryRight
      right_inv := ContinuousMultilinearMap.curry_uncurryRight }
    (fun f => by
      simp only [curryRight, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
      exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg f) _)
    (fun f => by
      simp only [uncurryRight, LinearEquiv.coe_symm_mk]
      exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg f) _)

variable (n G')

/-- The space of continuous multilinear maps on `Π(i : Fin (n+1)), G` is canonically isomorphic to
the space of continuous multilinear maps on `Π(i : Fin n), G` with values in the space
of continuous linear maps on `G`, by separating the last variable. We register this
isomorphism as a continuous linear equiv in `continuousMultilinearCurryRightEquiv' 𝕜 n G G'`.
For a version allowing dependent types, see `continuousMultilinearCurryRightEquiv`. When there
are no dependent types, use the primed version as it helps Lean a lot for unification.

The direct and inverse maps are given by `f.curryRight` and `f.uncurryRight`. Use these
unless you need the full framework of linear isometric equivs. -/
/-
**continuousMultilinearCurryRightEquiv'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：continuousMultilinearCurryRightEquiv' : (G [×n.succ]->L[𝕜] G') ≃ₗᵢ[𝕜] G [×
n]->L[𝕜] G ->L[𝕜] G'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The space of continuous multilinear maps on `Π(i : Fin (n+1)), G` is canonically
 isomorphic to
the space of continuous multilinear maps on `Π(i : Fin n), G` with values in the
 space
of continuous linear maps on `G`, by separating the last variable. We register t
his
isomorphism as a continuous linear equiv in `continuousMultilinearCurryRightEqui
v' 𝕜 n G G'`.
For a version allowing dependent types, see `continuousMultilinearCurryRightEqui
v`. When there
are no dependent types, use the primed version as it helps Lean a lot for unific
ation.

The direct and inverse maps are given by `f.curryRight` and `f.uncurryRight`. Us
e these
unless you need the full framework of linear isometric equivs.
-/
def continuousMultilinearCurryRightEquiv' : (G [×n.succ]→L[𝕜] G') ≃ₗᵢ[𝕜] G [×n]→L[𝕜] G →L[𝕜] G' :=
  continuousMultilinearCurryRightEquiv 𝕜 (fun _ => G) G'

variable {n 𝕜 G Ei G'}

@[simp]
/-
**continuousMultilinearCurryRightEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousMultilinearCurryRightEquiv_apply (f : ContinuousMultilinearMap 𝕜
 Ei G) (v : Π i : Fin n, Ei <| castSucc i) (x : Ei (last n)) : continuousMultili
nearCurryRightEquiv 𝕜 Ei G f v x = f (snoc v x)
参数：f : ContinuousMultilinearMap 𝕜 Ei G；v : Π i : Fin n, Ei <| castSucc i；x : Ei 
(last n)。
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
theorem continuousMultilinearCurryRightEquiv_apply
    (f : ContinuousMultilinearMap 𝕜 Ei G) (v : Π i : Fin n, Ei <| castSucc i) (x : Ei (last n)) :
    continuousMultilinearCurryRightEquiv 𝕜 Ei G f v x = f (snoc v x) :=
  rfl

@[simp]
/-
**continuousMultilinearCurryRightEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousMultilinearCurryRightEquiv_symm_apply (f : ContinuousMultilinear
Map 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) ->L[𝕜] G)) (v : Π i, Ei i
) : (continuousMultilinearCurryRightEquiv 𝕜 Ei G).symm f v = f (init v) (v (last
 n))
参数：f : ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last 
n) ->L[𝕜] G)；v : Π i, Ei i。
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
theorem continuousMultilinearCurryRightEquiv_symm_apply
    (f : ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) →L[𝕜] G))
    (v : Π i, Ei i) :
    (continuousMultilinearCurryRightEquiv 𝕜 Ei G).symm f v = f (init v) (v (last n)) :=
  rfl

@[simp]
/-
**continuousMultilinearCurryRightEquiv_apply'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousMultilinearCurryRightEquiv_apply' (f : G [×n.succ]->L[𝕜] G') (v 
: Fin n -> G) (x : G) : continuousMultilinearCurryRightEquiv' 𝕜 n G G' f v x = f
 (snoc v x)
参数：f : G [×n.succ]->L[𝕜] G'；v : Fin n -> G；x : G。
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
theorem continuousMultilinearCurryRightEquiv_apply'
    (f : G [×n.succ]→L[𝕜] G') (v : Fin n → G) (x : G) :
    continuousMultilinearCurryRightEquiv' 𝕜 n G G' f v x = f (snoc v x) :=
  rfl

@[simp]
/-
**continuousMultilinearCurryRightEquiv_symm_apply'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousMultilinearCurryRightEquiv_symm_apply' (f : G [×n]->L[𝕜] G ->L[𝕜
] G') (v : Fin (n + 1) -> G) : (continuousMultilinearCurryRightEquiv' 𝕜 n G G').
symm f v = f (init v) (v (last n))
参数：f : G [×n]->L[𝕜] G ->L[𝕜] G'；v : Fin (n + 1) -> G。
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
theorem continuousMultilinearCurryRightEquiv_symm_apply'
    (f : G [×n]→L[𝕜] G →L[𝕜] G') (v : Fin (n + 1) → G) :
    (continuousMultilinearCurryRightEquiv' 𝕜 n G G').symm f v = f (init v) (v (last n)) :=
  rfl

@[simp]
/-
**ContinuousMultilinearMap.curryRight_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMultilinearMap.curryRight_norm (f : ContinuousMultilinearMap 𝕜 E
i G) : ‖f.curryRight‖ = ‖f‖
参数：f : ContinuousMultilinearMap 𝕜 Ei G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.norm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type
 u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* 
R₂} {σ₂₁ : R₂ →+* …
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
theorem ContinuousMultilinearMap.curryRight_norm (f : ContinuousMultilinearMap 𝕜 Ei G) :
    ‖f.curryRight‖ = ‖f‖ :=
  (continuousMultilinearCurryRightEquiv 𝕜 Ei G).norm_map f

@[simp]
/-
**ContinuousMultilinearMap.uncurryRight_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMultilinearMap.uncurryRight_norm (f : ContinuousMultilinearMap 𝕜
 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) ->L[𝕜] G)) : ‖f.uncurryRight‖ 
= ‖f‖
参数：f : ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last 
n) ->L[𝕜] G)。
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
· 使用定理 `LinearIsometryEquiv.norm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type
 u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* 
R₂} {σ₂₁ : R₂ →+* …
-/
theorem ContinuousMultilinearMap.uncurryRight_norm
    (f : ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) →L[𝕜] G)) :
    ‖f.uncurryRight‖ = ‖f‖ :=
  (continuousMultilinearCurryRightEquiv 𝕜 Ei G).symm.norm_map f

/-!
### Currying a variable in the middle
-/

/-- Given a continuous linear map from `M p` to the space of continuous multilinear maps
in `n` variables `M 0`, ..., `M n` with `M p` removed,
returns a continuous multilinear map in all `n + 1` variables. -/
@[simps! apply]
/-
**ContinuousLinearMap.uncurryMid** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.uncurryMid (p : Fin (n + 1)) (f : Ei p ->L[𝕜] Continuo
usMultilinearMap 𝕜 (fun i => Ei (p.succAbove i)) G) : ContinuousMultilinearMap 𝕜
 Ei G
参数：p : Fin (n + 1)；f : Ei p ->L[𝕜] ContinuousMultilinearMap 𝕜 (fun i => Ei (p.su
ccAbove i)) G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a continuous linear map from `M p` to the space of continuous multilinear 
maps
in `n` variables `M 0`, ..., `M n` with `M p` removed,
returns a continuous multilinear map in all `n + 1` variables.
-/
def ContinuousLinearMap.uncurryMid (p : Fin (n + 1))
    (f : Ei p →L[𝕜] ContinuousMultilinearMap 𝕜 (fun i ↦ Ei (p.succAbove i)) G) :
    ContinuousMultilinearMap 𝕜 Ei G :=
  (ContinuousMultilinearMap.toMultilinearMapLinear ∘ₗ f.toLinearMap).uncurryMid p
    |>.mkContinuous ‖f‖ fun m => by exact ContinuousLinearMap.norm_map_removeNth_le f m

/-- Interpret a continuous multilinear map in `n + 1` variables
as a continuous linear map in `p`th variable
with values in the continuous multilinear maps in the other variables. -/
/-
**ContinuousMultilinearMap.curryMid** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ContinuousMultilinearMap.curryMid (p : Fin (n + 1)) (f : ContinuousMultili
nearMap 𝕜 Ei G) : Ei p ->L[𝕜] ContinuousMultilinearMap 𝕜 (fun i => Ei (p.succAbo
ve i)) G
参数：p : Fin (n + 1)；f : ContinuousMultilinearMap 𝕜 Ei G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.norm_map_insertNth_le`：ContinuousMultilinearMap
.norm_map_insertNth_le (f : ContinuousMultilinearMap 𝕜 Ei G) {i : Fin (n + 1)} (
x : Ei i) (m : forall j, Ei (i.succA…

--- 原说明 ---
Interpret a continuous multilinear map in `n + 1` variables
as a continuous linear map in `p`th variable
with values in the continuous multilinear maps in the other variables.
-/
def ContinuousMultilinearMap.curryMid (p : Fin (n + 1)) (f : ContinuousMultilinearMap 𝕜 Ei G) :
    Ei p →L[𝕜] ContinuousMultilinearMap 𝕜 (fun i ↦ Ei (p.succAbove i)) G :=
  MultilinearMap.mkContinuousLinear (f.toMultilinearMap.curryMid p) ‖f‖ f.norm_map_insertNth_le

@[simp]
/-
**ContinuousMultilinearMap.curryMid_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMultilinearMap.curryMid_apply (p : Fin (n + 1)) (f : ContinuousM
ultilinearMap 𝕜 Ei G) (x : Ei p) (m : forall i, Ei (p.succAbove i)) : f.curryMid
 p x m = f (p.insertNth x m)
参数：p : Fin (n + 1)；f : ContinuousMultilinearMap 𝕜 Ei G；x : Ei p；m : forall i, Ei
 (p.succAbove i)。
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
-/
theorem ContinuousMultilinearMap.curryMid_apply (p : Fin (n + 1))
    (f : ContinuousMultilinearMap 𝕜 Ei G) (x : Ei p) (m : ∀ i, Ei (p.succAbove i)) :
    f.curryMid p x m = f (p.insertNth x m) :=
  rfl

@[simp]
/-
**ContinuousLinearMap.curryMid_uncurryMid** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.curryMid_uncurryMid (p : Fin (n + 1)) (f : Ei p ->L[𝕜]
 ContinuousMultilinearMap 𝕜 (fun i => Ei (p.succAbove i)) G) : (f.uncurryMid p).
curryMid p = f
参数：p : Fin (n + 1)；f : Ei p ->L[𝕜] ContinuousMultilinearMap 𝕜 (fun i => Ei (p.su
ccAbove i)) G。
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
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.uncurryMid_apply`：∀ {𝕜 : Type u} {n : ℕ} {Ei : Fin n
.succ → Type wEi} {G : Type wG} [inst : NontriviallyNormedField 𝕜]   [inst_1 : (
i : Fin n.succ) → NormedAd…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fin.insertNth_apply_same`：insertNth_apply_same (i : Fin (n + 1)) (x : α 
i) (p : forall j, α (i.succAbove j)) : insertNth i x p i = x
· 使用定理 `Fin.removeNth_insertNth`：∀ {n : ℕ} {α : Fin (n + 1) → Sort u_1} (p : Fin
 (n + 1)) (a : α p) (f : (i : Fin n) → α (p.succAbove i)),   p.removeNth (p.inse
rtNth a f) = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ContinuousLinearMap.curryMid_uncurryMid (p : Fin (n + 1))
    (f : Ei p →L[𝕜] ContinuousMultilinearMap 𝕜 (fun i ↦ Ei (p.succAbove i)) G) :
    (f.uncurryMid p).curryMid p = f := by ext; simp

@[simp]
/-
**ContinuousMultilinearMap.uncurryMid_curryMid** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMultilinearMap.uncurryMid_curryMid (p : Fin (n + 1)) (f : Contin
uousMultilinearMap 𝕜 Ei G) : (f.curryMid p).uncurryMid p = f
参数：p : Fin (n + 1)；f : ContinuousMultilinearMap 𝕜 Ei G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.toMultilinearMap_injective`：∀ {R : Type u} {ι :
 Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : 
ι) → AddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `MultilinearMap.uncurryMid_curryMid`：MultilinearMap.uncurryMid_curryMid (
i : Fin (n + 1)) (f : MultilinearMap R M M₂) : (f.curryMid i).uncurryMid i = f
-/
theorem ContinuousMultilinearMap.uncurryMid_curryMid (p : Fin (n + 1))
    (f : ContinuousMultilinearMap 𝕜 Ei G) : (f.curryMid p).uncurryMid p = f :=
  ContinuousMultilinearMap.toMultilinearMap_injective <| f.toMultilinearMap.uncurryMid_curryMid p

variable (𝕜 Ei G)

set_option backward.isDefEq.respectTransparency false in
/-- `ContinuousMultilinearMap.curryMid` as a linear isometry equivalence. -/
@[simps! apply symm_apply]
/-
**ContinuousMultilinearMap.curryMidEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ContinuousMultilinearMap.curryMidEquiv (p : Fin (n + 1)) : ContinuousMulti
linearMap 𝕜 Ei G ≃ₗᵢ[𝕜] Ei p ->L[𝕜] ContinuousMultilinearMap 𝕜 (fun i => Ei (p.s
uccAbove i)) G
参数：p : Fin (n + 1)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.uncurryMid_curryMid`：ContinuousMultilinearMap.u
ncurryMid_curryMid (p : Fin (n + 1)) (f : ContinuousMultilinearMap 𝕜 Ei G) : (f.
curryMid p).uncurryMid p = f
· 使用定理 `ContinuousLinearMap.curryMid_uncurryMid`：ContinuousLinearMap.curryMid_un
curryMid (p : Fin (n + 1)) (f : Ei p ->L[𝕜] ContinuousMultilinearMap 𝕜 (fun i =>
 Ei (p.succAbove i)) G) : (f.…

--- 原说明 ---
`ContinuousMultilinearMap.curryMid` as a linear isometry equivalence.
-/
def ContinuousMultilinearMap.curryMidEquiv (p : Fin (n + 1)) :
    ContinuousMultilinearMap 𝕜 Ei G ≃ₗᵢ[𝕜]
      Ei p →L[𝕜] ContinuousMultilinearMap 𝕜 (fun i ↦ Ei (p.succAbove i)) G :=
  LinearIsometryEquiv.ofBounds
    { toFun := ContinuousMultilinearMap.curryMid p
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := ContinuousLinearMap.uncurryMid p
      left_inv := ContinuousMultilinearMap.uncurryMid_curryMid p
      right_inv := ContinuousLinearMap.curryMid_uncurryMid p }
    (fun f => by dsimp; exact MultilinearMap.mkContinuousLinear_norm_le _ (norm_nonneg f) _)
    (fun f => by
      simp only [LinearEquiv.coe_symm_mk]
      exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg f) _)

variable {𝕜 Ei G}

@[simp]
/-
**ContinuousMultilinearMap.norm_curryMid** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMultilinearMap.norm_curryMid (p : Fin (n + 1)) (f : ContinuousMu
ltilinearMap 𝕜 Ei G) : ‖f.curryMid p‖ = ‖f‖
参数：p : Fin (n + 1)；f : ContinuousMultilinearMap 𝕜 Ei G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.norm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type
 u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* 
R₂} {σ₂₁ : R₂ →+* …
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
theorem ContinuousMultilinearMap.norm_curryMid (p : Fin (n + 1))
    (f : ContinuousMultilinearMap 𝕜 Ei G) : ‖f.curryMid p‖ = ‖f‖ :=
  (ContinuousMultilinearMap.curryMidEquiv 𝕜 Ei G p).norm_map f

@[simp]
/-
**ContinuousLinearMap.norm_uncurryMid** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.norm_uncurryMid (p : Fin (n + 1)) (f : Ei p ->L[𝕜] Con
tinuousMultilinearMap 𝕜 (fun i => Ei (p.succAbove i)) G) : ‖f.uncurryMid p‖ = ‖f
‖
参数：p : Fin (n + 1)；f : Ei p ->L[𝕜] ContinuousMultilinearMap 𝕜 (fun i => Ei (p.su
ccAbove i)) G。
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
· 使用定理 `LinearIsometryEquiv.norm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type
 u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* 
R₂} {σ₂₁ : R₂ →+* …
· 使用定理 `ContinuousMultilinearMap.instSMulCommClass`：∀ {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCommMo
noid M₂]   [inst_2 : (i : ι) → T…
-/
theorem ContinuousLinearMap.norm_uncurryMid (p : Fin (n + 1))
    (f : Ei p →L[𝕜] ContinuousMultilinearMap 𝕜 (fun i ↦ Ei (p.succAbove i)) G) :
    ‖f.uncurryMid p‖ = ‖f‖ :=
  (ContinuousMultilinearMap.curryMidEquiv 𝕜 Ei G p).symm.norm_map f

/-!
#### Currying with `0` variables

The space of multilinear maps with `0` variables is trivial: such a multilinear map is just an
arbitrary constant (note that multilinear maps in `0` variables need not map `0` to `0`!).
Therefore, the space of continuous multilinear maps on `(Fin 0) → G` with values in `E₂` is
isomorphic (and even isometric) to `E₂`. As this is the zeroth step in the construction of iterated
derivatives, we register this isomorphism. -/


section

/-- Associating to a continuous multilinear map in `0` variables the unique value it takes. -/
/-
**ContinuousMultilinearMap.curry0** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ContinuousMultilinearMap.curry0 (f : ContinuousMultilinearMap 𝕜 (fun _ : F
in 0 => G) G') : G'
参数：f : ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => G) G'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Associating to a continuous multilinear map in `0` variables the unique value it
 takes.
-/
def ContinuousMultilinearMap.curry0 (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => G) G') :
    G' :=
  f 0

variable (𝕜 G) in
/-- Associating to an element `x` of a vector space `E₂` the continuous multilinear map in `0`
variables taking the (unique) value `x` -/
/-
**ContinuousMultilinearMap.uncurry0** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ContinuousMultilinearMap.uncurry0 (x : G') : G [×0]->L[𝕜] G'
参数：x : G'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Associating to an element `x` of a vector space `E₂` the continuous multilinear 
map in `0`
variables taking the (unique) value `x`
-/
def ContinuousMultilinearMap.uncurry0 (x : G') : G [×0]→L[𝕜] G' :=
  ContinuousMultilinearMap.constOfIsEmpty 𝕜 _ x

variable (𝕜) in
@[simp]
/-
**ContinuousMultilinearMap.uncurry0_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMultilinearMap.uncurry0_apply (x : G') (m : Fin 0 -> G) : Contin
uousMultilinearMap.uncurry0 𝕜 G x m = x
参数：x : G'；m : Fin 0 -> G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ContinuousMultilinearMap.uncurry0_apply (x : G') (m : Fin 0 → G) :
    ContinuousMultilinearMap.uncurry0 𝕜 G x m = x :=
  rfl

@[simp]
/-
**ContinuousMultilinearMap.curry0_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMultilinearMap.curry0_apply (f : G [×0]->L[𝕜] G') : f.curry0 = f
 0
参数：f : G [×0]->L[𝕜] G'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ContinuousMultilinearMap.curry0_apply (f : G [×0]→L[𝕜] G') : f.curry0 = f 0 :=
  rfl

@[simp]
/-
**ContinuousMultilinearMap.apply_zero_uncurry0** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMultilinearMap.apply_zero_uncurry0 (f : G [×0]->L[𝕜] G') {x : Fi
n 0 -> G} : ContinuousMultilinearMap.uncurry0 𝕜 G (f x) = f
参数：f : G [×0]->L[𝕜] G'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ContinuousMultilinearMap.apply_zero_uncurry0 (f : G [×0]→L[𝕜] G') {x : Fin 0 → G} :
    ContinuousMultilinearMap.uncurry0 𝕜 G (f x) = f := by
  ext m
  simp [Subsingleton.elim x m]
/-
**ContinuousMultilinearMap.uncurry0_curry0** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMultilinearMap.uncurry0_curry0 (f : G [×0]->L[𝕜] G') : Continuou
sMultilinearMap.uncurry0 𝕜 G f.curry0 = f
参数：f : G [×0]->L[𝕜] G'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.zero_empty`：∀ {α : Type u_1} [inst : Zero α], 0 = ![]
· 使用定理 `ContinuousMultilinearMap.apply_zero_uncurry0`：ContinuousMultilinearMap.a
pply_zero_uncurry0 (f : G [×0]->L[𝕜] G') {x : Fin 0 -> G} : ContinuousMultilinea
rMap.uncurry0 𝕜 G (f x) = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ContinuousMultilinearMap.uncurry0_curry0 (f : G [×0]→L[𝕜] G') :
    ContinuousMultilinearMap.uncurry0 𝕜 G f.curry0 = f := by simp

variable (𝕜 G) in
/-
**ContinuousMultilinearMap.curry0_uncurry0** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMultilinearMap.curry0_uncurry0 (x : G') : (ContinuousMultilinear
Map.uncurry0 𝕜 G x).curry0 = x
参数：x : G'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ContinuousMultilinearMap.curry0_uncurry0 (x : G') :
    (ContinuousMultilinearMap.uncurry0 𝕜 G x).curry0 = x :=
  rfl

variable (𝕜 G) in
@[simp]
/-
**ContinuousMultilinearMap.uncurry0_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMultilinearMap.uncurry0_norm (x : G') : ‖ContinuousMultilinearMa
p.uncurry0 𝕜 G x‖ = ‖x‖
参数：x : G'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.norm_constOfIsEmpty`：norm_constOfIsEmpty [IsEmp
ty ι] (x : G) : ‖constOfIsEmpty 𝕜 E x‖ = ‖x‖
-/
theorem ContinuousMultilinearMap.uncurry0_norm (x : G') :
    ‖ContinuousMultilinearMap.uncurry0 𝕜 G x‖ = ‖x‖ :=
  norm_constOfIsEmpty _ _ _

@[simp]
/-
**ContinuousMultilinearMap.fin0_apply_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMultilinearMap.fin0_apply_norm (f : G [×0]->L[𝕜] G') {x : Fin 0 
-> G} : ‖f x‖ = ‖f‖
参数：f : G [×0]->L[𝕜] G'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.zero_empty`：∀ {α : Type u_1} [inst : Zero α], 0 = ![]
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `ContinuousMultilinearMap.le_opNorm`：le_opNorm (f : ContinuousMultilinear
Map 𝕜 E G) (m : forall i, E i) : ‖f m‖ <= ‖f‖ * ∏ i, ‖m i‖
· 使用定理 `ContinuousMultilinearMap.opNorm_le_bound`：opNorm_le_bound {f : Continuou
sMultilinearMap 𝕜 E G} {M : Real} (hMp : 0 <= M) (hM : forall m, ‖f m‖ <= M * ∏ 
i, ‖m i‖) : ‖f‖ <= M
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ContinuousMultilinearMap.apply_zero_uncurry0`：ContinuousMultilinearMap.a
pply_zero_uncurry0 (f : G [×0]->L[𝕜] G') {x : Fin 0 -> G} : ContinuousMultilinea
rMap.uncurry0 𝕜 G (f x) = f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem ContinuousMultilinearMap.fin0_apply_norm (f : G [×0]→L[𝕜] G') {x : Fin 0 → G} :
    ‖f x‖ = ‖f‖ := by
  obtain rfl : x = 0 := Subsingleton.elim _ _
  refine le_antisymm (by simpa using f.le_opNorm 0) ?_
  have : ‖ContinuousMultilinearMap.uncurry0 𝕜 G f.curry0‖ ≤ ‖f.curry0‖ :=
    ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _) fun m => by
      simp [-ContinuousMultilinearMap.apply_zero_uncurry0]
  simpa [-Matrix.zero_empty] using this

@[simp]
/-
**ContinuousMultilinearMap.fin0_apply_enorm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMultilinearMap.fin0_apply_enorm (f : G [×0]->L[𝕜] G') {x : Fin 0
 -> G} : ‖f x‖ₑ = ‖f‖ₑ
参数：f : G [×0]->L[𝕜] G'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousMultilinearMap.fin0_apply_norm`：ContinuousMultilinearMap.fin0_
apply_norm (f : G [×0]->L[𝕜] G') {x : Fin 0 -> G} : ‖f x‖ = ‖f‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ContinuousMultilinearMap.fin0_apply_enorm (f : G [×0]→L[𝕜] G') {x : Fin 0 → G} :
    ‖f x‖ₑ = ‖f‖ₑ := by
  simp_rw [← ofReal_norm, fin0_apply_norm]
/-
**ContinuousMultilinearMap.curry0_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMultilinearMap.curry0_norm (f : G [×0]->L[𝕜] G') : ‖f.curry0‖ = 
‖f‖
参数：f : G [×0]->L[𝕜] G'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.zero_empty`：∀ {α : Type u_1} [inst : Zero α], 0 = ![]
· 使用定理 `ContinuousMultilinearMap.fin0_apply_norm`：ContinuousMultilinearMap.fin0_
apply_norm (f : G [×0]->L[𝕜] G') {x : Fin 0 -> G} : ‖f x‖ = ‖f‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ContinuousMultilinearMap.curry0_norm (f : G [×0]→L[𝕜] G') : ‖f.curry0‖ = ‖f‖ := by simp

variable (𝕜 G G')

/-- The continuous linear isomorphism between elements of a normed space, and continuous multilinear
maps in `0` variables with values in this normed space.

The direct and inverse maps are `uncurry0` and `curry0`. Use these unless you need the full
framework of linear isometric equivs. -/
/-
**continuousMultilinearCurryFin0** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：continuousMultilinearCurryFin0 : (G [×0]->L[𝕜] G') ≃ₗᵢ[𝕜] G' where toFun f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.uncurry0_curry0`：ContinuousMultilinearMap.uncur
ry0_curry0 (f : G [×0]->L[𝕜] G') : ContinuousMultilinearMap.uncurry0 𝕜 G f.curry
0 = f
· 使用定理 `ContinuousMultilinearMap.curry0_uncurry0`：ContinuousMultilinearMap.curry
0_uncurry0 (x : G') : (ContinuousMultilinearMap.uncurry0 𝕜 G x).curry0 = x
· 使用定理 `ContinuousMultilinearMap.curry0_norm`：ContinuousMultilinearMap.curry0_no
rm (f : G [×0]->L[𝕜] G') : ‖f.curry0‖ = ‖f‖

--- 原说明 ---
The continuous linear isomorphism between elements of a normed space, and contin
uous multilinear
maps in `0` variables with values in this normed space.

The direct and inverse maps are `uncurry0` and `curry0`. Use these unless you ne
ed the full
framework of linear isometric equivs.
-/
def continuousMultilinearCurryFin0 : (G [×0]→L[𝕜] G') ≃ₗᵢ[𝕜] G' where
  toFun f := ContinuousMultilinearMap.curry0 f
  invFun f := ContinuousMultilinearMap.uncurry0 𝕜 G f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv := ContinuousMultilinearMap.uncurry0_curry0
  right_inv := ContinuousMultilinearMap.curry0_uncurry0 𝕜 G
  norm_map' := ContinuousMultilinearMap.curry0_norm

variable {𝕜 G G'}

@[simp]
/-
**continuousMultilinearCurryFin0_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousMultilinearCurryFin0_apply (f : G [×0]->L[𝕜] G') : continuousMul
tilinearCurryFin0 𝕜 G G' f = f 0
参数：f : G [×0]->L[𝕜] G'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem continuousMultilinearCurryFin0_apply (f : G [×0]→L[𝕜] G') :
    continuousMultilinearCurryFin0 𝕜 G G' f = f 0 :=
  rfl

@[simp]
/-
**continuousMultilinearCurryFin0_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousMultilinearCurryFin0_symm_apply (x : G') : (continuousMultilinea
rCurryFin0 𝕜 G G').symm x = ContinuousMultilinearMap.uncurry0 𝕜 G x
参数：x : G'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem continuousMultilinearCurryFin0_symm_apply (x : G') :
    (continuousMultilinearCurryFin0 𝕜 G G').symm x = ContinuousMultilinearMap.uncurry0 𝕜 G x :=
  rfl
/-
**continuousMultilinearCurryFin0_symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousMultilinearCurryFin0_symm_apply_apply (x : G') (v : Fin 0 -> G) 
: (continuousMultilinearCurryFin0 𝕜 G G').symm x v = x
参数：x : G'；v : Fin 0 -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem continuousMultilinearCurryFin0_symm_apply_apply (x : G') (v : Fin 0 → G) :
    (continuousMultilinearCurryFin0 𝕜 G G').symm x v = x :=
  rfl

end

/-! #### With 1 variable -/


variable (𝕜 G G')

/-- Continuous multilinear maps from `G^1` to `G'` are isomorphic with continuous linear maps from
`G` to `G'`. -/
/-
**continuousMultilinearCurryFin1** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：continuousMultilinearCurryFin1 : (G [×1]->L[𝕜] G') ≃ₗᵢ[𝕜] G ->L[𝕜] G'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Continuous multilinear maps from `G^1` to `G'` are isomorphic with continuous li
near maps from
`G` to `G'`.
-/
def continuousMultilinearCurryFin1 : (G [×1]→L[𝕜] G') ≃ₗᵢ[𝕜] G →L[𝕜] G' :=
  (continuousMultilinearCurryRightEquiv 𝕜 (fun _ : Fin 1 => G) G').trans
    (continuousMultilinearCurryFin0 𝕜 G (G →L[𝕜] G'))

variable {𝕜 G G'}

@[simp]
/-
**continuousMultilinearCurryFin1_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousMultilinearCurryFin1_apply (f : G [×1]->L[𝕜] G') (x : G) : conti
nuousMultilinearCurryFin1 𝕜 G G' f x = f (Fin.snoc 0 x)
参数：f : G [×1]->L[𝕜] G'；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem continuousMultilinearCurryFin1_apply (f : G [×1]→L[𝕜] G') (x : G) :
    continuousMultilinearCurryFin1 𝕜 G G' f x = f (Fin.snoc 0 x) :=
  rfl

@[simp]
/-
**continuousMultilinearCurryFin1_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousMultilinearCurryFin1_symm_apply (f : G ->L[𝕜] G') (v : Fin 1 -> 
G) : (continuousMultilinearCurryFin1 𝕜 G G').symm f v = f (v 0)
参数：f : G ->L[𝕜] G'；v : Fin 1 -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem continuousMultilinearCurryFin1_symm_apply (f : G →L[𝕜] G') (v : Fin 1 → G) :
    (continuousMultilinearCurryFin1 𝕜 G G').symm f v = f (v 0) :=
  rfl

namespace ContinuousMultilinearMap

variable (𝕜 G G')

@[simp]
/-
**ContinuousMultilinearMap.norm_domDomCongr** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sMultilinearMap`。
形式化陈述：norm_domDomCongr (σ : ι ≃ ι') (f : ContinuousMultilinearMap 𝕜 (fun _ : ι =
> G) G') : ‖domDomCongr σ f‖ = ‖f‖
参数：σ : ι ≃ ι'；f : ContinuousMultilinearMap 𝕜 (fun _ : ι => G) G'。
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
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ContinuousMultilinearMap.domDomCongr_apply`：∀ {R : Type u} {ι : Type v} 
{M₂ : Type w₂} {M₃ : Type w₃} [inst : Semiring R] [inst_1 : AddCommMonoid M₂]   
[inst_2 : AddCommMonoid M₃] [ins…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.prod_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : 
Fintype ι] [inst_1 : Fintype κ] [inst_2 : CommMonoid M]   (e : ι ≃ κ) (g : κ → M
), ∏ …
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.arrowCongr_apply`：∀ {α₁ : Sort u_1} {β₁ : Sort u_2} {α₂ : Sort u_3
} {β₂ : Sort u_4} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) (f : α₁ → β₁) (a : α₂),   (e₁.ar
rowCongr e₂)…
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_domDomCongr (σ : ι ≃ ι') (f : ContinuousMultilinearMap 𝕜 (fun _ : ι => G) G') :
    ‖domDomCongr σ f‖ = ‖f‖ := by
  simp only [norm_def, ← σ.prod_comp,
    (σ.arrowCongr (Equiv.refl G)).surjective.forall, domDomCongr_apply, Equiv.arrowCongr_apply,
    Equiv.coe_refl, comp_apply, Equiv.symm_apply_apply, id]

/-- An equivalence of the index set defines a linear isometric equivalence between the spaces
of multilinear maps. -/
/-
**ContinuousMultilinearMap.domDomCongr** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMult
ilinearMap`。
形式化陈述：{R : Type u} →   {ι : Type v} →     {M₂ : Type w₂} →       {M₃ : Type w₃} 
→         [inst : Semiring R] →           [inst_1 : AddCommMonoid M₂] →         
    [inst_2 : AddCommMonoid M₃] →               [inst_3 : _root_.Module R M₂] → 
                [inst_4 : _root_.Module R M₃] →                   [inst_5 : Topo
logicalSpace M₂] →                     [inst_6 : TopologicalSpace M₃] →         
              {ι' : Type u_1} →                         ι ≃ ι' →                
           ContinuousMultilinearMap R (fun x => M₂) M₃ → ContinuousMultilinearMa
p R (fun x => M₂) M₃
参数：fun x => M₂；fun x => M₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence of the index set defines a linear isometric equivalence between t
he spaces
of multilinear maps.
-/
def domDomCongrₗᵢ (σ : ι ≃ ι') :
    ContinuousMultilinearMap 𝕜 (fun _ : ι => G) G' ≃ₗᵢ[𝕜]
      ContinuousMultilinearMap 𝕜 (fun _ : ι' => G) G' :=
  { domDomCongrEquiv σ with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    norm_map' := norm_domDomCongr 𝕜 G G' σ }

variable {𝕜 G G'}

section

/-- A continuous multilinear map with variables indexed by `ι ⊕ ι'` defines a continuous
multilinear map with variables indexed by `ι` taking values in the space of continuous multilinear
maps with variables indexed by `ι'`. -/
/-
**ContinuousMultilinearMap.currySum** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMultili
nearMap`。
形式化陈述：currySum (f : ContinuousMultilinearMap 𝕜 (fun _ : ι oplus ι' => G) G') : C
ontinuousMultilinearMap 𝕜 (fun _ : ι => G) (ContinuousMultilinearMap 𝕜 (fun _ : 
ι' => G) G')
参数：f : ContinuousMultilinearMap 𝕜 (fun _ : ι oplus ι' => G) G'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous multilinear map with variables indexed by `ι ⊕ ι'` defines a contin
uous
multilinear map with variables indexed by `ι` taking values in the space of cont
inuous multilinear
maps with variables indexed by `ι'`.
-/
def currySum (f : ContinuousMultilinearMap 𝕜 (fun _ : ι ⊕ ι' => G) G') :
    ContinuousMultilinearMap 𝕜 (fun _ : ι => G) (ContinuousMultilinearMap 𝕜 (fun _ : ι' => G) G') :=
  MultilinearMap.mkContinuousMultilinear (MultilinearMap.currySum f.toMultilinearMap) ‖f‖
    fun m m' => by simpa [Fintype.prod_sum_type, mul_assoc] using f.le_opNorm (Sum.elim m m')

@[simp]
/-
**ContinuousMultilinearMap.currySum_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousM
ultilinearMap`。
形式化陈述：currySum_apply (f : ContinuousMultilinearMap 𝕜 (fun _ : ι oplus ι' => G) G
') (m : ι -> G) (m' : ι' -> G) : f.currySum m m' = f (Sum.elim m m')
参数：f : ContinuousMultilinearMap 𝕜 (fun _ : ι oplus ι' => G) G'；m : ι -> G；m' : ι
' -> G。
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
theorem currySum_apply (f : ContinuousMultilinearMap 𝕜 (fun _ : ι ⊕ ι' => G) G') (m : ι → G)
    (m' : ι' → G) : f.currySum m m' = f (Sum.elim m m') :=
  rfl

/-- A continuous multilinear map with variables indexed by `ι` taking values in the space of
continuous multilinear maps with variables indexed by `ι'` defines a continuous multilinear map with
variables indexed by `ι ⊕ ι'`. -/
/-
**ContinuousMultilinearMap.uncurrySum** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMulti
linearMap`。
形式化陈述：uncurrySum (f : ContinuousMultilinearMap 𝕜 (fun _ : ι => G) (ContinuousMul
tilinearMap 𝕜 (fun _ : ι' => G) G')) : ContinuousMultilinearMap 𝕜 (fun _ : ι opl
us ι' => G) G'
参数：f : ContinuousMultilinearMap 𝕜 (fun _ : ι => G) (ContinuousMultilinearMap 𝕜 (
fun _ : ι' => G) G')。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous multilinear map with variables indexed by `ι` taking values in the 
space of
continuous multilinear maps with variables indexed by `ι'` defines a continuous 
multilinear map with
variables indexed by `ι ⊕ ι'`.
-/
def uncurrySum (f : ContinuousMultilinearMap 𝕜 (fun _ : ι => G)
    (ContinuousMultilinearMap 𝕜 (fun _ : ι' => G) G')) :
    ContinuousMultilinearMap 𝕜 (fun _ : ι ⊕ ι' => G) G' :=
  MultilinearMap.mkContinuous
    (toMultilinearMapLinear.compMultilinearMap f.toMultilinearMap).uncurrySum ‖f‖ fun m => by
    simpa [Fintype.prod_sum_type, mul_assoc] using!
      (f (m ∘ Sum.inl)).le_of_opNorm_le (f.le_opNorm _) (m ∘ Sum.inr)

@[simp]
/-
**ContinuousMultilinearMap.uncurrySum_apply** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sMultilinearMap`。
形式化陈述：uncurrySum_apply (f : ContinuousMultilinearMap 𝕜 (fun _ : ι => G) (Continu
ousMultilinearMap 𝕜 (fun _ : ι' => G) G')) (m : ι oplus ι' -> G) : f.uncurrySum 
m = f (m ∘ Sum.inl) (m ∘ Sum.inr)
参数：f : ContinuousMultilinearMap 𝕜 (fun _ : ι => G) (ContinuousMultilinearMap 𝕜 (
fun _ : ι' => G) G')；m : ι oplus ι' -> G。
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
theorem uncurrySum_apply (f : ContinuousMultilinearMap 𝕜 (fun _ : ι => G)
    (ContinuousMultilinearMap 𝕜 (fun _ : ι' => G) G'))
    (m : ι ⊕ ι' → G) : f.uncurrySum m = f (m ∘ Sum.inl) (m ∘ Sum.inr) :=
  rfl

variable (𝕜 ι ι' G G')

set_option backward.isDefEq.respectTransparency false in
/-- Linear isometric equivalence between the space of continuous multilinear maps with variables
indexed by `ι ⊕ ι'` and the space of continuous multilinear maps with variables indexed by `ι`
taking values in the space of continuous multilinear maps with variables indexed by `ι'`.

The forward and inverse functions are `ContinuousMultilinearMap.currySum`
and `ContinuousMultilinearMap.uncurrySum`. Use this definition only if you need
some properties of `LinearIsometryEquiv`. -/
/-
**ContinuousMultilinearMap.currySumEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMu
ltilinearMap`。
形式化陈述：currySumEquiv : ContinuousMultilinearMap 𝕜 (fun _ : ι oplus ι' => G) G' ≃ₗ
ᵢ[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι => G) (ContinuousMultilinearMap 𝕜 (fu
n _ : ι' => G) G')
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Linear isometric equivalence between the space of continuous multilinear maps wi
th variables
indexed by `ι ⊕ ι'` and the space of continuous multilinear maps with variables 
indexed by `ι`
taking values in the space of continuous multilinear maps with variables indexed
 by `ι'`.

The forward and inverse functions are `ContinuousMultilinearMap.currySum`
and `ContinuousMultilinearMap.uncurrySum`. Use this definition only if you need
some properties of `LinearIsometryEquiv`.
-/
def currySumEquiv : ContinuousMultilinearMap 𝕜 (fun _ : ι ⊕ ι' => G) G' ≃ₗᵢ[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : ι => G) (ContinuousMultilinearMap 𝕜 (fun _ : ι' => G) G') :=
  LinearIsometryEquiv.ofBounds
    { toFun := currySum
      invFun := uncurrySum
      map_add' := fun f g => by
        ext
        rfl
      map_smul' := fun c f => by
        ext
        rfl
      left_inv := fun f => by
        ext m
        exact congr_arg f (Sum.elim_comp_inl_inr m) }
    (fun f => MultilinearMap.mkContinuousMultilinear_norm_le _ (norm_nonneg f) _) fun f => by
      simp only [LinearEquiv.coe_symm_mk]
      exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg f) _

end

section

variable (𝕜 G G') {k l : ℕ} {s : Finset (Fin n)}

/-- If `s : Finset (Fin n)` is a finite set of cardinality `k` and its complement has cardinality
`l`, then the space of continuous multilinear maps `G [×n]→L[𝕜] G'` of `n` variables is isomorphic
to the space of continuous multilinear maps `G [×k]→L[𝕜] G [×l]→L[𝕜] G'` of `k` variables taking
values in the space of continuous multilinear maps of `l` variables. -/
/-
**ContinuousMultilinearMap.curryFinFinset** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousM
ultilinearMap`。
形式化陈述：curryFinFinset {k l n : Nat} {s : Finset (Fin n)} (hk : #s = k) (hl : #sᶜ 
= l) : (G [×n]->L[𝕜] G') ≃ₗᵢ[𝕜] G [×k]->L[𝕜] G [×l]->L[𝕜] G'
参数：Fin n；hk : #s = k；hl : #sᶜ = l。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `s : Finset (Fin n)` is a finite set of cardinality `k` and its complement ha
s cardinality
`l`, then the space of continuous multilinear maps `G [×n]→L[𝕜] G'` of `n` varia
bles is isomorphic
to the space of continuous multilinear maps `G [×k]→L[𝕜] G [×l]→L[𝕜] G'` of `k` 
variables taking
values in the space of continuous multilinear maps of `l` variables.
-/
def curryFinFinset {k l n : ℕ} {s : Finset (Fin n)} (hk : #s = k) (hl : #sᶜ = l) :
    (G [×n]→L[𝕜] G') ≃ₗᵢ[𝕜] G [×k]→L[𝕜] G [×l]→L[𝕜] G' :=
  (domDomCongrₗᵢ 𝕜 G G' (finSumEquivOfFinset hk hl).symm).trans
    (currySumEquiv 𝕜 (Fin k) (Fin l) G G')

variable {𝕜 G G'}

@[simp]
/-
**ContinuousMultilinearMap.curryFinFinset_apply** 是 Mathlib 中的一个定理，位于命名空间 `Conti
nuousMultilinearMap`。
形式化陈述：curryFinFinset_apply (hk : #s = k) (hl : #sᶜ = l) (f : G [×n]->L[𝕜] G') (m
k : Fin k -> G) (ml : Fin l -> G) : curryFinFinset 𝕜 G G' hk hl f mk ml = f fun 
i => Sum.elim mk ml ((finSumEquivOfFinset hk hl).symm i)
参数：hk : #s = k；hl : #sᶜ = l；f : G [×n]->L[𝕜] G'；mk : Fin k -> G；ml : Fin l -> G。
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
· 使用定理 `ContinuousMultilinearMap.instSMulCommClass`：∀ {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCommMo
noid M₂]   [inst_2 : (i : ι) → T…
-/
theorem curryFinFinset_apply (hk : #s = k) (hl : #sᶜ = l) (f : G [×n]→L[𝕜] G')
    (mk : Fin k → G) (ml : Fin l → G) : curryFinFinset 𝕜 G G' hk hl f mk ml =
      f fun i => Sum.elim mk ml ((finSumEquivOfFinset hk hl).symm i) :=
  rfl

@[simp]
/-
**ContinuousMultilinearMap.curryFinFinset_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `
ContinuousMultilinearMap`。
形式化陈述：curryFinFinset_symm_apply (hk : #s = k) (hl : #sᶜ = l) (f : G [×k]->L[𝕜] G
 [×l]->L[𝕜] G') (m : Fin n -> G) : (curryFinFinset 𝕜 G G' hk hl).symm f m = f (f
un i => m <| finSumEquivOfFinset hk hl (Sum.inl i)) fun i => m finSumEquivOfFins
et hk hl (Sum.inr i)
参数：hk : #s = k；hl : #sᶜ = l；f : G [×k]->L[𝕜] G [×l]->L[𝕜] G'；m : Fin n -> G。
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
· 使用定理 `ContinuousMultilinearMap.instSMulCommClass`：∀ {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCommMo
noid M₂]   [inst_2 : (i : ι) → T…
-/
theorem curryFinFinset_symm_apply (hk : #s = k) (hl : #sᶜ = l)
    (f : G [×k]→L[𝕜] G [×l]→L[𝕜] G') (m : Fin n → G) : (curryFinFinset 𝕜 G G' hk hl).symm f m =
      f (fun i => m <| finSumEquivOfFinset hk hl (Sum.inl i)) fun i =>
        m <| finSumEquivOfFinset hk hl (Sum.inr i) :=
  rfl
/-
**ContinuousMultilinearMap.curryFinFinset_symm_apply_piecewise_const** 是 Mathlib
 中的一个定理，位于命名空间 `ContinuousMultilinearMap`。
形式化陈述：curryFinFinset_symm_apply_piecewise_const (hk : #s = k) (hl : #sᶜ = l) (f 
: G [×k]->L[𝕜] G [×l]->L[𝕜] G') (x y : G) : (curryFinFinset 𝕜 G G' hk hl).symm f
 (s.piecewise (fun _ => x) fun _ => y) = f (fun _ => x) fun _ => y
参数：hk : #s = k；hl : #sᶜ = l；f : G [×k]->L[𝕜] G [×l]->L[𝕜] G'；x y : G。
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
· 使用定理 `MultilinearMap.curryFinFinset_symm_apply_piecewise_const`：curryFinFinset
_symm_apply_piecewise_const {k l n : Nat} {s : Finset (Fin n)} (hk : #s = k) (hl
 : #sᶜ = l) (f : MultilinearMap R (fun _ : Fin…
-/
theorem curryFinFinset_symm_apply_piecewise_const (hk : #s = k) (hl : #sᶜ = l)
    (f : G [×k]→L[𝕜] G [×l]→L[𝕜] G') (x y : G) :
    (curryFinFinset 𝕜 G G' hk hl).symm f (s.piecewise (fun _ => x) fun _ => y) =
      f (fun _ => x) fun _ => y :=
  MultilinearMap.curryFinFinset_symm_apply_piecewise_const hk hl _ x y

@[simp]
/-
**ContinuousMultilinearMap.curryFinFinset_symm_apply_const** 是 Mathlib 中的一个定理，位于
命名空间 `ContinuousMultilinearMap`。
形式化陈述：curryFinFinset_symm_apply_const (hk : #s = k) (hl : #sᶜ = l) (f : G [×k]->
L[𝕜] G [×l]->L[𝕜] G') (x : G) : ((curryFinFinset 𝕜 G G' hk hl).symm f fun _ => x
) = f (fun _ => x) fun _ => x
参数：hk : #s = k；hl : #sᶜ = l；f : G [×k]->L[𝕜] G [×l]->L[𝕜] G'；x : G。
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
· 使用定理 `ContinuousMultilinearMap.instSMulCommClass`：∀ {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCommMo
noid M₂]   [inst_2 : (i : ι) → T…
-/
theorem curryFinFinset_symm_apply_const (hk : #s = k) (hl : #sᶜ = l)
    (f : G [×k]→L[𝕜] G [×l]→L[𝕜] G') (x : G) :
    ((curryFinFinset 𝕜 G G' hk hl).symm f fun _ => x) = f (fun _ => x) fun _ => x :=
  rfl
/-
**ContinuousMultilinearMap.curryFinFinset_apply_const** 是 Mathlib 中的一个定理，位于命名空间 
`ContinuousMultilinearMap`。
形式化陈述：curryFinFinset_apply_const (hk : #s = k) (hl : #sᶜ = l) (f : G [×n]->L[𝕜] 
G') (x y : G) : (curryFinFinset 𝕜 G G' hk hl f (fun _ => x) fun _ => y) = f (s.p
iecewise (fun _ => x) fun _ => y)
参数：hk : #s = k；hl : #sᶜ = l；f : G [×n]->L[𝕜] G'；x y : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousMultilinearMap.curryFinFinset_symm_apply_piecewise_const`：curr
yFinFinset_symm_apply_piecewise_const (hk : #s = k) (hl : #sᶜ = l) (f : G [×k]->
L[𝕜] G [×l]->L[𝕜] G') (x y : G) : (curryFinFinset 𝕜 G G'…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearIsometryEquiv.symm_apply_apply`：symm_apply_apply (x : E) : e.symm 
(e x) = x
-/
theorem curryFinFinset_apply_const (hk : #s = k) (hl : #sᶜ = l) (f : G [×n]→L[𝕜] G')
    (x y : G) : (curryFinFinset 𝕜 G G' hk hl f (fun _ => x) fun _ => y) =
      f (s.piecewise (fun _ => x) fun _ => y) := by
  refine (curryFinFinset_symm_apply_piecewise_const hk hl _ _ _).symm.trans ?_
  rw [LinearIsometryEquiv.symm_apply_apply]

end

end ContinuousMultilinearMap

namespace ContinuousLinearMap

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Given a linear map into continuous multilinear maps
`B : G →L[𝕜] ContinuousMultilinearMap 𝕜 E F`, one cannot always uncurry it as `G` and `E` might
live in a different universe. However, one can always lift it to a continuous multilinear map
on `(G × (Π i, E i)) ^ (1 + n)`, which maps `(v_0, ..., v_n)` to `B (g_0) (u_1, ..., u_n)` where
`g_0` is the `G`-coordinate of `v_0` and `u_i` is the `E_i` coordinate of `v_i`. -/
/-
**ContinuousLinearMap.continuousMultilinearMapOption** 是 Mathlib 中的一个定义，位于命名空间 `
ContinuousLinearMap`。
形式化陈述：continuousMultilinearMapOption (B : G ->L[𝕜] ContinuousMultilinearMap 𝕜 E 
F) : ContinuousMultilinearMap 𝕜 (fun (_ : Option ι) => (G × (Π i, E i))) F
参数：B : G ->L[𝕜] ContinuousMultilinearMap 𝕜 E F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a linear map into continuous multilinear maps
`B : G →L[𝕜] ContinuousMultilinearMap 𝕜 E F`, one cannot always uncurry it as `G
` and `E` might
live in a different universe. However, one can always lift it to a continuous mu
ltilinear map
on `(G × (Π i, E i)) ^ (1 + n)`, which maps `(v_0, ..., v_n)` to `B (g_0) (u_1, 
..., u_n)` where
`g_0` is the `G`-coordinate of `v_0` and `u_i` is the `E_i` coordinate of `v_i`.
-/
noncomputable def continuousMultilinearMapOption (B : G →L[𝕜] ContinuousMultilinearMap 𝕜 E F) :
    ContinuousMultilinearMap 𝕜 (fun (_ : Option ι) ↦ (G × (Π i, E i))) F :=
  MultilinearMap.mkContinuous
  { toFun := fun p ↦ B (p none).1 (fun i ↦ (p i).2 i)
    map_update_add' := by
      intro inst v j x y
      match j with
      | none => simp
      | some j =>
        classical
        have B z : (fun i ↦ (Function.update v (some j) z (some i)).2 i) =
            Function.update (fun (i : ι) ↦ (v i).2 i) j (z.2 j) := by
          ext i
          rcases eq_or_ne i j with rfl | hij
          · simp
          · simp [hij]
        simp [B]
    map_update_smul' := by
      intro inst v j c x
      match j with
      | none => simp
      | some j =>
        classical
        have B z : (fun i ↦ (Function.update v (some j) z (some i)).2 i) =
            Function.update (fun (i : ι) ↦ (v i).2 i) j (z.2 j) := by
          ext i
          rcases eq_or_ne i j with rfl | hij
          · simp
          · simp [hij]
        simp [B] } (‖B‖) <| by
  intro b
  simp only [MultilinearMap.coe_mk, Fintype.prod_option]
  apply (ContinuousMultilinearMap.le_opNorm _ _).trans
  rw [← mul_assoc]
  gcongr with i _
  · apply (B.le_opNorm _).trans
    gcongr
    exact norm_fst_le _
  · exact (norm_le_pi_norm _ _).trans (norm_snd_le _)
/-
**ContinuousLinearMap.continuousMultilinearMapOption_apply_eq_self** 是 Mathlib 中
的一个引理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：continuousMultilinearMapOption_apply_eq_self (B : G ->L[𝕜] ContinuousMulti
linearMap 𝕜 E F) (a : G) (v : Π i, E i) : B.continuousMultilinearMapOption (fun 
_ => (a, v)) = B a v
参数：B : G ->L[𝕜] ContinuousMultilinearMap 𝕜 E F；a : G；v : Π i, E i。
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
-/
lemma continuousMultilinearMapOption_apply_eq_self (B : G →L[𝕜] ContinuousMultilinearMap 𝕜 E F)
    (a : G) (v : Π i, E i) : B.continuousMultilinearMapOption (fun _ ↦ (a, v)) = B a v := rfl

end ContinuousLinearMap

