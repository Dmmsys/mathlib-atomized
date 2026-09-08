/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Curry
public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin

/-!
# Uncurrying continuous alternating maps

Given a continuous function `f` which is linear in the first argument
and is alternating form in the other `n` arguments,
this file defines a continuous alternating form `ContinuousAlternatingMap.alternatizeUncurryFin f`
in `n + 1` arguments.

This function is given by
```
ContinuousAlternatingMap.alternatizeUncurryFin f v =
  ∑ i : Fin (n + 1), (-1) ^ (i : ℕ) • f (v i) (removeNth i v)
```

Given a continuous alternating map `f` of `n + 1` arguments,
each term in the sum above written for `f.curryLeft` equals the original map,
thus `f.curryLeft.alternatizeUncurryFin = (n + 1) • f`.

We do not multiply the result of `alternatizeUncurryFin` by `(n + 1)⁻¹`
so that the construction works for `𝕜`-multilinear maps over any normed field `𝕜`,
not only a field of characteristic zero.

## Main results

- `ContinuousAlternatingMap.alternatizeUncurryFin_curryLeft`:
  the round-trip formula for currying/uncurrying, see above.

- `ContinuousAlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinLM_comp_of_symmetric`:
  If `f` is a symmetric bilinear map taking values in the space of continuous alternating maps,
  then the twice uncurried `f` is zero.

The latter theorem will be used
to prove that the second exterior derivative of a differential form is zero.
-/

@[expose] public section

open Fin Function

namespace ContinuousAlternatingMap

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {n : ℕ}

/-- If `f` is a continuous `(n + 1)`-multilinear alternating map, `x` is an element of the domain,
and `v` is an `n`-vector, then the value of `f` at `v` with `x` inserted at the `p`th place
equals `(-1) ^ p` times the value of `f` at `v` with `x` prepended. -/
/-
**ContinuousAlternatingMap.map_insertNth** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAl
ternatingMap`。
形式化陈述：map_insertNth (f : E [⋀^Fin (n + 1)]->L[𝕜] F) (p : Fin (n + 1)) (x : E) (v
 : Fin n -> E) : f (p.insertNth x v) = (-1) ^ (p : Nat) • f (Matrix.vecCons x v)
参数：f : E [⋀^Fin (n + 1)]->L[𝕜] F；p : Fin (n + 1)；x : E；v : Fin n -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.map_insertNth`：map_insertNth (f : M [⋀^Fin (n + 1)]->ₗ[R]
 N) (p : Fin (n + 1)) (x : M) (v : Fin n -> M) : f (p.insertNth x v) = (-1) ^ (p
 : Nat) • f (Matri…

--- 原说明 ---
If `f` is a continuous `(n + 1)`-multilinear alternating map, `x` is an element 
of the domain,
and `v` is an `n`-vector, then the value of `f` at `v` with `x` inserted at the 
`p`th place
equals `(-1) ^ p` times the value of `f` at `v` with `x` prepended.
-/
theorem map_insertNth (f : E [⋀^Fin (n + 1)]→L[𝕜] F) (p : Fin (n + 1)) (x : E) (v : Fin n → E) :
    f (p.insertNth x v) = (-1) ^ (p : ℕ) • f (Matrix.vecCons x v) :=
  f.toAlternatingMap.map_insertNth p x v
/-
**ContinuousAlternatingMap.neg_one_pow_smul_map_insertNth** 是 Mathlib 中的一个定理，位于命
名空间 `ContinuousAlternatingMap`。
形式化陈述：neg_one_pow_smul_map_insertNth (f : E [⋀^Fin (n + 1)]->L[𝕜] F) (p : Fin (n
 + 1)) (x : E) (v : Fin n -> E) : (-1) ^ (p : Nat) • f (p.insertNth x v) = f (Ma
trix.vecCons x v)
参数：f : E [⋀^Fin (n + 1)]->L[𝕜] F；p : Fin (n + 1)；x : E；v : Fin n -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.neg_one_pow_smul_map_insertNth`：neg_one_pow_smul_map_inse
rtNth (f : M [⋀^Fin (n + 1)]->ₗ[R] N) (p : Fin (n + 1)) (x : M) (v : Fin n -> M)
 : (-1) ^ (p : Nat) • f (p.insertNt…
-/
theorem neg_one_pow_smul_map_insertNth (f : E [⋀^Fin (n + 1)]→L[𝕜] F) (p : Fin (n + 1)) (x : E)
    (v : Fin n → E) : (-1) ^ (p : ℕ) • f (p.insertNth x v) = f (Matrix.vecCons x v) :=
  f.toAlternatingMap.neg_one_pow_smul_map_insertNth p x v

/-- Let `v` be an `(n + 1)`-tuple with two equal elements `v i = v j`, `i ≠ j`.
Let `w i` (resp., `w j`) be the vector `v` with `i`th (resp., `j`th) element removed.
Then `(-1) ^ i • f (w i) + (-1) ^ j • f (w j) = 0`.
This follows from the fact that these two vectors differ by a permutation of sign `(-1) ^ (i + j)`.

These are the only two nonzero terms in the proof of `map_eq_zero_of_eq`
in the definition of `AlternatingMap.alternatizeUncurryFin`. -/
/-
**ContinuousAlternatingMap.neg_one_pow_smul_map_removeNth_add_eq_zero_of_eq** 是 
Mathlib 中的一个定理，位于命名空间 `ContinuousAlternatingMap`。
形式化陈述：neg_one_pow_smul_map_removeNth_add_eq_zero_of_eq (f : E [⋀^Fin n]->L[𝕜] F)
 {v : Fin (n + 1) -> E} {i j : Fin (n + 1)} (hvij : v i = v j) (hij : i != j) : 
(-1) ^ (i : Nat) • f (i.removeNth v) + (-1) ^ (j : Nat) • f (j.removeNth v) = 0
参数：f : E [⋀^Fin n]->L[𝕜] F；n + 1；n + 1；hvij : v i = v j；hij : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.neg_one_pow_smul_map_removeNth_add_eq_zero_of_eq`：neg_one
_pow_smul_map_removeNth_add_eq_zero_of_eq (f : M [⋀^Fin n]->ₗ[R] N) {v : Fin (n 
+ 1) -> M} {i j : Fin (n + 1)} (hvij : v i = v j) (hi…

--- 原说明 ---
Let `v` be an `(n + 1)`-tuple with two equal elements `v i = v j`, `i ≠ j`.
Let `w i` (resp., `w j`) be the vector `v` with `i`th (resp., `j`th) element rem
oved.
Then `(-1) ^ i • f (w i) + (-1) ^ j • f (w j) = 0`.
This follows from the fact that these two vectors differ by a permutation of sig
n `(-1) ^ (i + j)`.

These are the only two nonzero terms in the proof of `map_eq_zero_of_eq`
in the definition of `AlternatingMap.alternatizeUncurryFin`.
-/
theorem neg_one_pow_smul_map_removeNth_add_eq_zero_of_eq (f : E [⋀^Fin n]→L[𝕜] F)
    {v : Fin (n + 1) → E} {i j : Fin (n + 1)} (hvij : v i = v j) (hij : i ≠ j) :
    (-1) ^ (i : ℕ) • f (i.removeNth v) + (-1) ^ (j : ℕ) • f (j.removeNth v) = 0 :=
  f.toAlternatingMap.neg_one_pow_smul_map_removeNth_add_eq_zero_of_eq hvij hij

set_option backward.privateInPublic true in
/-
**ContinuousAlternatingMap.alternatizeUncurryFinCLM.aux** 是 Mathlib 中的一个定义，位于命名空
间 `ContinuousAlternatingMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def alternatizeUncurryFinCLM.aux :
    (E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) →ₗ[𝕜] E [⋀^Fin (n + 1)]→ₗ[𝕜] F :=
  AlternatingMap.alternatizeUncurryFinLM ∘ₗ (toAlternatingMapLinear (R := 𝕜)).compRight (S := 𝕜) ∘ₗ
    ContinuousLinearMap.coeLM 𝕜
/-
**ContinuousAlternatingMap.alternatizeUncurryFinCLM.aux_apply** 是 Mathlib 中的一个引理
，位于命名空间 `ContinuousAlternatingMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma alternatizeUncurryFinCLM.aux_apply (f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F)
    (v : Fin (n + 1) → E) :
    aux f v = ∑ i : Fin (n + 1), (-1) ^ (i : ℕ) • f (v i) (i.removeNth v) := by
  simp [aux, AlternatingMap.alternatizeUncurryFin_apply]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
variable (𝕜 E F) in
/-- `AlternatingMap.alternatizeUncurryFin` as a continuous linear map. -/
@[irreducible]
/-
**ContinuousAlternatingMap.alternatizeUncurryFinCLM** 是 Mathlib 中的一个定义，位于命名空间 `C
ontinuousAlternatingMap`。
形式化陈述：alternatizeUncurryFinCLM : (E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F) ->L[𝕜] E [⋀^Fin 
(n + 1)]->L[𝕜] F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AlternatingMap.alternatizeUncurryFin` as a continuous linear map.
-/
noncomputable def alternatizeUncurryFinCLM :
    (E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) →L[𝕜] E [⋀^Fin (n + 1)]→L[𝕜] F :=
  AlternatingMap.mkContinuousLinear alternatizeUncurryFinCLM.aux (n + 1) fun f v ↦ calc
    ‖alternatizeUncurryFinCLM.aux f v‖ ≤ ∑ i : Fin (n + 1), ‖f‖ * ∏ i, ‖v i‖ := by
      rw [alternatizeUncurryFinCLM.aux_apply]
      refine norm_sum_le_of_le _ fun i hi ↦ ?_
      rw [norm_isUnit_zsmul _ (.pow _ isUnit_one.neg), i.prod_univ_succAbove, ← mul_assoc]
      apply (f (v i)).le_of_opNorm_le
      apply f.le_opNorm
    _ = (n + 1) * ‖f‖ * ∏ i, ‖v i‖ := by simp [mul_assoc]
/-
**ContinuousAlternatingMap.norm_alternatizeUncurryFinCLM_le** 是 Mathlib 中的一个引理，位
于命名空间 `ContinuousAlternatingMap`。
形式化陈述：norm_alternatizeUncurryFinCLM_le : ‖alternatizeUncurryFinCLM (n
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `ContinuousAlternatingMap.instSMulCommClass`：∀ {M : Type u_2} {N : Type u
_4} {ι : Type u_6} [inst : AddCommMonoid M] [inst_1 : TopologicalSpace M]   [ins
t_2 : AddCommMonoid N] [inst_3 :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAlternatingMap.alternatizeUncurryFinCLM.eq_1`：∀ (𝕜 : Type u_1)
 (E : Type u_2) (F : Type u_3) [inst : NontriviallyNormedField 𝕜] [inst_1 : Norm
edAddCommGroup E]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `AlternatingMap.mkContinuousLinear_norm_le`：mkContinuousLinear_norm_le (f
 : F ->ₗ[𝕜] E [⋀^ι]->ₗ[𝕜] G) {C : Real} (hC : 0 <= C) (H : forall x m, ‖f x m‖ <
= C * ‖x‖ * ∏ i, ‖m i‖) : ‖mkCo…
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Right.add_pos_of_nonneg_of_pos`：∀ {α : Type u_1} [inst : AddZeroClass α]
 [inst_1 : Preorder α] [AddRightMono α] {a b : α}, 0 ≤ a → 0 < b → 0 < a + b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
lemma norm_alternatizeUncurryFinCLM_le : ‖alternatizeUncurryFinCLM (n := n) 𝕜 E F‖ ≤ n + 1 := by
  rw [alternatizeUncurryFinCLM]
  apply AlternatingMap.mkContinuousLinear_norm_le
  positivity

/-- Given a continuous function which is linear in the first argument
and is alternating in the other `n` arguments,
build a continuous alternating form in `n + 1` arguments.

The function is given by
```
alternatizeUncurryFin f v = ∑ i : Fin (n + 1), (-1) ^ (i : ℕ) • f (v i) (removeNth i v)
```

Note that the round-trip with `curryLeft` multiplies the form by `n + 1`,
since we want to avoid division in this definition. -/
/-
**ContinuousAlternatingMap.alternatizeUncurryFin** 是 Mathlib 中的一个定义，位于命名空间 `Cont
inuousAlternatingMap`。
形式化陈述：alternatizeUncurryFin (f : E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F) : E [⋀^Fin (n + 1
)]->L[𝕜] F
参数：f : E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a continuous function which is linear in the first argument
and is alternating in the other `n` arguments,
build a continuous alternating form in `n + 1` arguments.

The function is given by
```
alternatizeUncurryFin f v = ∑ i : Fin (n + 1), (-1) ^ (i : ℕ) • f (v i) (removeN
th i v)
```

Note that the round-trip with `curryLeft` multiplies the form by `n + 1`,
since we want to avoid division in this definition.
-/
noncomputable def alternatizeUncurryFin (f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) :
    E [⋀^Fin (n + 1)]→L[𝕜] F :=
  alternatizeUncurryFinCLM 𝕜 E F f

@[simp]
/-
**ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply** 是 Mathlib 中的一个引理，位于命
名空间 `ContinuousAlternatingMap`。
形式化陈述：alternatizeUncurryFinCLM_apply (f : E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F) : altern
atizeUncurryFinCLM 𝕜 E F f = alternatizeUncurryFin f
参数：f : E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F。
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
· 使用定理 `ContinuousAlternatingMap.instSMulCommClass`：∀ {M : Type u_2} {N : Type u
_4} {ι : Type u_6} [inst : AddCommMonoid M] [inst_1 : TopologicalSpace M]   [ins
t_2 : AddCommMonoid N] [inst_3 :…
-/
lemma alternatizeUncurryFinCLM_apply (f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) :
    alternatizeUncurryFinCLM 𝕜 E F f = alternatizeUncurryFin f :=
  rfl
/-
**ContinuousAlternatingMap.norm_alternatizeUncurryFin_le** 是 Mathlib 中的一个引理，位于命名
空间 `ContinuousAlternatingMap`。
形式化陈述：norm_alternatizeUncurryFin_le (f : E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F) : ‖altern
atizeUncurryFin f‖ <= (n + 1) * ‖f‖
参数：f : E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F。
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
· 使用定理 `ContinuousLinearMap.le_of_opNorm_le`：le_of_opNorm_le {c : Real} (h : ‖f‖
 <= c) (x : E) : ‖f x‖ <= c * ‖x‖
· 使用定理 `ContinuousAlternatingMap.instSMulCommClass`：∀ {M : Type u_2} {N : Type u
_4} {ι : Type u_6} [inst : AddCommMonoid M] [inst_1 : TopologicalSpace M]   [ins
t_2 : AddCommMonoid N] [inst_3 :…
· 使用引理 `ContinuousAlternatingMap.norm_alternatizeUncurryFinCLM_le`：norm_alternat
izeUncurryFinCLM_le : ‖alternatizeUncurryFinCLM (n
-/
lemma norm_alternatizeUncurryFin_le (f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) :
    ‖alternatizeUncurryFin f‖ ≤ (n + 1) * ‖f‖ :=
  (alternatizeUncurryFinCLM 𝕜 E F).le_of_opNorm_le norm_alternatizeUncurryFinCLM_le f
/-
**ContinuousAlternatingMap.alternatizeUncurryFin_apply** 是 Mathlib 中的一个定理，位于命名空间
 `ContinuousAlternatingMap`。
形式化陈述：alternatizeUncurryFin_apply (f : E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F) (v : Fin (n
 + 1) -> E) : alternatizeUncurryFin f v = ∑ i : Fin (n + 1), (-1) ^ (i : Nat) • 
f (v i) (removeNth i v)
参数：f : E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F；v : Fin (n + 1) -> E。
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
· 使用定理 `ContinuousAlternatingMap.alternatizeUncurryFin.eq_1`：∀ {𝕜 : Type u_1} {E
 : Type u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedA
ddCommGroup E]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `ContinuousAlternatingMap.instSMulCommClass`：∀ {M : Type u_2} {N : Type u
_4} {ι : Type u_6} [inst : AddCommMonoid M] [inst_1 : TopologicalSpace M]   [ins
t_2 : AddCommMonoid N] [inst_3 :…
· 使用定理 `ContinuousAlternatingMap.alternatizeUncurryFinCLM.eq_1`：∀ (𝕜 : Type u_1)
 (E : Type u_2) (F : Type u_3) [inst : NontriviallyNormedField 𝕜] [inst_1 : Norm
edAddCommGroup E]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `_private.Mathlib.Analysis.Normed.Module.Alternating.Uncurry.Fin.0.Contin
uousAlternatingMap.alternatizeUncurryFinCLM.aux_apply`：∀ {𝕜 : Type u_1} {E : Typ
e u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddComm
Group E]   [inst_2 : NormedSpace 𝕜 …
-/
theorem alternatizeUncurryFin_apply (f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) (v : Fin (n + 1) → E) :
    alternatizeUncurryFin f v = ∑ i : Fin (n + 1), (-1) ^ (i : ℕ) • f (v i) (removeNth i v) := by
  rw [alternatizeUncurryFin, alternatizeUncurryFinCLM]
  apply alternatizeUncurryFinCLM.aux_apply
/-
**ContinuousAlternatingMap.toAlternatingMap_alternatizeUncurryFin** 是 Mathlib 中的
一个引理，位于命名空间 `ContinuousAlternatingMap`。
形式化陈述：toAlternatingMap_alternatizeUncurryFin (f : E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F) 
: (alternatizeUncurryFin f).toAlternatingMap = .alternatizeUncurryFin (toAlterna
tingMapLinear ∘ₗ (f : E ->ₗ[𝕜] E [⋀^Fin n]->L[𝕜] F))
参数：f : E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F。
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
· 使用定理 `AlternatingMap.ext`：ext {f f' : M [⋀^ι]->ₗ[R] N} (H : forall x, f x = f'
 x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAlternatingMap.alternatizeUncurryFin_apply`：alternatizeUncurry
Fin_apply (f : E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F) (v : Fin (n + 1) -> E) : alternatiz
eUncurryFin f v = ∑ i : Fin (n + 1), (-1) …
· 使用定理 `AlternatingMap.alternatizeUncurryFin_apply`：alternatizeUncurryFin_apply 
(f : M ->ₗ[R] M [⋀^Fin n]->ₗ[R] N) (v : Fin (n + 1) -> M) : alternatizeUncurryFi
n f v = ∑ i : Fin (n + 1), (-1) …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousAlternatingMap.toAlternatingMapLinear_apply`：∀ {R : Type u_1} 
{A : Type u_2} {M : Type u_3} {N : Type u_4} {ι : Type u_5} [inst : Semiring R] 
[inst_1 : Semiring A]   [inst_2 : AddCommMo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toAlternatingMap_alternatizeUncurryFin (f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) :
    (alternatizeUncurryFin f).toAlternatingMap =
      .alternatizeUncurryFin (toAlternatingMapLinear ∘ₗ (f : E →ₗ[𝕜] E [⋀^Fin n]→L[𝕜] F)) := by
  ext
  simp [alternatizeUncurryFin_apply, AlternatingMap.alternatizeUncurryFin_apply]

@[simp]
/-
**ContinuousAlternatingMap.alternatizeUncurryFin_add** 是 Mathlib 中的一个定理，位于命名空间 `
ContinuousAlternatingMap`。
形式化陈述：alternatizeUncurryFin_add (f g : E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F) : alternati
zeUncurryFin (f + g) = alternatizeUncurryFin f + alternatizeUncurryFin g
参数：f g : E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F。
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
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `ContinuousAlternatingMap.instSMulCommClass`：∀ {M : Type u_2} {N : Type u
_4} {ι : Type u_6} [inst : AddCommMonoid M] [inst_1 : TopologicalSpace M]   [ins
t_2 : AddCommMonoid N] [inst_3 :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
-/
theorem alternatizeUncurryFin_add (f g : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) :
    alternatizeUncurryFin (f + g) = alternatizeUncurryFin f + alternatizeUncurryFin g :=
  map_add (alternatizeUncurryFinCLM 𝕜 E F) f g

@[simp]
/-
**ContinuousAlternatingMap.alternatizeUncurryFin_curryLeft** 是 Mathlib 中的一个引理，位于
命名空间 `ContinuousAlternatingMap`。
形式化陈述：alternatizeUncurryFin_curryLeft (f : E [⋀^Fin (n + 1)]->L[𝕜] F) : alternat
izeUncurryFin (curryLeft f) = (n + 1) • f
参数：f : E [⋀^Fin (n + 1)]->L[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAlternatingMap.ext`：ext {f g : M [⋀^ι]->L[R] N} (H : forall x,
 f x = g x) : f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousAlternatingMap.alternatizeUncurryFin_apply`：alternatizeUncurry
Fin_apply (f : E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F) (v : Fin (n + 1) -> E) : alternatiz
eUncurryFin f v = ∑ i : Fin (n + 1), (-1) …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.insertNth_removeNth`：∀ {n : ℕ} {α : Fin (n + 1) → Sort u_1} (p : Fin
 (n + 1)) (x : α p) (f : (j : Fin (n + 1)) → α j),   p.insertNth x (p.removeNth 
f) = Function…
· 使用定理 `Function.update_eq_self`：update_eq_self (a : α) (f : forall a, β a) : up
date f a (f a) = f
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma alternatizeUncurryFin_curryLeft (f : E [⋀^Fin (n + 1)]→L[𝕜] F) :
    alternatizeUncurryFin (curryLeft f) = (n + 1) • f := by
  ext v
  simp [alternatizeUncurryFin_apply, ← map_insertNth]

@[simp]
/-
**ContinuousAlternatingMap.alternatizeUncurryFin_smul** 是 Mathlib 中的一个定理，位于命名空间 
`ContinuousAlternatingMap`。
形式化陈述：alternatizeUncurryFin_smul {S : Type*} [Monoid S] [DistribMulAction S F] [
ContinuousConstSMul S F] [SMulCommClass 𝕜 S F] (c : S) (f : E ->L[𝕜] E [⋀^Fin n]
->L[𝕜] F) : alternatizeUncurryFin (c • f) = c • alternatizeUncurryFin f
参数：c : S；f : E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F。
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
· 使用定理 `ContinuousAlternatingMap.ext`：ext {f g : M [⋀^ι]->L[R] N} (H : forall x,
 f x = g x) : f = g
· 使用定理 `ContinuousAlternatingMap.instSMulCommClass`：∀ {M : Type u_2} {N : Type u
_4} {ι : Type u_6} [inst : AddCommMonoid M] [inst_1 : TopologicalSpace M]   [ins
t_2 : AddCommMonoid N] [inst_3 :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAlternatingMap.alternatizeUncurryFin_apply`：alternatizeUncurry
Fin_apply (f : E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F) (v : Fin (n + 1) -> E) : alternatiz
eUncurryFin f v = ∑ i : Fin (n + 1), (-1) …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem alternatizeUncurryFin_smul {S : Type*} [Monoid S] [DistribMulAction S F]
    [ContinuousConstSMul S F] [SMulCommClass 𝕜 S F] (c : S) (f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) :
    alternatizeUncurryFin (c • f) = c • alternatizeUncurryFin f := by
  ext v
  simp [alternatizeUncurryFin_apply, smul_comm _ c, Finset.smul_sum]
/-
**ContinuousAlternatingMap.alternatizeUncurryFin_constOfIsEmptyLIE_comp** 是 Math
lib 中的一个定理，位于命名空间 `ContinuousAlternatingMap`。
形式化陈述：alternatizeUncurryFin_constOfIsEmptyLIE_comp (f : E ->L[𝕜] F) : alternatiz
eUncurryFin (constOfIsEmptyLIE 𝕜 E F (Fin 0) ∘L f) = ofSubsingleton _ _ _ (0 : F
in 1) f
参数：f : E ->L[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAlternatingMap.ext`：ext {f g : M [⋀^ι]->L[R] N} (H : forall x,
 f x = g x) : f = g
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
· 使用定理 `Fin.subsingleton_one`：Subsingleton (Fin 1)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAlternatingMap.alternatizeUncurryFin_apply`：alternatizeUncurry
Fin_apply (f : E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F) (v : Fin (n + 1) -> E) : alternatiz
eUncurryFin f v = ∑ i : Fin (n + 1), (-1) …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Fin.val_eq_zero`：∀ (a : Fin 1), ↑a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousAlternatingMap.constOfIsEmptyLIE_apply`：∀ (𝕜 : Type u) (E : Ty
pe wE) (F : Type wF) (ι : Type v) [inst : NontriviallyNormedField 𝕜]   [inst_1 :
 SeminormedAddCommGroup E] [inst_2 : N…
· 使用定理 `ContinuousAlternatingMap.constOfIsEmpty_apply`：∀ (R : Type u_1) (M : Typ
e u_2) {N : Type u_4} (ι : Type u_6) [inst : Semiring R] [inst_1 : AddCommMonoid
 M]   [inst_2 : _root_.Module R M] …
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `ContinuousAlternatingMap.ofSubsingleton_apply_apply`：∀ (R : Type u_1) (M
 : Type u_2) (N : Type u_4) {ι : Type u_6} [inst : Semiring R] [inst_1 : AddComm
Monoid M]   [inst_2 : _root_.Module R M] …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem alternatizeUncurryFin_constOfIsEmptyLIE_comp (f : E →L[𝕜] F) :
    alternatizeUncurryFin (constOfIsEmptyLIE 𝕜 E F (Fin 0) ∘L f) =
      ofSubsingleton _ _ _ (0 : Fin 1) f := by
  ext
  simp [alternatizeUncurryFin_apply]

/-- If `f` is a continuous bilinear map taking values in the space of continuous alternating maps,
then evaluation of the twice uncurried `f` on a tuple of vectors `v`
can be represented as a sum of

$$
f(v_i, v_j; v_0, \dots, \hat{v_i}, \dots, \hat{v_j}, \dots, v_{n+1}) -
f(v_j, v_i; v_0, \dots, \hat{v_i}, \dots, \hat{v_j}, \dots, v_{n+1})
$$

over all `(i j : Fin (n + 2))`, `i < j`, taken with appropriate signs.
Here $\hat{v_i}$ and $\hat{v_j}$ mean that these vectors are removed from the tuple.

We use pairs of `i j : Fin (n + 1)`, `i ≤ j`,
to encode pairs `(i.castSucc : Fin (n + 2), j.succ : Fin (n + 2))`,
so the power of `-1` is off by one compared to the informal texts.

In particular, if `f` is symmetric in the first two arguments,
then the resulting alternating map is zero,
see `alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_of_symmetric` below.
-/
/-
**ContinuousAlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_a
pply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlternatingMap`。
形式化陈述：alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_apply (f : E ->L[𝕜] E 
->L[𝕜] E [⋀^Fin n]->L[𝕜] F) (v : Fin (n + 2) -> E) : alternatizeUncurryFin (alte
rnatizeUncurryFinCLM 𝕜 E F ∘L f) v = ∑ (i : Fin (n + 1)), ∑ j >= i, (-1 : Int) ^
 (i + j : Nat) • (f (v i.castSucc) (v j.succ) (j.removeNth <| i.castSucc.removeN
th v) - f (v j.succ) (v i.castSucc) (j.removeNth <| i.castSucc.removeNth v))
参数：f : E ->L[𝕜] E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F；v : Fin (n + 2) -> E。
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
· 使用定理 `ContinuousAlternatingMap.instSMulCommClass`：∀ {M : Type u_2} {N : Type u
_4} {ι : Type u_6} [inst : AddCommMonoid M] [inst_1 : TopologicalSpace M]   [ins
t_2 : AddCommMonoid N] [inst_3 :…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ContinuousAlternatingMap.alternatizeUncurryFin_apply`：alternatizeUncurry
Fin_apply (f : E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F) (v : Fin (n + 1) -> E) : alternatiz
eUncurryFin f v = ∑ i : Fin (n + 1), (-1) …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `ContinuousAlternatingMap.instIsScalarTower`：∀ {M : Type u_2} {N : Type u
_4} {ι : Type u_6} [inst : AddCommMonoid M] [inst_1 : TopologicalSpace M]   [ins
t_2 : AddCommMonoid N] [inst_3 :…
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AlternatingMap.alternatizeUncurryFin_apply`：alternatizeUncurryFin_apply 
(f : M ->ₗ[R] M [⋀^Fin n]->ₗ[R] N) (v : Fin (n + 1) -> M) : alternatizeUncurryFi
n f v = ∑ i : Fin (n + 1), (-1) …
· 使用定理 `AlternatingMap.alternatizeUncurryFinLM_apply`：∀ {R : Type u_1} {M : Type
 u_2} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : Add
CommGroup N]   [inst_3 : _root_.Mo…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ContinuousAlternatingMap.toAlternatingMapLinear_apply`：∀ {R : Type u_1} 
{A : Type u_2} {M : Type u_3} {N : Type u_4} {ι : Type u_5} [inst : Semiring R] 
[inst_1 : Semiring A]   [inst_2 : AddCommMo…
· 使用定理 `AlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinLM_comp_apply`
：alternatizeUncurryFin_alternatizeUncurryFinLM_comp_apply (f : M ->ₗ[R] M ->ₗ[R]
 M [⋀^Fin n]->ₗ[R] N) (v : Fin (n + 2) -> M) : alternatizeUnc…

--- 原说明 ---
If `f` is a continuous bilinear map taking values in the space of continuous alt
ernating maps,
then evaluation of the twice uncurried `f` on a tuple of vectors `v`
can be represented as a sum of

$$
f(v_i, v_j; v_0, \dots, \hat{v_i}, \dots, \hat{v_j}, \dots, v_{n+1}) -
f(v_j, v_i; v_0, \dots, \hat{v_i}, \dots, \hat{v_j}, \dots, v_{n+1})
$$

over all `(i j : Fin (n + 2))`, `i < j`, taken with appropriate signs.
Here $\hat{v_i}$ and $\hat{v_j}$ mean that these vectors are removed from the tu
ple.

We use pairs of `i j : Fin (n + 1)`, `i ≤ j`,
to encode pairs `(i.castSucc : Fin (n + 2), j.succ : Fin (n + 2))`,
so the power of `-1` is off by one compared to the informal texts.

In particular, if `f` is symmetric in the first two arguments,
then the resulting alternating map is zero,
see `alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_of_symmetric` below.
-/
theorem alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_apply
    (f : E →L[𝕜] E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) (v : Fin (n + 2) → E) :
    alternatizeUncurryFin (alternatizeUncurryFinCLM 𝕜 E F ∘L f) v =
      ∑ (i : Fin (n + 1)), ∑ j ≥ i,
        (-1 : ℤ) ^ (i + j : ℕ) •
          (f (v i.castSucc) (v j.succ) (j.removeNth <| i.castSucc.removeNth v) -
            f (v j.succ) (v i.castSucc) (j.removeNth <| i.castSucc.removeNth v)) := by
  simpa [alternatizeUncurryFin_apply, AlternatingMap.alternatizeUncurryFin_apply]
    using AlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinLM_comp_apply
      (R := 𝕜) (M := E) (N := F)
      (f.toLinearMap₁₂.compr₂ (toAlternatingMapLinear (R := 𝕜))) v

/-- If `f` is a symmetric continuous bilinear map
taking values in the space of continuous alternating maps,
then the twice uncurried `f` is zero. -/
/-
**ContinuousAlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_o
f_symmetric** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlternatingMap`。
形式化陈述：alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_of_symmetric {f : E ->
L[𝕜] E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F} (hf : forall x y, f x y = f y x) : alternatiz
eUncurryFin (alternatizeUncurryFinCLM 𝕜 E F ∘L f) = 0
参数：hf : forall x y, f x y = f y x。
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
· 使用定理 `ContinuousAlternatingMap.instSMulCommClass`：∀ {M : Type u_2} {N : Type u
_4} {ι : Type u_6} [inst : AddCommMonoid M] [inst_1 : TopologicalSpace M]   [ins
t_2 : AddCommMonoid N] [inst_3 :…
· 使用定理 `ContinuousAlternatingMap.ext`：ext {f g : M [⋀^ι]->L[R] N} (H : forall x,
 f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinCLM_
comp_apply`：alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_apply (f : E ->L
[𝕜] E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F) (v : Fin (n + 2) -> E) : alternatizeUn…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `f` is a symmetric continuous bilinear map
taking values in the space of continuous alternating maps,
then the twice uncurried `f` is zero.
-/
theorem alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_of_symmetric
    {f : E →L[𝕜] E →L[𝕜] E [⋀^Fin n]→L[𝕜] F}
    (hf : ∀ x y, f x y = f y x) :
    alternatizeUncurryFin (alternatizeUncurryFinCLM 𝕜 E F ∘L f) = 0 := by
  ext v
  simp [alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_apply, hf]

/-- The derivative of `compContinuousLinearMap` can be represented
in terms of `alternatizeUncurryFinCLM`. -/
/-
**ContinuousAlternatingMap.fderivCompContinuousLinearMap_eq_alternatizeUncurryFi
n** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlternatingMap`。
形式化陈述：fderivCompContinuousLinearMap_eq_alternatizeUncurryFin (f : F [⋀^Fin (n + 
1)]->L[𝕜] G) (g : E ->L[𝕜] F) : f.fderivCompContinuousLinearMap g = alternatizeU
ncurryFinCLM 𝕜 E G ∘L ((compContinuousLinearMapCLM g ∘L f.curryLeft).postcomp E)
参数：f : F [⋀^Fin (n + 1)]->L[𝕜] G；g : E ->L[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
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
· 使用定理 `ContinuousAlternatingMap.instSMulCommClass`：∀ {M : Type u_2} {N : Type u
_4} {ι : Type u_6} [inst : AddCommMonoid M] [inst_1 : TopologicalSpace M]   [ins
t_2 : AddCommMonoid N] [inst_3 :…
· 使用定理 `ContinuousAlternatingMap.ext`：ext {f g : M [⋀^ι]->L[R] N} (H : forall x,
 f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.insertNth_apply_same`：insertNth_apply_same (i : Fin (n + 1)) (x : α 
i) (p : forall j, α (i.succAbove j)) : insertNth i x p i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.insertNth_apply_succAbove`：insertNth_apply_succAbove (i : Fin (n + 1
)) (x : α i) (p : forall j, α (i.succAbove j)) (j : Fin n) : insertNth i x p (i.
succAbove j) = p j
· 使用引理 `ContinuousAlternatingMap.fderivCompContinuousLinearMap_apply`：fderivComp
ContinuousLinearMap_apply (f : F [⋀^ι]->L[𝕜] G) (g dg : E ->L[𝕜] F) (v : ι -> E)
 : f.fderivCompContinuousLinearMap g dg v = ∑ i, f…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ContinuousLinearMap.postcomp_apply`：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2} {𝕜
₃ : Type u_3} [inst : NormedField 𝕜₁] [inst_1 : NormedField 𝕜₂]   [inst_2 : Norm
edField 𝕜₃] {σ : 𝕜₁ →+* …
· 使用定理 `ContinuousAlternatingMap.alternatizeUncurryFin_apply`：alternatizeUncurry
Fin_apply (f : E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F) (v : Fin (n + 1) -> E) : alternatiz
eUncurryFin f v = ∑ i : Fin (n + 1), (-1) …
· 使用定理 `ContinuousAlternatingMap.compContinuousLinearMapCLM_apply`：∀ {𝕜 : Type u
_1} {E : Type u_2} {F : Type u_3} {ι : Type u_4} [inst : NormedField 𝕜] [inst_1 
: AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E…

--- 原说明 ---
The derivative of `compContinuousLinearMap` can be represented
in terms of `alternatizeUncurryFinCLM`.
-/
theorem fderivCompContinuousLinearMap_eq_alternatizeUncurryFin (f : F [⋀^Fin (n + 1)]→L[𝕜] G)
    (g : E →L[𝕜] F) :
    f.fderivCompContinuousLinearMap g = alternatizeUncurryFinCLM 𝕜 E G ∘L
      ((compContinuousLinearMapCLM g ∘L f.curryLeft).postcomp E) := by
  ext dg v
  have (i j : Fin (n + 1)) :
      i.insertNth (α := fun _ ↦ E →L[𝕜] F) dg (fun _ ↦ g) j (v j) =
        i.insertNth (α := fun _ ↦ F) (dg (v i)) (g ∘ i.removeNth v) j := by
    cases j using i.succAboveCases <;> simp [Fin.removeNth]
  simp [alternatizeUncurryFin_apply, ← Fin.insertNth_removeNth, Fin.removeNth_fun_const,
    ← map_insertNth, this]

/-- `alternatizeUncurryFin` of `fderivCompContinuousLinearMap f g`
composed with a symmetric bilinear map is zero. -/
/-
**ContinuousAlternatingMap.alternatizeUncurryFin_fderivCompContinuousLinearMap_e
q_zero** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlternatingMap`。
形式化陈述：alternatizeUncurryFin_fderivCompContinuousLinearMap_eq_zero (f : F [⋀^Fin 
n]->L[𝕜] G) (g : E ->L[𝕜] F) {h : E ->L[𝕜] E ->L[𝕜] F} (hsymm : forall x y, h x 
y = h y x) : alternatizeUncurryFin (f.fderivCompContinuousLinearMap g ∘L h) = 0
参数：f : F [⋀^Fin n]->L[𝕜] G；g : E ->L[𝕜] F；hsymm : forall x y, h x y = h y x。
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
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用引理 `ContinuousAlternatingMap.fderivCompContinuousLinearMap_of_isEmpty`：fderi
vCompContinuousLinearMap_of_isEmpty [IsEmpty ι] : fderivCompContinuousLinearMap 
(ι
· 使用定理 `ContinuousLinearMap.zero_comp`：zero_comp (f : M₁ ->SL[σ₁₂] M₂) : (0 : M₂
 ->SL[σ₂₃] M₃) ∘SL f = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `ContinuousAlternatingMap.instSMulCommClass`：∀ {M : Type u_2} {N : Type u
_4} {ι : Type u_6} [inst : AddCommMonoid M] [inst_1 : TopologicalSpace M]   [ins
t_2 : AddCommMonoid N] [inst_3 :…
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousAlternatingMap.fderivCompContinuousLinearMap_eq_alternatizeUnc
urryFin`：fderivCompContinuousLinearMap_eq_alternatizeUncurryFin (f : F [⋀^Fin (n
 + 1)]->L[𝕜] G) (g : E ->L[𝕜] F) : f.fderivCompContinuousLinearMap g …
· 使用定理 `ContinuousLinearMap.comp_assoc`：comp_assoc {R₄ : Type*} [Semiring R₄] [M
odule R₄ M₄] {σ₁₄ : R₁ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₃₄ : R₃ ->+* R₄} [RingHomCo
mpTriple σ₁₃ σ₃₄ σ₁₄…
· 使用定理 `ContinuousAlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinCLM_
comp_of_symmetric`：alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_of_symmet
ric {f : E ->L[𝕜] E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F} (hf : forall x y, f x y = f y x…
· 使用定理 `ContinuousAlternatingMap.ext`：ext {f g : M [⋀^ι]->L[R] N} (H : forall x,
 f x = g x) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ContinuousLinearMap.postcomp_apply`：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2} {𝕜
₃ : Type u_3} [inst : NormedField 𝕜₁] [inst_1 : NormedField 𝕜₂]   [inst_2 : Norm
edField 𝕜₃] {σ : 𝕜₁ →+* …
· 使用定理 `ContinuousAlternatingMap.compContinuousLinearMapCLM_apply`：∀ {𝕜 : Type u
_1} {E : Type u_2} {F : Type u_3} {ι : Type u_4} [inst : NormedField 𝕜] [inst_1 
: AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E…

--- 原说明 ---
`alternatizeUncurryFin` of `fderivCompContinuousLinearMap f g`
composed with a symmetric bilinear map is zero.
-/
theorem alternatizeUncurryFin_fderivCompContinuousLinearMap_eq_zero (f : F [⋀^Fin n]→L[𝕜] G)
    (g : E →L[𝕜] F) {h : E →L[𝕜] E →L[𝕜] F} (hsymm : ∀ x y, h x y = h y x) :
    alternatizeUncurryFin (f.fderivCompContinuousLinearMap g ∘L h) = 0 := by
  cases n with
  | zero =>
    simp [fderivCompContinuousLinearMap_of_isEmpty, ← alternatizeUncurryFinCLM_apply]
  | succ n =>
    rw [fderivCompContinuousLinearMap_eq_alternatizeUncurryFin,
      ContinuousLinearMap.comp_assoc,
      alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_of_symmetric]
    intro x y
    ext v
    simp [hsymm]

end ContinuousAlternatingMap

