/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Analysis.InnerProductSpace.CanonicalTensor

/-! # Type classes for derivatives and the Laplacian

In this file we define notation type classes for line derivatives, also known as partial
derivatives, and for the Laplacian.

Moreover, we provide type-classes that encode the linear structure.
We also define the iterated line derivative and prove elementary properties.
We define a Laplacian based on the sum of second derivatives formula and prove that the Laplacian
thus defined is independent of the choice of basis.

Currently, this type class is only used by Schwartz functions. Future uses include derivatives on
test functions, distributions, tempered distributions, and Sobolev spaces (and other generalized
function spaces).
-/

@[expose] public noncomputable section

universe u' u v w

variable {ι ι' 𝕜 R V E F V₁ V₂ V₃ : Type*}

/-! ## Line derivative -/

open Fin

/--
Definition of `LineDeriv` / `LineDeriv` 的定义

English:
class LineDeriv
  parameters: (V : Type u) (E : Type v) (F : outParam (Type w))
  axioms and operations (1):
    - lineDerivOp : V -> E -> F

中文:
类 LineDeriv
  参数: (V : 类型u) (E : 类型v) (F : outParam (类型 w))
  公理与运算 (1 个):
    - lineDerivOp : V -> E -> F
-/
class LineDeriv (V : Type u) (E : Type v) (F : outParam (Type w)) where
  /-- `∂_{v} f` is the line derivative of `f` in direction `v`. The meaning of this notation is
  type-dependent. -/
  lineDerivOp : V -> E -> F

namespace LineDeriv

@[inherit_doc] scoped notation "∂_{" v "}" => LineDeriv.lineDerivOp v

variable {V E : Type*} [LineDeriv V E E]

/--
Definition of `iteratedLineDerivOp` / `iteratedLineDerivOp` 的定义

English:
definition iteratedLineDerivOp
  signature: {n : Nat}
  body: Nat.recOn n (fun _ => id) (fun _ rec y => LineDeriv.lineDerivOp (y 0) ∘ rec (tail y))

@[inherit_doc] scoped notation "∂^{" v "}" => LineDeriv.iteratedLineDerivOp v

@[simp]

中文:
定义 iteratedLineDerivOp
  签名: {n : 自然数}
  定义体: Nat.recOn n (fun _ => id) (fun _ rec y => LineDeriv.lineDerivOp (y 0) ∘ rec (tail y))

@[inherit_doc] scoped notation "∂^{" v "}" => LineDeriv.iteratedLineDerivOp v

@[simp]

Depends on / 依赖: LineDeriv, LineDeriv.lineDerivOp, Nat.recOn, lineDerivOp
-/
def iteratedLineDerivOp {n : Nat} : (Fin n -> V) -> E -> E :=
  Nat.recOn n (fun _ => id) (fun _ rec y => LineDeriv.lineDerivOp (y 0) ∘ rec (tail y))

@[inherit_doc] scoped notation "∂^{" v "}" => LineDeriv.iteratedLineDerivOp v

@[simp]
/--
theorem `iteratedLineDerivOp_fin_zero` / 定理 `iteratedLineDerivOp_fin_zero`

English:
theorem iteratedLineDerivOp_fin_zero
  given: (m : Fin 0 -> V) (f : E)
  statement: ∂^{m} f = f
  proof: rfl

@[simp]

中文:
定理 iteratedLineDerivOp_fin_zero
  条件: (m : 有限集 0 -> V) (f : E)
  结论: ∂^{m} f = f
  证明: rfl

@[simp]
-/
theorem iteratedLineDerivOp_fin_zero (m : Fin 0 -> V) (f : E) : ∂^{m} f = f :=
  rfl

@[simp]
/--
theorem `iteratedLineDerivOp_one` / 定理 `iteratedLineDerivOp_one`

English:
theorem iteratedLineDerivOp_one
  given: (m : Fin 1 -> V) (f : E)
  statement: ∂^{m} f = ∂_{m 0} f
  proof: rfl

中文:
定理 iteratedLineDerivOp_one
  条件: (m : 有限集 1 -> V) (f : E)
  结论: ∂^{m} f = ∂_{m 0} f
  证明: rfl
-/
theorem iteratedLineDerivOp_one (m : Fin 1 -> V) (f : E) : ∂^{m} f = ∂_{m 0} f :=
  rfl

/--
theorem `iteratedLineDerivOp_succ_left` / 定理 `iteratedLineDerivOp_succ_left`

English:
theorem iteratedLineDerivOp_succ_left
  given: {n : Nat} (m : Fin (n + 1) -> V) (f : E)
  proof: rfl

中文:
定理 iteratedLineDerivOp_succ_left
  条件: {n : 自然数} (m : 有限集 (n + 1) -> V) (f : E)
  证明: rfl
-/
theorem iteratedLineDerivOp_succ_left {n : Nat} (m : Fin (n + 1) -> V) (f : E) :
    ∂^{m} f = ∂_{m 0} (∂^{tail m} f) :=
  rfl

/--
theorem `iteratedLineDerivOp_succ_right` / 定理 `iteratedLineDerivOp_succ_right`

English:
theorem iteratedLineDerivOp_succ_right
  given: {n : Nat} (m : Fin (n + 1) -> V) (f : E)
  proof: by
  induction n with
  | zero => rfl
  -- The proof is `∂^{n + 2} = ∂ ∂^{n + 1} = ∂ ∂^n ∂ = ∂^{n+1} ∂`
  | succ n IH =>
    have hmzero : init m 0 = m 0 := by simp only [init_def, castSucc_zero]
    have hmtail : tail m (last n) = m (last n.succ) := by
      simp only [tail_def, succ_last]
    calc
      _ = ∂_{m 0} (∂^{tail m} f) := iteratedLineDerivOp_succ_left _ _
      _ = ∂_{m 0} (∂^{init <| tail m} (∂_{tail m <| last n} f)) := by
        congr 1
        exact IH _
      _ = _ := by
        rw [hmtail]; rw [iteratedLineDerivOp_succ_left]; rw [hmzero]; rw [tail_init_eq_init_tail]

@[simp]

中文:
定理 iteratedLineDerivOp_succ_right
  条件: {n : 自然数} (m : 有限集 (n + 1) -> V) (f : E)
  证明: by
  induction n with
  | zero => rfl
  -- The proof is `∂^{n + 2} = ∂ ∂^{n + 1} = ∂ ∂^n ∂ = ∂^{n+1} ∂`
  | succ n IH =>
    have hmzero : init m 0 = m 0 := by simp only [init_def, castSucc_zero]
    have hmtail : tail m (last n) = m (last n.succ) := by
      simp only [tail_def, succ_last]
    calc
      _ = ∂_{m 0} (∂^{tail m} f) := iteratedLineDerivOp_succ_left _ _
      _ = ∂_{m 0} (∂^{init <| tail m} (∂_{tail m <| last n} f)) := by
        congr 1
        exact IH _
      _ = _ := by
        rw [hmtail]; rw [iteratedLineDerivOp_succ_left]; rw [hmzero]; rw [tail_init_eq_init_tail]

@[simp]
-/
theorem iteratedLineDerivOp_succ_right {n : Nat} (m : Fin (n + 1) -> V) (f : E) :
    ∂^{m} f = ∂^{init m} (∂_{m (last n)} f) := by
  induction n with
  | zero => rfl
  -- The proof is `∂^{n + 2} = ∂ ∂^{n + 1} = ∂ ∂^n ∂ = ∂^{n+1} ∂`
  | succ n IH =>
    have hmzero : init m 0 = m 0 := by simp only [init_def, castSucc_zero]
    have hmtail : tail m (last n) = m (last n.succ) := by
      simp only [tail_def, succ_last]
    calc
      _ = ∂_{m 0} (∂^{tail m} f) := iteratedLineDerivOp_succ_left _ _
      _ = ∂_{m 0} (∂^{init <| tail m} (∂_{tail m <| last n} f)) := by
        congr 1
        exact IH _
      _ = _ := by
        rw [hmtail]; rw [iteratedLineDerivOp_succ_left]; rw [hmzero]; rw [tail_init_eq_init_tail]

@[simp]
/--
theorem `iteratedLineDerivOp_const_eq_iter_lineDerivOp` / 定理 `iteratedLineDerivOp_const_eq_iter_lineDerivOp`

English:
theorem iteratedLineDerivOp_const_eq_iter_lineDerivOp
  given: (n : Nat) (y : V) (f : E)
  proof: by
  induction n with
  | zero => rfl
  | succ n IH =>
    rw [iteratedLineDerivOp_succ_left]; rw [Function.iterate_succ_apply']
    congr

中文:
定理 iteratedLineDerivOp_const_eq_iter_lineDerivOp
  条件: (n : 自然数) (y : V) (f : E)
  证明: by
  induction n with
  | zero => rfl
  | succ n IH =>
    rw [iteratedLineDerivOp_succ_left]; rw [Function.iterate_succ_apply']
    congr

Depends on / 依赖: Function, Function.iterate_succ_apply, iterate_succ_apply, iteratedLineDerivOp_succ_left
-/
theorem iteratedLineDerivOp_const_eq_iter_lineDerivOp (n : Nat) (y : V) (f : E) :
    ∂^{fun (_ : Fin n) => y} f = ∂_{y}^[n] f := by
  induction n with
  | zero => rfl
  | succ n IH =>
    rw [iteratedLineDerivOp_succ_left]; rw [Function.iterate_succ_apply']
    congr

end LineDeriv

open LineDeriv

/--
Definition of `LineDerivAdd` / `LineDerivAdd` 的定义

English:
class LineDerivAdd
  parameters: (V : Type u) (E : Type v) (F : outParam (Type w))
  axioms and operations (2):
    - lineDerivOp_add((v : V) (x y : E)) : ∂_{v} (x + y) = ∂_{v} x + ∂_{v} y
    - lineDerivOp_left_add((v w : V) (x : E)) : ∂_{v + w} x = ∂_{v} x + ∂_{w} x

中文:
类 LineDerivAdd
  参数: (V : 类型u) (E : 类型v) (F : outParam (类型 w))
  公理与运算 (2 个):
    - lineDerivOp_add((v : V) (x y : E)) : ∂_{v} (x + y) = ∂_{v} x + ∂_{v} y
    - lineDerivOp_left_add((v w : V) (x : E)) : ∂_{v + w} x = ∂_{v} x + ∂_{w} x
-/
class LineDerivAdd (V : Type u) (E : Type v) (F : outParam (Type w))
    [AddCommGroup V] [AddCommGroup E] [AddCommGroup F] [LineDeriv V E F] where
  lineDerivOp_add (v : V) (x y : E) : ∂_{v} (x + y) = ∂_{v} x + ∂_{v} y
  lineDerivOp_left_add (v w : V) (x : E) : ∂_{v + w} x = ∂_{v} x + ∂_{w} x

/--
Definition of `LineDerivSMul` / `LineDerivSMul` 的定义

English:
class LineDerivSMul
  parameters: (R : Type*) (V : Type u) (E : Type v) (F : outParam (Type w))
  axioms and operations (1):
    - lineDerivOp_smul((v : V) (r : R) (x : E)) : ∂_{v} (r • x) = r • ∂_{v} x

中文:
类 LineDerivSMul
  参数: (R : 类型) (V : 类型u) (E : 类型v) (F : outParam (类型 w))
  公理与运算 (1 个):
    - lineDerivOp_smul((v : V) (r : R) (x : E)) : ∂_{v} (r • x) = r • ∂_{v} x
-/
class LineDerivSMul (R : Type*) (V : Type u) (E : Type v) (F : outParam (Type w))
    [SMul R E] [SMul R F] [LineDeriv V E F] where
  lineDerivOp_smul (v : V) (r : R) (x : E) : ∂_{v} (r • x) = r • ∂_{v} x

/--
Definition of `LineDerivLeftSMul` / `LineDerivLeftSMul` 的定义

English:
class LineDerivLeftSMul
  parameters: (R : Type*) (V : Type u) (E : Type v) (F : outParam (Type w))
  axioms and operations (1):
    - lineDerivOp_left_smul((r : R) (v : V) (x : E)) : ∂_{r • v} x = r • ∂_{v} x

中文:
类 LineDerivLeftSMul
  参数: (R : 类型) (V : 类型u) (E : 类型v) (F : outParam (类型 w))
  公理与运算 (1 个):
    - lineDerivOp_left_smul((r : R) (v : V) (x : E)) : ∂_{r • v} x = r • ∂_{v} x
-/
class LineDerivLeftSMul (R : Type*) (V : Type u) (E : Type v) (F : outParam (Type w))
    [SMul R V] [SMul R F] [LineDeriv V E F] where
  lineDerivOp_left_smul (r : R) (v : V) (x : E) : ∂_{r • v} x = r • ∂_{v} x

/--
Definition of `ContinuousLineDeriv` / `ContinuousLineDeriv` 的定义

English:
class ContinuousLineDeriv
  parameters: (V : Type u) (E : Type v) (F : outParam (Type w))
  axioms and operations (1):
    - continuous_lineDerivOp((v : V)) : Continuous (∂_{v} : E -> F)

中文:
类 余ntinuousLineDeriv
  参数: (V : 类型u) (E : 类型v) (F : outParam (类型 w))
  公理与运算 (1 个):
    - continuous_lineDerivOp((v : V)) : 连续 (∂_{v} : E -> F)
-/
class ContinuousLineDeriv (V : Type u) (E : Type v) (F : outParam (Type w))
    [TopologicalSpace E] [TopologicalSpace F] [LineDeriv V E F] where
  continuous_lineDerivOp (v : V) : Continuous (∂_{v} : E -> F)

attribute [fun_prop] ContinuousLineDeriv.continuous_lineDerivOp

namespace LineDeriv

export LineDerivAdd (lineDerivOp_add)
export LineDerivAdd (lineDerivOp_left_add)
export LineDerivSMul (lineDerivOp_smul)
export LineDerivLeftSMul (lineDerivOp_left_smul)
export ContinuousLineDeriv (continuous_lineDerivOp)

section lineDerivOp

variable [AddCommGroup V] [AddCommGroup E] [AddCommGroup F] [LineDeriv V E F] [LineDerivAdd V E F]

@[simp]
/--
theorem `lineDerivOp_zero` / 定理 `lineDerivOp_zero`

English:
theorem lineDerivOp_zero
  given: (v : V)
  statement: ∂_{v} (0 : E) = 0
  proof: map_zero (AddMonoidHom.mk' ∂_{v} (lineDerivOp_add v))

@[simp]

中文:
定理 lineDerivOp_zero
  条件: (v : V)
  结论: ∂_{v} (0 : E) = 0
  证明: map_zero (AddMonoidHom.mk' ∂_{v} (lineDerivOp_add v))

@[simp]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mk, lineDerivOp_add, map_zero
-/
theorem lineDerivOp_zero (v : V) : ∂_{v} (0 : E) = 0 :=
  map_zero (AddMonoidHom.mk' ∂_{v} (lineDerivOp_add v))

@[simp]
/--
theorem `lineDerivOp_neg` / 定理 `lineDerivOp_neg`

English:
theorem lineDerivOp_neg
  given: (v : V) (x : E)
  statement: ∂_{v} (-x) = - ∂_{v} x
  proof: map_neg (AddMonoidHom.mk' ∂_{v} (lineDerivOp_add v)) x

@[simp]

中文:
定理 lineDerivOp_neg
  条件: (v : V) (x : E)
  结论: ∂_{v} (-x) = - ∂_{v} x
  证明: map_neg (AddMonoidHom.mk' ∂_{v} (lineDerivOp_add v)) x

@[simp]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mk, lineDerivOp_add, map_neg
-/
theorem lineDerivOp_neg (v : V) (x : E) : ∂_{v} (-x) = - ∂_{v} x :=
  map_neg (AddMonoidHom.mk' ∂_{v} (lineDerivOp_add v)) x

@[simp]
/--
theorem `lineDerivOp_sum` / 定理 `lineDerivOp_sum`

English:
theorem lineDerivOp_sum
  given: (v : V) (f : ι -> E) (s : Finset ι)
  proof: map_sum (AddMonoidHom.mk' ∂_{v} (lineDerivOp_add v)) f s

@[simp]

中文:
定理 lineDerivOp_sum
  条件: (v : V) (f : ι -> E) (s : 有限集 ι)
  证明: map_sum (AddMonoidHom.mk' ∂_{v} (lineDerivOp_add v)) f s

@[simp]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mk, lineDerivOp_add, map_sum
-/
theorem lineDerivOp_sum (v : V) (f : ι -> E) (s : Finset ι) :
    ∂_{v} (∑ i in s, f i) = ∑ i in s, ∂_{v} (f i) :=
  map_sum (AddMonoidHom.mk' ∂_{v} (lineDerivOp_add v)) f s

@[simp]
/--
theorem `lineDerivOp_left_zero` / 定理 `lineDerivOp_left_zero`

English:
theorem lineDerivOp_left_zero
  given: (x : E)
  statement: ∂_{(0 : V)} x = 0
  proof: map_zero (AddMonoidHom.mk' (∂_{·} x) (lineDerivOp_left_add · · x))

@[simp]

中文:
定理 lineDerivOp_left_zero
  条件: (x : E)
  结论: ∂_{(0 : V)} x = 0
  证明: map_zero (AddMonoidHom.mk' (∂_{·} x) (lineDerivOp_left_add · · x))

@[simp]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mk, lineDerivOp_left_add, map_zero
-/
theorem lineDerivOp_left_zero (x : E) : ∂_{(0 : V)} x = 0 :=
  map_zero (AddMonoidHom.mk' (∂_{·} x) (lineDerivOp_left_add · · x))

@[simp]
/--
theorem `lineDerivOp_left_neg` / 定理 `lineDerivOp_left_neg`

English:
theorem lineDerivOp_left_neg
  given: (v : V) (x : E)
  statement: ∂_{-v} x = - ∂_{v} x
  proof: map_neg (AddMonoidHom.mk' (∂_{·} x) (lineDerivOp_left_add · · x)) v

@[simp]

中文:
定理 lineDerivOp_left_neg
  条件: (v : V) (x : E)
  结论: ∂_{-v} x = - ∂_{v} x
  证明: map_neg (AddMonoidHom.mk' (∂_{·} x) (lineDerivOp_left_add · · x)) v

@[simp]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mk, lineDerivOp_left_add, map_neg
-/
theorem lineDerivOp_left_neg (v : V) (x : E) : ∂_{-v} x = - ∂_{v} x :=
  map_neg (AddMonoidHom.mk' (∂_{·} x) (lineDerivOp_left_add · · x)) v

@[simp]
/--
theorem `lineDerivOp_left_sum` / 定理 `lineDerivOp_left_sum`

English:
theorem lineDerivOp_left_sum
  given: (f : ι -> V) (x : E) (s : Finset ι)
  proof: map_sum (AddMonoidHom.mk' (∂_{·} x) (lineDerivOp_left_add · · x)) f s

中文:
定理 lineDerivOp_left_sum
  条件: (f : ι -> V) (x : E) (s : 有限集 ι)
  证明: map_sum (AddMonoidHom.mk' (∂_{·} x) (lineDerivOp_left_add · · x)) f s

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mk, lineDerivOp_left_add, map_sum
-/
theorem lineDerivOp_left_sum (f : ι -> V) (x : E) (s : Finset ι) :
    ∂_{∑ i in s, f i} x = ∑ i in s, ∂_{f i} x :=
  map_sum (AddMonoidHom.mk' (∂_{·} x) (lineDerivOp_left_add · · x)) f s

end lineDerivOp

section lineDerivOpCLM

variable [Ring R] [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
  [TopologicalSpace E] [TopologicalSpace F] [AddCommGroup V]
  [LineDeriv V E F] [LineDerivAdd V E F] [LineDerivSMul R V E F] [ContinuousLineDeriv V E F]

variable (R E) in
/--
Definition of `lineDerivOpCLM` / `lineDerivOpCLM` 的定义

English:
definition lineDerivOpCLM
  signature: (m : V)
  body: ∂_{m}
  map_add' := lineDerivOp_add m
  map_smul' := lineDerivOp_smul m

@[simp]

中文:
定义 lineDerivOpCLM
  签名: (m : V)
  定义体: ∂_{m}
  map_add' := lineDerivOp_add m
  map_smul' := lineDerivOp_smul m

@[simp]
-/
def lineDerivOpCLM (m : V) : E ->L[R] F where
  toFun := ∂_{m}
  map_add' := lineDerivOp_add m
  map_smul' := lineDerivOp_smul m

@[simp]
/--
theorem `lineDerivOpCLM_apply` / 定理 `lineDerivOpCLM_apply`

English:
theorem lineDerivOpCLM_apply
  given: (m : V) (x : E)
  proof: rfl

中文:
定理 lineDerivOpCLM_apply
  条件: (m : V) (x : E)
  证明: rfl
-/
theorem lineDerivOpCLM_apply (m : V) (x : E) :
    lineDerivOpCLM R E m x = ∂_{m} x := rfl

end lineDerivOpCLM

section iteratedLineDerivOp

variable [LineDeriv V E E]
variable {n : Nat} (m : Fin n -> V)

section add

variable [AddCommGroup V] [AddCommGroup E] [LineDerivAdd V E E]

/--
theorem `iteratedLineDerivOp_add` / 定理 `iteratedLineDerivOp_add`

English:
theorem iteratedLineDerivOp_add
  given: (x y : E)
  proof: by
  induction n with
  | zero =>
    simp
  | succ n IH =>
    simp_rw [iteratedLineDerivOp_succ_left, IH, lineDerivOp_add]

@[simp]

中文:
定理 iteratedLineDerivOp_add
  条件: (x y : E)
  证明: by
  induction n with
  | zero =>
    simp
  | succ n IH =>
    simp_rw [iteratedLineDerivOp_succ_left, IH, lineDerivOp_add]

@[simp]

Depends on / 依赖: iteratedLineDerivOp_succ_left, lineDerivOp_add, simp_rw
-/
theorem iteratedLineDerivOp_add (x y : E) :
    ∂^{m} (x + y) = ∂^{m} x + ∂^{m} y := by
  induction n with
  | zero =>
    simp
  | succ n IH =>
    simp_rw [iteratedLineDerivOp_succ_left, IH, lineDerivOp_add]

@[simp]
/--
theorem `iteratedLineDerivOp_zero` / 定理 `iteratedLineDerivOp_zero`

English:
theorem iteratedLineDerivOp_zero
  statement: ∂^{m} (0 : E) = 0
  proof: map_zero (AddMonoidHom.mk' ∂^{m} (iteratedLineDerivOp_add m))

@[simp]

中文:
定理 iteratedLineDerivOp_zero
  结论: ∂^{m} (0 : E) = 0
  证明: map_zero (AddMonoidHom.mk' ∂^{m} (iteratedLineDerivOp_add m))

@[simp]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mk, iteratedLineDerivOp_add, map_zero
-/
theorem iteratedLineDerivOp_zero : ∂^{m} (0 : E) = 0 :=
  map_zero (AddMonoidHom.mk' ∂^{m} (iteratedLineDerivOp_add m))

@[simp]
/--
theorem `iteratedLineDerivOp_neg` / 定理 `iteratedLineDerivOp_neg`

English:
theorem iteratedLineDerivOp_neg
  given: (x : E)
  statement: ∂^{m} (-x) = - ∂^{m} x
  proof: map_neg (AddMonoidHom.mk' ∂^{m} (iteratedLineDerivOp_add m)) x

@[simp]

中文:
定理 iteratedLineDerivOp_neg
  条件: (x : E)
  结论: ∂^{m} (-x) = - ∂^{m} x
  证明: map_neg (AddMonoidHom.mk' ∂^{m} (iteratedLineDerivOp_add m)) x

@[simp]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mk, iteratedLineDerivOp_add, map_neg
-/
theorem iteratedLineDerivOp_neg (x : E) : ∂^{m} (-x) = - ∂^{m} x :=
  map_neg (AddMonoidHom.mk' ∂^{m} (iteratedLineDerivOp_add m)) x

@[simp]
/--
theorem `iteratedLineDerivOp_sum` / 定理 `iteratedLineDerivOp_sum`

English:
theorem iteratedLineDerivOp_sum
  given: (f : ι -> E) (s : Finset ι)
  proof: map_sum (AddMonoidHom.mk' ∂^{m} (iteratedLineDerivOp_add m)) f s

中文:
定理 iteratedLineDerivOp_sum
  条件: (f : ι -> E) (s : 有限集 ι)
  证明: map_sum (AddMonoidHom.mk' ∂^{m} (iteratedLineDerivOp_add m)) f s

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mk, iteratedLineDerivOp_add, map_sum
-/
theorem iteratedLineDerivOp_sum (f : ι -> E) (s : Finset ι) :
    ∂^{m} (∑ i in s, f i) = ∑ i in s, ∂^{m} (f i) :=
  map_sum (AddMonoidHom.mk' ∂^{m} (iteratedLineDerivOp_add m)) f s

end add

/--
theorem `iteratedLineDerivOp_smul` / 定理 `iteratedLineDerivOp_smul`

English:
theorem iteratedLineDerivOp_smul
  given: [SMul R E] [LineDerivSMul R V E E] (r : R) (x : E)
  proof: by
  induction n with
  | zero =>
    simp
  | succ n IH =>
    simp_rw [iteratedLineDerivOp_succ_left, IH, lineDerivOp_smul]

中文:
定理 iteratedLineDerivOp_smul
  条件: [标量乘法 R E] [LineDerivSMul R V E E] (r : R) (x : E)
  证明: by
  induction n with
  | zero =>
    simp
  | succ n IH =>
    simp_rw [iteratedLineDerivOp_succ_left, IH, lineDerivOp_smul]

Depends on / 依赖: iteratedLineDerivOp_succ_left, lineDerivOp_smul, simp_rw
-/
theorem iteratedLineDerivOp_smul [SMul R E] [LineDerivSMul R V E E] (r : R) (x : E) :
    ∂^{m} (r • x) = r • ∂^{m} x := by
  induction n with
  | zero =>
    simp
  | succ n IH =>
    simp_rw [iteratedLineDerivOp_succ_left, IH, lineDerivOp_smul]

variable [TopologicalSpace E]

@[fun_prop]
/--
theorem `continuous_iteratedLineDerivOp` / 定理 `continuous_iteratedLineDerivOp`

English:
theorem continuous_iteratedLineDerivOp
  given: [ContinuousLineDeriv V E E] {n : Nat} (m : Fin n -> V)
  proof: by
  induction n with
  | zero =>
    exact continuous_id
  | succ n IH =>
    exact (continuous_lineDerivOp _).comp (IH _)

中文:
定理 continuous_iteratedLineDerivOp
  条件: [余ntinuousLineDeriv V E E] {n : 自然数} (m : 有限集 n -> V)
  证明: by
  induction n with
  | zero =>
    exact continuous_id
  | succ n IH =>
    exact (continuous_lineDerivOp _).comp (IH _)

Depends on / 依赖: continuous_id, continuous_lineDerivOp
-/
theorem continuous_iteratedLineDerivOp [ContinuousLineDeriv V E E] {n : Nat} (m : Fin n -> V) :
    Continuous (∂^{m} : E -> E) := by
  induction n with
  | zero =>
    exact continuous_id
  | succ n IH =>
    exact (continuous_lineDerivOp _).comp (IH _)

variable [Ring R] [AddCommGroup V] [AddCommGroup E] [Module R E]
  [LineDerivAdd V E E] [LineDerivSMul R V E E] [ContinuousLineDeriv V E E]

variable (R E) in
/--
Definition of `iteratedLineDerivOpCLM` / `iteratedLineDerivOpCLM` 的定义

English:
definition iteratedLineDerivOpCLM
  signature: {n : Nat} (m : Fin n -> V)
  body: ∂^{m}
  map_add' := iteratedLineDerivOp_add m
  map_smul' := iteratedLineDerivOp_smul m

@[simp]

中文:
定义 iteratedLineDerivOpCLM
  签名: {n : 自然数} (m : 有限集 n -> V)
  定义体: ∂^{m}
  map_add' := iteratedLineDerivOp_add m
  map_smul' := iteratedLineDerivOp_smul m

@[simp]
-/
def iteratedLineDerivOpCLM {n : Nat} (m : Fin n -> V) : E ->L[R] E where
  toFun := ∂^{m}
  map_add' := iteratedLineDerivOp_add m
  map_smul' := iteratedLineDerivOp_smul m

@[simp]
/--
theorem `iteratedLineDerivOpCLM_apply` / 定理 `iteratedLineDerivOpCLM_apply`

English:
theorem iteratedLineDerivOpCLM_apply
  given: {n : Nat} (m : Fin n -> V) (x : E)
  proof: rfl

中文:
定理 iteratedLineDerivOpCLM_apply
  条件: {n : 自然数} (m : 有限集 n -> V) (x : E)
  证明: rfl
-/
theorem iteratedLineDerivOpCLM_apply {n : Nat} (m : Fin n -> V) (x : E) :
    iteratedLineDerivOpCLM R E m x = ∂^{m} x := rfl

end iteratedLineDerivOp

end LineDeriv

/-! ## Laplacian -/

/--
Definition of `Laplacian` / `Laplacian` 的定义

English:
class Laplacian
  parameters: (E : Type v) (F : outParam (Type w))
  axioms and operations (1):
    - laplacian : E -> F

中文:
类 Laplace算子
  参数: (E : 类型v) (F : outParam (类型 w))
  公理与运算 (1 个):
    - laplacian : E -> F
-/
class Laplacian (E : Type v) (F : outParam (Type w)) where
  /-- `Δ f` is the Laplacian of `f`. The meaning of this notation is type-dependent. -/
  laplacian : E -> F

namespace Laplacian

@[inherit_doc] scoped notation "Δ" => Laplacian.laplacian

end Laplacian

namespace LineDeriv

variable [LineDeriv E V₁ V₂] [LineDeriv E V₂ V₃]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃]

/-! ## Laplacian of `LineDeriv` -/

section TensorProduct

variable [CommRing R] [AddCommGroup E] [Module R E]
  [Module R V₂] [Module R V₃]
  [LineDerivAdd E V₂ V₃] [LineDerivAdd E V₁ V₂]
  [LineDerivSMul R E V₂ V₃] [LineDerivLeftSMul R E V₁ V₂] [LineDerivLeftSMul R E V₂ V₃]

open InnerProductSpace TensorProduct

variable (R) in
/--
Definition of `bilinearLineDerivTwo` / `bilinearLineDerivTwo` 的定义

English:
definition bilinearLineDerivTwo
  signature: (f : V₁)
  body: LinearMap.mk₂ R (∂_{·} <| ∂_{·} f) (by simp [lineDerivOp_left_add])
    (by simp [lineDerivOp_left_smul]) (by simp [lineDerivOp_left_add, lineDerivOp_add])
    (by simp [lineDerivOp_left_smul, lineDerivOp_smul])

中文:
定义 bilinearLineDerivTwo
  签名: (f : V₁)
  定义体: LinearMap.mk₂ R (∂_{·} <| ∂_{·} f) (by simp [lineDerivOp_left_add])
    (by simp [lineDerivOp_left_smul]) (by simp [lineDerivOp_left_add, lineDerivOp_add])
    (by simp [lineDerivOp_left_smul, lineDerivOp_smul])

Depends on / 依赖: LinearMap, LinearMap.mk, lineDerivOp_add, lineDerivOp_left_add, lineDerivOp_left_smul, lineDerivOp_smul
-/
def bilinearLineDerivTwo (f : V₁) : E ->ₗ[R] E ->ₗ[R] V₃ :=
  LinearMap.mk₂ R (∂_{·} <| ∂_{·} f) (by simp [lineDerivOp_left_add])
    (by simp [lineDerivOp_left_smul]) (by simp [lineDerivOp_left_add, lineDerivOp_add])
    (by simp [lineDerivOp_left_smul, lineDerivOp_smul])

variable (R) in
/--
Definition of `tensorLineDerivTwo` / `tensorLineDerivTwo` 的定义

English:
definition tensorLineDerivTwo
  signature: (f : V₁)
  body: lift (bilinearLineDerivTwo R f)

中文:
定义 tensorLineDerivTwo
  签名: (f : V₁)
  定义体: lift (bilinearLineDerivTwo R f)

Depends on / 依赖: bilinearLineDerivTwo
-/
def tensorLineDerivTwo (f : V₁) : E otimes[R] E ->ₗ[R] V₃ :=
  lift (bilinearLineDerivTwo R f)

/--
lemma `tensorLineDerivTwo_eq_lineDerivOp_lineDerivOp` / 引理 `tensorLineDerivTwo_eq_lineDerivOp_lineDerivOp`

English:
lemma tensorLineDerivTwo_eq_lineDerivOp_lineDerivOp
  given: (f : V₁) (v w : E)
  proof: lift.tmul _ _

中文:
引理 tensorLineDerivTwo_eq_lineDerivOp_lineDerivOp
  条件: (f : V₁) (v w : E)
  证明: lift.tmul _ _

Depends on / 依赖: lift.tmul
-/
lemma tensorLineDerivTwo_eq_lineDerivOp_lineDerivOp (f : V₁) (v w : E) :
    tensorLineDerivTwo R f (v otimesₜ[R] w) = ∂_{v} (∂_{w} f) := lift.tmul _ _

end TensorProduct

section InnerProductSpace

variable [NormedAddCommGroup E] [InnerProductSpace Real E] [FiniteDimensional Real E]

section LinearMap

variable [Module Real V₂] [Module Real V₃]
  [LineDerivAdd E V₁ V₂] [LineDerivAdd E V₂ V₃]
  [LineDerivSMul Real E V₂ V₃] [LineDerivLeftSMul Real E V₁ V₂] [LineDerivLeftSMul Real E V₂ V₃]

open TensorProduct InnerProductSpace

/--
theorem `tensorLineDerivTwo_canonicalCovariantTensor_eq_sum` / 定理 `tensorLineDerivTwo_canonicalCovariantTensor_eq_sum`

English:
theorem tensorLineDerivTwo_canonicalCovariantTensor_eq_sum
  statement: [Fintype ι] (v : OrthonormalBasis ι Real E)
  proof: by
  simp [InnerProductSpace.canonicalCovariantTensor_eq_sum E v,
    tensorLineDerivTwo_eq_lineDerivOp_lineDerivOp]

中文:
定理 tensorLineDerivTwo_canonicalCovariantTensor_eq_sum
  结论: [有限类型 ι] (v : 正交标准基 ι 实数 E)
  证明: by
  simp [InnerProductSpace.canonicalCovariantTensor_eq_sum E v,
    tensorLineDerivTwo_eq_lineDerivOp_lineDerivOp]

Depends on / 依赖: InnerProductSpace, InnerProductSpace.canonicalCovariantTensor_eq_sum, canonicalCovariantTensor_eq_sum, tensorLineDerivTwo_eq_lineDerivOp_lineDerivOp
-/
theorem tensorLineDerivTwo_canonicalCovariantTensor_eq_sum [Fintype ι] (v : OrthonormalBasis ι Real E)
    (f : V₁) : tensorLineDerivTwo Real f (canonicalCovariantTensor E) = ∑ i, ∂_{v i} (∂_{v i} f) := by
  simp [InnerProductSpace.canonicalCovariantTensor_eq_sum E v,
    tensorLineDerivTwo_eq_lineDerivOp_lineDerivOp]

end LinearMap

section ContinuousLinearMap

section definition

variable [CommRing R]
  [Module R V₁] [Module R V₂] [Module R V₃]
  [TopologicalSpace V₁] [TopologicalSpace V₂] [TopologicalSpace V₃] [IsTopologicalAddGroup V₃]
  [LineDerivAdd E V₁ V₂] [LineDerivSMul R E V₁ V₂] [ContinuousLineDeriv E V₁ V₂]
  [LineDerivAdd E V₂ V₃] [LineDerivSMul R E V₂ V₃] [ContinuousLineDeriv E V₂ V₃]

variable (R E V₁) in
/--
Definition of `laplacianCLM` / `laplacianCLM` 的定义

English:
definition laplacianCLM
  signature: : V₁ ->L[R] V₃
  body: ∑ i, lineDerivOpCLM R V₂ (stdOrthonormalBasis Real E i) ∘L
    lineDerivOpCLM R V₁ (stdOrthonormalBasis Real E i)

中文:
定义 laplacianCLM
  签名: : V₁ ->L[R] V₃
  定义体: ∑ i, lineDerivOpCLM R V₂ (stdOrthonormalBasis Real E i) ∘L
    lineDerivOpCLM R V₁ (stdOrthonormalBasis Real E i)

Depends on / 依赖: lineDerivOpCLM, stdOrthonormalBasis
-/
def laplacianCLM : V₁ ->L[R] V₃ :=
  ∑ i, lineDerivOpCLM R V₂ (stdOrthonormalBasis Real E i) ∘L
    lineDerivOpCLM R V₁ (stdOrthonormalBasis Real E i)

end definition

variable [Module Real V₁] [Module Real V₂] [Module Real V₃]
  [TopologicalSpace V₁] [TopologicalSpace V₂] [TopologicalSpace V₃] [IsTopologicalAddGroup V₃]
  [LineDerivAdd E V₁ V₂] [LineDerivSMul Real E V₁ V₂] [ContinuousLineDeriv E V₁ V₂]
  [LineDerivAdd E V₂ V₃] [LineDerivSMul Real E V₂ V₃] [ContinuousLineDeriv E V₂ V₃]
  [LineDerivLeftSMul Real E V₁ V₂] [LineDerivLeftSMul Real E V₂ V₃]

/--
theorem `laplacianCLM_eq_sum` / 定理 `laplacianCLM_eq_sum`

English:
theorem laplacianCLM_eq_sum
  given: [Fintype ι] (v : OrthonormalBasis ι Real E) (f : V₁)
  proof: by
  simp [laplacianCLM, ← tensorLineDerivTwo_canonicalCovariantTensor_eq_sum]

中文:
定理 laplacianCLM_eq_sum
  条件: [有限类型 ι] (v : 正交标准基 ι 实数 E) (f : V₁)
  证明: by
  simp [laplacianCLM, ← tensorLineDerivTwo_canonicalCovariantTensor_eq_sum]

Depends on / 依赖: laplacianCLM, tensorLineDerivTwo_canonicalCovariantTensor_eq_sum
-/
theorem laplacianCLM_eq_sum [Fintype ι] (v : OrthonormalBasis ι Real E) (f : V₁) :
    laplacianCLM Real E V₁ f = ∑ i, ∂_{v i} (∂_{v i} f) := by
  simp [laplacianCLM, ← tensorLineDerivTwo_canonicalCovariantTensor_eq_sum]

end ContinuousLinearMap

end InnerProductSpace

end LineDeriv
