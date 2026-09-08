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
The notation typeclass for the line derivative.
-/
/-
**LineDeriv** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u → Type v → outParam (Type w) → Type (max (max u v) w)
参数：Type w；max (max u v) w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The notation typeclass for the line derivative.
-/
class LineDeriv (V : Type u) (E : Type v) (F : outParam (Type w)) where
  /-- `∂_{v} f` is the line derivative of `f` in direction `v`. The meaning of this notation is
  type-dependent. -/
  lineDerivOp : V → E → F

namespace LineDeriv

@[inherit_doc] scoped notation "∂_{" v "}" => LineDeriv.lineDerivOp v

variable {V E : Type*} [LineDeriv V E E]

/-- `∂^{m} f` is the iterated line derivative of `f`, where `m` is a finite number of (different)
directions. -/
/-
**LineDeriv.iteratedLineDerivOp** 是 Mathlib 中的一个定义，位于命名空间 `LineDeriv`。
形式化陈述：iteratedLineDerivOp {n : Nat} : (Fin n -> V) -> E -> E
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)

--- 原说明 ---
`∂^{m} f` is the iterated line derivative of `f`, where `m` is a finite number o
f (different)
directions.
-/
def iteratedLineDerivOp {n : ℕ} : (Fin n → V) → E → E :=
  Nat.recOn n (fun _ ↦ id) (fun _ rec y ↦ LineDeriv.lineDerivOp (y 0) ∘ rec (tail y))

@[inherit_doc] scoped notation "∂^{" v "}" => LineDeriv.iteratedLineDerivOp v

@[simp]
/-
**LineDeriv.iteratedLineDerivOp_fin_zero** 是 Mathlib 中的一个定理，位于命名空间 `LineDeriv`。
形式化陈述：iteratedLineDerivOp_fin_zero (m : Fin 0 -> V) (f : E) : ∂^{m} f = f
参数：m : Fin 0 -> V；f : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iteratedLineDerivOp_fin_zero (m : Fin 0 → V) (f : E) : ∂^{m} f = f :=
  rfl

@[simp]
/-
**LineDeriv.iteratedLineDerivOp_one** 是 Mathlib 中的一个定理，位于命名空间 `LineDeriv`。
形式化陈述：iteratedLineDerivOp_one (m : Fin 1 -> V) (f : E) : ∂^{m} f = ∂_{m 0} f
参数：m : Fin 1 -> V；f : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iteratedLineDerivOp_one (m : Fin 1 → V) (f : E) : ∂^{m} f = ∂_{m 0} f :=
  rfl
/-
**LineDeriv.iteratedLineDerivOp_succ_left** 是 Mathlib 中的一个定理，位于命名空间 `LineDeriv`。
形式化陈述：iteratedLineDerivOp_succ_left {n : Nat} (m : Fin (n + 1) -> V) (f : E) : ∂
^{m} f = ∂_{m 0} (∂^{tail m} f)
参数：m : Fin (n + 1) -> V；f : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iteratedLineDerivOp_succ_left {n : ℕ} (m : Fin (n + 1) → V) (f : E) :
    ∂^{m} f = ∂_{m 0} (∂^{tail m} f) :=
  rfl
/-
**LineDeriv.iteratedLineDerivOp_succ_right** 是 Mathlib 中的一个定理，位于命名空间 `LineDeriv`
。
形式化陈述：iteratedLineDerivOp_succ_right {n : Nat} (m : Fin (n + 1) -> V) (f : E) : 
∂^{m} f = ∂^{init m} (∂_{m (last n)} f)
参数：m : Fin (n + 1) -> V；f : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LineDeriv.iteratedLineDerivOp_succ_left`：iteratedLineDerivOp_succ_left {
n : Nat} (m : Fin (n + 1) -> V) (f : E) : ∂^{m} f = ∂_{m 0} (∂^{tail m} f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.tail_init_eq_init_tail`：tail_init_eq_init_tail {β : Sort*} (q : Fin 
(n + 2) -> β) : tail (init q) = init (tail q)
-/
theorem iteratedLineDerivOp_succ_right {n : ℕ} (m : Fin (n + 1) → V) (f : E) :
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
        rw [hmtail, iteratedLineDerivOp_succ_left, hmzero, tail_init_eq_init_tail]

@[simp]
/-
**LineDeriv.iteratedLineDerivOp_const_eq_iter_lineDerivOp** 是 Mathlib 中的一个定理，位于命
名空间 `LineDeriv`。
形式化陈述：iteratedLineDerivOp_const_eq_iter_lineDerivOp (n : Nat) (y : V) (f : E) : 
∂^{fun (_ : Fin n) => y} f = ∂_{y}^[n] f
参数：n : Nat；y : V；f : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LineDeriv.iteratedLineDerivOp_succ_left`：iteratedLineDerivOp_succ_left {
n : Nat} (m : Fin (n + 1) -> V) (f : E) : ∂^{m} f = ∂_{m 0} (∂^{tail m} f)
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
-/
theorem iteratedLineDerivOp_const_eq_iter_lineDerivOp (n : ℕ) (y : V) (f : E) :
    ∂^{fun (_ : Fin n) ↦ y} f = ∂_{y}^[n] f := by
  induction n with
  | zero => rfl
  | succ n IH =>
    rw [iteratedLineDerivOp_succ_left, Function.iterate_succ_apply']
    congr

end LineDeriv

open LineDeriv

/--
The line derivative is additive, `∂_{v} (x + y) = ∂_{v} x + ∂_{v} y` for all `x y : E`
and `∂_{v + w} x = ∂_{v} x + ∂_{w} y` for all `v w : V`.

Note that `lineDeriv` on functions is not additive.
-/
/-
**LineDerivAdd** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(V : Type u) →   (E : Type v) →     (F : outParam (Type w)) → [AddCommGrou
p V] → [AddCommGroup E] → [AddCommGroup F] → [LineDeriv V E F] → Prop
参数：Type w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The line derivative is additive, `∂_{v} (x + y) = ∂_{v} x + ∂_{v} y` for all `x 
y : E`
and `∂_{v + w} x = ∂_{v} x + ∂_{w} y` for all `v w : V`.

Note that `lineDeriv` on functions is not additive.
-/
class LineDerivAdd (V : Type u) (E : Type v) (F : outParam (Type w))
    [AddCommGroup V] [AddCommGroup E] [AddCommGroup F] [LineDeriv V E F] where
  lineDerivOp_add (v : V) (x y : E) : ∂_{v} (x + y) = ∂_{v} x + ∂_{v} y
  lineDerivOp_left_add (v w : V) (x : E) : ∂_{v + w} x = ∂_{v} x + ∂_{w} x

/--
The line derivative commutes with scalar multiplication, `∂_{v} (r • x) = r • ∂_{v} x` for all
`r : R` and `x : E`.
-/
/-
**LineDerivSMul** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_11) →   (V : Type u) → (E : Type v) → (F : outParam (Type w)) 
→ [SMul R E] → [SMul R F] → [LineDeriv V E F] → Prop
参数：Type w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The line derivative commutes with scalar multiplication, `∂_{v} (r • x) = r • ∂_
{v} x` for all
`r : R` and `x : E`.
-/
class LineDerivSMul (R : Type*) (V : Type u) (E : Type v) (F : outParam (Type w))
    [SMul R E] [SMul R F] [LineDeriv V E F] where
  lineDerivOp_smul (v : V) (r : R) (x : E) : ∂_{v} (r • x) = r • ∂_{v} x

/--
The line derivative commutes with scalar multiplication, `∂_{r • v} x = r • ∂_{v} x` for all
`r : R` and `v : V`.
-/
/-
**LineDerivLeftSMul** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_11) →   (V : Type u) → (E : Type v) → (F : outParam (Type w)) 
→ [SMul R V] → [SMul R F] → [LineDeriv V E F] → Prop
参数：Type w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The line derivative commutes with scalar multiplication, `∂_{r • v} x = r • ∂_{v
} x` for all
`r : R` and `v : V`.
-/
class LineDerivLeftSMul (R : Type*) (V : Type u) (E : Type v) (F : outParam (Type w))
    [SMul R V] [SMul R F] [LineDeriv V E F] where
  lineDerivOp_left_smul (r : R) (v : V) (x : E) : ∂_{r • v} x = r • ∂_{v} x

/--
The line derivative is continuous.
-/
/-
**ContinuousLineDeriv** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(V : Type u) →   (E : Type v) → (F : outParam (Type w)) → [TopologicalSpac
e E] → [TopologicalSpace F] → [LineDeriv V E F] → Prop
参数：Type w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The line derivative is continuous.
-/
class ContinuousLineDeriv (V : Type u) (E : Type v) (F : outParam (Type w))
    [TopologicalSpace E] [TopologicalSpace F] [LineDeriv V E F] where
  continuous_lineDerivOp (v : V) : Continuous (∂_{v} : E → F)

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
/-
**LineDeriv.lineDerivOp_zero** 是 Mathlib 中的一个定理，位于命名空间 `LineDeriv`。
形式化陈述：lineDerivOp_zero (v : V) : ∂_{v} (0 : E) = 0
参数：v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `LineDerivAdd.lineDerivOp_add`：∀ {V : Type u} {E : Type v} {F : outParam 
(Type w)} {inst : AddCommGroup V} {inst_1 : AddCommGroup E}   {inst_2 : AddCommG
roup F} {inst_3 : …
-/
theorem lineDerivOp_zero (v : V) : ∂_{v} (0 : E) = 0 :=
  map_zero (AddMonoidHom.mk' ∂_{v} (lineDerivOp_add v))

@[simp]
/-
**LineDeriv.lineDerivOp_neg** 是 Mathlib 中的一个定理，位于命名空间 `LineDeriv`。
形式化陈述：lineDerivOp_neg (v : V) (x : E) : ∂_{v} (-x) = - ∂_{v} x
参数：v : V；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `LineDerivAdd.lineDerivOp_add`：∀ {V : Type u} {E : Type v} {F : outParam 
(Type w)} {inst : AddCommGroup V} {inst_1 : AddCommGroup E}   {inst_2 : AddCommG
roup F} {inst_3 : …
-/
theorem lineDerivOp_neg (v : V) (x : E) : ∂_{v} (-x) = - ∂_{v} x :=
  map_neg (AddMonoidHom.mk' ∂_{v} (lineDerivOp_add v)) x

@[simp]
/-
**LineDeriv.lineDerivOp_sum** 是 Mathlib 中的一个定理，位于命名空间 `LineDeriv`。
形式化陈述：lineDerivOp_sum (v : V) (f : ι -> E) (s : Finset ι) : ∂_{v} (∑ i in s, f i
) = ∑ i in s, ∂_{v} (f i)
参数：v : V；f : ι -> E；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `LineDerivAdd.lineDerivOp_add`：∀ {V : Type u} {E : Type v} {F : outParam 
(Type w)} {inst : AddCommGroup V} {inst_1 : AddCommGroup E}   {inst_2 : AddCommG
roup F} {inst_3 : …
-/
theorem lineDerivOp_sum (v : V) (f : ι → E) (s : Finset ι) :
    ∂_{v} (∑ i ∈ s, f i) = ∑ i ∈ s, ∂_{v} (f i) :=
  map_sum (AddMonoidHom.mk' ∂_{v} (lineDerivOp_add v)) f s

@[simp]
/-
**LineDeriv.lineDerivOp_left_zero** 是 Mathlib 中的一个定理，位于命名空间 `LineDeriv`。
形式化陈述：lineDerivOp_left_zero (x : E) : ∂_{(0 : V)} x = 0
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `LineDerivAdd.lineDerivOp_left_add`：∀ {V : Type u} {E : Type v} {F : outP
aram (Type w)} {inst : AddCommGroup V} {inst_1 : AddCommGroup E}   {inst_2 : Add
CommGroup F} {inst_3 : …
-/
theorem lineDerivOp_left_zero (x : E) : ∂_{(0 : V)} x = 0 :=
  map_zero (AddMonoidHom.mk' (∂_{·} x) (lineDerivOp_left_add · · x))

@[simp]
/-
**LineDeriv.lineDerivOp_left_neg** 是 Mathlib 中的一个定理，位于命名空间 `LineDeriv`。
形式化陈述：lineDerivOp_left_neg (v : V) (x : E) : ∂_{-v} x = - ∂_{v} x
参数：v : V；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `LineDerivAdd.lineDerivOp_left_add`：∀ {V : Type u} {E : Type v} {F : outP
aram (Type w)} {inst : AddCommGroup V} {inst_1 : AddCommGroup E}   {inst_2 : Add
CommGroup F} {inst_3 : …
-/
theorem lineDerivOp_left_neg (v : V) (x : E) : ∂_{-v} x = - ∂_{v} x :=
  map_neg (AddMonoidHom.mk' (∂_{·} x) (lineDerivOp_left_add · · x)) v

@[simp]
/-
**LineDeriv.lineDerivOp_left_sum** 是 Mathlib 中的一个定理，位于命名空间 `LineDeriv`。
形式化陈述：lineDerivOp_left_sum (f : ι -> V) (x : E) (s : Finset ι) : ∂_{∑ i in s, f 
i} x = ∑ i in s, ∂_{f i} x
参数：f : ι -> V；x : E；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `LineDerivAdd.lineDerivOp_left_add`：∀ {V : Type u} {E : Type v} {F : outP
aram (Type w)} {inst : AddCommGroup V} {inst_1 : AddCommGroup E}   {inst_2 : Add
CommGroup F} {inst_3 : …
-/
theorem lineDerivOp_left_sum (f : ι → V) (x : E) (s : Finset ι) :
    ∂_{∑ i ∈ s, f i} x = ∑ i ∈ s, ∂_{f i} x :=
  map_sum (AddMonoidHom.mk' (∂_{·} x) (lineDerivOp_left_add · · x)) f s

end lineDerivOp

section lineDerivOpCLM

variable [Ring R] [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
  [TopologicalSpace E] [TopologicalSpace F] [AddCommGroup V]
  [LineDeriv V E F] [LineDerivAdd V E F] [LineDerivSMul R V E F] [ContinuousLineDeriv V E F]

variable (R E) in
/-- The line derivative as a continuous linear map. -/
/-
**LineDeriv.lineDerivOpCLM** 是 Mathlib 中的一个定义，位于命名空间 `LineDeriv`。
形式化陈述：lineDerivOpCLM (m : V) : E ->L[R] F where toFun
参数：m : V。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LineDerivAdd.lineDerivOp_add`：∀ {V : Type u} {E : Type v} {F : outParam 
(Type w)} {inst : AddCommGroup V} {inst_1 : AddCommGroup E}   {inst_2 : AddCommG
roup F} {inst_3 : …

--- 原说明 ---
The line derivative as a continuous linear map.
-/
def lineDerivOpCLM (m : V) : E →L[R] F where
  toFun := ∂_{m}
  map_add' := lineDerivOp_add m
  map_smul' := lineDerivOp_smul m

@[simp]
/-
**LineDeriv.lineDerivOpCLM_apply** 是 Mathlib 中的一个定理，位于命名空间 `LineDeriv`。
形式化陈述：lineDerivOpCLM_apply (m : V) (x : E) : lineDerivOpCLM R E m x = ∂_{m} x
参数：m : V；x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lineDerivOpCLM_apply (m : V) (x : E) :
    lineDerivOpCLM R E m x = ∂_{m} x := rfl

end lineDerivOpCLM

section iteratedLineDerivOp

variable [LineDeriv V E E]
variable {n : ℕ} (m : Fin n → V)

section add

variable [AddCommGroup V] [AddCommGroup E] [LineDerivAdd V E E]

/-
**LineDeriv.iteratedLineDerivOp_add** 是 Mathlib 中的一个定理，位于命名空间 `LineDeriv`。
形式化陈述：iteratedLineDerivOp_add (x y : E) : ∂^{m} (x + y) = ∂^{m} x + ∂^{m} y
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LineDerivAdd.lineDerivOp_add`：∀ {V : Type u} {E : Type v} {F : outParam 
(Type w)} {inst : AddCommGroup V} {inst_1 : AddCommGroup E}   {inst_2 : AddCommG
roup F} {inst_3 : …
-/
theorem iteratedLineDerivOp_add (x y : E) :
    ∂^{m} (x + y) = ∂^{m} x + ∂^{m} y := by
  induction n with
  | zero =>
    simp
  | succ n IH =>
    simp_rw [iteratedLineDerivOp_succ_left, IH, lineDerivOp_add]

@[simp]
/-
**LineDeriv.iteratedLineDerivOp_zero** 是 Mathlib 中的一个定理，位于命名空间 `LineDeriv`。
形式化陈述：iteratedLineDerivOp_zero : ∂^{m} (0 : E) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `LineDeriv.iteratedLineDerivOp_add`：iteratedLineDerivOp_add (x y : E) : ∂
^{m} (x + y) = ∂^{m} x + ∂^{m} y
-/
theorem iteratedLineDerivOp_zero : ∂^{m} (0 : E) = 0 :=
  map_zero (AddMonoidHom.mk' ∂^{m} (iteratedLineDerivOp_add m))

@[simp]
/-
**LineDeriv.iteratedLineDerivOp_neg** 是 Mathlib 中的一个定理，位于命名空间 `LineDeriv`。
形式化陈述：iteratedLineDerivOp_neg (x : E) : ∂^{m} (-x) = - ∂^{m} x
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `LineDeriv.iteratedLineDerivOp_add`：iteratedLineDerivOp_add (x y : E) : ∂
^{m} (x + y) = ∂^{m} x + ∂^{m} y
-/
theorem iteratedLineDerivOp_neg (x : E) : ∂^{m} (-x) = - ∂^{m} x :=
  map_neg (AddMonoidHom.mk' ∂^{m} (iteratedLineDerivOp_add m)) x

@[simp]
/-
**LineDeriv.iteratedLineDerivOp_sum** 是 Mathlib 中的一个定理，位于命名空间 `LineDeriv`。
形式化陈述：iteratedLineDerivOp_sum (f : ι -> E) (s : Finset ι) : ∂^{m} (∑ i in s, f i
) = ∑ i in s, ∂^{m} (f i)
参数：f : ι -> E；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `LineDeriv.iteratedLineDerivOp_add`：iteratedLineDerivOp_add (x y : E) : ∂
^{m} (x + y) = ∂^{m} x + ∂^{m} y
-/
theorem iteratedLineDerivOp_sum (f : ι → E) (s : Finset ι) :
    ∂^{m} (∑ i ∈ s, f i) = ∑ i ∈ s, ∂^{m} (f i) :=
  map_sum (AddMonoidHom.mk' ∂^{m} (iteratedLineDerivOp_add m)) f s

end add

/-
**LineDeriv.iteratedLineDerivOp_smul** 是 Mathlib 中的一个定理，位于命名空间 `LineDeriv`。
形式化陈述：iteratedLineDerivOp_smul [SMul R E] [LineDerivSMul R V E E] (r : R) (x : E
) : ∂^{m} (r • x) = r • ∂^{m} x
参数：r : R；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LineDerivSMul.lineDerivOp_smul`：∀ {R : Type u_11} {V : Type u} {E : Type
 v} {F : outParam (Type w)} {inst : SMul R E} {inst_1 : SMul R F}   {inst_2 : Li
neDeriv V E F} [self…
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
/-
**LineDeriv.continuous_iteratedLineDerivOp** 是 Mathlib 中的一个定理，位于命名空间 `LineDeriv`
。
形式化陈述：continuous_iteratedLineDerivOp [ContinuousLineDeriv V E E] {n : Nat} (m : 
Fin n -> V) : Continuous (∂^{m} : E -> E)
参数：m : Fin n -> V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ContinuousLineDeriv.continuous_lineDerivOp`：∀ {V : Type u} {E : Type v} 
{F : outParam (Type w)} {inst : TopologicalSpace E} {inst_1 : TopologicalSpace F
}   {inst_2 : LineDeriv V E F} […
-/
theorem continuous_iteratedLineDerivOp [ContinuousLineDeriv V E E] {n : ℕ} (m : Fin n → V) :
    Continuous (∂^{m} : E → E) := by
  induction n with
  | zero =>
    exact continuous_id
  | succ n IH =>
    exact (continuous_lineDerivOp _).comp (IH _)

variable [Ring R] [AddCommGroup V] [AddCommGroup E] [Module R E]
  [LineDerivAdd V E E] [LineDerivSMul R V E E] [ContinuousLineDeriv V E E]

variable (R E) in
/-- The iterated line derivative as a continuous linear map. -/
/-
**LineDeriv.iteratedLineDerivOpCLM** 是 Mathlib 中的一个定义，位于命名空间 `LineDeriv`。
形式化陈述：iteratedLineDerivOpCLM {n : Nat} (m : Fin n -> V) : E ->L[R] E where toFun
参数：m : Fin n -> V。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LineDeriv.iteratedLineDerivOp_add`：iteratedLineDerivOp_add (x y : E) : ∂
^{m} (x + y) = ∂^{m} x + ∂^{m} y

--- 原说明 ---
The iterated line derivative as a continuous linear map.
-/
def iteratedLineDerivOpCLM {n : ℕ} (m : Fin n → V) : E →L[R] E where
  toFun := ∂^{m}
  map_add' := iteratedLineDerivOp_add m
  map_smul' := iteratedLineDerivOp_smul m

@[simp]
/-
**LineDeriv.iteratedLineDerivOpCLM_apply** 是 Mathlib 中的一个定理，位于命名空间 `LineDeriv`。
形式化陈述：iteratedLineDerivOpCLM_apply {n : Nat} (m : Fin n -> V) (x : E) : iterated
LineDerivOpCLM R E m x = ∂^{m} x
参数：m : Fin n -> V；x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iteratedLineDerivOpCLM_apply {n : ℕ} (m : Fin n → V) (x : E) :
    iteratedLineDerivOpCLM R E m x = ∂^{m} x := rfl

end iteratedLineDerivOp

end LineDeriv

/-! ## Laplacian -/

/--
The notation typeclass for the Laplace operator.
-/
/-
**Laplacian** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type v → outParam (Type w) → Type (max v w)
参数：Type w；max v w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The notation typeclass for the Laplace operator.
-/
class Laplacian (E : Type v) (F : outParam (Type w)) where
  /-- `Δ f` is the Laplacian of `f`. The meaning of this notation is type-dependent. -/
  laplacian : E → F

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
/-- The second derivative in terms `lineDerivOp` as a bilinear map.

Mainly used to give an abstract definition of the Laplacian. -/
/-
**LineDeriv.bilinearLineDerivTwo** 是 Mathlib 中的一个定义，位于命名空间 `LineDeriv`。
形式化陈述：bilinearLineDerivTwo (f : V₁) : E ->ₗ[R] E ->ₗ[R] V₃
参数：f : V₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second derivative in terms `lineDerivOp` as a bilinear map.

Mainly used to give an abstract definition of the Laplacian.
-/
def bilinearLineDerivTwo (f : V₁) : E →ₗ[R] E →ₗ[R] V₃ :=
  LinearMap.mk₂ R (∂_{·} <| ∂_{·} f) (by simp [lineDerivOp_left_add])
    (by simp [lineDerivOp_left_smul]) (by simp [lineDerivOp_left_add, lineDerivOp_add])
    (by simp [lineDerivOp_left_smul, lineDerivOp_smul])

variable (R) in
/-- The second derivative in terms `lineDerivOp` as a linear map from the tensor product.

Mainly used to give an abstract definition of the Laplacian. -/
/-
**LineDeriv.tensorLineDerivTwo** 是 Mathlib 中的一个定义，位于命名空间 `LineDeriv`。
形式化陈述：tensorLineDerivTwo (f : V₁) : E otimes[R] E ->ₗ[R] V₃
参数：f : V₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second derivative in terms `lineDerivOp` as a linear map from the tensor pro
duct.

Mainly used to give an abstract definition of the Laplacian.
-/
def tensorLineDerivTwo (f : V₁) : E ⊗[R] E →ₗ[R] V₃ :=
  lift (bilinearLineDerivTwo R f)
/-
**LineDeriv.tensorLineDerivTwo_eq_lineDerivOp_lineDerivOp** 是 Mathlib 中的一个引理，位于命
名空间 `LineDeriv`。
形式化陈述：tensorLineDerivTwo_eq_lineDerivOp_lineDerivOp (f : V₁) (v w : E) : tensorL
ineDerivTwo R f (v otimesₜ[R] w) = ∂_{v} (∂_{w} f)
参数：f : V₁；v w : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.lift.tmul`：∀ {R : Type u_1} {R₂ : Type u_2} [inst : CommSe
miring R] [inst_1 : CommSemiring R₂] {σ₁₂ : R →+* R₂} {M : Type u_7}   {N : Type
 u_8} {P₂ : T…
-/
lemma tensorLineDerivTwo_eq_lineDerivOp_lineDerivOp (f : V₁) (v w : E) :
    tensorLineDerivTwo R f (v ⊗ₜ[R] w) = ∂_{v} (∂_{w} f) := lift.tmul _ _

end TensorProduct

section InnerProductSpace

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section LinearMap

variable [Module ℝ V₂] [Module ℝ V₃]
  [LineDerivAdd E V₁ V₂] [LineDerivAdd E V₂ V₃]
  [LineDerivSMul ℝ E V₂ V₃] [LineDerivLeftSMul ℝ E V₁ V₂] [LineDerivLeftSMul ℝ E V₂ V₃]

open TensorProduct InnerProductSpace

/-
**LineDeriv.tensorLineDerivTwo_canonicalCovariantTensor_eq_sum** 是 Mathlib 中的一个定
理，位于命名空间 `LineDeriv`。
形式化陈述：tensorLineDerivTwo_canonicalCovariantTensor_eq_sum [Fintype ι] (v : Orthon
ormalBasis ι Real E) (f : V₁) : tensorLineDerivTwo Real f (canonicalCovariantTen
sor E) = ∑ i, ∂_{v i} (∂_{v i} f)
参数：v : OrthonormalBasis ι Real E；f : V₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductSpace.canonicalCovariantTensor_eq_sum`：InnerProductSpace.can
onicalCovariantTensor_eq_sum [FiniteDimensional Real E] {ι : Type*} [Fintype ι] 
(v : OrthonormalBasis ι Real E) : Inner…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `LineDeriv.tensorLineDerivTwo_eq_lineDerivOp_lineDerivOp`：tensorLineDeriv
Two_eq_lineDerivOp_lineDerivOp (f : V₁) (v w : E) : tensorLineDerivTwo R f (v ot
imesₜ[R] w) = ∂_{v} (∂_{w} f)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tensorLineDerivTwo_canonicalCovariantTensor_eq_sum [Fintype ι] (v : OrthonormalBasis ι ℝ E)
    (f : V₁) : tensorLineDerivTwo ℝ f (canonicalCovariantTensor E) = ∑ i, ∂_{v i} (∂_{v i} f) := by
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
/-- The Laplacian defined by iterated `lineDerivOp` as a continuous linear map. -/
/-
**LineDeriv.laplacianCLM** 是 Mathlib 中的一个定义，位于命名空间 `LineDeriv`。
形式化陈述：laplacianCLM : V₁ ->L[R] V₃
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Laplacian defined by iterated `lineDerivOp` as a continuous linear map.
-/
def laplacianCLM : V₁ →L[R] V₃ :=
  ∑ i, lineDerivOpCLM R V₂ (stdOrthonormalBasis ℝ E i) ∘L
    lineDerivOpCLM R V₁ (stdOrthonormalBasis ℝ E i)

end definition

variable [Module ℝ V₁] [Module ℝ V₂] [Module ℝ V₃]
  [TopologicalSpace V₁] [TopologicalSpace V₂] [TopologicalSpace V₃] [IsTopologicalAddGroup V₃]
  [LineDerivAdd E V₁ V₂] [LineDerivSMul ℝ E V₁ V₂] [ContinuousLineDeriv E V₁ V₂]
  [LineDerivAdd E V₂ V₃] [LineDerivSMul ℝ E V₂ V₃] [ContinuousLineDeriv E V₂ V₃]
  [LineDerivLeftSMul ℝ E V₁ V₂] [LineDerivLeftSMul ℝ E V₂ V₃]

/-
**LineDeriv.laplacianCLM_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `LineDeriv`。
形式化陈述：laplacianCLM_eq_sum [Fintype ι] (v : OrthonormalBasis ι Real E) (f : V₁) :
 laplacianCLM Real E V₁ f = ∑ i, ∂_{v i} (∂_{v i} f)
参数：v : OrthonormalBasis ι Real E；f : V₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem laplacianCLM_eq_sum [Fintype ι] (v : OrthonormalBasis ι ℝ E) (f : V₁) :
    laplacianCLM ℝ E V₁ f = ∑ i, ∂_{v i} (∂_{v i} f) := by
  simp [laplacianCLM, ← tensorLineDerivTwo_canonicalCovariantTensor_eq_sum]

end ContinuousLinearMap

end InnerProductSpace

end LineDeriv

