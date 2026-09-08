/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Caflisch, David Loeffler, Yu Shao, Weijie Jiang, BeiBei Xiong
-/
module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Tactic.Abel
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Forward difference operators and Newton series

We define the forward difference operator, sending `f` to the function `x ↦ f (x + h) - f x` for
a given `h` (for any additive semigroup, taking values in an abelian group). The notation `Δ_[h]` is
defined for this operator, scoped in namespace `fwdDiff`.

We prove two key formulae about this operator:

* `shift_eq_sum_fwdDiff_iter`: the **Gregory-Newton formula**, expressing `f (y + n • h)` as a
  linear combination of forward differences of `f` at `y`, for `n ∈ ℕ`;
* `fwdDiff_iter_eq_sum_shift`: formula expressing the `n`-th forward difference of `f` at `y` as
  a linear combination of `f (y + k • h)` for `0 ≤ k ≤ n`.

We also prove some auxiliary results about iterated forward differences of the function
`n ↦ n.choose k`.
-/

@[expose] public section

open Finset Nat Function Polynomial

variable {M G : Type*} [AddCommMonoid M] [AddCommGroup G] (h : M)

/--
Forward difference operator, `fwdDiff h f n = f (n + h) - f n`. The notation `Δ_[h]` for this
operator is available in the `fwdDiff` namespace.
-/
/-
**fwdDiff** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：fwdDiff (h : M) (f : M -> G) : M -> G
参数：h : M；f : M -> G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Forward difference operator, `fwdDiff h f n = f (n + h) - f n`. The notation `Δ_
[h]` for this
operator is available in the `fwdDiff` namespace.
-/
def fwdDiff (h : M) (f : M → G) : M → G := fun n ↦ f (n + h) - f n

@[inherit_doc] scoped[fwdDiff] notation "Δ_[" h "]" => fwdDiff h

open fwdDiff
/-
**fwdDiff_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M : Type u_1} {G : Type u_2} [inst : AddCommMonoid M] [inst_1 : AddComm
Group G] (h : M) (f g : M → G),   fwdDiff h (f + g) = fwdDiff h f + fwdDiff h g
参数：h : M；f g : M → G；f + g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_sub_add_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b
 c d : α), a + b - (c + d) = a - c + (b - d)
-/
@[simp] lemma fwdDiff_add (h : M) (f g : M → G) :
    Δ_[h] (f + g) = Δ_[h] f + Δ_[h] g :=
  add_sub_add_comm ..
/-
**fwdDiff_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M : Type u_1} {G : Type u_2} [inst : AddCommMonoid M] [inst_1 : AddComm
Group G] (h : M) (g : G),   (fwdDiff h fun x => g) = fun x => 0
参数：h : M；g : G；fwdDiff h fun x => g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
@[simp] lemma fwdDiff_const (g : G) : Δ_[h] (fun _ ↦ g : M → G) = fun _ ↦ 0 :=
  funext fun _ ↦ sub_self g

section smul

/-
**fwdDiff_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：fwdDiff_smul {R : Type*} [Ring R] [Module R G] (f : M -> R) (g : M -> G) :
 Δ_[h] (f • g) = Δ_[h] f • g + f • Δ_[h] g + Δ_[h] f • Δ_[h] g
参数：f : M -> R；g : M -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `_private.Mathlib.Algebra.Group.ForwardDiff.0.fwdDiff_smul._abel_1_2`：∀ {
M : Type u_3} {G : Type u_1} [inst : AddCommMonoid M] [inst_1 : AddCommGroup G] 
(h : M) {R : Type u_2}   [inst_2 : Ring R] [inst_3 : _roo…
-/
lemma fwdDiff_smul {R : Type*} [Ring R] [Module R G] (f : M → R) (g : M → G) :
    Δ_[h] (f • g) = Δ_[h] f • g + f • Δ_[h] g + Δ_[h] f • Δ_[h] g := by
  ext y
  simp only [fwdDiff, Pi.smul_apply', Pi.add_apply, smul_sub, sub_smul]
  abel

-- Note `fwdDiff_const_smul` is more general than `fwdDiff_smul` since it allows `R` to be a
-- semiring, rather than a ring; in particular `R = ℕ` is allowed.
/-
**fwdDiff_const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M : Type u_1} {G : Type u_2} [inst : AddCommMonoid M] [inst_1 : AddComm
Group G] (h : M) {R : Type u_3}   [inst_2 : Monoid R] [inst_3 : DistribMulAction
 R G] (r : R) (f : M → G), fwdDiff h (r • f) = r • fwdDiff h f
参数：h : M；r : R；f : M → G；r • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
-/
@[simp] lemma fwdDiff_const_smul {R : Type*} [Monoid R] [DistribMulAction R G] (r : R) (f : M → G) :
    Δ_[h] (r • f) = r • Δ_[h] f :=
  funext fun _ ↦ (smul_sub ..).symm
/-
**fwdDiff_smul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M : Type u_1} {G : Type u_2} [inst : AddCommMonoid M] [inst_1 : AddComm
Group G] (h : M) {R : Type u_3}   [inst_2 : Ring R] [inst_3 : _root_.Module R G]
 (f : M → R) (g : G),   (fwdDiff h fun y => f y • g) = fwdDiff h f • fun x => g
参数：h : M；f : M → R；g : G；fwdDiff h fun y => f y • g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma fwdDiff_smul_const {R : Type*} [Ring R] [Module R G] (f : M → R) (g : G) :
    Δ_[h] (fun y ↦ f y • g) = Δ_[h] f • fun _ ↦ g := by
  ext y
  simp only [fwdDiff, Pi.smul_apply', sub_smul]

end smul

namespace fwdDiff_aux
/-!
## Forward-difference and shift operators as linear endomorphisms

This section contains versions of the forward-difference operator and the shift operator bundled as
`ℤ`-linear endomorphisms. These are useful for certain proofs; but they are slightly annoying to
use, as the source and target types of the maps have to be specified each time, and various
coercions need to be un-wound when the operators are applied, so we also provide the un-bundled
version.
-/

variable (M G) in
/-- Linear-endomorphism version of the forward difference operator. -/
@[simps]
/-
**fwdDiff_aux.fwdDiff** 是 Mathlib 中的一个定义，位于命名空间 `fwdDiff_aux`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Linear-endomorphism version of the forward difference operator.
-/
def fwdDiffₗ : Module.End ℤ (M → G) where
  toFun := fwdDiff h
  map_add' := fwdDiff_add h
  map_smul' := fwdDiff_const_smul h
/-
**fwdDiff_aux.coe_fwdDiff** 是 Mathlib 中的一个引理，位于命名空间 `fwdDiff_aux`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_fwdDiffₗ : ↑(fwdDiffₗ M G h) = fwdDiff h := rfl
/-
**fwdDiff_aux.coe_fwdDiff** 是 Mathlib 中的一个引理，位于命名空间 `fwdDiff_aux`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_fwdDiffₗ_pow (n : ℕ) : ↑(fwdDiffₗ M G h ^ n) = (fwdDiff h)^[n] := by
  ext; rw [Module.End.pow_apply, coe_fwdDiffₗ]

variable (M G) in
/-- Linear-endomorphism version of the shift-by-1 operator. -/
/-
**fwdDiff_aux.shift** 是 Mathlib 中的一个定义，位于命名空间 `fwdDiff_aux`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Linear-endomorphism version of the shift-by-1 operator.
-/
def shiftₗ : Module.End ℤ (M → G) := fwdDiffₗ M G h + 1
/-
**fwdDiff_aux.shift** 是 Mathlib 中的一个引理，位于命名空间 `fwdDiff_aux`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma shiftₗ_apply (f : M → G) (y : M) : shiftₗ M G h f y = f (y + h) := by simp [shiftₗ, fwdDiff]
/-
**fwdDiff_aux.shift** 是 Mathlib 中的一个引理，位于命名空间 `fwdDiff_aux`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma shiftₗ_pow_apply (f : M → G) (k : ℕ) (y : M) : (shiftₗ M G h ^ k) f y = f (y + k • h) := by
  induction k generalizing f with
  | zero => simp
  | succ k IH => simp [pow_add, IH (shiftₗ M G h f), shiftₗ_apply, add_assoc, add_nsmul]

end fwdDiff_aux

open fwdDiff_aux

/-
**fwdDiff_finsetSum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M : Type u_1} {G : Type u_2} [inst : AddCommMonoid M] [inst_1 : AddComm
Group G] (h : M) {α : Type u_3} (s : Finset α)   (f : α → M → G), fwdDiff h (∑ k
 ∈ s, f k) = ∑ k ∈ s, fwdDiff h (f k)
参数：h : M；s : Finset α；f : α → M → G；∑ k ∈ s, f k；f k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
@[simp] lemma fwdDiff_finsetSum {α : Type*} (s : Finset α) (f : α → M → G) :
    Δ_[h] (∑ k ∈ s, f k) = ∑ k ∈ s, Δ_[h] (f k) :=
  map_sum (fwdDiffₗ M G h) f s

@[deprecated (since := "2026-04-08")] alias fwdDiff_finset_sum := fwdDiff_finsetSum
/-
**fwdDiff_iter_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M : Type u_1} {G : Type u_2} [inst : AddCommMonoid M] [inst_1 : AddComm
Group G] (h : M) (f g : M → G) (n : ℕ),   (fwdDiff h)^[n] (f + g) = (fwdDiff h)^
[n] f + (fwdDiff h)^[n] g
参数：h : M；f g : M → G；n : ℕ；fwdDiff h；f + g；fwdDiff h；fwdDiff h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `fwdDiff_aux.coe_fwdDiffₗ_pow`：coe_fwdDiffₗ_pow (n : Nat) : ↑(fwdDiffₗ M 
G h ^ n) = (fwdDiff h)^[n]
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
-/
@[simp] lemma fwdDiff_iter_add (f g : M → G) (n : ℕ) :
    Δ_[h]^[n] (f + g) = Δ_[h]^[n] f + Δ_[h]^[n] g := by
  simpa only [coe_fwdDiffₗ_pow] using map_add (fwdDiffₗ M G h ^ n) f g
/-
**fwdDiff_iter_const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M : Type u_1} {G : Type u_2} [inst : AddCommMonoid M] [inst_1 : AddComm
Group G] (h : M) {R : Type u_3}   [inst_2 : Monoid R] [inst_3 : DistribMulAction
 R G] (r : R) (f : M → G) (n : ℕ),   (fwdDiff h)^[n] (r • f) = r • (fwdDiff h)^[
n] f
参数：h : M；r : R；f : M → G；n : ℕ；fwdDiff h；r • f；fwdDiff h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fwdDiff_const_smul`：∀ {M : Type u_1} {G : Type u_2} [inst : AddCommMonoi
d M] [inst_1 : AddCommGroup G] (h : M) {R : Type u_3}   [inst_2 : Monoid R] [ins
t_3 : Di…
-/
@[simp] lemma fwdDiff_iter_const_smul {R : Type*} [Monoid R] [DistribMulAction R G]
    (r : R) (f : M → G) (n : ℕ) : Δ_[h]^[n] (r • f) = r • Δ_[h]^[n] f := by
  induction n generalizing f with
  | zero => simp only [iterate_zero, id_eq]
  | succ n IH => simp only [iterate_succ_apply, fwdDiff_const_smul, IH]
/-
**fwdDiff_iter_finsetSum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M : Type u_1} {G : Type u_2} [inst : AddCommMonoid M] [inst_1 : AddComm
Group G] (h : M) {α : Type u_3} (s : Finset α)   (f : α → M → G) (n : ℕ), (fwdDi
ff h)^[n] (∑ k ∈ s, f k) = ∑ k ∈ s, (fwdDiff h)^[n] (f k)
参数：h : M；s : Finset α；f : α → M → G；n : ℕ；fwdDiff h；∑ k ∈ s, f k；fwdDiff h；f k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `fwdDiff_aux.coe_fwdDiffₗ_pow`：coe_fwdDiffₗ_pow (n : Nat) : ↑(fwdDiffₗ M 
G h ^ n) = (fwdDiff h)^[n]
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
@[simp] lemma fwdDiff_iter_finsetSum {α : Type*} (s : Finset α) (f : α → M → G) (n : ℕ) :
    Δ_[h]^[n] (∑ k ∈ s, f k) = ∑ k ∈ s, Δ_[h]^[n] (f k) := by
  simpa only [coe_fwdDiffₗ_pow] using map_sum (fwdDiffₗ M G h ^ n) f s

@[deprecated (since := "2026-04-08")] alias fwdDiff_iter_finset_sum := fwdDiff_iter_finsetSum

section newton_formulae

/--
Express the `n`-th forward difference of `f` at `y` in terms of the values `f (y + k)`, for
`0 ≤ k ≤ n`.
-/
/-
**fwdDiff_iter_eq_sum_shift** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fwdDiff_iter_eq_sum_shift (f : M -> G) (n : Nat) (y : M) : Δ_[h]^[n] f y =
 ∑ k in range (n + 1), ((-1 : Int) ^ (n - k) * n.choose k) • f (y + k • h)
参数：f : M -> G；n : Nat；y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `fwdDiff_aux.coe_fwdDiffₗ`：coe_fwdDiffₗ : ↑(fwdDiffₗ M G h) = fwdDiff h
· 使用定理 `Module.End.pow_apply`：pow_apply (f : End R M) (n : Nat) (m : M) : (f ^ n
) m = f^[n] m
· 使用定理 `Commute.neg_right`：neg_right : Commute a b -> Commute a (-b)
· 使用定理 `Commute.one_right`：one_right (a : M) : Commute a 1
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `LinearMap.sum_apply`：sum_apply (t : Finset ι) (f : ι -> M ->ₛₗ[σ₁₂] M₂) 
(b : M) : (∑ d in t, f d) b = ∑ d in t, f d b
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Int.cast_pow`：∀ {R : Type u_1} [inst : Ring R] (n : ℤ) (m : ℕ), ↑(n ^ m)
 = ↑n ^ m
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Module.End.mul_apply`：mul_apply (f g : Module.End R M) (x : M) : (f * g)
 x = f (g x)
· 使用定理 `Module.End.intCast_apply`：intCast_apply (z : Int) (m : N₁) : (z : Module
.End R N₁) m = z • m
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Pi.smul_apply`：∀ {ι : Type u_1} {α : Type u_2} {M : ι → Type u_5} [inst 
: (i : ι) → SMul α (M i)] (a : α) (f : (i : ι) → M i) (i : ι),   (a • f) i = a •
 f …
· 使用引理 `fwdDiff_aux.shiftₗ_pow_apply`：shiftₗ_pow_apply (f : M -> G) (k : Nat) (y
 : M) : (shiftₗ M G h ^ k) f y = f (y + k • h)
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
Express the `n`-th forward difference of `f` at `y` in terms of the values `f (y
 + k)`, for
`0 ≤ k ≤ n`.
-/
theorem fwdDiff_iter_eq_sum_shift (f : M → G) (n : ℕ) (y : M) :
    Δ_[h]^[n] f y = ∑ k ∈ range (n + 1), ((-1 : ℤ) ^ (n - k) * n.choose k) • f (y + k • h) := by
  -- rewrite in terms of `(shiftₗ - 1) ^ n`
  have : fwdDiffₗ M G h = shiftₗ M G h - 1 := by simp only [shiftₗ, add_sub_cancel_right]
  rw [← coe_fwdDiffₗ, this, ← Module.End.pow_apply]
  -- use binomial theorem `Commute.add_pow` to expand this
  have : Commute (shiftₗ M G h) (-1) := (Commute.one_right _).neg_right
  convert congr_fun (LinearMap.congr_fun (this.add_pow n) f) y
  · simp only [sub_eq_add_neg]
  · rw [LinearMap.sum_apply, sum_apply]
    congr 1 with k
    have : ((-1) ^ (n - k) * n.choose k : Module.End ℤ (M → G))
              = ↑((-1) ^ (n - k) * n.choose k : ℤ) := by norm_cast
    rw [mul_assoc, Module.End.mul_apply, this, Module.End.intCast_apply, map_smul,
      Pi.smul_apply, shiftₗ_pow_apply]
/-
**fwdDiff_iter_comp_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：fwdDiff_iter_comp_add (f : M -> G) (m : M) (n : Nat) (y : M) : Δ_[h]^[n] (
fun r => f (r + m)) y = (Δ_[h]^[n] f) (y + m)
参数：f : M -> G；m : M；n : Nat；y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fwdDiff_iter_eq_sum_shift`：fwdDiff_iter_eq_sum_shift (f : M -> G) (n : N
at) (y : M) : Δ_[h]^[n] f y = ∑ k in range (n + 1), ((-1 : Int) ^ (n - k) * n.ch
oose k) • f (y …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fwdDiff_iter_comp_add (f : M → G) (m : M) (n : ℕ) (y : M) :
    Δ_[h]^[n] (fun r ↦ f (r + m)) y = (Δ_[h]^[n] f) (y + m) := by
  simp [fwdDiff_iter_eq_sum_shift, add_right_comm]
/-
**fwdDiff_comp_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：fwdDiff_comp_add (f : M -> G) (m : M) (y : M) : Δ_[h] (fun r => f (r + m))
 y = (Δ_[h] f) (y + m)
参数：f : M -> G；m : M；y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `fwdDiff_iter_comp_add`：fwdDiff_iter_comp_add (f : M -> G) (m : M) (n : N
at) (y : M) : Δ_[h]^[n] (fun r => f (r + m)) y = (Δ_[h]^[n] f) (y + m)
-/
lemma fwdDiff_comp_add (f : M → G) (m : M) (y : M) :
    Δ_[h] (fun r ↦ f (r + m)) y = (Δ_[h] f) (y + m) :=
  fwdDiff_iter_comp_add h f m 1 y

/--
**Gregory-Newton formula** expressing `f (y + n • h)` in terms of the iterated forward differences
of `f` at `y`.
-/
/-
**shift_eq_sum_fwdDiff_iter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：shift_eq_sum_fwdDiff_iter (f : M -> G) (n : Nat) (y : M) : f (y + n • h) =
 ∑ k in range (n + 1), n.choose k • Δ_[h]^[k] f y
参数：f : M -> G；n : Nat；y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `fwdDiff_aux.shiftₗ_pow_apply`：shiftₗ_pow_apply (f : M -> G) (k : Nat) (y
 : M) : (shiftₗ M G h ^ k) f y = f (y + k • h)
· 使用定理 `fwdDiff_aux.shiftₗ.eq_1`：∀ (M : Type u_1) (G : Type u_2) [inst : AddComm
Monoid M] [inst_1 : AddCommGroup G] (h : M),   fwdDiff_aux.shiftₗ M G h = fwdDif
f_aux.fwdDiff…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `LinearMap.map_smul_of_tower`：map_smul_of_tower [CompatibleSMul M M₂ R S]
 (fₗ : M ->ₗ[S] M₂) (c : R) (x : M) : fₗ (c • x) = c • fₗ x
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `Module.End.pow_apply`：pow_apply (f : End R M) (n : Nat) (m : M) : (f ^ n
) m = f^[n] m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `Commute.add_pow`：add_pow (h : Commute x y) (n : Nat) : (x + y) ^ n = ∑ m
 in range (n + 1), x ^ m * y ^ (n - m) * n.choose m
· 使用定理 `Commute.one_right`：one_right (a : M) : Commute a 1

--- 原说明 ---
**Gregory-Newton formula** expressing `f (y + n • h)` in terms of the iterated f
orward differences
of `f` at `y`.
-/
theorem shift_eq_sum_fwdDiff_iter (f : M → G) (n : ℕ) (y : M) :
    f (y + n • h) = ∑ k ∈ range (n + 1), n.choose k • Δ_[h]^[k] f y := by
  convert!
    congr_fun (LinearMap.congr_fun ((Commute.one_right (fwdDiffₗ M G h)).add_pow n) f) y using 1
  · rw [← shiftₗ_pow_apply h f, shiftₗ]
  · simp [Module.End.pow_apply, coe_fwdDiffₗ]

end newton_formulae

section choose

/-
**fwdDiff_choose** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：fwdDiff_choose (j : Nat) : Δ_[1] (fun x => x.choose (j + 1) : Nat -> Int) 
= fun x => x.choose j
参数：j : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fwdDiff_choose (j : ℕ) : Δ_[1] (fun x ↦ x.choose (j + 1) : ℕ → ℤ) = fun x ↦ x.choose j := by
  ext n
  simp only [fwdDiff, choose_succ_succ' n j, cast_add, add_sub_cancel_right]
/-
**fwdDiff_iter_choose** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：fwdDiff_iter_choose (j k : Nat) : Δ_[1]^[k] (fun x => x.choose (k + j) : N
at -> Int) = fun x => x.choose j
参数：j k : Nat。
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
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
· 使用引理 `fwdDiff_choose`：fwdDiff_choose (j : Nat) : Δ_[1] (fun x => x.choose (j +
 1) : Nat -> Int) = fun x => x.choose j
-/
lemma fwdDiff_iter_choose (j k : ℕ) :
    Δ_[1]^[k] (fun x ↦ x.choose (k + j) : ℕ → ℤ) = fun x ↦ x.choose j := by
  induction k generalizing j with
  | zero => simp only [zero_add, iterate_zero, id_eq]
  | succ k IH =>
    simp only [iterate_succ_apply', add_assoc, add_comm 1 j, IH, fwdDiff_choose]
/-
**fwdDiff_iter_choose_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：fwdDiff_iter_choose_zero (m n : Nat) : Δ_[1]^[n] (fun x => x.choose m : Na
t -> Int) 0 = if n = m then 1 else 0
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `Nat.exists_eq_add_of_lt`：∀ {m n : ℕ}, m < n → ∃ k, n = m + k + 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.iterate_add_apply`：iterate_add_apply (m n : Nat) (x : α) : f^[m
 + n] x = f^[m] (f^[n] x)
· 使用引理 `fwdDiff_iter_choose`：fwdDiff_iter_choose (j k : Nat) : Δ_[1]^[k] (fun x 
=> x.choose (k + j) : Nat -> Int) = fun x => x.choose j
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.choose_zero_right`：choose_zero_right (n : Nat) : choose n 0 = 1
· 使用定理 `Function.iterate_one`：iterate_one : f^[1] = f
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `fwdDiff_const`：∀ {M : Type u_1} {G : Type u_2} [inst : AddCommMonoid M] 
[inst_1 : AddCommGroup G] (h : M) (g : G),   (fwdDiff h fun x => g) = fun x => 0
· 使用定理 `fwdDiff_iter_eq_sum_shift`：fwdDiff_iter_eq_sum_shift (f : M -> G) (n : N
at) (y : M) : Δ_[h]^[n] f y = ∑ k in range (n + 1), ((-1 : Int) ^ (n - k) * n.ch
oose k) • f (y …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
（共 39 条，此处仅展示前 30 条）
-/
lemma fwdDiff_iter_choose_zero (m n : ℕ) :
    Δ_[1]^[n] (fun x ↦ x.choose m : ℕ → ℤ) 0 = if n = m then 1 else 0 := by
  rcases lt_trichotomy m n with hmn | rfl | hnm
  · rcases Nat.exists_eq_add_of_lt hmn with ⟨k, rfl⟩
    simp_rw [hmn.ne', if_false, (by ring : m + k + 1 = k + 1 + m), iterate_add_apply,
      add_zero m ▸ fwdDiff_iter_choose 0 m, choose_zero_right, iterate_one, cast_one, fwdDiff_const,
      fwdDiff_iter_eq_sum_shift, smul_zero, sum_const_zero]
  · simp only [if_true, add_zero m ▸ fwdDiff_iter_choose 0 m, choose_zero_right, cast_one]
  · rcases Nat.exists_eq_add_of_lt hnm with ⟨k, rfl⟩
    simp_rw [hnm.ne, if_false, add_assoc n k 1, fwdDiff_iter_choose, choose_zero_succ, cast_zero]

end choose

/-
**fwdDiff_addChar_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：fwdDiff_addChar_eq {M R : Type*} [AddCommMonoid M] [Ring R] (φ : AddChar M
 R) (x h : M) (n : Nat) : Δ_[h]^[n] φ x = (φ h - 1) ^ n * φ x
参数：φ : AddChar M R；x h : M；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AddChar.map_add_eq_mul`：map_add_eq_mul (ψ : AddChar A M) (x y : A) : ψ (
x + y) = ψ x * ψ y
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
lemma fwdDiff_addChar_eq {M R : Type*} [AddCommMonoid M] [Ring R]
    (φ : AddChar M R) (x h : M) (n : ℕ) : Δ_[h]^[n] φ x = (φ h - 1) ^ n * φ x := by
  induction n generalizing x with
  | zero => simp
  | succ n IH =>
    simp only [pow_succ, iterate_succ_apply', fwdDiff, IH, ← mul_sub, mul_assoc]
    rw [sub_mul, ← AddChar.map_add_eq_mul, add_comm h x, one_mul]

/-!
## Forward differences of polynomials

We prove formulae about the forward difference operator applied to polynomials:

* `fwdDiff_iter_pow_eq_zero_of_lt` :
  The `n`-th forward difference of the function `x ↦ x^j` is zero if `j < n`;
* `fwdDiff_iter_eq_factorial` :
  The `n`-th forward difference of the function `x ↦ x^n` is the constant function `n!`;
* `fwdDiff_iter_sum_mul_pow_eq_zero` :
  The `n`-th forward difference of a polynomial of degree `< n` is zero (formulated using explicit
    sums over `range n`).
-/

variable {R : Type*} [CommRing R]

/--
The `n`-th forward difference of the function `x ↦ x^j` is zero if `j < n`.
-/
/-
**fwdDiff_iter_pow_eq_zero_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fwdDiff_iter_pow_eq_zero_of_lt {j n : Nat} (h : j < n) : Δ_[1]^[n] (fun (r
 : R) => r ^ j) = 0
参数：h : j < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_pow`：add_pow [CommSemiring R] (x y : R) (n : Nat) : (x + y) ^ n = ∑ 
m in range (n + 1), x ^ m * y ^ (n - m) * n.choose m
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `Nat.choose_self`：choose_self (n : Nat) : choose n n = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.iterate_succ_apply`：iterate_succ_apply (n : Nat) (x : α) : f^[n
.succ] x = f^[n] (f x)
· 使用定理 `fwdDiff_iter_finsetSum`：∀ {M : Type u_1} {G : Type u_2} [inst : AddCommM
onoid M] [inst_1 : AddCommGroup G] (h : M) {α : Type u_3} (s : Finset α)   (f : 
α → M → G) (…
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `fwdDiff_iter_const_smul`：∀ {M : Type u_1} {G : Type u_2} [inst : AddComm
Monoid M] [inst_1 : AddCommGroup G] (h : M) {R : Type u_3}   [inst_2 : Monoid R]
 [inst_3 : Di…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `nsmul_zero`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ), n • 0 = 0

--- 原说明 ---
The `n`-th forward difference of the function `x ↦ x^j` is zero if `j < n`.
-/
theorem fwdDiff_iter_pow_eq_zero_of_lt {j n : ℕ} (h : j < n) :
    Δ_[1]^[n] (fun (r : R) ↦ r ^ j) = 0 := by
  induction n generalizing j with
  | zero => aesop
  | succ n ih =>
    have : (Δ_[1] fun (r : R) ↦ r ^ j) = ∑ i ∈ range j, j.choose i • fun r ↦ r ^ i := by
      ext x
      simp [nsmul_eq_mul, fwdDiff, add_pow, sum_range_succ, mul_comm]
    rw [iterate_succ_apply, this, fwdDiff_iter_finsetSum]
    exact sum_eq_zero fun i hi ↦ by
      rw [fwdDiff_iter_const_smul, ih (by have := mem_range.1 hi; lia), nsmul_zero]

/--
The `n`-th forward difference of `x ↦ x^n` is the constant function `n!`.
-/
/-
**fwdDiff_iter_eq_factorial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fwdDiff_iter_eq_factorial {n : Nat} : Δ_[1]^[n] (fun (r : R) => r ^ n) = n
 !
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_pow`：add_pow [CommSemiring R] (x y : R) (n : Nat) : (x + y) ^ n = ∑ 
m in range (n + 1), x ^ m * y ^ (n - m) * n.choose m
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `Nat.choose_succ_self_right`：∀ (n : ℕ), (n + 1).choose n = n + 1
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.choose_self`：choose_self (n : Nat) : choose n n = 1
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `fwdDiff_iter_finsetSum`：∀ {M : Type u_1} {G : Type u_2} [inst : AddCommM
onoid M] [inst_1 : AddCommGroup G] (h : M) {α : Type u_3} (s : Finset α)   (f : 
α → M → G) (…
· 使用定理 `fwdDiff_iter_const_smul`：∀ {M : Type u_1} {G : Type u_2} [inst : AddComm
Monoid M] [inst_1 : AddCommGroup G] (h : M) {R : Type u_3}   [inst_2 : Monoid R]
 [inst_3 : Di…
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Pi.instIsRightCancelAdd`：∀ {I : Type u} {f : I → Type v₁} [inst : (i : I
) → Add (f i)] [∀ (i : I), IsRightCancelAdd (f i)],   IsRightCancelAdd ((i : I) 
→ f i)
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `fwdDiff_iter_pow_eq_zero_of_lt`：fwdDiff_iter_pow_eq_zero_of_lt {j n : Na
t} (h : j < n) : Δ_[1]^[n] (fun (r : R) => r ^ j) = 0
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
The `n`-th forward difference of `x ↦ x^n` is the constant function `n!`.
-/
theorem fwdDiff_iter_eq_factorial {n : ℕ} :
    Δ_[1]^[n] (fun (r : R) ↦ r ^ n) = n ! := by
  induction n with
  | zero => aesop
  | succ n IH =>
    have : (Δ_[1] fun (r : R) ↦ r ^ (n + 1)) =
      ∑ i ∈ range (n + 1), (n + 1).choose i • fun r ↦ r ^ i := by
      ext x
      simp [nsmul_eq_mul, fwdDiff, add_pow, sum_range_succ, mul_comm]
    simp_rw [iterate_succ_apply, this, fwdDiff_iter_finsetSum, fwdDiff_iter_const_smul,
       sum_range_succ]
    simpa [IH, factorial_succ] using sum_eq_zero fun i hi ↦ by
      rw [fwdDiff_iter_pow_eq_zero_of_lt (by have := mem_range.1 hi; lia), mul_zero]
/-
**Polynomial.fwdDiff_iter_degree_eq_factorial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Polynomial.fwdDiff_iter_degree_eq_factorial (P : R[X]) : Δ_[1]^[P.natDegre
e] P.eval = P.leadingCoeff • P.natDegree !
参数：P : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_eq_sum_range`：eval_eq_sum_range {p : R[X]} (x : R) : p.e
val x = ∑ i in Finset.range (p.natDegree + 1), p.coeff i * x ^ i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `fwdDiff_iter_finsetSum`：∀ {M : Type u_1} {G : Type u_2} [inst : AddCommM
onoid M] [inst_1 : AddCommGroup G] (h : M) {α : Type u_3} (s : Finset α)   (f : 
α → M → G) (…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `fwdDiff_iter_const_smul`：∀ {M : Type u_1} {G : Type u_2} [inst : AddComm
Monoid M] [inst_1 : AddCommGroup G] (h : M) {R : Type u_3}   [inst_2 : Monoid R]
 [inst_3 : Di…
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `fwdDiff_iter_pow_eq_zero_of_lt`：fwdDiff_iter_pow_eq_zero_of_lt {j n : Na
t} (h : j < n) : Δ_[1]^[n] (fun (r : R) => r ^ j) = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `fwdDiff_iter_eq_factorial`：fwdDiff_iter_eq_factorial {n : Nat} : Δ_[1]^[
n] (fun (r : R) => r ^ n) = n !
· 使用定理 `Polynomial.leadingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Po
lynomial R), p.leadingCoeff = p.coeff p.natDegree
· 使用定理 `Pi.smul_apply`：∀ {ι : Type u_1} {α : Type u_2} {M : ι → Type u_5} [inst 
: (i : ι) → SMul α (M i)] (a : α) (f : (i : ι) → M i) (i : ι),   (a • f) i = a •
 f …
-/
theorem Polynomial.fwdDiff_iter_degree_eq_factorial (P : R[X]) :
    Δ_[1]^[P.natDegree] P.eval = P.leadingCoeff • P.natDegree ! := funext fun x ↦ by
  simp_rw [P.eval_eq_sum_range, ← sum_apply _ _ (fun i x ↦ P.coeff i * x ^ i),
    fwdDiff_iter_finsetSum, ← smul_eq_mul, ← Pi.smul_def, fwdDiff_iter_const_smul, Pi.smul_apply]
  rw [sum_apply, sum_range_succ, sum_eq_zero (fun i hi ↦ ?_), zero_add,
    fwdDiff_iter_eq_factorial, leadingCoeff, Pi.smul_apply]
  rw [fwdDiff_iter_pow_eq_zero_of_lt (mem_range.mp hi), smul_zero, Pi.zero_apply]
/-
**Polynomial.fwdDiff_iter_eq_zero_of_degree_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Polynomial.fwdDiff_iter_eq_zero_of_degree_lt {P : R[X]} {n : Nat} (hP : P.
natDegree < n) : Δ_[1]^[n] P.eval = 0
参数：hP : P.natDegree < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.exists_eq_add_of_lt`：∀ {m n : ℕ}, m < n → ∃ k, n = m + k + 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Function.iterate_add_apply`：iterate_add_apply (m n : Nat) (x : α) : f^[m
 + n] x = f^[m] (f^[n] x)
· 使用定理 `Function.iterate_succ_apply`：iterate_succ_apply (n : Nat) (x : α) : f^[n
.succ] x = f^[n] (f x)
· 使用定理 `Polynomial.fwdDiff_iter_degree_eq_factorial`：Polynomial.fwdDiff_iter_deg
ree_eq_factorial (P : R[X]) : Δ_[1]^[P.natDegree] P.eval = P.leadingCoeff • P.na
tDegree !
· 使用定理 `Pi.smul_def`：∀ {ι : Type u_1} {α : Type u_2} {M : ι → Type u_5} [inst : 
(i : ι) → SMul α (M i)] (a : α) (f : (i : ι) → M i),   a • f = fun i => a • f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `fwdDiff_const`：∀ {M : Type u_1} {G : Type u_2} [inst : AddCommMonoid M] 
[inst_1 : AddCommGroup G] (h : M) (g : G),   (fwdDiff h fun x => g) = fun x => 0
· 使用定理 `fwdDiff_iter_eq_sum_shift`：fwdDiff_iter_eq_sum_shift (f : M -> G) (n : N
at) (y : M) : Δ_[h]^[n] f y = ∑ k in range (n + 1), ((-1 : Int) ^ (n - k) * n.ch
oose k) • f (y …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Polynomial.fwdDiff_iter_eq_zero_of_degree_lt {P : R[X]} {n : ℕ} (hP : P.natDegree < n) :
    Δ_[1]^[n] P.eval = 0 := funext fun x ↦ by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hP
  rw [add_assoc, add_comm, Function.iterate_add_apply, Function.iterate_succ_apply,
    P.fwdDiff_iter_degree_eq_factorial, Pi.smul_def]
  simp [fwdDiff_iter_eq_sum_shift]
/-
**Polynomial.fwdDiff_iter_degree_add_one_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Polynomial.fwdDiff_iter_degree_add_one_eq_zero (P : R[X]) : Δ_[1]^[P.natDe
gree + 1] P.eval = 0
参数：P : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `Polynomial.fwdDiff_iter_eq_zero_of_degree_lt`：Polynomial.fwdDiff_iter_eq
_zero_of_degree_lt {P : R[X]} {n : Nat} (hP : P.natDegree < n) : Δ_[1]^[n] P.eva
l = 0
-/
theorem Polynomial.fwdDiff_iter_degree_add_one_eq_zero (P : R[X]) :
    Δ_[1]^[P.natDegree + 1] P.eval = 0 := by
  have hP : P.natDegree < P.natDegree + 1 := Nat.lt_succ_self P.natDegree
  exact Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hP

/--
The `n`-th forward difference of a polynomial of degree `< n` is zero (formulated using explicit
sums over `range n`).
-/
/-
**fwdDiff_iter_sum_mul_pow_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fwdDiff_iter_sum_mul_pow_eq_zero {n : Nat} (P : Nat -> R) : Δ_[1]^[n] (fun
 r : R => ∑ k in range n, P k * r ^ k) = 0
参数：P : Nat -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `fwdDiff_iter_finsetSum`：∀ {M : Type u_1} {G : Type u_2} [inst : AddCommM
onoid M] [inst_1 : AddCommGroup G] (h : M) {α : Type u_3} (s : Finset α)   (f : 
α → M → G) (…
· 使用定理 `Finset.sum_fn`：∀ {α : Type u_7} {M : α → Type u_8} {ι : Type u_9} [inst 
: (a : α) → AddCommMonoid (M a)] (s : Finset ι)   (g : ι → (a : α) → M a), ∑ c ∈
 s,…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `fwdDiff_iter_const_smul`：∀ {M : Type u_1} {G : Type u_2} [inst : AddComm
Monoid M] [inst_1 : AddCommGroup G] (h : M) {R : Type u_3}   [inst_2 : Monoid R]
 [inst_3 : Di…
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用引理 `smul_eq_zero_of_right`：smul_eq_zero_of_right (a : M) {b : A} (h : b = 0)
 : a • b = 0
· 使用定理 `fwdDiff_iter_pow_eq_zero_of_lt`：fwdDiff_iter_pow_eq_zero_of_lt {j n : Na
t} (h : j < n) : Δ_[1]^[n] (fun (r : R) => r ^ j) = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n

--- 原说明 ---
The `n`-th forward difference of a polynomial of degree `< n` is zero (formulate
d using explicit
sums over `range n`).
-/
theorem fwdDiff_iter_sum_mul_pow_eq_zero {n : ℕ} (P : ℕ → R) :
    Δ_[1]^[n] (fun r : R ↦ ∑ k ∈ range n, P k * r ^ k) = 0 := by
  simp_rw [← sum_apply _ _ (fun i x ↦ P i * x ^ i), fwdDiff_iter_finsetSum, sum_fn, ← smul_eq_mul,
    ← Pi.smul_def, fwdDiff_iter_const_smul, ← sum_fn]
  exact sum_eq_zero fun i hi ↦ smul_eq_zero_of_right _ <| fwdDiff_iter_pow_eq_zero_of_lt
    <| mem_range.mp hi
