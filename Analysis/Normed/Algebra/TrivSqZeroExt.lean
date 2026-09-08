/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.Topology.Instances.TrivSqZeroExt

/-!
# Results on `TrivSqZeroExt R M` related to the norm

This file contains results about `NormedSpace.exp` for `TrivSqZeroExt`.

It also contains a definition of the $ℓ^1$ norm,
which defines $\|r + m\| \coloneqq \|r\| + \|m\|$.
This is not a particularly canonical choice of definition,
but it is sufficient to provide a `NormedAlgebra` instance,
and thus enables `NormedSpace.exp_add_of_commute` to be used on `TrivSqZeroExt`.
If the non-canonicity becomes problematic in future,
we could keep the collection of instances behind an `open scoped`.

## Main results

* `TrivSqZeroExt.fst_exp`
* `TrivSqZeroExt.snd_exp`
* `TrivSqZeroExt.exp_inl`
* `TrivSqZeroExt.exp_inr`
* The $ℓ^1$ norm on `TrivSqZeroExt`:
  * `TrivSqZeroExt.instL1SeminormedAddCommGroup`
  * `TrivSqZeroExt.instL1SeminormedRing`
  * `TrivSqZeroExt.instL1SeminormedCommRing`
  * `TrivSqZeroExt.instL1IsBoundedSMul`
  * `TrivSqZeroExt.instL1NormedAddCommGroup`
  * `TrivSqZeroExt.instL1NormedRing`
  * `TrivSqZeroExt.instL1NormedCommRing`
  * `TrivSqZeroExt.instL1NormedSpace`
  * `TrivSqZeroExt.instL1NormedAlgebra`

## TODO

* Generalize more of these results to non-commutative `R`. In principle, under sufficient conditions
  we should expect
  `(exp x).snd = ∫ t in 0..1, exp (t • x.fst) • op (exp ((1 - t) • x.fst)) • x.snd`
  ([Physics.SE](https://physics.stackexchange.com/a/41671/185147), and
  https://link.springer.com/chapter/10.1007/978-3-540-44953-9_2).

-/

@[expose] public section


variable (𝕜 : Type*) {S R M : Type*}

local notation "tsze" => TrivSqZeroExt

open NormedSpace -- For `NormedSpace.exp`.

namespace TrivSqZeroExt

section Topology

section not_charZero
variable [Field 𝕜] [Ring R] [AddCommGroup M]
  [Algebra 𝕜 R] [Module 𝕜 M] [Module R M] [Module Rᵐᵒᵖ M]
  [SMulCommClass R Rᵐᵒᵖ M] [IsScalarTower 𝕜 R M] [IsScalarTower 𝕜 Rᵐᵒᵖ M]
  [TopologicalSpace R] [TopologicalSpace M]
  [IsTopologicalRing R] [IsTopologicalAddGroup M] [ContinuousSMul R M] [ContinuousSMul Rᵐᵒᵖ M]

/-
**TrivSqZeroExt.fst_expSeries** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：∀ (𝕜 : Type u_1) {R : Type u_3} {M : Type u_4} [inst : Field 𝕜] [inst_1 : 
Ring R] [inst_2 : AddCommGroup M]   [inst_3 : Algebra 𝕜 R] [inst_4 : _root_.Modu
le 𝕜 M] [inst_5 : _root_.Module R M] [inst_6 : _root_.Module Rᵐᵒᵖ M]   [inst_7 :
 SMulCommClass R Rᵐᵒᵖ M] [inst_8 : IsScalarTower 𝕜 R M] [inst_9 : IsScalarTower 
𝕜 Rᵐᵒᵖ M]   [inst_10 : TopologicalSpace R] [inst_11 : TopologicalSpace M] [inst_
12 : IsTopologicalRing R]   [inst_13 : IsTopologicalAddGroup M] [inst_14 : Conti
nuousSMul R M] [inst_15 : ContinuousSMul Rᵐᵒᵖ M]   (x : TrivSqZeroExt R M) (n : 
ℕ),   ((NormedSpace.expSeries 𝕜 (TrivSqZeroExt R M) n) fun x_1 => x).fst = (Norm
edSpace.expSeries 𝕜 R n) fun x_1 => x.fst
参数：𝕜 : Type u_1；x : TrivSqZeroExt R M；n : ℕ；(NormedSpace.expSeries 𝕜 (TrivSqZero
Ext R M) n) fun x_1 => x；NormedSpace.expSeries 𝕜 R n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `TrivSqZeroExt.instIsTopologicalRingOfIsTopologicalAddGroupOfContinuousSM
ulMulOpposite`：∀ {R : Type u_3} {M : Type u_4} [inst : TopologicalSpace R] [inst
_1 : TopologicalSpace M] [inst_2 : Ring R]   [inst_3 : AddCommGroup M] [ins…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedSpace.expSeries_apply_eq`：expSeries_apply_eq (x : 𝔸) (n : Nat) : (
expSeries 𝕂 𝔸 n fun _ => x) = (n !⁻¹ : 𝕂) • x ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem fst_expSeries (x : tsze R M) (n : ℕ) :
    fst (expSeries 𝕜 (tsze R M) n fun _ => x) = expSeries 𝕜 R n fun _ => x.fst := by
  simp [expSeries_apply_eq]

end not_charZero

section Ring
variable [Field 𝕜] [CharZero 𝕜] [Ring R] [AddCommGroup M]
  [Algebra 𝕜 R] [Module 𝕜 M] [Module R M] [Module Rᵐᵒᵖ M]
  [SMulCommClass R Rᵐᵒᵖ M] [IsScalarTower 𝕜 R M] [IsScalarTower 𝕜 Rᵐᵒᵖ M]
  [TopologicalSpace R] [TopologicalSpace M]
  [IsTopologicalRing R] [IsTopologicalAddGroup M] [ContinuousSMul R M] [ContinuousSMul Rᵐᵒᵖ M]

/-
**TrivSqZeroExt.snd_expSeries_of_smul_comm** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZero
Ext`。
形式化陈述：snd_expSeries_of_smul_comm (x : tsze R M) (hx : MulOpposite.op x.fst • x.s
nd = x.fst • x.snd) (n : Nat) : snd (expSeries 𝕜 (tsze R M) (n + 1) fun _ => x) 
= (expSeries 𝕜 R n fun _ => x.fst) • x.snd
参数：x : tsze R M；hx : MulOpposite.op x.fst • x.snd = x.fst • x.snd；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.instIsTopologicalRingOfIsTopologicalAddGroupOfContinuousSM
ulMulOpposite`：∀ {R : Type u_3} {M : Type u_4} [inst : TopologicalSpace R] [inst
_1 : TopologicalSpace M] [inst_2 : Ring R]   [inst_3 : AddCommGroup M] [ins…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedSpace.expSeries_apply_eq`：expSeries_apply_eq (x : 𝔸) (n : Nat) : (
expSeries 𝕂 𝔸 n fun _ => x) = (n !⁻¹ : 𝕂) • x ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TrivSqZeroExt.snd_pow_of_smul_comm`：snd_pow_of_smul_comm [Monoid R] [Add
Monoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ
 M] (x : tsze R M) (n : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inv_mul_cancel_right₀`：inv_mul_cancel_right₀ (h : b != 0) (a : G₀) : a *
 b⁻¹ * b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem snd_expSeries_of_smul_comm
    (x : tsze R M) (hx : MulOpposite.op x.fst • x.snd = x.fst • x.snd) (n : ℕ) :
    snd (expSeries 𝕜 (tsze R M) (n + 1) fun _ => x) = (expSeries 𝕜 R n fun _ => x.fst) • x.snd := by
  simp_rw [expSeries_apply_eq, snd_smul, snd_pow_of_smul_comm _ _ hx,
    ← Nat.cast_smul_eq_nsmul 𝕜 (n + 1), smul_smul, smul_assoc, Nat.factorial_succ, Nat.pred_succ,
    Nat.cast_mul, mul_inv_rev,
    inv_mul_cancel_right₀ ((Nat.cast_ne_zero (R := 𝕜)).mpr <| Nat.succ_ne_zero n)]

/-- If `NormedSpace.exp R x.fst` converges to `e`
then `(NormedSpace.exp R x).snd` converges to `e • x.snd`. -/
/-
**TrivSqZeroExt.hasSum_snd_expSeries_of_smul_comm** 是 Mathlib 中的一个定理，位于命名空间 `Tri
vSqZeroExt`。
形式化陈述：hasSum_snd_expSeries_of_smul_comm (x : tsze R M) (hx : MulOpposite.op x.fs
t • x.snd = x.fst • x.snd) {e : R} (h : HasSum (fun n => expSeries 𝕜 R n fun _ =
> x.fst) e) : HasSum (fun n => snd (expSeries 𝕜 (tsze R M) n fun _ => x)) (e • x
.snd)
参数：x : tsze R M；hx : MulOpposite.op x.fst • x.snd = x.fst • x.snd；h : HasSum (fu
n n => expSeries 𝕜 R n fun _ => x.fst) e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.instIsTopologicalRingOfIsTopologicalAddGroupOfContinuousSM
ulMulOpposite`：∀ {R : Type u_3} {M : Type u_4} [inst : TopologicalSpace R] [inst
_1 : TopologicalSpace M] [inst_2 : Ring R]   [inst_3 : AddCommGroup M] [ins…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasSum_nat_add_iff'`：∀ {G : Type u_2} [inst : AddCommGroup G] {g : G} [i
nst_1 : TopologicalSpace G] [IsTopologicalAddGroup G] {f : ℕ → G}   (k : ℕ), Has
Sum (fun …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `TrivSqZeroExt.snd_expSeries_of_smul_comm`：snd_expSeries_of_smul_comm (x 
: tsze R M) (hx : MulOpposite.op x.fst • x.snd = x.fst • x.snd) (n : Nat) : snd 
(expSeries 𝕜 (tsze R M) (n + 1…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NormedSpace.expSeries_apply_eq`：expSeries_apply_eq (x : 𝔸) (n : Nat) : (
expSeries 𝕂 𝔸 n fun _ => x) = (n !⁻¹ : 𝕂) • x ^ n
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.range_one`：range_one : range 1 = {0}
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Nat.factorial_zero`：Nat.factorial 0 = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `TrivSqZeroExt.snd_one`：snd_one [One R] [Zero M] : (1 : tsze R M).snd = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `HasSum.smul_const`：HasSum.smul_const {r : R} (hf : HasSum f r L) (a : M)
 : HasSum (fun z => f z • a) (r • a) L

--- 原说明 ---
If `NormedSpace.exp R x.fst` converges to `e`
then `(NormedSpace.exp R x).snd` converges to `e • x.snd`.
-/
theorem hasSum_snd_expSeries_of_smul_comm (x : tsze R M)
    (hx : MulOpposite.op x.fst • x.snd = x.fst • x.snd) {e : R}
    (h : HasSum (fun n => expSeries 𝕜 R n fun _ => x.fst) e) :
    HasSum (fun n => snd (expSeries 𝕜 (tsze R M) n fun _ => x)) (e • x.snd) := by
  rw [← hasSum_nat_add_iff' 1]
  simp_rw [snd_expSeries_of_smul_comm _ _ hx]
  simp_rw [expSeries_apply_eq] at *
  rw [Finset.range_one, Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one, pow_zero,
    inv_one, one_smul, snd_one, sub_zero]
  exact h.smul_const _

/-- If `NormedSpace.exp R x.fst` converges to `e`
then `NormedSpace.exp R x` converges to `inl e + inr (e • x.snd)`. -/
/-
**TrivSqZeroExt.hasSum_expSeries_of_smul_comm** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZ
eroExt`。
形式化陈述：hasSum_expSeries_of_smul_comm (x : tsze R M) (hx : MulOpposite.op x.fst • 
x.snd = x.fst • x.snd) {e : R} (h : HasSum (fun n => expSeries 𝕜 R n fun _ => x.
fst) e) : HasSum (fun n => expSeries 𝕜 (tsze R M) n fun _ => x) (inl e + inr (e 
• x.snd))
参数：x : tsze R M；hx : MulOpposite.op x.fst • x.snd = x.fst • x.snd；h : HasSum (fu
n n => expSeries 𝕜 R n fun _ => x.fst) e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.instIsTopologicalRingOfIsTopologicalAddGroupOfContinuousSM
ulMulOpposite`：∀ {R : Type u_3} {M : Type u_4} [inst : TopologicalSpace R] [inst
_1 : TopologicalSpace M] [inst_2 : Ring R]   [inst_3 : AddCommGroup M] [ins…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `TrivSqZeroExt.fst_expSeries`：∀ (𝕜 : Type u_1) {R : Type u_3} {M : Type u
_4} [inst : Field 𝕜] [inst_1 : Ring R] [inst_2 : AddCommGroup M]   [inst_3 : Alg
ebra 𝕜 R] [inst_4…
· 使用定理 `TrivSqZeroExt.inl_fst_add_inr_snd_eq`：inl_fst_add_inr_snd_eq [AddZeroCla
ss R] [AddZeroClass M] (x : tsze R M) : inl x.fst + inr x.snd = x
· 使用定理 `HasSum.add`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {f g : β → α} {a b : α}   {L : SummationFilter β} [Co
…
· 使用定理 `TrivSqZeroExt.instContinuousAdd`：∀ {R : Type u_3} {M : Type u_4} [inst :
 TopologicalSpace R] [inst_1 : TopologicalSpace M] [inst_2 : Add R]   [inst_3 : 
Add M] [ContinuousAdd…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `TrivSqZeroExt.hasSum_inl`：hasSum_inl [AddCommMonoid R] [AddCommMonoid M]
 {f : α -> R} {a : R} (h : HasSum f a) : HasSum (fun x => inl (f x)) (inl a : ts
ze R M)
· 使用定理 `TrivSqZeroExt.hasSum_inr`：hasSum_inr [AddCommMonoid R] [AddCommMonoid M]
 {f : α -> M} {a : M} (h : HasSum f a) : HasSum (fun x => inr (f x)) (inr a : ts
ze R M)
· 使用定理 `TrivSqZeroExt.hasSum_snd_expSeries_of_smul_comm`：hasSum_snd_expSeries_of
_smul_comm (x : tsze R M) (hx : MulOpposite.op x.fst • x.snd = x.fst • x.snd) {e
 : R} (h : HasSum (fun n => expSeries…

--- 原说明 ---
If `NormedSpace.exp R x.fst` converges to `e`
then `NormedSpace.exp R x` converges to `inl e + inr (e • x.snd)`.
-/
theorem hasSum_expSeries_of_smul_comm
    (x : tsze R M) (hx : MulOpposite.op x.fst • x.snd = x.fst • x.snd)
    {e : R} (h : HasSum (fun n => expSeries 𝕜 R n fun _ => x.fst) e) :
    HasSum (fun n => expSeries 𝕜 (tsze R M) n fun _ => x) (inl e + inr (e • x.snd)) := by
  have : HasSum (fun n => fst (expSeries 𝕜 (tsze R M) n fun _ => x)) e := by
    simpa [fst_expSeries] using h
  simpa only [inl_fst_add_inr_snd_eq] using
    (hasSum_inl _ <| this).add (hasSum_inr _ <| hasSum_snd_expSeries_of_smul_comm 𝕜 x hx h)

variable [Algebra ℚ R] [Module ℚ M]
variable [T2Space R] [T2Space M]
/-
**TrivSqZeroExt.exp_def_of_smul_comm** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：exp_def_of_smul_comm (x : tsze R M) (hx : MulOpposite.op x.fst • x.snd = x
.fst • x.snd) : exp x = inl (exp x.fst) + inr (exp x.fst • x.snd)
参数：x : tsze R M；hx : MulOpposite.op x.fst • x.snd = x.fst • x.snd。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.instIsTopologicalRingOfIsTopologicalAddGroupOfContinuousSM
ulMulOpposite`：∀ {R : Type u_3} {M : Type u_4} [inst : TopologicalSpace R] [inst
_1 : TopologicalSpace M] [inst_2 : Ring R]   [inst_3 : AddCommGroup M] [ins…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `NormedSpace.exp_eq_expSeries_sum`：exp_eq_expSeries_sum [CharZero 𝕂] : ex
p = (expSeries 𝕂 𝔸).sum
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `TrivSqZeroExt.instT2Space`：∀ {R : Type u_3} {M : Type u_4} [inst : Topol
ogicalSpace R] [inst_1 : TopologicalSpace M] [T2Space R] [T2Space M],   T2Space 
(TrivSqZeroExt …
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `TrivSqZeroExt.hasSum_expSeries_of_smul_comm`：hasSum_expSeries_of_smul_co
mm (x : tsze R M) (hx : MulOpposite.op x.fst • x.snd = x.fst • x.snd) {e : R} (h
 : HasSum (fun n => expSeries 𝕜 R…
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用定理 `tsum_eq_zero_of_not_summable`：∀ {α : Type u_1} {β : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → 
α}, ¬Summable f L …
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `TrivSqZeroExt.inr_zero`：inr_zero [Zero R] [Zero M] : (inr 0 : tsze R M) 
= 0
· 使用定理 `TrivSqZeroExt.inl_zero`：inl_zero [Zero R] [Zero M] : (inl 0 : tsze R M) 
= 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Summable.map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Add
CommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {L : SummationFilter β
} …
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `TrivSqZeroExt.continuous_fst`：∀ {R : Type u_3} {M : Type u_4} [inst : To
pologicalSpace R] [inst_1 : TopologicalSpace M], Continuous TrivSqZeroExt.fst
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem exp_def_of_smul_comm (x : tsze R M) (hx : MulOpposite.op x.fst • x.snd = x.fst • x.snd) :
    exp x = inl (exp x.fst) + inr (exp x.fst • x.snd) := by
  simp_rw [exp_eq_expSeries_sum ℚ, FormalMultilinearSeries.sum]
  by_cases h : Summable (fun (n : ℕ) => (expSeries ℚ R n) fun _ ↦ fst x)
  · refine (hasSum_expSeries_of_smul_comm ℚ x hx ?_).tsum_eq
    exact h.hasSum
  · rw [tsum_eq_zero_of_not_summable h, zero_smul, inr_zero, inl_zero, zero_add,
      tsum_eq_zero_of_not_summable]
    simp_rw [← fst_expSeries] at h
    refine mt ?_ h
    exact (Summable.map · (TrivSqZeroExt.fstHom ℚ R M).toLinearMap continuous_fst)

@[simp]
/-
**TrivSqZeroExt.exp_inl** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：exp_inl (x : R) : exp (inl x : tsze R M) = inl (exp x)
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.instIsTopologicalRingOfIsTopologicalAddGroupOfContinuousSM
ulMulOpposite`：∀ {R : Type u_3} {M : Type u_4} [inst : TopologicalSpace R] [inst
_1 : TopologicalSpace M] [inst_2 : Ring R]   [inst_3 : AddCommGroup M] [ins…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TrivSqZeroExt.exp_def_of_smul_comm`：exp_def_of_smul_comm (x : tsze R M) 
(hx : MulOpposite.op x.fst • x.snd = x.fst • x.snd) : exp x = inl (exp x.fst) + 
inr (exp x.fst • x.snd)
· 使用定理 `TrivSqZeroExt.snd_inl`：snd_inl [Zero M] (r : R) : (inl r : tsze R M).snd
 = 0
· 使用定理 `TrivSqZeroExt.fst_inl`：fst_inl [Zero M] (r : R) : (inl r : tsze R M).fst
 = r
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `TrivSqZeroExt.inr_zero`：inr_zero [Zero R] [Zero M] : (inr 0 : tsze R M) 
= 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem exp_inl (x : R) : exp (inl x : tsze R M) = inl (exp x) := by
  rw [exp_def_of_smul_comm, snd_inl, fst_inl, smul_zero, inr_zero, add_zero]
  rw [snd_inl, fst_inl, smul_zero, smul_zero]

@[simp]
/-
**TrivSqZeroExt.exp_inr** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：exp_inr (m : M) : exp (inr m : tsze R M) = 1 + inr m
参数：m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.instIsTopologicalRingOfIsTopologicalAddGroupOfContinuousSM
ulMulOpposite`：∀ {R : Type u_3} {M : Type u_4} [inst : TopologicalSpace R] [inst
_1 : TopologicalSpace M] [inst_2 : Ring R]   [inst_3 : AddCommGroup M] [ins…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TrivSqZeroExt.exp_def_of_smul_comm`：exp_def_of_smul_comm (x : tsze R M) 
(hx : MulOpposite.op x.fst • x.snd = x.fst • x.snd) : exp x = inl (exp x.fst) + 
inr (exp x.fst • x.snd)
· 使用定理 `TrivSqZeroExt.snd_inr`：snd_inr [Zero R] (m : M) : (inr m : tsze R M).snd
 = m
· 使用定理 `TrivSqZeroExt.fst_inr`：fst_inr [Zero R] (m : M) : (inr m : tsze R M).fst
 = 0
· 使用定理 `MulOpposite.op_zero`：∀ {α : Type u_1} [inst : Zero α], MulOpposite.op 0 
= 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `NormedSpace.exp_zero`：exp_zero : exp (0 : 𝔸) = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `TrivSqZeroExt.inl_one`：inl_one [One R] [Zero M] : (inl 1 : tsze R M) = 1
-/
theorem exp_inr (m : M) : exp (inr m : tsze R M) = 1 + inr m := by
  rw [exp_def_of_smul_comm, snd_inr, fst_inr, exp_zero, one_smul, inl_one]
  rw [snd_inr, fst_inr, MulOpposite.op_zero, zero_smul, zero_smul]

end Ring

section CommRing
variable [CommRing R] [AddCommGroup M] [Algebra ℚ R] [Module ℚ M] [Module R M] [Module Rᵐᵒᵖ M]
  [IsCentralScalar R M]
  [TopologicalSpace R] [TopologicalSpace M]
  [IsTopologicalRing R] [IsTopologicalAddGroup M] [ContinuousSMul R M] [ContinuousSMul Rᵐᵒᵖ M]

variable [T2Space R] [T2Space M]

/-
**TrivSqZeroExt.exp_def** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：exp_def (x : tsze R M) : exp x = inl (exp x.fst) + inr (exp x.fst • x.snd)
参数：x : tsze R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.exp_def_of_smul_comm`：exp_def_of_smul_comm (x : tsze R M) 
(hx : MulOpposite.op x.fst • x.snd = x.fst • x.snd) : exp x = inl (exp x.fst) + 
inr (exp x.fst • x.snd)
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.op_right`：∀ {M : Type u_1} {N : Type u_2} {α : Type u_5} [
inst : SMul M α] [inst_1 : SMul M N] [inst_2 : SMul N α]   [inst_3 : SMul Nᵐᵒᵖ α
] [IsCentral…
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
-/
theorem exp_def (x : tsze R M) : exp x = inl (exp x.fst) + inr (exp x.fst • x.snd) :=
  exp_def_of_smul_comm x (op_smul_eq_smul _ _)

@[simp]
/-
**TrivSqZeroExt.fst_exp** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：fst_exp (x : tsze R M) : fst (exp x) = exp x.fst
参数：x : tsze R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.op_right`：∀ {M : Type u_1} {N : Type u_2} {α : Type u_5} [
inst : SMul M α] [inst_1 : SMul M N] [inst_2 : SMul N α]   [inst_3 : SMul Nᵐᵒᵖ α
] [IsCentral…
· 使用定理 `TrivSqZeroExt.instIsTopologicalRingOfIsTopologicalAddGroupOfContinuousSM
ulMulOpposite`：∀ {R : Type u_3} {M : Type u_4} [inst : TopologicalSpace R] [inst
_1 : TopologicalSpace M] [inst_2 : Ring R]   [inst_3 : AddCommGroup M] [ins…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TrivSqZeroExt.exp_def`：exp_def (x : tsze R M) : exp x = inl (exp x.fst) 
+ inr (exp x.fst • x.snd)
· 使用定理 `TrivSqZeroExt.fst_add`：fst_add [Add R] [Add M] (x₁ x₂ : tsze R M) : (x₁ 
+ x₂).fst = x₁.fst + x₂.fst
· 使用定理 `TrivSqZeroExt.fst_inl`：fst_inl [Zero M] (r : R) : (inl r : tsze R M).fst
 = r
· 使用定理 `TrivSqZeroExt.fst_inr`：fst_inr [Zero R] (m : M) : (inr m : tsze R M).fst
 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem fst_exp (x : tsze R M) : fst (exp x) = exp x.fst := by
  rw [exp_def, fst_add, fst_inl, fst_inr, add_zero]

@[simp]
/-
**TrivSqZeroExt.snd_exp** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：snd_exp (x : tsze R M) : snd (exp x) = exp x.fst • x.snd
参数：x : tsze R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.op_right`：∀ {M : Type u_1} {N : Type u_2} {α : Type u_5} [
inst : SMul M α] [inst_1 : SMul M N] [inst_2 : SMul N α]   [inst_3 : SMul Nᵐᵒᵖ α
] [IsCentral…
· 使用定理 `TrivSqZeroExt.instIsTopologicalRingOfIsTopologicalAddGroupOfContinuousSM
ulMulOpposite`：∀ {R : Type u_3} {M : Type u_4} [inst : TopologicalSpace R] [inst
_1 : TopologicalSpace M] [inst_2 : Ring R]   [inst_3 : AddCommGroup M] [ins…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TrivSqZeroExt.exp_def`：exp_def (x : tsze R M) : exp x = inl (exp x.fst) 
+ inr (exp x.fst • x.snd)
· 使用定理 `TrivSqZeroExt.snd_add`：snd_add [Add R] [Add M] (x₁ x₂ : tsze R M) : (x₁ 
+ x₂).snd = x₁.snd + x₂.snd
· 使用定理 `TrivSqZeroExt.snd_inl`：snd_inl [Zero M] (r : R) : (inl r : tsze R M).snd
 = 0
· 使用定理 `TrivSqZeroExt.snd_inr`：snd_inr [Zero R] (m : M) : (inr m : tsze R M).snd
 = m
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem snd_exp (x : tsze R M) : snd (exp x) = exp x.fst • x.snd := by
  rw [exp_def, snd_add, snd_inl, snd_inr, zero_add]

/-- Polar form of trivial-square-zero extension. -/
/-
**TrivSqZeroExt.eq_smul_exp_of_invertible** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroE
xt`。
形式化陈述：eq_smul_exp_of_invertible (x : tsze R M) [Invertible x.fst] : x = x.fst • 
exp (⅟x.fst • inr x.snd)
参数：x : tsze R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.op_right`：∀ {M : Type u_1} {N : Type u_2} {α : Type u_5} [
inst : SMul M α] [inst_1 : SMul M N] [inst_2 : SMul N α]   [inst_3 : SMul Nᵐᵒᵖ α
] [IsCentral…
· 使用定理 `TrivSqZeroExt.instIsTopologicalRingOfIsTopologicalAddGroupOfContinuousSM
ulMulOpposite`：∀ {R : Type u_3} {M : Type u_4} [inst : TopologicalSpace R] [inst
_1 : TopologicalSpace M] [inst_2 : Ring R]   [inst_3 : AddCommGroup M] [ins…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TrivSqZeroExt.inr_smul`：inr_smul [Zero R] [SMulZeroClass S R] [SMul S M]
 (r : S) (m : M) : (inr (r • m) : tsze R M) = r • inr m
· 使用定理 `TrivSqZeroExt.exp_inr`：exp_inr (m : M) : exp (inr m : tsze R M) = 1 + in
r m
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `TrivSqZeroExt.inl_one`：inl_one [One R] [Zero M] : (inl 1 : tsze R M) = 1
· 使用定理 `TrivSqZeroExt.inl_smul`：inl_smul [Monoid S] [AddMonoid M] [SMul S R] [Di
stribMulAction S M] (s : S) (r : R) : (inl (s • r) : tsze R M) = s • inl r
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `mul_invOf_self`：mul_invOf_self [Mul α] [One α] (a : α) [Invertible a] : 
a * ⅟a = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `TrivSqZeroExt.inl_fst_add_inr_snd_eq`：inl_fst_add_inr_snd_eq [AddZeroCla
ss R] [AddZeroClass M] (x : tsze R M) : inl x.fst + inr x.snd = x

--- 原说明 ---
Polar form of trivial-square-zero extension.
-/
theorem eq_smul_exp_of_invertible (x : tsze R M) [Invertible x.fst] :
    x = x.fst • exp (⅟x.fst • inr x.snd) := by
  rw [← inr_smul, exp_inr, smul_add, ← inl_one, ← inl_smul, ← inr_smul, smul_eq_mul, mul_one,
    smul_smul, mul_invOf_self, one_smul, inl_fst_add_inr_snd_eq]

end CommRing

section Field
variable [Field R] [AddCommGroup M]
  [Algebra ℚ R] [Module ℚ M] [Module R M] [Module Rᵐᵒᵖ M]
  [IsCentralScalar R M]
  [TopologicalSpace R] [TopologicalSpace M]
  [IsTopologicalRing R] [IsTopologicalAddGroup M] [ContinuousSMul R M] [ContinuousSMul Rᵐᵒᵖ M]

variable [T2Space R] [T2Space M]

/-- More convenient version of `TrivSqZeroExt.eq_smul_exp_of_invertible` for when `R` is a
field. -/
/-
**TrivSqZeroExt.eq_smul_exp_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`
。
形式化陈述：eq_smul_exp_of_ne_zero (x : tsze R M) (hx : x.fst != 0) : x = x.fst • exp 
(x.fst⁻¹ • inr x.snd)
参数：x : tsze R M；hx : x.fst != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.eq_smul_exp_of_invertible`：eq_smul_exp_of_invertible (x : 
tsze R M) [Invertible x.fst] : x = x.fst • exp (⅟x.fst • inr x.snd)

--- 原说明 ---
More convenient version of `TrivSqZeroExt.eq_smul_exp_of_invertible` for when `R
` is a
field.
-/
theorem eq_smul_exp_of_ne_zero (x : tsze R M) (hx : x.fst ≠ 0) :
    x = x.fst • exp (x.fst⁻¹ • inr x.snd) :=
  letI : Invertible x.fst := invertibleOfNonzero hx
  eq_smul_exp_of_invertible _

end Field

end Topology

/-!
### The $ℓ^1$ norm on the trivial square zero extension
-/

noncomputable section Seminormed

section Ring
variable [SeminormedCommRing S] [SeminormedRing R] [SeminormedAddCommGroup M]
variable [Algebra S R] [Module S M]
variable [IsBoundedSMul S R] [IsBoundedSMul S M]

/-
**TrivSqZeroExt.instL1SeminormedAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZe
roExt`。
形式化陈述：instL1SeminormedAddCommGroup : SeminormedAddCommGroup (tsze R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instL1SeminormedAddCommGroup : SeminormedAddCommGroup (tsze R M) :=
  fast_instance% {
    WithLp.seminormedAddCommGroupToProd 1 R M with
    toUniformSpace := inferInstance }
/-
**TrivSqZeroExt.** 是 Mathlib 中的一个示例，位于命名空间 `TrivSqZeroExt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example :
    (TrivSqZeroExt.instUniformSpace : UniformSpace (tsze R M)) =
    PseudoMetricSpace.toUniformSpace := rfl

set_option backward.isDefEq.respectTransparency false in
/-
**TrivSqZeroExt.norm_def** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：norm_def (x : tsze R M) : ‖x‖ = ‖fst x‖ + ‖snd x‖
参数：x : tsze R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用引理 `WithLp.norm_seminormedAddCommGroupToProd`：norm_seminormedAddCommGroupToP
rod [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] (x : α × β) : @Norm.no
rm _ (seminormedAddCommGroupTo…
· 使用定理 `WithLp.prod_norm_eq_add`：prod_norm_eq_add (hp : 0 < p.toReal) (f : WithL
p p (α × β)) : ‖f‖ = (‖f.fst‖ ^ p.toReal + ‖f.snd‖ ^ p.toReal) ^ (1 / p.toReal)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_def (x : tsze R M) : ‖x‖ = ‖fst x‖ + ‖snd x‖ := by
  erw [WithLp.norm_seminormedAddCommGroupToProd]
  rw [WithLp.prod_norm_eq_add (by norm_num)]
  simp only [WithLp.toLp_fst, ENNReal.toReal_one, Real.rpow_one, WithLp.toLp_snd, ne_eq,
    one_ne_zero, not_false_eq_true, div_self, fst, snd]
/-
**TrivSqZeroExt.nnnorm_def** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：nnnorm_def (x : tsze R M) : ‖x‖₊ = ‖fst x‖₊ + ‖snd x‖₊
参数：x : tsze R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TrivSqZeroExt.norm_def`：norm_def (x : tsze R M) : ‖x‖ = ‖fst x‖ + ‖snd x
‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nnnorm_def (x : tsze R M) : ‖x‖₊ = ‖fst x‖₊ + ‖snd x‖₊ := by
  ext; simp [norm_def]
/-
**TrivSqZeroExt.norm_inl** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：∀ {R : Type u_3} {M : Type u_4} [inst : SeminormedRing R] [inst_1 : Semino
rmedAddCommGroup M] (r : R),   ‖TrivSqZeroExt.inl r‖ = ‖r‖
参数：r : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TrivSqZeroExt.norm_def`：norm_def (x : tsze R M) : ‖x‖ = ‖fst x‖ + ‖snd x
‖
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem norm_inl (r : R) : ‖(inl r : tsze R M)‖ = ‖r‖ := by simp [norm_def]
/-
**TrivSqZeroExt.norm_inr** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：∀ {R : Type u_3} {M : Type u_4} [inst : SeminormedRing R] [inst_1 : Semino
rmedAddCommGroup M] (m : M),   ‖TrivSqZeroExt.inr m‖ = ‖m‖
参数：m : M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TrivSqZeroExt.norm_def`：norm_def (x : tsze R M) : ‖x‖ = ‖fst x‖ + ‖snd x
‖
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem norm_inr (m : M) : ‖(inr m : tsze R M)‖ = ‖m‖ := by simp [norm_def]
/-
**TrivSqZeroExt.nnnorm_inl** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：∀ {R : Type u_3} {M : Type u_4} [inst : SeminormedRing R] [inst_1 : Semino
rmedAddCommGroup M] (r : R),   ‖TrivSqZeroExt.inl r‖₊ = ‖r‖₊
参数：r : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TrivSqZeroExt.nnnorm_def`：nnnorm_def (x : tsze R M) : ‖x‖₊ = ‖fst x‖₊ + 
‖snd x‖₊
· 使用定理 `nnnorm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖₊ = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem nnnorm_inl (r : R) : ‖(inl r : tsze R M)‖₊ = ‖r‖₊ := by simp [nnnorm_def]
/-
**TrivSqZeroExt.nnnorm_inr** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：∀ {R : Type u_3} {M : Type u_4} [inst : SeminormedRing R] [inst_1 : Semino
rmedAddCommGroup M] (m : M),   ‖TrivSqZeroExt.inr m‖₊ = ‖m‖₊
参数：m : M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TrivSqZeroExt.nnnorm_def`：nnnorm_def (x : tsze R M) : ‖x‖₊ = ‖fst x‖₊ + 
‖snd x‖₊
· 使用定理 `nnnorm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖₊ = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem nnnorm_inr (m : M) : ‖(inr m : tsze R M)‖₊ = ‖m‖₊ := by simp [nnnorm_def]

variable [Module R M] [IsBoundedSMul R M] [Module Rᵐᵒᵖ M] [IsBoundedSMul Rᵐᵒᵖ M]
  [SMulCommClass R Rᵐᵒᵖ M]

set_option backward.isDefEq.respectTransparency false in
/-
**TrivSqZeroExt.instL1SeminormedRing** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
形式化陈述：instL1SeminormedRing : SeminormedRing (tsze R M) where norm_mul_le | ⟨r₁, 
m₁⟩, ⟨r₂, m₂⟩ => by simp_rw [norm_def] calc ‖r₁ * r₂‖ + ‖r₁ • m₂ + MulOpposite.o
p r₂ • m₁‖ _ <= ‖r₁‖ * ‖r₂‖ + (‖r₁‖ * ‖m₂‖ + ‖r₂‖ * ‖m₁‖)
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instL1SeminormedRing : SeminormedRing (tsze R M) where
  norm_mul_le
  | ⟨r₁, m₁⟩, ⟨r₂, m₂⟩ => by
    simp_rw [norm_def]
    calc ‖r₁ * r₂‖ + ‖r₁ • m₂ + MulOpposite.op r₂ • m₁‖
    _ ≤ ‖r₁‖ * ‖r₂‖ + (‖r₁‖ * ‖m₂‖ + ‖r₂‖ * ‖m₁‖) := by
      gcongr
      · apply norm_mul_le
      · refine norm_add_le_of_le ?_ ?_ <;>
        apply norm_smul_le
    _ ≤ ‖r₁‖ * ‖r₂‖ + (‖r₁‖ * ‖m₂‖ + ‖r₂‖ * ‖m₁‖) + (‖m₁‖ * ‖m₂‖) := by
      apply le_add_of_nonneg_right
      positivity
    _ = (‖r₁‖ + ‖m₁‖) * (‖r₂‖ + ‖m₂‖) := by ring
  __ : Ring (tsze R M) := inferInstance
  __ : SeminormedAddCommGroup (tsze R M) := inferInstance
/-
**TrivSqZeroExt.instL1IsBoundedSMul** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
形式化陈述：instL1IsBoundedSMul : IsBoundedSMul S (tsze R M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `WithLp.isBoundedSMulSeminormedAddCommGroupToProd`：isBoundedSMulSeminorme
dAddCommGroupToProd [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] {R : T
ype*} [SeminormedRing R] [Module R α] …
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
-/
instance instL1IsBoundedSMul : IsBoundedSMul S (tsze R M) :=
  WithLp.isBoundedSMulSeminormedAddCommGroupToProd 1 R M
/-
**TrivSqZeroExt.** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NormOneClass R] : NormOneClass (tsze R M) where
  norm_one := by rw [norm_def, fst_one, snd_one, norm_zero, norm_one, add_zero]

end Ring

section CommRing

variable [SeminormedCommRing R] [SeminormedAddCommGroup M]
variable [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
variable [IsBoundedSMul R M]

/-
**TrivSqZeroExt.instL1SeminormedCommRing** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroEx
t`。
形式化陈述：instL1SeminormedCommRing : SeminormedCommRing (tsze R M) where __ : Semino
rmedRing (tsze R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instL1SeminormedCommRing : SeminormedCommRing (tsze R M) where
  __ : SeminormedRing (tsze R M) := inferInstance
  __ : CommRing (tsze R M) := inferInstance

end CommRing

end Seminormed

noncomputable section Normed

section Ring

variable [NormedRing R] [NormedAddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
variable [IsBoundedSMul R M] [IsBoundedSMul Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]

/-
**TrivSqZeroExt.instL1NormedAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroEx
t`。
形式化陈述：instL1NormedAddCommGroup : NormedAddCommGroup (tsze R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instL1NormedAddCommGroup : NormedAddCommGroup (tsze R M) :=
  fast_instance% WithLp.normedAddCommGroupToProd 1 R M
/-
**TrivSqZeroExt.instL1NormedRing** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
形式化陈述：instL1NormedRing : NormedRing (tsze R M) where __ : SeminormedRing (tsze R
 M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instL1NormedRing : NormedRing (tsze R M) where
  __ : SeminormedRing (tsze R M) := inferInstance
  __ : NormedAddCommGroup (tsze R M) := inferInstance

end Ring

section CommRing

variable [NormedCommRing R] [NormedAddCommGroup M]
variable [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
variable [IsBoundedSMul R M]

/-
**TrivSqZeroExt.instL1NormedCommRing** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
形式化陈述：instL1NormedCommRing : NormedCommRing (tsze R M) where __ : NormedRing (ts
ze R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instL1NormedCommRing : NormedCommRing (tsze R M) where
  __ : NormedRing (tsze R M) := inferInstance
  __ : CommRing (tsze R M) := inferInstance

end CommRing

section Algebra

variable [NormedField 𝕜] [NormedRing R] [NormedAddCommGroup M]
variable [NormedAlgebra 𝕜 R] [NormedSpace 𝕜 M] [Module R M] [Module Rᵐᵒᵖ M]
variable [IsBoundedSMul R M] [IsBoundedSMul Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]
variable [IsScalarTower 𝕜 R M] [IsScalarTower 𝕜 Rᵐᵒᵖ M]

/-
**TrivSqZeroExt.instL1NormedSpace** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
形式化陈述：instL1NormedSpace : NormedSpace 𝕜 (tsze R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instL1NormedSpace : NormedSpace 𝕜 (tsze R M) :=
  fast_instance% WithLp.normedSpaceSeminormedAddCommGroupToProd 1 R M
/-
**TrivSqZeroExt.instL1NormedAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
形式化陈述：instL1NormedAlgebra : NormedAlgebra 𝕜 (tsze R M) where norm_smul_le
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instL1NormedAlgebra : NormedAlgebra 𝕜 (tsze R M) where
  norm_smul_le := _root_.norm_smul_le

end Algebra


end Normed

section

variable [NormedRing R] [NormedAddCommGroup M]
variable [NormedAlgebra ℚ R] [NormedSpace ℚ M] [Module R M] [Module Rᵐᵒᵖ M]
variable [IsBoundedSMul R M] [IsBoundedSMul Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]
variable [CompleteSpace R] [CompleteSpace M]

-- Evidence that we have sufficient instances on `tsze R N`
-- to make `NormedSpace.exp_add_of_commute` usable
/-
**TrivSqZeroExt.** 是 Mathlib 中的一个示例，位于命名空间 `TrivSqZeroExt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (a b : tsze R M) (h : Commute a b) : exp (a + b) = exp a * exp b :=
  exp_add_of_commute h

end

end TrivSqZeroExt

