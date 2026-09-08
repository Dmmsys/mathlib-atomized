/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Eric Wieser, Yuyang Zhao
-/
module

public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Algebra.Ring.Action.ConjAct
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Analysis.Analytic.OfScalars

/-!
# Exponential in a Banach algebra

In this file, we define `NormedSpace.exp : 𝔸 → 𝔸`,
the exponential map in a topological algebra `𝔸`.

While for most interesting results we need `𝔸` to be normed algebra, we do not require this in the
definition in order to make `NormedSpace.exp` independent of a particular choice of norm. The
definition also does not require that `𝔸` be complete, but we need to assume it for most results.

We then prove some basic results, but we avoid importing derivatives here to minimize dependencies.
Results involving derivatives and comparisons with `Real.exp` and `Complex.exp` can be found in
`Analysis.SpecialFunctions.Exponential`.

## Main results

We prove most result for an arbitrary field `𝕂`, and then specialize to `𝕂 = ℝ` or `𝕂 = ℂ`.

### General case

- `NormedSpace.exp_add_of_commute_of_mem_ball` : if `𝕂` has characteristic zero,
  then given two commuting elements `x` and `y` in the disk of convergence, we have
  `NormedSpace.exp (x+y) = (NormedSpace.exp x) * (NormedSpace.exp y)`
- `NormedSpace.exp_add_of_mem_ball` : if `𝕂` has characteristic zero and `𝔸` is commutative,
  then given two elements `x` and `y` in the disk of convergence, we have
  `NormedSpace.exp (x+y) = (NormedSpace.exp x) * (NormedSpace.exp y)`
- `NormedSpace.exp_neg_of_mem_ball` : if `𝕂` has characteristic zero and `𝔸` is a division ring,
  then given an element `x` in the disk of convergence,
  we have `NormedSpace.exp (-x) = (NormedSpace.exp x)⁻¹`.

### `𝕂 = ℝ` or `𝕂 = ℂ`

- `expSeries_radius_eq_top` : the `FormalMultilinearSeries` defining `NormedSpace.exp`
  has infinite radius of convergence
- `NormedSpace.exp_add_of_commute` : given two commuting elements `x` and `y`, we have
  `NormedSpace.exp (x+y) = (NormedSpace.exp x) * (NormedSpace.exp y)`
- `NormedSpace.exp_add` : if `𝔸` is commutative, then we have
  `NormedSpace.exp (x+y) = (NormedSpace.exp x) * (NormedSpace.exp y)` for any `x` and `y`
- `NormedSpace.exp_neg` : if `𝔸` is a division ring, then we have
  `NormedSpace.exp (-x) = (NormedSpace.exp x)⁻¹`.
- `NormedSpace.exp_sum_of_commute` : the analogous result to `NormedSpace.exp_add_of_commute`
  for `Finset.sum`.
- `NormedSpace.exp_sum` : the analogous result to `NormedSpace.exp_add` for `Finset.sum`.
- `NormedSpace.exp_nsmul` : repeated addition in the domain corresponds to
  repeated multiplication in the codomain.
- `NormedSpace.exp_zsmul` : repeated addition in the domain corresponds to
  repeated multiplication in the codomain.

### Notes

We put nearly all the statements in this file in the `NormedSpace` namespace,
to avoid collisions with the `Real` or `Complex` namespaces.

As of 2023-11-16 due to bad instances in Mathlib
```
import Mathlib

open Real

#time example (x : ℝ) : 0 < exp x      := exp_pos _ -- 250ms
#time example (x : ℝ) : 0 < Real.exp x := exp_pos _ -- 2ms
```
This is because `exp x` tries the `NormedSpace.exp 𝕂 : 𝔸 → 𝔸` function previously defined here,
and generates a slow coercion search from `Real` to `Type`, to fit the first argument here.
We will resolve this slow coercion separately,
but we want to move `exp` out of the root namespace in any case to avoid this ambiguity.

To avoid explicitly passing the base field `𝕂`, we currently fix `𝕂 = ℚ` in the definition of
`NormedSpace.exp : 𝔸 → 𝔸`. If `𝔸` can be equipped with a `ℚ`-algebra structure, we use
`Classical.choice` to pick the unique `Algebra ℚ 𝔸` instead of requiring an instance argument.
This eliminates the need to provide `Algebra ℚ 𝔸` every time `exp` is used. If `𝔸` can't be equipped
with a `ℚ`-algebra structure, we use the junk value `1`.

In the long term it may be possible to replace `Real.exp` and `Complex.exp` with `NormedSpace.exp`
and move it back to the root namespace.
-/

@[expose] public section


namespace NormedSpace

open Filter RCLike ContinuousMultilinearMap NormedField Asymptotics FormalMultilinearSeries

open scoped Nat Topology ENNReal Ring

section TopologicalAlgebra

variable (𝕂 𝔸 : Type*) [Field 𝕂] [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸]

/-- `expSeries 𝕂 𝔸` is the `FormalMultilinearSeries` whose `n`-th term is the map
`(xᵢ) : 𝔸ⁿ ↦ (1/n! : 𝕂) • ∏ xᵢ`. Its sum is the exponential map `NormedSpace.exp : 𝔸 → 𝔸`. -/
/-
**NormedSpace.expSeries** 是 Mathlib 中的一个定义，位于命名空间 `NormedSpace`。
形式化陈述：expSeries : FormalMultilinearSeries 𝕂 𝔸 𝔸
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`expSeries 𝕂 𝔸` is the `FormalMultilinearSeries` whose `n`-th term is the map
`(xᵢ) : 𝔸ⁿ ↦ (1/n! : 𝕂) • ∏ xᵢ`. Its sum is the exponential map `NormedSpace.exp
 : 𝔸 → 𝔸`.
-/
def expSeries : FormalMultilinearSeries 𝕂 𝔸 𝔸 := fun n =>
  (n !⁻¹ : 𝕂) • ContinuousMultilinearMap.mkPiAlgebraFin 𝕂 n 𝔸

/-- The exponential series as an `ofScalars` series. -/
/-
**NormedSpace.expSeries_eq_ofScalars** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：expSeries_eq_ofScalars : expSeries 𝕂 𝔸 = ofScalars 𝔸 fun n => (n !⁻¹ : 𝕂)
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
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
The exponential series as an `ofScalars` series.
-/
theorem expSeries_eq_ofScalars : expSeries 𝕂 𝔸 = ofScalars 𝔸 fun n ↦ (n !⁻¹ : 𝕂) := by
  simp_rw [FormalMultilinearSeries.ext_iff, expSeries, ofScalars, implies_true]

variable {𝕂 𝔸}

open scoped Classical in
/-- `NormedSpace.exp : 𝔸 → 𝔸` is the exponential map. It is defined as the sum of the
`FormalMultilinearSeries` `expSeries ℚ 𝔸`.

If `𝔸` can't be equipped with a `ℚ`-algebra structure, we use the junk value `1`. For details on why
this approach is taken, see the module documentation for
`Mathlib/Analysis/Normed/Algebra/Exponential.lean`.

Note that when `𝔸 = Matrix n n 𝕂`, this is the **Matrix Exponential**; see
`Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean` for lemmas
specific to that case. -/
noncomputable irreducible_def exp (x : 𝔸) : 𝔸 :=
  if h : Nonempty (Algebra ℚ 𝔸) then
    letI _ := h.some
    (NormedSpace.expSeries ℚ 𝔸).sum x
  else
    1

/-- The junk value when `𝔸` can't be equipped with a `ℚ`-algebra structure. -/
@[simp]
/-
**NormedSpace.exp_of_isEmpty_algebra_rat** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`
。
形式化陈述：exp_of_isEmpty_algebra_rat [IsEmpty (Algebra Rat 𝔸)] (x : 𝔸) : exp x = 1
参数：Algebra Rat 𝔸；x : 𝔸。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedSpace.exp_def`：∀ {𝔸 : Type u_3} [inst : Ring 𝔸] [inst_1 : Topologi
calSpace 𝔸] [inst_2 : IsTopologicalRing 𝔸] (x : 𝔸),   NormedSpace.exp x = if h :
 Nonempty…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_nonempty_iff`：not_nonempty_iff : ¬Nonempty α ↔ IsEmpty α

--- 原说明 ---
The junk value when `𝔸` can't be equipped with a `ℚ`-algebra structure.
-/
theorem exp_of_isEmpty_algebra_rat [IsEmpty (Algebra ℚ 𝔸)] (x : 𝔸) : exp x = 1 := by
  rw [exp, dif_neg (not_nonempty_iff.mpr ‹_›)]
/-
**NormedSpace.expSeries_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：expSeries_apply_eq (x : 𝔸) (n : Nat) : (expSeries 𝕂 𝔸 n fun _ => x) = (n !
⁻¹ : 𝕂) • x ^ n
参数：x : 𝔸；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousMultilinearMap.instIsSMulApplyForall`：∀ {ι : Type v} {M₁ : ι →
 Type w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCo
mmMonoid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `List.ofFn_const`：∀ {α : Type u} (n : ℕ) (c : α), (List.ofFn fun x => c) 
= List.replicate n c
· 使用定理 `List.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n a).
prod = a ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem expSeries_apply_eq (x : 𝔸) (n : ℕ) :
    (expSeries 𝕂 𝔸 n fun _ => x) = (n !⁻¹ : 𝕂) • x ^ n := by simp [expSeries]
/-
**NormedSpace.expSeries_apply_eq'** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：expSeries_apply_eq' (x : 𝔸) : (fun n => expSeries 𝕂 𝔸 n fun _ => x) = fun 
n => (n !⁻¹ : 𝕂) • x ^ n
参数：x : 𝔸。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NormedSpace.expSeries_apply_eq`：expSeries_apply_eq (x : 𝔸) (n : Nat) : (
expSeries 𝕂 𝔸 n fun _ => x) = (n !⁻¹ : 𝕂) • x ^ n
-/
theorem expSeries_apply_eq' (x : 𝔸) :
    (fun n => expSeries 𝕂 𝔸 n fun _ => x) = fun n => (n !⁻¹ : 𝕂) • x ^ n :=
  funext (expSeries_apply_eq x)
/-
**NormedSpace.expSeries_sum_eq** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：expSeries_sum_eq (x : 𝔸) : (expSeries 𝕂 𝔸).sum x = ∑' n : Nat, (n !⁻¹ : 𝕂)
 • x ^ n
参数：x : 𝔸。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsum_congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {L : SummationFilter β}   {f g : β → α}, (∀ (b : β), 
…
· 使用定理 `NormedSpace.expSeries_apply_eq`：expSeries_apply_eq (x : 𝔸) (n : Nat) : (
expSeries 𝕂 𝔸 n fun _ => x) = (n !⁻¹ : 𝕂) • x ^ n
-/
theorem expSeries_sum_eq (x : 𝔸) : (expSeries 𝕂 𝔸).sum x = ∑' n : ℕ, (n !⁻¹ : 𝕂) • x ^ n :=
  tsum_congr fun n => expSeries_apply_eq x n
/-
**NormedSpace.expSeries_sum_eq_rat** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：expSeries_sum_eq_rat [Algebra Rat 𝔸] : (expSeries 𝕂 𝔸).sum = (expSeries Ra
t 𝔸).sum
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
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
· 使用定理 `NormedSpace.expSeries_sum_eq`：expSeries_sum_eq (x : 𝔸) : (expSeries 𝕂 𝔸)
.sum x = ∑' n : Nat, (n !⁻¹ : 𝕂) • x ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_natCast_smul_eq`：inv_natCast_smul_eq {E : Type*} (R S : Type*) [AddC
ommMonoid E] [DivisionSemiring R] [DivisionSemiring S] [Module R E] [Module S E]
 (n : Nat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem expSeries_sum_eq_rat [Algebra ℚ 𝔸] : (expSeries 𝕂 𝔸).sum = (expSeries ℚ 𝔸).sum := by
  ext; simp_rw [expSeries_sum_eq, inv_natCast_smul_eq 𝕂 ℚ]
/-
**NormedSpace.expSeries_eq_expSeries_rat** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`
。
形式化陈述：expSeries_eq_expSeries_rat [Algebra Rat 𝔸] (n : Nat) : ⇑(expSeries 𝕂 𝔸 n) 
= expSeries Rat 𝔸 n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_natCast_smul_eq`：inv_natCast_smul_eq {E : Type*} (R S : Type*) [AddC
ommMonoid E] [DivisionSemiring R] [DivisionSemiring S] [Module R E] [Module S E]
 (n : Nat…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousMultilinearMap.instIsSMulApplyForall`：∀ {ι : Type v} {M₁ : ι →
 Type w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCo
mmMonoid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem expSeries_eq_expSeries_rat [Algebra ℚ 𝔸] (n : ℕ) :
    ⇑(expSeries 𝕂 𝔸 n) = expSeries ℚ 𝔸 n := by
  ext c
  simp [expSeries, inv_natCast_smul_eq 𝕂 ℚ]

variable (𝕂) in
/-
**NormedSpace.exp_eq_expSeries_sum** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：exp_eq_expSeries_sum [CharZero 𝕂] : exp = (expSeries 𝕂 𝔸).sum
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedSpace.exp_def`：∀ {𝔸 : Type u_3} [inst : Ring 𝔸] [inst_1 : Topologi
calSpace 𝔸] [inst_2 : IsTopologicalRing 𝔸] (x : 𝔸),   NormedSpace.exp x = if h :
 Nonempty…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NormedSpace.expSeries_sum_eq_rat`：expSeries_sum_eq_rat [Algebra Rat 𝔸] :
 (expSeries 𝕂 𝔸).sum = (expSeries Rat 𝔸).sum
-/
theorem exp_eq_expSeries_sum [CharZero 𝕂] : exp = (expSeries 𝕂 𝔸).sum := by
  ext x
  rw [exp, dif_pos ⟨RestrictScalars.algebra ℚ 𝕂 𝔸⟩, ← @expSeries_sum_eq_rat (𝕂 := 𝕂)]

variable (𝕂) in
/-
**NormedSpace.exp_eq_tsum** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：exp_eq_tsum [CharZero 𝕂] : exp = fun x : 𝔸 => ∑' n : Nat, (n !⁻¹ : 𝕂) • x 
^ n
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
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedSpace.exp_eq_expSeries_sum`：exp_eq_expSeries_sum [CharZero 𝕂] : ex
p = (expSeries 𝕂 𝔸).sum
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NormedSpace.expSeries_sum_eq`：expSeries_sum_eq (x : 𝔸) : (expSeries 𝕂 𝔸)
.sum x = ∑' n : Nat, (n !⁻¹ : 𝕂) • x ^ n
-/
theorem exp_eq_tsum [CharZero 𝕂] : exp = fun x : 𝔸 => ∑' n : ℕ, (n !⁻¹ : 𝕂) • x ^ n := by
  rw [exp_eq_expSeries_sum 𝕂]
  ext x
  exact expSeries_sum_eq x
/-
**NormedSpace.exp_eq_tsum_rat** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：exp_eq_tsum_rat [Algebra Rat 𝔸] : exp = fun x : 𝔸 => ∑' n : Nat, (n !⁻¹ : 
Rat) • x ^ n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedSpace.exp_eq_tsum`：exp_eq_tsum [CharZero 𝕂] : exp = fun x : 𝔸 => ∑
' n : Nat, (n !⁻¹ : 𝕂) • x ^ n
-/
theorem exp_eq_tsum_rat [Algebra ℚ 𝔸] : exp = fun x : 𝔸 => ∑' n : ℕ, (n !⁻¹ : ℚ) • x ^ n :=
  exp_eq_tsum ℚ

variable (𝕂) in
/-- The exponential sum as an `ofScalarsSum`. -/
/-
**NormedSpace.exp_eq_ofScalarsSum** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：exp_eq_ofScalarsSum [CharZero 𝕂] : exp = ofScalarsSum (E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedSpace.exp_eq_tsum`：exp_eq_tsum [CharZero 𝕂] : exp = fun x : 𝔸 => ∑
' n : Nat, (n !⁻¹ : 𝕂) • x ^ n
· 使用定理 `FormalMultilinearSeries.ofScalarsSum_eq_tsum`：ofScalarsSum_eq_tsum : ofS
calarsSum c = fun (x : E) => ∑' n : Nat, c n • x ^ n

--- 原说明 ---
The exponential sum as an `ofScalarsSum`.
-/
theorem exp_eq_ofScalarsSum [CharZero 𝕂] :
    exp = ofScalarsSum (E := 𝔸) fun n ↦ (n !⁻¹ : 𝕂) := by
  rw [exp_eq_tsum 𝕂, ofScalarsSum_eq_tsum]
/-
**NormedSpace.expSeries_apply_zero** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：expSeries_apply_zero (n : Nat) : expSeries 𝕂 𝔸 n (fun _ => (0 : 𝔸)) = Pi.s
ingle (M
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedSpace.expSeries_apply_eq`：expSeries_apply_eq (x : 𝔸) (n : Nat) : (
expSeries 𝕂 𝔸 n fun _ => x) = (n !⁻¹ : 𝕂) • x ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
-/
theorem expSeries_apply_zero (n : ℕ) :
    expSeries 𝕂 𝔸 n (fun _ => (0 : 𝔸)) = Pi.single (M := fun _ => 𝔸) 0 1 n := by
  rw [expSeries_apply_eq]
  rcases n with - | n
  · simp
  · rw [zero_pow (Nat.succ_ne_zero _), smul_zero, Pi.single_eq_of_ne n.succ_ne_zero]

@[simp]
/-
**NormedSpace.exp_zero** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：exp_zero : exp (0 : 𝔸) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedSpace.exp_def`：∀ {𝔸 : Type u_3} [inst : Ring 𝔸] [inst_1 : Topologi
calSpace 𝔸] [inst_2 : IsTopologicalRing 𝔸] (x : 𝔸),   NormedSpace.exp x = if h :
 Nonempty…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `NormedSpace.expSeries_sum_eq`：expSeries_sum_eq (x : 𝔸) : (expSeries 𝕂 𝔸)
.sum x = ∑' n : Nat, (n !⁻¹ : 𝕂) • x ^ n
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NormedSpace.expSeries_apply_zero`：expSeries_apply_zero (n : Nat) : expSe
ries 𝕂 𝔸 n (fun _ => (0 : 𝔸)) = Pi.single (M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `tsum_pi_single`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] [inst_2 : DecidableEq β] (b : β)   (a : α), ∑' (b
' : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem exp_zero : exp (0 : 𝔸) = 1 := by
  rw [exp]
  split_ifs
  · simp_rw [expSeries_sum_eq, ← expSeries_apply_eq, expSeries_apply_zero, tsum_pi_single]
  · rfl

@[simp]
/-
**NormedSpace.exp_op** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：exp_op [T2Space 𝔸] (x : 𝔸) : exp (MulOpposite.op x) = MulOpposite.op (exp 
x)
参数：x : 𝔸。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalRingMulOpposite`：∀ {R : Type u_1} [inst : NonUnitalNonA
ssocRing R] [inst_1 : TopologicalSpace R] [IsTopologicalRing R],   IsTopological
Ring Rᵐᵒᵖ
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedSpace.exp_of_isEmpty_algebra_rat`：exp_of_isEmpty_algebra_rat [IsEm
pty (Algebra Rat 𝔸)] (x : 𝔸) : exp x = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `NormedSpace.exp_eq_tsum`：exp_eq_tsum [CharZero 𝕂] : exp = fun x : 𝔸 => ∑
' n : Nat, (n !⁻¹ : 𝕂) • x ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `tsum_op`：tsum_op [T2Space α] : ∑'[L] x, op (f x) = op (∑'[L] x, f x)
-/
theorem exp_op [T2Space 𝔸] (x : 𝔸) :
    exp (MulOpposite.op x) = MulOpposite.op (exp x) := by
  obtain h | ⟨⟨_⟩⟩ := isEmpty_or_nonempty (Algebra ℚ 𝔸)
  · have : IsEmpty (Algebra ℚ 𝔸ᵐᵒᵖ) := ⟨fun _ => h.elim <| (RingEquiv.opOp 𝔸).algebra ℚ⟩
    simp
  · rw [exp_eq_tsum ℚ, exp_eq_tsum ℚ]
    simp_rw [← MulOpposite.op_pow, ← MulOpposite.op_smul, tsum_op]

@[simp]
/-
**NormedSpace.exp_unop** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：exp_unop [T2Space 𝔸] (x : 𝔸ᵐᵒᵖ) : exp (MulOpposite.unop x) = MulOpposite.u
nop (exp x)
参数：x : 𝔸ᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalRingMulOpposite`：∀ {R : Type u_1} [inst : NonUnitalNonA
ssocRing R] [inst_1 : TopologicalSpace R] [IsTopologicalRing R],   IsTopological
Ring Rᵐᵒᵖ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedSpace.exp_op`：exp_op [T2Space 𝔸] (x : 𝔸) : exp (MulOpposite.op x) 
= MulOpposite.op (exp x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem exp_unop [T2Space 𝔸] (x : 𝔸ᵐᵒᵖ) :
    exp (MulOpposite.unop x) = MulOpposite.unop (exp x) := by
  induction x; simp
/-
**NormedSpace.star_exp** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：star_exp [T2Space 𝔸] [StarRing 𝔸] [ContinuousStar 𝔸] (x : 𝔸) : star (exp x
) = exp (star x)
参数：x : 𝔸。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedSpace.exp_of_isEmpty_algebra_rat`：exp_of_isEmpty_algebra_rat [IsEm
pty (Algebra Rat 𝔸)] (x : 𝔸) : exp x = 1
· 使用定理 `star_one`：star_one [MulOneClass R] [StarMul R] : star (1 : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `NormedSpace.exp_eq_tsum`：exp_eq_tsum [CharZero 𝕂] : exp = fun x : 𝔸 => ∑
' n : Nat, (n !⁻¹ : 𝕂) • x ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem star_exp [T2Space 𝔸] [StarRing 𝔸] [ContinuousStar 𝔸] (x : 𝔸) :
    star (exp x) = exp (star x) := by
  obtain _ | ⟨⟨_⟩⟩ := isEmpty_or_nonempty (Algebra ℚ 𝔸)
  · simp
  · simp_rw [exp_eq_tsum ℚ, ← star_pow, ← star_inv_natCast_smul, ← tsum_star]

/-- A subalgebra of `𝔸` that is closed topologically and under `ℚ`-scaling is closed under `exp`. -/
/-
**NormedSpace.exp_mem** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：exp_mem {R S : Type*} [Monoid R] [SMul Rat R] [MulAction R 𝔸] [Algebra Rat
 𝔸] [IsScalarTower Rat R 𝔸] [SetLike S 𝔸] [SubsemiringClass S 𝔸] [SMulMemClass S
 R 𝔸] {s : S} (h_closed : IsClosed (s : Set 𝔸)) {x : 𝔸} (h : x in s) : exp x in 
s
参数：h_closed : IsClosed (s : Set 𝔸)；h : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SMulMemClass.ofIsScalarTower`：∀ (S : Type u_1) (M : Type u_2) (N : Type 
u_3) (α : Type u_4) [inst : SetLike S α] [inst_1 : SMul M N]   [inst_2 : SMul M 
α] [inst_3 : Monoi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedSpace.exp_eq_tsum`：exp_eq_tsum [CharZero 𝕂] : exp = fun x : 𝔸 => ∑
' n : Nat, (n !⁻¹ : 𝕂) • x ^ n
· 使用定理 `tsum_mem`：∀ {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : Topologica
lSpace α] {ι : Type u_4} {S : Type u_5} {s : S}   [inst_2 : SetLike S α] [AddS…
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …
· 使用定理 `pow_mem`：∀ {M : Type u_3} {A : Type u_4} [inst : Monoid M] [inst_1 : Set
Like A M] [SubmonoidClass A M] {S : A} {x : M},   x ∈ S → ∀ (n : ℕ), x ^ n ∈ …
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …

--- 原说明 ---
A subalgebra of `𝔸` that is closed topologically and under `ℚ`-scaling is closed
 under `exp`.
-/
theorem exp_mem
    {R S : Type*} [Monoid R] [SMul ℚ R] [MulAction R 𝔸] [Algebra ℚ 𝔸] [IsScalarTower ℚ R 𝔸]
    [SetLike S 𝔸] [SubsemiringClass S 𝔸] [SMulMemClass S R 𝔸] {s : S}
    (h_closed : IsClosed (s : Set 𝔸)) {x : 𝔸} (h : x ∈ s) :
    exp x ∈ s := by
  have := SMulMemClass.ofIsScalarTower S ℚ R 𝔸
  rw [exp_eq_tsum ℚ]
  exact tsum_mem h_closed fun i => SMulMemClass.smul_mem _ <| pow_mem h _

variable (𝕂)

@[aesop safe apply]
/-
**NormedSpace._root_.IsSelfAdjoint.exp** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsSelfAdjoint.exp [T2Space 𝔸] [StarRing 𝔸] [ContinuousStar 𝔸] {x : 𝔸}
    (h : IsSelfAdjoint x) : IsSelfAdjoint (exp x) :=
  (star_exp x).trans <| h.symm ▸ rfl
/-
**NormedSpace._root_.Commute.exp_right** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Commute.exp_right [T2Space 𝔸] {x y : 𝔸} (h : Commute x y) :
    Commute x (exp y) := by
  obtain _ | ⟨⟨_⟩⟩ := isEmpty_or_nonempty (Algebra ℚ 𝔸)
  · simp
  · rw [exp_eq_tsum ℚ]
    exact Commute.tsum_right x fun n => (h.pow_right n).smul_right _
/-
**NormedSpace._root_.Commute.exp_left** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Commute.exp_left [T2Space 𝔸] {x y : 𝔸} (h : Commute x y) :
    Commute (exp x) y :=
  h.symm.exp_right.symm
/-
**NormedSpace._root_.Commute.exp** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Commute.exp [T2Space 𝔸] {x y : 𝔸} (h : Commute x y) :
    Commute (exp x) (exp y) :=
  h.exp_left.exp_right

end TopologicalAlgebra

section TopologicalDivisionAlgebra

variable {𝕂 𝔸 : Type*} [Field 𝕂] [DivisionRing 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸]
  [IsTopologicalRing 𝔸]

/-
**NormedSpace.expSeries_apply_eq_div** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：expSeries_apply_eq_div (x : 𝔸) (n : Nat) : (expSeries 𝕂 𝔸 n fun _ => x) = 
x ^ n / n !
参数：x : 𝔸；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `Commute.inv_left₀`：inv_left₀ (h : Commute a b) : Commute a⁻¹ b
· 使用定理 `Nat.cast_commute`：cast_commute (n : Nat) (x : α) : Commute (n : α) x
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `NormedSpace.expSeries_apply_eq`：expSeries_apply_eq (x : 𝔸) (n : Nat) : (
expSeries 𝕂 𝔸 n fun _ => x) = (n !⁻¹ : 𝕂) • x ^ n
· 使用定理 `inv_natCast_smul_eq`：inv_natCast_smul_eq {E : Type*} (R S : Type*) [AddC
ommMonoid E] [DivisionSemiring R] [DivisionSemiring S] [Module R E] [Module S E]
 (n : Nat…
-/
theorem expSeries_apply_eq_div (x : 𝔸) (n : ℕ) : (expSeries 𝕂 𝔸 n fun _ => x) = x ^ n / n ! := by
  rw [div_eq_mul_inv, ← (Nat.cast_commute n ! (x ^ n)).inv_left₀.eq, ← smul_eq_mul,
    expSeries_apply_eq, inv_natCast_smul_eq 𝕂 𝔸]
/-
**NormedSpace.expSeries_apply_eq_div'** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：expSeries_apply_eq_div' (x : 𝔸) : (fun n => expSeries 𝕂 𝔸 n fun _ => x) = 
fun n => x ^ n / n !
参数：x : 𝔸。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NormedSpace.expSeries_apply_eq_div`：expSeries_apply_eq_div (x : 𝔸) (n : 
Nat) : (expSeries 𝕂 𝔸 n fun _ => x) = x ^ n / n !
-/
theorem expSeries_apply_eq_div' (x : 𝔸) :
    (fun n => expSeries 𝕂 𝔸 n fun _ => x) = fun n => x ^ n / n ! :=
  funext (expSeries_apply_eq_div x)
/-
**NormedSpace.expSeries_sum_eq_div** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：expSeries_sum_eq_div (x : 𝔸) : (expSeries 𝕂 𝔸).sum x = ∑' n : Nat, x ^ n /
 n !
参数：x : 𝔸。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsum_congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {L : SummationFilter β}   {f g : β → α}, (∀ (b : β), 
…
· 使用定理 `NormedSpace.expSeries_apply_eq_div`：expSeries_apply_eq_div (x : 𝔸) (n : 
Nat) : (expSeries 𝕂 𝔸 n fun _ => x) = x ^ n / n !
-/
theorem expSeries_sum_eq_div (x : 𝔸) : (expSeries 𝕂 𝔸).sum x = ∑' n : ℕ, x ^ n / n ! :=
  tsum_congr (expSeries_apply_eq_div x)
/-
**NormedSpace.exp_eq_tsum_div** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：exp_eq_tsum_div [CharZero 𝔸] : exp = fun x : 𝔸 => ∑' n : Nat, x ^ n / n !
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
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedSpace.exp_eq_expSeries_sum`：exp_eq_expSeries_sum [CharZero 𝕂] : ex
p = (expSeries 𝕂 𝔸).sum
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NormedSpace.expSeries_sum_eq_div`：expSeries_sum_eq_div (x : 𝔸) : (expSer
ies 𝕂 𝔸).sum x = ∑' n : Nat, x ^ n / n !
-/
theorem exp_eq_tsum_div [CharZero 𝔸] : exp = fun x : 𝔸 => ∑' n : ℕ, x ^ n / n ! := by
  rw [exp_eq_expSeries_sum ℚ]
  ext x
  exact expSeries_sum_eq_div x

end TopologicalDivisionAlgebra

section Normed

section AnyFieldAnyAlgebra

variable {𝕂 𝔸 𝔹 : Type*} [NontriviallyNormedField 𝕂]
variable [NormedRing 𝔸] [NormedRing 𝔹] [NormedAlgebra 𝕂 𝔸]

/-
**NormedSpace.norm_expSeries_summable_of_mem_ball** 是 Mathlib 中的一个定理，位于命名空间 `Nor
medSpace`。
形式化陈述：norm_expSeries_summable_of_mem_ball (x : 𝔸) (hx : x in Metric.eball (0 : 𝔸
) (expSeries 𝕂 𝔸).radius) : Summable fun n => ‖expSeries 𝕂 𝔸 n fun _ => x‖
参数：x : 𝔸；hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `FormalMultilinearSeries.summable_norm_apply`：summable_norm_apply (p : Fo
rmalMultilinearSeries 𝕜 E F) {x : E} (hx : x in Metric.eball (0 : E) p.radius) :
 Summable fun n : Nat => ‖p n fun…
-/
theorem norm_expSeries_summable_of_mem_ball (x : 𝔸)
    (hx : x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    Summable fun n => ‖expSeries 𝕂 𝔸 n fun _ => x‖ :=
  (expSeries 𝕂 𝔸).summable_norm_apply hx
/-
**NormedSpace.norm_expSeries_summable_of_mem_ball'** 是 Mathlib 中的一个定理，位于命名空间 `No
rmedSpace`。
形式化陈述：norm_expSeries_summable_of_mem_ball' (x : 𝔸) (hx : x in Metric.eball (0 : 
𝔸) (expSeries 𝕂 𝔸).radius) : Summable fun n => ‖(n !⁻¹ : 𝕂) • x ^ n‖
参数：x : 𝔸；hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NormedSpace.expSeries_apply_eq'`：expSeries_apply_eq' (x : 𝔸) : (fun n =>
 expSeries 𝕂 𝔸 n fun _ => x) = fun n => (n !⁻¹ : 𝕂) • x ^ n
· 使用定理 `NormedSpace.norm_expSeries_summable_of_mem_ball`：norm_expSeries_summable
_of_mem_ball (x : 𝔸) (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : S
ummable fun n => ‖expSeries 𝕂 𝔸 n fun…
-/
theorem norm_expSeries_summable_of_mem_ball' (x : 𝔸)
    (hx : x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    Summable fun n => ‖(n !⁻¹ : 𝕂) • x ^ n‖ := by
  change Summable (norm ∘ _)
  rw [← expSeries_apply_eq']
  exact norm_expSeries_summable_of_mem_ball x hx

section CompleteAlgebra

variable [CompleteSpace 𝔸]

/-
**NormedSpace.expSeries_summable_of_mem_ball** 是 Mathlib 中的一个定理，位于命名空间 `NormedSp
ace`。
形式化陈述：expSeries_summable_of_mem_ball (x : 𝔸) (hx : x in Metric.eball (0 : 𝔸) (ex
pSeries 𝕂 𝔸).radius) : Summable fun n => expSeries 𝕂 𝔸 n fun _ => x
参数：x : 𝔸；hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Summable.of_norm`：Summable.of_norm {f : ι -> E} (hf : Summable fun a => 
‖f a‖) : Summable f
· 使用定理 `NormedSpace.norm_expSeries_summable_of_mem_ball`：norm_expSeries_summable
_of_mem_ball (x : 𝔸) (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : S
ummable fun n => ‖expSeries 𝕂 𝔸 n fun…
-/
theorem expSeries_summable_of_mem_ball (x : 𝔸)
    (hx : x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    Summable fun n => expSeries 𝕂 𝔸 n fun _ => x :=
  (norm_expSeries_summable_of_mem_ball x hx).of_norm
/-
**NormedSpace.expSeries_summable_of_mem_ball'** 是 Mathlib 中的一个定理，位于命名空间 `NormedS
pace`。
形式化陈述：expSeries_summable_of_mem_ball' (x : 𝔸) (hx : x in Metric.eball (0 : 𝔸) (e
xpSeries 𝕂 𝔸).radius) : Summable fun n => (n !⁻¹ : 𝕂) • x ^ n
参数：x : 𝔸；hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Summable.of_norm`：Summable.of_norm {f : ι -> E} (hf : Summable fun a => 
‖f a‖) : Summable f
· 使用定理 `NormedSpace.norm_expSeries_summable_of_mem_ball'`：norm_expSeries_summabl
e_of_mem_ball' (x : 𝔸) (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
 Summable fun n => ‖(n !⁻¹ : 𝕂) • x ^ …
-/
theorem expSeries_summable_of_mem_ball' (x : 𝔸)
    (hx : x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    Summable fun n => (n !⁻¹ : 𝕂) • x ^ n :=
  (norm_expSeries_summable_of_mem_ball' x hx).of_norm
/-
**NormedSpace.expSeries_hasSum_exp_of_mem_ball** 是 Mathlib 中的一个定理，位于命名空间 `Normed
Space`。
形式化陈述：expSeries_hasSum_exp_of_mem_ball [CharZero 𝕂] (x : 𝔸) (hx : x in Metric.eb
all (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : HasSum (fun n => expSeries 𝕂 𝔸 n fun _ => 
x) (exp x)
参数：x : 𝔸；hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `NormedSpace.exp_eq_expSeries_sum`：exp_eq_expSeries_sum [CharZero 𝕂] : ex
p = (expSeries 𝕂 𝔸).sum
· 使用定理 `FormalMultilinearSeries.hasSum`：∀ {𝕜 : Type u_1} {E : Type u_3} {F : Typ
e u_4} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [ins
t_2 : NormedSpace 𝕜 …
-/
theorem expSeries_hasSum_exp_of_mem_ball [CharZero 𝕂] (x : 𝔸)
    (hx : x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasSum (fun n => expSeries 𝕂 𝔸 n fun _ => x) (exp x) := by
  simpa only [exp_eq_expSeries_sum 𝕂, expSeries_sum_eq_rat] using
    FormalMultilinearSeries.hasSum (expSeries 𝕂 𝔸) hx
/-
**NormedSpace.expSeries_hasSum_exp_of_mem_ball'** 是 Mathlib 中的一个定理，位于命名空间 `Norme
dSpace`。
形式化陈述：expSeries_hasSum_exp_of_mem_ball' [CharZero 𝕂] (x : 𝔸) (hx : x in Metric.e
ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : HasSum (fun n => (n !⁻¹ : 𝕂) • x ^ n) (ex
p x)
参数：x : 𝔸；hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NormedSpace.expSeries_apply_eq'`：expSeries_apply_eq' (x : 𝔸) : (fun n =>
 expSeries 𝕂 𝔸 n fun _ => x) = fun n => (n !⁻¹ : 𝕂) • x ^ n
· 使用定理 `NormedSpace.expSeries_hasSum_exp_of_mem_ball`：expSeries_hasSum_exp_of_me
m_ball [CharZero 𝕂] (x : 𝔸) (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radi
us) : HasSum (fun n => expSeries 𝕂…
-/
theorem expSeries_hasSum_exp_of_mem_ball' [CharZero 𝕂] (x : 𝔸)
    (hx : x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasSum (fun n => (n !⁻¹ : 𝕂) • x ^ n) (exp x) := by
  rw [← expSeries_apply_eq']
  exact expSeries_hasSum_exp_of_mem_ball x hx
/-
**NormedSpace.hasFPowerSeriesOnBall_exp_of_radius_pos** 是 Mathlib 中的一个定理，位于命名空间 
`NormedSpace`。
形式化陈述：hasFPowerSeriesOnBall_exp_of_radius_pos [CharZero 𝕂] (h : 0 < (expSeries 𝕂
 𝔸).radius) : HasFPowerSeriesOnBall exp (expSeries 𝕂 𝔸) 0 (expSeries 𝕂 𝔸).radius
参数：h : 0 < (expSeries 𝕂 𝔸).radius。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `NormedSpace.exp_eq_expSeries_sum`：exp_eq_expSeries_sum [CharZero 𝕂] : ex
p = (expSeries 𝕂 𝔸).sum
· 使用定理 `FormalMultilinearSeries.hasFPowerSeriesOnBall`：∀ {𝕜 : Type u_1} {E : Typ
e u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddComm
Group E]   [inst_2 : NormedSpace 𝕜 …
-/
theorem hasFPowerSeriesOnBall_exp_of_radius_pos [CharZero 𝕂] (h : 0 < (expSeries 𝕂 𝔸).radius) :
    HasFPowerSeriesOnBall exp (expSeries 𝕂 𝔸) 0 (expSeries 𝕂 𝔸).radius := by
  simpa only [exp_eq_expSeries_sum 𝕂, expSeries_sum_eq_rat] using
    (expSeries 𝕂 𝔸).hasFPowerSeriesOnBall h
/-
**NormedSpace.hasFPowerSeriesAt_exp_zero_of_radius_pos** 是 Mathlib 中的一个定理，位于命名空间
 `NormedSpace`。
形式化陈述：hasFPowerSeriesAt_exp_zero_of_radius_pos [CharZero 𝕂] (h : 0 < (expSeries 
𝕂 𝔸).radius) : HasFPowerSeriesAt exp (expSeries 𝕂 𝔸) 0
参数：h : 0 < (expSeries 𝕂 𝔸).radius。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `HasFPowerSeriesOnBall.hasFPowerSeriesAt`：HasFPowerSeriesOnBall.hasFPower
SeriesAt (hf : HasFPowerSeriesOnBall f p x r) : HasFPowerSeriesAt f p x
· 使用定理 `NormedSpace.hasFPowerSeriesOnBall_exp_of_radius_pos`：hasFPowerSeriesOnBa
ll_exp_of_radius_pos [CharZero 𝕂] (h : 0 < (expSeries 𝕂 𝔸).radius) : HasFPowerSe
riesOnBall exp (expSeries 𝕂 𝔸) 0 (expSeri…
-/
theorem hasFPowerSeriesAt_exp_zero_of_radius_pos [CharZero 𝕂] (h : 0 < (expSeries 𝕂 𝔸).radius) :
    HasFPowerSeriesAt exp (expSeries 𝕂 𝔸) 0 := by
  simpa only [exp, expSeries_sum_eq_rat] using
    (hasFPowerSeriesOnBall_exp_of_radius_pos h).hasFPowerSeriesAt
/-
**NormedSpace.continuousOn_exp** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：continuousOn_exp [CharZero 𝕂] : ContinuousOn (exp : 𝔸 -> 𝔸) (Metric.eball 
0 (expSeries 𝕂 𝔸).radius)
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `FormalMultilinearSeries.continuousOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F
 : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E] 
  [inst_2 : NormedSpace 𝕜 …
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedSpace.exp_eq_expSeries_sum`：exp_eq_expSeries_sum [CharZero 𝕂] : ex
p = (expSeries 𝕂 𝔸).sum
-/
theorem continuousOn_exp [CharZero 𝕂] :
    ContinuousOn (exp : 𝔸 → 𝔸) (Metric.eball 0 (expSeries 𝕂 𝔸).radius) := by
  have := FormalMultilinearSeries.continuousOn (p := expSeries 𝕂 𝔸)
  simpa only [exp_eq_expSeries_sum 𝕂, expSeries_sum_eq_rat] using this
/-
**NormedSpace.analyticAt_exp_of_mem_ball** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`
。
形式化陈述：analyticAt_exp_of_mem_ball [CharZero 𝕂] (x : 𝔸) (hx : x in Metric.eball (0
 : 𝔸) (expSeries 𝕂 𝔸).radius) : AnalyticAt 𝕂 exp x
参数：x : 𝔸；hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `ENNReal.not_lt_zero`：not_lt_zero : ¬a < 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `HasFPowerSeriesOnBall.analyticAt_of_mem`：HasFPowerSeriesOnBall.analyticA
t_of_mem (hf : HasFPowerSeriesOnBall f p x r) (h : y in Metric.eball x r) : Anal
yticAt 𝕜 f y
· 使用定理 `NormedSpace.hasFPowerSeriesOnBall_exp_of_radius_pos`：hasFPowerSeriesOnBa
ll_exp_of_radius_pos [CharZero 𝕂] (h : 0 < (expSeries 𝕂 𝔸).radius) : HasFPowerSe
riesOnBall exp (expSeries 𝕂 𝔸) 0 (expSeri…
-/
theorem analyticAt_exp_of_mem_ball [CharZero 𝕂] (x : 𝔸)
    (hx : x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : AnalyticAt 𝕂 exp x := by
  by_cases h : (expSeries 𝕂 𝔸).radius = 0
  · rw [h] at hx; exact (ENNReal.not_lt_zero hx).elim
  · have h := pos_iff_ne_zero.mpr h
    exact (hasFPowerSeriesOnBall_exp_of_radius_pos h).analyticAt_of_mem hx

/-- In a Banach-algebra `𝔸` over a normed field `𝕂` of characteristic zero, if `x` and `y` are
in the disk of convergence and commute, then
`NormedSpace.exp (x + y) = (NormedSpace.exp x) * (NormedSpace.exp y)`. -/
/-
**NormedSpace.exp_add_of_commute_of_mem_ball** 是 Mathlib 中的一个定理，位于命名空间 `NormedSp
ace`。
形式化陈述：exp_add_of_commute_of_mem_ball [CharZero 𝕂] {x y : 𝔸} (hxy : Commute x y) 
(hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) (hy : y in Metric.eball 
(0 : 𝔸) (expSeries 𝕂 𝔸).radius) : exp (x + y) = exp x * exp y
参数：hxy : Commute x y；hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius；hy : 
y in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedSpace.exp_eq_tsum`：exp_eq_tsum [CharZero 𝕂] : exp = fun x : 𝔸 => ∑
' n : Nat, (n !⁻¹ : 𝕂) • x ^ n
· 使用定理 `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`：tsum_mul_tsum_e
q_tsum_sum_antidiagonal_of_summable_norm [CompleteSpace R] {f g : Nat -> R} (hf 
: Summable fun x => ‖f x‖) (hg : Summable fun…
· 使用定理 `NormedSpace.norm_expSeries_summable_of_mem_ball'`：norm_expSeries_summabl
e_of_mem_ball' (x : 𝔸) (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
 Summable fun n => ‖(n !⁻¹ : 𝕂) • x ^ …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Commute.add_pow'`：add_pow' (h : Commute x y) (n : Nat) : (x + y) ^ n = ∑
 m in antidiagonal n, n.choose m.1 • (x ^ m.1 * y ^ m.2)
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `tsum_congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {L : SummationFilter β}   {f g : β → α}, (∀ (b : β), 
…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用引理 `smul_mul_smul_comm`：smul_mul_smul_comm [Mul α] [Mul β] [SMul α β] [IsSca
larTower α β β] [IsScalarTower α α β] [SMulCommClass α β β] (a : α) (b : β) (c :
 α) (d :…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.HasAntidiagonal.mem_antidiagonal`：∀ {A : Type u_1} {inst : AddMon
oid A} [self : Finset.HasAntidiagonal A] {n : A} {a : A × A},   a ∈ Finset.HasAn
tidiagonal.antidiagonal n ↔ a…
· 使用定理 `Nat.cast_add_choose`：cast_add_choose {a b : Nat} : ((a + b).choose a : K
) = (a + b)! / (a ! * b !)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.inv_eq_eval`：inv_eq_eval [CommGroupWithZero 
M] {l : NF M} {x : M} (h : x = l.eval) : x⁻¹ = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
In a Banach-algebra `𝔸` over a normed field `𝕂` of characteristic zero, if `x` a
nd `y` are
in the disk of convergence and commute, then
`NormedSpace.exp (x + y) = (NormedSpace.exp x) * (NormedSpace.exp y)`.
-/
theorem exp_add_of_commute_of_mem_ball [CharZero 𝕂] {x y : 𝔸} (hxy : Commute x y)
    (hx : x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius)
    (hy : y ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : exp (x + y) = exp x * exp y := by
  rw [exp_eq_tsum 𝕂,
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
      (norm_expSeries_summable_of_mem_ball' x hx) (norm_expSeries_summable_of_mem_ball' y hy)]
  dsimp only
  conv_lhs =>
    congr
    ext
    rw [hxy.add_pow' _, Finset.smul_sum]
  refine tsum_congr fun n => Finset.sum_congr rfl fun kl hkl => ?_
  rw [← Nat.cast_smul_eq_nsmul 𝕂, smul_smul, smul_mul_smul_comm, ← Finset.mem_antidiagonal.mp hkl,
    Nat.cast_add_choose, Finset.mem_antidiagonal.mp hkl]
  field_simp [n.factorial_ne_zero]

/-- `NormedSpace.exp x` has explicit two-sided inverse `NormedSpace.exp (-x)`. -/
@[instance_reducible]
/-
**NormedSpace.invertibleExpOfMemBall** 是 Mathlib 中的一个定义，位于命名空间 `NormedSpace`。
形式化陈述：invertibleExpOfMemBall [CharZero 𝕂] {x : 𝔸} (hx : x in Metric.eball (0 : 𝔸
) (expSeries 𝕂 𝔸).radius) : Invertible (exp x) where invOf
参数：hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`NormedSpace.exp x` has explicit two-sided inverse `NormedSpace.exp (-x)`.
-/
noncomputable def invertibleExpOfMemBall [CharZero 𝕂] {x : 𝔸}
    (hx : x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : Invertible (exp x)
    where
  invOf := exp (-x)
  invOf_mul_self := by
    have hnx : -x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius := by
      rw [Metric.mem_eball, ← neg_zero, edist_neg_neg]
      exact hx
    rw [← exp_add_of_commute_of_mem_ball (Commute.neg_left <| Commute.refl x) hnx hx,
      neg_add_cancel, exp_zero]
  mul_invOf_self := by
    have hnx : -x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius := by
      rw [Metric.mem_eball, ← neg_zero, edist_neg_neg]
      exact hx
    rw [← exp_add_of_commute_of_mem_ball (Commute.neg_right <| Commute.refl x) hx hnx,
      add_neg_cancel, exp_zero]
/-
**NormedSpace.isUnit_exp_of_mem_ball** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：isUnit_exp_of_mem_ball [CharZero 𝕂] {x : 𝔸} (hx : x in Metric.eball (0 : 𝔸
) (expSeries 𝕂 𝔸).radius) : IsUnit (exp x)
参数：hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `isUnit_of_invertible`：isUnit_of_invertible [Monoid α] (a : α) [Invertibl
e a] : IsUnit a
-/
theorem isUnit_exp_of_mem_ball [CharZero 𝕂] {x : 𝔸}
    (hx : x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : IsUnit (exp x) :=
  @isUnit_of_invertible _ _ _ (invertibleExpOfMemBall hx)
/-
**NormedSpace.invOf_exp_of_mem_ball** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：invOf_exp_of_mem_ball [CharZero 𝕂] {x : 𝔸} (hx : x in Metric.eball (0 : 𝔸)
 (expSeries 𝕂 𝔸).radius) [Invertible (exp x)] : ⅟(exp x) = exp (-x)
参数：hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius；exp x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Invertible.congr`：Invertible.congr [Invertible a] [Invertible b] (h : a 
= b) : ⅟a = ⅟b
-/
theorem invOf_exp_of_mem_ball [CharZero 𝕂] {x : 𝔸}
    (hx : x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) [Invertible (exp x)] :
    ⅟(exp x) = exp (-x) := by
  let := invertibleExpOfMemBall hx; convert! (rfl : ⅟(exp x) = _)

/-- Any continuous ring homomorphism commutes with `NormedSpace.exp`. -/
/-
**NormedSpace.map_exp_of_mem_ball** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：map_exp_of_mem_ball [Algebra 𝕂 𝔹] [CharZero 𝕂] {F} [FunLike F 𝔸 𝔹] [RingHo
mClass F 𝔸 𝔹] (f : F) (hf : Continuous f) (x : 𝔸) (hx : x in Metric.eball (0 : 𝔸
) (expSeries 𝕂 𝔸).radius) : f (exp x) = exp (f x)
参数：f : F；hf : Continuous f；x : 𝔸；hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).
radius。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedSpace.exp_eq_tsum`：exp_eq_tsum [CharZero 𝕂] : exp = fun x : 𝔸 => ∑
' n : Nat, (n !⁻¹ : 𝕂) • x ^ n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `HasSum.map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : AddCo
mmMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {a : α} {L : SummationFi
…
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用定理 `NormedSpace.expSeries_summable_of_mem_ball'`：expSeries_summable_of_mem_b
all' (x : 𝔸) (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : Summable 
fun n => (n !⁻¹ : 𝕂) • x ^ n
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_inv_natCast_smul`：map_inv_natCast_smul [AddCommMonoid M] [AddCommMon
oid M₂] {F : Type*} [FunLike F M M₂] [AddMonoidHomClass F M M₂] (f : F) (R S : T
ype*) [Div…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Any continuous ring homomorphism commutes with `NormedSpace.exp`.
-/
theorem map_exp_of_mem_ball [Algebra 𝕂 𝔹] [CharZero 𝕂] {F} [FunLike F 𝔸 𝔹] [RingHomClass F 𝔸 𝔹]
    (f : F) (hf : Continuous f) (x : 𝔸) (hx : x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    f (exp x) = exp (f x) := by
  rw [exp_eq_tsum 𝕂, exp_eq_tsum 𝕂]
  refine ((expSeries_summable_of_mem_ball' _ hx).hasSum.map f hf).tsum_eq.symm.trans ?_
  dsimp only [Function.comp_def]
  simp_rw [map_inv_natCast_smul f 𝕂 𝕂, map_pow]

end CompleteAlgebra

/-
**NormedSpace.algebraMap_exp_comm_of_mem_ball** 是 Mathlib 中的一个定理，位于命名空间 `NormedS
pace`。
形式化陈述：algebraMap_exp_comm_of_mem_ball [CharZero 𝕂] [CompleteSpace 𝕂] (x : 𝕂) (hx
 : x in Metric.eball (0 : 𝕂) (expSeries 𝕂 𝕂).radius) : algebraMap 𝕂 𝔸 (exp x) = 
exp (algebraMap 𝕂 𝔸 x)
参数：x : 𝕂；hx : x in Metric.eball (0 : 𝕂) (expSeries 𝕂 𝕂).radius。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `NormedSpace.map_exp_of_mem_ball`：map_exp_of_mem_ball [Algebra 𝕂 𝔹] [Char
Zero 𝕂] {F} [FunLike F 𝔸 𝔹] [RingHomClass F 𝔸 𝔹] (f : F) (hf : Continuous f) (x 
: 𝔸) (hx : x in Metri…
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem algebraMap_exp_comm_of_mem_ball [CharZero 𝕂] [CompleteSpace 𝕂] (x : 𝕂)
    (hx : x ∈ Metric.eball (0 : 𝕂) (expSeries 𝕂 𝕂).radius) :
    algebraMap 𝕂 𝔸 (exp x) = exp (algebraMap 𝕂 𝔸 x) :=
  map_exp_of_mem_ball (algebraMap _ _) (algebraMapCLM _ _).continuous _ hx

end AnyFieldAnyAlgebra

section AnyFieldDivisionAlgebra

variable {𝕂 𝔸 : Type*} [NontriviallyNormedField 𝕂] [NormedDivisionRing 𝔸] [NormedAlgebra 𝕂 𝔸]
variable (𝕂)

/-
**NormedSpace.norm_expSeries_div_summable_of_mem_ball** 是 Mathlib 中的一个定理，位于命名空间 
`NormedSpace`。
形式化陈述：norm_expSeries_div_summable_of_mem_ball (x : 𝔸) (hx : x in Metric.eball (0
 : 𝔸) (expSeries 𝕂 𝔸).radius) : Summable fun n => ‖x ^ n / (n !)‖
参数：x : 𝔸；hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NormedSpace.expSeries_apply_eq_div'`：expSeries_apply_eq_div' (x : 𝔸) : (
fun n => expSeries 𝕂 𝔸 n fun _ => x) = fun n => x ^ n / n !
· 使用定理 `NormedSpace.norm_expSeries_summable_of_mem_ball`：norm_expSeries_summable
_of_mem_ball (x : 𝔸) (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : S
ummable fun n => ‖expSeries 𝕂 𝔸 n fun…
-/
theorem norm_expSeries_div_summable_of_mem_ball (x : 𝔸)
    (hx : x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    Summable fun n => ‖x ^ n / (n !)‖ := by
  change Summable (norm ∘ _)
  rw [← expSeries_apply_eq_div' (𝕂 := 𝕂) x]
  exact norm_expSeries_summable_of_mem_ball x hx
/-
**NormedSpace.expSeries_div_summable_of_mem_ball** 是 Mathlib 中的一个定理，位于命名空间 `Norm
edSpace`。
形式化陈述：expSeries_div_summable_of_mem_ball [CompleteSpace 𝔸] (x : 𝔸) (hx : x in Me
tric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : Summable fun n => x ^ n / n !
参数：x : 𝔸；hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Summable.of_norm`：Summable.of_norm {f : ι -> E} (hf : Summable fun a => 
‖f a‖) : Summable f
· 使用定理 `NormedSpace.norm_expSeries_div_summable_of_mem_ball`：norm_expSeries_div_
summable_of_mem_ball (x : 𝔸) (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).rad
ius) : Summable fun n => ‖x ^ n / (n !)‖
-/
theorem expSeries_div_summable_of_mem_ball [CompleteSpace 𝔸] (x : 𝔸)
    (hx : x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : Summable fun n => x ^ n / n ! :=
  (norm_expSeries_div_summable_of_mem_ball 𝕂 x hx).of_norm
/-
**NormedSpace.expSeries_div_hasSum_exp_of_mem_ball** 是 Mathlib 中的一个定理，位于命名空间 `No
rmedSpace`。
形式化陈述：expSeries_div_hasSum_exp_of_mem_ball [CharZero 𝕂] [CompleteSpace 𝔸] (x : 𝔸
) (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : HasSum (fun n => x ^
 n / n !) (exp x)
参数：x : 𝔸；hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NormedSpace.expSeries_apply_eq_div'`：expSeries_apply_eq_div' (x : 𝔸) : (
fun n => expSeries 𝕂 𝔸 n fun _ => x) = fun n => x ^ n / n !
· 使用定理 `NormedSpace.expSeries_hasSum_exp_of_mem_ball`：expSeries_hasSum_exp_of_me
m_ball [CharZero 𝕂] (x : 𝔸) (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radi
us) : HasSum (fun n => expSeries 𝕂…
-/
theorem expSeries_div_hasSum_exp_of_mem_ball [CharZero 𝕂] [CompleteSpace 𝔸] (x : 𝔸)
    (hx : x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasSum (fun n => x ^ n / n !) (exp x) := by
  rw [← expSeries_apply_eq_div' (𝕂 := 𝕂) x]
  exact expSeries_hasSum_exp_of_mem_ball x hx
/-
**NormedSpace.exp_neg_of_mem_ball** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：exp_neg_of_mem_ball [CharZero 𝕂] [CompleteSpace 𝔸] {x : 𝔸} (hx : x in Metr
ic.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : exp (-x) = (exp x)⁻¹
参数：hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
-/
theorem exp_neg_of_mem_ball [CharZero 𝕂] [CompleteSpace 𝔸] {x : 𝔸}
    (hx : x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : exp (-x) = (exp x)⁻¹ :=
  letI := invertibleExpOfMemBall hx
  invOf_eq_inv (exp x)

end AnyFieldDivisionAlgebra

section AnyFieldCommAlgebra

variable {𝕂 𝔸 : Type*} [NontriviallyNormedField 𝕂] [NormedCommRing 𝔸] [NormedAlgebra 𝕂 𝔸]
  [CompleteSpace 𝔸]

/-- In a commutative Banach-algebra `𝔸` over a normed field `𝕂` of characteristic zero,
`NormedSpace.exp (x+y) = (NormedSpace.exp x) * (NormedSpace.exp y)`
for all `x`, `y` in the disk of convergence. -/
/-
**NormedSpace.exp_add_of_mem_ball** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：exp_add_of_mem_ball [CharZero 𝕂] {x y : 𝔸} (hx : x in Metric.eball (0 : 𝔸)
 (expSeries 𝕂 𝔸).radius) (hy : y in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius)
 : exp (x + y) = exp x * exp y
参数：hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius；hy : y in Metric.eball 
(0 : 𝔸) (expSeries 𝕂 𝔸).radius。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `NormedSpace.exp_add_of_commute_of_mem_ball`：exp_add_of_commute_of_mem_ba
ll [CharZero 𝕂] {x y : 𝔸} (hxy : Commute x y) (hx : x in Metric.eball (0 : 𝔸) (e
xpSeries 𝕂 𝔸).radius) (hy : y in…
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b

--- 原说明 ---
In a commutative Banach-algebra `𝔸` over a normed field `𝕂` of characteristic ze
ro,
`NormedSpace.exp (x+y) = (NormedSpace.exp x) * (NormedSpace.exp y)`
for all `x`, `y` in the disk of convergence.
-/
theorem exp_add_of_mem_ball [CharZero 𝕂] {x y : 𝔸}
    (hx : x ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius)
    (hy : y ∈ Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : exp (x + y) = exp x * exp y :=
  exp_add_of_commute_of_mem_ball (Commute.all x y) hx hy

end AnyFieldCommAlgebra

section AnyAlgebra

variable (𝕂 𝔸 : Type*) [NontriviallyNormedField 𝕂] [CharZero 𝕂] [ContinuousSMul ℚ 𝕂]
variable [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]

/-- In a normed algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`, the series defining the exponential map
has an infinite radius of convergence. -/
/-
**NormedSpace.expSeries_radius_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：expSeries_radius_eq_top : (expSeries 𝕂 𝔸).radius = ∞
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto`：ofScalars_ra
dius_eq_top_of_tendsto (hc : forallᶠ n in atTop, c n != 0) (hc' : Tendsto (fun n
 => ‖c n.succ‖ / ‖c n‖) atTop (𝓝 0)) : (ofScalar…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NormedSpace.expSeries_eq_ofScalars`：expSeries_eq_ofScalars : expSeries 𝕂
 𝔸 = ofScalars 𝔸 fun n => (n !⁻¹ : 𝕂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `mul_div_right_comm`：mul_div_right_comm : a * b / c = a / c * b
· 使用定理 `inv_div_inv`：inv_div_inv : a⁻¹ / b⁻¹ = b / a
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
In a normed algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`, the series defining the exponen
tial map
has an infinite radius of convergence.
-/
theorem expSeries_radius_eq_top : (expSeries 𝕂 𝔸).radius = ∞ := by
  have {n : ℕ} : (Nat.factorial n : 𝕂) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  apply expSeries_eq_ofScalars 𝕂 𝔸 ▸
    ofScalars_radius_eq_top_of_tendsto 𝔸 _ (Eventually.of_forall fun n => ?_)
  · simp_rw [← norm_div, Nat.factorial_succ, Nat.cast_mul, mul_inv_rev, mul_div_right_comm,
      inv_div_inv, norm_mul, div_self this, norm_one, one_mul]
    apply norm_zero (E := 𝕂) ▸ Filter.Tendsto.norm
    apply (Filter.tendsto_add_atTop_iff_nat (f := fun n => (n : 𝕂)⁻¹) 1).mpr
    exact tendsto_inv_atTop_nhds_zero_nat
  · simp [this]
/-
**NormedSpace.expSeries_radius_pos** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：expSeries_radius_pos : 0 < (expSeries 𝕂 𝔸).radius
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedSpace.expSeries_radius_eq_top`：expSeries_radius_eq_top : (expSerie
s 𝕂 𝔸).radius = ∞
· 使用定理 `WithTop.top_pos`：∀ {α : Type u} [inst : Zero α] [inst_1 : LT α], 0 < ⊤
-/
theorem expSeries_radius_pos : 0 < (expSeries 𝕂 𝔸).radius := by
  rw [expSeries_radius_eq_top]
  exact WithTop.top_pos

variable {𝕂 𝔸}
/-
**NormedSpace.norm_expSeries_summable** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：norm_expSeries_summable (x : 𝔸) : Summable fun n => ‖expSeries 𝕂 𝔸 n fun _
 => x‖
参数：x : 𝔸。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedSpace.norm_expSeries_summable_of_mem_ball`：norm_expSeries_summable
_of_mem_ball (x : 𝔸) (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : S
ummable fun n => ‖expSeries 𝕂 𝔸 n fun…
· 使用定理 `edist_lt_top`：edist_lt_top {α : Type*} [PseudoMetricSpace α] (x y : α) :
 edist x y < ⊤
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NormedSpace.expSeries_radius_eq_top`：expSeries_radius_eq_top : (expSerie
s 𝕂 𝔸).radius = ∞
-/
theorem norm_expSeries_summable (x : 𝔸) : Summable fun n => ‖expSeries 𝕂 𝔸 n fun _ => x‖ :=
  norm_expSeries_summable_of_mem_ball x ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
/-
**NormedSpace.norm_expSeries_summable'** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：norm_expSeries_summable' (x : 𝔸) : Summable fun n => ‖(n !⁻¹ : 𝕂) • x ^ n‖
参数：x : 𝔸。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedSpace.norm_expSeries_summable_of_mem_ball'`：norm_expSeries_summabl
e_of_mem_ball' (x : 𝔸) (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
 Summable fun n => ‖(n !⁻¹ : 𝕂) • x ^ …
· 使用定理 `edist_lt_top`：edist_lt_top {α : Type*} [PseudoMetricSpace α] (x y : α) :
 edist x y < ⊤
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NormedSpace.expSeries_radius_eq_top`：expSeries_radius_eq_top : (expSerie
s 𝕂 𝔸).radius = ∞
-/
theorem norm_expSeries_summable' (x : 𝔸) : Summable fun n => ‖(n !⁻¹ : 𝕂) • x ^ n‖ :=
  norm_expSeries_summable_of_mem_ball' x ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
/-
**NormedSpace.algebraMap_exp_comm** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：algebraMap_exp_comm [CompleteSpace 𝕂] (x : 𝕂) : algebraMap 𝕂 𝔸 (exp x) = e
xp (algebraMap 𝕂 𝔸 x)
参数：x : 𝕂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedSpace.algebraMap_exp_comm_of_mem_ball`：algebraMap_exp_comm_of_mem_
ball [CharZero 𝕂] [CompleteSpace 𝕂] (x : 𝕂) (hx : x in Metric.eball (0 : 𝕂) (exp
Series 𝕂 𝕂).radius) : algebraMap …
· 使用定理 `edist_lt_top`：edist_lt_top {α : Type*} [PseudoMetricSpace α] (x y : α) :
 edist x y < ⊤
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NormedSpace.expSeries_radius_eq_top`：expSeries_radius_eq_top : (expSerie
s 𝕂 𝔸).radius = ∞
-/
theorem algebraMap_exp_comm [CompleteSpace 𝕂] (x : 𝕂) :
    algebraMap 𝕂 𝔸 (exp x) = exp (algebraMap 𝕂 𝔸 x) :=
  algebraMap_exp_comm_of_mem_ball x <| (expSeries_radius_eq_top 𝕂 𝕂).symm ▸ edist_lt_top _ _

variable [CompleteSpace 𝔸]
/-
**NormedSpace.expSeries_summable** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：expSeries_summable (x : 𝔸) : Summable fun n => expSeries 𝕂 𝔸 n fun _ => x
参数：x : 𝔸。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.of_norm`：Summable.of_norm {f : ι -> E} (hf : Summable fun a => 
‖f a‖) : Summable f
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `NormedSpace.norm_expSeries_summable`：norm_expSeries_summable (x : 𝔸) : S
ummable fun n => ‖expSeries 𝕂 𝔸 n fun _ => x‖
-/
theorem expSeries_summable (x : 𝔸) : Summable fun n => expSeries 𝕂 𝔸 n fun _ => x :=
  (norm_expSeries_summable x).of_norm
/-
**NormedSpace.expSeries_summable'** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：expSeries_summable' (x : 𝔸) : Summable fun n => (n !⁻¹ : 𝕂) • x ^ n
参数：x : 𝔸。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.of_norm`：Summable.of_norm {f : ι -> E} (hf : Summable fun a => 
‖f a‖) : Summable f
· 使用定理 `NormedSpace.norm_expSeries_summable'`：norm_expSeries_summable' (x : 𝔸) :
 Summable fun n => ‖(n !⁻¹ : 𝕂) • x ^ n‖
-/
theorem expSeries_summable' (x : 𝔸) : Summable fun n => (n !⁻¹ : 𝕂) • x ^ n :=
  (norm_expSeries_summable' x).of_norm
/-
**NormedSpace.expSeries_hasSum_exp** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：expSeries_hasSum_exp (x : 𝔸) : HasSum (fun n => expSeries 𝕂 𝔸 n fun _ => x
) (exp x)
参数：x : 𝔸。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedSpace.expSeries_hasSum_exp_of_mem_ball`：expSeries_hasSum_exp_of_me
m_ball [CharZero 𝕂] (x : 𝔸) (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radi
us) : HasSum (fun n => expSeries 𝕂…
· 使用定理 `edist_lt_top`：edist_lt_top {α : Type*} [PseudoMetricSpace α] (x y : α) :
 edist x y < ⊤
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NormedSpace.expSeries_radius_eq_top`：expSeries_radius_eq_top : (expSerie
s 𝕂 𝔸).radius = ∞
-/
theorem expSeries_hasSum_exp (x : 𝔸) : HasSum (fun n => expSeries 𝕂 𝔸 n fun _ => x) (exp x) :=
  expSeries_hasSum_exp_of_mem_ball x ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
/-
**NormedSpace.exp_series_hasSum_exp'** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：exp_series_hasSum_exp' (x : 𝔸) : HasSum (fun n => (n !⁻¹ : 𝕂) • x ^ n) (ex
p x)
参数：x : 𝔸。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedSpace.expSeries_hasSum_exp_of_mem_ball'`：expSeries_hasSum_exp_of_m
em_ball' [CharZero 𝕂] (x : 𝔸) (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).ra
dius) : HasSum (fun n => (n !⁻¹ : 𝕂…
· 使用定理 `edist_lt_top`：edist_lt_top {α : Type*} [PseudoMetricSpace α] (x y : α) :
 edist x y < ⊤
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NormedSpace.expSeries_radius_eq_top`：expSeries_radius_eq_top : (expSerie
s 𝕂 𝔸).radius = ∞
-/
theorem exp_series_hasSum_exp' (x : 𝔸) : HasSum (fun n => (n !⁻¹ : 𝕂) • x ^ n) (exp x) :=
  expSeries_hasSum_exp_of_mem_ball' x ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
/-
**NormedSpace.exp_hasFPowerSeriesOnBall** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：exp_hasFPowerSeriesOnBall : HasFPowerSeriesOnBall exp (expSeries 𝕂 𝔸) 0 ∞
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `NormedSpace.hasFPowerSeriesOnBall_exp_of_radius_pos`：hasFPowerSeriesOnBa
ll_exp_of_radius_pos [CharZero 𝕂] (h : 0 < (expSeries 𝕂 𝔸).radius) : HasFPowerSe
riesOnBall exp (expSeries 𝕂 𝔸) 0 (expSeri…
· 使用定理 `NormedSpace.expSeries_radius_pos`：expSeries_radius_pos : 0 < (expSeries 
𝕂 𝔸).radius
· 使用定理 `NormedSpace.expSeries_radius_eq_top`：expSeries_radius_eq_top : (expSerie
s 𝕂 𝔸).radius = ∞
-/
theorem exp_hasFPowerSeriesOnBall : HasFPowerSeriesOnBall exp (expSeries 𝕂 𝔸) 0 ∞ :=
  expSeries_radius_eq_top 𝕂 𝔸 ▸ hasFPowerSeriesOnBall_exp_of_radius_pos (expSeries_radius_pos _ _)
/-
**NormedSpace.exp_hasFPowerSeriesAt_zero** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`
。
形式化陈述：exp_hasFPowerSeriesAt_zero : HasFPowerSeriesAt exp (expSeries 𝕂 𝔸) 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFPowerSeriesOnBall.hasFPowerSeriesAt`：HasFPowerSeriesOnBall.hasFPower
SeriesAt (hf : HasFPowerSeriesOnBall f p x r) : HasFPowerSeriesAt f p x
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `NormedSpace.exp_hasFPowerSeriesOnBall`：exp_hasFPowerSeriesOnBall : HasFP
owerSeriesOnBall exp (expSeries 𝕂 𝔸) 0 ∞
-/
theorem exp_hasFPowerSeriesAt_zero : HasFPowerSeriesAt exp (expSeries 𝕂 𝔸) 0 :=
  exp_hasFPowerSeriesOnBall.hasFPowerSeriesAt
/-
**NormedSpace.exp_analytic** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：exp_analytic (x : 𝔸) : AnalyticAt 𝕂 exp x
参数：x : 𝔸。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedSpace.analyticAt_exp_of_mem_ball`：analyticAt_exp_of_mem_ball [Char
Zero 𝕂] (x : 𝔸) (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : Analyt
icAt 𝕂 exp x
· 使用定理 `edist_lt_top`：edist_lt_top {α : Type*} [PseudoMetricSpace α] (x y : α) :
 edist x y < ⊤
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NormedSpace.expSeries_radius_eq_top`：expSeries_radius_eq_top : (expSerie
s 𝕂 𝔸).radius = ∞
-/
theorem exp_analytic (x : 𝔸) : AnalyticAt 𝕂 exp x :=
  analyticAt_exp_of_mem_ball x ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

end AnyAlgebra

section Rat
variable {𝔸 𝔹 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] [NormedRing 𝔹]

@[continuity, fun_prop]
/-
**NormedSpace.exp_continuous** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：exp_continuous : Continuous (exp : 𝔸 -> 𝔸)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousOn_univ`：continuousOn_univ {f : α -> β} : ContinuousOn f univ 
↔ Continuous f
· 使用定理 `Metric.eball_top_eq_univ`：Metric.eball_top_eq_univ (x : α) : eball x ∞ =
 Set.univ
· 使用定理 `NormedSpace.expSeries_radius_eq_top`：expSeries_radius_eq_top : (expSerie
s 𝕂 𝔸).radius = ∞
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Rat.instIsTopologicalRing`：IsTopologicalRing ℚ
· 使用定理 `NormedSpace.continuousOn_exp`：continuousOn_exp [CharZero 𝕂] : Continuous
On (exp : 𝔸 -> 𝔸) (Metric.eball 0 (expSeries 𝕂 𝔸).radius)
-/
theorem exp_continuous : Continuous (exp : 𝔸 → 𝔸) := by
  rw [← continuousOn_univ, ← Metric.eball_top_eq_univ (0 : 𝔸), ←
    expSeries_radius_eq_top ℚ 𝔸]
  exact continuousOn_exp

open Topology in
/-
**NormedSpace._root_.Filter.Tendsto.exp** 是 Mathlib 中的一个引理，位于命名空间 `NormedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Filter.Tendsto.exp {α : Type*} {l : Filter α} {f : α → 𝔸} {a : 𝔸}
    (hf : Tendsto f l (𝓝 a)) :
    Tendsto (fun x => exp (f x)) l (𝓝 (exp a)) :=
  (exp_continuous.tendsto _).comp hf

/-- In a Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`, if `x` and `y` commute, then
`NormedSpace.exp (x+y) = (NormedSpace.exp x) * (NormedSpace.exp y)`. -/
/-
**NormedSpace.exp_add_of_commute** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：exp_add_of_commute {x y : 𝔸} (hxy : Commute x y) : exp (x + y) = exp x * e
xp y
参数：hxy : Commute x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedSpace.exp_add_of_commute_of_mem_ball`：exp_add_of_commute_of_mem_ba
ll [CharZero 𝕂] {x y : 𝔸} (hxy : Commute x y) (hx : x in Metric.eball (0 : 𝔸) (e
xpSeries 𝕂 𝔸).radius) (hy : y in…
· 使用定理 `edist_lt_top`：edist_lt_top {α : Type*} [PseudoMetricSpace α] (x y : α) :
 edist x y < ⊤
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NormedSpace.expSeries_radius_eq_top`：expSeries_radius_eq_top : (expSerie
s 𝕂 𝔸).radius = ∞
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Rat.instIsTopologicalRing`：IsTopologicalRing ℚ

--- 原说明 ---
In a Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`, if `x` and `y` commute, then
`NormedSpace.exp (x+y) = (NormedSpace.exp x) * (NormedSpace.exp y)`.
-/
theorem exp_add_of_commute {x y : 𝔸} (hxy : Commute x y) : exp (x + y) = exp x * exp y :=
  exp_add_of_commute_of_mem_ball hxy ((expSeries_radius_eq_top ℚ 𝔸).symm ▸ edist_lt_top _ _)
    ((expSeries_radius_eq_top ℚ 𝔸).symm ▸ edist_lt_top _ _)

/-- `NormedSpace.exp x` has explicit two-sided inverse `NormedSpace.exp (-x)`. -/
@[instance_reducible]
/-
**NormedSpace.invertibleExp** 是 Mathlib 中的一个定义，位于命名空间 `NormedSpace`。
形式化陈述：invertibleExp (x : 𝔸) : Invertible (exp x)
参数：x : 𝔸。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`NormedSpace.exp x` has explicit two-sided inverse `NormedSpace.exp (-x)`.
-/
noncomputable def invertibleExp (x : 𝔸) : Invertible (exp x) :=
  invertibleExpOfMemBall <| (expSeries_radius_eq_top ℚ 𝔸).symm ▸ edist_lt_top _ _
/-
**NormedSpace.isUnit_exp** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：isUnit_exp (x : 𝔸) : IsUnit (exp x)
参数：x : 𝔸。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedSpace.isUnit_exp_of_mem_ball`：isUnit_exp_of_mem_ball [CharZero 𝕂] 
{x : 𝔸} (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : IsUnit (exp x)
· 使用定理 `edist_lt_top`：edist_lt_top {α : Type*} [PseudoMetricSpace α] (x y : α) :
 edist x y < ⊤
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NormedSpace.expSeries_radius_eq_top`：expSeries_radius_eq_top : (expSerie
s 𝕂 𝔸).radius = ∞
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Rat.instIsTopologicalRing`：IsTopologicalRing ℚ
-/
theorem isUnit_exp (x : 𝔸) : IsUnit (exp x) :=
  isUnit_exp_of_mem_ball <| (expSeries_radius_eq_top ℚ 𝔸).symm ▸ edist_lt_top _ _
/-
**NormedSpace.invOf_exp** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：invOf_exp (x : 𝔸) [Invertible (exp x)] : ⅟(exp x) = exp (-x)
参数：x : 𝔸；exp x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `NormedSpace.invOf_exp_of_mem_ball`：invOf_exp_of_mem_ball [CharZero 𝕂] {x
 : 𝔸} (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) [Invertible (exp x
)] : ⅟(exp x) = exp (-x…
· 使用定理 `edist_lt_top`：edist_lt_top {α : Type*} [PseudoMetricSpace α] (x y : α) :
 edist x y < ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NormedSpace.expSeries_radius_eq_top`：expSeries_radius_eq_top : (expSerie
s 𝕂 𝔸).radius = ∞
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Rat.instIsTopologicalRing`：IsTopologicalRing ℚ
-/
theorem invOf_exp (x : 𝔸) [Invertible (exp x)] : ⅟(exp x) = exp (-x) :=
  invOf_exp_of_mem_ball <| (expSeries_radius_eq_top ℚ 𝔸).symm ▸ edist_lt_top _ _
/-
**NormedSpace._root_.Ring.inverse_exp** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Ring.inverse_exp (x : 𝔸) : (exp x)⁻¹ʳ = exp (-x) :=
  letI := invertibleExp x
  Ring.inverse_invertible _
/-
**NormedSpace.exp_mem_unitary_of_mem_skewAdjoint** 是 Mathlib 中的一个定理，位于命名空间 `Norm
edSpace`。
形式化陈述：exp_mem_unitary_of_mem_skewAdjoint [StarRing 𝔸] [ContinuousStar 𝔸] {x : 𝔸}
 (h : x in skewAdjoint 𝔸) : exp x in unitary 𝔸
参数：h : x in skewAdjoint 𝔸。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unitary.mem_iff`：mem_iff {U : R} : U in unitary R ↔ star U * U = 1 ∧ U *
 star U = 1
· 使用定理 `NormedSpace.star_exp`：star_exp [T2Space 𝔸] [StarRing 𝔸] [ContinuousStar 
𝔸] (x : 𝔸) : star (exp x) = exp (star x)
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `skewAdjoint.mem_iff`：mem_iff {x : R} : x in skewAdjoint R ↔ star x = -x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NormedSpace.exp_add_of_commute`：exp_add_of_commute {x y : 𝔸} (hxy : Comm
ute x y) : exp (x + y) = exp x * exp y
· 使用定理 `Commute.neg_left`：neg_left : Commute a b -> Commute (-a) b
· 使用定理 `Commute.refl`：∀ {S : Type u_3} [inst : Mul S] (a : S), Commute a a
· 使用定理 `Commute.neg_right`：neg_right : Commute a b -> Commute a (-b)
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `NormedSpace.exp_zero`：exp_zero : exp (0 : 𝔸) = 1
· 使用定理 `and_self_iff`：∀ {a : Prop}, a ∧ a ↔ a
-/
theorem exp_mem_unitary_of_mem_skewAdjoint [StarRing 𝔸] [ContinuousStar 𝔸] {x : 𝔸}
    (h : x ∈ skewAdjoint 𝔸) : exp x ∈ unitary 𝔸 := by
  rw [Unitary.mem_iff, star_exp, skewAdjoint.mem_iff.mp h, ←
    exp_add_of_commute (Commute.refl x).neg_left, ← exp_add_of_commute (Commute.refl x).neg_right,
    neg_add_cancel, add_neg_cancel, exp_zero, and_self_iff]
/-
**NormedSpace._root_.SemiconjBy.exp_right** 是 Mathlib 中的一个引理，位于命名空间 `NormedSpace
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.SemiconjBy.exp_right {x a b : 𝔸} (h : SemiconjBy x a b) :
    SemiconjBy x (exp a) (exp b) := by
  rw [exp_eq_tsum ℚ]
  apply SemiconjBy.tsum_right x (expSeries_summable' _) (expSeries_summable' _)
  exact fun _ ↦ h.pow_right _ |>.smul_right _
/-
**NormedSpace._root_.SemiconjBy.exp_neg_mul_mul_exp_eq_self** 是 Mathlib 中的一个引理，位
于命名空间 `NormedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.SemiconjBy.exp_neg_mul_mul_exp_eq_self {x a b : 𝔸} (h : SemiconjBy x a b) :
    exp (-b) * x * exp a = x := by
  let := invertibleExp b
  simpa [← invOf_exp, mul_assoc, invOf_mul_eq_iff_eq_mul_left] using! h.exp_right

set_option backward.isDefEq.respectTransparency false in
open scoped Function in -- required for scoped `on` notation
/-- In a Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`, if a family of elements `f i` mutually
commute then `NormedSpace.exp (∑ i, f i) = ∏ i, NormedSpace.exp (f i)`. -/
/-
**NormedSpace.exp_sum_of_commute** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：exp_sum_of_commute {ι} (s : Finset ι) (f : ι -> 𝔸) (h : (s : Set ι).Pairwi
se (Commute on f)) : exp (∑ i in s, f i) = s.noncommProd (fun i => exp (f i)) fu
n _ hi _ hj _ => (h.of_refl hi hj).exp
参数：s : Finset ι；f : ι -> 𝔸；h : (s : Set ι).Pairwise (Commute on f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Commute.exp`：∀ {𝔸 : Type u_2} [inst : Ring 𝔸] [inst_1 : TopologicalSpace
 𝔸] [inst_2 : IsTopologicalRing 𝔸] [T2Space 𝔸] {x y : 𝔸},   Commute x y → Commut
e…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Set.Pairwise.of_refl`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α} [S
td.Refl r], s.Pairwise r → ∀ ⦃a : α⦄, a ∈ s → ∀ ⦃b : α⦄, b ∈ s → r a b
· 使用定理 `Commute.instRefl`：∀ {S : Type u_3} [inst : Mul S], Std.Refl Commute
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedSpace.exp_zero`：exp_zero : exp (0 : 𝔸) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.Pairwise.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, t 
⊆ s → s.Pairwise r → t.Pairwise r
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `Finset.noncommProd_insert_of_notMem`：noncommProd_insert_of_notMem [Decid
ableEq α] (s : Finset α) (a : α) (f : α -> β) (comm) (ha : a ∉ s) : noncommProd 
(insert a s) f comm = f a…
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `NormedSpace.exp_add_of_commute`：exp_add_of_commute {x y : 𝔸} (hxy : Comm
ute x y) : exp (x + y) = exp x * exp y
· 使用定理 `Commute.sum_right`：∀ {ι : Type u_1} {R : Type u_4} [inst : NonUnitalNonA
ssocSemiring R] (s : Finset ι) (f : ι → R) (b : R),   (∀ i ∈ s, Commute b (f i))
 → Comm…
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.subset_insert`：∀ {α : Type u_1} [inst : DecidableEq α] (a : α) (s
 : Finset α), s ⊆ insert a s

--- 原说明 ---
In a Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`, if a family of elements `f i` m
utually
commute then `NormedSpace.exp (∑ i, f i) = ∏ i, NormedSpace.exp (f i)`.
-/
theorem exp_sum_of_commute {ι} (s : Finset ι) (f : ι → 𝔸)
    (h : (s : Set ι).Pairwise (Commute on f)) :
    exp (∑ i ∈ s, f i) =
      s.noncommProd (fun i => exp (f i)) fun _ hi _ hj _ => (h.of_refl hi hj).exp := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha, Finset.sum_insert ha, exp_add_of_commute,
      ih (h.mono <| Finset.subset_insert _ _)]
    refine Commute.sum_right _ _ _ fun i hi => ?_
    exact h.of_refl (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hi)
/-
**NormedSpace.exp_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：exp_nsmul (n : Nat) (x : 𝔸) : exp (n • x) = exp x ^ n
参数：n : Nat；x : 𝔸。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `NormedSpace.exp_zero`：exp_zero : exp (0 : 𝔸) = 1
· 使用定理 `succ_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (n : ℕ), (n + 
1) • a = n • a + a
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `NormedSpace.exp_add_of_commute`：exp_add_of_commute {x y : 𝔸} (hxy : Comm
ute x y) : exp (x + y) = exp x * exp y
· 使用引理 `Commute.smul_left`：Commute.smul_left [Mul α] [SMulCommClass M α α] [IsSc
alarTower M α α] {a b : α} (h : Commute a b) (r : M) : Commute (r • a) b
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Commute.refl`：∀ {S : Type u_3} [inst : Mul S] (a : S), Commute a a
-/
theorem exp_nsmul (n : ℕ) (x : 𝔸) : exp (n • x) = exp x ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, exp_zero]
  | succ n ih => rw [succ_nsmul, pow_succ, exp_add_of_commute ((Commute.refl x).smul_left n), ih]

/-- Any continuous ring homomorphism commutes with `NormedSpace.exp`. -/
/-
**NormedSpace.map_exp** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：map_exp [Algebra Rat 𝔹] {F} [FunLike F 𝔸 𝔹] [RingHomClass F 𝔸 𝔹] (f : F) (
hf : Continuous f) (x : 𝔸) : f (exp x) = exp (f x)
参数：f : F；hf : Continuous f；x : 𝔸。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedSpace.map_exp_of_mem_ball`：map_exp_of_mem_ball [Algebra 𝕂 𝔹] [Char
Zero 𝕂] {F} [FunLike F 𝔸 𝔹] [RingHomClass F 𝔸 𝔹] (f : F) (hf : Continuous f) (x 
: 𝔸) (hx : x in Metri…
· 使用定理 `edist_lt_top`：edist_lt_top {α : Type*} [PseudoMetricSpace α] (x y : α) :
 edist x y < ⊤
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NormedSpace.expSeries_radius_eq_top`：expSeries_radius_eq_top : (expSerie
s 𝕂 𝔸).radius = ∞
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Rat.instIsTopologicalRing`：IsTopologicalRing ℚ

--- 原说明 ---
Any continuous ring homomorphism commutes with `NormedSpace.exp`.
-/
theorem map_exp [Algebra ℚ 𝔹]
    {F} [FunLike F 𝔸 𝔹] [RingHomClass F 𝔸 𝔹] (f : F) (hf : Continuous f) (x : 𝔸) :
    f (exp x) = exp (f x) :=
  map_exp_of_mem_ball f hf x <| (expSeries_radius_eq_top ℚ 𝔸).symm ▸ edist_lt_top _ _
/-
**NormedSpace.exp_smul** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：exp_smul {G} [Monoid G] [MulSemiringAction G 𝔸] [ContinuousConstSMul G 𝔸] 
(g : G) (x : 𝔸) : exp (g • x) = g • exp x
参数：g : G；x : 𝔸。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `NormedSpace.map_exp`：map_exp [Algebra Rat 𝔹] {F} [FunLike F 𝔸 𝔹] [RingHo
mClass F 𝔸 𝔹] (f : F) (hf : Continuous f) (x : 𝔸) : f (exp x) = exp (f x)
· 使用定理 `ContinuousConstSMul.continuous_const_smul`：∀ {Γ : Type u_1} {T : Type u_
2} {inst : TopologicalSpace T} {inst_1 : SMul Γ T} [self : ContinuousConstSMul Γ
 T]   (γ : Γ), Continuous fun x…
-/
theorem exp_smul {G} [Monoid G] [MulSemiringAction G 𝔸] [ContinuousConstSMul G 𝔸] (g : G) (x : 𝔸) :
    exp (g • x) = g • exp x :=
  (map_exp (MulSemiringAction.toRingHom G 𝔸 g) (continuous_const_smul g) x).symm
/-
**NormedSpace.exp_units_conj** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：exp_units_conj (y : 𝔸ˣ) (x : 𝔸) : exp (y * x * ↑y⁻¹ : 𝔸) = y * exp x * ↑y⁻
¹
参数：y : 𝔸ˣ；x : 𝔸。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedSpace.exp_smul`：exp_smul {G} [Monoid G] [MulSemiringAction G 𝔸] [C
ontinuousConstSMul G 𝔸] (g : G) (x : 𝔸) : exp (g • x) = g • exp x
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
-/
theorem exp_units_conj (y : 𝔸ˣ) (x : 𝔸) : exp (y * x * ↑y⁻¹ : 𝔸) = y * exp x * ↑y⁻¹ :=
  exp_smul (ConjAct.toConjAct y) x
/-
**NormedSpace.exp_units_conj'** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：exp_units_conj' (y : 𝔸ˣ) (x : 𝔸) : exp (↑y⁻¹ * x * y) = ↑y⁻¹ * exp x * y
参数：y : 𝔸ˣ；x : 𝔸。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedSpace.exp_units_conj`：exp_units_conj (y : 𝔸ˣ) (x : 𝔸) : exp (y * x
 * ↑y⁻¹ : 𝔸) = y * exp x * ↑y⁻¹
-/
theorem exp_units_conj' (y : 𝔸ˣ) (x : 𝔸) : exp (↑y⁻¹ * x * y) = ↑y⁻¹ * exp x * y :=
  exp_units_conj _ _

@[simp]
/-
**NormedSpace._root_.Prod.fst_exp** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Prod.fst_exp [NormedAlgebra ℚ 𝔹] [CompleteSpace 𝔹] (x : 𝔸 × 𝔹) :
    (exp x).fst = exp x.fst :=
  map_exp (RingHom.fst 𝔸 𝔹) continuous_fst x

@[simp]
/-
**NormedSpace._root_.Prod.snd_exp** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Prod.snd_exp [NormedAlgebra ℚ 𝔹] [CompleteSpace 𝔹] (x : 𝔸 × 𝔹) :
    (exp x).snd = exp x.snd :=
  map_exp (RingHom.snd 𝔸 𝔹) continuous_snd x

@[simp]
/-
**NormedSpace._root_.Pi.coe_exp** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Pi.coe_exp {ι : Type*} {𝔸 : ι → Type*} [Finite ι] [∀ i, NormedRing (𝔸 i)]
    [∀ i, NormedAlgebra ℚ (𝔸 i)] [∀ i, CompleteSpace (𝔸 i)] (x : ∀ i, 𝔸 i) (i : ι) :
    exp x i = exp (x i) :=
  let ⟨_⟩ := nonempty_fintype ι
  map_exp (Pi.evalRingHom 𝔸 i) (continuous_apply _) x
/-
**NormedSpace._root_.Pi.exp_def** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Pi.exp_def {ι : Type*} {𝔸 : ι → Type*} [Finite ι] [∀ i, NormedRing (𝔸 i)]
    [∀ i, NormedAlgebra ℚ (𝔸 i)] [∀ i, CompleteSpace (𝔸 i)] (x : ∀ i, 𝔸 i) :
    exp x = fun i => exp (x i) :=
  funext <| Pi.coe_exp x
/-
**NormedSpace._root_.Function.update_exp** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.update_exp {ι : Type*} {𝔸 : ι → Type*} [Finite ι] [DecidableEq ι]
    [∀ i, NormedRing (𝔸 i)] [∀ i, NormedAlgebra ℚ (𝔸 i)] [∀ i, CompleteSpace (𝔸 i)] (x : ∀ i, 𝔸 i)
    (j : ι) (xj : 𝔸 j) :
    Function.update (exp x) j (exp xj) = exp (Function.update x j xj) := by
  ext i
  simp_rw [Pi.exp_def]
  exact (Function.apply_update (fun i => exp) x j xj i).symm

end Rat

section DivisionAlgebra

variable {𝔸 : Type*} [NormedDivisionRing 𝔸] [NormedAlgebra ℚ 𝔸]

/-
**NormedSpace.norm_expSeries_div_summable** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace
`。
形式化陈述：norm_expSeries_div_summable (x : 𝔸) : Summable fun n => ‖(x ^ n / n ! : 𝔸)
‖
参数：x : 𝔸。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedSpace.norm_expSeries_div_summable_of_mem_ball`：norm_expSeries_div_
summable_of_mem_ball (x : 𝔸) (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).rad
ius) : Summable fun n => ‖x ^ n / (n !)‖
· 使用定理 `edist_lt_top`：edist_lt_top {α : Type*} [PseudoMetricSpace α] (x y : α) :
 edist x y < ⊤
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NormedSpace.expSeries_radius_eq_top`：expSeries_radius_eq_top : (expSerie
s 𝕂 𝔸).radius = ∞
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Rat.instIsTopologicalRing`：IsTopologicalRing ℚ
-/
theorem norm_expSeries_div_summable (x : 𝔸) : Summable fun n => ‖(x ^ n / n ! : 𝔸)‖ :=
  norm_expSeries_div_summable_of_mem_ball ℚ x
    ((expSeries_radius_eq_top ℚ 𝔸).symm ▸ edist_lt_top _ _)

variable [CompleteSpace 𝔸]
/-
**NormedSpace.expSeries_div_summable** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：expSeries_div_summable (x : 𝔸) : Summable fun n => x ^ n / n !
参数：x : 𝔸。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.of_norm`：Summable.of_norm {f : ι -> E} (hf : Summable fun a => 
‖f a‖) : Summable f
· 使用定理 `NormedSpace.norm_expSeries_div_summable`：norm_expSeries_div_summable (x 
: 𝔸) : Summable fun n => ‖(x ^ n / n ! : 𝔸)‖
-/
theorem expSeries_div_summable (x : 𝔸) : Summable fun n => x ^ n / n ! :=
  (norm_expSeries_div_summable x).of_norm
/-
**NormedSpace.expSeries_div_hasSum_exp** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：expSeries_div_hasSum_exp (x : 𝔸) : HasSum (fun n => x ^ n / n !) (exp x)
参数：x : 𝔸。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedSpace.expSeries_div_hasSum_exp_of_mem_ball`：expSeries_div_hasSum_e
xp_of_mem_ball [CharZero 𝕂] [CompleteSpace 𝔸] (x : 𝔸) (hx : x in Metric.eball (0
 : 𝔸) (expSeries 𝕂 𝔸).radius) : HasSum…
· 使用定理 `edist_lt_top`：edist_lt_top {α : Type*} [PseudoMetricSpace α] (x y : α) :
 edist x y < ⊤
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NormedSpace.expSeries_radius_eq_top`：expSeries_radius_eq_top : (expSerie
s 𝕂 𝔸).radius = ∞
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Rat.instIsTopologicalRing`：IsTopologicalRing ℚ
-/
theorem expSeries_div_hasSum_exp (x : 𝔸) : HasSum (fun n => x ^ n / n !) (exp x) :=
  expSeries_div_hasSum_exp_of_mem_ball ℚ x ((expSeries_radius_eq_top ℚ 𝔸).symm ▸ edist_lt_top _ _)
/-
**NormedSpace.exp_neg** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：exp_neg (x : 𝔸) : exp (-x) = (exp x)⁻¹
参数：x : 𝔸。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedSpace.exp_neg_of_mem_ball`：exp_neg_of_mem_ball [CharZero 𝕂] [Compl
eteSpace 𝔸] {x : 𝔸} (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : ex
p (-x) = (exp x)⁻¹
· 使用定理 `edist_lt_top`：edist_lt_top {α : Type*} [PseudoMetricSpace α] (x y : α) :
 edist x y < ⊤
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NormedSpace.expSeries_radius_eq_top`：expSeries_radius_eq_top : (expSerie
s 𝕂 𝔸).radius = ∞
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Rat.instIsTopologicalRing`：IsTopologicalRing ℚ
-/
theorem exp_neg (x : 𝔸) : exp (-x) = (exp x)⁻¹ :=
  exp_neg_of_mem_ball ℚ <| (expSeries_radius_eq_top ℚ 𝔸).symm ▸ edist_lt_top _ _
/-
**NormedSpace.exp_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：exp_zsmul (z : Int) (x : 𝔸) : exp (z • x) = exp x ^ z
参数：z : Int；x : 𝔸。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Int.eq_nat_or_neg`：∀ (a : ℤ), ∃ n, a = ↑n ∨ a = -↑n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `NormedSpace.exp_nsmul`：exp_nsmul (n : Nat) (x : 𝔸) : exp (n • x) = exp x
 ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `NormedSpace.exp_neg`：exp_neg (x : 𝔸) : exp (-x) = (exp x)⁻¹
-/
theorem exp_zsmul (z : ℤ) (x : 𝔸) : exp (z • x) = exp x ^ z := by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · rw [zpow_natCast, natCast_zsmul, exp_nsmul]
  · rw [zpow_neg, zpow_natCast, neg_smul, exp_neg, natCast_zsmul, exp_nsmul]
/-
**NormedSpace.exp_conj** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：exp_conj (y : 𝔸) (x : 𝔸) (hy : y != 0) : exp (y * x * y⁻¹) = y * exp x * y
⁻¹
参数：y : 𝔸；x : 𝔸；hy : y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedSpace.exp_units_conj`：exp_units_conj (y : 𝔸ˣ) (x : 𝔸) : exp (y * x
 * ↑y⁻¹ : 𝔸) = y * exp x * ↑y⁻¹
-/
theorem exp_conj (y : 𝔸) (x : 𝔸) (hy : y ≠ 0) : exp (y * x * y⁻¹) = y * exp x * y⁻¹ :=
  exp_units_conj (Units.mk0 y hy) x
/-
**NormedSpace.exp_conj'** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：exp_conj' (y : 𝔸) (x : 𝔸) (hy : y != 0) : exp (y⁻¹ * x * y) = y⁻¹ * exp x 
* y
参数：y : 𝔸；x : 𝔸；hy : y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedSpace.exp_units_conj'`：exp_units_conj' (y : 𝔸ˣ) (x : 𝔸) : exp (↑y⁻
¹ * x * y) = ↑y⁻¹ * exp x * y
-/
theorem exp_conj' (y : 𝔸) (x : 𝔸) (hy : y ≠ 0) : exp (y⁻¹ * x * y) = y⁻¹ * exp x * y :=
  exp_units_conj' (Units.mk0 y hy) x

end DivisionAlgebra

section CommAlgebra

variable {𝕂 𝔸 : Type*} [NormedCommRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]

/-- In a commutative Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`,
`NormedSpace.exp (x+y) = (NormedSpace.exp x) * (NormedSpace.exp y)`. -/
/-
**NormedSpace.exp_add** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：exp_add {x y : 𝔸} : exp (x + y) = exp x * exp y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedSpace.exp_add_of_mem_ball`：exp_add_of_mem_ball [CharZero 𝕂] {x y :
 𝔸} (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) (hy : y in Metric.eb
all (0 : 𝔸) (expSerie…
· 使用定理 `edist_lt_top`：edist_lt_top {α : Type*} [PseudoMetricSpace α] (x y : α) :
 edist x y < ⊤
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NormedSpace.expSeries_radius_eq_top`：expSeries_radius_eq_top : (expSerie
s 𝕂 𝔸).radius = ∞
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Rat.instIsTopologicalRing`：IsTopologicalRing ℚ

--- 原说明 ---
In a commutative Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`,
`NormedSpace.exp (x+y) = (NormedSpace.exp x) * (NormedSpace.exp y)`.
-/
theorem exp_add {x y : 𝔸} : exp (x + y) = exp x * exp y :=
  exp_add_of_mem_ball ((expSeries_radius_eq_top ℚ 𝔸).symm ▸ edist_lt_top _ _)
    ((expSeries_radius_eq_top ℚ 𝔸).symm ▸ edist_lt_top _ _)

/-- A version of `NormedSpace.exp_sum_of_commute` for a commutative Banach-algebra. -/
/-
**NormedSpace.exp_sum** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：exp_sum {ι} (s : Finset ι) (f : ι -> 𝔸) : exp (∑ i in s, f i) = ∏ i in s, 
exp (f i)
参数：s : Finset ι；f : ι -> 𝔸。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Commute.exp`：∀ {𝔸 : Type u_2} [inst : Ring 𝔸] [inst_1 : TopologicalSpace
 𝔸] [inst_2 : IsTopologicalRing 𝔸] [T2Space 𝔸] {x y : 𝔸},   Commute x y → Commut
e…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Set.Pairwise.of_refl`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α} [S
td.Refl r], s.Pairwise r → ∀ ⦃a : α⦄, a ∈ s → ∀ ⦃b : α⦄, b ∈ s → r a b
· 使用定理 `Commute.instRefl`：∀ {S : Type u_3} [inst : Mul S], Std.Refl Commute
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedSpace.exp_sum_of_commute`：exp_sum_of_commute {ι} (s : Finset ι) (f
 : ι -> 𝔸) (h : (s : Set ι).Pairwise (Commute on f)) : exp (∑ i in s, f i) = s.n
oncommProd (fun i =>…
· 使用定理 `Finset.noncommProd_eq_prod`：noncommProd_eq_prod {β : Type*} [CommMonoid 
β] (s : Finset α) (f : α -> β) : (noncommProd s f fun _ _ _ _ _ => Commute.all _
 _) = s.prod f

--- 原说明 ---
A version of `NormedSpace.exp_sum_of_commute` for a commutative Banach-algebra.
-/
theorem exp_sum {ι} (s : Finset ι) (f : ι → 𝔸) : exp (∑ i ∈ s, f i) = ∏ i ∈ s, exp (f i) := by
  rw [exp_sum_of_commute, Finset.noncommProd_eq_prod]
  exact fun i _hi j _hj _ => Commute.all _ _

end CommAlgebra

end Normed

section ScalarTower

variable (𝕂 𝕂' 𝔸 : Type*) [Field 𝕂] [Field 𝕂'] [Ring 𝔸] [Algebra 𝕂 𝔸] [Algebra 𝕂' 𝔸]
  [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸]

/-- If a normed ring `𝔸` is a normed algebra over two fields, then they define the same
`expSeries` on `𝔸`. -/
/-
**NormedSpace.expSeries_eq_expSeries** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：expSeries_eq_expSeries (n : Nat) (x : 𝔸) : (expSeries 𝕂 𝔸 n fun _ => x) = 
expSeries 𝕂' 𝔸 n fun _ => x
参数：n : Nat；x : 𝔸。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedSpace.expSeries_apply_eq`：expSeries_apply_eq (x : 𝔸) (n : Nat) : (
expSeries 𝕂 𝔸 n fun _ => x) = (n !⁻¹ : 𝕂) • x ^ n
· 使用定理 `inv_natCast_smul_eq`：inv_natCast_smul_eq {E : Type*} (R S : Type*) [AddC
ommMonoid E] [DivisionSemiring R] [DivisionSemiring S] [Module R E] [Module S E]
 (n : Nat…

--- 原说明 ---
If a normed ring `𝔸` is a normed algebra over two fields, then they define the s
ame
`expSeries` on `𝔸`.
-/
theorem expSeries_eq_expSeries (n : ℕ) (x : 𝔸) :
    (expSeries 𝕂 𝔸 n fun _ => x) = expSeries 𝕂' 𝔸 n fun _ => x := by
  rw [expSeries_apply_eq, expSeries_apply_eq, inv_natCast_smul_eq 𝕂 𝕂']

/-- A version of `Complex.ofReal_exp` for `NormedSpace.exp` instead of `Complex.exp` -/
@[simp, norm_cast]
/-
**NormedSpace.ofReal_exp_** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Complex.ofReal_exp` for `NormedSpace.exp` instead of `Complex.exp`
-/
theorem ofReal_exp_ℝ_ℝ (r : ℝ) : ↑(exp r) = exp (r : ℂ) :=
  map_exp (algebraMap ℝ ℂ) (continuous_algebraMap _ _) r

end ScalarTower

end NormedSpace

